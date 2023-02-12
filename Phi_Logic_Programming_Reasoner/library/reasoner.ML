(*
The engine of the Phi Logic Programming Reasoner
Author: Qiyuan Xu
*)
signature NU_REASONER = sig
  (* This file is the major hot point of the whole system.
     TODO: optimize it as much as possible! *)

 
  type priority = int
  type pattern = term
  type name = term

  type reasoner = {name: name,
                 pos: Position.T,
                 pattern: pattern list,
                 blacklist: pattern list,
                 tactic: (context_state -> context_state Seq.seq)}


  val trace : bool Config.T (*Prints the state of every reasoning step.*)
  val trace_candidates : bool Config.T (*Prints the candidates at each step.*)
  val count_performance : bool Config.T
  val step_limit : int Config.T (*limit of the number of reasoning steps*)
  val debug_info: Proof.context -> (unit -> string) -> unit
  val debug_pretty: Proof.context -> (unit -> Pretty.T) -> unit
            (*Prints any debug info only when the flag \<phi>trace_reasoning is turned on.*)
  val debug_pretty_generic : Context.generic -> (unit -> Pretty.T) -> unit
  val error : string -> 'a
  val bad_config : string -> 'a

  (*auto level: 2 - fully auto, 1 - partially auto, 0 - fully manual*)
  val auto_level : int Config.T
  val reduce_auto_level : int -> Proof.context -> Proof.context

  exception Success of context_state
  exception Global_Cut of context_state

  structure Global_Cut_Handlers : PLPR_HANDLERS
  structure Success_Handlers : PLPR_HANDLERS
  val disable_global_cut : string -> Proof.context -> serial * Proof.context
  val disable_success    : string -> Proof.context -> serial * Proof.context

  val add : priority * reasoner -> Context.generic -> Context.generic
  val add_lthy : priority * reasoner -> local_theory -> local_theory
  val del : name -> Context.generic -> Context.generic
  val has : term -> Context.generic -> bool
  val reasoners : Proof.context -> (priority * reasoner) list
  val reasoner_net : Proof.context -> reasoner Cost_Net.T

  (* Interfaces for Reasoning *)
  (*N: number of premises to be attacked at most, if it is positive;
       to attack all if it is None;
       to attack until a sequent remains at most |N| premises, if N is negative*)
  val reason  : int option (*N*) -> context_state -> context_state option
  val reason1 : (unit -> string) (*error message*)
             -> int option (*N*) -> context_state -> context_state
  val reason_s : Proof.context (*the context for accessing reasoner db*)
              -> (Proof.context -> 'a * (priority * context_state Seq.seq) list)
              -> 'a * context_state option
  (*Note it returns at most one state in the returned sequence.*)
  val reason_tac : int option (*N*)
                -> Proof.context (*the context for accessing reasoner db*)
                -> context_tactic

  (*The nested level of the current reasoning*)
  val nested_level : Proof.context -> int (*Starting from 1*)


  val add_intro_rule : Position.T -> priority -> term list * term list
                    -> (context_state -> bool) option
                    -> thm list
                    -> Context.generic -> Context.generic
  val add_intro_rules: (thm list * Position.T * priority * term list * term list
                       * (context_state -> bool) option) list
                    -> Context.generic -> Context.generic
  val has_intro_rule : thm list -> Context.generic -> bool
  val del_intro_rule : thm list -> Context.generic -> Context.generic
  val attr_add_intro :
        (((Position.T * int) * thm list) * (term list * term list)) * (context_state -> bool) option
       -> attribute
  val attr_del_intro : thm list -> attribute

  val setup_cmd : (((string (*name term*) * Position.T) * priority)
                   * (bool (*true for matching, false for not matching*)
                      * string (*pattern term*)) list
                  ) * Input.source (* tactic source*)
        -> local_theory -> local_theory

  (* Default Pattern of Introduction Rule *)
  val add_default_pattern :
                  (int (*priority*) * term (*pattern P*) * term (*the default pattern X*)) list
               -> Context.generic -> Context.generic
      (*The default pattern of an introduction rule whose conclusion matches P is X.*)
  val remove_default_pattern : int * term * term -> Context.generic -> Context.generic
  val the_default_pattern_of : Context.generic -> term -> term

  (* Helpful Tools *)
  val chop_seq_head' : 'a Seq.seq -> 'a option
  val chop_seq_head  : 'a Seq.seq -> 'a Seq.seq
  val single_RS' : thm (*rule*) -> context_state -> context_state option
  val single_RS  : thm (*rule*) -> context_state -> context_state Seq.seq
        (*The resolution that returns at most one solution.*)
end

(*A special name to prevent someone overriding this structure, whose visibility is essential
  for parsing ML guard, see the ML_guard parser in declaring the \<phi>reason attribute*)
structure PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu = Proof_Data (
  type T = (context_state -> bool)
  val init = K (K true)
)

structure Phi_Reasoner : NU_REASONER = struct

(*** Preliminaries ***)

(* Types *)
type priority = int
type pattern = term
type name = term
type reasoner = {name: term,
                 pos: Position.T,
                 pattern: term list,
                 blacklist: term list,
                 tactic: (context_state -> context_state Seq.seq)}

val trick = map_aterms (fn Var ((s,i),T) => Var ((s, if String.isPrefix "var_" s then ~i - 1 else i),T)
                         | X => X)

fun normalize_reasoner ({name,pos,pattern,blacklist,tactic}:reasoner) =
  ({name=name, pos=pos, pattern = map (trick o Envir.beta_eta_contract) pattern,
    blacklist = map (trick o Envir.beta_eta_contract) blacklist, tactic = tactic}:reasoner)

fun transform_reasoner phi ({name,pos,pattern,blacklist,tactic}:reasoner) =
  ({name=name, pos=pos,
    pattern = map (Morphism.term phi) pattern,
    blacklist = map (Morphism.term phi) blacklist,
    tactic = tactic}:reasoner)
  

(* Attributes *)
val auto_level = Attrib.setup_config_int \<^binding>\<open>\<phi>auto_level\<close> (K 2)
fun reduce_auto_level i = Config.map auto_level (fn j => Int.min (i,j))

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning\<close> (K false);
val trace_candidates = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning_candidates\<close> (K false);
val count_performance = Attrib.setup_config_bool \<^binding>\<open>\<phi>count_performance\<close> (K false);

val step_limit = Attrib.setup_config_int \<^binding>\<open>\<phi>reasoning_step_limit\<close> (K 1000);


(* Debug Info *)
fun debug_pretty ctxt G =
  if Config.get ctxt trace
  then tracing (Pretty.string_of (G ()))  
  else ()
fun debug_info ctxt G = debug_pretty ctxt (G #> Pretty.str)

fun debug_pretty_generic ctxt G =
  if Config.get_generic ctxt trace
  then tracing (Pretty.string_of (G ()))  
  else ()

fun error msg = Exn.error (msg ^ "\nReasoning Fail! You may turn on \<phi>trace_reasoning or\
      \ \<phi>trace_reasoning_candidates to debug.")
fun bad_config msg = Exn.error (msg ^ "\nSome rule is configured incorrectly!")

(* Reasoning Environ *)

structure Environ = Proof_Data (
  type T = int (*nested level*)
  val init = K 0
)

val enter_reasoning_envir = Environ.map (fn x => x + 1)
val exit_reasoning_envir  = Environ.map (fn x => x - 1)
val nested_level = Environ.get

(* Cut, Abrupt Termination, and Handlers *)

exception Success    of context_state
exception Global_Cut of context_state
exception Local_Cut  of (priority * Position.T * context_state Seq.seq)

structure Global_Cut_Handlers = PLPR_Handlers(
  type domT = context_state
  type retT = (priority * Position.T * context_state Seq.seq) list
  fun default s = raise Global_Cut s
  val current_level = nested_level
  val ctxt_of = fst
)

structure Success_Handlers = PLPR_Handlers(
  type domT = context_state
  type retT = (priority * Position.T * context_state Seq.seq) list
  fun default s = raise Success s
  val current_level = nested_level
  val ctxt_of = fst
)

fun disable_global_cut msg = Global_Cut_Handlers.push_local (fn _ => bad_config msg)
fun disable_success    msg = Success_Handlers.push_local (fn _ => bad_config msg)

(*** Reasoner Registry ***)
fun reasoner_eq ({name,...}, {name=name',...}) = (name = name')

structure Reasoners = Generic_Data (
  type T = reasoner Cost_Net.T
  val empty : T = Cost_Net.init reasoner_eq #pattern
  val merge : T * T -> T = Cost_Net.merge
)

fun reasoners ctxt = Cost_Net.content (Reasoners.get (Context.Proof ctxt)) |> map (apfst ~)
fun reasoner_net ctxt = Reasoners.get (Context.Proof ctxt)
fun add (priority,reasoner) =
      Reasoners.map (Cost_Net.update (~priority, normalize_reasoner reasoner));
fun adds reasoners =
      Reasoners.map (fold (Cost_Net.update o apfst (op ~) o apsnd normalize_reasoner) reasoners)
fun add_lthy cost_reasoner =
  Local_Theory.declaration {syntax=false, pervasive=false} (fn phi =>
    add (apsnd (transform_reasoner phi) cost_reasoner)
  )

fun del name = Reasoners.map (Cost_Net.remove(
      {name=name, pos=Position.none, pattern=[], blacklist=[], tactic = K Seq.empty}))

fun has name ctxt = Cost_Net.member (Reasoners.get ctxt) (
      {name=name, pos=Position.none, pattern=[], blacklist=[], tactic = K Seq.empty})

(*** Implementing Functions ***)

(* Main Reasoning Function *)

fun debug ctxt (c,(r : reasoner as {name,...})) =
  tracing ("reasoning candicates (" ^ string_of_int c ^ "):\n"
              ^ Syntax.string_of_term (Proof_Context.set_mode Proof_Context.mode_abbrev ctxt) name)

fun is_var (A $ _) = is_var A
  | is_var (Var _) = true
  | is_var _ = false

fun match_term thy pat_obj =
  let
    val (_,tms) = PLPR_Pattern.match thy pat_obj (Vartab.empty, Vartab.empty)
  in Vartab.fold (fn ((name,i),(_,tm)) => fn flag =>
        if i < 0 (* String.isPrefix "var_" name *)
        then flag andalso is_var (Envir.beta_eta_contract tm)
        else flag
     ) tms true
  end
  handle Pattern.MATCH => false

fun concl_of_goal st i =
  let val (gi, rfrees) = Logic.goal_params st i
      val B = Logic.strip_assums_concl gi
      (*val As = Logic.strip_assums_hyp gi*)
  in subst_bounds (rfrees, B)
  end


fun beta_eta_contract_leading_antecedent th =
  if (case Thm.prop_of th
        of \<^const>\<open>Pure.imp\<close> $ X $ _ => Term.could_beta_eta_contract X
         | _ => false)
  then Thm.equal_elim (Conv.implies_conv Drule.beta_eta_conversion
                                         Conv.all_conv (Thm.cprop_of th)) th
  else th

fun call_tactics cost_delt N ctxt tactics th0 =
  let val th = beta_eta_contract_leading_antecedent th0 in
  if Thm.nprems_of th <= N
  then raise Success (ctxt, th)
  else let
    val tacs = Thm.major_prem_of th (*TODO: if we can implement a HO match which tolerates loose
                                      bounds, we don't need substituting loose bounds any more here
                                      and the performance can be improved effectively.*)
                |> (fn term =>
                    Cost_Net.retrieve tactics term
                      |> filter (fn (_,reasoner) =>
                          exists (fn pat =>
                            match_term (Proof_Context.theory_of ctxt) (pat,term))
                          (#pattern reasoner)
                          andalso forall (fn pat =>
                            not (match_term (Proof_Context.theory_of ctxt) (pat,term)))
                          (#blacklist reasoner))
                      |> (if Config.get ctxt trace_candidates
                          then (fn rs => (List.app (debug ctxt) rs; rs))
                          else I))
  in
    tacs 
      |> map_filter (fn (cost, r : reasoner) =>
          if cost <= ~1000000 then
            case Seq.pull (#tactic r (ctxt,th))
              of SOME (x,_) => raise Global_Cut x
               | _ => NONE
          else if cost <= ~1000 then
            case Seq.pull (#tactic r (ctxt,th))
              of SOME (x,s) => raise Local_Cut (cost + cost_delt, #pos r, Seq.cons x s)
               | _ => NONE
          else SOME (cost + cost_delt, #pos r, Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))))
        )
  end
  end
  handle Local_Cut ret => [ret]
       | Success s => Success_Handlers.invoke (fst s) s
       | Global_Cut s => Global_Cut_Handlers.invoke (fst s) s

fun gen_reason _ _ _ _ _ [] = NONE
  | gen_reason N trace limit iter tactics ([]::L) =
      (if trace then tracing ("Backtracking...") else ();
       gen_reason N trace limit iter tactics L)
  | gen_reason N trace limit iter tactics (((cost,pos,seq)::L')::L) =
  let
    val _ = if iter > limit
            then error "The reasoning reaches the limit of the number of reasoning steps.\n\
                       \Perhaps an infinite loop is encountered.\nOtherwise, \
                       \you can set \<phi>reasoning_step_limit to increase the limit of the steps\
                       \if it is too small."
            else ()
  in
    case Seq.pull seq
      of SOME ((ctxt,th), seq') =>
          (let
            val _ = if trace
                    then tracing ("\<phi>reasoning (score " ^ string_of_int (~cost)
                      ^ "):"^ Position.here pos ^"\n" ^ Thm.string_of_thm ctxt th)
                    else ()
            val Z = (call_tactics cost N ctxt tactics th)
                  |> (fn Z => Z::(
                        let val t = if pointer_eq (seq',Seq.empty) then L' else (cost,pos,seq')::L'
                        in if null t then L else t::L end))
                handle Success ret => raise Success ret
                     | Global_Cut stat =>
                        let
                          val _ = if trace
                                  then tracing ("\<phi>reasoning cut:\n"
                                          ^ Thm.string_of_thm ctxt (snd stat))
                                  else ()
                        in
                          [[(0,pos, Seq.single stat)]]
                        end
          in
            gen_reason N trace limit (iter+1) tactics Z
          end)
       | NONE => gen_reason N trace limit iter tactics (L'::L)
  end

(*Entry point*)
fun gen_reason' ctxt N states =
  Timing.cond_timeit (Config.get ctxt count_performance) "Time spent by \<phi>-LPR reasoning:" (fn () =>
     (gen_reason N (Config.get ctxt trace) (Config.get ctxt step_limit)
                 0 (Reasoners.get (Context.Proof ctxt))
                 (map (map (fn (a,b) => (~a,Position.none, b))) states)
      handle Success ret => SOME ret)
     |> Option.map (apfst exit_reasoning_envir)
  )
    


(* Various Interfaces for Invoking Reasoning *)

fun num_of_protected_prems  _  NONE = 0
  | num_of_protected_prems thm (SOME N) =
      if N >= 0 then Thm.nprems_of thm - N else ~N

fun reason (SOME 0) S = SOME S
  | reason N (ctxt,sequent) =
      gen_reason' ctxt (num_of_protected_prems sequent N)
                  [[(0, Seq.single (enter_reasoning_envir ctxt, sequent))]]

fun reason1 G N stat = case reason N stat of SOME x => x | NONE => error (G ())

fun reason_s ctxt seqs =
  let val (ret,seqs') = seqs (enter_reasoning_envir ctxt)
   in (ret, gen_reason' ctxt 0 [seqs'])
  end

fun reason_tac N ctxt stat = Seq.make (fn () =>
      gen_reason' ctxt (num_of_protected_prems (snd stat) N)
                  [[(0, Seq.single (apfst enter_reasoning_envir stat))]]
       |> Option.map (rpair Seq.empty o Seq.Result)
    )



(*** Command Interface ***)

fun setup_method_cmd (((name,cost),patterns),method) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val patterns = split_list patterns
                      |> apsnd (Syntax.read_props ctxt)
                      |> (op ~~)
    val pos_pats = patterns |> map_filter (fn (direct, pat) => if direct then SOME pat else NONE)
    val neg_pats = patterns |> map_filter (fn (direct, pat) => if direct then NONE else SOME pat)
    val name' = Free(Binding.name_of name, dummyT)

    val (method',lthy') = Method_Closure.method_cmd name [] [] [] [] method lthy
    val method'' = Method_Closure.apply_method lthy' method' [] [] []
    val method'''= (fn (ctxt,thm) => method'' ctxt [] (ctxt,thm) |> Seq.filter_results)
  in add_lthy (cost, {name=name', pos=Binding.pos_of name,
                      pattern=pos_pats, blacklist=neg_pats, tactic=method'''}) lthy'
  end

fun setup_cmd ((((name,pos),cost),patterns),tactic_src) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val name = Syntax.read_term lthy name
    val patterns = split_list patterns
                      |> apsnd (Syntax.read_props ctxt)
                      |> (op ~~)
    val pos_pats = patterns |> map_filter (fn (direct, pat) =>
              if direct then SOME pat else NONE)
    val neg_pats = patterns |> map_filter (fn (direct, pat) =>
              if direct then NONE else SOME pat)
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of tactic_src)
        (ML_Lex.read
          ("Theory.local_setup (Phi_Reasoner.add_lthy (" ^
          ML_Syntax.print_int cost ^ ", {name=(" ^
          ML_Syntax.print_term name ^ "), pos=("^
          ML_Syntax.print_position pos ^ "), pattern=(" ^
          ML_Syntax.print_list ML_Syntax.print_term pos_pats
          ^ "), blacklist=("^
          ML_Syntax.print_list ML_Syntax.print_term neg_pats
          ^"), tactic=(let in ") @
          ML_Lex.read_source tactic_src @
          ML_Lex.read (" end):(context_state -> context_state Seq.seq)}))"))
    )
  end

val patterns = Parse.$$$ "(" |-- Parse.enum "|"
      (Scan.optional (\<^keyword>\<open>except\<close> >> K false) true -- Parse.term)
      --| Parse.$$$ ")"

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner_ML} "define \<phi>reasoner"
    (Parse.position Parse.term -- Parse.int -- patterns
        --| @{keyword =} -- Parse.ML_source
      >> setup_cmd)

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner} "define \<phi>reasoner"
    (Parse.binding -- Parse.int -- patterns
        --| @{keyword =} -- Parse.args1 (K true)
      >> setup_method_cmd)


(*** Default Pattern for Introduction Reasoning Rule ***)

fun pat_pat_eq ((p1,a1,b1),(p2,a2,b2)) = p1 = p2 andalso a1 aconv a2 andalso b1 aconv b2

structure Default_Pattern = Generic_Data (
  type T = (int (*priority*) * term (*pattern P*) * term (*the default pattern X*)) Net.net
  (*It gives the default pattern P of an introduction rule whose conclusion matches some pattern P.
    Larger priority is more prior.*)
  val empty = Net.empty
  val merge = Net.merge pat_pat_eq
)

fun add_default_pattern pat_pats ctxt =
      Default_Pattern.map (fold (fn (n,p1,p2) =>
              Net.insert_term pat_pat_eq (p1,(n,p1,p2))) pat_pats) ctxt
      handle Net.INSERT => Exn.error ("Some pattern clashes with existing entries.")
fun remove_default_pattern (n,p1,p2) =
      Default_Pattern.map (Net.delete_term_safe pat_pat_eq (p1,(n,p1,p2)))

fun calc_pattern thy term (n, pat, pat_ret) =
 (SOME (n, Envir.subst_term (Pattern.match thy (pat, term) (Vartab.empty, Vartab.empty)) pat_ret))
  handle Pattern.MATCH => NONE

fun the_default_pattern_of ctxt term =
  Net.match_term (Default_Pattern.get ctxt) term
    |> sort (fn ((n1,_,_),(n2,_,_)) => int_ord (n2,n1))
    |> Seq.of_list
    |> Seq.map_filter (calc_pattern (Context.theory_of ctxt) term)
    |> Seq.chop 2
    |> (fn ([], _) => term
         | ([(_,ret)], _) => ret
         | ([(n1,ret),(n2,ret2)], _) =>
            if n1 = n2
            then error (Pretty.string_of (Pretty.chunks (
                    [Pretty.str "Multiple default patterns are available:"] @
                    (map (Syntax.pretty_term (Context.proof_of ctxt)) [ret,ret2]) @
                    [Pretty.str "Fail to determine which pattern is preferable. \
                                \Please indicate the pattern manually using syntax \
                                \\<open>\<phi>reason for \<open>pattern\<close>\<close>"]
                 )))
            else ret)


fun wrap2L f (x,y) = case f [x,y] of [x',y'] => (x',y')
val pat2 = (Args.context -- Scan.lift (Parse.prop --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) -- Parse.prop
                                      --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (ctxt,((p1,p2),n)) =>
    let val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
        val [p1',p2'] = Syntax.check_props ctxt_p [Syntax.parse_prop ctxt_p p1,
                                                   Syntax.parse_prop ctxt_p p2]
     in (n,p1',p2')
     end)

val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>reason_default_pattern\<close>
    (Parse.enum1' "and" pat2 >> (fn pats =>
              Thm.declaration_attribute (K (add_default_pattern pats))))
    "set the default pattern of a reasoning rule once its conclusion matches some pattern"
)

(*** Reasoner for Introduction Reasoning Rule ***)

fun chop_seq_head' seq =
  case Seq.chop 2 seq
    of ([ret], _) => SOME ret
       | ([], _) => NONE
       | (ret::_, _) => (warning "Multi Resolution! For performance consideration, PLPR only takes\
                                 \ the first solution and discards the remains.";
                         SOME ret)

fun chop_seq_head seq =
  Seq.make (fn _ => Option.map (rpair Seq.empty) (chop_seq_head' seq))

fun single_RS' rule (ctxt,thm) =
  Thm.biresolution (SOME ctxt) false [(false,rule)] 1 thm
    |> chop_seq_head'
    |> Option.map (pair ctxt)

fun single_RS rule (ctxt,thm) =
  Seq.make (fn _ => Option.map (rpair Seq.empty) (single_RS' rule (ctxt,thm)))


fun name_of_intro_reasoner rules =
  Free ("\<phi>Intro_Rule", \<^typ>\<open>prop \<Rightarrow> prop\<close>) $ Logic.mk_conjunction_list (map Thm.prop_of rules)

fun intro_reasoner ctxt pos priority patterns blacklist guard rules =
  let
    val rules = rules
             |> filter (fn th => not (Thm.is_free_dummy th orelse Thm.is_dummy th))
             |> map Thm.trim_context
    val _ = if null rules then error ("No rule is given!") else ()
    val pats = if null patterns
               then case rules
                      of [rule] =>
                        let val pat = the_default_pattern_of ctxt (Thm.concl_of rule)
                            val _ = debug_pretty_generic ctxt (fn () => Pretty.chunks [
                                    Pretty.str "No pattern is given, use the default pattern:",
                                    Syntax.pretty_term (Context.proof_of ctxt) pat
                                ])
                        in [pat] end
                       | _ => error "Pattern of the reasoner is required"
               else patterns
    
    val rules_with_flag = map (fn rule =>
      let fun is_Require (Const (\<^const_name>\<open>\<r>Require\<close>, _) $ _) = true
            | is_Require (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_Require X
            | is_Require (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_,_,X)) = is_Require X
            | is_Require _ = false
       in case Thm.prems_of rule
            of []    => (rule, false)
             | (r::L)=> if exists is_Require L
                        then error("A reasoning rule can contain one \<r>Require antecedent at \
                                   \the leading position.")
                        else if is_Require r
                         then if priority < 1000
                          then error("Conditional \<r>Require only makes sense for confident rule.")
                          else (rule, true)
                         else (rule, false)
      end) rules

    fun tactic [] _ = Seq.empty
      | tactic ((rule, has_semantic_guard)::R) s = Seq.make (fn _ =>
          single_RS' rule s
            |> has_semantic_guard ? Option.mapPartial (reason (SOME 1))
            |> (fn NONE => Seq.pull (tactic R s)
                 | SOME ret => SOME (ret, tactic R s))
        )
    fun guarded_tac rules =
      case guard of NONE => tactic rules
                  | SOME G => let val tac = tactic rules
                               in (fn s => if G s then tac s else Seq.empty) end
  in {name = name_of_intro_reasoner rules,
      pos = pos,
      pattern = pats,
      blacklist = blacklist,
      tactic = guarded_tac rules_with_flag
      }
  end

fun add_intro_rule pos priority (pattern,blacklist) guard rules ctxt =
      add (priority, intro_reasoner ctxt pos priority pattern blacklist guard rules) ctxt
fun add_intro_rules rules ctxt =
  if null rules then ctxt
  else adds (map (fn (rule,pos,priority,pattern,blacklist,guard) =>
              (priority, intro_reasoner ctxt pos priority pattern blacklist guard rule)) rules) ctxt
fun del_intro_rule rule = del (name_of_intro_reasoner rule)
fun has_intro_rule rule = has (name_of_intro_reasoner rule)

fun attr_add_intro ((((pos, priority), additional_rules), (pattern, blacklist)), guard) =
  Thm.declaration_attribute (fn rule =>
      add_intro_rule pos priority (pattern,blacklist) guard (rule::additional_rules))
fun attr_del_intro additional_rules =
  Thm.declaration_attribute (fn rule => del_intro_rule (rule::additional_rules))



val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>reason\<close>
(let open Args Scan Parse 
  fun read_prop_mode mode' ctxt tm = Syntax.read_prop (Proof_Context.set_mode mode' ctxt) tm
  val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
  val prop_pattern = Scan.repeat (Scan.peek (named_term o read_prop_pattern o Context.proof_of))
  fun pos_parser x = (Token.pos_of (hd x), x)
  val ML_guard = depend (fn ctxt0 => ML_source >> (fn src =>
       let val ctxt = Context.Proof (Context.proof_of ctxt0)
            |> ML_Context.expression (Input.pos_of src)
              (ML_Lex.read "Theory.local_setup (PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.put (" @
               ML_Lex.read_source src @
               ML_Lex.read "))")
       in (ctxt0, PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.get (Context.the_proof ctxt)) end
     ))
in
  (lift pos_parser
  -- lift (option add |-- ((\<^keyword>\<open>!\<close> >> K 2000000) || optional Parse.int 100))
  -- Attrib.thms
  -- ( optional (lift (\<^keyword>\<open>for\<close>) |-- prop_pattern) []
    -- optional (lift (\<^keyword>\<open>except\<close>) |-- prop_pattern) [])
  -- option (lift \<^keyword>\<open>if\<close> |-- ML_guard)
  >> attr_add_intro)
|| ((lift del |-- Attrib.thms) >> attr_del_intro)
end)
"Decalre or remove introduction rules in \<phi>-LPR."

#> Method.setup \<^binding>\<open>\<phi>reason\<close>
(let open Scan Parse in
  Scan.lift (Scan.option Parse.nat) --|
  Method.sections [
    Parse.position Args.add >> (fn (_,pos) =>
               Method.modifier (attr_add_intro ((((pos,100),[]),([],[])),NONE)) \<^here>),
    Args.del >> K (Method.modifier (attr_del_intro []) \<^here>)
] >> (fn num_prems => fn ctxt => fn ths => reason_tac num_prems ctxt)
end)
"Apply \<phi>-LPR as a proof method."

)



end
