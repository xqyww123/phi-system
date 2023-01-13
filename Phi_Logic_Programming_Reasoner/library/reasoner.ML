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
  val step_limit : int Config.T (*limit of the number of reasoning steps*)
  val debug_info: Proof.context -> (unit -> string) -> unit
  val debug_pretty: Proof.context -> (unit -> Pretty.T) -> unit
            (*Prints any debug info only when the flag \<phi>trace_reasoning is turned on.*)
  val debug_pretty_generic : Context.generic -> (unit -> Pretty.T) -> unit
  val error : string -> 'a

  (*auto level: 2 - fully auto, 1 - partially auto, 0 - fully manual*)
  val auto_level : int Config.T
  val reduce_auto_level : int -> Proof.context -> Proof.context

  exception Success of context_state
  exception Global_Cut of context_state

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
              -> (priority * context_state Seq.seq) list -> context_state Seq.seq
  (*Note it returns at most one state in the returned sequence.*)
  val reason_tac : int option (*N*)
                -> Proof.context (*the context for accessing reasoner db*)
                -> context_tactic
  
  val add_intro_rule : Position.T -> priority -> term list * term list -> thm
                    -> Context.generic -> Context.generic
  val add_intro_rules: (thm * Position.T * priority * term list * term list) list
                    -> Context.generic -> Context.generic
  val has_intro_rule : thm -> Context.generic -> bool
  val del_intro_rule : thm -> Context.generic -> Context.generic
  val attr_add_intro : (Position.T * (int * (term list * term list))) -> attribute
  val attr_del_intro : attribute

  val setup_cmd : (((string (*name term*) * Position.T) * priority)
                   * (bool (*true for matching, false for not matching*)
                      * string (*pattern term*)) list
                  ) * Input.source (* tactic source*)
        -> local_theory -> local_theory

  (* Default Pattern of Introduction Rule *)
  val add_default_pattern : (term (*pattern P*) * term (*the default pattern X*)) list
                         -> Context.generic -> Context.generic
      (*The default pattern of an introduction rule whose conclusion matches P is X.*)
  val remove_default_pattern : term * term -> Context.generic -> Context.generic
  val the_default_pattern_of : Context.generic -> term -> term
end


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

fun transform_reasoner phi ({name,pos,pattern,blacklist,tactic}:reasoner) =
  ({name=name, pos=pos, pattern = map (Morphism.term phi) pattern,
    blacklist = map (Morphism.term phi) blacklist, tactic = tactic}:reasoner)
  

(* Attributes *)
val auto_level = Attrib.setup_config_int \<^binding>\<open>\<phi>auto_level\<close> (K 2)
fun reduce_auto_level i = Config.map auto_level (fn j => Int.min (i,j))

val trace = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning\<close> (K false);
val trace_candidates = Attrib.setup_config_bool \<^binding>\<open>\<phi>trace_reasoning_candidates\<close> (K false);

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

fun error msg = Exn.error (msg ^ "\nReasoning Fail! You may turn on \<phi>reasoning_tracing and \
      \\<phi>reasoning_tracing_condidates to debug.")


exception Success  of context_state
exception Global_Cut of context_state
exception Local_Cut of (priority * Position.T * context_state Seq.seq)


(*** Reasoner Registry ***)
fun reasoner_eq ({name,pattern,...}, {name=name',pattern=pattern',...}) =
  (name = name')

structure Reasoners = Generic_Data (
  type T = reasoner Cost_Net.T;
  val empty : T = Cost_Net.init reasoner_eq #pattern;
  val extend = I;
  val merge : T * T -> T = Cost_Net.merge
)

fun reasoners ctxt = Cost_Net.content (Reasoners.get (Context.Proof ctxt)) |> map (apfst ~)
fun reasoner_net ctxt = Reasoners.get (Context.Proof ctxt)
fun add (priority,reasoner) = Reasoners.map (Cost_Net.update (~priority,reasoner));
fun adds reasoners = Reasoners.map (fold (Cost_Net.update o apfst (op ~)) reasoners)
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
    val (_,tms) = Pattern.match thy pat_obj (Vartab.empty, Vartab.empty)
  in Vartab.fold (fn ((name,_),(_,tm)) => fn flag =>
        if String.isPrefix "var_" name
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

fun call_tactics N ctxt tactics th =
  if Thm.nprems_of th <= N
  then raise Success (ctxt, th)
  else let
    val prop = Thm.prop_of th
    val tacs = concl_of_goal prop 1
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
                |> sort (int_ord o apply2 fst)
  in
    tacs 
      |> map_filter (fn (cost, r : reasoner) =>
          if cost <= ~1000000 then
            case Seq.pull (#tactic r (ctxt,th))
              of SOME (x,_) => raise Global_Cut x
               | _ => NONE
          else if cost <= ~1000 then
            case Seq.pull (#tactic r (ctxt,th))
              of SOME (x,s) => raise Local_Cut (cost, #pos r, Seq.cons x s)
               | _ => NONE
          else SOME (cost, #pos r, Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))))
        )
    handle Local_Cut ret => [ret]
  end

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
            val Z = (call_tactics N ctxt tactics th)
                  |> map (fn (a,b,c) => (a+cost,b,c))
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


(* Various Interfaces for Invoking Reasoning *)

fun gen_reason' N trace limit tactics states =
      gen_reason N trace limit 0 tactics (map (map (fn (a,b) => (~a,Position.none,b))) states)
      handle Success ret => SOME ret

fun num_of_protected_prems thm NONE = 0
  | num_of_protected_prems thm (SOME N) =
      if N >= 0 then Thm.nprems_of thm - N else ~N

fun reason (SOME 0) S = SOME S
  | reason N (ctxt,sequent) =
      gen_reason' (num_of_protected_prems sequent N)
                  (Config.get ctxt trace)
                  (Config.get ctxt step_limit)
                  (Reasoners.get (Context.Proof ctxt))
                  [[(0, Seq.single (ctxt, sequent))]]

fun reason1 G N stat =
      case reason N stat of SOME x => x
        | NONE => error (G ())

fun reason_s ctxt seqs = Seq.make (fn () =>
      gen_reason' 0
                  (Config.get ctxt trace)
                  (Config.get ctxt step_limit)
                  (Reasoners.get (Context.Proof ctxt))
                  [seqs]
        |> Option.map (rpair Seq.empty)
    )

fun reason_tac N ctxt stat = Seq.make (fn () =>
      gen_reason' (num_of_protected_prems (snd stat) N)
                  (Config.get ctxt trace)
                  (Config.get ctxt step_limit)
                  (Reasoners.get (Context.Proof ctxt))
                  [[(0, Seq.single stat)]]
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

fun pat_pat_eq ((a1,b1),(a2,b2)) = a1 aconv a2 andalso b1 aconv b2

structure Default_Pattern = Generic_Data (
  type T = (term (*pattern P*) * term (*the default pattern X*)) Net.net
  (*It gives the default pattern P of an introduction rule whose conclusion matches some pattern P*)
  val empty = Net.empty
(* Item_Net.init 
                            (single o fst) *)
  val merge = Net.merge pat_pat_eq
)

fun add_default_pattern pat_pats ctxt =
      Default_Pattern.map (fold (fn (p1,p2) =>
              Net.insert_term pat_pat_eq (p1,(p1,p2))) pat_pats) ctxt
      handle Net.INSERT => Exn.error ("Some pattern clashes with existing entries.")
fun remove_default_pattern (p1,p2) =
      Default_Pattern.map (Net.delete_term_safe pat_pat_eq (p1,(p1,p2)))

fun calc_pattern thy term (pat, pat_ret) =
 (SOME (Envir.subst_term (Pattern.match thy (pat, term) (Vartab.empty, Vartab.empty)) pat_ret))
  handle Pattern.MATCH => NONE

fun the_default_pattern_of ctxt term =
  Net.match_term (Default_Pattern.get ctxt) term
    |> map_filter (calc_pattern (Context.theory_of ctxt) term)
    |> (fn [] => term
         | [ret] => ret
         | ls => error (Pretty.string_of (Pretty.chunks (
                    [Pretty.str "Multiple default patterns are available:"] @
                    (map (Syntax.pretty_term (Context.proof_of ctxt)) ls) @
                    [Pretty.str "Fail to determine which pattern is preferable. \
                                \Please indicate the pattern manually using syntax \
                                \\<open>\<phi>reason for \<open>pattern\<close>\<close>"]
                 ))))

fun set_reason_rule_default_pattern_cmd raw_pat_pats lthy =
  let
    fun wrap2L f (x,y) = case f [x,y] of [x',y'] => (x',y')
    val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val pat_pats = map ( apply2 (Syntax.parse_prop ctxt_p)
                      #> wrap2L (Syntax.check_props ctxt_p)) raw_pat_pats
  in Local_Theory.declaration {syntax=false,pervasive=false} (fn phi =>
        add_default_pattern (map (apply2 (Morphism.term phi)) pat_pats)) lthy
  end

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>setup_reason_rule_default_pattern}
    "set the default pattern of a reasoning rule once its conclusion matches some pattern"
    (Parse.and_list1 (Parse.prop --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) -- Parse.prop)
      >> set_reason_rule_default_pattern_cmd)


(*** Reasoner for Introduction Reasoning Rule ***)

fun name_of_intro_reasoner rule = Free ("\<phi>Intro_Rule", \<^typ>\<open>prop \<Rightarrow> prop\<close>) $ Thm.prop_of rule
fun intro_reasoner ctxt pos priority patterns blacklist rule =
  let
    val rule = Thm.trim_context rule
    val pats = if null patterns
               then let val pat = the_default_pattern_of ctxt (Thm.concl_of rule)
                        val _ = debug_pretty_generic ctxt (fn () => Pretty.chunks [
                                Pretty.str "No pattern is given, use the default pattern:",
                                Syntax.pretty_term (Context.proof_of ctxt) pat
                            ])
                    in [pat] end
               else patterns
    val f_num = length (filter (fn \<^prop>\<open>\<r>Feasible\<close> => true | _ => false) (Thm.prems_of rule))
    val has_feasible =
          if f_num > 0 andalso priority < 1000
          then error ("Conditional \<r>Feasible only makes sense for assertive rule.")
          else if f_num > 1
          then error ("A reasoning rule can contain one \<r>Feasible antecedent at most.")
          else f_num > 0
  in {name = name_of_intro_reasoner rule,
      pos = pos,
      pattern = pats,
      blacklist = blacklist,
      tactic = (fn (ctxt, th) =>
          Seq.make (fn _ =>
            case Seq.pull (HEADGOAL (Tactic.resolve_tac ctxt [rule]) th)
              of SOME (ret, _) =>
                  if has_feasible
                  then reason NONE (ctxt, ret) |> Option.map (rpair Seq.empty)
                  else SOME ((ctxt, ret), Seq.empty)
               | _ => NONE))
      }
  end

fun add_intro_rule pos priority (pattern,blacklist) rule ctxt =
      add (priority, intro_reasoner ctxt pos priority pattern blacklist rule) ctxt
fun add_intro_rules rules ctxt =
  if null rules then ctxt
  else adds (map (fn (rule,pos,priority,pattern,blacklist) =>
              (priority, intro_reasoner ctxt pos priority pattern blacklist rule)) rules) ctxt
fun del_intro_rule rule = del (name_of_intro_reasoner rule)
fun has_intro_rule rule = has (name_of_intro_reasoner rule)

fun attr_add_intro (pos, (priority, (pattern, blacklist))) =
  Thm.declaration_attribute (add_intro_rule pos priority (pattern,blacklist))
val attr_del_intro = Thm.declaration_attribute del_intro_rule


val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>reason\<close>
(let open Args Scan Parse 
  fun read_prop_mode mode' ctxt tm = Syntax.read_prop (Proof_Context.set_mode mode' ctxt) tm
  val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
  val prop_pattern = Scan.repeat (Scan.peek (named_term o read_prop_pattern o Context.proof_of))
  fun pos_parser x = (Token.pos_of (hd x), x)
in
  (lift pos_parser --
  (lift (option add |-- ((\<^keyword>\<open>!\<close> >> K 2000000) || optional Parse.int 100))
      -- (optional (lift (\<^keyword>\<open>for\<close>) |-- prop_pattern) []
       -- optional (lift (\<^keyword>\<open>except\<close>) |-- prop_pattern) []))
        >> attr_add_intro)
  || (lift del >> K attr_del_intro)
end)
"Decalre or remove introduction rules in \<phi>-LPR."

#> Method.setup \<^binding>\<open>\<phi>reason\<close>
(let open Scan Parse in
  Scan.lift (Scan.option Parse.nat) --|
  Method.sections [
    Parse.position Args.add >> (fn (_,pos) =>
                                    Method.modifier (attr_add_intro (pos,(100,([],[])))) \<^here>),
    Args.del >> K (Method.modifier attr_del_intro \<^here>)
] >> (fn num_prems => fn ctxt => fn ths => reason_tac num_prems ctxt)
end)
"Apply \<phi>-LPR as a proof method."

)



end
