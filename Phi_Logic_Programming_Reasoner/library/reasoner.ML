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
  type reasoners

  type reasoner = {name: name,
                 pos: Position.T,
                 pattern: (pattern * priority) list,
                 blacklist: pattern list,
                 tactic: (context_state -> context_state Seq.seq)}


  val trace : int Config.T (*Prints the state of every reasoning step.*)
                     (*trace level: 0 - none; 1 - less info; 2 - more info; 3 - much more info*)
  val count_performance : bool Config.T
  val step_limit : int Config.T (*limit of the number of reasoning steps*)
  val info_print : Proof.context -> int (*level*) -> (unit -> string) -> unit
  val info_pretty: Proof.context -> int (*level*) -> (unit -> Pretty.T) -> unit
  val info_pretty_generic : Context.generic -> int (*level*) -> (unit -> Pretty.T) -> unit
  val error : string -> 'a
  val bad_config : string -> 'a

  (*auto level: 2 - fully auto, 1 - partially auto, 0 - fully manual*)
  val auto_level : int Config.T
  val reduce_auto_level : int -> Proof.context -> Proof.context

  exception Success of context_state
  exception Global_Cut of context_state

  structure Global_Cut_Handlers : PLPR_HANDLERS
  structure Success_Handlers : PLPR_HANDLERS
  val disable_global_cut : int -> string -> Proof.context -> serial * Proof.context
  val disable_success    : int -> string -> Proof.context -> serial * Proof.context

  val add : reasoner -> Context.generic -> Context.generic
  val add_lthy : reasoner -> local_theory -> local_theory
  val del_reasoners: term (*pattern*)
                  -> (reasoner -> bool) (*filter, returning true to delete one*)
                  -> Context.generic -> Context.generic
  val has_reasoner : term -> (reasoner -> bool) -> Context.generic -> bool
  val reasoners : Proof.context -> reasoners
  val content : reasoners -> reasoner list
  val get_reasoners : theory -> reasoners
                   -> term (*pattern*) -> reasoner list
  val pretty : Proof.context -> reasoner -> Pretty.T
  (*val call_reasoners : context_state -> (Position.T * context_state Seq.seq) list*)

  (* Interfaces for Reasoning *)
  (*N: number of premises to be attacked at most, if it is positive;
       to attack all if it is None;
       to attack until a sequent remains at most |N| premises, if N is negative*)
  val reason  : int option (*N*) -> context_state -> context_state option
  val reason1 : (unit -> string) (*error message*)
             -> int option (*N*) -> context_state -> context_state
  val reason_s : Proof.context (*the context for accessing reasoner db*)
              -> (Proof.context -> 'a * context_state Seq.seq list)
              -> 'a * context_state option
  (*Note it returns at most one state in the returned sequence.*)
  val reason_tac : int option (*N*)
                -> Proof.context (*the context for accessing reasoner db*)
                -> context_tactic

  (*The nested level of the current reasoning*)
  val nested_level : Proof.context -> int (*Starting from 1*)


  val add_intro_rule : Position.T -> priority -> (pattern * priority option) list * pattern list
                    -> (context_state -> bool) option
                    -> thm list
                    -> Context.generic -> Context.generic
  val add_intro_rules: (thm list * Position.T * priority * (pattern * priority option) list * pattern list
                       * (context_state -> bool) option) list
                    -> Context.generic -> Context.generic
  val attr_add_intro :
        ( ((Position.T * priority) * thm list)
        * ((pattern * priority option) list * pattern list))
        * (context_state -> bool) option
       -> attribute

  val setup_cmd : (((string (*name term*) * Position.T) * priority (*default priority*))
                   * ((bool (*true for matching, false for not matching*)
                      * string (*pattern term*))
                      * priority option) list
                  ) * Input.source (* tactic source*)
        -> local_theory -> local_theory

  (* Default Pattern of Introduction Rule *)
  val add_default_pattern :
                  (int (*priority*) * term (*pattern P*) * term (*the default pattern X*)) list
               -> Context.generic -> Context.generic
      (*The default pattern of an introduction rule whose conclusion matches P is X.*)
  val remove_default_pattern : int * term * term -> Context.generic -> Context.generic
  val the_default_pattern_of : Context.generic -> term -> term option

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
                 pattern: (term * int) list,
                 blacklist: term list,
                 tactic: (context_state -> context_state Seq.seq)}

val trick = map_aterms (fn Var ((s,i),T) => Var ((s, if String.isPrefix "var_" s then ~i - 1 else i),T)
                         | X => X)

fun normalize_reasoner f ({name,pos,pattern,blacklist,tactic}:reasoner) =
  ({name=name, pos=pos, pattern = map (fn (x,y) => (trick (Envir.beta_eta_contract x), f y)) pattern,
    blacklist = map (trick o Envir.beta_eta_contract) blacklist, tactic = tactic}:reasoner)

fun transform_reasoner phi ({name,pos,pattern,blacklist,tactic}:reasoner) =
  ({name=name, pos=pos,
    pattern = map (apfst (Morphism.term phi)) pattern,
    blacklist = map (Morphism.term phi) blacklist,
    tactic = tactic}:reasoner)


(* Attributes *)
val auto_level = Attrib.setup_config_int \<^binding>\<open>\<phi>auto_level\<close> (K 2)
fun reduce_auto_level i = Config.map auto_level (fn j => Int.min (i,j))

val trace = Attrib.setup_config_int \<^binding>\<open>\<phi>trace_reasoning\<close> (K 0);
val count_performance = Attrib.setup_config_bool \<^binding>\<open>\<phi>count_performance\<close> (K false);

val step_limit = Attrib.setup_config_int \<^binding>\<open>\<phi>reasoning_step_limit\<close> (K 1000);


(* Debug Info *)
fun info_pretty ctxt level G =
  if level <= Config.get ctxt trace
  then tracing (Pretty.string_of (G ()))
  else ()
fun info_print ctxt level G = info_pretty ctxt level (G #> Pretty.str)

fun info_pretty_generic ctxt level G =
  if 1 <= Config.get_generic ctxt trace
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
  type retT = (Position.T * context_state Seq.seq) list
  fun default s = raise Global_Cut s
  val current_level = nested_level
  val ctxt_of = fst
)

structure Success_Handlers = PLPR_Handlers(
  type domT = context_state
  type retT = (Position.T * context_state Seq.seq) list
  fun default s = raise Success s
  val current_level = nested_level
  val ctxt_of = fst
)

(*delt: 0 for the current reasoning context
        1 for the sub-calling environment*)
fun disable_global_cut delt msg = Global_Cut_Handlers.push_localctxt delt (fn _ => bad_config msg)
fun disable_success    delt msg = Success_Handlers.push_localctxt delt (fn _ => bad_config msg)

(*** Reasoner Registry ***)

(** Hasher **)

type reasoner_id = serial
fun hasher_eq ((_,s1),(_,s2)) = (s1 = s2)
val hasher_net = Synchronized.var "Phi_Reasoner.reasoner_hasher"
                                  (0, (Net.empty : (name * reasoner_id) Net.net))

fun hash name =
  Synchronized.change_result hasher_net (fn (N,net) =>
    case find_first (fn (x,_) => x = name) (Net.lookup net (Net.key_of_term name))
      of SOME (_,s) => (s, (N,net))
       | NONE => (N, (N+1, Net.insert_term (K false) (name, (name, N)) net))
  )


(** Main Registry **)
fun registry_eq ((c1,pat1,id1,_),(c2,pat2,id2,_))
      = (c1 = c2 andalso pat1 = pat2 andalso id1 = id2)
type reasoners = (priority * pattern * reasoner_id * reasoner) Net.net

structure Reasoners = Generic_Data (
  type T = reasoners
  val empty : T = Net.empty
  val merge : T * T -> T = Net.merge registry_eq
)

fun reasoners ctxt = Reasoners.get (Context.Proof ctxt)
fun content net = Net.content net |> map (fn (_,_,_,r) => r)

fun pretty ctxt (r:reasoner) =
  Pretty.chunks (
    Pretty.block (Pretty.here (#pos r) @ [Pretty.str " ", Syntax.pretty_term ctxt (#name r)]) ::
    map (fn (pat,n) => Pretty.item [
          Pretty.str "(", Pretty.str (string_of_int n), Pretty.str "): ",
          Syntax.pretty_term ctxt pat
        ]) (#pattern r)
  )

fun pretty' ctxt (priority, pat, _, (r:reasoner)) =
   Pretty.block (
     Pretty.here (#pos r) @
    [Pretty.str "(", Pretty.str (string_of_int priority), Pretty.str ") on pattern ",
     Syntax.pretty_term ctxt pat, Pretty.str " : ",
     Pretty.fbrk,
     Syntax.pretty_term ctxt (#name r)])


fun insert_net ctxt (reasoner:reasoner) (pat,priority) net =
  let val x = (priority, pat, hash (#name reasoner), reasoner)
   in Net.insert_term registry_eq (pat, x) net
      handle Net.INSERT =>
        let val dups = Net.lookup net (Net.key_of_term pat)
                   |> filter (fn y => registry_eq (x,y))
            val ctxt' = Context.proof_of ctxt
         in Exn.error (Pretty.string_of (Pretty.chunks (
              Pretty.str "Clash with existing reasoner!" ::
              map (fn d => pretty' ctxt' d) dups
           )))
        end
  end

fun add reasoner0 ctxt =
  let val reasoner = normalize_reasoner I reasoner0
      val _ = info_pretty_generic ctxt 2 (fn () =>
                Pretty.chunks [Pretty.str "Installing \<phi>-LPR reasoner:",
                               pretty (Context.proof_of ctxt) reasoner])
   in Reasoners.map (fold (insert_net ctxt reasoner) (#pattern reasoner)) ctxt
  end

fun adds reasoners ctxt = Reasoners.map (
      fold (fn reasoner0 =>
        let val reasoner = normalize_reasoner I reasoner0
            val _ = info_pretty_generic ctxt 2 (fn () =>
                Pretty.chunks [Pretty.str "Installing \<phi>-LPR reasoner:",
                               pretty (Context.proof_of ctxt) reasoner])
         in fold (insert_net ctxt reasoner) (#pattern reasoner)
        end) reasoners) ctxt

fun add_lthy reasoner =
  Local_Theory.declaration {syntax=false, pervasive=false} (fn phi =>
    add (transform_reasoner phi reasoner)
  )

(*** Implementing Functions ***)

(* Main Reasoning Function *)

fun debug ctxt (c,_,_,(r : reasoner as {name,...})) =
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

(* fun beta_eta_contract_leading_antecedent th =
  if (case Thm.prop_of th
        of \<^const>\<open>Pure.imp\<close> $ X $ _ => Term.could_beta_eta_contract X
         | _ => false)
  then Thm.equal_elim (Conv.implies_conv Drule.beta_eta_conversion
                                         Conv.all_conv (Thm.cprop_of th)) th
  else th *)

fun distinct_rev eq lst =
  let
    fun dist (rev_seen, []) = rev_seen
      | dist (rev_seen, x :: xs) =
          if member eq xs x then dist (rev_seen, xs)
          else dist (x :: rev_seen, xs);
  in dist ([], lst) end;


fun get_reasoners' thy tactics term =
  Net.match_term tactics term
    |> filter (fn (_,pat,_,reasoner) =>
        match_term thy (pat,term)
        andalso forall (fn pat =>
          not (match_term thy (pat,term)))
        (#blacklist reasoner))
    |> sort (fn ((c1,_,_,_),(c2,_,_,_)) => int_ord (c1,c2))
    |> distinct_rev (fn (a,b) => #3 a = #3 b)

fun get_reasoners thy tactics term =
      get_reasoners' thy tactics term |> map (fn (_,_,_,r) => r)


fun del_reasoners pattern filter ctxt =
  Reasoners.map (fn all_reasoners =>
    let val to_remove = Net.match_term all_reasoners pattern
                     |> List.filter (fn (_,_,_,r) => filter r)
     in fold (fn (c,p,id,R) => Net.delete_term registry_eq (p, (c,p,id,R)))
             to_remove all_reasoners
    end) ctxt

fun has_reasoner pattern filter ctxt =
  Net.match_term (Reasoners.get ctxt) pattern
    |> exists (fn (_,_,_,r) => filter r)

fun gen_call_reasoners trace score tactics ctxt th =
  Thm.major_prem_of th
    |> Envir.beta_eta_contract
    |> get_reasoners' (Proof_Context.theory_of ctxt) tactics
    |> (if 3 <= trace
        then (fn rs => (List.app (debug ctxt) rs; rs))
        else I)
    |> map_filter (fn (priority, _, _, r : reasoner) =>
        if priority >= 1000000 then
          case Seq.pull (#tactic r (ctxt,th))
            of SOME (x,_) => raise Global_Cut x
             | _ => NONE
        else if priority >= 1000 then
          case Seq.pull (#tactic r (ctxt,th))
            of SOME (x,s) => raise Local_Cut (score + priority, #pos r, Seq.cons x s)
             | _ => NONE
        else SOME (priority + score, #pos r, Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))))
      )
  handle Local_Cut (s,pos,seq) => [(s,pos,seq)]
       | Success s => Success_Handlers.invoke (fst s) s
                   |> map (fn (x,y) => (score,x,y))
       | Global_Cut s => Global_Cut_Handlers.invoke (fst s) s
                      |> map (fn (x,y) => (score,x,y))

fun call_reasoners' trace score N ctxt tactics th =
  if Thm.nprems_of th <= N
  then raise Success (ctxt, th)
  else gen_call_reasoners trace score tactics ctxt th

(*fun call_reasoners (ctxt,th) =
  gen_call_reasoners (Config.get ctxt trace) (Reasoners.get (Context.Proof ctxt)) ctxt th *)


fun gen_reason _ _ _ _ _ [] = NONE
  | gen_reason N trace limit iter tactics ([]::L) =
      (if 2 <= trace then tracing ("Backtracking...") else ();
       gen_reason N trace limit iter tactics L)
  | gen_reason N trace limit iter tactics (((score,pos,seq)::L')::L) =
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
            val _ = if 2 <= trace
                    then tracing ("\<phi>reasoning("^string_of_int score^"):"^
                                  Position.here pos ^"\n" ^ Thm.string_of_thm ctxt th)
                    else ()
            val Z = (call_reasoners' trace score N ctxt tactics th)
                  |> (fn Z => Z::(
                        let val t = if pointer_eq (seq',Seq.empty) then L' else (score,pos,seq')::L'
                        in if null t then L else t::L end))
                handle Success ret => raise Success ret
                     | Global_Cut stat =>
                        let
                          val _ = if 2 <= trace
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
                 (map (map (fn seq => (0, Position.none, seq))) states)
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
                  [[Seq.single (enter_reasoning_envir ctxt, sequent)]]

fun reason1 G N stat = case reason N stat of SOME x => x | NONE => error (G ())

fun reason_s ctxt seqs =
  let val (ret,seqs') = seqs (enter_reasoning_envir ctxt)
   in (ret, gen_reason' ctxt 0 [seqs'])
  end

fun reason_tac N ctxt stat = Seq.make (fn () =>
      gen_reason' ctxt (num_of_protected_prems (snd stat) N)
                  [[Seq.single (apfst enter_reasoning_envir stat)]]
       |> Option.map (rpair Seq.empty o Seq.Result)
    )



(*** Command Interface ***)

fun setup_method_cmd (((name,priority), raw_patterns),method) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val terms = map (fn ((_,x),_) => x) raw_patterns
             |> Syntax.read_props ctxt
    val patterns = map2 (fn ((flag,_),c) => fn tm => (flag,(tm, the_default priority c)))
                        raw_patterns terms
    val pos_pats = patterns |> map_filter (fn (sgn, pat) => if sgn then SOME pat else NONE)
    val neg_pats = patterns |> map_filter (fn (sgn, (pat,_)) => if sgn then NONE else SOME pat)
    val name' = Free(Binding.name_of name, dummyT)

    val (method',lthy') = Method_Closure.method_cmd name [] [] [] [] method lthy
    val method'' = Method_Closure.apply_method lthy' method' [] [] []
    val method'''= (fn (ctxt,thm) => method'' ctxt [] (ctxt,thm) |> Seq.filter_results)
  in add_lthy {name=name', pos=Binding.pos_of name,
               pattern=pos_pats, blacklist=neg_pats, tactic=method'''} lthy'
  end

fun setup_cmd ((((name,pos),priority),raw_patterns),tactic_src) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val name = Syntax.read_term lthy name
    val terms = map (fn ((_,x),_) => x) raw_patterns
             |> Syntax.read_props ctxt
    val patterns = map2 (fn ((flag,_),c) => fn tm => (flag,(tm, the_default priority c)))
                        raw_patterns terms
    val pos_pats = patterns |> map_filter (fn (sign, pat) => if sign then SOME pat else NONE)
    val neg_pats = patterns |> map_filter (fn (sign, (pat,_)) => if sign then NONE else SOME pat)
    open ML_Syntax
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of tactic_src)
        (ML_Lex.read
          ("Theory.local_setup (Phi_Reasoner.add_lthy {name=(" ^
          print_term name ^ "), pos=("^
          print_position pos ^ "), pattern=(" ^
          print_list (print_pair print_term print_int) pos_pats
          ^ "), blacklist=("^
          print_list print_term neg_pats
          ^"), tactic=(let in ") @
          ML_Lex.read_source tactic_src @
          ML_Lex.read (" end):(context_state -> context_state Seq.seq)})"))
    )
  end

val patterns = Parse.$$$ "(" |-- Parse.enum "|"
      (Scan.optional (\<^keyword>\<open>except\<close> >> K false) true -- Parse.term
                -- Scan.option (\<^keyword>\<open>(\<close> |-- Parse.int --| \<^keyword>\<open>)\<close>))
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

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_\<phi>reasoners\<close>
    "print \<phi>reasoner matching the given pattern"
    (Parse.term -- (Scan.optional (Args.query >> K false) true) >> (fn (raw_pattern, strict) =>
      Toplevel.keep (fn top =>
        let val ctxt = Toplevel.context_of top
            val pattern = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt) raw_pattern
            val all_reasoners = Reasoners.get (Context.Proof ctxt)
            val reasoners = if strict
                            then get_reasoners' (Proof_Context.theory_of ctxt) all_reasoners pattern
                            else Net.match_term all_reasoners pattern
                                  |> sort (fn ((c1,_,_,_),(c2,_,_,_)) => int_ord (c1,c2))
         in if null reasoners
            then writeln "No reasoner found."
            else writeln (Pretty.string_of (Pretty.chunks
                              (map (fn (_,_,_,r) => pretty ctxt r) reasoners)))
        end)));


(*** Default Pattern for Introduction Reasoning Rule ***)

structure Default_Pattern = Pattern_Translation (
  val multi_translation_err_msg = "Fail to determine which pattern is preferable. \
                                \Please indicate the pattern manually using syntax \
                                \\<open>\<phi>reason for \<open>pattern\<close>\<close>"
)

val add_default_pattern = Default_Pattern.add
val remove_default_pattern = Default_Pattern.remove
val the_default_pattern_of = Default_Pattern.translate

val _ = Theory.setup (Default_Pattern.setup_attribute \<^binding>\<open>\<phi>reason_default_pattern\<close>
          "set the default pattern of a reasoning rule once its conclusion matches some pattern")

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
  (*Free ("\<phi>Intro_Rule", \<^typ>\<open>prop \<Rightarrow> prop\<close>) $ *) Logic.mk_conjunction_list (map Thm.prop_of rules)

fun intro_reasoner ctxt pos (priority:priority) patterns blacklist guard rules =
  let
    val rules = rules
             |> filter (fn th => not (Thm.is_free_dummy th orelse Thm.is_dummy th))
             |> Drule.zero_var_indexes_list
             |> map Thm.trim_context
    val _ = if null rules then error ("No rule is given!") else ()
    val pats = if null patterns
               then case rules
                      of [rule] =>
                        let val concl = Thm.concl_of rule
                            val pat = the_default concl (the_default_pattern_of ctxt concl)
                            val _ = info_pretty_generic ctxt (fn () => Pretty.chunks [
                                    Pretty.str "No pattern is given, use the default pattern:",
                                    Syntax.pretty_term (Context.proof_of ctxt) pat
                                ])
                        in [(pat,priority)] end
                       | _ => error "Pattern of the reasoner is required"
               else map (apsnd (the_default priority)) patterns

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
                        else (rule, is_Require r)
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
      add (intro_reasoner ctxt pos priority pattern blacklist guard rules) ctxt
fun add_intro_rules rules ctxt =
  if null rules then ctxt
  else adds (map (fn (rule,pos,priority,pattern,blacklist,guard) =>
              intro_reasoner ctxt pos priority pattern blacklist guard rule) rules) ctxt

fun attr_add_intro ((((pos, priority), additional_rules), (pattern, blacklist)), guard) =
  Thm.declaration_attribute (fn rule =>
      add_intro_rule pos priority (pattern,blacklist) guard (rule::additional_rules))



val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>reason\<close>
(let open Args Scan Parse
  fun read_prop_mode mode' ctxt tm = Syntax.read_prop (Proof_Context.set_mode mode' ctxt) tm
  val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
  val prop_pattern = Scan.peek (named_term o read_prop_pattern o Context.proof_of)
  val pos_parser = Phi_Reasoner_Helpers.pos_parser "\<phi>reasoner"
  val ML_guard = depend (fn ctxt0 => ML_source >> (fn src =>
       let val ctxt = Context.Proof (Context.proof_of ctxt0)
            |> ML_Context.expression (Input.pos_of src)
              (ML_Lex.read "Theory.local_setup (PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.put (" @
               ML_Lex.read_source src @
               ML_Lex.read "))")
       in (ctxt0, PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.get (Context.the_proof ctxt)) end
     ))
  val priority = Scan.lift (Scan.option (\<^keyword>\<open>(\<close> |-- Parse.int --| \<^keyword>\<open>)\<close>))
in
  (lift pos_parser
  -- lift (option add |-- ((\<^keyword>\<open>!\<close> >> K 2000000) || optional Parse.int 100))
  -- Attrib.thms
  -- ( optional (lift (\<^keyword>\<open>for\<close>) |-- Scan.repeat (prop_pattern -- priority)) []
    -- optional (lift (\<^keyword>\<open>except\<close>) |-- Scan.repeat prop_pattern) [])
  -- option (lift \<^keyword>\<open>if\<close> |-- ML_guard)
  >> attr_add_intro)
end)
"Decalre or remove introduction rules in \<phi>-LPR."

#> Method.setup \<^binding>\<open>\<phi>reason\<close>
(let open Scan Parse in
  Scan.lift (Scan.option Parse.nat) --|
  Method.sections [
    Parse.position Args.add >> (fn (_,pos) =>
               Method.modifier (attr_add_intro ((((pos,100),[]),([],[])),NONE)) \<^here>)
] >> (fn num_prems => fn ctxt => fn ths => reason_tac num_prems ctxt)
end)
"Apply \<phi>-LPR as a proof method."

)



end
