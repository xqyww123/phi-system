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
  type ML_guard = context_state -> bool
  type action = cterm

  datatype cut_mode = NO_CUT | LOCAL_CUT | GLOBAL_CUT
  datatype backtrack_mode = ADMIT_BACKTRACK | NO_BACKTRACK | NO_EXPLORATIVE_BACKTRACK
  type mode = cut_mode * backtrack_mode
  (* declare by NO_BACKTRACK to disable applying the reasoner during backtracking.
        It causes the reasoner will not be applied once there is another reasoner of a higher priority,
        no matter if that reasoner's application succeeds.
        It is therefore useful to declare `default' rules which works when user does not give any
        specific rule and to be overrided once any rule is given.

     In exhaustive reasoning mode, in order to obtain all reachable solution of a reasoning goal,
     the reasoning will not terminate even when a success is reached. Instead, a special `explorative'
     backtrack is triggered to backtrack to other branches.
     NO_EXPLORATIVE_BACKTRACK disables the rule to be applied in this explorative backtracking.
     It can be for consideration of performance.
 *)
  val NORMAL_MODE : mode
  val NORMAL_LOCAL_CUT : mode
  val TO_BE_OVERRIDE : mode


  datatype backtracking = NO_BACKTRACKING | BACKTRACKING | EXPLORATIVE_BACKTRACKING
  datatype tactic = Tac_ML of backtracking * context_state -> context_state Seq.seq | Tac_Rule of thm list
  type reasoner = {name: term,
                   pos: Position.T,
                   mode: mode,
                   pattern: (term * int) list,
                   blacklist: term list,
                   tactic: tactic}
  val match_reasoner : theory -> term -> reasoner -> bool


  val trace : int Config.T (*Prints the state of every reasoning step.*)
                     (*trace level: 0 - none; 1 - less info; 2 - more info; 3 - much more info*)
  val count_performance : bool Config.T
  val step_limit : int Config.T (*limit of the number of reasoning steps*)
  val info_print : Proof.context -> int (*level*) -> (unit -> string) -> unit
  val info_pretty: Proof.context -> int (*level*) -> (unit -> Pretty.T) -> unit
  val info_pretty_generic : Context.generic -> int (*level*) -> (unit -> Pretty.T) -> unit
  val warn_pretty: Context.generic -> int (*level*) -> (unit -> Pretty.T) -> unit
  val error : string -> 'a
  val bad_config : string -> 'a

  val pretty_mode : mode -> Pretty.T option
  val pretty_mode_priority : mode * priority -> Pretty.T

  (*auto level: 2 - fully auto, 1 - partially auto, 0 - fully manual*)
  val auto_level : int Config.T
  val reduce_auto_level : int -> Proof.context -> Proof.context

  exception Success of context_state
  exception Global_Cut of context_state
  exception Explorative_Backtrack

  structure Global_Cut_Handlers : PLPR_HANDLERS
  structure Success_Handlers : PLPR_HANDLERS
  val disable_global_cut : int -> string -> Proof.context -> serial * Proof.context
  val disable_success    : int -> string -> Proof.context -> serial * Proof.context

  val add : reasoner -> Context.generic -> Context.generic
  val adds : reasoner list -> Context.generic -> Context.generic
  val add_lthy : reasoner -> local_theory -> local_theory
  val del_reasoners: term (*pattern*)
                  -> (reasoner -> bool) (*filter, returning true to delete one*)
                  -> Context.generic -> Context.generic
  val del_reasoners_by_name: term (*pattern matching the name*)
                  -> Context.generic -> Context.generic
  val has_reasoner : pattern -> (reasoner -> bool) -> Context.generic -> bool
  val reasoners : Proof.context -> reasoners
  val content : reasoners -> reasoner list
  (*val call_reasoners : reasoners -> Proof.context -> *)
  val get_reasoners : theory -> reasoners -> pattern -> reasoner list
  (*a faster version but a bit dirty*)
  val get_reasoners' : theory -> reasoners
                    -> pattern -> (priority * pattern * serial (*reasoner id*) * reasoner) list
  val pretty : Proof.context -> reasoner -> Pretty.T
  val apply_tactic : backtracking -> tactic -> context_state -> context_state Seq.seq
  (*val call_reasoners : context_state -> (Position.T * context_state Seq.seq) list*)

  (* Interfaces for Reasoning *)
  (*N: number of premises to be attacked at most, if it is positive;
       to attack all if it is None;
       to attack until a sequent remains at most |N| premises, if N is negative*)
  val internal_reason  : int option (*N*)
             -> bool (*if to open new context*)
             -> context_state -> context_state option
  val reason  : int option (*N*)
             -> bool (*if to open new context. It affects the scope of Success and Global_Cut handlers.
                       Set to true if you are initiating a fresh new work, or false if it is just a sub-part of
                       the on-going work.*)
             -> Proof.context -> thm -> thm option
  val reason1 : (unit -> string) (*error message*)
             -> int option (*N*)
             -> bool (*if to open new context*)
             -> Proof.context -> thm -> thm
  val internal_reason_s :
                 bool (*if to open new context*)
              -> Proof.context (*the context for accessing reasoner db*)
              -> (Proof.context -> 'a * context_state Seq.seq)
              -> 'a * context_state option
  val reason_sXXX : bool (*if to open new context*)
              -> Proof.context (*the context for accessing reasoner db*)
              -> (Proof.context -> 'a * context_state Seq.seq)
              -> 'a * thm option
  (*Note it returns at most one state in the returned sequence.*)
  val reason_tac : int option (*N*)
                -> bool (*if to open new context*)
                -> Proof.context (*the context for accessing reasoner db*)
                -> context_tactic

  (*The nested level of the current reasoning*)
  val nested_level : Proof.context -> int (*Starting from 1*)

  type guard = context_state -> bool
  val default_mode_of : priority -> cut_mode
  val add_rule : Position.T -> mode -> priority
                    -> (pattern * priority option) list * pattern list
                    -> guard option
                    -> thm list
                    -> Context.generic -> Context.generic
  val add_rules: (thm list * Position.T * mode * priority
                       * (pattern * priority option) list * pattern list
                       * (context_state -> bool) option) list
                    -> Context.generic -> Context.generic

  type pass_data = thm list (*rules*) * (mode * priority) * ((pattern * priority option) list * pattern list) * guard option * Context.generic
  type rule_pass = Position.T -> pass_data -> pass_data
  val get_passes : Context.generic -> term list -> (string * term * rule_pass) list
  val run_passes : Position.T -> pass_data -> pass_data
  val add_pass : string (*identifier*) * pattern * rule_pass -> Context.generic -> Context.generic

  val setup_cmd : (((string (*name term*) * Position.T) * (mode * priority (*default priority*)))
                   * ((bool (*true for matching, false for not matching*)
                      * string (*pattern term*))
                      * priority option) list
                  ) * Input.source (* tactic source*)
        -> local_theory -> local_theory

  (* Default Pattern of Reasoning Rule *)
  structure Default_Pattern : PATTERN_REWRITE
  val the_default_pattern_of : Context.generic -> term -> term list

  (* Helpful Tools *)
  val chop_seq_head' : 'a Seq.seq -> 'a option
  val chop_seq_head  : 'a Seq.seq -> 'a Seq.seq
  val single_RS' : thm (*rule*) -> Proof.context -> thm -> thm option
  val single_RS  : thm (*rule*) -> Proof.context -> thm -> thm Seq.seq
        (*The resolution that returns at most one solution.*)

  val attr_syntax :
      'ext context_parser (*extension*) ->
      (Position.T * mode * priority * 'ext
        * ((pattern * priority option) list * pattern list) * ML_guard option
       -> attribute)
     -> attribute context_parser

  val attr_rule_syntax : (thm list * Context.generic -> thm list * Context.generic) ->  attribute context_parser

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
type ML_guard = context_state -> bool
type action = cterm

datatype cut_mode = NO_CUT | LOCAL_CUT | GLOBAL_CUT
datatype backtrack_mode = ADMIT_BACKTRACK | NO_BACKTRACK | NO_EXPLORATIVE_BACKTRACK
type mode = cut_mode * backtrack_mode

val NORMAL_MODE = (NO_CUT, ADMIT_BACKTRACK)
val NORMAL_LOCAL_CUT = (LOCAL_CUT, ADMIT_BACKTRACK)
val TO_BE_OVERRIDE = (NO_CUT, NO_BACKTRACK)


datatype backtracking = NO_BACKTRACKING | BACKTRACKING | EXPLORATIVE_BACKTRACKING
datatype tactic = Tac_ML of backtracking * context_state -> context_state Seq.seq | Tac_Rule of thm list
type reasoner = {name: term,
                 pos: Position.T,
                 mode: mode,
                 pattern: (term * int) list,
                 blacklist: term list,
                 tactic: tactic}

fun normalize_reasoner f ({name,pos,mode,pattern,blacklist,tactic}:reasoner) =
  ({name=name, pos=pos, mode=mode,
    pattern = map (fn (x,y) => (Pattern_Translation.mk_pattern (Envir.beta_eta_contract x), f y)) pattern,
    blacklist = map (Pattern_Translation.mk_pattern o Envir.beta_eta_contract) blacklist,
    tactic = tactic}:reasoner)

fun transform_reasoner phi ({name,pos,mode,pattern,blacklist,tactic}:reasoner) =
  ({name=name, pos=pos, mode=mode,
    pattern = map (apfst (Morphism.term phi)) pattern,
    blacklist = map (Morphism.term phi) blacklist,
    tactic = tactic}:reasoner)

fun print_cut_mode_ML NO_CUT = "Phi_Reasoner.NO_CUT"
  | print_cut_mode_ML LOCAL_CUT = "Phi_Reasoner.LOCAL_CUT"
  | print_cut_mode_ML GLOBAL_CUT = "Phi_Reasoner.GLOBAL_CUT"

fun print_backtrack_mode_ML ADMIT_BACKTRACK = "Phi_Reasoner.ADMIT_BACKTRACK"
  | print_backtrack_mode_ML NO_BACKTRACK = "Phi_Reasoner.NO_BACKTRACK"
  | print_backtrack_mode_ML NO_EXPLORATIVE_BACKTRACK = "Phi_Reasoner.NO_EXPLORATIVE_BACKTRACK"

val print_mode_ML = ML_Syntax.print_pair print_cut_mode_ML print_backtrack_mode_ML

fun name_of_intro_reasoner rules = Logic.mk_conjunction_list (map Thm.prop_of rules)
fun match_reasoner_name thy pattern name =
  let val name_concls = Logic.dest_conjunction_list name
                     |> map Logic.strip_assums_concl
   in exists (fn X => Pattern_Translation.does_match_term thy (pattern, X)) name_concls
  end
fun match_reasoner thy pattern reasoner = match_reasoner_name thy pattern (#name reasoner)

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
  if level <= Config.get_generic ctxt trace
  then tracing (Pretty.string_of (G ()))
  else ()

fun warn_pretty ctxt level G =
  if level <= Config.get_generic ctxt trace
  then warning (Pretty.string_of (G ()))
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
fun enter_reasoning_envir' opewn_newctxt ctxt =
  if opewn_newctxt then enter_reasoning_envir ctxt else ctxt
fun exit_reasoning_envir' opewn_newctxt ctxt =
  if opewn_newctxt then exit_reasoning_envir ctxt else ctxt

val nested_level = Environ.get

(* Cut, Abrupt Termination, and Handlers *)

exception Success    of context_state
exception Global_Cut of context_state
exception Explorative_Backtrack

structure Global_Cut_Handlers = Local_Handlers(
  type domT = context_state
  type retT = (Position.T * context_state Seq.seq) list
  fun default s = raise Global_Cut s
  val current_level = nested_level
  val ctxt_of = fst
)

structure Success_Handlers = Local_Handlers(
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
(*fun hasher_eq ((_,s1),(_,s2)) = (s1 = s2)*)
val hasher_net = Synchronized.var "Phi_Reasoner.reasoner_hasher"
                                  (0, (iNet.empty : (name * reasoner_id) iNet.net))

fun hash name =
  Synchronized.change_result hasher_net (fn (N,net) =>
    case find_first (fn (x,_) => x = name) (iNet.lookup net (iNet.key_of_term name))
      of SOME (_,s) => (s, (N,net))
       | NONE => (N, (N+1, iNet.insert_term (K false) (name, (name, N)) net))
  )


(** Main Registry **)
fun registry_eq ((c1,pat1,id1,_),(c2,pat2,id2,_))
      = (c1 = c2 andalso pat1 = pat2 andalso id1 = id2)
type reasoners = (priority * pattern * reasoner_id * reasoner) iNet.net

structure Reasoners = Generic_Data (
  type T = reasoners
  val empty : T = iNet.empty
  val merge : T * T -> T = iNet.merge registry_eq
)

fun reasoners ctxt = Reasoners.get (Context.Proof ctxt)
fun content net = iNet.content net |> map (fn (_,_,_,r) => r)

fun pretty_mode (cmode, bmode) =
  let open Pretty
      val b = case bmode of ADMIT_BACKTRACK => NONE
                          | NO_BACKTRACK => SOME (str "default")
                          | NO_EXPLORATIVE_BACKTRACK => SOME (para "no explorative backtrack")
      val c = case cmode of NO_CUT => NONE
                          | LOCAL_CUT => SOME (str "!")
                          | GLOBAL_CUT => SOME (str "!!")
   in case (b,c)
   of (SOME pb, SOME pc) => SOME (block [pb, pc])
    | (NONE, SOME pc) => SOME pc
    | (SOME pb, NONE) => SOME pb
    | _ => NONE
  end

fun pretty_mode_priority (mode, priority) =
  let open Pretty
   in block ( [str "(", str (string_of_int priority)]
            @ the_list (pretty_mode mode)
            @ [str ")"] )
  end

fun pretty ctxt (r:reasoner) = let open Pretty in
  Pretty.chunks (
    Pretty.block (Pretty.here (#pos r) @ [brk 1, Syntax.pretty_term ctxt (#name r)]) ::
    map (fn (pat,n) => Pretty.item [
          str "(", str (string_of_int n), str "): ",
          Syntax.pretty_term ctxt pat
        ]) (#pattern r)
  ) end

fun pretty' ctxt (priority, pat, _, (r:reasoner)) =
   Pretty.block (
     Pretty.here (#pos r) @
    [Pretty.str "(", Pretty.str (string_of_int priority), Pretty.str ") on pattern ",
     Syntax.pretty_term ctxt pat, Pretty.str " : ",
     Pretty.fbrk,
     Syntax.pretty_term ctxt (#name r)])


fun insert_net ctxt (reasoner:reasoner) (pat,priority) net =
  let val x = (priority, pat, hash (#name reasoner), reasoner)
      fun chk pat = case Term.fastype_of pat
                      of Type(\<^type_name>\<open>prop\<close>, _) => ()
                       | _ => error "Bad reasoner, the pattern must be a proposition"
      val _ = List.app (chk o fst) (#pattern reasoner)
      val _ = List.app chk (#blacklist reasoner)
   in iNet.insert_term registry_eq (pat, x) net
      handle iNet.INSERT =>
        let val dups = iNet.lookup net (iNet.key_of_term pat)
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
      val _ = info_pretty_generic ctxt 1 (fn () =>
                Pretty.chunks [Pretty.str "Installing \<phi>-LPR reasoner:",
                               pretty (Context.proof_of ctxt) reasoner])
   in Reasoners.map (fold (insert_net ctxt reasoner) (#pattern reasoner)) ctxt
  end

fun adds reasoners ctxt = Reasoners.map (
      fold (fn reasoner0 =>
        let val reasoner = normalize_reasoner I reasoner0
            val _ = info_pretty_generic ctxt 1 (fn () =>
                Pretty.chunks [Pretty.str "Installing \<phi>-LPR reasoner:",
                               pretty (Context.proof_of ctxt) reasoner])
         in fold (insert_net ctxt reasoner) (#pattern reasoner)
        end) reasoners) ctxt

fun add_lthy reasoner =
  Local_Theory.declaration {syntax=false, pervasive=false} (fn phi =>
    add (transform_reasoner phi reasoner)
  )

(*** Implementing Functions ***)

(* Auxiliary Helpers *)

fun chop_seq_head' seq =
  case Seq.chop 2 seq
    of ([ret], _) => SOME ret
       | ([], _) => NONE
       | (ret::_, _) => (warning "Multi Resolution! For performance consideration, PLPR only takes\
                                 \ the first solution and discards the remains.";
                         SOME ret)

fun chop_seq_head seq =
  Seq.make (fn _ => Option.map (rpair Seq.empty) (chop_seq_head' seq))

fun single_RS' rule ctxt thm =
  Thm.biresolution (SOME ctxt) false [(false,rule)] 1 thm
    |> chop_seq_head'

fun single_RS rule ctxt thm =
  Seq.make (fn _ => Option.map (rpair Seq.empty) (single_RS' rule ctxt thm))


type guard = context_state -> bool

(* Main Reasoning Function *)

fun debug ctxt (c,_,_,({name,pos,...} : reasoner)) = let open Pretty in
      tracing (string_of (chunks [
        block ([str "candidate reasoners (", str (string_of_int c), str "): "] @ here pos),
        Syntax.pretty_term (Proof_Context.set_mode Proof_Context.mode_abbrev ctxt) name
      ]))
  end

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

fun apply_tactic bmode (Tac_ML tac) s = tac (bmode, s)
  | apply_tactic _ (Tac_Rule []) (ctxt,sequent) = Seq.empty
  | apply_tactic _ (Tac_Rule [rule]) (ctxt,sequent) = Seq.make (fn () =>
        case single_RS' rule ctxt sequent
          of SOME ret => SOME ((ctxt, ret), Seq.empty)
           | NONE => NONE)
  | apply_tactic _ (Tac_Rule rules) (ctxt,sequent) =
           Seq.of_list rules
        |> Seq.map_filter (fn rule => Option.map (pair ctxt) (single_RS' rule ctxt sequent))

fun get_reasoners' thy tactics term =
  iNet.match_term tactics term
    |> filter (fn (_,pat,_,reasoner) =>
        Pattern_Translation.does_match_term thy (pat,term)
        andalso forall (fn pat =>
          not (Pattern_Translation.does_match_term thy (pat,term)))
        (#blacklist reasoner))
    |> sort (fn ((c1,_,_,_),(c2,_,_,_)) => int_ord (c1,c2))
    |> distinct_rev (fn (a,b) => #3 a = #3 b)

fun get_reasoners thy tactics term =
      get_reasoners' thy tactics term |> map (fn (_,_,_,r) => r)

fun del_reasoners pattern filter ctxt =
  Reasoners.map (fn all_reasoners =>
    let val to_remove = iNet.unify_term all_reasoners pattern
                     |> List.filter (fn (_,_,_,r) => filter r)
     in fold (fn (c,p,id,R) => iNet.delete_term registry_eq (p, (c,p,id,R)))
             to_remove all_reasoners
    end) ctxt

fun del_reasoners_by_name pattern ctxt =
      del_reasoners pattern (match_reasoner (Context.theory_of ctxt) pattern) ctxt

fun has_reasoner pattern filter ctxt =
  iNet.unify_term (Reasoners.get ctxt) pattern
    |> exists (fn (_,_,_,r) => filter r)

(*
fun gen_call_reasoners trace score tactics ctxt th =
  Thm.major_prem_of th
    |> Envir.beta_eta_contract
    |> get_reasoners' (Proof_Context.theory_of ctxt) tactics
    |> 3 <= trace ? (fn rs => (List.app (debug ctxt) rs; rs))
    |> map (fn (priority, _, _, r : reasoner) =>
          (priority + score, #pos r, #mode r, #tactic r (ctxt,th)
                    (* Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))) *))) *)
    (*|> map_filter (fn (priority, _, _, r : reasoner) =>
        case #mode r
          of GLOBAL_CUT =>
               (case Seq.pull (#tactic r (ctxt,th))
                  of SOME (x,_) => raise Global_Cut x
                   | _ => NONE)
           | LOCAL_CUT =>
               (case Seq.pull (#tactic r (ctxt,th))
                  of SOME (x,s) => raise Local_Cut (score + priority, #pos r, Seq.cons x s)
                   | _ => NONE)
           | NORMAL =>
              SOME (priority + score, #pos r, false,
                    Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))))
           | TO_BE_OVERRIDE =>
              SOME (priority + score, #pos r, true,
                    Seq.make (fn () => Seq.pull (#tactic r (ctxt,th))))
              
      )
  handle Local_Cut (s,pos,seq) => [(s,pos,false,seq)]
       | Success s => Success_Handlers.invoke (fst s) s
                   |> map (fn (x,y) => (score,x,false,y))
       | Global_Cut s => Global_Cut_Handlers.invoke (fst s) s
                      |> map (fn (x,y) => (score,x,false,y))*)

(*fun call_reasoners (ctxt,th) =
  gen_call_reasoners (Config.get ctxt trace) (Reasoners.get (Context.Proof ctxt)) ctxt th *)

fun disabled_due_to_backtrack ADMIT_BACKTRACK _ = false
  | disabled_due_to_backtrack NO_BACKTRACK NO_BACKTRACKING = false
  | disabled_due_to_backtrack NO_BACKTRACK _ = true
  | disabled_due_to_backtrack NO_EXPLORATIVE_BACKTRACK EXPLORATIVE_BACKTRACKING = true
  | disabled_due_to_backtrack NO_EXPLORATIVE_BACKTRACK _ = false

fun gen_reason _ _ _ _ _ _ [] = NONE
  | gen_reason N trace limit iter backtracking tactics ([]::L) =
      (if 2 <= trace then tracing ("Backtracking...") else ();
       gen_reason N trace limit iter
          (if backtracking = EXPLORATIVE_BACKTRACKING then EXPLORATIVE_BACKTRACKING else BACKTRACKING)
          tactics L)
  | gen_reason N trace limit iter backtracking tactics (((score,pos,(mode as (cut_mode,backtrack_mode)),seq)::L')::L) =
  let
    val _ = if backtrack_mode = NO_EXPLORATIVE_BACKTRACK then () else ()
    val _ = if iter > limit
            then error "The reasoning reaches the limit of the number of reasoning steps.\n\
                       \Perhaps an infinite loop is encountered.\nOtherwise, \
                       \you can set \<phi>reasoning_step_limit to increase the limit of the steps\
                       \if it is too small."
            else ()
  in if disabled_due_to_backtrack backtrack_mode backtracking
  then gen_reason N trace limit iter backtracking tactics (L'::L)
  else
  ((case Seq.pull seq
      of SOME ((ctxt,th), seq') =>
          (let
            val _ = if 2 <= trace
                    then tracing ("\<phi>reasoning("^string_of_int score^"):"^
                                  Position.here pos ^"\n" ^ Thm.string_of_thm ctxt th)
                    else ()
            val _ = if score = 3015 then () else ()
         (* fun filter_out_TBO L =
              if exists (fn (_,_,m,_) => m = TO_BE_OVERRIDE) L
              then filter_out (fn (_,_,m,_) => m = TO_BE_OVERRIDE) L
              else L *)

            val Z = if Thm.nprems_of th <= N
                    then raise Success (ctxt, th)
                    else let val th' = if Term.could_beta_eta_contract (Thm.major_prem_of th)
                                       then Conv.gconv_rule Phi_Help.beta_eta_conversion 1 th
                                       else th
                      in get_reasoners' (Proof_Context.theory_of ctxt) tactics (Thm.major_prem_of th')
                            |> 3 <= trace ? (fn rs => (List.app (debug ctxt) rs; rs))
                            |> map (fn (priority, _, _, r : reasoner) =>
                                  (priority + score, #pos r, #mode r, apply_tactic backtracking (#tactic r) (ctxt,th')))
                     end

            val Z = case cut_mode
                      of GLOBAL_CUT => let val _ = if 2 <= trace
                                                   then tracing ("\<phi>reasoning cut:\n" ^ Thm.string_of_thm ctxt th)
                                                   else ()
                                        in [[(score, pos, NORMAL_MODE, Seq.single (ctxt,th))]]
                                       end
                       | LOCAL_CUT => Z :: (
                                        if pointer_eq (seq',Seq.empty) then L
                                        else [(score,pos,mode,seq')]::L)
                       | NO_CUT => Z :: (
                              let (*val L' = filter_out_TBO L'*)
                                  val t = if pointer_eq (seq',Seq.empty) then L'
                                          else (score,pos,mode,seq')::L' 
                              in if null t then L else t::L end)
          in
            gen_reason N trace limit (iter+1) NO_BACKTRACKING tactics Z
          end)
       | NONE => gen_reason N trace limit iter backtracking tactics (L'::L) )
    handle Success s => Success_Handlers.invoke (fst s) s
                     |> map (fn (x,y) => (score,x,NORMAL_MODE,y))
                     |> (fn Z => gen_reason N trace limit (iter+1) NO_BACKTRACKING tactics (Z :: L))
         | Global_Cut s => Global_Cut_Handlers.invoke (fst s) s
                     |> map (fn (x,y) => (score,x,NORMAL_MODE,y))
                     |> (fn Z => gen_reason N trace limit (iter+1) NO_BACKTRACKING tactics (Z :: L)) )
    handle Explorative_Backtrack =>
              gen_reason N trace limit iter EXPLORATIVE_BACKTRACKING tactics (L'::L)
  end

(*Entry point*)
fun gen_reason' ctxt N states =
  Timing.cond_timeit (Config.get ctxt count_performance) "Time spent by \<phi>-LPR reasoning:" (fn () =>
     (gen_reason N (Config.get ctxt trace) (Config.get ctxt step_limit)
                 0 NO_BACKTRACKING (Reasoners.get (Context.Proof ctxt))
                 (map (map (fn seq => (0, Position.none, NORMAL_MODE, seq))) states)
      handle Success ret => SOME ret)
  )



(* Various Interfaces for Invoking Reasoning *)

fun num_of_protected_prems  _  NONE = 0
  | num_of_protected_prems thm (SOME N) =
      if N >= 0 then Thm.nprems_of thm - N else ~N

fun internal_reason (SOME 0) _ S = SOME S
  | internal_reason N open_newctxt (ctxt,sequent) =
      if Thm.nprems_of sequent = 0 then SOME (ctxt, sequent)
      else gen_reason' ctxt (num_of_protected_prems sequent N)
                  [[ (Seq.single (enter_reasoning_envir' open_newctxt ctxt, sequent))]]
        |> Option.map (apfst (exit_reasoning_envir' open_newctxt))

fun reason num open_newctxt ctxt sequent =
  case internal_reason num open_newctxt (ctxt,sequent)
    of SOME (ctxt', sequent') =>
               SOME (singleton (Proof_Context.export ctxt' ctxt) sequent')
     | NONE => NONE

fun reason1 G N ON ctxt sequent =
  case reason N ON ctxt sequent of SOME x => x | NONE => error (G ())

fun internal_reason_s open_newctxt ctxt seqs =
  let val (ret,seqs') = seqs (enter_reasoning_envir' open_newctxt ctxt)
   in (ret, gen_reason' ctxt 0 [[ seqs' ]]
              |> Option.map (apfst (exit_reasoning_envir' open_newctxt)))
  end

fun reason_sXXX open_newctxt ctxt seqs =
  case internal_reason_s open_newctxt ctxt seqs
    of (ret, SOME ( ctxt', sequent')) =>
               (ret, SOME (singleton (Proof_Context.export ctxt' ctxt) sequent'))
     | (ret, NONE) => (ret, NONE)

fun reason_tac N open_newctxt ctxt stat = Seq.make (fn () =>
      gen_reason' ctxt (num_of_protected_prems (snd stat) N)
                  [[ (Seq.single (apfst (enter_reasoning_envir' open_newctxt) stat)) ]]
       |> Option.map ( apfst (exit_reasoning_envir' open_newctxt)
                    #> Seq.Result
                    #> rpair Seq.empty)
    )



(*** Command Interface ***)

fun setup_method_cmd (((name,(mode,priority)), raw_patterns), method) lthy =
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
    val method'''= (fn (_, (ctxt,thm)) => method'' ctxt [] (ctxt,thm) |> Seq.filter_results)
  in add_lthy {name=name', pos=Binding.pos_of name, mode=mode,
               pattern=pos_pats, blacklist=neg_pats, tactic= Tac_ML method'''} lthy'
  end

fun setup_cmd ((((name,pos),(mode,priority)),raw_patterns),tactic_src) lthy =
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern lthy
    val name = Syntax.read_term ctxt name
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
        (ML_Lex.read "Theory.local_setup (Phi_Reasoner.add_lthy {name=(" @
         ML_Lex.read (print_term name) @ ML_Lex.read ("), pos=(") @
         ML_Lex.read (print_position pos) @ ML_Lex.read "), mode=(" @
         ML_Lex.read (print_mode_ML mode) @ ML_Lex.read "), pattern=(" @
         ML_Lex.read (print_list (print_pair print_term print_int) pos_pats) @
         ML_Lex.read "), blacklist=(" @ ML_Lex.read (print_list print_term neg_pats) @
         ML_Lex.read "), tactic= Phi_Reasoner.Tac_ML ((let in " @
         ML_Lex.read_source tactic_src @
         ML_Lex.read (" end) : Phi_Reasoner.backtracking * context_state -> context_state Seq.seq)})"))
    )
  end

val cut_mode_parser = (\<^keyword>\<open>!\<close> |-- \<^keyword>\<open>!\<close> >> K (SOME GLOBAL_CUT))
                   || (\<^keyword>\<open>!\<close> >> K (SOME LOCAL_CUT))
                   || (\<^keyword>\<open>?\<close> >> K (SOME NO_CUT))
                   || Scan.succeed NONE
val backtrack_mode_parser = (Args.$$$ "default" >> K NO_BACKTRACK)
                         || ((Args.$$$ "no" -- Args.$$$ "backtrack") >> K NO_BACKTRACK)
                         || ((Args.$$$ "no" -- Args.$$$ "explorative" -- Args.$$$ "backtrack") >> K NO_EXPLORATIVE_BACKTRACK)
                         || Scan.succeed ADMIT_BACKTRACK

fun default_mode_of priority =
      if priority >= 1000000 then GLOBAL_CUT
      else if priority >= 1000 then LOCAL_CUT
      else NO_CUT

val mode_and_priority =
      (backtrack_mode_parser -- cut_mode_parser -- Scan.optional Parse.int 100) >> 
      (fn ((bm, SOME m), i) => ((m,bm),i)
        | ((bm, NONE), i) => ((default_mode_of i, bm), i))

val patterns = Parse.$$$ "(" |-- Parse.enum "|"
      (Scan.optional (\<^keyword>\<open>except\<close> >> K false) true -- Parse.term
                -- Scan.option (\<^keyword>\<open>(\<close> |-- Parse.int --| \<^keyword>\<open>)\<close>))
      --| Parse.$$$ ")"

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner_ML} "define \<phi>reasoner"
    (Parse.position Parse.term -- mode_and_priority -- patterns
        --| @{keyword =} -- Parse.ML_source
      >> setup_cmd)

val _ =
  Outer_Syntax.local_theory @{command_keyword \<phi>reasoner} "define \<phi>reasoner"
    (Parse.binding -- mode_and_priority -- patterns
        --| @{keyword =} -- Parse.args1 (K true)
      >> setup_method_cmd)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_\<phi>reasoners\<close>
    "print \<phi>reasoner matching the given pattern\n\
    \No question mark: prints what reasoners will be attempted on the given task exactly\n\
    \One question mark: pritns all reasoners whose binding patterns match the given term\n\
    \Two question mark: prints all reasoners whose binding patterns are matched by the given pattern"
    (Parse.term -- (Scan.optional ((Args.query |-- Args.query >> K 2) ||
                                   (Args.query >> K 1)) 0)
   >> (fn (raw_pattern, power) =>
      Toplevel.keep (fn top =>
        let val ctxt = Toplevel.context_of top
            val thy = Proof_Context.theory_of ctxt
            val pattern = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt) raw_pattern
            val all_reasoners = Reasoners.get (Context.Proof ctxt)
            val reasoners = case power
                              of 0 => get_reasoners' thy all_reasoners pattern
                               | 1 => iNet.match_term all_reasoners pattern
                                        |> distinct (fn (a,b) => #3 a = #3 b)
                                        |> sort (fn ((c1,_,_,_),(c2,_,_,_)) => int_ord (c1,c2))
                               | 2 => iNet.entries all_reasoners
                                        |> filter (fn (_,_,_,r) => match_reasoner thy pattern r)
                                        |> distinct (fn (a,b) => #3 a = #3 b)
                                        |> sort (fn ((c1,_,_,_),(c2,_,_,_)) => int_ord (c1,c2))
         in if null reasoners
            then writeln "No reasoner found."
            else writeln (Pretty.string_of (Pretty.chunks
                              (map (fn (_,_,_,r) => pretty ctxt r) reasoners)))
        end)));



(*** Reasoner for Reasoning Rule ***)



(** Default Pattern **)

structure Default_Pattern = Pattern_Translation (
  val parse_pattern = Syntax.parse_prop
  val check_pattern = Syntax.check_props
  val multi_translation_err_msg = "Fail to determine which pattern is preferable. \
                                \Please indicate the pattern manually using syntax \
                                \\<open>\<phi>reason for \<open>pattern\<close>\<close>"
)

val the_default_pattern_of = Default_Pattern.translate

val _ = Theory.setup (Default_Pattern.setup_attribute \<^binding>\<open>\<phi>reason_default_pattern\<close>
          "set the default pattern of a reasoning rule once its conclusion matches some pattern")

(** Reasoning Rule Pass **)

type pass_data = thm list (*rules*) * (mode * priority) * ((pattern * priority option) list * pattern list) * guard option * Context.generic
type rule_pass = Position.T -> pass_data -> pass_data

fun rule_pass_eq ((n1,_,_),(n2,_,_)) = (n1 = n2)
structure Rule_Pass = Generic_Data (
  type T = (string (*name*) * pattern * rule_pass) iNet.net
  val empty = iNet.empty
  val merge = iNet.merge rule_pass_eq
)

fun get_passes ctxt terms =
  let val thy = Context.theory_of ctxt
      fun get term =
        iNet.match_term (Rule_Pass.get ctxt) term
          |> filter (fn (_,pat,_) => Pattern.matches thy (pat,term))
   in fold (fn TM => union rule_pass_eq (get TM)) terms []
  end

fun run_passes pos (data as (rules, mode, _, _, ctxt)) =
  fold (fn (_,_,f) => f pos) (get_passes ctxt (map Thm.concl_of rules)) data

fun add_pass rule_pass =
  Rule_Pass.map (iNet.insert_term rule_pass_eq (#2 rule_pass, rule_pass))

(*structure Rule_Pass *)

(** Main Function **)

fun process_error_rule ctxt (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>ERROR\<close>, _) $ text))
      = (Exn.error (Text_Encoding.decode_text_str (Context.proof_of ctxt) text) ; false)
  | process_error_rule ctxt (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>TRACING\<close>, _) $ text))
      = (tracing (Text_Encoding.decode_text_str (Context.proof_of ctxt) text) ; false)
  | process_error_rule ctxt (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>WARNING\<close>, _) $ text))
      = (warning (Text_Encoding.decode_text_str (Context.proof_of ctxt) text) ; false)
  | process_error_rule ctxt (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>FAIL\<close>, _) $ text))
      = (warning (Text_Encoding.decode_text_str (Context.proof_of ctxt) text) ; false)
  | process_error_rule _ _ = true

fun intro_reasoner ctxt0 pos mode0 priority0 pats0 guard0 rules0 =
  let
    val (rules01, (mode, priority), (patterns, blacklist), guard, ctxt) =
            run_passes pos (map (Thm.transfer'' ctxt0) rules0, (mode0, priority0), pats0, guard0, ctxt0)
    val rules = rules01
             |> filter (fn th => not (Thm.is_free_dummy th orelse Thm.is_dummy th))
             |> map ( Phi_Help.beta_eta_contract
                   #> Drule.zero_var_indexes
                   #> Thm.trim_context )
    val _ = if null rules then error ("No rule is given!") else ()
    val pats = if null patterns
               then case rules
                      of [rule] =>
                        let val concl = Thm.concl_of rule
                            val pat' = the_default_pattern_of ctxt concl
                            val pat = case pat' of [] => [concl]
                                         | _ => List.filter (process_error_rule ctxt) pat'
                          (* val _ = info_pretty_generic ctxt 1 (fn () => Pretty.chunks (
                                    Pretty.str "No pattern is given, use the default pattern:" ::
                                    map (Syntax.pretty_term (Context.proof_of ctxt)) pat
                                )) *)
                        in map (rpair priority) pat end
                       | _ => error "Pattern of the reasoner is required"
               else map (apsnd (the_default priority)) patterns
    val rules_with_flag = map (fn rule =>
      let fun is_Require (Const (\<^const_name>\<open>\<r>Guard\<close>, _) $ _) = true
            | is_Require (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_Require X
            | is_Require (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_,_,X)) = is_Require X
            | is_Require _ = false
       in case Thm.prems_of rule
            of []    => (rule, false)
             | (r::L)=> if exists is_Require L
                        then error("A reasoning rule can contain one \<r>Guard antecedent at \
                                   \the leading position.")
                        else (rule, is_Require r)
      end) rules

    fun tactic [] _ = Seq.empty
      | tactic ((rule, has_semantic_guard)::R) (bm, (ctxt,sequent)) = Seq.make (fn _ =>
          case single_RS' rule ctxt sequent
            of NONE => Seq.pull (tactic R (bm, (ctxt,sequent)))
             | SOME sequent' =>
                if has_semantic_guard
                then (case internal_reason (SOME 1) false (ctxt, sequent')
                        of SOME s' => SOME (s', tactic R (bm, (ctxt,sequent)))
                         | NONE => Seq.pull (tactic R (bm, (ctxt,sequent))))
                else SOME ((ctxt, sequent'), tactic R (bm, (ctxt,sequent)))
        )
    fun guarded_tac rules =
      case guard of NONE => tactic rules
                  | SOME G => let val tac = tactic rules
                               in (fn (bm,s) => if G s then tac (bm,s) else Seq.empty) end
    val tac = if is_none guard andalso forall (not o snd) rules_with_flag
              then Tac_Rule rules
              else Tac_ML (guarded_tac rules_with_flag)
  in ({name = name_of_intro_reasoner rules,
       pos = pos,
       mode = mode,
       pattern = pats,
       blacklist = blacklist,
       tactic = tac},
     ctxt)
  end

fun add_rule pos mode priority pats guard rules ctxt =
      intro_reasoner ctxt pos mode priority pats guard rules
        |-> add

fun add_rules [] ctxt = ctxt
  | add_rules rules ctxt =
      if null rules then ctxt
      else fold_map (fn (rule,pos,mode,priority,pattern,blacklist,guard) => fn ctxt =>
                    intro_reasoner ctxt pos mode priority (pattern,blacklist) guard rule) rules ctxt
            |-> adds

(** Interfaces **)

fun attr_syntax ext gen =
  let open Args Scan Parse
    fun read_prop_mode mode' ctxt tm = Syntax.read_prop (Proof_Context.set_mode mode' ctxt) tm
    val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
    val prop_pattern = Scan.peek (named_term o read_prop_pattern o Context.proof_of)
    val pos_parser = Phi_Help.pos_parser "\<phi>reasoner"
    val ML_guard = depend (fn ctxt0 => ML_source >> (fn src =>
         let val ctxt = Context.Proof (Context.proof_of ctxt0)
              |> ML_Context.expression (Input.pos_of src)
                (ML_Lex.read "Theory.local_setup (PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.put ((" @
                 ML_Lex.read_source src @
                 ML_Lex.read ") : context_state -> bool))")
         in (ctxt0, PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.get (Context.the_proof ctxt)) end
       ))
    val priority = Scan.lift (Scan.option (\<^keyword>\<open>(\<close> |-- Parse.int --| \<^keyword>\<open>)\<close>))
  in
    lift pos_parser
    -- lift (option add |-- mode_and_priority)
    -- ext
    -- ( optional (lift (\<^keyword>\<open>for\<close>) |-- Scan.repeat (prop_pattern -- priority)) []
      -- optional (lift (\<^keyword>\<open>except\<close>) |-- Scan.repeat prop_pattern) [])
    -- option (lift \<^keyword>\<open>if\<close> |-- ML_guard)
    >> (fn ((((pos, (mode,priority)), ext), (pattern, blacklist)), guard) =>
          gen (pos, mode, priority, ext, (pattern, blacklist), guard))
  end

(*fun attr_syntax gen =
  let open Args Scan Parse
    fun read_term_mode mode' ctxt tm = Syntax.read_term (Proof_Context.set_mode mode' ctxt) tm
    val read_term_pattern = read_term_mode Proof_Context.mode_pattern
    val term_pattern = Scan.peek (named_term o read_term_pattern o Context.proof_of)
  
    fun read_prop_mode mode' ctxt tm = Syntax.read_prop (Proof_Context.set_mode mode' ctxt) tm
    val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
    val prop_pattern = Scan.peek (named_term o read_prop_pattern o Context.proof_of)
    fun cterm (ctxt,toks) = let val (term,ret) = term_pattern (ctxt,toks)
                             in (Context.cases Thm.global_cterm_of Thm.cterm_of ctxt term, ret) end
    val pos_parser = Phi_Help.pos_parser "\<phi>reasoner"
    val ML_guard = depend (fn ctxt0 => ML_source >> (fn src =>
         let val ctxt = Context.Proof (Context.proof_of ctxt0)
              |> ML_Context.expression (Input.pos_of src)
                (ML_Lex.read "Theory.local_setup (PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.put ((" @
                 ML_Lex.read_source src @
                 ML_Lex.read ") : context_state -> bool))")
         in (ctxt0, PLP_Reasoner_Guard_Parse_Sender_Qiyuan_Xu.get (Context.the_proof ctxt)) end
       ))
    val priority = Scan.lift (Scan.option (\<^keyword>\<open>(\<close> |-- Parse.int --| \<^keyword>\<open>)\<close>))
  in
    lift pos_parser
    -- lift (option add |-- mode_and_priority)
    -- Attrib.thms
    -- option (lift (\<^keyword>\<open>for\<close> |-- Args.$$$ "action") |-- cterm)
    -- ( optional (lift (\<^keyword>\<open>for\<close>) |-- Scan.repeat (prop_pattern -- priority)) []
      -- optional (lift (\<^keyword>\<open>except\<close>) |-- Scan.repeat prop_pattern) [])
    -- option (lift \<^keyword>\<open>if\<close> |-- ML_guard)
    >> (fn (((((pos, (mode,priority)), additional_rules), action), (pattern, blacklist)), guard) =>
          gen (pos, mode, priority, additional_rules, action, (pattern, blacklist), guard))
  end
*)

fun gen_attr_add_intro' pass (pos, mode, priority, (additional_rules, action), (pattern, blacklist), guard) =
  Thm.declaration_attribute (fn rule => fn ctxt =>
      let val rules = (rule::additional_rules)
                   |> is_some action ? map (fn th =>
                        th RS (Thm.instantiate (TVars.empty,
                                                Vars.make [((("A",0),\<^typ>\<open>action\<close>), the action)])
                                  (Thm.transfer'' ctxt @{thm' Action_Tag_I})))
                   |> map Phi_Help.beta_eta_contract
                   |> Drule.zero_var_indexes_list
          val (rules', ctxt') = pass (rules, ctxt)
       in add_rule pos mode priority (pattern,blacklist) guard rules' ctxt' end)

local
fun read_term_mode mode' ctxt tm = Syntax.read_term (Proof_Context.set_mode mode' ctxt) tm
val read_term_pattern = read_term_mode Proof_Context.mode_pattern
val term_pattern = Scan.peek (Args.named_term o read_term_pattern o Context.proof_of)
fun cterm (ctxt,toks) = let val (term,ret) = term_pattern (ctxt,toks)
                             in (Context.cases Thm.global_cterm_of Thm.cterm_of ctxt term, ret) end
in                
fun attr_rule_syntax pass = attr_syntax
      (Attrib.thms -- Scan.option (Scan.lift (\<^keyword>\<open>for\<close> |-- Args.$$$ "action") |-- cterm))
      (gen_attr_add_intro' pass)
end

val attr_add_rule = attr_rule_syntax I


val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>reason\<close> attr_add_rule
    "Decalre or remove introduction rules in \<phi>-LPR."
#> Method.setup \<^binding>\<open>\<phi>reason\<close>
(let open Scan Parse in
  Scan.lift (Scan.option Parse.nat) --|
  Method.sections [
    Parse.position Args.add >> (fn (_,pos) =>
               Method.modifier (gen_attr_add_intro' I (pos,NORMAL_MODE,100,([],NONE),([],[]),NONE)) \<^here>)
] >> (fn num_prems => fn ctxt => fn ths => reason_tac num_prems true ctxt)
end)
"Apply \<phi>-LPR as a proof method."

)



end
