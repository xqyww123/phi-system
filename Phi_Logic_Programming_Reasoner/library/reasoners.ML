signature PHI_REASONERS = sig

  include PHI_REASONERS

  type schm_by_ex = int
  (*whether to replace schematic variables by existential quantified variables if feasible.
      0: do not generate existence in obligations, leaving them schematic variables, so this feature
         is disabled at all.
      1: generate existences in obligations, which are given at the beginning the obligations.
      2: generate existences in obligations and try to push them over (\<longrightarrow>, \<and>) to the bottom.
         This pushing is done by the mechanism of special existences (\<exists>\<^sup>\<phi>\<^sup>-\<^sup>L\<^sup>P\<^sup>R).
      ~1: take \<open>Config.get existential_obligation\<close> *)

  type contraction_mode = bool * bool * schm_by_ex
  (*contraction_mode = (collect_premises, conv_all, schm_by_ex)

    collect_premises: shall the antecedents be put into the proof obligation?
      If not, they are discarded.  \<open>A \<Longrightarrow> B \<Longrightarrow> obligation G\<close> gives
      \<open>obligation (A \<longrightarrow> B \<longrightarrow> G)\<close> when true, \<open>obligation G\<close> when false.
    conv_all: convert meta-all into hol-all inside the obligation.  Fails if any
      antecedent is still there, so they must be gone by then. *)

  val collect_obligation_premises : contraction_mode -> Proof.context -> thm
                                 -> int (*number of new conditions introduced*) * thm
  val obligation_intro_Ex_conv : schm_by_ex -> Proof.context -> thm -> thm

  (* Sledgehammer first, AoA as fallback.
     In phi contexts call `Phi_Envir.solve_obligation` — it freezes `\<phi>` /
     `\<phi>lemmata` into the named snapshots that recorded proofs refer to.
     The (string -> string) argument wraps every failure text (sync and async
     alike) — the cast site layers its provenance line through it; pass `I`
     for no wrapping.
     Pull the returned sequence at most once: the `Agent_Give_Up` handler wraps only
     the first pull. *)
  (*async_mode: pass Async {failure_msg = NONE, ...} -- this solver substitutes
    its own composer for the NONE, because it is the innermost layer that holds
    BOTH the obligation and the context the obligation must be printed in, and
    the only one that knows the AoA give-up vocabulary.  A SOME would be honoured
    verbatim, but no caller has anything better to say.*)
  (*return_empty_seq_instead_of_raising_detailed_error: what to do when the proof
    agent gives up, i.e. when `MiniLang_Agent_AoA.Agent_Give_Up` reaches this
    solver.

    false (what every caller passes today): raise ERROR carrying the agent's own
      banner and detail, wrapped by the (string -> string) argument.  The command
      fails then and there, and the user reads why.
    true: return an empty sequence instead, so the reasoner backtracks and looks
      for another way to discharge the antecedent.  The give-up text is lost --
      whatever happens next, nothing reports that the agent was ever consulted.

    Only these four give-up reasons are softened, and only when the flag is true:
    "refute" (the agent believes the obligation is false), "resource_unavailable"
    (it could not reach the model backend), "resource_exhausted" (it ran out of
    budget) and "surrender" (it could not find a proof).  "technical_failure" AND
    ANY REASON NOT IN THAT LIST always raise: `MiniLang_Agent_AoA.banner_of` has
    a catch-all branch and the agent's reason string is passed through verbatim,
    so the vocabulary is open and an unknown reason must not be swallowed.

    Two failure channels are NOT covered by this flag -- they raise regardless:
    the error raised when the AoA gate is closed, and
    `Phi_Sledgehammer_Solver.Auto_Fail`.

    Note that the flag interacts with the pull-at-most-once convention stated
    above: that convention holds because the handler raises, so there is never a
    second pull.  A caller passing true must re-examine it.

    A caveat for whoever turns this on: a soft failure makes the reasoner take
    another path in silence.  The premise-loss defect fixed in 2026-08-11 was
    found only because the obligation failed loudly.  Pair any `true` with a
    trace that reports the backtracking.*)
  val hammer_obligation_solver :
        {async_mode : Phi_Sledgehammer_Solver.async_mode,
         read_store : bool option, write_store : bool option,
         return_empty_seq_instead_of_raising_detailed_error : bool}
     -> (string -> string) (*wraps the failure text*)
     -> Phi_Proof_Store.proof_id option -> Proof.context -> thm -> thm Seq.seq
  val hammer_obligation_solver' :
        {async_mode : Phi_Sledgehammer_Solver.async_mode,
         read_store : bool option, write_store : bool option,
         return_empty_seq_instead_of_raising_detailed_error : bool}
     -> (string -> string) (*wraps the failure text*)
     -> Phi_Proof_Store.proof_id option
     -> (Proof.context -> thm -> thm) (*failure callback*)
     -> Proof.context -> thm -> thm

  val guard_condition_solver : {can_inst: bool} -> Proof.context -> thm -> thm Seq.seq
      (*The annotation of \<open>case_split\<close> is supported*)
  val guard_condition_solver': {can_inst: bool}
                             -> (Proof.context -> thm -> thm) (*failure callback*)
                             -> Proof.context -> thm -> thm
  val guard_condition_solver1: {can_inst: bool} -> Proof.context -> thm -> thm

  val safe_obligation_solver : {can_inst: bool} -> Proof.context -> thm -> thm Seq.seq
      (*The annotation of \<open>case_split\<close> is supported*)
  val safe_obligation_solver': {can_inst: bool}
                             -> (Proof.context -> thm -> thm) (*failure callback*)
                             -> Proof.context -> thm -> thm
  val safe_obligation_solver1: {can_inst: bool} -> Proof.context -> thm -> thm


  (*defer the leading antecedent to the nearest obligation and call the contract*)
  val defer_obligation : {can_inst:bool, fix_level:int}
                      -> (Proof.context -> thm -> thm) (*contract*)
                      -> Proof.context -> thm -> thm Seq.seq
  val defer_obligation_tac : {can_inst:bool, fix_level:int}
                          -> contraction_mode
                          -> Proof.context -> thm -> thm Seq.seq
  val augment_conditions : thm list -> Proof.context -> thm -> thm
        (*augmenting conditions to the leading proof obligations*)
  val has_obligations_tag : thm -> bool


  structure Tactic_Configures : HOOKS (*You can alter auxiliary facts, tactics, and configure the
      context before applying either the automatic solving*)

(*  val extract_prem  : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm option
  val extract_prems : Context.generic -> bool (*strip the Premise tag or not*) -> thm -> thm list
  val extract_prems_rewr : Proof.context -> cterm -> thm option option*)
  val is_syntactic_premise : term -> bool

  (*Whether an antecedent is to be dropped from the proof obligation instead of
    being collected into it as a premise.  Only shapes registered by the
    attribute \<open>\<phi>filter_out_from_obligation_premise\<close> are dropped; the registry is
    empty by default, so by default nothing is dropped.*)
  val is_filtered_out_from_obligation_premise : Context.generic -> bvs -> term -> bool

  (*(* Simplifications that uses the extracted premises.
     The boolean: use_origin. if not use_origin, drops the original premises
     and only remains the extracted premises.*)*)
  val asm_simplify : bool -> Proof.context -> thm -> thm
  val asm_lr_simplify : bool -> Proof.context -> thm -> thm
  val full_simplify : bool -> Proof.context -> thm -> thm
  val asm_simp_tac : bool -> Proof.context -> int -> tactic
  val asm_lr_simp_tac : bool -> Proof.context -> int -> tactic
  val asm_rewrite : bool -> Proof.context -> conv
  val asm_lr_rewrite : bool -> Proof.context -> conv
  val asm_full_rewrite : bool -> Proof.context -> conv

  (*structure Is_Premise_of_Obligation : HANDLERS
      (*Tell me what antecedents are considered premise of a proof obligation to be reported,
        and what are not so that to be ignored.*)*)
  (*val is_premise_of_obligation : (*Context.generic ->*) term -> bool*)

  (*structure Local_Premises_of_Obligation : NAMED_THMS
      (*You can add any facts to be reported as premises of a proof obligation*)*)

  (*guard race (prove_or_refute) -- see Docs/GUARD_NITPICK_FALSIFY_PLAN.md*)
  val guard_race_timeout : int Config.T
      (*milliseconds; per-racer budget -- when the race degrades to serial
        execution, the wall-clock upper bound is #racers * budget.  The budget
        is virtual time (Timeout.apply scales it by timeout_scale and
        discounts GC) while the logged elapsed is wall clock, so a logged
        race may honestly exceed its nominal budget.*)
  val guard_race_log : string Config.T
      (*empty = off; otherwise a file path receiving one TSV line per race:
        serial, verdict (proved/refuted/undecided), winner racer or "-",
        wall-clock ms, #subgoals, mode (forked/serial), and per-racer exits
        as name:code pairs (win/none/timeout/crash/cancelled/discarded)*)

end


structure Phi_Reasoners : PHI_REASONERS = struct
open Thm Term Phi_Reasoners

(** Preliminary **)


(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty))) *)

val aux_thms = Useful_Thms.get


(* Simple Simplification of Obligations Before Exporting *)
(*to see if it can be reduced to some trivial form like \<open>A = ?x\<close>*)

(*
val conv_LRHS_heads = [\<^const_name>\<open>id\<close>, \<^const_name>\<open>fst\<close>, \<^const_name>\<open>snd\<close>]
fun conv_LRHS ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>id\<close>, _) $ _ =>
          Conv.rewr_conv @{thm' Fun.id_apply[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>fst\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' Product_Type.fst_conv[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>snd\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' Product_Type.snd_conv[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) =>
          Conv.rewr_conv @{thm' prod.case[folded atomize_eq]} ctm
     | _ => raise CTERM ("conv_LRHS", [ctm])

fun need_conv_LRHS tm =
  case Term.head_of tm of Const(N, _) => member (op =) conv_LRHS_heads N
                        | _ => false

fun simple_simp ctxt sequent =
  case PLPR_Syntax.dest_premise_tag (major_prem_of sequent)
    of (_, Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y) =>
         if need_conv_LRHS X orelse need_conv_LRHS Y
         then Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn _ =>
                 Conv.arg_conv (Conv.arg_conv (
                      HOLogic.eq_conv (Conv.repeat_conv conv_LRHS) (Conv.repeat_conv conv_LRHS)))
                 ) ctxt
              ) 1 sequent
         else sequent
     | _ => sequent
*)

(*** Tactics ***)

(** Tactic Configures **)
(*depreciate?*)

datatype solver_mode = Agressive_Solver (*the auto method*) | Safe_Solver (*by clarsimp*)

structure Tactic_Configures = Hooks (
  type arg = solver_mode
  type state = thm list (*aux thms*) * tactic * Proof.context
)

fun apply_tac ctxt tactic mode =
  HEADGOAL (SOLVED' (fn i => fn th =>
    let val tac = #2 (Tactic_Configures.invoke_until_success (Context.Proof ctxt)
          (fn mode => fn (aux,tac,ctxt) =>
              ([], tactic (ctxt,tac,aux,mode), ctxt)) mode (aux_thms ctxt, all_tac, ctxt))
     in tac th
    end ))

(*
(** Tactic Template **)

structure Very_Safe_Oblg_Simp_SS = Simpset(
  val initial_ss = Simpset_Configure.Minimal_SS_configure (fn ctxt =>
                      ctxt addsimps @{thms' HOL.simp_thms})
  val binding = NONE
  val attribute = NONE
  val comment = "Very safe rewrite rules normalizing proof obligations"
  val post_merging = I
)*)

(** Annot of Fixing **)

fun annot_of_fixing ret (Const(\<^const_name>\<open>LPR_ctrl\<close>, _) $ X) = Term.add_vars X ret
  | annot_of_fixing ret (A $ B) = annot_of_fixing (annot_of_fixing ret A) B
  | annot_of_fixing ret (Abs (_,_,X)) = annot_of_fixing ret X
  | annot_of_fixing ret _ = ret

(*Eliminating unknown variables as early as possible is essential for the performance of solving
proof obligations. It seems that Isabelle is not very good at eliminating existentially quantified
variables (to which unknown variables will be instantiate) and fails sometimes even for naive instantiation.
Therefore, we use sophisticated instantiation strategy here involving different levels of
computational complexity to instantiate them as early as possible.*)

fun mk_boolean_inst (Var v) b ret = Vars.add (v, if b then Phi_Help.True else Phi_Help.False) ret
  | mk_boolean_inst (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) b ret
      = mk_boolean_inst B b (mk_boolean_inst A b ret)
  | mk_boolean_inst (Const(\<^const_name>\<open>HOL.Not\<close>, _) $ A) b ret
      = mk_boolean_inst A (not b) ret
  | mk_boolean_inst (Const(\<^const_name>\<open>id\<close>, _) $ X) b ret
      = mk_boolean_inst X b ret
  | mk_boolean_inst _ _ _ = raise Match

(*it is unsafe to instantiate any functional unknown variable because you don't know how
  the function would be and it may be even not unique. For example, \<open>?x a b = True\<close>, you
  may think the instantiation would be \<open>\<lambda>_ _. True\<close> but it actually can also be \<open>\<lambda>a b. a = b\<close>
  when \<open>a = b\<close>.

  However, even if it is unsafe, it works in most of cases and our simplifier tactics are already
  unsafe. The unsafe instantiation is still acceptable once users can use tags to prevent aggressive
  instantiation.

  TODO: I don't know if we should re-enable IEUV but I believe the procedure of IEUV should be hard-coded
    in the fast_inst below.
*)

fun is_var' vars x =
  case Term.strip_comb x
    of (Var (v,_), args) => forall (fn Bound _ => true | _ => false) args andalso
                            not (member (op =) vars v)
     | _ => false

fun fast_inst can_inst th =
  let val vars = fold (Term.add_var_names) (Logic.strip_assums_hyp (hd (Thm.prems_of th))) []
   in case (can_inst, PLPR_Syntax.may_dest_premise_tag (major_prem_of th))
   of (_, Const (\<^const_name>\<open>True\<close>, _)) =>
            SOME (@{thm' Premise_True} RS th, Seq.empty)
     | (true, Const(\<^const_name>\<open>HOL.Not\<close>, _) $ X) =>
         (SOME (Thm.instantiate (TVars.empty, mk_boolean_inst (Phi_Help.beta_eta_contract_term X) false Vars.empty) th,
                Seq.empty)
          handle Match => NONE)
     | (true, Const(\<^const_name>\<open>HOL.conj\<close>, _)
                    $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y)
                    $ _) =>
         if is_var' vars X orelse is_var' vars Y
         then (SOME (@{lemma' \<open>Premise mode P \<Longrightarrow> Premise mode (x = x \<and> P)\<close>
                     by (simp add: Premise_def)} RS th, Seq.empty)
               handle THM _ => NONE)
         else NONE
     | (true, X as Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
         (SOME (Thm.instantiate (TVars.empty, mk_boolean_inst (Phi_Help.beta_eta_contract_term X) false Vars.empty) th,
                Seq.empty)
          handle Match => NONE)
     | (true, Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ Y) =>
         (*solves the equation by unification once single resolution*)
         (*TODO, BUG: ant \<open>fst (fst x, undefined) = fst ?x\<close> results in single unification \<open>x <- (fst x, undefined)\<close>*)
         if is_var' vars X orelse is_var' vars Y
         then (SOME (@{lemma' \<open>Premise mode (x = x)\<close> by (simp add: Premise_def)} RS th, Seq.empty)
               handle THM _ => NONE)
         else NONE
     | (true, X) =>
          if is_Var (Term.head_of X)
          then SOME (@{thm' Premise_True} RS th, Seq.empty)
          else NONE
     | _ => NONE
  end

(*slow but powerfull and flexible*)
fun LPR_inst ctxt th = ( (*TODO: strengthen fast_inst*)
  (*if Term.is_schematic (Thm.major_prem_of th)
  then (
    Phi_Reasoner.info_print ctxt 3 (fn () => "Phi_Reasoners.LPR_inst") ;
    Phi_Reasoner.reason NONE (SOME 1) ctxt
                        (@{lemma' \<open> \<guard> IEUV Any False P P' \<and>\<^sub>\<r> Literal_Boolean Any
                                \<Longrightarrow> Premise mode P'
                                \<Longrightarrow> Premise mode P \<close>
                               by (simp add: IEUV_def \<r>Guard_def Ant_Seq_def)
                          } RS' (ctxt, th)) )
  else*) NONE
)

(*fix_level = 0 for no fix
            | 1 for fixing the conditions of the leading antecedent only but leaves variables
                    in the conclusion of the leading antecedent free
            | 2 for fixing variables in the entire leading antecedent*)
fun oblg_template report_time {can_inst, fix_level} f ctxt th00 = Seq.make (fn () =>
  PLPR_Statistics.measure_time_of_proof_evaluation' report_time ctxt (fn () =>
  let val th01 = case PLPR_Syntax.dest_premise_tag_opt (major_prem_of th00)
                   of SOME _ => th00
                    | NONE => @{thm' Premise_D[where mode=default]} RS th00
      val th = Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
              PLPR_Syntax.premise_tag_conv (K true) (Simplifier.full_rewrite ctxt)) ctxt) 1 th01
   in case Thm.major_prem_of th
   of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) =>
        SOME (@{thm' TrueI} RS' (ctxt, th), Seq.empty)
    | _ => case fast_inst can_inst th
   of SOME ret => SOME ret
    | _ => let (* simple_simp ctxt (Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (Conv.arg_conv (
                  Simplifier.rewrite (Very_Safe_Oblg_Simp_SS.equip ctxt)))
             ) ctxt) 1 th01) *)

      val (_,prems,concl) = Phi_Help.leading_antecedent (Thm.prop_of th)
      val annotated_fixs = annot_of_fixing [] concl
      val fixing_targets = map Var (
             case fix_level
               of 1 => merge (op =) (subtract (op =) (add_vars concl []) (fold add_vars prems []),
                                     annotated_fixs)
                | 2 => add_vars (Phi_Help.leading_antecedent' th) annotated_fixs
                | _ => annotated_fixs )

      val (ctxt', th2, instc) =
            if null fixing_targets then (ctxt, th, (TVars.empty, Vars.empty))
            else let val (inst, ctxt') = Variable.import_inst false fixing_targets ctxt
                     val instc = Phi_Help.certify_vars (Context.Proof ctxt') inst
                  in (ctxt', Thm.instantiate instc th, instc)
                 end
                    
   in (case fast_inst can_inst th2
   of SOME ret => SOME ret
    | NONE => (
      case LPR_inst ctxt' th2
        of SOME ret => f ctxt' ret
         | _ => f ctxt' th2))
   |> not (null fixing_targets) ? Option.map (fn (th, seq') =>
        let val f = singleton (Variable.export_inst (Phi_Help.uncertify_vars instc))
         in (f th, Seq.map f seq')
        end)
  end end) ())


(*** Auxiliaries ***)

(*protects the remaining goals and only attack the first one*)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude


(*Wrap a context tactic of type `Proof.context -> thm -> thm Seq.seq` to the
  transition between states, of type `Proof.context * thm -> Proof.context * thm`.
  *This wrap only adopts the first result of applying the tactic, and drops other alternatives.*
  The original seq-based tactics are not affected by this.

  Because reasoners in the file only attack the first antecedent and solves it totally or fails,
  this short-cut makes differences only when the antecedent to be solved has some schematic variables
  to be instantiated during the tactic application.

  The semantics of schematic variables in hammer_obligation_solver and guard_condition_solver is,
  any possible instantiation is acceptable.

  If the schematic variables are not able to be chosen arbitrarily, additional mechanisms have
  to be applied previously.*)
fun context_tactic_to_state_transition tac fail ctxt sequent =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => th'
     | NONE => fail ctxt sequent

(*fun context_tactic_to_state_transition_opt tac (ctxt, sequent) =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => SOME (ctxt, th')
     | NONE => NONE *)


(** Case Split **)

fun case_split_by_annotations term =
  let fun insrt x splits = if Term.is_open x then splits else insert (op aconv) x splits
      fun parse_split (Const(N, Type("fun", [T,_])) $ X) splits =
            if N = \<^const_name>\<open>case_split\<close> orelse N = \<^const_name>\<open>LPR_ctrl\<close>
            then (case (T,X)
              of (\<^Type>\<open>prod _ _\<close>, Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) => splits
               | (\<^Type>\<open>prod _ _\<close>, x) => insrt x splits
               | (\<^Type>\<open>bool\<close>, Const(\<^const_name>\<open>True\<close>, _)) => splits
               | (\<^Type>\<open>bool\<close>, Const(\<^const_name>\<open>False\<close>, _)) => splits
               | (\<^Type>\<open>bool\<close>, x) => insrt x splits
               | (\<^Type>\<open>sum _ _\<close>, Const(\<^const_name>\<open>Inl\<close>, _) $ _) => splits
               | (\<^Type>\<open>sum _ _\<close>, Const(\<^const_name>\<open>Inr\<close>, _) $ _) => splits
               | (\<^Type>\<open>sum _ _\<close>, x) => insrt x splits
               | _ => insrt X splits)
            else parse_split X splits
       | parse_split (A $ B) splits = parse_split B (parse_split A splits)
       | parse_split (Abs (_, _, X)) splits = parse_split X splits
       | parse_split _ splits = splits
   in case parse_split term []
   of [] => K (K all_tac)
    | L => fn ctxt => fn goal => fn st =>
                  foldl1 (op THEN_ALL_NEW)
                         (map (fn tm => DETERM o Induct.cases_tac ctxt true [[SOME tm]] NONE []) L) goal st
  end

fun case_split_by_annotations_leading_subgoal ctxt goal th =
      case_split_by_annotations (Phi_Help.leading_antecedent' th) ctxt goal th
  

(*** Obligation Extraction ***)

(** Premise Extraction **)

(*Given any antecedent, if we can extract abstract pure facts that can help to solve the target
  proof obligation?*)
(*Convention: the rule of premise extraction has form \<open>A \<equiv> Premise \<and> A\<close>*)
type pattern = term

fun is_syntactic_premise_mode \<^const_name>\<open>MODE_GUARD\<close> = true
  | is_syntactic_premise_mode \<^const_name>\<open>NO_INST\<close> = true
  | is_syntactic_premise_mode \<^const_name>\<open>MODE_COLLECT\<close> = true
  | is_syntactic_premise_mode \<^const_name>\<open>default\<close> = true
  | is_syntactic_premise_mode _ = false

fun is_syntactic_premise (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(M, _) $ _) = is_syntactic_premise_mode M
  | is_syntactic_premise (Abs (_,_,X)) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = is_syntactic_premise X
  | is_syntactic_premise (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = is_syntactic_premise X
  | is_syntactic_premise _ = false

fun strip_premise_tag ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ _ =>
        Conv.try_conv (Conv.rewrs_conv @{thms' Premise_def}) ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
        Conv.arg_conv (strip_premise_tag ctxt) ctm
     | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (strip_premise_tag ctxt)) (strip_premise_tag ctxt) ctm
     | Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
        Phi_Conv.hol_all_conv (strip_premise_tag o snd) ctxt ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (strip_premise_tag ctxt)) (strip_premise_tag ctxt) ctm
     | Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (strip_premise_tag ctxt)) (strip_premise_tag ctxt) ctm
     | _ => Conv.all_conv ctm

(*
fun extract_prem ctxt strip =
  let val ctxt' = Context.proof_of ctxt
   in fn thm =>
   if is_syntactic_premise (Thm.prop_of thm)
   then SOME (if strip
              then (Raw_Simplifier.norm_hhf ctxt' thm)
                |> Conv.fconv_rule (strip_premise_tag ctxt')
              else thm)
   else (*if qchk [] (Thm.prop_of thm)
        then let val thm = Raw_Simplifier.norm_hhf ctxt' thm
              in (case conv ctxt' (Thm.cprop_of thm)
                    of SOME NONE => SOME (if strip
                                          then Conv.fconv_rule (strip_premise_tag ctxt') thm
                                          else thm)
                     | SOME (SOME rule) => SOME (
                         (Thm.equal_elim rule thm RS' (ctxt', conjunct1))
                           |> not strip ? (fn th => th RS' (ctxt', @{thm' Premise_I[where mode=MODE_GUARD]})))
                     | NONE => NONE)
             end
   else*) NONE
  end
*)

fun extract_prems thm =
  let fun extract th =
        case Thm.concl_of th
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ XX => (
              case XX
                of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
                    extract (Conv.fconv_rule (Conv.rewr_conv @{thm' atomize_all[symmetric]}) th)
                 | Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _ =>
                    extract (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' \<r>Guard_def})) th)
                 | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
                    maps extract (PLPR_Syntax.elim_ant_sequence_or_HOL_conj th)
                 | Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ _ $ _ =>
                    maps extract (PLPR_Syntax.elim_ant_sequence_or_HOL_conj th)
                 | Const(\<^const_name>\<open>Premise\<close>, _) $ Const (M, _) $ _ =>
                    if is_syntactic_premise_mode M
                    then [Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm' Premise_def})) th]
                    else []
                 | _ => []
             )
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                extract (Thm.forall_elim_var (Thm.maxidx_of th+1) th)
           | _ => []
   in extract thm
  end


(** Applications of the Premise Extraction **)


(* if not use_origin, drops the original premises and only remains the extracted premises. *)
fun gen_simplify simp use_origin ctxt =
  let val extract = extract_prems
      val extract' = if use_origin
                     then (fn th => th :: extract th)
                     else (fn th => case extract th of [] => [th] | L => L)
      val sctxt = Simplifier.set_mksimps (fn ctxt =>
                      maps (Simpdata.mksimps Simpdata.mksimps_pairs ctxt)
                    o extract') ctxt
   in simp sctxt
  end

val asm_simplify = gen_simplify Simplifier.asm_simplify
val asm_lr_simplify = gen_simplify Simplifier.asm_lr_simplify
val full_simplify = gen_simplify Simplifier.full_simplify
val asm_simp_tac = gen_simplify Simplifier.asm_simp_tac
val asm_lr_simp_tac = gen_simplify Simplifier.asm_lr_simp_tac
val asm_rewrite = gen_simplify Simplifier.asm_rewrite
val asm_lr_rewrite = gen_simplify Simplifier.asm_lr_rewrite
val asm_full_rewrite = gen_simplify Simplifier.asm_full_rewrite

(** Obligation Extraction **)

val contract_premise_imp =
    @{lemma \<open>(P \<Longrightarrow> PROP Waste \<Longrightarrow> Premise mode G) \<equiv> (PROP Waste \<Longrightarrow> Premise mode (P \<longrightarrow> G))\<close>
            by (rule, (simp add: Premise_def)+)}

(* Antecedents filtered out of the proof obligation *)

(*An antecedent of the leading antecedent becomes a premise of the proof
  obligation unless its shape is registered here.  The registry is a blacklist:
  whatever is not registered is collected, so nothing disappears silently.*)

val trace_filter_out_from_obligation_premise =
      Attrib.setup_config_bool
          \<^binding>\<open>\<phi>trace_filter_out_from_obligation_premise\<close> (K false)

fun filtered_out_eq ((a,_) : spattern * Position.T, (b,_)) = a aconv b

structure Filtered_Out_From_Obligation_Premise = Generic_Data (
  type T = (spattern * Position.T) iNet.net
  val empty = iNet.empty
  val merge = iNet.merge filtered_out_eq
)

fun err_clashed_filter_out ctxt net entry =
  let val (pat, _) = entry
   in error (Pretty.string_of (Pretty.chunks (
        Pretty.str "Clash with an existing \<phi>filter_out_from_obligation_premise \
                   \pattern:" ::
        Pretty.item [Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt pat] ::
        (iNet.lookup net (iNet.key_of_term pat)
          |> filter (fn e => filtered_out_eq (e, entry))
          |> map (fn (_,pos) =>
                Pretty.block (Pretty.str "already declared" :: Pretty.brk 1 :: Pretty.here pos))))))
  end

fun add_filtered_out_from_obligation_premise (pat0, pos) ctxt =
  let val _ = case Term.fastype_of pat0
                of Type(\<^type_name>\<open>prop\<close>, _) => ()
                 | _ => error "The pattern of \<phi>filter_out_from_obligation_premise \
                              \must be a proposition"
      val entry = (PLPR_Pattern.mk_spattern (Envir.beta_eta_contract pat0), pos)
   in Filtered_Out_From_Obligation_Premise.map (fn net =>
        iNet.insert_term filtered_out_eq (fst entry, entry) net
          handle iNet.INSERT => err_clashed_filter_out ctxt net entry) ctxt
  end

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>filter_out_from_obligation_premise\<close> (
    Scan.peek (fn generic =>
      let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern
                                            (Context.proof_of generic)
       in Scan.repeat1 (Parse.position (Args.named_term (fn str =>
            let val tm = Syntax.read_prop ctxt str
                val ctxt' = Proof_Context.augment tm ctxt
             in singleton (Variable.export_terms ctxt' ctxt) tm
            end)))
      end)
    >> (fn pats => Thm.declaration_attribute (K (
          fold add_filtered_out_from_obligation_premise pats))))
  "declare that antecedents matching the given proposition patterns are dropped \
  \from the proof obligation instead of being collected into it as premises")

fun is_filtered_out_from_obligation_premise ctxt =
  let val net = Filtered_Out_From_Obligation_Premise.get ctxt
      val thy = Context.theory_of ctxt
      val trace = Config.get_generic ctxt trace_filter_out_from_obligation_premise
      val pretty = Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt
   in fn bvs => fn tm =>
      case find_first (fn (pat,_) => PLPR_Pattern.does_smatch thy (K true) bvs (pat, tm))
                      (iNet.match_term net tm)
        of NONE => false
         | SOME (pat, pos) =>
            (if trace
             then tracing (Pretty.string_of (Pretty.chunks [
                    Pretty.str "filtering the antecedent",
                    Pretty.item [pretty tm],
                    Pretty.str "out of the proof obligation, because it matches the pattern",
                    Pretty.item (pretty pat :: Pretty.brk 1 :: Pretty.here pos)]))
             else ();
             true)
  end


(*the term must be beta-eta normalized*)
fun obligation_collect counter ctxt =
  let val is_filtered_out = is_filtered_out_from_obligation_premise (Context.Proof ctxt)
      fun conv bvs ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
                Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ A $ _
               =>((*the whitelist wins: an antecedent that says of itself that it is a
                    proof premise is never filtered out, whatever is registered*)
                  if is_filtered_out bvs A andalso not (is_syntactic_premise A)
                  then (Conv.arg_conv (conv bvs) then_conv
                        Conv.rewr_conv @{thm' conjunction_imp[symmetric]}) ctm
                  else (counter := !counter + 1;
                         (Conv.implies_conv
                            (Phi_Conv.atomize_conv ctxt then_conv
                             strip_premise_tag ctxt)
                            (conv bvs) then_conv
                          Conv.rewr_conv contract_premise_imp) ctm))
           | _ => raise CTERM ("unexpected proof obligation form", [ctm])
   in conv []
  end

(* REMOVE THIS WHEN NO BUG
fun obligation_collect ctxt filter ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
    case Thm.term_of ctm
      of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
            Conv.rewr_conv @{thm True_implies_equals[symmetric]} ctm
       | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ Pr $ _
           => if filter Pr
              then (Conv.implies_conv
                      (Phi_Conv.atomize_conv ctxt then_conv
                       Raw_Simplifier.rewrite ctxt true @{thms' Premise_def[where mode=default]
                                                                Premise_def[where mode=MODE_GUARD]})
                      (obligation_collect ctxt filter) then_conv
                    Conv.rewr_conv @{thm' contract_premise_imp}) ctm
              else (Conv.arg_conv (obligation_collect ctxt filter) then_conv
                    Conv.rewr_conv @{thm' conjunction_imp[symmetric]}) ctm
       | _ => raise CTERM ("unexpected proof obligation form", [ctm])
  ) ctm
*)

type schm_by_ex = int
type contraction_mode = bool * bool * schm_by_ex

fun chk_schm_by_ex ctxt ~1 = Config.get ctxt existential_obligation
  | chk_schm_by_ex _ i = i

fun chk_option ctxt (a,b,~1) = (a,b,Config.get ctxt existential_obligation)
  | chk_option _ option = option


fun obligation_conv_all ctxt ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
        (Phi_Conv.meta_all_conv (obligation_conv_all o snd) ctxt then_conv
          Conv.rewr_conv @{thm contract_premise_all}) ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
          Conv.all_conv ctm
     | _ => raise CTERM ("internal bug 6733574a-42dc-4592-a08e-ddc223bb6b94", [ctm])
  ) ctm

fun obligation_intro_Ex_conv' conv_schematic ctxt thm0 =
  let val thm = Phi_Help.beta_eta_contract thm0
             |> (fn th => if null (Thm.tpairs_of th) then th
                          else case Seq.chop 2 (Thm.flexflex_rule (SOME ctxt) th)
                                 of ([th'], _) => th'
                                  | _ => th (*fails to solve flex-flex pairs*))
      fun dest' (\<^Const>\<open>Pure.imp\<close> $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (
                      Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ P)) $ Q) = (P,Q)
        | dest' tm = raise TERM ("obligation_intro_Ex", [tm])
      fun dest ctm = dest' (Thm.term_of ctm)
      (*fun dest_c ctm =
            (dest ctm; (Thm.dest_arg (Thm.dest_arg1 ctm), Thm.dest_arg ctm))*)

      val (P,Q) = dest (Thm.cprop_of thm)
      val vars = Term.add_vars Q []
              |> fold (fn (A,B) => Term.add_vars A o Term.add_vars B) (Thm.tpairs_of thm)
      fun collect_var ret (Var v) = if member (op =) vars v then ret
                                    else insert (op =) v ret
        | collect_var ret (A $ B) = collect_var (collect_var ret A) B
        | collect_var ret (Abs(_,_,X)) = collect_var ret X
        | collect_var ret _ = ret
      val vars' = collect_var [] P
                |> map (fn (N,T) => Thm.var (N, Thm.ctyp_of ctxt T))
      val mode = conv_schematic = 2
      val contract_Ex_rule = if mode then @{thm' contract_intro_sp_Ex}
                                     else @{thm' contract_intro_Ex}
   (* val mv_Ex_All = if mode then Phi_Conv.move_sp_Ex_inside_All_recursive
                              else Phi_Conv.move_Ex_inside_All_recursive
      val mv_Ex_Disj = if mode then Phi_Conv.move_sp_Ex_downto_Disj_recursive
                               else Phi_Conv.move_Ex_downto_Disj_recursive *)
      fun intro_Ex v thm =
            Conv.fconv_rule (
                Conv.rewr_conv contract_Ex_rule then_conv (
                if mode
                then Phi_Conv.leading_antecedent_conv (
                    PLPR_Syntax.premise_tag_conv (K true) (
                      (Phi_Conv.move_sp_Ex_inside (K (
                                    Conv.fun_conv (Conv.rewr_conv @{thm' special_Ex_def}))) ctxt)
                      (*mv_Ex_All (fn _ => mv_Ex_Disj Conv.all_conv) ctxt*) )
                  )
                else Conv.all_conv)
            ) (Thm.forall_intr v thm)
   in fold intro_Ex vars' thm
  end

fun obligation_intro_Ex_conv conv_schematic ctxt thm =
  obligation_intro_Ex_conv' (chk_schm_by_ex ctxt conv_schematic) ctxt thm

fun augment_conditions conds ctxt sequent =
  let val _ = if can (PLPR_Syntax.dest_premise_tag o HOLogic.dest_Trueprop o Phi_Help.leading_antecedent') sequent
              then () else raise THM ("must be leaded by a bare premise antecedent quantified by no \
                                      \HHF conditions nor universal variables", 1, [sequent])
      val conds = map (Phi_Conv.atomize ctxt o Thm.forall_intr_vars) conds
   in sequent
   |> fold (fn cond => fn th =>
        Thm.implies_elim
          \<^instantiate>\<open>cond = \<open>Thm.dest_arg (Thm.cconcl_of cond)\<close> and
                      mode = \<open>Thm.dest_arg1 (Thm.dest_arg (Thm.dest_arg1 (Thm.cprop_of th)))\<close> and
                      P = \<open>Thm.dest_arg (Thm.dest_arg (Thm.dest_arg1 (Thm.cprop_of th)))\<close>
                        in lemma \<open>cond \<Longrightarrow> Premise mode (cond \<longrightarrow> P) \<Longrightarrow> Premise mode P\<close>
                              by (unfold Premise_def, blast)\<close>
          cond RS th) conds
  end

(*the leading antecedent must be beta-eta normalized*)
fun collect_obligation_premises option ctxt thm = let open Conv
  val (collect_premises,conv_all,conv_schematic) = chk_option ctxt option
  val new_cond = Unsynchronized.ref 0
  val rule1 = gconv_rule (Phi_Conv.meta_alls_conv (fn ctxt => 
                (if collect_premises then obligation_collect new_cond ctxt
                                     else Conv.all_conv) then_conv
                rewr_conv @{thm Pure.prop_def[symmetric]}) ctxt
              ) 1 thm

  (*val rule2 = if collect_premises
              then case Local_Premises_of_Obligation.get ctxt
                of [] => rule1
                 | L => let val fact = map (Conv.fconv_rule (Object_Logic.atomize ctxt)) L
                                    |> foldl1 (uncurry HOLogic.conj_intr)
                         in fact RS (@{thm' contract_add_additional_prems} RS rule1)
                        end
              else rule1*)

  fun drop_wastes thm =
    case Thm.major_prem_of thm
      of Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X => (
          case X of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _
                      => drop_wastes (@{thm' contract_drop_waste} RS thm)
                  | _ => @{lemma' \<open> PROP P \<Longrightarrow> PROP Pure.prop P \<close> by (unfold Pure.prop_def)} RS thm)
       | _ => error "BUG nhtCAsmjS+Oj4YsI8qtXQw"

   in drop_wastes rule1
   |> conv_all ? gconv_rule (obligation_conv_all ctxt) 1
   |> conv_schematic > 0 ? obligation_intro_Ex_conv' conv_schematic ctxt
   |> pair (!new_cond)
  end

(*Config.get ctxt existential_obligation*)

(*the leading antecedent must be beta-eta normalized*)
fun contract_obligations mode ctxt thm = thm
    |> collect_obligation_premises mode ctxt |> snd
    |> Conv.fconv_rule (Conv.rewr_conv @{thm contract_obligations})

fun find_obligations_tag thm = tl (Thm.prems_of thm)
      |> find_index (fn tm =>
            case tm of (_ $ (Const(\<^const_name>\<open>Premise\<close>, _) $ Const(\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _)) => true
                     | _ => false)
fun has_obligations_tag thm = find_obligations_tag thm <> ~1

fun defer_obligation cfg contract = oblg_template false cfg (fn ctxt => fn thm =>
  let val idx = find_obligations_tag thm
  in if idx = ~1
     then error ("Fail to defer a proof obligation: an \<obligation> antecedent is not found.")
     else Thm.permute_prems 1 idx thm
      |> contract ctxt
      |> Thm.permute_prems 0 (~idx)
      |> (fn X => SOME (X, Seq.empty))
  end)

fun defer_obligation_tac cfg contr_mode =
      defer_obligation cfg (contract_obligations contr_mode)

(*** Premise tac ***)

(*fun intro_all_leading_ex i thm =
  if i > Thm.nprems_of thm
  then thm
  else case Logic.concl_of_goal (Thm.prop_of thm) i
         of _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
              intro_all_leading_ex i (@{thm' conjI} RSN (i, thm))
          | _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ _ ) =>
              intro_all_leading_ex i (@{thm' exI} RSN (i, thm))
          | _ => intro_all_leading_ex (i+1) thm*)

(*The tactic slot holds `hammer_or_AoA` (stage 5, §2.3): level-0 store lookup,
  then one fork over [engine ORELSE AoA].  `Agent_Give_Up` is reachable from
  here on; the handle below renders it (D51).*)
fun hammer_obligation_solver
      {async_mode, read_store, write_store,
       return_empty_seq_instead_of_raising_detailed_error} wrap id =
      oblg_template true {can_inst=true, fix_level=0} (fn ctxt => fn th =>
        let val (_, th'1) = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
            val th' = @{thm' Premise_I} RS th'1
         in th'
         |> head_only (apply_tac ctxt (fn (ctxt,pre,aux,_) =>
            pre THEN HEADGOAL (Method.insert_tac ctxt aux)
                THEN (fn st =>
                   let (*The one place all failure text is composed (D51, revised
                         2026-08-09): the forked report and the promise branch
                         receive it via the failure_msg hook; the sync error
                         path is the handle right below the call.  This is the
                         innermost layer holding both the obligation (st) and the
                         context to print it in, which is why the composer is
                         built here and substituted into the caller's mode below,
                         rather than being handed down from Phi_Envir.*)
                       fun compose (MiniLang_Agent_AoA.Agent_Give_Up (reason, detail, _)) =
                             wrap (MiniLang_Agent_AoA.banner_of reason ^ "\n" ^ detail)
                         | compose (Phi_Sledgehammer_Solver.Auto_Fail
                                      (Phi_Sledgehammer_Solver.Internal_Failure msg)) =
                             (*engine bug, not an unprovable goal: the payload IS the message*)
                             wrap msg
                         | compose (exn as Phi_Sledgehammer_Solver.Auto_Fail _) =
                             wrap (Pretty.string_of (Pretty.chunks
                               (Pretty.para "Fail to solve the proof obligation automatically" ::
                                (case Thm.prems_of st
                                   of x :: _ => [Syntax.pretty_term ctxt x]
                                    | _ => [Pretty.str (Runtime.exn_message exn)]))))
                         | compose exn = wrap (Runtime.exn_message exn)
                       (*Substitute our composer for the caller's NONE — see the
                         signature.  A caller that did supply one keeps it.*)
                       val mode =
                         (case async_mode of
                            Phi_Sledgehammer_Solver.Async {failure_msg = NONE, user_facing} =>
                              Phi_Sledgehammer_Solver.Async
                                {failure_msg = SOME compose, user_facing = user_facing}
                          | m => m)
                       (*The obligation exactly as the solver receives it: after
                         collect_obligation_premises and the aux insertion.*)
                       val _ = Phi_Reasoner.info_pretty ctxt 1 (fn () => Pretty.chunks
                                 (Pretty.str "Proof obligation handed to the solver:"
                                  :: map (Syntax.pretty_term ctxt) (Thm.prems_of st)))
                    in
                   (* Text future dropped on purpose — the text was already stored
                      inside `hammer_or_AoA`, and `oblg_template` has no channel
                      for it. Do not join the future either; that would undo the fork. *)
                   (Seq.single (snd (MiniLang_Agent_AoA.hammer_or_AoA
                      {fact_override = Sledgehammer_Fact.no_fact_override,
                       proof_id = id, hammer_timeout = NONE, async_mode = mode,
                       read_store = read_store, write_store = write_store} ctxt st))
                    (* Sync face: under Sync nothing upstream converts an escaping
                       Auto_Fail, and Internal_Failure must surface its payload
                       (§2.9's consumption rule) — so this terminal slot renders
                       it through the same composer.  Agent_Give_Up is NOT caught
                       here: it falls through to the outer handle, which also
                       prints the agent cost. *)
                    handle e as Phi_Sledgehammer_Solver.Auto_Fail _ => error (compose e))
                   end))
            Agressive_Solver)
         |> Seq.pull
        end
        handle MiniLang_Agent_AoA.Agent_Give_Up (reason, detail, cost) =>
          (Phi_Reasoner.info_print ctxt 1 (fn () =>
              MiniLang_Agent_AoA.string_of_cost cost);
           (*Any reason outside this list -- "technical_failure" and whatever the
             agent may invent, see `banner_of`'s catch-all -- always raises.*)
           if return_empty_seq_instead_of_raising_detailed_error andalso
              member (op =) ["refute", "resource_unavailable",
                             "resource_exhausted", "surrender"] reason
           then NONE
           else error (wrap (MiniLang_Agent_AoA.banner_of reason ^ "\n" ^ detail))))

fun hammer_obligation_solver' opts wrap id =
      context_tactic_to_state_transition (hammer_obligation_solver opts wrap id)

fun norm_tac tac th = Seq.make (fn () => Seq.pull (tac th))

fun timed_seq time s =
  Seq.make (fn () => 
    Timeout.apply time Seq.pull s
      handle Timeout.TIMEOUT _ => NONE )

fun timed_tac time tac th = timed_seq time (tac th)

fun timed1_tac time t' tac th =
  let val s = tac th
   in Seq.make (fn () =>
      Timeout.apply time Seq.pull s
      handle Timeout.TIMEOUT t'' =>
        if t'' > t' then raise Timeout.TIMEOUT t'' else NONE )
  end

fun quick_cut i th =
  case Logic.strip_assums_concl (Logic.nth_prem (i, Thm.prop_of th))
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>False\<close>, _) => Seq.empty
     | _ => Seq.single th

fun slow_step_tac' ctxt =
  Classical.appWrappers ctxt
    (Classical.instp_step_tac ctxt APPEND' Classical.unsafe_step_tac ctxt);

fun nodup_depth_tac ctxt m i st =
  SELECT_GOAL
    (Classical.safe_steps_tac ctxt 1 THEN_ELSE
      (DEPTH_SOLVE (nodup_depth_tac ctxt m 1),
        Classical.inst0_step_tac ctxt 1 APPEND COND (K (m = 0)) no_tac
          (slow_step_tac' ctxt 1 THEN DEPTH_SOLVE (nodup_depth_tac ctxt (m - 1) 1)))) i st;

fun auto_search_tac ctxt =
  let
    val ctxt = Context_Position.set_visible false ctxt
    fun main_tac i =
        CHANGED (nodup_depth_tac (addss ctxt) 10 i)
  in
    norm_tac ((
      TRY (Classical.safe_tac ctxt) THEN
      REPEAT_DETERM (FIRSTGOAL main_tac) THEN
      TRY (Classical.safe_tac (addSss ctxt)) THEN
      prune_params_tac ctxt)
      #> Seq.take 1 )
  end;


(*
fun auto_search1_tac ctxt t th =
  norm_tac (auto_search_tac ctxt t) th
    |> Seq.take 1 *)

fun dest_all ct used =
  (case Thm.term_of ct of
    Const ("Pure.all", _) $ Abs (x, _, _) =>
      let
        val (x', used') = Name.variant x used;
        val (v, ct') = Thm.dest_abs_fresh x' (Thm.dest_arg ct);
      in SOME ((x, Thm.ctyp_of_cterm v), (ct', used')) end
  | _ => NONE)

(*** Guard Race ***)

(*Docs/GUARD_NITPICK_FALSIFY_PLAN.md §1–§3.  After the 30ms serial quick-proof
  attempt, proving and refuting racers race under a per-racer budget on the
  race engine of Performant_Isabelle_ML (Race.race, library/race.ML): the
  winner is the lowest-indexed racer that recorded a claim (the first claim
  to arrive ends the race), losers are cancelled promptly, every racer gets
  a truthful exit, and every racer has terminated before the race returns —
  the join barrier the post-race record below relies on.  The engine never
  converts an interrupt into a result: external cancellation re-raises out
  of the race, while a racer's own internal interrupt is absorbed as that
  racer's Cancelled exit; a racer's crash is that racer's failure only,
  reported post-race from its exit.  The exception discipline shared with
  auto_sledgehammer's sledgehammer_solver.ML (classify / normalise) has its
  kernel in Race.contains_interrupt — sledgehammer_solver.ML still carries
  its own inline copy: keep the two in sync (unification pending, plan §8).*)

(** Racers **)

datatype race_result = Proved of thm | Refuted of string
  (*Refuted carries the REFUTER's name: a refutation can reach the winner
    slot by relay (see the early-finish protocol below), so attribution
    travels in the result, not in the racer name the engine reports.*)

(*the shared acceptance criterion of both searching racers: run the search,
  keep the state iff nothing is left to prove*)
fun search_solved search st =
  (case Seq.pull (search st) of
     SOME (st', _) => if Thm.no_prems st' then SOME st' else NONE
   | NONE => NONE)

(*Early-finish protocol (plan §8, author-ruled 2026-08-25): let a refutation
  end the race the moment it is known that no proof can still arrive.  Both
  events live in ONE variable, so each racer publishes its own event and
  reads the other's inside a single critical section — whenever both events
  occur, the second racer to enter the critical section sees the first's,
  and no ordering argument is needed.
    pauto_finished — P-auto ran to completion without proving.  Set on that
      normal empty-handed return only: a timeout or crash leaves the body by
      an exception path, which the racer exit discipline does not intercept.
    refuted_by — a refutation was found, recorded under the refuter's name.
      A refutation computed but not yet committed can be lost to a perfectly
      timed interrupt; the cost is one suppressed default-off warning (all
      three failure exits are observationally equivalent, plan §11.1 ⑤).
  A refutation may END the race only when pauto_finished is already set.
  P-auto is the only producer of Proved, so this pre-empts no still-possible
  proof; the verdict is the same one the no-winner path would read from the
  record (visible there because the engine joins all racers first) — the
  protocol only moves it earlier.  With today's two racers the time saved is
  about zero; the protocol pays once R-nitpick joins and an early verdict
  cancels racers still burning budget (plan §8).  "No winner" implies P-auto
  failed, which structurally closes the vacuous-hypothesis guard (a
  contradictory hypothesis H makes both H \<Longrightarrow> C and H \<Longrightarrow> \<not>C provable):
  P-auto would have won.  Synchronized.change_result, never
  Synchronized.assign (assign makes the variable Immutable).*)

fun p_auto_racer search protocol th : race_result Race.racer =
  ("P-auto", fn () =>
     (case search_solved search th of
        SOME th' => SOME (Proved th')
      | NONE =>
          Synchronized.change_result protocol
            (fn {pauto_finished = _, refuted_by} =>
              (Option.map Refuted refuted_by,
               {pauto_finished = true, refuted_by = refuted_by}))))

val negation = \<^cterm>\<open>Not\<close>

(*R-conv (plan §2.2): refute by PROVING the negation — each subgoal's
  conclusion is negated under its \<And>/\<Longrightarrow> prefix and handed to the same
  classical search.  The whole computation, negation included, runs inside
  the racer body (plan §8 D6): it is bounded by this racer's budget and
  covered by the engine's exception discipline, and a non-Trueprop
  conclusion (Unsupported) just comes back empty-handed.
  ctxt is the inner, goal-side context; ctxt0 the outer context of
  guard_condition_solver — Variable.export ctxt ctxt0 is direction-
  sensitive, do not swap the two.  can_inst = true freezes the residual
  schematics (a universal refutation); false exports them back (an
  existential refutation — an accepted completeness-only weakening, plan
  §2.3).  This variable discipline is the proof-searcher's own,
  intentionally different from R-nitpick's as-is discipline — see the
  duality note in plan §2.3; the discarded import context is the question
  T2 must answer before extending this (plan §11.1 ④).*)
fun r_conv_racer can_inst ctxt ctxt0 search protocol goals : race_result Race.racer =
  ("R-conv", fn () =>
     let exception Unsupported
         fun conv_goal used ctm =
           case Thm.term_of ctm
             of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                   let val (f,a) = Thm.dest_comb ctm
                    in Thm.apply f (conv_goal used a)
                   end
              | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (x,_,_) =>
                   let val (q,b) = Thm.dest_comb ctm
                       val (x', used') = Name.variant x used;
                       val (v, b') = Thm.dest_abs_fresh x' b
                    in Thm.apply q (Thm.lambda v (conv_goal used' b'))
                   end
              | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
                   let val (c,b) = Thm.dest_comb ctm
                    in Thm.apply c (Thm.apply negation b)
                   end
              | _ => raise Unsupported
         val refuted =
           (map (fn goal =>
                Goal.init (conv_goal (Term.declare_free_names (Thm.term_of goal) Name.context) goal)
              ) goals
              |> (fn gs => if can_inst
                           then Variable.import false gs ctxt |> #1 |> #2
                           else Variable.export ctxt ctxt0 gs)
              |> exists (is_some o search_solved search))
           handle Unsupported => false
      in if refuted
         then Synchronized.change_result protocol
                (fn {pauto_finished, refuted_by = _} =>
                  (if pauto_finished then SOME (Refuted "R-conv") else NONE,
                   {pauto_finished = pauto_finished, refuted_by = SOME "R-conv"}))
         else NONE
     end)


(** Guard Solver **)

val guard_race_timeout =
      Attrib.setup_config_int \<^binding>\<open>\<phi>guard_race_timeout\<close> (K 500)
val guard_race_log =
      Attrib.setup_config_string \<^binding>\<open>\<phi>guard_race_log\<close> (K "")

fun prove_or_refute can_inst ctxt ctxt0 =
  let val search = auto_search_tac ctxt
   in timed_tac (Time.fromMilliseconds 30) search ORELSE
  (fn th =>
    let val timer = Timing.start ()
        val goals = Thm.cprems_of th
        val fail = Seq.make (fn () => (
              List.app (fn goal =>
                Phi_Reasoner.warn_pretty (Context.Proof ctxt) 1 (fn () => let open Pretty in
                  chunks (
                    [block (text "Fail to prove or falsify the following guard condition"),
                    Goal_Display.pretty_a_goal ctxt (Thm.term_of goal),
                    block (text "We assume the conditions do not hold and this assumption can cause reasoning failure.")]
                    )
                end)) goals
              ; NONE))

        (*a budget < 1ms would mean NO timeout at all (Timeout.ignored) — clamp*)
        val budget = Time.fromMilliseconds (Int.max (1, Config.get ctxt guard_race_timeout))

        fun diag level msg =
          Phi_Reasoner.warn_pretty (Context.Proof ctxt) level
            (fn () => Pretty.str ("guard race: " ^ msg ()))

        (*diagnostic I/O must never decide a proof: on any failure, report
          via diag and disable logging, never fail the tactic*)
        fun checked_io what f =
          (case Exn.capture_body f of
             Exn.Res r => SOME r
           | Exn.Exn exn =>
               if Race.contains_interrupt exn then Exn.reraise exn
               else (diag 2 (fn () => what ^ ": " ^ Runtime.exn_message exn); NONE))
        val log_path =
          (case Config.get ctxt guard_race_log of
             "" => NONE
           | s => checked_io "invalid \<phi>guard_race_log path" (fn () => Path.explode s))

        val protocol = Synchronized.var "guard_race.protocol"
                         {pauto_finished = false, refuted_by = NONE : string option}

        (*engine contract, both caller obligations: (a) racer bodies must be
          self-bounded — each gets its own Timeout.apply budget here; (b) this
          call site must not defer interrupts — nothing in phi-system does.
          P-auto stays first: the engine breaks concurrent claims to the
          lowest index and starts serial racers in order, both biasing ties
          toward Proved.*)
        val racers =
          [p_auto_racer search protocol th,
           r_conv_racer can_inst ctxt ctxt0 search protocol goals]
          |> map (fn (name, body) => (name, fn () => Timeout.apply budget body ()))

        val {winner, exits, forked} = Race.race racers

        val _ = List.app (fn (name, Race.Crashed exn) =>
                                diag 2 (fn () => "racer " ^ name ^ " crashed: " ^ Runtime.exn_message exn)
                            | _ => ()) exits

        (*total outcome mapping (D7 schema): a single-token verdict plus the
          winner's name feed both the TSV log and the human summary; the
          direct-win and post-race-record refutations share one verdict
          token — the exits column tells them apart (a recorded refutation
          has no "win" exit)*)
        val recorded_refuter =
          (case winner of
             NONE => #refuted_by (Synchronized.value protocol)
           | SOME _ => NONE)
        val (verdict, vwinner, result) =
          (case winner of
             SOME (name, Proved th') => ("proved", name, Seq.single th')
           | SOME (_, Refuted refuter) => ("refuted", refuter, Seq.empty)
           | NONE =>
               (case recorded_refuter of
                  SOME refuter => ("refuted", refuter, Seq.empty)
                | NONE => ("undecided", "-", fail)))
        val verdict_text =
          verdict ^ (if vwinner = "-" then "" else " by " ^ vwinner) ^
          (if is_some recorded_refuter then " (post-race record)" else "")

        val elapsed = Time.toMilliseconds (#elapsed (Timing.result timer))
        val _ =
          (case log_path of
             NONE => ()
           | SOME path =>
               ignore (checked_io "guard race log write failed" (fn () =>
                 let fun exit_code Race.Won = "win"
                       | exit_code Race.Gave_None = "none"
                       | exit_code Race.Timed_Out = "timeout"
                       | exit_code (Race.Crashed _) = "crash"
                       | exit_code Race.Cancelled = "cancelled"
                       | exit_code (Race.Discarded _) = "discarded"
                  in File.append path
                       (String.concatWith "\t"
                          [serial_string (), verdict, vwinner,
                           string_of_int elapsed, string_of_int (length goals),
                           if forked then "forked" else "serial",
                           String.concatWith ","
                             (map (fn (n, e) => n ^ ":" ^ exit_code e) exits)] ^ "\n")
                 end)))
        val _ = diag 2 (fn () =>
                  verdict_text ^ " in " ^ string_of_int elapsed ^ "ms, " ^
                  string_of_int (length goals) ^ " subgoal(s), " ^
                  (if forked then "forked" else "serial"))
     in result end)
  end

  


(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
fun guard_condition_solver {can_inst} ctxt0 th0 =
  let fun is_guard_mode (Const(\<^const_name>\<open>MODE_GUARD\<close>, _)) = true
        | is_guard_mode (Const(\<^const_name>\<open>NO_INST\<close>, _)) = true
        | is_guard_mode _ = false
      fun is_false (Const(\<^const_name>\<open>Premise\<close>, _) $ mode $ Const(\<^const_name>\<open>False\<close>, _))
            = is_guard_mode mode
        | is_false (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_false X
        | is_false _ = false
      val is_F = is_false (Thm.major_prem_of th0)

   in oblg_template true {can_inst = can_inst, fix_level= if can_inst then 1 else 2 }
  (fn ctxt => fn th =>
      let (*val (new_conds, th'1) = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
          val th' = @{thm' Premise_I} RS th'1*)
          val th' = th
          fun auto_tac ctxt =
                ALLGOALS (Simplifier.asm_full_simp_tac ctxt THEN_ALL_NEW quick_cut) THEN
                (if is_F
                 then timed_tac (Time.fromMilliseconds 250) (auto_search_tac ctxt)
                 else prove_or_refute can_inst ctxt ctxt0)
                (* (timed_tac (Time.fromMilliseconds 300) (auto_search_tac ctxt)) *)
        (*fun clarsimp_tac ctxt =
                Simplifier.asm_full_simp_tac (Guess_Instantiate.add_guess_inst_solver ctxt) THEN_ALL_NEW
             (*For some reason I don't know, some goals rely on unsafe tactics even when no variables occur 
               (if can_inst then Simplifier.asm_full_simp_tac ctxt
                            else Simplifier.safe_asm_full_simp_tac ctxt) THEN_ALL_NEW *)
                (fn i => fn th => timed_tac (Time.fromMilliseconds 300) (Classical.fast_tac (addSss ctxt) i) th)
          fun clarsimp'_tac ctxt =
                Simplifier.asm_full_simp_tac ctxt THEN_ALL_NEW
                (fn i => fn th => timed_tac (Time.fromMilliseconds 300) (Classical.fast_tac (addss ctxt) i) th)
          fun force_tac ctxt =
                Classical.clarify_tac ctxt THEN_ALL_NEW
                Simplifier.asm_full_simp_tac ctxt THEN_ALL_NEW
                (fn i => fn th => timed_tac (Time.fromMilliseconds 300) (Classical.first_best_tac (addss ctxt) i) th) *)
       in
        apply_tac ctxt (fn (ctxt,pre,aux,_) => fn thtt => thtt |> (quick_cut 1 THEN (head_only (
             pre (*THEN REPEAT_DETERM_N new_conds (HEADGOAL (resolve_tac ctxt @{thms' impI}))*)
                 THEN HEADGOAL (
                              case_split_by_annotations_leading_subgoal ctxt 
                 THEN_ALL_NEW Method.insert_tac ctxt aux
                 ) THEN auto_tac (Guess_Instantiate.add_guess_inst_solver ctxt addsimps @{thms' Premise_def})
               (* THEN_ALL_NEW (fn s => fn x => clarsimp_tac (ctxt addsimps @{thms' Premise_def}) s x) ) *)
               (*THEN_ALL_NEW (fn s => fn x => Clasimp.fast_force_tac
                      (Guess_Instantiate.add_guess_inst_solver ctxt addsimps @{thms' Premise_def}) s x)*) )
               ))
              |> Seq.take 1 ) Safe_Solver th'
       |> Seq.take 1
       |> Seq.pull
      end) ctxt0 th0
  end

val guard_condition_solver' = context_tactic_to_state_transition o guard_condition_solver

fun guard_condition_solver1 can_inst ctxt sequent =
  guard_condition_solver' can_inst (fn _ =>
    error (Pretty.string_of (Pretty.chunks [
        Pretty.str "Fail to solve the proof obligation automatically:",
        Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
  ]))) ctxt sequent

fun safe_obligation_solver {can_inst} ctxt0 =
        oblg_template true {can_inst = can_inst, fix_level= if can_inst then 1 else 2 }
  (fn ctxt => fn th =>
      let val th' = th
          fun clarsimp_tac ctxt =
                Simplifier.asm_full_simp_tac (Guess_Instantiate.add_guess_inst_solver ctxt) THEN_ALL_NEW
                (fn i => fn th => Classical.clarify_tac (addSss ctxt) i th)
       in
        apply_tac ctxt (fn (ctxt,pre,aux,_) => fn thtt => thtt |> (quick_cut 1 THEN (
             pre (*THEN REPEAT_DETERM_N new_conds (HEADGOAL (resolve_tac ctxt @{thms' impI}))*)
                 THEN HEADGOAL (
                              case_split_by_annotations_leading_subgoal ctxt 
                 THEN_ALL_NEW Method.insert_tac ctxt aux
                 THEN_ALL_NEW (fn s => fn x => clarsimp_tac (ctxt addsimps @{thms' Premise_def}) s x) )
               (*THEN_ALL_NEW (fn s => fn x => Clasimp.fast_force_tac
                      (Guess_Instantiate.add_guess_inst_solver ctxt addsimps @{thms' Premise_def}) s x)*) )
               )
              |> Seq.take 1 ) Safe_Solver th'
       |> Seq.take 1
       |> Seq.pull
      end)
  (Phi_Safe_Simps.equip ctxt0)

val safe_obligation_solver' = context_tactic_to_state_transition o safe_obligation_solver

fun safe_obligation_solver1 can_inst ctxt sequent =
  safe_obligation_solver' can_inst (fn _ =>
    error (Pretty.string_of (Pretty.chunks [
        Pretty.str "Fail to solve the proof obligation automatically:",
        Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
  ]))) ctxt sequent

(*case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>Premise\<close> $ _ $ Goal) => (
        (*Phi_Reasoner.info_pretty ctxt 2 (fn _ => Pretty.chunks [
            Pretty.str "Solving the following goal using \<open>clarsimp\<close> method...",
            Syntax.pretty_term ctxt Goal,
            Pretty.block (Pretty.here \<^here>)
        ]); *)
        guard_condition_solver' (fn _ =>
          error (Pretty.string_of (Pretty.chunks [
              Pretty.str "Fail to solve the proof obligation automatically:",
              Syntax.pretty_term ctxt (Phi_Help.leading_antecedent' sequent)
        ]))) (ctxt addsimps @{thms Premise_def}) sequent
     )
     | _ => raise THM ("auto_obligation_solver1: The leading antecedent of the given sequent \
              \is not a proof obligation.", 1, [sequent])*)



(*fun declare_local_assume_reasoners sequent i *)




end
