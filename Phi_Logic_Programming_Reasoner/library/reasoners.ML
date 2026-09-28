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
    another path in silence -- a defect was once found only because the obligation
    failed loudly.  Pair any `true` with a trace that reports the backtracking.*)
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

  (*The guard factory (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md): the preprocessing template
    -- oblg_template, the case split, the aux-fact insertion -- parameterised by the
    solving function it ends with (the type of `prove_or_refute kind`: can_inst, the
    guard-side context, what the digest step computed, then the state, UNSIMPLIFIED: each
    solving function decides its own simplification) and by that digest
    step, computed on the state after the case split and before the insertion.  A
    result carries the context the factory was called on plus what the solving
    function added.  The annotation of \<open>case_split\<close> is supported.*)
  val gen_guard_condition_solver : (Proof.context -> thm -> 'd)
                            -> (bool -> Proof.context -> 'd -> context_state -> context_state Seq.seq)
                            -> {can_inst: bool} -> context_state -> context_state Seq.seq
  (*which kind of guard a decision is about, Phi_Guard_Refute's datatype re-exported:
    Normal, or Check_Premise_Consistency -- the guard \<condition> False AS WRITTEN, which
    asks whether the premises are inconsistent, so the three steps that presuppose them
    consistent are off for it: the refutation by the simplifier, R-conv, R-nitpick's slice
    (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md, section 1: the check)*)
  datatype guard_kind = datatype Phi_Guard_Refute.guard_kind
  (*the kind of guard a goal state carries: Check_Premise_Consistency iff its leading
    antecedent concludes False under a premise tag (Premise _ False) under its \<And>/\<Longrightarrow>
    prefix; read on the state the factory receives, BEFORE oblg_template's rewrite turns
    ordinary guards into \<condition> False as well*)
  val guard_kind_of : thm -> guard_kind
  (*the judge instance: the factory over prove_or_refute with the guard digest, both
    under the kind of the guard as written*)
  val guard_condition_judge : {can_inst: bool} -> context_state -> context_state Seq.seq
  (*the guard digest: the whole goal state -- the guard's subgoals and the protected
    rest of the sequent -- and the context's assumptions, on the state after the case
    split and before the aux facts are inserted (those are derivable, so not part of
    the key); for the check the digest marker False is prepended, so that a check and an
    ordinary guard the template's rewrite turned into \<condition> False never share an entry*)
  val guard_digest : guard_kind -> Proof.context -> thm -> Hasher.digest
  (*the judge instance's digest step: guard_digest under the kind of the state given --
    the one value the engine and the smoke test's digest helper name*)
  val guard_digest_of : thm -> Proof.context -> thm -> Hasher.digest
  val prove_or_refute : guard_kind -> bool -> Proof.context -> Hasher.digest -> context_state -> context_state Seq.seq
  val string_of_guard_kind : guard_kind -> string
  (*the out-of-run instances, named after their first callers: the factory over
    p_auto_attempt -- no store read or written, no refuter, no judge, no undecided-guard
    warning (guard_simp_tac's loop warning still applies); the context comes back
    unchanged, and the search sees the lemma list the context carries, like every
    guard-side prover.  guard_condition_solver is also the reasoner of \<condition>[\<safe>] P
    and \<condition>[\<no>-\<inst>-\<safe>] P inside runs (PLPR.thy); the primed forms are its
    tactic shapes*)
  val guard_condition_solver : {can_inst: bool} -> context_state -> context_state Seq.seq
  val guard_condition_solver': {can_inst: bool}
                             -> (Proof.context -> thm -> thm) (*failure callback*)
                             -> Proof.context -> thm -> thm
  val guard_condition_solver1: {can_inst: bool} -> Proof.context -> thm -> thm

  (*run the tactic once, under the bound (thread CPU) if given, and keep only a solved state*)
  val try_prove_or_give_up : Time.time option -> (Proof.context -> tactic) -> Proof.context -> thm -> thm Seq.seq
  (*the guard-side simplification: asm_full_simp with \<phi>guard_simp and the guard
    cache's lemmas enabled, under 60 s of thread CPU (a timeout warns and yields the
    state unchanged); always exactly one state, and no refutation -- prove_or_refute
    reads the refutation by the simplifier off its result, for an ordinary guard.  It
    runs it on ctxt_g, the context carrying the entry's delta, and again on ctxt_g' when
    the judge replaces that delta; p_auto_solving runs it once; the obligation instance
    runs none, its fastforce simplifying in the same simpset itself*)
  val guard_simp_tac : Proof.context -> tactic
  (*P-auto's search, on a state guard_simp_tac has simplified, in the same enhanced
    context; P-auto = cpu_bounded_tac (guard_classic_prover_bound ctxt) o p_auto_tac*)
  val p_auto_tac : Proof.context -> tactic
  (*guard_simp_tac then P-auto once, no refutation: the out-of-run instance and the method
    \<phi>guard_P_auto -- a conclusion the simplification leaves as False is P-auto's to
    prove from the premises, or to fail on*)
  val p_auto_attempt : Proof.context -> tactic
  val cpu_bounded_tac : Time.time -> tactic -> tactic    (*thread CPU; an error without a CPU clock*)
  val guard_classic_prover_timeout : int Config.T (*milliseconds of thread CPU, 400 provisional*)
  val guard_classic_prover_bound : Proof.context -> Time.time


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


  structure Tactic_Configures : HOOKS (*alter the auxiliary facts, the pre-tactic and the context
      before the automatic solving -- the obligation solver and the guard factory*)

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

  (*the judge of the guard cache (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md, sections 1 and
    5): one optional function in a process-global ref, default NONE, consulted by
    prove_or_refute after the refuters; thm is the goal state, ctxt the guard-side
    context carrying the lemma list as it was BEFORE this entry's delta was applied,
    outer_ctxt the run's context, delta this entry's delta.  Provable carries the
    delta that REPLACES this entry's, its lemmas with RAW measured times.*)
  type judge_arg = {ctxt : Proof.context, outer_ctxt : Proof.context, can_inst : bool, thm : thm,
                    delta : Phi_Guard_Cache.delta}
  datatype judgement = Provable of Phi_Guard_Cache.delta | Unprovable
  val judge : (judge_arg -> judgement) option Unsynchronized.ref

  (*the guard_decision Event_Log category, written under ML_debugger: one record
    per prove_or_refute call -- verdict (proved/refuted/unknown), hit (the entry's
    verdict, or none), refuter (R-conv/R-nitpick/guard_simp_tac/-), judge (Provable/Unprovable/-),
    kind (Normal/Check_Premise_Consistency), wall-clock ms, the guard digest in hex, #subgoals*)

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

structure Tactic_Configures = Hooks (
  type arg = unit
  type state = thm list (*aux thms*) * tactic * Proof.context
)

(*Runs the hook fold of Tactic_Configures to obtain the configured (aux, pre, ctxt),
  then the body on them OUTSIDE the hook, so that a body may return results of any
  type; `prj` reads the theorem out of a result for the SOLVED' filter: a result is
  kept iff it has fewer premises than the input.  A hook raising Success with a
  tactic of its own no longer replaces the body: its state is used like the fold's
  result and the body runs (no registration does that today).*)
fun apply_tac prj ctxt body th =
  let val (aux, pre, ctxt') =
        Tactic_Configures.invoke (Context.Proof ctxt) () (aux_thms ctxt, all_tac, ctxt)
   in body (ctxt', pre, aux) th
   |> Seq.filter (fn st => Thm.nprems_of (prj st) < Thm.nprems_of th)
  end

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
(*Polymorphic in the result type of `f`: `inj` makes a result of a theorem that never
  reached `f` (the exits below), `on_thm` applies a theorem post-pass to a result; the
  theorem-returning callers pass I and I, the guard factory pairs with its context.*)
fun oblg_template report_time {can_inst, fix_level} {inj, on_thm} f ctxt th00 = Seq.make (fn () =>
  PLPR_Statistics.measure_time_of_proof_evaluation' report_time ctxt (fn () =>
  let val th01 = case PLPR_Syntax.dest_premise_tag_opt (major_prem_of th00)
                   of SOME _ => th00
                    | NONE => @{thm' Premise_D[where mode=default]} RS th00
      val th = Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
              PLPR_Syntax.premise_tag_conv (K true) (Simplifier.full_rewrite ctxt)) ctxt) 1 th01
      fun inj_ret (th, seq) = (inj th, Seq.map inj seq)
   in case Thm.major_prem_of th
   of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) =>
        SOME (inj (@{thm' TrueI} RS' (ctxt, th)), Seq.empty)
    | _ => case fast_inst can_inst th
   of SOME ret => SOME (inj_ret ret)
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
   of SOME ret => SOME (inj_ret ret)
    | NONE => (
      case LPR_inst ctxt' th2
        of SOME ret => f ctxt' ret
         | _ => f ctxt' th2))
   |> not (null fixing_targets) ? Option.map (fn (r, seq') =>
        let val f = on_thm (singleton (Variable.export_inst (Phi_Help.uncertify_vars instc)))
         in (f r, Seq.map f seq')
        end)
  end end) ())


(*** Auxiliaries ***)

(*protects the remaining goals and only attack the first one; a result of any type
  through inj (a state the tactic never saw) and on_thm (the conclude post-pass)*)
fun head_only' inj on_thm tac th =
  if Thm.nprems_of th = 0
  then Seq.single (inj th)
  else Goal.protect 1 th |> tac |> Seq.map (on_thm Goal.conclude)

fun head_only tac = head_only' I I tac


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

fun defer_obligation cfg contract = oblg_template false cfg {inj = I, on_thm = I} (fn ctxt => fn thm =>
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
      oblg_template true {can_inst=true, fix_level=0} {inj = I, on_thm = I} (fn ctxt => fn th =>
        let val (_, th'1) = collect_obligation_premises (true, true, Config.get ctxt existential_obligation) ctxt th
            val th' = @{thm' Premise_I} RS th'1
         in th'
         |> head_only (apply_tac I ctxt (fn (ctxt,pre,aux) =>
            pre THEN HEADGOAL (Method.insert_tac ctxt aux)
                THEN (fn st =>
                   let (*The one place all failure text is composed: the forked
                         report and the promise branch
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
                   end)))
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

(*a subgoal whose conclusion, under its \<And>/\<Longrightarrow> prefix, is the bare False -- not the
  tagged one (Premise _ False): the factory's front quick_cut runs before Premise_def is
  unfolded and must stay a no-op there*)
fun concl_is_false subgoal =
  case Logic.strip_assums_concl subgoal
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ Const(\<^const_name>\<open>False\<close>, _) => true
     | _ => false
fun quick_cut i th = if concl_is_false (Logic.nth_prem (i, Thm.prop_of th)) then Seq.empty else Seq.single th

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

(*** Guard decision ***)

(*One prove_or_refute call decides one guard (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md,
  sections 5 and 6): the entry under the guard digest is read from the store, its
  lemmas are replayed and enabled, the guard is simplified once (guard_simp_tac) and,
  for an ordinary guard, a conclusion left as False refutes it; otherwise
  P-auto proves the guard or fails, and on a failure
  the entry's verdict selects what runs next -- the refuters R-conv and R-nitpick,
  then the judge -- one after another on the run's thread, each bounding itself.
  A non-interrupt exception of a prover, a refuter, a replay or the judge is the
  run's exception.*)

(*the kind of guard the call decides (the signature): Normal, or the check
  Check_Premise_Consistency, for which the three steps that presuppose consistent
  premises are off*)
datatype guard_kind = datatype Phi_Guard_Refute.guard_kind

(*400 ms of thread CPU: the bound of P-auto and of R-conv, and the replay floor of a
  judge lemma; guard_simp_tac has its own 60 s.  Thread CPU, not wall clock, so that
  machine load cannot flip a verdict.*)
val guard_classic_prover_timeout =
      Attrib.setup_config_int \<^binding>\<open>\<phi>guard_classic_prover_timeout\<close> (K 400)
(*a budget < 1ms would mean NO timeout at all (Timeout.ignored) -- clamp*)
fun guard_classic_prover_bound ctxt =
      Time.fromMilliseconds (Int.max (1, Config.get ctxt guard_classic_prover_timeout))

(*the guard side's one way of bounding a computation: the calling thread's CPU, no
  wall clock -- Thread_CPU.apply raises an error where the thread has no CPU clock;
  the refuter that waits on an external process, R-nitpick, keeps wall clock
  (Thread_CPU: "a blocked thread never reaches the limit")*)
fun cpu_bounded bound f x = Thread_CPU.apply {thread_cpu = bound, wall = NONE} f x
fun cpu_bounded_seq bound s =
  Seq.make (fn () => cpu_bounded bound Seq.pull s handle Timeout.TIMEOUT _ => NONE)
fun cpu_bounded_tac bound tac th = cpu_bounded_seq bound (tac th)

(** The provers **)

(*the acceptance criterion of every search: its solved states, as a lazy
  sequence -- nothing runs until it is pulled, so a caller's timeout still
  covers the search*)
fun solved_states search st = Seq.filter Thm.no_prems (search st)
fun search_solved search st =
  Option.map #1 (Seq.pull (solved_states search st))

(*every consumer of the guard cache's lemmas enhances its own context: \<phi>guard_simp,
  then the lemmas under fresh budgets (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md, section 4)*)
val enhance_for_guard =
      Phi_Guard_Cache.enhance_with_lemmas o Phi_Guard_Cache.Guard_Simp_SS.enhance

(*The guard-side simplification: asm_full_simp on every subgoal, in the enhanced
  context, under 60 s of thread CPU -- several times the slowest simplification
  measured (13 s, a Quicksort slice-bound guard with 26 premises under
  linarith_split_limit = 20), so a timeout means the simplifier is looping: it is warned
  about, and the state comes back unchanged.  Exactly one state, always: the first
  simplified state only (Seq.take 1, so the one bound covers the whole simplification),
  and the timeout path yields the state it was given -- a caller composing with THEN
  would read an empty sequence as a failed attempt, and prove_or_refute's pulls stay
  total.  No refutation here: prove_or_refute reads the refutation by the simplifier off
  the result, for an ordinary guard only (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md, section 1:
  guard_simp_tac; section 5 step 1 1/2).  prove_or_refute runs it on ctxt_g, the context that carries the
  entry's delta, and again on ctxt_g' when the judge replaces that delta; p_auto_solving
  runs it once; the obligation instance runs none (its fastforce simplifies in the same
  simpset itself).  P-auto has no simplification step of its own -- its search still
  simplifies through addss -- so the state it is given is this function's result.*)
fun guard_simp_tac ctxt th =
  let val seq = Seq.take 1 (ALLGOALS (Simplifier.asm_full_simp_tac (enhance_for_guard ctxt)) th)
   in Seq.make (fn () =>
        cpu_bounded (Time.fromSeconds 60) Seq.pull seq
        handle Timeout.TIMEOUT _ =>
          (warning (Pretty.string_of (let open Pretty in
             chunks (block (text "The system simplifier probably loops on:")
                     :: map (Goal_Display.pretty_a_goal ctxt o Thm.term_of) (Thm.cprems_of th)) end));
           SOME (th, Seq.empty)))
  end

(*P-auto's search: nodup_depth_tac (depth 10) in the enhanced context, solved states
  only, on a state guard_simp_tac has simplified; P-auto is this under
  \<phi>guard_classic_prover_timeout.  R-conv uses auto_search_tac instead.*)
fun p_auto_tac ctxt =
  let val ctxt = enhance_for_guard (Context_Position.set_visible false ctxt)
      fun main_tac i = CHANGED (nodup_depth_tac (addss ctxt) 10 i)
   in solved_states (norm_tac (REPEAT_DETERM (FIRSTGOAL main_tac) #> Seq.take 1))
  end

(*one whole attempt: the guard-side simplification, then P-auto once under
  \<phi>guard_classic_prover_timeout -- the out-of-run instance and the method
  \<phi>guard_P_auto share this one definition, so the two cannot drift apart*)
fun p_auto_attempt ctxt =
  guard_simp_tac ctxt THEN cpu_bounded_tac (guard_classic_prover_bound ctxt) (p_auto_tac ctxt)

(** The refuters **)

val negation = \<^cterm>\<open>Not\<close>

(*R-conv (GUARD_NITPICK_FALSIFY_PLAN §2.2): refute by PROVING the negation — each
  subgoal's conclusion is negated under its \<And>/\<Longrightarrow> prefix and handed to the
  classical search in the context enhanced (\<phi>guard_simp, the lemmas under fresh
  budgets).  The whole computation, negation included, runs under
  \<phi>guard_classic_prover_timeout of thread CPU; TIMEOUT and a non-Trueprop
  conclusion (Unsupported) are "not refuted".
  ctxt is prove_or_refute's ctxt_g, the guard-side context with the lemmas;
  ctxt0 the run's context, the one
  gen_guard_condition_solver was called on — Variable.export ctxt ctxt0 is direction-
  sensitive, do not swap the two.  can_inst = true freezes the residual
  schematics (a universal refutation); false exports them back (an
  existential refutation — an accepted completeness-only weakening, plan
  §2.3).  This variable discipline is the proof-searcher's own,
  intentionally different from R-nitpick's as-is discipline — see the
  duality note in plan §2.3.
  The freeze branch MUST build its own
  search over the import context ctxt' — its goals carry Frees only ctxt'
  declares, and the search runs under USER proof contexts, whose claset
  wrappers (a stock user extension point, outside any audit of phi-system)
  must not receive a context that misdescribes the frozen Frees.  The
  export branch deliberately keeps the shared ctxt search: its goals live
  in ctxt0 and ctxt merely over-declares (ctxt extends ctxt0) — the safe
  direction; do not "fix" it to search under ctxt0.  Only a bool leaves
  this refuter; consuming the proved state would additionally require
  Variable.export through ctxt'.  (That search_solved accepts on no_prems
  alone, ignoring hyps/tpairs, is a recorded hardening candidate —
  plan §8.)*)
fun r_conv can_inst ctxt ctxt0 goals =
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
      fun refuted () =
        (map (fn goal =>
             Goal.init (conv_goal (Term.declare_free_names (Thm.term_of goal) Name.context) goal)
           ) goals
           |> (fn gs =>
                if can_inst
                then let val ((_, gs'), ctxt') = Variable.import false gs ctxt
                      in exists (is_some o search_solved (auto_search_tac (enhance_for_guard ctxt'))) gs'
                     end
                else Variable.export ctxt ctxt0 gs
                     |> exists (is_some o search_solved (auto_search_tac (enhance_for_guard ctxt)))))
        handle Unsupported => false
   in cpu_bounded (guard_classic_prover_bound ctxt) refuted ()
      handle Timeout.TIMEOUT _ => false
  end


(*R-nitpick (plan §2.3): refute by MODEL — a finite countermodel of the
  subgoal under the collected context assumptions.  The search is
  Phi_Guard_Refute.nitpick, which preprocesses the guard (weakening hooks,
  the memory-model and per-struct rewrites, datatype case splits, and -- for
  an ordinary guard -- a slice down to the conclusion's variables) and then
  hands the result to the patched Nitpick copy Phi_Nitpick: for an ordinary
  guard the premises are trusted rather than re-derived; for the check they
  are antecedents of the conjecture, so that a countermodel is a model of
  them (the comment above Phi_Guard_Refute.nitpick).  That recipe is what
  makes the refuter useful: on the replayed
  corpus it refutes 222 of 247 guards where the unpreprocessed call refutes
  far fewer, at zero misjudgment over 161 guards known provable (plan §22).
  The variable discipline is zero-transform, intentionally OPPOSITE to
  R-conv's freeze/export (duality note, plan §2.3 — do not cross-correct):
  the subgoal goes in as-is; falsify's close_form \<And>-closes residual Vars
  (= refute every instantiation) and lets the model pick the Frees
  (= arbitrary but fixed).  Auto_Try mode is silent by construction
  (messages are buffered into the ignored second component).  Assumptions
  travel with the goal so the model must satisfy them (dropping one breaks the
  immunity argument; the context asked is the goal-side ctxt, as Nitpick's own
  entry does); which of them survive is
  Phi_Guard_Refute's premise filter, not this refuter's business.*)

(*verbatim from nitpick.ML:972-982 (not exported); the call below mirrors
  the entry recipe of pick_nits_in_subgoal, nitpick.ML:984-996 — the full
  assumption set, with fixed-variable defining equations folded into a
  substitution that IS threaded through.  Keep in sync with those lines.*)
fun is_fixed_equation ctxt
      (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ Free (s, _) $ Const _) =
      Variable.is_fixed ctxt s
  | is_fixed_equation _ _ = false
fun extract_fixed_frees ctxt (assms, t) =
  let val (subst, other_assms) =
        List.partition (is_fixed_equation ctxt) assms
        |>> map Logic.dest_equals
   in (subst, other_assms, subst_atomic subst t) end

(*pinned parameters (plan §2.3): Nitpick_Commands.default_params reads
  theory-level state the user command nitpick_params can write.  Pinned is
  every STRING-SETTABLE key whose pollution could change a verdict
  (expect, falsify), burn the budget (tac_timeout, card, max_threads —
  Normal-mode extraction would otherwise hand Kodkod a platform-wide
  thread pool where Nitpick's own auto mode uses 1), break silence or
  determinism (debug, verbose, overlord, spy), or crash the JVM (a *_JNI
  sat_solver).  Structural residue this interface cannot pin: term-list
  keys (whack, eval, need) and per-type/per-const assignments (card <T>,
  iter <c>, ...) are read straight off the raw params — tolerated, worst
  known effect is completeness-only (plan §2.3).  spy=false is
  load-bearing beyond silence: spying would call Proof.goal on the
  goal-less Proof.init state below; the NITPICK_SPY env var ORs past this
  pin and is guarded at assembly instead.  The nitpick_params command
  validates KEYS only, so a malformed stored value errors HERE, inside
  R-nitpick, and propagates as the run's exception like any other exception
  of a refuter (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md section 5).  Time strings
  are decimal seconds (§1.2-4); tac_timeout pinned
  low because the 0.5s default is billed per candidate type in pre-Kodkod
  monotonicity checks (§1.2-2).

  The budget passed in is the model search's OWN timeout, fixed and never
  charged for preprocessing.  Nitpick divides the number across the card
  scopes, and its own net (budget + timeout_bonus) enforces it; preprocessing
  is covered only by R-nitpick's bound per subgoal.

  mono = true drops Nitpick's per-type monotonicity INFERENCE (default
  "smart", nitpick_commands.ML:43) and simply assumes monotonicity, so the
  scope search does not spend the budget re-deriving it.

  card and user_axioms are measured choices, not defaults.  user_axioms =
  false keeps phi-system's ten monomorphic user axioms out of the problem:
  the flag that decides certification does NOT consult the relevance filter
  (got_all_mono_user_axioms, nitpick_preproc.ML:1038, is
  "user_axioms = SOME true orelse null mono_nondefs"), so their mere
  existence in the theory would downgrade every verdict anyway — see the
  verdict map below, which is what pays for this.  card = 1-6 is an
  INTERVAL on purpose: its scopes go to Kodkod in one batch and the
  smallest model short-circuits the rest, where a single value loses
  refutations and costs several times the total time.  No per-type
  cardinality is pinned: with the axioms out, phi-system's abstract types
  do not enter the problem at all, so pinning them is idle at best.*)
(*The model search's own timeout, separate from R-nitpick's bounds: preprocessing is
  not charged against the search, whose reach should not depend on it.  Declared to
  Nitpick, whose own net (+ timeout_bonus) enforces it; R-nitpick's bound per subgoal
  and its outer net derive from it, so the three stay consistent.*)
val guard_refute_timeout =
      Attrib.setup_config_int \<^binding>\<open>\<phi>guard_refute_timeout\<close> (K 2000)

fun pinned_nitpick_params ctxt budget =
  Nitpick_Commands.default_params (Proof_Context.theory_of ctxt)
    [("expect", ""), ("falsify", "true"),
     ("debug", "false"), ("verbose", "false"), ("overlord", "false"), ("spy", "false"),
     ("max_genuine", "1"), ("max_potential", "0"), ("max_threads", "1"),
     ("sat_solver", "SAT4J"), ("batch_size", "smart"),
     ("card", "1-6"), ("user_axioms", "false"), ("mono", "true"),
     ("timeout", Real.fmt (StringCvt.FIX (SOME 3)) (Time.toReal budget)),
     ("tac_timeout", "0.05")]

(*Single path: the external kodkodi process (kodkod_scala forced false), so each
  invocation launches its own JVM ($KODKODI/bin/kodkodi through the bash_process
  server; never overlord, never a *_JNI SAT solver).  The JVM launch runs inside
  Nitpick's own net, so the bounds' margins are unchanged.  The in-process Scala call
  was the pipeline's only source of Output.Protocol_Message; a stray one now leaves
  R-nitpick as the run's exception.*)
(*Provable means the preprocessing simplifier closed the guard, which is a
  real proof of the ORIGINAL guard but yields no proof object here; this
  refuter therefore only stands down -- P-auto, which has already failed, was
  the one to produce the theorem.

  quasi_genuine counts as a refutation.  It has to: under user_axioms = false Nitpick can never
  certify a model genuine, so the two codes together are the only refutation
  this refuter can ever report.  What that costs: (a) what is waived are
  phi-system's ten monomorphic user axioms, all derivable from HOL's own, so
  a model ignoring them models a theory no stronger than HOL's; (b) a wrong
  refutation costs COMPLETENESS only — a guard judged false leaves one
  reasoning rule unapplied, and the undecided exit already assumes the guard
  fails — and P-auto has already had its attempt; (c) quasi_genuine does not
  say WHICH check downgraded it, so accepting it also accepts downgrades from
  wf / finitize / total_consts / bisim_depth.  Over the replayed corpus only
  user_axioms ever fired — a property of that corpus, not a guarantee.
  Unknown (Nitpick found nothing, or the budget was already spent in
  preprocessing) stands down as well.  Other exceptions are NOT absorbed:
  they leave the refuter as the run's exception — we bypass
  Nitpick_Commands.handle_exceptions, incidentally a silence win (its
  NOT_SUPPORTED bare warning is unreachable).

  The bounds (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md section 6), wall clock since
  the search waits on an external process: the subgoals one after another,
  each under \<phi>guard_refute_timeout + 5 s -- strictly above worst
  preprocessing (2.6 s) + Nitpick's net (+1 s) at any config value, with
  preprocessing (0.4 s median) uncharged -- so one subgoal's overrun moves on
  to the next; the whole under \<phi>guard_refute_timeout + 5 s x the number of
  subgoals -- below the sum of the bounds per subgoal from two subgoals on,
  equal to it at one -- so the net normally ends R-nitpick inside the
  running subgoal.  Either TIMEOUT is "not refuted" for what it covers.
  The screen: a schematic TYPE variable in any assumption silences the whole
  refuter, in a subgoal silences that subgoal (no monotonization —
  "substitute a typical type and refute" is unsound, since type
  instantiation is also the prover's choice).  NITPICK_SPY=yes ORs past the
  spy pin and would crash on the goal-less Proof.init state — ruled an
  absent-refuter condition.  The tested term is derived from the screened
  one by subst_atomic over screened assumptions (which cannot introduce
  TVars — the global assumption screen is load-bearing for the per-goal
  one), and the assumptions are asked once from the goal-side ctxt.*)
fun r_nitpick kind ctxt goals =
  let val refute_timeout = Time.fromMilliseconds (Config.get ctxt guard_refute_timeout)
      val margin = seconds 5.0
      val bound = refute_timeout + margin   (*one subgoal*)
      fun tvar_free t = null (Term.add_tvars t [])
      val nctxt = Config.put Kodkod.kodkod_scala false ctxt
      val assms0 = map Thm.term_of (Assumption.all_assms_of nctxt)
   in getenv "NITPICK_SPY" <> "yes" andalso forall tvar_free assms0 andalso
      let val params = Lazy.lazy (fn () => pinned_nitpick_params nctxt refute_timeout)
          val n = length goals
          fun refutes (k, goal) =
            let val t0 = Thm.term_of goal
             in tvar_free t0 andalso
                (Timeout.apply bound (fn () =>
                   Phi_Guard_Refute.nitpick kind nctxt (Lazy.force params) (k + 1, n)
                     (extract_fixed_frees nctxt (assms0, t0)) = Phi_Guard_Refute.Refuted) ()
                 handle Timeout.TIMEOUT _ => false)
            end
       in Timeout.apply (refute_timeout + Time.scale (Real.fromInt n) margin)
            (fn () => exists refutes (map_index I goals)) ()
          handle Timeout.TIMEOUT _ => false
      end
  end


(** The judge **)

(*ONE optional function in a process-global ref (plan section 1), default NONE,
  installed by ML code (phase 2: the LLM judge).  Consulted by prove_or_refute
  where section 5 says, on the run's own thread, concurrently across runs, with
  the guard-side context as it was before this entry's delta was applied -- the
  lemmas of earlier guards are in it, and the judge may delete any of them by
  its proposition, read off Phi_Guard_Cache.get_lemmas ctxt (a lemma stated with
  an outer \<And> is held so until a run or block boundary generalises it) -- and
  with this entry's delta.  Its delta REPLACES this
  entry's, relative to that same context; each added lemma must be a closed
  statement of type prop, certifiable by Thm.cterm_of outer_ctxt and provable
  by its own method text citing theory-level facts only, with RAW measured
  times on this machine's clock -- the clock the delta it receives is on too;
  prove_or_refute converts both ways.  A run re-entered inside the judge
  enables its own lemmas on top of ctxt's (nesting is not designed for).*)
type judge_arg = {ctxt : Proof.context, outer_ctxt : Proof.context, can_inst : bool, thm : thm,
                  delta : Phi_Guard_Cache.delta}
datatype judgement = Provable of Phi_Guard_Cache.delta | Unprovable
val judge : (judge_arg -> judgement) option Unsynchronized.ref = Unsynchronized.ref NONE


(** One prove_or_refute call **)

(*the guard_decision Event_Log record, written under ML_debugger: the verdict, the
  path -- the entry's verdict (hit), which refuter, the judge's answer -- the kind of
  guard, the call's wall clock, the guard digest and the number of subgoals*)
val guard_decision_category =
  Event_Log.category {name = "guard_decision", enabled = fn () => true,
    encode = fn {verdict, hit, refuter, judge, kind, elapsed_ms, digest, n_goals} =>
      ([("verdict", verdict), ("hit", hit), ("refuter", refuter), ("judge", judge),
        ("kind", kind), ("elapsed_ms", string_of_int elapsed_ms), ("digest", digest),
        ("subgoals", string_of_int n_goals)], [])}

fun string_of_verdict Phi_Guard_Cache.Proved = "proved"
  | string_of_verdict Phi_Guard_Cache.Refuted = "refuted"
  | string_of_verdict Phi_Guard_Cache.Unknown = "unknown"

(*the kind as the record and the trace line render it: the constructor's own spelling*)
fun string_of_guard_kind Normal = "Normal"
  | string_of_guard_kind Check_Premise_Consistency = "Check_Premise_Consistency"

(*the undecided-guard warning -- neither a proof nor a refutation, and no judge -- and,
  for the check, the undecided-check warning in its place: one gate, trace-gated like
  every reasoner warning, one message per goal, the kind selecting the two text lines*)
fun undecided_guard_warning kind ctxt goals =
  let val (head, tail) =
        case kind of
          Normal =>
            ("Fail to prove or falsify the following guard condition",
             "We assume the conditions do not hold and this assumption can cause reasoning failure.")
        | Check_Premise_Consistency =>
            ("Fail to check the consistency of the premises:",
             "We assume they are consistent. If they are not, the reasoning continues \
             \in a case that cannot occur, and may fail there.")
   in List.app (fn goal =>
        Phi_Reasoner.warn_pretty (Context.Proof ctxt) 1 (fn () => let open Pretty in
          chunks [block (text head), Goal_Display.pretty_a_goal ctxt (Thm.term_of goal), block (text tail)]
        end)) goals
  end

(*the loud guard warning: the entry said Proved and the judge (no refuter could refute
  the guard) or the simplifier (a conclusion rewritten to False) overturned it; printed
  unconditionally, `who` naming which*)
fun loud_guard_warning ctxt who goals =
  warning (Pretty.string_of (let open Pretty in
    chunks (block (text ("A guard condition proved before is now refuted by " ^ who ^ ":"))
            :: map (Goal_Display.pretty_a_goal ctxt o Thm.term_of) goals)
  end))

(*the refuter name a refutation by the simplifier carries in the decision record*)
val simp_refuter = "guard_simp_tac"

(*The replay of one lemma (plan section 5 step 1): the statement certified in ctxt0
  and proved by its own method text in ctxt0 exactly as the run holds it -- nothing
  enhanced, no other lemma enabled -- under Phi_Proof_Store.replay_limits of the
  recorded times, each floored by the classic bound.  Fails_To_Certify = TYPE, TERM
  or THM (the last from Goal.init on a non-prop); Fails_To_Replay = Auto_Fail, the
  whole failure vocabulary of eval_prf_str; anything else, the interrupt family
  included, propagates.  The goal is Goal.init's, concluded here; eval_prf_str's own
  protect/conclude pair works on the layer it adds.*)
datatype failure = Fails_To_Certify | Fails_To_Replay
datatype replay = Replayed of thm | Failed of failure

fun failure_text Fails_To_Certify = "fails to certify (its statement is not a well-typed prop in this context)"
  | failure_text Fails_To_Replay =
      "fails to replay (its method text cites a fact this context does not have, or overruns its recorded time)"

(*the times of a delta's lemmas through f*)
fun map_times f ({added, deleted} : Phi_Guard_Cache.delta) : Phi_Guard_Cache.delta =
  {added = map (fn (stmt, (times, script), tier) => (stmt, (f times, script), tier)) added,
   deleted = deleted}

fun replay_lemma ctxt0 ((stmt, (times, script), _) : Phi_Guard_Cache.lemma) =
  let val floor = guard_classic_prover_bound ctxt0
      val limits = Phi_Proof_Store.replay_limits
                     {thread_cpu = Time.max (#thread_cpu times, floor), wall = Time.max (#wall times, floor)}
      val kws = Keyword.no_major_keywords (Thy_Header.get_keywords (Proof_Context.theory_of ctxt0))
   in case (SOME (Goal.init (Thm.cterm_of ctxt0 stmt))
            handle TYPE _ => NONE | TERM _ => NONE | THM _ => NONE) of
        NONE => Failed Fails_To_Certify
      | SOME goal =>
          (Replayed (Goal.conclude (snd (snd (Phi_Sledgehammer_Solver.eval_prf_str kws 1 limits script (ctxt0, goal)))))
           handle Phi_Sledgehammer_Solver.Auto_Fail _ => Failed Fails_To_Replay)
  end

(*the dropped-lemma warning: unconditional, naming the statement and the failure*)
fun dropped_lemma_warning ctxt0 stmt failure =
  warning (Pretty.string_of (Pretty.block [
    Pretty.str ("The guard cache drops a lemma that " ^ failure_text failure ^ ":"),
    Pretty.brk 1, Syntax.pretty_term ctxt0 stmt]))

(*One prove_or_refute call (plan sections 5 and 6): the kind of the guard as written
  (guard_condition_judge reads it on the state before oblg_template), can_inst, the
  guard-side context, the guard digest, then the run's state -- the run's context ctxt0
  and the goal state.  The context it returns is ctxt0 with this guard's delta applied.*)
fun prove_or_refute kind can_inst ctxt d (ctxt0, th0) =
  let val timer = Timing.start ()
      val thy = Proof_Context.theory_of ctxt0
      val use_store = Config.get ctxt0 Phi_Guard_Cache.guard_cache
      val entry = if use_store then Phi_Guard_Cache.lookup_entry thy d else NONE
      val entry_verdict = Option.map #verdict entry
      fun write delta verdict =
        if use_store then Phi_Guard_Cache.write_entry thy d {delta = delta, verdict = verdict} else ()
      fun budget_of ((_, _, tier) : Phi_Guard_Cache.lemma) = Phi_Guard_Cache.budget_of_tier ctxt0 tier
      (*a delta -- its deletions, then its replayed lemmas -- onto the lemma lists of
        the call's two base contexts, ctxt0 (returned) and ctxt (the provers'): step 1
        and step 6 both start from these, never from each other's result, and both
        simplify th0, the state the call was given, never each other's result.
        Returns the delta it applied, which is what the store gets.*)
      fun apply_delta deleted replayed =
        let fun into c = c |> Phi_Guard_Cache.delete_lemmas deleted
                           |> fold (fn (lemma, th) => Phi_Guard_Cache.add_lemma (th, budget_of lemma)) replayed
         in ({added = map fst replayed, deleted = deleted} : Phi_Guard_Cache.delta, into ctxt0, into ctxt) end

      (*step 1: the entry's lemmas replayed in ctxt0, in order; a failure drops the
        lemma from the entry; the delta with the survivors goes onto the lemma list of
        ctxt0 (ctxt1, returned) and of ctxt (ctxt_g, where every prover of this call
        starts)*)
      val {added = stored, deleted} =
            case entry of SOME {delta, ...} => delta | NONE => Phi_Guard_Cache.empty_delta
      val replays = map (fn lemma => (lemma, replay_lemma ctxt0 lemma)) stored
      val replayed = map_filter (fn (lemma, Replayed th) => SOME (lemma, th) | _ => NONE) replays
      val _ = List.app (fn (_, Replayed _) => ()
                         | ((stmt, _, _), Failed failure) => dropped_lemma_warning ctxt0 stmt failure) replays
      val (delta, ctxt1, ctxt_g) = apply_delta deleted replayed
      (*every write but the judge's stores the entry as step 1 left it*)
      fun keep verdict = write delta verdict
      (*a dropped lemma rewrites the entry: the survivors, its verdict unchanged*)
      val _ = case entry of
                SOME {verdict, ...} =>
                  if length replayed < length stored then keep verdict else ()
              | NONE => ()

      fun refuted_by name =
        (keep Phi_Guard_Cache.Refuted;
         {verdict = Phi_Guard_Cache.Refuted, refuter = SOME name, judge = NONE, result = Seq.empty})

      (*the state this call was given, simplified in a guard-side context -- what P-auto,
        both refuters and the judge all see; guard_simp_tac always yields exactly one
        state, so the NONE arm is unreachable*)
      fun simplified_in ctxt' = case Seq.pull (guard_simp_tac ctxt' th0) of SOME (th, _) => th | NONE => th0
      (*the refutation by the simplifier, for an ordinary guard: a subgoal whose conclusion
        the simplification left as False; for the check that conclusion is the normal state
        before P-auto proves it from the premises*)
      fun refuted_by_simp th =
            case kind of Normal => exists concl_is_false (Thm.prems_of th)
                       | Check_Premise_Consistency => false

      (*step 1 1/2: the simplification in ctxt_g, then the refutation by the simplifier:
        Refuted, and nothing else runs*)
      val th1 = simplified_in ctxt_g
      val by_simp = refuted_by_simp th1
      (*the goals the warnings, the record and the trace line describe: the state the
        call was given, UNSIMPLIFIED, when the simplifier refuted; the simplified one otherwise*)
      val goals = Thm.cprems_of (if by_simp then th0 else th1)

      (*steps 2 to 6, on the simplified state th*)
      fun decide th =
        let
          (*step 2: P-auto, the search on the simplified state, under the classic bound
            of thread CPU; p_auto_tac enhances the context itself, so every P-auto run
            has fresh lemma budgets*)
          fun p_auto ctxt' th =
            Option.map #1 (Seq.pull (cpu_bounded_tac (guard_classic_prover_bound ctxt0) (p_auto_tac ctxt') th))

          (*step 6: the judge, on the guard-side context as it was BEFORE this entry's
            delta was applied, and this entry's delta; its delta REPLACES this entry's:
            it is applied to the lists of that moment (ctxt, ctxt0); a lemma that fails,
            or a P-auto that still fails, is the judge's error.  Times cross the judge on
            this machine's clock in both directions: the delta handed over is converted
            from the store's standard-machine times, the answer's RAW times are
            normalised on receipt -- so a lemma handed back as received is measured, not
            scaled twice.*)
          fun consult j =
            case j {ctxt = ctxt, outer_ctxt = ctxt0, can_inst = can_inst, thm = th,
                    delta = map_times Phi_Proof_Store.machine_time delta} of
              Provable answer =>
                let val {added = new, deleted = deleted'} = map_times Phi_Proof_Store.standard_time answer
                    val replayed' = map (fn lemma as (stmt, _, _) =>
                          case replay_lemma ctxt0 lemma of
                            Replayed th => (lemma, th)
                          | Failed failure => error (Pretty.string_of (Pretty.block [
                                Pretty.str ("The judge is broken: its lemma " ^ failure_text failure ^ ":"),
                                Pretty.brk 1, Syntax.pretty_term ctxt0 stmt]))) new
                    val (delta', ctxt1', ctxt_g') = apply_delta deleted' replayed'
                    (*the judge's lemmas are simp rules: the guard is simplified again
                      with them, from the state the call was given, so that what P-auto
                      proves is what the judge's delta alone produces -- a later call
                      reproduces it*)
                    val th' = simplified_in ctxt_g'
                    (*a later call's step 1 1/2 must not refute what P-auto proves here*)
                    val _ = if refuted_by_simp th'
                            then error "The judge is broken: its lemmas rewrite the guard to False."
                            else ()
                 in case p_auto ctxt_g' th' of
                      SOME solved =>
                        (write delta' Phi_Guard_Cache.Proved;
                         {verdict = Phi_Guard_Cache.Proved, refuter = NONE, judge = SOME "Provable",
                          result = Seq.single (ctxt1', solved)})
                    | NONE => error "The judge is broken: P-auto cannot prove the guard with the lemmas it proposed."
                end
            | Unprovable =>
                (keep Phi_Guard_Cache.Refuted;
                 {verdict = Phi_Guard_Cache.Refuted, refuter = NONE, judge = SOME "Unprovable", result = Seq.empty})

          (*no refuter refuted: the judge if installed, else Unknown; an entry already
            Unknown is not rewritten*)
          fun judge_or_give_up () =
            case ! judge of
              SOME j => consult j
            | NONE =>
                (if entry_verdict = SOME Phi_Guard_Cache.Unknown then () else keep Phi_Guard_Cache.Unknown;
                 {verdict = Phi_Guard_Cache.Unknown, refuter = NONE, judge = NONE, result = Seq.empty})

          (*steps 2 to 4*)
         in case p_auto ctxt_g th of
              SOME solved =>
                (if entry_verdict = SOME Phi_Guard_Cache.Proved orelse is_none entry then ()
                 else keep Phi_Guard_Cache.Proved;
                 {verdict = Phi_Guard_Cache.Proved, refuter = NONE, judge = NONE, result = Seq.single (ctxt1, solved)})
            | NONE =>
                (case entry_verdict of
                   SOME Phi_Guard_Cache.Refuted =>
                     {verdict = Phi_Guard_Cache.Refuted, refuter = NONE, judge = NONE, result = Seq.empty}
                 | SOME Phi_Guard_Cache.Unknown => judge_or_give_up ()
                 | _ =>
                     (*R-conv proves the negation of the conclusion, which for the check is
                       True: it is not run for the check
                       (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md, section 5 step 4)*)
                     let val r_conv_refutes =
                           case kind of Normal => r_conv can_inst ctxt_g ctxt0 goals
                                      | Check_Premise_Consistency => false
                      in if r_conv_refutes then refuted_by "R-conv"
                         else if r_nitpick kind ctxt goals then refuted_by "R-nitpick"
                         else judge_or_give_up ()
                     end)
        end

      val outcome = if by_simp then refuted_by simp_refuter else decide th1

      val {verdict, refuter, judge = judge_answer, result} = outcome
      (*a Proved entry changes the report only when the judge or the simplifier
        overturns it (the loud guard warning); every other ending reports as a call
        without an entry does: a refuter's refutation is silent, Unknown gets the
        undecided-guard warning (the undecided-check warning for the check)*)
      val _ =
        if entry_verdict = SOME Phi_Guard_Cache.Proved andalso judge_answer = SOME "Unprovable"
        then loud_guard_warning ctxt "the LLM judge" goals
        else if entry_verdict = SOME Phi_Guard_Cache.Proved andalso refuter = SOME simp_refuter
        then loud_guard_warning ctxt "the simplifier" goals
        else if verdict = Phi_Guard_Cache.Unknown then undecided_guard_warning kind ctxt goals
        else ()

      val elapsed = Time.toMilliseconds (#elapsed (Timing.result timer))
      val _ =
        if Config.get ctxt0 ML_Options.debugger
        then Event_Log.append guard_decision_category
               {verdict = string_of_verdict verdict,
                hit = (case entry_verdict of NONE => "none" | SOME v => string_of_verdict v),
                refuter = the_default "-" refuter, judge = the_default "-" judge_answer,
                kind = string_of_guard_kind kind,
                elapsed_ms = elapsed, digest = Hasher.hex d, n_goals = length goals}
        else ()
      val _ = Phi_Reasoner.warn_pretty (Context.Proof ctxt) 2 (fn () =>
                Pretty.str ("guard decision: " ^ string_of_verdict verdict ^
                            (case refuter of SOME name => " by " ^ name | NONE => "") ^
                            (case judge_answer of SOME answer => ", the judge: " ^ answer | NONE => "") ^
                            " in " ^ string_of_int elapsed ^ "ms, " ^
                            string_of_int (length goals) ^ " subgoal(s)" ^
                            (case kind of Normal => ""
                                        | Check_Premise_Consistency => ", " ^ string_of_guard_kind kind)))
   in result end


(*** The guard factory ***)

(*run the tactic once, under the bound (thread CPU) if given; keep only a solved state*)
fun try_prove_or_give_up bound tac ctxt th =
  let val seq = Seq.take 1 (solved_states (tac ctxt) th)
   in case bound of NONE => seq | SOME t => cpu_bounded_seq t seq end

(*The factory: the preprocessing template -- oblg_template, quick_cut, under head_only
  the configured pre-tactic, the case split of the leading subgoal, the digest step,
  the aux-fact insertion -- ending in the solving function `solve`, of the type of
  `prove_or_refute kind`, which receives the state unsimplified: the factory knows
  nothing of entries, deltas or simplification.  `digest_of` computes, on the state
  right after the case split and before the insertion (every visible premise is then a
  guard subgoal), what `solve` is given: the guard digest for the judge instance, ()
  for the others.  Every exit bypassing `solve` is paired with ctxt0, the context the
  factory was called on -- never with oblg_template's imported context, whose fresh
  frees would make the export hook drop the lemmas; only `solve` may replace the
  context.  guess_inst's looper and solver enter the guard machinery here and only
  here, through the guard-side context guard_ctxt -- prove_or_refute's ctxt, from
  which it derives its ctxt_g by applying the entry's delta (plan section 5 step 1)
  and on which every simplification and search of the call runs.*)
fun gen_guard_condition_solver digest_of solve {can_inst} (ctxt0, th0) =
  oblg_template true {can_inst = can_inst, fix_level = if can_inst then 1 else 2}
                {inj = pair ctxt0, on_thm = apsnd}
  (fn ctxt => fn th =>
      apply_tac snd ctxt (fn (ctxt, pre, aux) => fn th =>
        let val guard_ctxt = Guess_Instantiate.add_guess_inst_solver ctxt addsimps @{thms' Premise_def}
                             |> Guess_Instantiate.add_guess_inst_looper
         in quick_cut 1 th
         |> Seq.maps (head_only' (pair ctxt0) apsnd (fn th =>
              (pre THEN HEADGOAL (case_split_by_annotations_leading_subgoal ctxt)) th
              |> Seq.maps (fn th =>
                   let val d = digest_of ctxt th
                    in ALLGOALS (Method.insert_tac ctxt aux) th
                       |> Seq.maps (fn th => solve can_inst guard_ctxt d (ctxt0, th))
                   end)))
         |> Seq.take 1
        end) th
      |> Seq.take 1
      |> Seq.pull) ctxt0 th0

(*the guard digest: one hash of the whole goal state (the guard's subgoals and, under
  Goal.protect, the rest of the sequent with its conclusion) and of the context's
  assumptions; the aux facts, derivable, stay out.  For the check the digest marker
  False is prepended: the digest is computed AFTER the template's rewrite, where a check
  and an ordinary guard rewritten to \<condition> False look alike, and one entry for both
  would let the ordinary path's refutation by the simplifier overwrite the check's verdict*)
fun guard_digest kind ctxt th =
  Hasher.terms ((case kind of Normal => [] | Check_Premise_Consistency => [\<^prop>\<open>False\<close>]) @
                Thm.prop_of th :: map Thm.prop_of (Assumption.all_prems_of ctxt))

(*the kind of guard a goal state carries, read on the state the factory receives --
  BEFORE oblg_template's rewrite, which turns ordinary guards into \<condition> False too:
  the check iff the leading antecedent concludes False under a premise tag, Premise _ False,
  under its \<And>/\<Longrightarrow> prefix (the tag's mode is not read: only \<condition> guards reach the
  judge instance); a state without premise is Normal.  Not concl_is_false, which reads the
  bare False.*)
fun guard_kind_of th =
  case Thm.prems_of th of
    [] => Normal
  | prem :: _ =>
      (case Logic.strip_assums_concl prem of
         Const (\<^const_name>\<open>Trueprop\<close>, _) $
           (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ Const (\<^const_name>\<open>False\<close>, _)) =>
           Check_Premise_Consistency
       | _ => Normal)

fun guard_digest_of th0 = guard_digest (guard_kind_of th0)

(*the kind enters the digest and the decision in this one place, read off the state as
  written*)
fun guard_condition_judge cfg (ctxt0, th0) =
  gen_guard_condition_solver (guard_digest_of th0) (prove_or_refute (guard_kind_of th0)) cfg (ctxt0, th0)

(*the out-of-run instance: one whole attempt, no store*)
fun p_auto_solving _ ctxt _ (ctxt0, th) = p_auto_attempt ctxt th |> Seq.map (pair ctxt0)

fun guard_condition_solver cfg (ctxt0, th0) =
  gen_guard_condition_solver (K (K ())) p_auto_solving cfg (ctxt0, th0)

fun guard_condition_solver' cfg =
  context_tactic_to_state_transition (fn ctxt => fn th =>
    guard_condition_solver cfg (ctxt, th) |> Seq.map snd)

fun guard_condition_solver1 can_inst ctxt sequent =
  guard_condition_solver' can_inst (fn _ =>
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
