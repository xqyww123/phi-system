- Fix the debt axiom `can_eqcmp_ptr`, 
- I also remember there are some problems in the scalar warping rule. It turns out that, a mechanism is required in the TP reasoning subsystem to know if the reasoning at least applies some meaningful transformation or just fallback only.
- Introduce native $\exists$ into TP.
- Nondeterministic degenerate derivation branch in `\<phi>type_def` (observed 2026-08-10,
  `Phi_System/Phi_Types.thy:2529`, `\<phi>Mul_Quant_LenIv deriving ... Semimodule_NonAssoc`):
  the `Transformation_Functor\<^sub>\<Lambda>` derivation SOMETIMES emits a residual proof
  obligation that is unprovable as stated — the pointwise mapper hypothesis appears as a
  CONJUNCT of the conclusion instead of an assumption, and the third quantified variable
  has type `nat => 'c` where the mapper side has `'c list`; the goal is then refutable by
  instantiating the relation with the constant-false predicate. Healthy runs (jEdit, most
  batch builds) never emit this obligation (its store key
  `local.\<phi>Mul_Quant_LenIv/Transformation_Functor/0` has never had a record); which
  branch fires is nondeterministic (reasoner search order / timing — two consecutive
  PIDE evaluations on a fresh prover both hit it while jEdit did not). With the AoA-backed
  obligation solver the agent correctly refutes the degenerate goal and the whole command
  dies on a hard error, where the old engine would merely fail. Full obligation text and
  probe evidence: PHI_VC_SOLVER_PLAN_V2.md stage-5 record (probe 2026-08-10). Two things
  to decide: fix the derivation branch, and whether refute-class give-ups in the
  obligation slot should fail softly (empty Seq, allowing reasoner backtracking) instead
  of raising a hard error.
  WHAT THE TRACES SHOW, 2026-08-10, from diffing a successful against a failing
  `\<phi>trace_reasoning = 3` trace of the same command (690 vs 719 lines, both captured under
  isabelle-mcp): the two traces are byte-identical for their first 691 lines except that
  the two `Sledgehammering on the ...th goal` lines float by one position relative to the
  `Instantiate reasoning template` / `Installing \<phi>-LPR reasoner` stream. That float is NOT
  evidence of anything: obligation solving is asynchronous by design (`\<phi>async_proof`
  defaults to true, Phi_Envir.ML:222 -> hammer_obligation_solver -> async_prove', which
  forks a worker and hands the main thread a `Thm.future` promise), so the two message
  streams come from different threads and their interleaving in the log is meaningless.
  What IS meaningful: every `Instantiate template X` -> `Installing the rule from X` pair
  keeps identical order in both runs, i.e. the command's MAIN THREAD did byte-identical
  work in the healthy and the degenerate run. An earlier entry here blamed a race between
  rule installation and obligation solving; that claim is RETRACTED -- the evidence
  contradicts it. The only substantive difference is that the degenerate run makes one
  extra obligation call (the AoA refutation), emitted after the main thread's last
  message; because obligations are discharged asynchronously, that position says nothing
  about when the obligation was created. Both runs: 2 sledgehammer invocations, 1 proof
  store miss, 3 guard-condition `falisfy` warnings, no `[async_prove] running
  synchronously instead` fallback. Next probe: rerun with `\<phi>async_proof = false` -- if the
  outcome becomes deterministic, the nondeterminism lives in the async obligation
  machinery rather than in the derivation itself.
  Two hypotheses REFUTED by evidence: (a) the guard-condition wall-clock budgets
  in `prove_or_rebute` are not the cause — its "Fail to prove or falisfy ... We assume the
  conditions do not hold" warning fires exactly three times in BOTH the healthy and the
  degenerate run, and raising the budgets from 30/30/250/100 ms to 100/100/300/200 ms
  changed nothing; (b) machine load is not the cause either — the degenerate branch also
  occurs on an idle machine. (The warnings are invisible by default because
  `Phi_Types.thy:2527` declares `\<phi>trace_reasoning = 0`.)
  The lemma right after it, `\<phi>Mul_Quant_LenIv_wrap_module_src` (Phi_Types.thy:2581-2594),
  then fails with a bare `exception Option` (i.e. some `the NONE`) at the block
  bracket — seen on both the old and the new budgets, so it predates this experiment and
  is a separate blocker.
  UPDATE 2026-08-24 (guard race landed, GUARD_NITPICK_FALSIFY_PLAN.md): the names above
  are stale — `prove_or_rebute` is now `prove_or_refute`, its typo'd "falisfy" warning now
  reads "falsify", and the serial 30/30/250/100 ms budget cascade it refers to has been
  replaced by a prove/refute race (30ms front + one per-racer budget,
  `\<phi>guard_race_timeout`), so the budget experiments recorded here are not reproducible
  on current sources.