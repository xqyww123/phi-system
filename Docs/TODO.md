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
  ROOT CAUSE, established 2026-08-10 by diffing a successful against a failing
  `\<phi>trace_reasoning = 3` trace of the same command (690 vs 719 lines, both captured under
  isabelle-mcp): the two traces are byte-identical except that the `Sledgehammering on the
  1th goal` lines sit at DIFFERENT positions relative to the stream of `Instantiate
  reasoning template` / `Installing \<phi>-LPR reasoner` events. In the healthy run the reasoner
  instantiated from template `\<phi>Mul_Quant_LenIv.\<A>backward_simp` is installed BEFORE the
  engine attacks the obligation; in the degenerate run the engine goes first and the rule
  is installed after. So `deriving` installs reasoning rules incrementally WHILE
  obligations are being solved in parallel, and whether a rule is available at the moment
  an obligation is attacked is a race: lose it and the reasoning falls back to another
  rule, leaving the residual obligation that has lost its `len_intvl.len iv = 0`
  hypothesis. Fix directions (author's call): serialise rule installation against
  obligation solving, or defer obligation solving until the derivation phase has finished
  installing, or make the fallback branch fail explicitly instead of silently emitting a
  residual obligation.
  Two hypotheses REFUTED by the same evidence: (a) the guard-condition wall-clock budgets
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