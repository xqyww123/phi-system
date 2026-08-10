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