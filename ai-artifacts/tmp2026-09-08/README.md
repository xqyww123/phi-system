# Scratch files of the C emitter instance-naming work (2026-09-08)

These files may be deleted after 2026-09-15.

- `Scratch_Naming_{A,B,C,D}.thy`: the negative tests of Section 10.4 of
  `../CODEGEN_INSTANCE_NAMING_PLAN.md` (two exports of one instance; an export name shaped
  like a generated name; an export whose body reaches no routine).
- `Scratch_Export.thy`, `Scratch_Export.C`: an early export experiment.
- `Scratch_PtrIdx.thy` (+ proof store): the experiment on `ptr[-1]` indexing; result: bracket
  indexing on slice pointers is unsupported and negative machine-int literals do not synthesise.
- `CODEGEN_REVIEW_BRIEF.md`, `codegen_review.diff`: inputs of the adversarial reviews of the plan.
