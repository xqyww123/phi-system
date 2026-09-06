# Handoff (2026-09-05, before compaction): stateful PLPR reasoning — plan converged, implementation not started

## State
- Plan: `contrib/phi-system/ai-artifacts/STATEFUL_PLPR_REASONING_PLAN.md`, rev 11, review converged
  (eight adversarial rounds; the eighth ruled READY_WITH_EDITS, its one wording fix is in).
  Every author ruling is in §10 (10.1–10.38) with transcript timestamps; §9.10 lists rejected review
  opinions (never re-raise); §9.12–§9.14 are decided drafter choices.
- No code has been written.  The author has NOT yet said "开始"; the last message asked for the go-ahead
  for §8 step 1.  Wait for it.
- Verdict JSONs of rounds 3–8 were in the session scratchpad (`rev4-…rev9-verdict.json`); the scratchpad has
  been wiped once before, treat them as gone.  The plan is the only authoritative artifact.

## Process rules (the author's, unchanged)
- The author's process: I identify what genuinely needs the author's decision and ask; everything else goes to
  adversarial review.  There is NO "section-by-section approval" step (I invented that once; the author
  corrected me).  Do not attribute process to the author that the author did not state.
- Every design/behaviour decision needs the author's explicit ruling, recorded as
  [author YYYY-MM-DDTHH:MM "quote"] (timestamps from the transcript jsonl, UTC; grep the user message).
- Explain in Chinese; "essence first, then from zero, full context"; never coin words; no ad-hoc labels;
  do not assume the author remembers earlier framing.
- Plan/design documents: edit ONLY with the Edit tool (never sed/python).  Reading via Bash is fine.
- Reviews: Workflow, 5 interrogators → 5 fresh defenders → 1 judge, Opus 5, English.  Since the sixth round
  the author ordered hair-splitting to be rebutted HARSHLY (defender + judge prompts carry the standard: a
  defect = wrong code / silent behaviour change / missed live site / contradictory instructions; everything
  else rejected).  Reuse that prompt shape for any further review.
- Never run `isabelle build` (author builds; V1–V3 in §7).  After editing any .ML the author's build is the check.
- Commit directly on `main`, one commit per §8 step, message ends with the Co-Authored-By/Claude-Session trailer.
- Never git stash/checkout/reset --hard/clean.  Shared working tree.
- Memory writes need explicit approval.  Subagents default to Opus 5.

## Implementation kick-off (§8, once the author says 开始)
Step 1 (one commit; must build unchanged with no hook registered = V1):
- New `Phi_Logic_Programming_Reasoner/library/context_export.ML`, `ML_file` line before `library/reasoner.ML`
  at `PLPR.thy:542`: structure `PLPR_Context_Export` = `Hooks` (the existing Hooks functor, arg = inner ctxt,
  state = outer ctxt), `export_context` (pointer_eq short cut, `Hooks.invoke (Context.Proof outer) inner outer`),
  `export_state`, `exception UNEXPORTABLE of thm`, `export_aux_lemma` (§4.1).
- `reason` / `reason1` return `context_state`; `reason_tac` exports onto `fst stat`; `best_among` returns
  `context_state option`; exhaustive success handler uses `snd (export_state …)`.
- Delete `reason_sXXX`, `internal_reason_s` (reasoner.ML:124-133, :960-969), `SYS/tools/elimination_rule.ML`,
  `SYS/phi_type_algebra/SE_Trim_Empty.ML`, `deriver_framework.ML:2075-2082 pure_PLPR_reasoner`.
- Same commit: EVERY caller of reason/reason1/best_among re-shaped to pass `(ctxt, thm)`; discarding sites
  drop where the option is consumed (§5.4 shapes); inheriting sites provisionally drop too.
- Then steps 2–6 per §8 (Phi_Apply; synthesis/get_value; cast family; PLPR_Simplifier; local sites +
  `\<phi>reason` method + `end_tac` §10.30 + `block_export` at the seven frames §6.4 + the `toplevel0.ML:234`
  mechanism §9.12/§9.13).  §12.3 is the silent-drop checklist to walk after step 6.
- Anchors are as of 2026-09-04/05; §8 step 0 = re-verify anchors of §2, §5, §6, §10, §12 before editing.
