# Handoff: guard cache — step 2 DONE and reviewed twice; the 2608 flip diagnosed and fixed; close-out in progress (2026-09-11)

Supersedes `GUARD_CACHE_RESUME_HANDOFF_2026-09-09.md`.  Plan:
`contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` **rev 24** — §1 glossary
authoritative; §30 step 2 as done; §31 the first code review's rulings/fixes; §32 the
re-review's fixes, the author's rulings of 09-10/09-11, the CPU measurement; **§33 the
`Phi_Types.thy:2608` flip diagnosed (2026-09-11) and the rulings that fixed it**.  Read
§31–§33 before touching anything.

## Committed (2026-09-09; NOT pushed — push only when told, only to origin)
Performant_Isabelle_ML `4e850dd`, Isabelle_RPC `65cdbaa`, Isa-Mini `1ce791f`,
auto_sledgehammer `1360b21`, phi-system `d19e4521` + `1d376c80`, root MLML `bf4fd202`.

## Uncommitted — the whole of step 2 plus the 09-11 work (phi-system only, no heap rebuilt)
`git status` in contrib/phi-system: Docs/GUARD_CACHE_QUICK_MODE_PLAN.md (+ .rev23.md),
Phi_Logic_Programming_Reasoner/{PLPR.thy, library/reasoners.ML, library/guard_cache.ML,
library/guard_refute.ML, library/guess_instantiate.ML (one comment)}, Test/Guard_Race_Smoke.thy
→ Test/Guard_Decision_Smoke.thy (git mv, staged), Phi_System/library/system/processor.ML
(one comment), ai-artifacts/ handoffs + `ai-artifacts/Guard_False_Probe.thy` (the
`\<condition> False` probe of §33 item 3; keep, it is evidence).
Final code shape: reasoners.ML "Guard decision" section — `cpu_bounded`/`cpu_bounded_seq`/
`cpu_bounded_tac` (thread CPU; the wall-clock `timed_*` family deleted), `r_conv` (thread
CPU), `r_nitpick` (wall clock; net `refute_timeout + n × 5 s`), the judge ref, the
`guard_decision` record (verdict/hit/refuter/judge/elapsed_ms/digest/subgoals), the two
warnings decided at one site, `replay_lemma`, `prove_or_refute` with the pair-valued
`add_lemmas` over `(ctxt0, ctxt)`, `consult` on `ctxt` (no lemma of this entry) with
`update_lemma`; the factory is now **`gen_guard_condition_solver`** (renamed 09-11;
the instances `guard_condition_solver'`/`guard_condition_solver1` keep their names) with
**`simpcut_tac` as a local function under 5 s of thread CPU, fixed in the code**, warning
`The system simplifier probably loops on:` on its timeout and then yielding the state
unchanged; the factory's local `guard_ctxt`.  guard_cache.ML: `lookup_entry`/
`write_entry` (in-memory `Symtab`, step 4 swaps the store in), `add_lemma_with` →
`add_lemma`/`update_lemma`.  guard_refute.ML: the `refuter_probe` scaffolding deleted;
`nitpick` = preprocessing + one Nitpick call.  PLPR.thy: `cpu_bounded_tac` in
`\<phi>guard_P_auto`; `hide_const`; the `declare` block.

## What 09-11 found (details in §33)
The 2608 flip was the "G.simpcut" pass's 400 ms bound: those `len_intvl` guards need
371–437 ms of thread CPU in that pass (measured, low load), the timeout was silent and
P-auto then failed on the unsimplified goal.  Not load, not a digest collision.  Side
findings: the `is_F` shortcut's 250 ms `auto_search_tac` never sees a goal (the pass
closes or cuts every `\<condition> False` guard first) — the idiom is simp-only, since
2024; the loud guard warning fires by design on the shared entry `3d7696d10790e4a8`.

## CLOSE-OUT STEPS REMAINING (do in this order)
1. `PhiTest_Arithmetic.thy` is being evaluated under Isabelle-MCP (Phi_System_Base) with
   the TEMPORARY declare in PLPR.thy (`\<phi>log_guard_decision = true, AoA_driver = "test",
   AoA_write_proof_store = false`, after the `\<phi>log_guess_inst` declare) and the 5 s
   bound.  Check `isabelle_evaluation_status`; expect clean, no "probably loops" warning
   (grep the decision log's process file for none; the warning is a PIDE warning, check
   `isabelle_command_output` at `Phi_Types.thy:2608` and `:2732`).
2. REVERT the TEMPORARY declare (the four-line block with its comment) so the `declare`
   reads `[[\<phi>log_guess_inst = true]]` only; re-evaluate PLPR.thy (clean).
3. Commit in contrib/phi-system on its current branch (master): message naming step 2,
   the two reviews, the rulings, the 2608 diagnosis and fix (§33), the rename; then the
   root MLML commit bumping the submodule pointer (`git add -f contrib/phi-system` from
   the MLML root).  NO push.  Sweep in others' uncommitted tracked edits if any, naming
   them in the message.  Untracked build products in the tree (`Phi_Examples/*.C`,
   `*.o`, `PhiTest_Arithmetic.o`, `Phi_Semantics/PhiSem_Real_Abst.proof-store`) are not
   ours: leave them.
4. Open with the author: `\<phi>log_guess_inst = true` in PLPR.thy (another subsystem's
   instrumentation) — keep or delete (asked 09-10, unanswered); the `is_F` shortcut
   (§33 pending); §33 item 4 (the loud warning on a shared entry); whether to rename
   `guard_condition_solver` → `gen_guard_condition_solver` throughout the plan text or
   leave §33 item 5's note as the pointer.

## Then: STEP 3 (plan §10 step 3)
The export hook end to end — a lemma enabled at one call reaching the next call of the
run and the next statement of the block (model: the V2 smoke test of
`ai-artifacts/STATEFUL_PLPR_REASONING_PLAN.md`); the budget tiers measured on the corpus
with test-injected lemmas per tier on the budget's own unit (one consumer run).  Then step
4 (persistence: `cache_file.ML` store functor, `Phi_Guard_Store`, the entry codec over
`RPC_Pretty_Bytes`, gitignore; needs the author's approval to rebuild Phi_System_Base),
step 5 (corpus acceptance via Isa-REPL with the AoA gate closed).  After the plan: move
the term-codec functor to Performant_Isabelle_ML; the author's follow-up of §33: a new
antecedent constant `\<check> \<hypothesis> \<consistency>` (= `False`) with dedicated
reasoners for it and for `\<condition> False`, above the condition solver in priority.

## Working notes
- Corpus loads under Isabelle-MCP MUST use the `AoA_driver = "test"` declare (the AoA
  gate is open under an interactive frontend; the 09-09 incident cost agent time).
- The in-memory table lives in guard_cache.ML: a reload of that file empties it; a
  reload of reasoners.ML alone keeps it (warm-table runs show ~145 `Refuted` hits, cold
  ~75 first refutations by R-nitpick at ~1.4 s each).
- A reload of reasoners.ML re-evaluates the whole corpus in parallel (load 5–9); the
  harness kills background `sleep` timers "for low memory" spuriously — poll anyway.
- The battery's guards carry `fresh ()` numerals because the table has no deletion.
- Decision statistics: `~/.isabelle/Isabelle2025-2/event_log/guard_decision/`; the
  session scratchpad's scripts (`simpcut_probe.py`, `lowload.py`, `compare_decisions.py`)
  may be gone after compaction — trivial to rewrite (parse `<record …>` attributes).
- A thread's CPU for the same work varies ±30 % between runs (SMT contention): a bound
  needs that margin over the measured maximum.

## Rules (the author's, all binding)
Edit source with the Edit tool; plan docs by hand; never coin words (fixed terms:
entry/store/the lemma list/the lemma budget/ctxt_g/ctxt1/guard_ctxt/the canonical form/
"G.simpcut"/the undecided-guard warning/the loud guard warning/the dropped-lemma warning);
explain in Chinese, essence first, full context, exact file:line; `isabelle build` only
with approval; after `.ML` edits re-evaluate, never rebuild heaps for that; never git
stash/checkout/reset/clean; commit on the repo's current branch, push origin only, only
when told; memory writes need approval; probes must not load phi-system theories under
NEW names; do not relay agent progress ticks; monitor long runs at most every 10 minutes;
review shape: workflow, Opus, English, interrogators → more fresh defenders → judge; the
drafter re-verifies every upheld finding; no code change before the author agrees on
anything classified AUTHOR_DECISION.
