# Handoff: guard cache — steps P, 0, 1 ACCEPTED and committed; step 2 DONE, first review's fixes applied, re-review in flight (2026-09-09, night)

Supersedes the evening handoff.  Plan: `contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md`
**rev 24** — §1 glossary authoritative (the judge, "G.simpcut", P-auto, the undecided-guard
warning were corrected on 2026-09-09); §3; §5 (steps 2, 6 corrected); §6; §10 (thread CPU,
the record without a lemma count); §30 step 2 as done; **§31 the first code review's rulings
and fixes**; §32 will record the re-review.  Rev 23 archived as `.rev23.md`.

## Committed (2026-09-09 14:xx; NOT pushed — push only when told, only to origin)
Performant_Isabelle_ML `4e850dd`, Isabelle_RPC `65cdbaa`, Isa-Mini `1ce791f`,
auto_sledgehammer `1360b21`, phi-system `d19e4521` + `1d376c80`, root MLML `bf4fd202`.

## The author's rulings of 2026-09-09 (all applied; see plan §31)
- The 400 ms classic bound is THREAD CPU on every guard-side consumer (`Thread_CPU.apply`,
  no wall limit, an error without a CPU clock); R-nitpick keeps wall clock.  Code:
  `cpu_bounded`, `cpu_bounded_seq`, `cpu_bounded_tac` in reasoners.ML.
- spec-3 (a): a call from a `Proved` entry prints the loud guard warning only; the two
  warnings are decided at one site, mutually exclusive.
- The judge's `Provable` replaces THIS ENTRY's lemmas only; the judge's ctxt is the
  guard-side ctxt WITHOUT this entry's lemmas (earlier guards' lemmas in it); a
  re-proposed statement takes the judge's budget (`update_lemma`; step 1's append keeps
  the first budget — the drafter's assumption, stated to the author).  `replace_lemmas`
  deleted.  (The drafter had misread 08:34's "已有的 lemmas" as the whole list.)
- `guard_decision`'s `lemmas` field deleted.  The 35 ms gate's removal was deliberate.
- The AoA incident (§30.9) is shelved ("先别管").  The two small proposals (rename the test
  file; the deleted probe categories) got no answer yet.

## Uncommitted (phi-system only, no heap rebuilt)
reasoners.ML (the "Guard decision" section: `cpu_bounded*`, `r_conv`, `r_nitpick` with the
net `refute_timeout + n × 5 s`, the judge ref, `guard_decision_category` without lemmas,
the warnings, `replay_lemma`, `prove_or_refute` with `add_lemmas add replayed`, `consult`
on `ctxt`/`ctxt0` with `update_lemma`, `judge_or_give_up`, the one warning site; the
factory's local `guard_ctxt`; comments); guard_cache.ML (`lookup_entry`/`write_entry`,
`add_lemma_with` → `add_lemma`/`update_lemma`); guard_refute.ML (comments);
Phi_System/library/system/processor.ML (one comment); PLPR.thy (`cpu_bounded_tac` in
`\<phi>guard_P_auto`; the `declare` is `[[\<phi>log_guess_inst = true]]` only — the
TEMPORARY diagnostic declare is reverted); Test/Guard_Race_Smoke.thy (rewritten: `decide`
with the `contract` wrapper on every test judge, projection `(verdict, hit, refuter,
judge)`, the new probes of §31 item 7); the plan (rev 24, §30, §31); this handoff.

## Evidence (Isabelle-MCP on Phi_System_Base, final code)
PLPR.thy clean, no new ML warning; the battery clean; the screen control of §31 item 7
done (screen disabled → the probe goes red; restored); `PhiTest_Arithmetic.thy` clean on
a cold table (366 decisions, 102.5 s of guard time; §31).  Corpus loads under MCP MUST
use the temporary declare `[[\<phi>log_guard_decision = true, AoA_driver = "test",
AoA_write_proof_store = false]]` in PLPR.thy after the `\<phi>log_guess_inst` declare, and
revert it before committing (the AoA gate is open under MCP).

## The re-review `wf_59c9d545-ddb` — DONE, its eight fixes applied and verified (plan §32)
NOT ACCEPTED "but only just": nothing behavioural; the eight drafter fixes (the
replacement probe's entry lemma `useless_other`; `timed_seq`/`timed_tac` deleted; the
pair-valued `add_lemmas`; the net comment; "knife"; plan §4; contract labels; the
`run_guard` seam) are in and verified (PLPR clean, battery clean, corpus clean).  The
author's answers of 2026-09-10: `timed1_tac` deleted; the battery is now
`Test/Guard_Decision_Smoke.thy`; the probe categories stay deleted and `guard_refute.ML`'s
`refuter_probe` scaffolding went with them (§32).  Open: whether `\<phi>log_guess_inst =
true` in PLPR.thy (another subsystem's instrumentation) should go too.  Next: verify, then
commit on phi-system's current branch (master), no push.

## Next after acceptance: STEP 3 (plan §10 step 3) — the export hook end to end, the
budget measured on the corpus with test-injected lemmas per tier; then step 4
(persistence; needs the author's approval to rebuild Phi_System_Base).

## Rules (the author's, all binding)
Edit source with the Edit tool; plan docs by hand; never coin words (fixed terms:
entry/store/the lemma list/the lemma budget/ctxt_g/ctxt1/guard_ctxt/the canonical form/
"G.simpcut"/the undecided-guard warning/the loud guard warning/the dropped-lemma warning);
explain in Chinese, essence first, full context, exact file:line; `isabelle build` only
with approval; after `.ML` edits re-evaluate, never rebuild heaps for that; never git
stash/checkout/reset/clean; commit on the repo's current branch, push origin only, only
when told; memory writes need approval; probes must not load phi-system theories under
NEW names; do not relay agent progress ticks; monitor long runs at most every 10 minutes.
