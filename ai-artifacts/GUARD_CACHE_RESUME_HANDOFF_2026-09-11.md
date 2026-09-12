# Handoff: guard cache — steps P/0/1/2/3(first half)/4 DONE; step 5 next (updated 2026-09-12)

Supersedes `GUARD_CACHE_RESUME_HANDOFF_2026-09-09.md`.  Plan:
`contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` **rev 24** — §1 glossary
authoritative (the guard digest bullet carries the 2026-09-11 CORRECTION); §30–§32 step 2
and its two reviews; §33 the `Phi_Types.thy:2608` flip diagnosed and fixed, the tier
measurement SHELVED, the budget semantics ruled; §34 step 3 first half (the export hook
end to end) with its correction; **§35 step 4 (the persistent store) done and reviewed,
one AUTHOR_DECISION open**.  Read §33–§35 before touching anything.

## Committed (NOT pushed — push only when told, only to origin)
2026-09-09: Performant_Isabelle_ML `4e850dd`, Isabelle_RPC `65cdbaa`, Isa-Mini `1ce791f`,
auto_sledgehammer `1360b21`, phi-system `d19e4521` + `1d376c80`, root `bf4fd202`.
2026-09-11: phi-system `b83790d5` (step 2 + the 2608 fix), `da0fd908`, `602e2a41` (the
digest = whole goal state + assumptions), `9c2a29e6`, `377dc749` (step 3 first half);
root bumps up to `8c0796bd`.  2026-09-12: phi-system `9dd703c1` (§34 correction), root
`53002977`; auto_sledgehammer: the functor commit (step 4); phi-system: the step 4 commit;
root bump — see `git log` for the last three.

## The code, as it stands
- `auto_sledgehammer/library/cache_file.ML`: `functor Proof_Store (Kind : STORE_KIND) :
  PHI_PROOF_STORE`; `Phi_Proof_Store` instantiated at the file's end; `compact_store` does
  nothing for a missing file; `openning_stores : (store * written)`.  Compiled INTO the
  `Phi_System_Base` heap from source (the heap holds phi-system's external deps): an edit
  needs `isabelle build -b -d /home/qiyuan/Current/MLML Phi_System_Base` (author's approval
  each time; ~45 s) and an Isabelle-MCP relaunch (`isabelle_terminate`, `isabelle_launch
  Phi_System_Base`).  The Auto_Sledgehammer/Minilang heaps are NOT rebuilt by that; Isabelle
  invalidates them itself when someone builds them.
- `phi-system/Phi_Logic_Programming_Reasoner/library/guard_cache.ML`: `PHI_GUARD_STORE`,
  `Phi_Guard_Store` (`<thy>.guard-cache` beside the theory, gitignored), the entry codec
  (`encode_entry`/`decode_entry`), `lookup_entry`/`write_entry`; the lemma list, budget,
  export hook as before.  `reasoners.ML`: `prove_or_refute`, the factory
  `gen_guard_condition_solver` with `simpcut_tac` local under 5 s of thread CPU (warns
  "The system simplifier probably loops on:"), `guard_digest ctxt th` over the whole state
  plus `Assumption.all_prems_of ctxt`.
- Tests (none in a ROOT; evaluate on demand on Phi_System_Base): `Test/Guard_Decision_Smoke.thy`
  (every prove_or_refute path; `fresh` = wall-clock run tag + serial), `Test/Guard_Export_Smoke.thy`
  (the export hook: same run, `;` boundary, nested block), `ai-artifacts/Guard_False_Probe.thy`.

## OPEN WITH THE AUTHOR
- §35: `val store_path` in `PHI_GUARD_STORE` has no caller; §8 says two entry points, no
  new ones.  (a) drop it [recommended] or (b) expose it via `PHI_GUARD_CACHE` so the battery
  deletes its own store file at entry.
- §33: item 4 (closed by the digest ruling); the tier measurement (shelved; the drafter's
  plan when resumed: stages A and B of `ai-artifacts/TIER_MEASUREMENT_BRAINSTORM_2026-09-11.md`,
  not C without the author); phase-2 design points: a budgeted lemma is a CONDITIONAL rule
  (tried after unconditional rules, refused past `simp_depth_limit`), `Frequent` = the
  ceiling, whether a judge lemma may cite the context's assumptions; the `is_F` shortcut
  left to the follow-up constant `\<check> \<hypothesis> \<consistency>`.

## NEXT: STEP 5 (plan §10 step 5) — corpus acceptance via Isa-REPL
A cache-on and a cache-off leg (`\<phi>guard_cache`), a concurrent Isa-REPL leg, a
consecutive-run leg with a hit-rate floor; measure wall time, verdict flips per guard
cache-on vs cache-off, first-decision latency, the path distribution (hit kinds, refuters,
judge), lemma replay cost, budget cut-offs, hard failures attributable to guard-side
exceptions, digest cost, store I/O, the forked-proof write, the export hook's cost per run
boundary; re-measure the 400 ms bound.  Isa-REPL against Phi_System_Base sources; the AoA
gate is CLOSED under Isa-REPL (no interactive frontend) — no test-driver declare needed
there; under Isabelle-MCP it is open and the TEMPORARY `declare [[\<phi>log_guard_decision =
true, AoA_driver = "test", AoA_write_proof_store = false]]` after the `\<phi>guard_P_auto`
method_setup in PLPR.thy keeps a failing statement off the LLM (the author calls the
escalation expected behaviour; the declare is the drafter's practice for deterministic
verification runs; revert before commit).  Baselines: warm corpus = 355 decisions, 146
Refuted + 5 Unknown hits, ~21 s of guard time; cold = ~122 s.  After the plan: move the
term-codec functor to Performant_Isabelle_ML.

## Working notes
- Under Isabelle-MCP, editing PLPR.thy makes the MCP re-evaluate every open downstream
  theory automatically; after reverting the declare, cancel that re-evaluation
  (`isabelle_cancel_evaluation`) unless it is wanted.
- The harness kills background `sleep` timers "for low memory" spuriously — poll anyway.
- Decision statistics: `~/.isabelle/Isabelle2025-2/event_log/guard_decision/<ts>-<pid>.xml`;
  parse `<record …>` attributes (verdict/hit/refuter/judge/elapsed_ms/digest/subgoals).
- A theory importing `PhiSem_Machine_Integer` beside `PhiSem_Int_ArbiPrec` cannot open an
  `if` branch on a `\<val> \<nat>` (pre-existing; `toplevel0.ML:267`'s `@{print}` stays by
  the author's word).

## Rules (the author's, all binding)
Edit source with the Edit tool; plan docs by hand; never coin words (fixed terms:
entry/store/the lemma list/the lemma budget/ctxt_g/ctxt1/guard_ctxt/the canonical form/
"G.simpcut"/the undecided-guard warning/the loud guard warning/the dropped-lemma warning);
explain in Chinese, essence first, full context, exact file:line; `isabelle build` only
with approval; after `.ML` edits re-evaluate, never rebuild heaps for that (except
cache_file.ML, above); never git stash/checkout/reset/clean; commit on the repo's current
branch, push origin only, only when told; memory writes need approval; probes must not
load phi-system theories under NEW names; do not relay agent progress ticks; monitor long
runs at most every 10 minutes; review shape: workflow, Opus, English, interrogators →
fresh defenders → judge; the drafter re-verifies every upheld finding; no code change
before the author agrees on anything classified AUTHOR_DECISION; when narrowing a
definition beyond the author's words, quote the author verbatim, mark the narrowing
[drafter] and ask — never file it under an author citation.
