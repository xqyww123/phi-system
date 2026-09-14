# STEP 5 — corpus acceptance via Isa-REPL (2026-09-14)

Plan: `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` §10 step 5, §37 item 12.  Harness:
`run_leg.py` (one fresh Isa-REPL server per leg on the `Phi_System_Base` heap,
`load_theory` of the corpus from source, wall clock by the harness, the
`guard_decision` records into the leg's own `event_log` directory) and
`analyze.py`.  The corpus: `Phi_Test.PhiTest_Arithmetic` and its imports (the
355-decision corpus of §26/§30/§35/§36).  Threads 8 per server (6 each on the
concurrent leg); 14 cores.  Each leg's configuration is a TEMPORARY `declare`
in `PLPR.thy` (reverted before the commit).

**The AoA gate is NOT closed under Isa-REPL** — a finding of this step, against
the plan's assumption (§10 step 5 "AoA gate closed there").  The gate
(`agent_server.ML:560-562`) opens on the second component of
`Dialogue.frontend_identity ()`, and under the REPL server that component is
`SOME true`: the Phi_Examples leg tried to reach the Codex API three times
(`Bucket_Hash.thy:20`, `:99`, `Matrix_Oprs.thy:140`) and was stopped only by
the local proxy being down ("local openai-oauth proxy unreachable at
http://127.0.0.1:8317/v1/") — no money was spent, by luck, not by the gate.
The `PhiTest_Arithmetic` corpus never reaches the gate (every obligation is
in its store).  A future harness must set `AoA_driver = "test"` (the test
driver, which the gate admits and which never calls a model) or
`AoA_ALLOW_NONINTERACTIVE` must stay unset AND the frontend probe must answer
NONE under Isa-REPL — which of the two is the author's call.

The `guard_decision` record is written under `ML_debugger` (§37 item 1), so the
legs that count decisions run with `declare [[ML_debugger]]`, which instruments
every ML file compiled from source after `PLPR.thy` — the "dbg" legs are slower
than a plain load by that instrumentation; the plain legs measure wall time only.

## Legs

| leg | cache | ML_debugger | wall | decisions / digests | guard time | result |
|---|---|---|---|---|---|---|
| C1_on_dbg | on | on | 319.8 s (first load of the day: heap pages cold) | 355 / 261 | 24.5 s | clean |
| C2_on_dbg | on | on | 213.2 s | 355 / 261 | 21.7 s | clean |
| E_off_dbg | off | on | 412.1 s | 355 / 261 | 161.4 s | clean |
| B_off | off | off | 415.5 s | (no records) | — | clean |
| A_on | on | off | 182.0 s (aborted) | — | — | `exception Option` at `Phi_Types.thy:2591` |
| A2_on | on | off | 243.2 s (aborted) | — | — | `exception Option` at `Phi_Types.thy:2594` |
| F1_conc, F2_conc (two servers at once, 6 threads each) | on | on | 365.4 s, 379.2 s | 355 / 261 each | 26.8 s, 24.0 s | clean, clean |
| G_examples (the eight Phi_Examples theories) | on | on | 1059.1 s | 1756 / 1646 | 269.0 s | 4 obligation errors, see below |

## The concurrent leg (F1 ‖ F2): 0 flips, 100 % hits, no collision warning — MET

Two Isa-REPL servers loaded the corpus at the same time, sharing the tracked
`.proof-store` files.  Each saw 355 decisions over 261 digests with the
verdict distribution of the sequential runs; 261 digests in common between
the two and with C2, 0 flips in every pairing; 151 of 151 non-proved decisions
hits on both.  Neither server printed the collision marks' warning
(`ML_debugger` was on, so the marks were live).  Wall 365 s and 379 s against
213 s alone: the two servers shared the 14 cores.

## The Phi_Examples leg (G): the guard cache clean; the obligations of two theories fail for reasons outside it

`Phi_Examples.{Dynamic_Array, Linked_List, Quicksort, Rational_Arith,
Binary_Trees, Matrix_Oprs, Binary_Search, Bucket_Hash}` loaded in one server
(`PhiEx_All.thy` itself was NOT loaded: its `run_semantic_interpretation`
calls a language model).  1756 decisions over 1646 digests: 1048 proved, 585
refuted (582 hits, 3 first decisions by R-nitpick), 123 unknown (121 hits);
guard time 269 s of the 1059 s wall; 703 of 708 non-proved decisions hits.
Timings under the 8-thread load: proved median 0 ms, p99 220 ms; refuted
median 312 ms, p99 1290 ms, max 4961 ms; unknown p99 5504 ms, max 8652 ms —
these are wall milliseconds of the whole call, and an `Unknown` hit runs
P-auto to its 400 ms of thread CPU, then the "G.simpcut" pass had run before
under its 5 s bound; under contention wall exceeds CPU.  No `guard_decision`
anomaly, no guard-side exception.

The load ended with errors that are not the guard cache's: three obligations
whose proof is not in the store escalated to AoA and failed on the unreachable
proxy (above), and one obligation of `Quicksort.thy:49` failed in
sledgehammer (`Par_Exn` at `hammer sledgehammer`, the exception record) —
"Fail to solve the proof obligation automatically".  Whether these four
obligations have proofs in the tracked stores on the author's machine, or
were always AoA-solved, is not something this leg can tell; they fail the same
way without the guard cache.

The leg wrote guard entries into the eight theories' tracked `.proof-store`
files and regenerated the theories' exported C files (`*.C`, untracked).  Those
stores were ALREADY modified in the working tree before this step (other
work, uncommitted); this step's commit leaves every store and every generated
file uncommitted — the author decides what to add.

## The consecutive-run leg (C1 → C2): floor 100 % hits, 0 flips — MET

261 digests in C1, 261 in C2, all 261 in common, 0 only in C2; verdict sets equal
on every digest (0 flips).  Of C2's 151 non-proved decisions, 151 are hits
(100 %): 146 `Refuted` hits, 5 `Unknown` hits.  The 204 proved decisions are
first decisions in both runs by design (a first-decision proof writes no entry,
§5 step 3).

## Cache on vs cache off (C2 vs E, both instrumented): 0 flips

Every digest of the cache-off run gets the same verdict from the cache-on run
(261 common, 0 flips).  Path distribution, cache off: 204 proved in P-auto,
146 refuted (142 R-nitpick, 4 R-conv), 5 unknown, no judge installed.  Guard
time 161.4 s off vs 21.7 s on; the refuted decisions cost a median of 1006 ms
(p90 1729 ms, max 2690 ms) off and 56 ms (p90 401 ms) on — an `Refuted` hit
still runs P-auto to its 400 ms bound, which is where the remaining cost sits
(§5 step 2; the plan accepted it, §17 item 5).  First-decision latency: 455 ms
mean over all 355 decisions off; 5–7 ms mean over the 204 proved ones on.

Wall time: 412 s off vs 213 s on (instrumented), 415.5 s off uninstrumented;
the uninstrumented cache-on wall time could not be measured (below).

## The 400 ms bound (re-measurement, §10 step 5)

Proved decisions, cache on: median 0 ms, p90 20–28 ms, p99 76–108 ms, max
93–112 ms — the guards this corpus proves sit far below 400 ms of thread CPU.
Refuted decisions reach the bound (p90 401 ms) because P-auto runs to it before
the hit is honoured.  Nothing in this corpus argues for moving the bound.

## Hard failures attributable to guard-side exceptions: TWO, both the known `Option` bug

Both uninstrumented cache-on legs aborted the load of `Phi_System.Phi_Types`
with `exception Option raised (line 84 of "General/basics.ML")` — at the
`\<medium_left_bracket>` of line 2591 (A_on) and the `\<medium_right_bracket>
certified by hammer_or_aoa` of line 2594 (A2_on): the `len_intvl` lemma whose
guards §33 found straddling the bound.  The exception records (Exception_Log,
site `\<phi> statement` and `Phi_Reasoner.reason`) carry no frames without
`ML_debugger`.  This is the bug closed on 2026-09-08 in
`OPTION_EXCEPTION_IN_PROOF_REPLAY.md`: `Pure/Concurrent/future.ML`'s
`assign_result` swallows an asynchronous interrupt (its `Exn.capture_body`
handler has `| _ => ()`), then `the (Single_Assignment.peek result)` on the
never-assigned result raises `Option`.  The one-line fix recorded there (reraise
in that arm) is NOT in the distribution today (`future.ML:425-430`, checked
2026-09-14): `contrib/Isabelle2025-2` is git-ignored, and the patched file did
not survive.  The four instrumented legs and the uninstrumented cache-off leg
did not hit it (the instrumentation and the refuter runs change the timing of
the interrupt window); no proof store was invalidated by the two failures.

## Not measured (no probe installed; the plan lists them)

The lemma replay cost and budget cut-offs (no judge is installed, so no entry
holds a lemma: both are zero on this corpus); the digest cost (measured 76.8 us
per decision on 2026-09-11, §33 item 4); store I/O, the forked-proof write and
the export hook's cost per run boundary (would need TEMPORARY probes; the wall
times above bound them: a cache-on load is 200 s faster than a cache-off one).
