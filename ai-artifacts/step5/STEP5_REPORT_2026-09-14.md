# STEP 5 — corpus acceptance via Isa-REPL (2026-09-14)

Plan: `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` §10 step 5, §37 item 12.  Harness:
`run_leg.py` (one fresh Isa-REPL server per leg on the `Phi_System_Base` heap,
`load_theory` of the corpus from source, wall clock by the harness, the
`guard_decision` records into the leg's own `event_log` directory) and
`analyze.py`.  The corpus: `Phi_Test.PhiTest_Arithmetic` and its imports (the
355-decision corpus of §26/§30/§35/§36).  Threads 8 per server (6 each on the
concurrent leg); 14 cores.  For the legs below, each leg's configuration
(`ML_debugger` for the records, `\<phi>guard_cache = false` for a cache-off leg)
was a TEMPORARY `declare` in `PLPR.thy`, reverted before the commit.  Since the
review (2026-09-15) the harness passes `-o ML_debugger=true` to the server
itself (`--ml-debugger`: an Isabelle system option reaches every theory the
server compiles from source — an inference from `config.ML`'s option-backed
defaults, not yet an observation: no recorded leg used the flag; a leg that
does instruments from the first source theory rather than from `PLPR.thy` on,
so its wall time is not comparable with the legs below — so no `PLPR.thy`
edit is needed for the records; the cache switch is a context attribute and
still needs the `declare`),
records in `result.txt` what the leg ran under (phi-system HEAD, the server
options, `PLPR.thy`'s diff, the sha256 of `future.ML`), and refuses a non-empty
leg directory as it already refused an occupied port.

If a genuine cold → warm guard pair is ever wanted (this step's consecutive leg
was warm → warm): strip only the `PLPRGUARD` records from a COPY of the corpus
stores, or load copied theories under new names, and declare
`AoA_driver = "test"` first.  Never move the tracked `.proof-store` files aside:
they carry the obligation proofs and other agents' uncommitted work in this
shared tree, and with the AoA gate open every defeated obligation escalates to a
paid model.

**The AoA gate is open under Isa-REPL, by design** (the author, 2026-09-14:
"AoA 应该在 Isa-REPL 下工作的, 这是 expected").  The gate (`agent_server.ML:560-562`)
opens on the second component of `Dialogue.frontend_identity ()`, which is
`SOME true` under the REPL server.  Consequence for a corpus run: every
obligation missing from its store escalates to the language model and costs
money.  The `PhiTest_Arithmetic` corpus has no missing obligation; the
Phi_Examples leg had three (`Bucket_Hash.thy:20`, `:99`, `Matrix_Oprs.thy:140`),
whose escalation failed only because the local proxy was down ("local
openai-oauth proxy unreachable at http://127.0.0.1:8317/v1/").  The plan's
step-5 clause "AoA escalation disabled in the harness" was the drafter's own
assumption and is corrected in §10; a future Phi_Examples leg either accepts
the cost or declares `AoA_driver = "test"`.

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
| A_on | on | off | 182.0 s (aborted) | — | — | `exception Option` at `Phi_Types.thy:2591` (the future.ML bug, patched afterwards) |
| A2_on | on | off | 243.2 s (aborted) | — | — | `exception Option` at `Phi_Types.thy:2594` |
| F1_conc, F2_conc (two servers at once, 6 threads each) | on | on | 365.4 s, 379.2 s | 355 / 261 each | 26.8 s, 24.0 s | clean, clean |
| G_examples (the eight Phi_Examples theories) | on | on | 1059.1 s | 1756 / 1646 | 269.0 s | 4 obligation errors, see below |

## The concurrent leg (F1 ‖ F2): 0 flips, 100 % hits, the shared store intact — MET

Two Isa-REPL servers loaded the corpus at the same time, sharing the tracked
`.proof-store` files.  Each saw 355 decisions over 261 digests with the
verdict distribution of the sequential runs; 261 digests in common between
the two and with C2, 0 flips in every pairing; 151 of 151 non-proved decisions
hits on both.  Both servers ran the store's end-of-theory `compact_store` —
a whole-file rewrite under the `fcntl` lock — on
`Phi_Test/PhiTest_Arithmetic.proof-store`: the file's mtime (22:27:13) lies
between F1's finish (22:27:06) and F2's (22:27:20), and afterwards the file
is byte-identical to the committed HEAD.  So two processes reading and
rewriting one store file concurrently neither corrupted it nor changed a
verdict.  Wall 365 s and 379 s against 213 s alone: the two servers shared
the 14 cores.

(The first version of this report also listed "no collision warning" as a
criterion here.  Withdrawn: the collision marks cannot observe this leg at
all — a guard entry's write is exempt from them by design (`rewrites = true`,
`guard_cache.ML:138`; `cache_file.ML:816` tests it before `ML_debugger`), the
`written` table is per process and sees nothing of the other server, and the
REPL server silences warnings altogether (`REPL.disable_output ()` in
`repl_server.sh`'s generated theory, `REPL.ML:286-296`).  "No warning" was
vacuously true of every leg.)

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

The load ended with four errors.  Three are obligations whose proof is not
in the store, escalated to AoA and failed on the unreachable proxy (above);
they do not involve the guard cache.  The fourth is at `Quicksort.thy:49`:
"Fail to solve the proof obligation automatically:" with the obligation —
the colon form, which only the on-the-spot obligation solvers print
(`reasoners.ML:1626`, `:1659` as committed in `fbb8ad78`:
`guard_condition_solver1` / `safe_obligation_solver1`, called from `toplevel0.ML:387`,
`generic_variable_access2.ML:272`, `local_value.ML:169`), not the hammer
path.  It is UNDIAGNOSED: the leg's only exception record is not it — that
record is at `Quicksort.thy:45` (the `;` command, 22:36:34.913, four and a
half minutes before line 49 ran at 22:41:00–22:41:03): a `Par_Exn` raised at
`par_exn.ML:48` wrapping `FOUND` from `Par_List.get_some`'s success
short-circuit (`par_list.ML:47`), escaping `run_sledgehammer` into
`Exception_Log.capture`; line 45 itself reported no error.  (An earlier
version of this report attributed that record to line 49.)  Those on-the-spot
solvers run the guard factory with `p_auto_solving` and no digest step, so
they never consult the store; whether the guard cache's changes to the shared
machinery (P-auto's body, the "G.simpcut" bound) touch the line-49 obligation
is not known: no cache-off Phi_Examples leg was run (it would escalate every
missing obligation to a paid model unless `AoA_driver = "test"` is declared).
Whether the three escalated obligations have proofs in the stores on the
author's machine, or were always AoA-solved, this leg cannot tell.

The leg wrote five guard entries, into the stores of the two theories the
decisions are in (an entry goes to the store of the theory being loaded,
`cache_file.ML:812`): four into `Dynamic_Array`'s (all at `Dynamic_Array.thy:121`:
3 `Refuted` by R-nitpick, 1 `Unknown`) and one into `Quicksort`'s
(`Quicksort.thy:46`, `Unknown`).  After the leg, eight tracked `.proof-store`
files are modified in the working tree — those of `Binary_Search`,
`Binary_Trees`, `Bucket_Hash`, `Dynamic_Array`, `Dynamic_Array_arbi_len`
(imported by `Bucket_Hash`), `Linked_List`, `Matrix_Oprs` and `Quicksort`
(`Rational_Arith`'s is unchanged) — but those eight were ALREADY modified
before this step by other, uncommitted work, and the end-of-theory
`compact_store` rewrites a store even when it holds no new entry; the leg also
regenerated the theories' exported C files (six untracked `*.C`, plus
`Bucket_Hash.C`, which is tracked and shows as modified).  This step's commits
leave every store and every generated file uncommitted — the author decides
what to add.

## The consecutive-run leg (C1 → C2): floor 100 % hits, 0 flips — MET

261 digests in C1, 261 in C2, all 261 in common, 0 only in either; verdict sets
equal on every digest (0 flips).  Of C2's 151 non-proved decisions, 151 are hits
(100 %): 146 `Refuted` hits, 5 `Unknown` hits — and C1's hit column is the
same, decision for decision.  The 204 proved decisions are first decisions in
both runs by design (a first-decision proof writes no entry, §5 step 3).

What this pair is evidence of: cross-process stability of reading — two fresh
processes, in sequence, read the entries committed in `1a02873a` (the store
was already warm before C1) and decide identically.  Neither C1 nor C2 wrote an
entry: every decision took a non-writing path (a first-decision proof, a
`Refuted` hit, an `Unknown` hit with no judge), and
`Phi_Test/PhiTest_Arithmetic.proof-store` is byte-identical to HEAD after the
run.  The cold → warm pair on this corpus (the entries written, then read in a
new process) is the one recorded in §35/§36 of the plan.

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

Proved decisions, cache on, over the four instrumented cache-on legs (C1, C2,
F1, F2): median 0 ms, p90 20–32 ms, p99 76–115 ms, max 93–173 ms (the highest
figures are F1's, under the concurrent load) — the guards this corpus proves
sit far below 400 ms of thread CPU.
Refuted decisions reach the bound (p90 401 ms) because P-auto runs to it before
the hit is honoured.  Nothing in this corpus argues for moving the bound.

## Hard failures attributable to guard-side exceptions: none; two legs hit the known `Option` bug

Both uninstrumented cache-on legs aborted the load of `Phi_System.Phi_Types`
with `exception Option raised (line 84 of "General/basics.ML")` — at the
`\<medium_left_bracket>` of line 2591 (A_on) and the `\<medium_right_bracket>
certified by hammer_or_aoa` of line 2594 (A2_on): the `len_intvl` lemma whose
guards §33 found straddling the bound.  The exception records (Exception_Log,
site `\<phi> statement` and `Phi_Reasoner.reason`) carry no frames without
`ML_debugger`.  This is the bug closed on 2026-09-08 in
`OPTION_EXCEPTION_IN_PROOF_REPLAY.md`: `Pure/Concurrent/future.ML`'s
`assign_result` swallows an asynchronous interrupt (its `Exn.capture_body`
handler had `| _ => ()`), then `the (Single_Assignment.peek result)` on the
never-assigned result raises `Option`.  The one-line fix recorded there was
found missing from `contrib/Isabelle2025-2/src/Pure/Concurrent/future.ML`
(git-ignored directory; the file's mtime 2026-01-18 says the 2026-09-08 patch
never reached this copy) and was applied on this machine on the author's
order ("请对本机打补丁"): `future.ML:430-431`, the `Exn.Exn` arm reraises.  Pure
changed, so every heap is outdated until the author rebuilds.  The other seven
legs (C1, C2, E, B, F1, F2, G) did not hit the bug (instrumentation and the
refuter runs shift the interrupt window); no proof store was invalidated by
the two failures.

## Not measured (no probe installed; the plan lists them)

The lemma replay cost and budget cut-offs (no judge is installed, so no entry
holds a lemma: both are zero on this corpus); the digest cost (measured 76.8 us
per decision on 2026-09-11, §33 item 4).  Store I/O and the forked-proof
write exist only on the cache-on side (both gated by `use_store`,
`reasoners.ML:1405-1409`), so the 200 s by which a cache-on load beats a
cache-off one bounds them from above.  The export hook is installed
unconditionally (`guard_cache.ML:177-182`, `Theory.setup`) and runs on the
cache-off leg too, so it cancels out of that difference and is NOT bounded by
it; measuring it would need a TEMPORARY probe at the run boundary.
