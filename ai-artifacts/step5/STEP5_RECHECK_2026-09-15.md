# Light re-check of the STEP 5 fixes (one Opus agent, read-only, 2026-09-15)

Scope: the conditions of `STEP5_REVIEW_2026-09-14.md` as applied in phi-system commits
`12558336`, `2859c075`, `656a8b42` (the author ruled MD-5 ignored, MD-6 declined).
Every number was recomputed by the agent from the raw `event_log/` data with its own
parser and, separately, by re-running `analyze.py`.

| condition | verdict | evidence |
|---|---|---|
| MD-1 withdraw the "no collision warning" criterion | PASS | The only `— MET` headings left are the concurrent leg ("0 flips, 100 % hits, the shared store intact") and the consecutive leg; the withdrawal states all three reasons, re-verified on disk: `guard_cache.ML:139` passes `rewrites = true`, `cache_file.ML:816` tests it before `ML_debugger`, `REPL.ML:286-296` (`warning_fn := K ()` at `:291`) is called from `repl_server.sh:92`. `Phi_Test/PhiTest_Arithmetic.proof-store` is git-clean with mtime 2026-09-14 22:27:13, between the two F legs' finishes. |
| MD-2 §38's "the legs wrote entries"; C1's hit column | PASS | C1/C2/F1/F2 are each exactly `{(proved,none):204, (refuted,refuted):146, (unknown,unknown):5}`; the per-digest `(verdict, hit)` multisets of C1 and C2 are equal; §35/§36 cited as the cold→warm evidence. |
| MD-3 Quicksort attribution, cache-off qualification | PASS | The G leg's single exception record: `line=45`, `label=command.\<semicolon>`, 22:36:34.913, site `hammer sledgehammer`, `Par_Exn` raised at `par_exn.ML:48`; the `guard_decision` timeline puts line 45 at 22:35:47–22:36:18 and line 49 at 22:41:00–22:41:02; `run.log` shows the colon form at line 49. The cache-off claim is now "no cache-off Phi_Examples leg was run". |
| MD-4 the stores actually modified | PASS | `git status --short -- Phi_Examples \| grep proof-store` lists exactly the eight named; `Rational_Arith.proof-store` untouched. |
| DD-1 "seven other legs", named | PASS | Nine leg directories; only `A_on` and `A2_on` carry the `exception Option` record. |
| DD-2 analyze.py hardening | PASS | `analyze.py:36-40` mixed-verdict check (`-- DEFECT`, never aborting); `:61-72` per-`(digest, verdict)` Counters, flips split from count-only differences; "only in A" printed; 0 offenders in every leg and pairing under the multiset test. |
| DD-3 run_leg.py poll | PASS | `server.poll()` is the first statement of the readiness loop; the wrapper stays alive for the whole leg (the build runs in the foreground and the generated theory blocks in `REPL_Server.startup`), so `poll()` is `None` while healthy. |
| DD-4 the "bounded by the wall times" sentence | PASS | Store I/O and the forked-proof write are gated by `use_store` (`reasoners.ML:1405-1409`); the export hook is installed unconditionally (`guard_cache.ML:177-182`) and stated as not bounded. |
| P-1 harness half (`-o ML_debugger=true`) | PASS, reasoning correct | `ml_options.ML:46` is `Config.declare_option_bool`; `config.ML:182-191` makes the default `fn _ => Bool (Options.default_bool name)` and `config.ML:155-159` evaluates it on every `get` with no context value; the record's gate is that config (`reasoners.ML:1516`). `ML_debugger` (`etc/options:187`) carries no `for build`/content tag, so it never enters `build_prefs_digests` (`sessions.scala:641-643`) and cannot invalidate `Phi_System_Base`. |
| P-2 provenance in result.txt | PASS | Written (truncating) before the server starts, the leg summary appended at the end; if `provenance()` raises it does so before `Popen`, so no server leaks. |
| P-3 refuse a non-empty leg directory | PASS | Before `mkdir` and before the port guard. |
| P-5 the cold→warm recipe | PASS | Recorded in substance. |

Headline numbers recomputed: 355 / 261 per PhiTest leg; 151 of 151 non-proved hits in C1, C2,
F1, F2 and 0 of 151 in E; G: 1756 / 1646, 703 of 708 hits; 0 flips in eight pairings (the five
recorded plus C1↔F1, C1↔F2, C1↔E) under the multiset test; wall times and thread counts match
every `result.txt`; `ANALYSIS_2026-09-14.txt` regenerates byte-identically.

## Other observations (all corrected on 2026-09-15, phi-system commit after this file)

1. "The leg wrote guard entries into eight tracked `.proof-store` files" was false: an entry goes
   to the store of the theory being loaded (`cache_file.ML:812`); the five writes lie in two
   theories — `Dynamic_Array` (4, all at `Dynamic_Array.thy:121`) and `Quicksort` (1,
   `Quicksort.thy:46`). The eight-file list is the set of stores modified in the working tree.
   Report and plan §38 reworded.
2. The Quicksort paragraph cited `reasoners.ML:1637`/`:1670`; as committed the messages are at
   `:1626`/`:1659`. Corrected (cited as committed in `fbb8ad78`).
3. "exported C files (`*.C`, untracked)": six are untracked, `Bucket_Hash.C` is tracked and
   modified. Stated.
4. The `--ml-debugger` path has never been exercised; the report's sentence is an inference. Now
   said so, with the note that such a leg instruments from the first source theory, so its wall
   time is not comparable with the recorded legs.
5. `plpr_thy_diff` used `git diff --` (unstaged only); a staged temporary declare would be
   recorded as no edit. Now `git diff HEAD --`.
6. The 400 ms section's proved-decision ranges covered C1/C2 only; now the four instrumented
   cache-on legs (p90 20–32 ms, p99 76–115 ms, max 93–173 ms, the highest F1's under load).

OVERALL as returned: ISSUES (the six above; none touches a measured number or a ruling).
