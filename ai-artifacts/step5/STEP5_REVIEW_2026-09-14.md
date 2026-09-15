# Review of the STEP 5 acceptance work (workflow wf_a73260f5-a8a: 5 interrogators, 4 fresh defenders per finding, a judge; 166 agents, 40 round-one findings, one defender lost to an API safeguard)

# Step 5 review — judge's report

## Verdict on acceptance

**MET_ON_CONDITION.**

Every floor the author fixed on 2026-09-14 is genuinely met by the recorded data, and I re-derived the load-bearing numbers rather than taking them on trust:

- Consecutive-run leg C1→C2: 261 of 261 digests in common, 0 only in B, 0 flips, 151 of 151 non-proved decisions hits (100 %). Verified against the stronger per-(digest, verdict) multiset test as well.
- Concurrent leg F1‖F2 (two REPL processes, as ruled): same 261 digests, 0 flips, 151/151 hits on each server, and each leg's records agree with C2.
- Cache on vs cache off (C2 vs E, both instrumented): 261 common digests, 0 flips; guard time 21.7 s vs 161.4 s; wall 213.2 s vs 412.1 s.
- Corpus order as ruled (PhiTest_Arithmetic, then Phi_Examples). Measurement list produced, with the gaps stated honestly in the report.

No surviving finding invalidates a measured number, and **no re-run is required**. What blocks a clean MET is a set of claims in the acceptance record itself — one criterion declared MET that cannot be evidence at all, one false sentence about what the legs wrote, one misattributed exception record, a miscount, and an instruction to the author that names the wrong set of files — plus the fact that the Pure fix this step applied has no durable record and the repository's own installer will delete it.

**Conditions (all documentation or harness work; none needs a rebuild, a leg, or money):**

1. Withdraw or restate the concurrent leg's "no collision warning" criterion (MD-1).
2. Correct §38:3340 and state C1's hit column in the report (MD-2).
3. Correct the Quicksort attribution and qualify the cache-off claim (MD-3).
4. Correct the "eight theories' `.proof-store` files" instruction to name the nine actually written (MD-4).
5. Give the `future.ML` fix a durable, replayable record and stop `init.sh` from silently deleting it (MD-5).
6. Fix the leg count (five → seven) and the small analyzer/harness items in "Drafter may decide".

Item 5 is a condition because §38 presents the patch as the closure of observation 1 while the only copy of it lives in a git-ignored tree that `./init.sh` is currently wired to `rm -rf`; the acceptance record would otherwise assert a machine state that one ordinary command destroys without warning.

---

## Must discuss

### MD-1 — "No collision warning" is not evidence, and it is listed as a MET criterion — **major**
*(merges `acceptance-2`, `evidence-concurrent-leg-cannot-collide`, `method-2`, `evidence-harness-discards-warnings`)*

`STEP5_REPORT_2026-09-14.md:43` heads the concurrent leg with "no collision warning — MET" and `:49-51` supports it with "Neither server printed the collision marks' warning (`ML_debugger` was on, so the marks were live)"; `GUARD_CACHE_QUICK_MODE_PLAN.md:3309` repeats it, as does the commit message. The observation is impossible three times over, and the parenthetical is backwards:

- A guard-cache write is exempt from the marks *by design*: `guard_cache.ML:138-139` passes `rewrites = true`, and `cache_file.ML:816` sets `mark = NONE` whenever `rewrites` holds — **before** `ML_debugger` is consulted. The plan itself rules this at `:1239-1254` (§36 ruling 9). So the alarm can never fire for a guard entry, with or without the debugger.
- The `written` table is per-process (`cache_file.ML:690-704`, `:724`, `:731`; the message text itself says "in this session"), so it cannot observe the other server — the one thing the concurrent leg exists to probe.
- No warning could have been observed in any leg: `repl_server.sh` has the generated session run `REPL.disable_output ()`, which sets `Private_Output.warning_fn := K ()` (`REPL.ML:286-296`), and `init_printers` — the only route into the per-session message buffer — is never called (`REPL.ML:284` is commented out). Confirmed in the data: every leg's `server.log` is 332 bytes of banner, `repl_out` holds only GC statistics, and no leg artifact contains "warning" or "collision".

Fix: delete the criterion from `report:43`, `:49-51` and `plan:3309`, and say instead what the leg does show — two processes read the same stores concurrently, both ran the end-of-theory `compact_store` full-file rewrite on `Phi_Test/PhiTest_Arithmetic.proof-store` (mtime 22:27:13, between F1's finish at 22:27:06 and F2's at 22:27:20) under the `fcntl` lock, and the file came out byte-identical to HEAD; plus 261 common digests, 0 flips, 151/151 hits on both servers.

Why MUST_DISCUSS: this withdraws a criterion the acceptance declares MET, in three documents including a commit message.

Explicitly **not** required: re-running the leg from a stripped store. Guard entries share `<thy>.proof-store` with the obligation proofs, and with the AoA gate open under Isa-REPL (fixed ruling) a stripped store sends every obligation to a paid model.

### MD-2 — §38 says the legs wrote guard entries; seven of eight wrote none, and C1 was already warm — **minor**
*(merges `evidence-consecutive-floor-proves-no-write`, `method-1`, `acceptance-3`)*

`plan:3340` ("The legs wrote guard entries into the corpus' tracked `.proof-store` files") is false for every PhiTest_Arithmetic leg. Cross-tabulating the records: C1, C2, F1 and F2 are each `{(proved,none):204, (refuted,refuted):146, (unknown,unknown):5}`, and all three of those arms are non-writing paths (`reasoners.ML:1485`, `:1492`, `:1497`); the drop-rewrite is dead because no judge is installed and every entry is lemma-less. `git status` confirms `Phi_Test/PhiTest_Arithmetic.proof-store` is byte-identical to HEAD after the run. Only `G_examples` wrote — 5 entries (3 R-nitpick Refuted, 2 Unknown first decisions). This matters because the very next sentence asks the author to decide which uncommitted store changes to add.

Second half: `report:83-89` gives C2's 151/151 without saying C1's hit column is bit-for-bit identical, so the pair reads as populate-then-hit when it is cross-process read-and-verdict stability against a store committed in `1a02873a`.

Fix (wording only): name `G_examples` as the only writing leg; print C1's hit column beside C2's; and cite §35/§36, which record the cold→warm cross-process pair on this same corpus, as the write→read evidence.

Rejected as a remedy: forcing a cold C1. Beyond the money hazard above, patching `lookup_entry` to return `NONE` for one leg writes byte-identical entries and proves nothing.

### MD-3 — The Quicksort failure is attributed to a record at a different command — **minor**
*(merges `evidence-quicksort-exception-misattributed`, `method-3`, `acceptance-7`)*

`report:70-71` says "one obligation of `Quicksort.thy:49` failed in sledgehammer (`Par_Exn` at `hammer sledgehammer`, the exception record)". The leg's only exception record is at `line="45" label="command.\<semicolon>"`, ts 22:36:34.913. The `guard_decision` timeline puts line 45 at 22:35:47–22:36:18, line 46 from 22:36:35.099, and line 49 only at 22:41:00–22:41:03 — four and a half minutes later; line 45 reported no error. So the line-49 failure has **no exception record and is undiagnosed**, and the report presents it as diagnosed.

The record's payload is a `Par_Exn` raised at `par_exn.ML:48` (`release_all`) wrapping `FOUND` from `par_list.ML:47` — `Par_List.get_some`'s success short-circuit, escaping the handler that should have absorbed it. Describe it factually; the defenders split on whether to call it "normal operation" (it is not: `Exception_Log.capture` records only what escapes `run_sledgehammer`) versus a lost-success anomaly worth its own item, so state what the record is and leave the classification to the author.

Also qualify `report:74-75` "they fail the same way without the guard cache": there is no cache-off Phi_Examples leg. The exculpation is structurally sound — with no judge every entry is lemma-less, `p_auto` runs before the entry is consulted, and `Refuted`/`Unknown` are both `Seq.empty` — so say that, rather than asserting a measurement that was not made.

One datum to check while rewriting (raised by a single defender, not independently confirmed here): the line-49 message in `run.log` carries a colon, a form emitted only by `reasoners.ML:1626`/`:1659` (the guard/safe obligation solvers), not by the hammer path. If that holds, the sentence should not say "failed in sledgehammer" at all.

### MD-4 — The store-commit instruction names eight theories; nine were written — **minor**
*(narrowed from `acceptance-4`)*

`report:73-79` tells the author to decide what to commit from "the eight theories' tracked `.proof-store` files". `Phi_Examples.Dynamic_Array_arbi_len` (231 decisions, imported by `Bucket_Hash.thy:2`) also has a modified store, while the listed `Rational_Arith` contributed 0 decisions and its store is untouched. Following the list literally commits the wrong set. Fix: name the stores actually modified.

The rest of `acceptance-4` is rejected — see below.

### MD-5 — The `future.ML` fix has no durable record, and `init.sh` is wired to delete it — **major**
*(`patch-1`; 4/4 defenders sustained it)*

Verified on disk: `contrib/Isabelle2025-2/src/Pure/Concurrent/future.ML:430` carries the patched arm (md5 `0240c297…`), the tree is git-ignored (`.gitignore:12:/contrib`), no Isabelle2025-2 source is tracked, and there is **no** `contrib/Isabelle2025-2.local.patch` although the sibling convention exists and is tracked (`contrib/afp-2026-05-13.local.patch`, with an apply/regenerate header). `contrib/Isabelle2025-2.md5sum:13265` still holds the pristine digest, so applying the patch is itself what arms `init.sh`: the gate at `init.sh:56` fails (it already fails on ~100 AFP files the tracked AFP patch edits), and `init.sh:59-66` then `rm -rf`s both distributions and re-extracts the 2026-08-24 tarball, which predates the fix. Nothing in `init.sh` re-applies either local patch. This loss has already cost this run once: legs `A_on` and `A2_on` aborted with `exception Option` precisely because the 2026-09-08 fix had never reached this copy.

Proposed discharge (author's choice of route):
- Track a `contrib/Isabelle2025-2.local.patch` (`git add -f`) with the AFP patch's header convention, pointing at `OPTION_EXCEPTION_IN_PROOF_REPLAY.md`; and/or republish the tarball with the fix baked in via the `sync-isabelle-afp-distribution` route.
- Have `init.sh` re-apply both local patches immediately after extraction, **idempotently** (`patch -p1 --forward` behind a dry-run guard; `set -e` at `init.sh:2` would otherwise kill the installer on an already-patched tarball).
- Regenerate `contrib/Isabelle2025-2.md5sum` only from the post-extraction, post-patch tree (or after republishing). Regenerating it from today's patched tree alone would make the gate mismatch after every extraction and re-download 7.8 GB on every run.
- `contrib/Isabelle2024/src/Pure/Concurrent/future.ML` carries the identical unpatched `| _ => ()`; same arm if that tree is still used.

### MD-6 — The raw acceptance evidence is untracked while the report quoting it is committed — **minor**
*(`method-10`)*

Commit `7e7d36ae` committed §38, the report, `analyze.py` and `run_leg.py`; all nine leg directories are `??` and nothing ignores them (`ai-artifacts/.gitignore` holds only `*.tar.zst`). `analyze.py` is a committed script with no committed input, and `A_on`/`A2_on`'s exception records — the only primary evidence for the Option section — cannot be regenerated now that the patch is applied. Size is not an objection: the `event_log` set gzips to ~126 KB.

Fix: commit each leg's `event_log/`, `result.txt`, `run.log` and `server.log`; drop `repl_out/` (376 KB of GC statistics nothing uses). Precedent exists in the same directory (`ai-artifacts/debt-axiom-poly-support/corpus_run_*.out.txt`, `ledger_dump.{pre,post}.txt`). Flagged MUST_DISCUSS because §38 already defers "what to commit" to the author, and because `analyze.py:13`'s absolute cross-repository `sys.path` would also need relaxing for "reproducible from the repository alone" to be literally true.

---

## Drafter may decide

*(mechanical; re-reviewed after application)*

- **DD-1 — "the other five legs" → seven.** `plan:3326` and `report:129-130`. Nine legs ran; `exception Option` appears only in `A_on/run.log:24` and `A2_on/run.log:24`. Name them (C1, C2, E, B, F1, F2, G) so the count is checkable against the directory listing. The error is conservative — it understates the drafter's own evidence. *(merges `evidence-leg-count-wrong`, `acceptance-10`)*

- **DD-2 — `analyze.py` hardening.** Three cheap additions, none of which changes a reported number: (a) assert per leg that every digest carries exactly one verdict and report offenders loudly rather than aborting — verified 0 such digests in all six instrumented legs today, so the set-fold at `analyze.py:47-53` is latent-blind only; (b) compare per-(digest, verdict) decision multisets instead of verdict sets; (c) print "only in A" explicitly alongside "only in B" (it is currently derivable from the printed `|A|`/`|common|`, but only by arithmetic). *(narrowed from `evidence-flip-test-uses-verdict-sets` and `harness-4`; the rest of both is rejected)*

- **DD-3 — `run_leg.py` readiness loop.** Add `if server.poll() is not None: raise RuntimeError(f'server exited with {server.returncode}; see {log_path}')` as the first statement of the loop body, so a build that aborts in 10 s is reported in 10 s instead of after the full 1800 s. Reject the rest of `harness-1`: the deadline **is** a wall clock, and "reset t0 when server.log grows" / "refuse to start if a rebuild is needed" are both worse than the status quo (the latter needs an `isabelle build` probe).

- **DD-4 — Split the "bounded by the wall times" sentence** (`report:137-139`, `plan:3339`). It is sound for store I/O and the forked-proof write, which are gated by `use_store` (`reasoners.ML:1405-1409`) and therefore exist only on the cache-on side. It does **not** bound the export hook, which `guard_cache.ML:177-182` installs unconditionally via `Theory.setup` and which therefore runs on the cache-off leg too and cancels out of the 200 s difference. Say so. *(narrowed from `acceptance-9`; the "lemma half unexercised" half is rejected — the plan rules at `:1329-1333` that phase 1 has no producer of lemmas and assigns that path to §10 steps 2–3, and §38/report already state "no judge installed, every entry lemma-less")*

---

## Proposals

*(labelled as loosenings/extensions, not defects)*

- **P-1 — Let the harness own `ML_debugger`.** `ML_debugger` is a real Isabelle system option (`etc/options:187`; `Config.declare_option_bool` at `ml_options.ML:46`), and `run_leg.py` already passes `-o threads=N`. Passing `-o ML_debugger=true` removes half the PLPR.thy hand edit and gets it echoed into `server.log` for free. The cache switch cannot follow the same route today — `\<phi>guard_cache` is `Attrib.setup_config_bool` (`guard_cache.ML:73`) and `load_theory` elaborates from source under `Options.default ()`, so nothing sent over the client reaches it; making it a `Config.declare_option_bool` backed by a phi-system option would close that too (a product change, worth considering for phase 2).
- **P-2 — Stamp provenance into `result.txt`.** The `git diff` of `PLPR.thy` at leg start, the phi-system HEAD, and the sha of `Pure/Concurrent/future.ML`. Cheap, and it makes a leg directory self-describing without pretending the settings can be applied over the wire.
- **P-3 — Refuse a non-empty leg directory** in `run_leg.py:45` (abort naming the path, or rotate to `<leg>.<ISO>`), mirroring the port guard already at `:47-50`. Do **not** add the proposed `analyze.py` "at most one log file per category" check — it contradicts Event_Log's per-process file naming and would reject correct data.
- **P-4 — Two items outside this diff.** `IsaREPL.Client.__init__` accepts a `timeout` (`IsaREPL.py:132`, stored at `:142`) that nothing ever reads — implement or delete it, since it reads as a safeguard and is not one. And `repl_server.sh:127` echoes a command line different from the one `:128` executes (no `quick_and_dirty=true`, no `REPL_DEFAULT_SESSION`/`REPL_PID`), so every leg's `server.log` misstates the build configuration; harmless here (identical across legs) but worth fixing where it lives.
- **P-5 — If a genuine cold→warm guard pair is ever wanted** (loosening the fixed corpus ruling): strip only the `PLPRGUARD` records from a *copy* of the corpus stores, or load copied theories under new names with `AoA_driver = "test"` declared. Never move tracked `.proof-store` files aside — they carry the obligation proofs and other agents' uncommitted work in this shared tree, and with the AoA gate open every defeated obligation escalates to a paid model. Declaring `AoA_driver = "test"` should also be the default for any future Phi_Examples leg.

---

## Rejected findings

- `evidence-hit-floor-denominator` — "only in B" is printed on the adjacent line and was 0 for the floor leg; excluding proved decisions is store semantics (a first-decision proof writes no entry), and `analyze.py:63-64` already prints proved-entry hits separately. 4/4 refuted.
- `evidence-no-clean-leg-in-shipping-config` — the floors are only measurable under `ML_debugger` by the author's own §37 ruling, so demanding an uninstrumented floor leg asks for an impossibility; the abort's cause is a Pure race validated over five clean uninstrumented rounds in the dossier. 4/4 refuted.
- `harness-2` — the AoA session carries its own 4 h budget (`model.py:12070`, enforced at `driver_api.py:468`), `timeout=None` correctly names the actual behaviour, and a cap on a measurement harness manufactures a result-shaped record with no measurement in it. 4/4 refuted.
- `harness-3`, `method-8`, `acceptance-8` (configuration not recorded) — both knobs are attested in the data (`ML_debugger` by the presence of `guard_decision` records; the cache by the `hit`/`refuter` columns), B_off's 415.5 s sits on the cache-off trajectory (E 412.1 s) and nowhere near cache-on (213.2 s), and the proposed client-side config application cannot work. 12/12 refuted.
- `harness-4` — an empty leg prints "0 decisions, 0 digests" and "0.0 %", a truncated leg prints `|A| ≠ |B|`, and `result.txt` records `loaded`/`errors`; the useful residue is folded into DD-2. 3/4 refuted.
- `harness-5` — every leg directory holds exactly one `guard_decision` file, the one actual re-run used a new leg name (`A2_on`), and a doubled leg would print 710 decisions over 261 digests — the loudest possible signal. 4/4 refuted; the directory guard survives as P-3.
- `harness-6` — the largest error block on disk is 2.4 kB against a 6000-character cap, all nine legs have a `run.log`, and the decisive `Option` evidence is in `event_log/exception/` independent of stdout. The proposed `finally`-clause `result.txt` would raise `NameError` on unbound `startup`/`elapsed`. 4/4 refuted.
- `harness-7` — the store state is recorded per digest by the `hit` field (finer than a file hash), the corpus stores are git-clean at a named commit, and the cache-off leg E independently re-derives every verdict with 0 flips. 4/4 refuted.
- `harness-8` — the scripts die at import on a machine without the path (loud, zero side effects); `parents[4]` is a wrong guess for a phi-system standalone clone, and an env-var Isabelle path would un-pin the one distribution these numbers belong to. 4/4 refuted.
- `harness-9` — `Server.ML:543-546` shadows the connection qualifier with the one in the load message, so `'Phi_Test'` is inert; a short name under `""` fails loudly as a missing file, never as a wrong theory. 4/4 refuted.
- `method-4` — §38 already states that both uninstrumented cache-on legs aborted and that every heap is outdated until rebuilt; the missing wall time follows from that, and the cache-off pair puts instrumentation overhead at −0.8 %. 4/4 refuted.
- `method-5` — the headline comparison is instrumentation-matched by its own heading, and both cache-off walls are printed side by side; a single 3.4 s pair cannot be called a noise bound when the same-configuration repeat C1/C2 differs by 107 s. 4/4 refuted.
- `method-6` — the report names both populations and sample sizes inline, states no ratio, and reports the matched refuted comparison (1006 ms → 56 ms) one clause earlier. 3/4 refuted.
- `method-7` — store I/O and the forked-proof write are inside `prove_or_refute`'s own timer and hence inside the reported 21.7 s guard time; the export-hook grain survives as DD-4. 4/4 refuted.
- `method-9` — factually wrong: Event_Log stamps `theory`, `file`, `line`, `offset` and `label` on **every** record (`event_log.ML:93-110`), and the G leg's records answer both of the questions said to be unanswerable (32 decisions at `Quicksort.thy:49`, 9 at `Matrix_Oprs.thy:140`). The proposed fix would emit duplicate attributes. 4/4 refuted.
- `acceptance-1` — the leg *did* drive the cross-process write path: both servers ran `compact_store`'s whole-file read-modify-rewrite on the same store under the `fcntl` lock, and the posited "loser's snapshot drops the winner's record" is impossible because compaction re-reads from disk inside the lock. 4/4 refuted.
- `acceptance-4` (main claim) — the report states the "and its imports" convention at `:7-8`, and the same convention is far more extreme in the leg it does label (only 15 of C2's 355 decisions are in `PhiTest_Arithmetic` itself); the offered "free cross-check" is 246 digests lying entirely in shared import theories, so it is not independent evidence. Narrow store-list piece kept as MD-4.
- `acceptance-5` — `analyze.py:63-64` already implements the requested proved-entry line (0 in every leg); the proposed denominator ("decisions for which an entry existed") is either circular or uncomputable from the recorded fields. 4/4 refuted.
- `acceptance-6` — `repl_server.sh` is the one build path `CLAUDE.md` explicitly exempts from the never-build rule; the patch's validation is recorded in the dossier (5 clean rounds, `REPLFail = 0`, same uninstrumented configuration); §38 and the report already warn that heaps are outdated. 4/4 refuted.
- `acceptance-9` (as filed) — the lemma half being unexercised is the ruled phase-1 design, and the disclosure demanded is already present verbatim. Narrow export-hook piece kept as DD-4.
- `patch-2` — style only: Pure has longer comment lines (`drule.ML:701` at 142) and backticked comments (`raw_simplifier.ML:270-271`), and the comment is currently the sole in-repo explanation of an arm in an untracked tree.
- `patch-3` — mechanically wrong: `with_attributes`' restoring `set_attributes atts1` sits *outside* the `Exn.capture0` and calls `testInterrupt ()` for asynch states, so `ok` is still discarded and `worker_exec`'s `SYNCHRONIZED "finish"` is still skipped. The wrapper fixes neither loose end and would reinstate upstream's `| _ => ()` wildcard. 4/4 refuted.

---

## Notes

- **Instrumentation is free on this corpus.** The one controlled pair (E_off_dbg 412.1 s instrumented vs B_off 415.5 s uninstrumented, back to back, same cache setting) puts `ML_debugger` overhead at −0.8 %, i.e. inside noise. That closes the "missing uninstrumented cache-on wall time" worry quantitatively: 213.2 s is a sound stand-in. Worth one sentence in the report if the drafter wants it, but not a condition.
- **Two review claims were factually wrong in ways worth recording** so they are not re-raised: `guard_decision` records *do* carry theory/file/line (`method-9`), and `analyze.py` *does* already print both the "only in B" count and the proved-from-an-entry count (`evidence-hit-floor-denominator`, `acceptance-5`).
- **Write-path coverage** for the current code rests on `Test/Guard_Decision_Smoke.thy` (which asserts store content through `lookup_entry` after every probe) and on §35/§36's cold→warm cross-process pairs, plus G_examples' 5 entries in this run — all five of whose digests I confirmed are absent from HEAD and present in the working-tree stores. That is why I did not make a cold re-run a condition.
- **The concurrent leg's real evidence** is stronger than the criterion it was credited with: two processes each performed a full-file `compact_store` rewrite of the same tracked store within seconds of one another, and the file came out byte-identical to HEAD, on top of 0 flips and 151/151 hits on both sides. If MD-1 removes a line, this is the line to put in its place.
