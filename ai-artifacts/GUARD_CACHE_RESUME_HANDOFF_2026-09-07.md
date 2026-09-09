# Handoff: resume GUARD_CACHE_QUICK_MODE_PLAN after compaction (2026-09-07)

The stateful-PLPR work is finished, committed and pushed (origin/master at 4a6d9d4c;
its own plan `ai-artifacts/STATEFUL_PLPR_REASONING_PLAN.md`, steps 1–6 + V2 done).
The user now wants to return to the guard-cache rework.

## The plan
`Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` — "PLPR Guard Cache — prove_or_refute rework",
rev 11 (2026-09-04).  Read THIS file for the design; never read the archived
`.rev7-full.md` / `.rev9.md` / `.rev10.md` except for history.

## Where in the plan stack this sits
- Predecessor, in production now: `GUARD_NITPICK_FALSIFY_PLAN.md` — the guard *race*
  (auto-prove vs nitpick-refute concurrently), landed via commits 1fdfbd41, 87cc212d,
  da0626a4, c8178d05 etc.  THIS rework **dismantles** that race.
- This plan is independent of stateful PLPR (no reference to it; sibling spun off
  2026-09-04).  Do not assume a dependency.
- Abandoned siblings (do not revive): `RAUTO_VERIFY_PLAN.md` (abandoned 2026-09-01),
  `DEBT_AXIOM_FILTER_PLAN.md` (closed 2026-09-02).

## Current status (from the plan head)
- rev 11.  **No code has been written.**  Eighth review was NOT_READY (19 upheld);
  the author then redesigned to **no asynchrony at all**: `prove_or_refute` is a
  synchronous function returning a verdict on the spot + a cache + ONE optional judge
  in a global `hook option Unsynchronized.ref` (Futures/groups/joins/judge-crash
  classification all gone) [author 2026-09-04 03:04].
- "Submitted for a ninth review, scoped to §4, §5, §6 and §8."
- "Nothing is pending the author" (§10).
- **First action after compact:** determine whether that ninth review has returned and
  its verdict has been folded in.  If not, run it (5 interrogators → 5 fresh defenders
  → 1 judge, Opus 5, English; harsh-rebuttal standard as for the stateful-PLPR reviews)
  scoped to §4/§5/§6/§8, report to the author, converge, THEN implement.  Do not start
  coding before the author says so.

## Design in one paragraph (essence)
A guard (a `\<condition>`-family premise) is decided by `prove_or_refute`, now a plain
synchronous function: try P-auto (classic prover, `\<phi>guard_classic_prover_timeout`
400 ms), then R-conv, then R-nitpick (`\<phi>guard_refute_timeout` 2000 ms), then the
optional judge ref, then an undecided warning; the verdict is written to its slot and,
when caching is on, to a per-run cache.  §4 is the env + in-memory table, §5 is one
call's control flow (record hits, two replays, `Guard_Record_Stale`), §6 the refuters
and judge, §8 the on-disk persistence (store functor + raw-term codec).

## §10 implementation order (0–5)
0. Re-verify line anchors; `Hasher.terms`; the tracing gate.
1. The factory: parameterise `guard_condition_solver`; `try_prove_or_give_up`;
   `p_auto_body` + `\<phi>guard_P_auto` method_setup; `Guard_Simp_SS` (+attribute,
   +enhance sites); `Nitpick_Refute_SS` rename; `guard_condition_solver'`/`1` on
   P-auto; `fastforce` instance for `defer_premise`; undecided-guard warning as a fn.
2. `prove_or_refute` synchronous over P-auto→R-conv→R-nitpick→judge ref→warning, NO
   table (every call takes the no-record path); `guard_condition_judge`; migrate every
   caller (§3) and `Test/Guard_Race_Smoke.thy`; the `guard_decision` log record.
3. The env + in-memory table: installation, call index, both paths of §5 (record-side
   fed by a test-injected table: hits, two replays, `Guard_Record_Stale`), end-of-run
   steps with the no-cache re-run, R4.
4. Persistence — GATED: proceed only if step (3)'s instrumentation shows record keys
   repeating across two consecutive corpus runs AND a repeated key's final digest
   reproducing.  Then the store functor + `Phi_Guard_Store`, raw-term codec functor +
   `BytesIO` instance, gitignore, record read at install, R1 write, R2, R3.
5. Corpus acceptance: cache-on + cache-off legs, a concurrent Isa-REPL leg, a
   consecutive-run leg with a hit-rate floor; measure wall time, verdict flips, latency,
   refuter distribution, stale/R2/R3 counts, digest cost, store I/O; re-measure 400 ms.
   Testing via Isa-REPL against `Phi_System_Base` sources — NEVER `isabelle build`.

After the plan: move the raw-term codec functor to `Performant_Isabelle_ML`
[author 2026-09-03 14:19].

## Defaults (§10 table)
`\<phi>guard_classic_prover_timeout` 400 ms; `\<phi>guard_refute_timeout` 2000 ms
(R-nitpick's own net = this + 5 s per subgoal); `\<phi>guard_cache` true;
`\<phi>log_guard_race` renamed `\<phi>log_guard_decision`, false.

## Process rules (unchanged, the author's)
- Identify what genuinely needs the author's decision and ask; everything else to
  adversarial review.  Every design/behaviour decision recorded as
  [author YYYY-MM-DD HH:MM "quote"] (UTC, grepped from the transcript).
- Explain in Chinese, essence first then from zero; never coin words.
- Edit the plan ONLY with the Edit tool (never sed/python); reading via Bash is fine.
- This plan's testing uses Isa-REPL against `Phi_System_Base`, never `isabelle build`.
- Commit directly on `master`, never branch; push origin only (also has cslh19 —
  never push it); memory writes need explicit approval; subagents default to Opus 5.
