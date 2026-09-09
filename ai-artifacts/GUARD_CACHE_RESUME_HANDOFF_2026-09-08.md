# Handoff: resume GUARD_CACHE_QUICK_MODE_PLAN after compaction (2026-09-08, evening)

Supersedes `GUARD_CACHE_RESUME_HANDOFF_2026-09-07.md`.  NO CODE HAS BEEN WRITTEN AND
NONE MAY BE until the author says "开工" — the author reminded me of this today.

## Where the plan is
`contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` is **rev 15** (2026-09-08).
Archived: `.rev7-full.md`, `.rev9.md` … `.rev14.md` beside it.  Read rev 15 itself
(§1 glossary authoritative; §17 = the 2026-09-08 redesign rulings; §18 = the
lemma-budget rulings).  Design in one sentence: **the cache stores advice, not
verdicts** — every `prove_or_refute` call decides its guard by P-auto on every run;
the store (`<thy>.guard-cache`, keyed by the guard's digest) keeps per guard the
judge's lemmas (each with a tier budget) and the last verdict `Proved | Refuted |
Unknown`; no run-level state, `gen_reason'` untouched; refuters inline and
sequential; the lemma budget is enforced by weakening each lemma to
`Guard_Budget \<r>BUDGET<i> ⟹ P` (`Guard_Budget :: ind ⇒ bool`, `hide_const (open)`
at the end of PLPR.thy) and one ctxt-local simproc on `Guard_Budget ?v` counting in a
`Strhashtab` keyed by the fixed variable's internal name; lemmas live in a
`Proof_Data` thm list `Guard_Lemmas` carried across statements by a
`PLPR_Context_Export` hook (stateful PLPR, already implemented).

## The thirteenth review (rev 15) came back NOT_READY — verdict at
`/tmp/claude-1002/-home-qiyuan-Current-MLML/dcf9a85a-9a01-420a-9a51-ce2e8b6bec19/scratchpad/rev15-verdict.json`
(workflow `wf_d0bf5d11-dba`).  I re-verified it: 8 MAJOR + 9 MINOR, ALL genuine, all
DRAFTER_FIX; the judge discarded 6 nitpicks (rightly).  Reported to the author
(Chinese) on 2026-09-08 ~13:10 UTC.  Fixes to apply in rev 16:
- DUP-LEMMAS: my "merge_ss dedupes" sentence is false (each copy carries its own
  `\<r>BUDGET` Free → distinct props).  Fix: §5 step 1 append is idempotent by
  `Thm.eq_thm_prop`; one budget per statement; drop the merge_ss dedupe claim.
- PROOF-CACHE type: `cache_file.ML` CHANGED under us (commit 7615fe5 + uncommitted):
  `proof_cache = times * string`, `times = {thread_cpu, wall}` (`:168`, `:274`),
  `replay_limits :228`, `ms_of_times`/`times_of_ms` (~:279-281).  ALL cache_file.ML
  anchors in the plan are stale — re-take by symbol, never by offset.  §8 codec:
  pack `times` as a pair of ms.
- BUDGET-CHARGED-BEFORE + WEAKENING-BEFORE-MKSIMPS: do `Raw_Simplifier.mksimps ctxt`
  FIRST on the raw lemma, then weaken EACH derived rule with the budget premise
  rotated to the LAST position (`Thm.implies_intr` + `Thm.permute_prems`), then add.
- ENHANCE-TWO-OWNERS: `enhance_with_lemmas` is called INSIDE each consumer
  (`p_auto_body`, R-conv body, "G.simpcut"), once per consumer run; §3/§5 wording
  "P-auto on ctxt_g".
- SIMPCUT-HAS-NO-WALL-CLOCK: §7 sentence false for "G.simpcut" → relaxation 1.
- DIGEST-DEPENDS-ON-AMBIENT-NAMES: digest is after `oblg_template`'s
  `Variable.import_inst` (`reasoners.ML:364`); fresh Free names vary with the ctxt's
  name pool → relaxation 2.
- FACTORY-CONTRACT: add `prj : 'a -> thm` (guard path `snd`), `apply_tac`'s `SOLVED'`
  tests `Thm.nprems_of (prj st')`; add `apply_tac` (`reasoners.ML:222-228`) to the
  migration list; `head_only`'s zero-premise arm goes through `inj`.
- MINORs: replay floor from `\<phi>guard_classic_prover_timeout` via
  `replay_limits_with` (per §15.7); judge must not under-state its times; R-nitpick
  outer net bounds only when the next subgoal may start (nested Timeout semantics,
  `timeout.ML:48-56`); interrupt sentence: both Pure's and the shadow's conversions
  (`accounted_timeout.ML:113-133`, `:142-147`); §7 "no entry written" needs "unless a
  Refuted/Unknown entry is promoted"; "judge not told" → "no lemmas field; must ignore
  those in judge_arg.ctxt"; dropped-lemma warning: give it a gate (I intend
  unconditional `warning`) and content; §10: steps 1 and 4 change files inside the
  `Phi_System_Base` heap → each needs the author's approval to rebuild it; switch-off
  sentence scoped (store's at_end still touches the file).

## Pending the author (asked, unanswered at compaction)
1. Relaxation 1: wall-clock bound on "G.simpcut" (`\<phi>guard_classic_prover_timeout`;
   timeout = state unchanged).  Touches [author 2026-09-03 12:53].  I recommend yes.
2. Relaxation 2: normalise the digest against `import_inst`'s fresh names (replace
   newly-fixed Frees/TFrees by positional placeholders before hashing).  Touches
   [author 2026-09-08 06:10 "2. 不掺"; 07:05; 11:52].  I recommend yes.
Then: write rev 16 by hand (archive rev 15 as `.rev15.md`; the pattern used: write the
new head+§1–§10 to the scratchpad, `cat` with the unchanged tail from "## 11." and a new
§19), re-read, run the fourteenth review (Workflow: 5 interrogators → 5 fresh defenders
→ 1 judge, Opus 5, English, REBUT HARD — the author demands harsh rebuttal of nitpicks;
after it returns I must re-verify every finding in code myself and drop nitpicks before
reporting), report in Chinese, converge.  Review scripts live under
`~/.claude/projects/-home-qiyuan-Current-MLML-contrib-phi-system/dcf9a85a-…/workflows/scripts/`
(guard-cache-plan-review-13-….js is the latest; copy its shape).

## Facts learned today (keep)
- Isabelle's simplifier has no loop detection for unconditional rules; `trace_ops` is
  Theory_Data kept by the FIRST parent on merge (lost under `Phi_Preliminary`, whose
  first parent is `SSymb`); per-call derived theories give unrelated sibling
  certificates (`context.ML:483-495`, `:663-669`).  Hence the conditional-rule +
  simproc budget.  Measurements: `ai-artifacts/Simp_Loop_Probe.thy`,
  `Lemma_Simproc_Probe.thy`, `Simp_Count_Base.thy`/`Simp_Count_Probe.thy`,
  `simp_count_report.txt` (legit rules 100–895 per invocation; only One_nat_def >1000;
  Big_def = 66 % of all rewriting — a phi-system perf issue, out of scope).
- Term codec: msgpack (`RPC_Pretty.pack_raw_term`) kept; `Term_Codec_Bench.thy`.
- The Simp_Count probe copied PhiTest_Arithmetic under a new name, defeating its proof
  store → AoA + semantic interpretation ran, ≈ $23.  Semantic-DB residue (126 records)
  removed via the library (`contrib/Semantic_Embedding/ai-artifacts/probe_cleanup_*.py`,
  `probe_deleted_records.json`).  Author: file residue "别管"; future probes must not
  load phi-system theories under new names.
- `Phi_System_Base` heap was rebuilt today on the author's approval (13:23 UTC).
- Uncommitted: the plan + archives rev11–rev14, ai-artifacts probe files, the deletion
  of the "in-process only" comment on `Hasher.compact` (auto_sledgehammer, on the
  author's order 2026-09-07 13:05; `Hasher.compact` itself is also uncommitted there),
  Semantic_Embedding cleanup scripts.  Commit only when the author says.

## Process rules (the author's)
Never write code before "开工"; edit the plan only by hand (Edit/Write, never sed/python
over its text); every design decision tagged [author YYYY-MM-DD HH:MM "quote"] with
UTC timestamps grepped from the transcript (`~/.claude/projects/-home-qiyuan-Current-MLML/dcf9a85a-9a01-420a-9a51-ce2e8b6bec19.jsonl`);
explain in Chinese, essence first, then from zero; never coin words (fixed terms:
record/entry/store/the lemma list/the lemma budget/ctxt_g/ctxt1); do not relay agents'
progress ticks; never `isabelle build` without explicit approval; commit on `master`,
push origin only; memory writes need approval.
