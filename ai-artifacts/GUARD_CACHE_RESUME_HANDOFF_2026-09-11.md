# Handoff: guard cache — step 4 REDONE on the author's design (entries in the proof store); uncommitted; audit findings pending the author (updated 2026-09-12 evening)

Plan: `contrib/phi-system/Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` rev 24.  §1 glossary (the guard digest
bullet carries the 2026-09-11 correction); §33 the 2608 flip + tier measurement shelved; §34 step 3
first half; §8 REWRITTEN 2026-09-12 to the author's design (the store IS the proof store) with a
CORRECTION of the record; §35 still describes the withdrawn functor design and must be rewritten.

## What happened on 2026-09-12 (read this first)
1. Step 4 was first implemented as a functor over `cache_file.ML` plus a second store instance writing
   `<thy>.guard-cache` (auto_sledgehammer `316f143`, phi-system `1cc4e95e`, root `859c1174`).  The
   author rejected it: their design, said repeatedly on 2026-09-03 and again today, is that guard
   entries go INTO the existing proof store `<thy>.proof-store` through `Phi_Proof_Store.get_cached_proof`
   / `update_cached_proof`, key `"PLPRGUARD" ^ Hasher.compact d`, `hash = NONE`, `zero_times`, the
   packed entry as the text.  The functor was the drafter's/reviewers' invention filed under author
   citations — "纯粹是胡闹…必须撤回这些".  REVERTED: auto_sledgehammer `5ac4877` (cache_file.ML
   byte-identical to `1360b21`, i.e. the dead `openning_stores` bool and the `at_end`/`compact_store`
   gate are gone too — both were the drafter's, not adopted).  guard_cache.ML now calls
   `Phi_Proof_Store` directly; `.gitignore` lines removed; all `*.guard-cache*` files deleted.
   Entries land in the git-TRACKED `*.proof-store` files (42 in phi-system): intended ("1. 好").
2. Source comments were rewritten to be for readers: no `[author …]`, dates, review labels or
   measurement logs (reasoners.ML, guard_cache.ML, guard_refute.ML, guess_instantiate.ML, the test theory).
   Rule from the author: comments are short, load-bearing, never the drafter's notes.
3. Three feedback drafts filed (digest scope; separate store file; comment style).
4. An Opus audit of the plan's provenance found more over-claims — see "Pending the author".

## Current state of the tree (UNCOMMITTED in phi-system; auto_sledgehammer committed at 5ac4877)
phi-system modified: `.gitignore`, `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` (§8 rewritten), `PLPR.thy`
(carries the TEMPORARY declare `[[\<phi>log_guard_decision = true, AoA_driver = "test",
AoA_write_proof_store = false]]` after the `\<phi>guard_P_auto` method_setup — REVERT before commit),
`Test/Guard_Decision_Smoke.thy` (comment; `fresh` = run tag + serial), `library/guard_cache.ML`,
`library/guard_refute.ML`, `library/guess_instantiate.ML`, `library/reasoners.ML` (comments only),
plus the proof stores the corpus run wrote guard entries into (`Phi_System/Phi_Types.proof-store`,
`Phi_Test/PhiTest_Arithmetic.proof-store`, `Phi_Semantics/PhiSem_CF_{Basic,Break,Breakable}.proof-store`,
new `Phi_System/Resource_Template.proof-store`, new `Test/Guard_Decision_Smoke.proof-store`).
`Phi_Semantics/PhiSem_Real_Abst.proof-store` (untracked) is another agent's — leave it.
Verified on the reverted heap: PLPR.thy clean, test theory clean, cold corpus clean (355 decisions, 129 s
of guard time, entries written).  The Phi_System_Base heap was rebuilt again (4th time today) because
other sessions changed Isa-Mini/Semantic_Embedding; the WARM corpus run in a fresh process (expect
146 Refuted + 5 Unknown hits read from the proof stores, ~21 s) was about to start.

## Remaining for step 4
- warm corpus run; revert the TEMPORARY declare; re-evaluate PLPR.thy; rewrite §35 (and §1/§4/§10
  mentions of `Phi_Guard_Store`/`<thy>.guard-cache`, see audit A3); commit phi-system (master) and
  bump both submodule pointers in the root (`git add -f contrib/phi-system contrib/auto_sledgehammer`).
  NO push.
- The proof store's key-collision alarm (`written` table + "two DIFFERENT proofs under one key"
  warning in cache_file.ML): never approved by the author (archaeology 2026-09-12: settled by review
  agents K1/K2 on 2026-08-16, implemented after a blanket "开始动手"); misfires on legitimate guard
  entry rewrites AND on interactive re-evaluation in PIDE (the table is a process-global
  Synchronized.var keyed by theory name, closed only at Theory.at_end).  Options put to the author:
  (i) delete the mechanism; (ii) keep, exempt guard entries (explicit bit on the write / prefix);
  (iii) keep, reword.  UNDECIDED — do nothing until ruled.

## Pending the author (from the 2026-09-12 audit; do not act before a ruling)
- A4: plan §1 says the judge "may re-enter PLPR", reversing the author's rule (2026-09-07 13:21 "judge
  不能重入 PLPR") on the drafter's own bullet; mark [drafter, 待裁].
- A1: §1 judge contract and §7 cite "2. 不掺" (which ruled assumptions OUT of the digest, since
  reversed) for "not the simpset/lemmas/local facts"; §7 still says the digest excludes assumptions
  (false).  A9: unmarked drafter clauses in the judge contract (closed `prop` lemmas; RAW times
  normalised on receipt; judge must be re-entrant; "no deletion" [descriptive] vs the author's C6
  "墓碑用 invalidate_proof_cache 采纳").  A2/A6/A7/A8: citation errors (the key's citation points at
  the author's objection; "two entry points, no new ones" is drafter wording over "C7 好"; tier tag
  cited to 09-03; the codec-parameter withdrawal was the author's).  A10: §10 "Nothing is pending the
  author" is false.  C: no author message exists at 2026-09-03 07:48 although the drafter cited it;
  §10 step 2's deletion of `\<phi>log_guard_race = true` had no ruling.
- Earlier open items: tier measurement shelved (§33); `is_F` left to the follow-up constant
  `\<check> \<hypothesis> \<consistency>`; phase-2 points (budgeted lemma = conditional rule; `Frequent`
  = ceiling; may a judge lemma cite assumptions).

## Then: STEP 5 — corpus acceptance via Isa-REPL (plan §10 step 5; AoA gate closed there).

## Rules (the author's, all binding)
Edit source with the Edit tool; plan docs by hand; never coin words; explain in Chinese, essence first,
full context, exact file:line; `isabelle build` only with approval (Phi_System_Base rebuilds were
approved for step 4); after `.ML` edits re-evaluate; never git stash/checkout/reset/clean; commit on the
repo's current branch, push origin only, only when told; memory writes need approval; probes must not
load phi-system theories under NEW names; monitor long runs ≤10 min; review shape: workflow, Opus,
English, interrogators → fresh defenders → judge; no code change on AUTHOR_DECISION items before the
author agrees; quote the author verbatim and mark any narrowing [drafter] — never file a drafter's or a
reviewer's design under an author citation; source comments are for readers (short, no citations,
no dates, no logs).  Corpus loads under Isabelle-MCP: add the TEMPORARY test-driver declare (the
author calls AoA escalation expected behaviour; the declare keeps verification runs deterministic).

## ADDENDUM 2026-09-14 night — STEP 5 run; pending the author's acceptance (READ THIS FIRST)
Plan rev 27, §38; the report `ai-artifacts/step5/STEP5_REPORT_2026-09-14.md`; the harness
`ai-artifacts/step5/{run_leg.py,analyze.py}` (one fresh Isa-REPL server per leg; the
harness kills the listener on its port afterwards -- a poly process outlives its process
group -- and refuses a port that already answers).  Floors met: consecutive runs 100 % hits /
0 flips; cache on vs off 0 flips; two concurrent servers 0 flips, no collision warning;
Phi_Examples clean on the guard side.  Two findings for the author, NOT the guard cache's:
(1) `exception Option` (future.ML's assign_result, the 2026-09-08 fix is not in the
distribution) aborted both uninstrumented cache-on legs at Phi_Types.thy:2591/2594;
(2) the AoA gate is OPEN under Isa-REPL (frontend_identity answers SOME true) -- the
Phi_Examples leg reached for the Codex API and was saved by the proxy being down; never run a
Phi_Examples leg again without `AoA_driver = "test"` or a closed gate.  The review of the
audit-rulings code: ACCEPTED_ON_CONDITION, both conditions applied (phi-system fbb8ad78,
Performant_Isabelle_ML a28e6f2).  PLPR.thy is at its committed text (every TEMPORARY declare
reverted).  Uncommitted and NOT mine to commit: the corpus' and Phi_Examples' `.proof-store`
files (guard entries written on top of other work's modifications), Phi_Examples' `*.C`/`*.o`.
NEXT: the author's acceptance of step 5; then the deferred plans (tier measurement, the
`\<check> \<hypothesis> \<consistency>` constant, the Isabelle_RPC rendering unification).

## ADDENDUM 2026-09-14 — the provenance audit ruled; where to resume
Plan rev 26, §37: every item of the audit (B2–B9) was gone through one by one and ruled;
B10 (plan text) was the drafter's to fix and is fixed (A1, A2-class citations, A4, A9,
A10).  Code changed accordingly (list in §37 "What changed in code"); PLPR.thy and both
test theories clean under Isabelle-MCP; Event_Log's marker format checked by the
TEMPORARY probe `Performant_Isabelle_ML/ai-artifacts/Event_Log_Marker_Probe.thy` (delete
it once `Test/Event_Log_Test.thy` has run on a rebuilt heap); the author's event logs
migrated in place (591 files).  Isa-Mini's `toplevel.py`/`translator` are still another
agent's, untouched.
NEXT, in order: (1) a review of today's code (workflow, Opus, English, interrogators →
fresh defenders → judge; report in Chinese; no fix before the author agrees on the
MUST_DISCUSS items); (2) the author rebuilds Phi_System_Base (`event_log.ML` is in the
heap) — never run `isabelle build` yourself; then `Test/Event_Log_Test.thy` with
ISABELLE_EVENT_LOG_DIR set to a scratch directory; (3) STEP 5 per §37 item 12 (Isa-REPL,
cache-on/off, two concurrent REPL processes, consecutive-run floor 100 % hits / 0 flips;
the earlier corpus first, then Phi_Examples).  DEFERRED by ruling, after step 5: the tier
measurement (§33 "(a)"), the `\<check> \<hypothesis> \<consistency>` plan, the
Isabelle_RPC rendering unification (one rendering function for `pretty_unicode` and
`FileIndex`; `UNICODE_CONSISTENCY_FIX_PLAN.md` is the draft), phase-2 point 2.
Standing rule added today: a departure from an author decision, or a drafter decision
recorded as the author's, is reported with a feedback draft ("对这种对我当时的决策的偏离请问
责然后报告").  PLPR reasoning is DETERMINISTIC: a replay of an entry happens in the same
ctxt0 with the same fact names — never reason as if it were "another context".

## ADDENDUM 2026-09-13 evening — where to resume after compaction
Everything is committed on the repos' current branches, nothing pushed: phi-system master
`643f6da4`, auto_sledgehammer main `8134469`, Isa-Mini main `cfe6942`, root `f4a01a43`
(Isa-Mini's `IsaMini/AoA/toplevel.py` and `translator` are another agent's, untouched).
DONE today: the delta redesign (plan §36: entry = {delta = {added, deleted}, verdict};
identity = plain `Pattern.equiv`, no binder handling; one append rule, the delta's budget
wins; `same_prop` total; the judge gets guard_ctxt + the entry's delta on this machine's
clock and answers `Provable of delta` which replaces the entry's; `canonical_form` gone) —
two adversarial reviews + one light check, all fixes applied; the collision marks (plan §8,
§36 ruling 9: `update_cached_proof {id, hash, rewrites}`, guard_cache writes rewrites = true;
marks dropped at Theory.at_begin too; mark = {digest = Hasher.string text, head via
Symbol.beginning, ms}; the whole mechanism only under the RUNTIME ML_debugger; the warning is
the author's four lines; tests 20–20i) — two adversarial reviews, all fixes applied; the
word "battery" scrubbed; the two test theories' `.proof-store` files are NOT tracked (ruled).
Reports: ai-artifacts/DELTA_REDESIGN_REVIEW_2026-09-13.md, …_REREVIEW_…, COLLISION_MARKS_REVIEW_…,
COLLISION_MARKS_REREVIEW_….  The Phi_System_Base heap is current (the author rebuilt it).
STILL PENDING THE AUTHOR (go through one by one, no code change before a ruling):
- the provenance audit's B2–B10 (see the addendum "2026-09-12 late" below; B1 ruled "ignore",
  the canonical form and the collision marks are settled): B2's rest — the guard_decision
  record's fields and "permanent" status, the loud guard warning's results text, the
  dropped-lemma warning ungated, the option name \<phi>log_guess_inst, the export hook's
  priority 200 + overwrite, the catch-all decode; B3 proof store (ruling O widened 1b05b2b,
  goal-hash 0146687, "Find proof" trace c88ad1d); B4 phi-system 752be368 / d4cbde68 / 08-09
  failure text; B5 Isa-Mini price table + cost line; B6 Event_Log default dir + XML boundary;
  B7 Semantic_Embedding D19; B8 Isabelle_RPC pretty_unicode regression + map size/version;
  B9 jEdit slice (A1–A4); B10 plan-provenance errors (A1 "2. 不掺" re-gloss, A2, A4, A9, A10).
- earlier deferred: tier measurement (§33); `\<check> \<hypothesis> \<consistency>`; phase-2
  points (budgeted lemma = conditional rule; Frequent = ceiling; may a judge lemma cite
  assumptions); STEP 5 (Isa-REPL corpus acceptance).
Rules unchanged (see "Rules" above); in addition today: call things by their names — the
collision marks (`written`), a proof obligation, a proof id, the key mint, a test case (an
ML block of a test theory), the two test theories by name; never "探针"/"battery".

## ADDENDUM 2026-09-13 — the delta redesign done; warm run pending a heap rebuild
Safe point: phi-system `f49007c2` (step 4 on the proof store, before the redesign).
Then, ruled and implemented (plan §36): an entry is `{delta = {added, deleted}, verdict}`;
a deletion removes every theorem of the context's list whose proposition is aconv to a
deleted statement (any guard's); the judge gets `guard_ctxt` (before the delta) and the
entry's delta, answers `Provable of delta`, which replaces the entry's delta; identity is
the proposition (`aconv`); `canonical_form` deleted.  Files: guard_cache.ML, reasoners.ML,
both test theories (three deletion probes added; Guard_Export_Smoke `fresh` fixed), plan §1/§5/
§7/§8/§10/§35/§36.  Verified under Isabelle-MCP: PLPR.thy, both test theories, the corpus cold
(355 decisions, 261 digests, all misses since old entries do not decode) — all clean.
The warm run passed after the author rebuilt the heap (146 Refuted + 5 Unknown hits, 20.6 s).
First code review (96 agents, `ai-artifacts/DELTA_REDESIGN_REVIEW_2026-09-13.md`):
ACCEPTED_ON_CONDITION.  The author ruled SEM-2 (a) — one collision rule, the delta's
budget wins, identity by `Pattern.equiv` (both sites; `update_lemma` gone) — and P3 status
quo.  Drafter fixes applied: SEM-1 (`map_times`, `machine_time` on the delta handed to
the judge), `apply_delta` returns the delta it applied, documentation residue (plan status,
§1, §3 pipeline collapsed to a pointer at §5), probes E4/T2/T3 + the one-rule replay probe
(T1 unobservable through the factory: G.simpcut applies the lemma from the pre-delta list —
noted in the test theory and §7).  Verified again: PLPR.thy, both test theories, the corpus
— clean.  A re-review workflow was launched; its report goes to
`ai-artifacts/DELTA_REDESIGN_REREVIEW_2026-09-13.md`.
Re-review (65 agents, `ai-artifacts/DELTA_REDESIGN_REREVIEW_2026-09-13.md`): ACCEPTED_ON_CONDITION,
no behavioural defect; the author ruled plain Pattern.equiv (no binder handling) and same_prop total
without a contract change; D1-D9 applied (keep alias, RR/equiv/delete-before-add probes, prose fixes);
everything clean again; the TEMPORARY declare reverted; committing.  P5 ruled: the two test theories'
stores are neither tracked nor ignored.
The collision alarm: ruled 2026-09-13 (§36 ruling 9) — `update_cached_proof`'s key record gains
`rewrites : bool`; the guard cache writes `rewrites = true` (neither checked nor marked); the marks
are dropped at Theory.at_begin as well as at_end; changed in auto_sledgehammer, Isa-Mini and
phi-system together, Phi_System_Base rebuilt by the author, everything clean.  Still open on the
alarm: whether it has any true positive left after the unified key mint (if not, delete), its
never-approved wording, and its lack of tests.
PENDING: (4) the
word "battery" was the drafter's coinage; scrubbed from the test theories and the plan on the author's nod; (5) revert the TEMPORARY declare in PLPR.thy, commit, bump.
The items B1–B10 below remain open except B1 (the author: acceptable, ignore) and B2's
canonical form (withdrawn by this redesign).

## ADDENDUM 2026-09-12 late — where to resume after compaction
Everything below is UNDECIDED; do nothing on any of it before the author rules.  The author
asked to compact and then go through the items ONE BY ONE ("先 compact 然后逐一审议这些问题").
Full texts: `ai-artifacts/STEP4_REDO_REVIEW_2026-09-12.md` (the code review: judge's report +
every concern) and `ai-artifacts/PROVENANCE_AUDITS_2026-09-12.md` (four audits).

State of the tree: phi-system UNCOMMITTED (step-4 redo on the author's design; comments
cleaned; PLPR.thy still carries the TEMPORARY test-driver declare — revert before commit; the
warm corpus run passed: 146 Refuted + 5 Unknown hits read from the tracked *.proof-store files,
~21 s); auto_sledgehammer at 5ac4877 (functor reverted); root not yet bumped.  Untracked new
stores: Test/Guard_Decision_Smoke.proof-store, Test/Guard_Export_Smoke.proof-store,
Phi_System/Resource_Template.proof-store, Phi_Semantics/PhiSem_Real_Abst.proof-store (the last
is another agent's).

A. Code review (accepted on condition).  MUST_DISCUSS: (1) the proof store's collision alarm —
options (a) an explicit bit on update_cached_proof [judge recommends; name it "this id is derived
from the goal", a fact, not a permission], (b) PLPRGUARD-prefix exemption, (c) delete [the judge
argues against: hash = NONE records have no by-hash fallback], (d) keep+reword; (2) which new
*.proof-store files to git add [judge: the two real theories', not the two test theories'; no
.gitignore change].  DRAFTER_MAY_DECIDE (held until the author says go): plan §7:1146-1148 and
§3:811 and §17.6:1796 still carry the pre-09-11 digest ("2. 不掺" must leave the corrected
sentence); Test/Guard_Export_Smoke.thy :24 comment and :65/:112 bare serial() → reuse the
test theory's run_tag+serial, then evaluate twice in two processes; the summary said one new store
file, it is three; §8 one sentence (phase 2 makes one call rewrite a key twice); conditional:
escape the id/head in collision_message if the alarm stays and guard entries are not exempt.
Rejected (7, with rebuttals in the file): digest-vs-text alarm; content-key accumulation;
Hasher.hex; FNV soundness note; single end-of-call write; Unknown freezes R-nitpick; cpu_bounded_seq.

B. Provenance audit — items to go through one by one (the author's order; suggested first: B1):
B1 Isa-Mini 4e42984 automatic DROP TABLE of the L1 proof cache (plan forbade it; live at
   proof_store.py:43,:55).  B2 guard cache: canonical form reshaped by three review rounds
   ("No author ruling was needed"); guard_decision record fields; loud-warning text; dropped-lemma
   warning ungated; \<phi>log_guess_inst option name.  B3 proof store: ruling O widened
   (1b05b2b); goal-hash change (0146687); "Find proof" trace (c88ad1d).  B4 phi-system 752be368
   derived-obligation keys (two audits disagree: one found "好的，赞同，请修复" 2026-08-29 13:30, one
   found nothing); d4cbde68 bool comparisons in generated C; 08-09 failure text.  B5 Isa-Mini
   2324fc5 DeepSeek price table; 402a2e1 cost line "author-finalized" claim.  B6
   Performant_Isabelle_ML 2cf1b52 Event_Log default dir (author ruled $ISABELLE_HOME_USER/log/phi)
   and the XML boundary transform.  B7 Semantic_Embedding 6cac576 D19 (false "user decision"
   claim).  B8 Isabelle_RPC 8b7325e pretty_unicode escape regression, never fixed.  B9 jEdit
   slice: 95d8f799/f27f25c9 store records committed without asking; phi_field_font W3;
   font name-table "decision 13"; primary-selection memo.  B10 plan-provenance errors in
   GUARD_CACHE_QUICK_MODE_PLAN.md (A1 "2. 不掺" re-glossed; A2 key citation; A4 judge re-entry
   reversed by the drafter; A9 unmarked judge-contract clauses; A10 "Nothing is pending").
   Unverified (audit's own list): Semantic_Embedding 710594e, twin-implementation gate, lock
   file; 3102b9d; ae1dd806 D7; 87cc212d; fbb528fe "/" separator ruling not found.

C. Feedback drafts filed today (5): digest scope; separate store file; comment style; the
collision detector implemented on review-agent spec; (earlier) narrowing under author citations.
