# Resume handoff — `\<check> \<premise> \<consistency>`: stage 1 starts here (2026-09-23)

Written for the session that resumes after the author's context
compaction.  The plan is `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md`
(rev 6): read it whole before touching anything; §5 is the stage list, §6
the verification, §2 the rulings verbatim, §9 what is still open.  This
file is the state of the world and the rules; it does not restate the
design.

## 1. Where things stand

- phi-system master `56f1f569` + the rev 6 commit that follows this file
  (root `main` bumped alongside; NOTHING pushed).  Stage P (the two word
  symbols `\<check>` = `0x00E087`, `\<consistency>` = `0x00E088`) is done and
  committed at `be16be02`; the author still has to look at the two glyphs
  in his own jEdit after restarting it (not our step).
- No ML has been changed.  The ML files this plan touches are byte-identical
  to `1f3c2142`, whose line numbers the plan cites (verified by all three
  reviews; re-verify with `git diff --stat 1f3c2142 HEAD -- Phi_Logic_Programming_Reasoner Phi_BI`
  before relying on a line number).
- The plan has been reviewed three times (§10 of the plan; the reports are
  `..._REVIEW_2026-09-22.md`, `..._REREVIEW_2026-09-22.md`,
  `..._THIRD_READ_2026-09-22.md`, all committed).  Every condition is ruled
  or applied.  Two names are answered and await the author's word (§2 below).
- The author said (2026-09-23): "之后在 compact 后再开工，请准备，请确保你的计划
  足够详细，请再次通读确保自洽".  So: after compaction, stage 1 begins — but
  first settle §2 below with the author, and ask for the explicit go
  ("阶段 1 开工") before the first edit, because the author has twice this
  week objected to work proceeding on an unanswered question.

## 2. Open with the author before typing them

1. `guard_kind_of` — the author asked "是做什么的？".  Answer given: it is
   the function that recognises the check from the goal state at
   `guard_condition_judge`'s entrance — it reads the leading antecedent (the
   guard as written, before `oblg_template`'s rewrite), strips its `\<And>`/`\<Longrightarrow>`
   prefix with `Logic.strip_assums_concl`, and answers
   `Check_Premise_Consistency` iff the conclusion is `False` under the
   premise tag (or bare); `Normal` otherwise.  It is the only place the check
   is recognised; `guard_digest_of` uses it too (plan §1, §4.2).
2. `string_of_guard_kind` — the author asked "为什么你需要".  Answer given:
   the `guard_decision` record's attributes are strings, the kind is rendered
   at two sites (the record's `kind` attribute — approved — and the trace
   line), and `verdict`/`hit` already go through the one `string_of_verdict`
   for the same two sites; one function keeps the two renderings from
   drifting (plan §4.7; the second review's F15).
   If the author prefers another name for either, use his; if he objects to
   the function, render the token inline at both sites and say so in §4.7.

Approved on 2026-09-23 (ruling 21): `guard_digest_of`, `concl_is_false`,
the abbreviation constant `Check_Premise_Consistency` followed by
`hide_const (open) Check_Premise_Consistency`, the record attribute `kind`.
Delegated to the drafter (ruling 20, "计划文本只要不违背我的设计可以你自行书写"):
the plan's text; the type name `guard_kind` ("名字你随意起"); the token and
trace suffix; the new `\<^descr>` wording; retiring `Guard_False_Probe.thy`.

## 3. The author's standing rules (binding; the ones that bit this week first)

- Never `isabelle build` (any session, any flags), never launch Isabelle
  except through the Isabelle-MCP tools or `repl_server.sh`.  After a `.ML`
  edit, re-evaluate under Isabelle-MCP session `Phi_System_Base` (that heap
  holds only the external dependencies; phi-system's own theories load from
  source, so an edited `.ML` is picked up).  If `isabelle_launch` reports the
  heap outdated, STOP and ask — a rebuild needs the author's explicit word
  (last time: "你可以自己 build 批准", one rebuild, ~55 s).
- Restart the Isabelle-MCP session FIRST: a running Isabelle read
  `symbols-words` at startup and `PLPR.thy` is about to use `\<check>` and
  `\<consistency>` (plan §5 stage 1, first sentence).
- Never git stash / checkout / reset --hard / clean.  Commit on phi-system
  `master` and root `main`; root needs `git add -f contrib/phi-system`
  (`/contrib` is gitignored).  Push nothing.  Other agents' uncommitted
  `.proof-store`/`.C`/`.o` files may be in the tree: leave them.
- Do not change code before the author agrees; do not proceed past a
  question he has not answered; report departures from his rulings.
- Plan documents are edited by hand (Edit tool), never by scripts.
- Subagents: Opus.  Reviews: the adversarial workflow (interrogators → a
  curator → ONE fresh defender per finding → a judge; English; Opus at
  xhigh; read-only; no Isabelle), the report to the author in Chinese.
- One word per concept, never coin: the plan's §1 glossary and the guard
  plan's §1 are authoritative.  Say "premises", never "hypotheses".  Fixed
  terms: guard, entry, delta, the judge, the factory, the solving function,
  P-auto, R-conv, R-nitpick, `guard_simp_tac`, `p_auto_attempt`, the check,
  the template's rewrite, `guard_kind`, the three steps, the strict rail /
  the unknown-tolerant rail, the digest marker, the undecided-check warning,
  the refutation by the simplifier.
- Chinese to the author, essence first, plainly, neither terse nor a wall;
  quote him verbatim; mark the drafter's narrowings [drafter].
- Monitor long runs at most every 10 minutes.  Temp files in
  `ai-artifacts/` (or the job's tmp dir), never `/tmp`.
- Memory writes need explicit approval (declined this week); no CLAUDE.md
  edits; no PRs.

## 4. Stage 1, step by step (plan §5; the anchors are `1f3c2142`'s)

0. Restart Isabelle-MCP; `isabelle_launch` session `Phi_System_Base`.
1. `Phi_Logic_Programming_Reasoner/library/phi_nitpick.ML` — COMMENTS
   ONLY (ruling 19): the patch header :14-22 and the PHI-PATCH block
   :519-526, as plan §5 stage 1 item 0 says; no distribution line, not the
   `fun_box` paragraph :24-28, no pinned parameter values.
2. `library/guard_refute.ML` — `datatype guard_kind = Normal | Check_Premise_Consistency`
   in the signature (:14-34; it already carries a datatype spec at :19) and
   the structure; `preprocess kind ...` (:176-200: under `Normal` split and
   slice as today, :196-199; under `Check_Premise_Consistency` return
   `([], residue)`); `nitpick kind ...` (:216-230: pass `(kind = Normal)`
   for `trust_assms` at :226, and `[] prems concl` as today); the three
   comments per plan §5 item 1 (the pipeline comment :168-174; the comment
   above `nitpick` :202-205 REWRITTEN for both cases; what keeping every
   premise buys — content, not certification).  The tree does not compile
   until step 3 (reasoners.ML:1320 calls `nitpick`); expected.
3. `library/reasoners.ML` — in the signature (:1-198) and the structure:
   `datatype guard_kind = datatype Phi_Guard_Refute.guard_kind`;
   `concl_is_false` on a subgoal (strip inside), `quick_cut` over it
   (:975-978); `guard_simp_tac` (:1074-1085) without the `THEN_ALL_NEW
   quick_cut`, keeping `Seq.take 1`, the 60 s bound and the timeout handler,
   its comment (:1062-1073) rewritten (one state; the cap; the timeout
   path's surviving reason; a pointer at plan §4.3 a); `guard_kind_of`,
   `guard_digest kind` (:1633-1635, the marker), `guard_digest_of`,
   `guard_condition_judge` (:1637) per plan §4.2; `prove_or_refute kind`
   (:1433): step 1½ per plan §4.3 a (the sketch is there verbatim), the
   judge path (:1511-1516) total with the `Normal`-only error, R-conv under
   `Normal` only (:1548), `r_nitpick kind` (~:1283-1310, passing it to
   `Phi_Guard_Refute.nitpick` at :1320), the warning function taking the
   kind (:1371-1378; text in plan §4.6, approved), `string_of_guard_kind`
   beside `string_of_verdict` (:1365-1367), the record attribute `kind`
   (:1358-1364 and the body copy :1355-1357) and the trace suffix
   (:1581-1587); the comments listed in plan §5 item 2 (signature block
   :88, :98-102, :103, :112-117, :122-123, :193-196; body :1169-1172,
   :1430-1432, :1596-1600).  `p_auto_attempt`, `p_auto_solving`,
   `guard_condition_solver'`, the factory and its front `quick_cut 1 th`
   (:1617) stay as they are.
4. `PLPR.thy` — after `Simp_Premise` (:204-205): the abbreviation with the
   RAW right-hand side `Premise MODE_GUARD False`, then
   `hide_const (open) Check_Premise_Consistency` (precedent :3279); the two
   `\<^descr>` paragraphs in :210-226 exactly as plan §4.8 words them
   (approved).  No ML in PLPR.thy changes.
5. `Test/Guard_Decision_Smoke.thy` — the probes of plan §6 item 2 in a new
   section "The check" after "The judge"; `digest_of` (:74-79) passes
   `Phi_Reasoners.guard_digest_of st`; the header (:14-20) gains the second
   exception; the comment at :685-686 loses "which quick_cut drops"; the
   method probes of §6 item 6 (bare `False`, Eisbach `fails` for the
   negative control).
6. Delete `ai-artifacts/Guard_False_Probe.thy` (ruling 20 covers it).
7. Re-evaluate after every `.ML` edit; the whole of §6 is stage 2.

Measurements stage 1 owes (plan §6 item 1): the display of
`\<condition> False` folds to the notation with the constant hidden;
`\<check> \<premise> \<consistency>` parses to `Premise MODE_GUARD False`.
Do NOT "verify that `trust_assms` affects nothing" — that claim was
retired (plan §4.3 c); record what the flag moves.

## 5. Stage 2 and 3 in brief

- Stage 2 = plan §6: PLPR.thy clean; the smoke theory clean twice; Phi_BI
  clean; the corpus leg (`Phi_Test.PhiTest_Arithmetic` + imports, the eight
  `Phi_Examples`) under a TEMPORARY `declare [[ML_debugger]]` in PLPR.thy,
  reverted; the harness is `ai-artifacts/step5/run_leg.py` and
  `ai-artifacts/step5/analyze.py` (the `kind` attribute counted with grep);
  floors and the reported numbers per §6 item 4; the out-of-run instance
  and the method per items 5-6.
- Stage 3 = the review (shape above), its conditions applied and
  re-verified; the documents (the guard plan's §1 entries, §5, §33 item 3,
  §39, status line; the guard cache handoff addendum with ruling 15's
  deferred item); commit phi-system master + root bump; nothing pushed.

## 6. Facts that cost time this week (do not rediscover them)

- Isabelle-MCP `isabelle_launch` fails when the heap is stale (another
  session rebuilding `Semantic_Embedding` made `Phi_System_Base` stale once);
  LSP `initialize` times out under high load (24 orphaned busy loops were
  the cause; the author had them killed).
- `Simplifier.asm_full_simp_tac` never yields an empty sequence for an
  in-range index; only `quick_cut` could empty `guard_simp_tac` (plan §4.3 a
  has the chain with Pure line numbers).
- `oblg_template` rewrites the premise tag's CONTENT with the run's full
  simpset before any solving function sees the state (reasoners.ML:386-387,
  PLPR_Syntax.ML:39-44) — that is why the kind is computed on `th0` at
  `guard_condition_judge`'s entrance and nowhere later.
- The refuter R-nitpick's `slice` drops EVERY premise when the conclusion
  has no free variables; today's verdict on `\<condition> False` is
  content-free.  With the premises as antecedents they ride the strict rail
  regardless of `trust_assms`; the flag then governs only Nitpick's own
  generated nondefinitional axioms (plan §4.3 c, the rule).
- `Phi_BI.thy` has eight LIVE uses of `\<condition> False` (four sum-type
  rules, two each); twelve more are in comments.  No `Phi_Examples` theory
  uses sums; `Phi_System`'s `Spec_Framework.thy`, `Phi_Types.thy`,
  `Phi_Type.thy` do and are in the corpus's import closure.
- `\<phi>trace_reasoning` defaults to 0 (reasoner.ML:316), so level-1
  warnings are silent unless raised; the smoke theory sets it to 3.
