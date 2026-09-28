# Resume handoff — replacing `\<condition>[\<safe>] P` by `\<condition> P` (2026-09-23)

Written for the session that resumes after the author's context compaction.
Nothing of this topic has been designed, planned or ruled yet: the author's
only words are the deferral of 2026-09-22 ("\<condition>[\<safe>] P 是另一个问题，
其实我有计划打算最后都换成 \<condition> P 的。不过这个我们之后再讨论吧。请记一笔",
ruling 15 of `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md`) and, on
2026-09-23 after the check was committed, "建议在 compact 后来看这个，请准备
compact".  So the first thing the resuming session does is ASK the author
what he wants — a plan, a survey first, or the replacement outright — and
what "换成" means for each use (below): nothing here is his design yet.

## 1. Where things stand (the state of the world)

- phi-system master `0110a6fa` (root `main` `681e7961`, NOTHING pushed): the
  check `\<check> \<premise> \<consistency>` implemented, verified, reviewed
  and committed (`ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md` rev 11,
  its §10; `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` rev 33).  The author
  checked the two new glyphs `\<check>` and `\<consistency>` in his jEdit:
  "通过".
- Uncommitted in the shared working tree, on purpose (ruling 24 of the check
  plan, "别管。不是问题。"): eight `.proof-store` files and `Bucket_Hash.C`
  that today's corpus legs rewrote (three live records lost from
  `Bucket_Hash`, `Matrix_Oprs`, `Phi_Types` stores; all still in HEAD), the
  stage-2 record `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_STAGE2_2026-09-23.md`,
  the gitignored patches, the display probe and the step5 event logs.  Leave
  them; never `git checkout`/`stash`/`reset --hard`/`clean`.
- The `Phi_System_Base` heap was rebuilt by the author at 14:10 (another
  session had changed `contrib/Isabelle_RPC/Tools/theory_hash.ML` and three
  Isa-REPL files); if `isabelle_launch` reports it outdated again, STOP and
  ask — a rebuild needs the author's explicit word.
- The check plan's §1 glossary and the guard plan's §1 are the vocabulary;
  "premises", never "hypotheses"; one word per concept.

## 2. What `\<condition>[\<safe>] P` is today (facts, all read from the tree)

- `PLPR.thy:192-193` declare the two modes: `MODE_SAFE :: mode ("\<safe>")`
  and `MODE_NO_INST_SAFE :: mode ("\<no>-\<inst>-\<safe>")`, both commented
  "simplification where only selected safe rules are applied".
- `PLPR.thy:2021-2025` register the two reasoners on `\<condition>[\<safe>] ?P`
  and `\<condition>[\<no>-\<inst>-\<safe>] ?P`: `Phi_Reasoners.wrap
  (Phi_Reasoners.safe_obligation_solver {can_inst = true | false})`.
  `\<condition> ?P` and `\<condition>[NO_INST] ?P` go to
  `guard_condition_judge` instead (the guard machinery: entry, delta,
  `guard_simp_tac`, P-auto, R-conv, R-nitpick, the judge; the check plan).
- `safe_obligation_solver` (`reasoners.ML:1750-1773` in the working tree):
  `oblg_template` with `{inj = I, on_thm = I}`, then `quick_cut 1`, the
  pre-tactic, the case split, the aux facts, and `clarsimp_tac` =
  `asm_full_simp_tac (add_guess_inst_solver ctxt) THEN_ALL_NEW clarify_tac
  (addSss ctxt)` in `ctxt addsimps Premise_def`, on `Phi_Safe_Simps.equip
  ctxt0`; first state only; NO store, NO refuter, NO judge: it proves or
  fails (the check plan's §4.4 "does not go through the factory").  Its
  `quick_cut 1` is the second caller of `quick_cut` (the first is the
  factory's front); the check plan's §8 (F11) and its review's R2 kept both.
- `PLPR.thy:247` declares `\<condition>[\<safe>] True` and the NO_INST_SAFE
  twin as simp facts beside the other tags; `:2052-2053` and `:2062-2063`
  give the `\<r>EIF`/`\<r>ESC` rules for both safe modes; `:2152` is
  `\<simplify>[\<safe>]`, a different construct (not a guard) that shares the
  word symbol.
- `library/PLPR_Syntax0.ML` mentions the safe mode once (grep it).
- `PLPR.thy:210-235`, the `\<^descr>` block, does NOT mention the safe variant
  (the check plan's §4.8, ruling 15 deferred it).

## 3. The uses to replace (18 lines in 5 files, the `.unicode.thy` twins excluded)

| file | lines | shape |
| --- | --- | --- |
| `Phi_Logic_Programming_Reasoner/PLPR.thy` | 8 | the declarations, registrations and rules of §2 above — infrastructure, not uses |
| `Phi_Semantics/PhiSem_Mem_C_Ag_NT.thy` | 131, 175, 209, 244, 271, 297, 322 | `\<Longrightarrow> \<condition>[\<safe>] s \|\<notin>\| field\<^sub>2` (a field-name not in a finite set) |
| `Phi_System/Phi_Type.thy` | 82, 102 | `\<guard> \<condition>[\<safe>] C` (a guard inside `\<guard>`); 4227: `\<condition>[\<safe>] (C\<^sub>R \<or> r = (\<lambda>_. unspec)) \<and> (C\<^sub>W \<or> w = (\<lambda>_. unspec))` |
| `Phi_Semantics/PhiSem_Aggregate_Named_Tuple.thy` | 440 | `\<Longrightarrow> \<condition>[\<safe>] s \|\<notin>\| fmdom tys` |
| `Phi_Logic_Programming_Reasoner/library/PLPR_Syntax0.ML` | 1 | the ML side of the syntax |

No use of `\<condition>[\<no>-\<inst>-\<safe>]` outside PLPR.thy was found.

## 4. Questions the resuming session must put to the author before any edit

1. Scope: replace the eleven uses only, or also retire the two modes, their
   registrations, rules and `safe_obligation_solver`?  (If the modes stay,
   nothing changes for anyone who still writes them; if they go, the
   `\<r>EIF`/`\<r>ESC` rules and `:247` go with them.)
2. Behaviour: the safe solver proves-or-fails with clarsimp and no store;
   `\<condition> P` decides through the guard machinery (entries in the
   theory's `.proof-store`, P-auto's 400 ms, the refuters, the judge, the
   undecided-guard warning at trace level 1).  Each replaced use therefore
   changes what happens when the condition is NOT provable: a refuted guard
   backtracks silently with a `Refuted` entry written; an undecided one warns.
   Ask whether that is intended for the field-name conditions of
   `PhiSem_Mem_C_Ag_NT` (probably decidable by simp either way) and for
   `Phi_Type.thy:4227`.
3. `can_inst`: `\<condition>[\<safe>]` runs with `can_inst = true`; so does
   `\<condition>`; `\<condition>[NO_INST]` is the no-instantiation form.  Confirm
   the plain form is wanted everywhere.
4. Verification: which corpus (the check plan's §6 item 4 corpus, run as a
   leg in a COPY of the tree — the check plan's R4, adopted as the rule for
   future legs — and with `AoA_driver = "test"`), and whether 0 flips against
   the committed stores is the floor.
5. Whether this deserves a plan of its own in `ai-artifacts/` with the
   adversarial review, or is small enough for a direct change plus one
   review round (the author decides; do not assume).

## 5. The standing rules (unchanged; the ones that bit this week first)

Never `isabelle build` (the author runs it); after any `.ML` edit re-evaluate
under Isabelle-MCP `Phi_System_Base` (restart the session first if
`symbols-words` or PLPR changed); never proceed past a question the author
has not answered ("这个问题我还没回答你怎么就继续了？？"); never change his
decisions on your own ("你为什么要擅自改变我的决策！"); documents and tests
are the drafter's to decide ("与文档与测试相关的可以你自主决定"), design and
user-visible text are his; plan documents by hand (Edit), never scripts;
one word per concept; Chinese to the author, essence first, then the full
context from scratch ("请先简要讲一下本质，再从头讲一遍，给我完整上下文");
reviews as workflows, Opus at xhigh (the model id `claude-opus-5-5` answered
today), interrogators → curator → one fresh defender per finding → judge;
commit on phi-system master and root main (`git add -f contrib/phi-system`)
only on his word; push nothing; memory writes need explicit approval.

## 6. Resolution (2026-09-28)

Rulings (author, 2026-09-28): keep the spelling; unify the safe guard onto
the guard machinery as the out-of-run instance ("保留 \<condition>[\<safe>]
但修改其 reasoner，统一到 condition guard judge 上，但以一种'快速模式'去做，例如
不走 LLM judge and the refuters 只走 the P-auto"); "1. 不用 store 2. 不告警";
the `\<^descr>` text approved after a reader test ("批准这个文案", "可以直说
it's weaker than \<condition>"); the two details of §4 Q1/Q3 "赞同"; the code
step "好，请继续"; `isabelle build` on cslh19 approved ("可以用 isabelle build",
"批准你在 cslh19 上调用此构建指令").

Done (uncommitted, awaiting the author's word): `reasoners.ML` —
`guard_condition_solver` (the out-of-run instance, state-shaped; the primed
forms built on it), `safe_obligation_solver` / `'` / `1` deleted;
`PLPR.thy` — the two registrations, the `\<^descr>` block, the mode
comments, the `case_split` comment; `Test/Guard_Decision_Smoke.thy` —
section "The out-of-run instance"; the guard plan §40 (rev 34) and the
check plan's ruling 15 closed.  Verified on cslh19 (three experiments,
guard plan §40): PLPR, the smoke session and Phi_Examples clean; then, on
the review's F1 ("赞同你的建议，请做"), `Phi_Test` and `Bucket_Hash` clean too.
The name `guard_condition_solver`: "挺好的".  The adversarial review
(2026-09-28, MET_ON_CONDITION) is `ai-artifacts/SAFE_GUARD_CODE_REVIEW_2026-09-28.md`.
Its conditions, applied the same day under the author's rulings (F1 "赞同你的
建议，请做", F4 "按你提议的来改", F5 "'不告警'指'guard 失败时不告警'", F6 "不大的
话你可以直接改"): the simpset-delta paragraph and the corrected build
mechanism in guard plan §40 (F1, F2); the smoke probes driven through the
registrations, the `SOMETRUE ?x` pair, the `PP (LOOP _)` probe, the
same-object context check (F3, F7); the per-antecedent `MODE_SAFE` comment
(F4); "no undecided-guard warning" in the comments (F5); the three
corrections of the `\<^descr>` block (F6); the in-run / out-of-run wording
(F8); the `Safe_Solver` comment (F9).  Verified on cslh19: PLPR, the smoke
session (plus a negative control on the registration), `Phi_Examples`,
`Phi_Test`, `Bucket_Hash` clean on the bytes of that time (guard plan
§40, run (5)).  The re-review
(`ai-artifacts/SAFE_GUARD_CODE_REREVIEW_2026-09-28.md`, MET_ON_CONDITION):
its residuals applied (the dropped-rules list corrected, the ground
no-inst probe, the status lines, the OUT OF A RUN box); F4's wording
option (a) and the deletion of the dead `solver_mode` argument (the F9
`Safe_Solver` comment went with the datatype): "赞同", applied.  Run (6)
then verified PLPR, the smoke session and the full leg on the bytes
offered for the commit: the databases record `reasoners.ML` `0558ce0f…`,
`PLPR.thy` `2de5dc5b…`, `Guard_Decision_Smoke.thy` `78ec8479…`.  The
final check (`ai-artifacts/SAFE_GUARD_CODE_FINAL_CHECK_2026-09-28.md`,
MET_ON_CONDITION): its document corrections applied; its one text question
(the MODE_SAFE parenthetical and the two simprocs `Phi_BI.thy:4809-4810`
adds to the `\<phi>safe_simp` simpset) ruled "保持原样就好"; the commit
approved: "批准提交".

cslh19 is left in the test state: the six modules on the `safe-guard-test`
branches at the committed pins; phi-system's working tree carries these
edits, the stores rewritten by three experiments (not a reference) and
`Guard_Decision_Smoke.proof-store`; `ai-artifacts/smoke_root/ROOT` (a
temporary session for the smoke theory, never committed) is on both
machines.  The eleven uses are as committed.
