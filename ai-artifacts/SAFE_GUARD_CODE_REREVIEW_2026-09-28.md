# Re-review — the applied conditions of the 2026-09-28 code review (`\<condition>[\<safe>] P` unified onto the out-of-run instance)

Workflow: one fresh verifier per condition F1–F9, then a judge; model claude-opus-5-5, xhigh, read-only.  First review: `ai-artifacts/SAFE_GUARD_CODE_REVIEW_2026-09-28.md`.

## The judge's report

# Re-review judge's ruling: `\<condition>[\<safe>] P` unified onto the out-of-run instance (phi-system, baseline 0110a6fa)

## Verdict: MET_ON_CONDITION

The code is sound and matches the brief. The brief's section 5 diff is byte-identical to `git diff` of the three source files; I compared the MD5 of both. I found no new code defect.

The hard condition of the first ruling (F2) is met. I ran a read-only sqlite query (mode=ro) on cslh19 myself, in `~/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux/log`:
- `Phi_Semantics_Framework.db` records `PLPR.thy` 8891d280fffb… and `reasoners.ML` 93764d6817….
- `Guard_Decision_Smoke_Run.db` records those two, plus `Guard_Decision_Smoke.thy` 685eb7ba1904….
- All three equal the local working tree's `sha1sum`.
- Every session has return code 0: Phi_Semantics_Framework, the smoke run, Phi_Examples, Phi_Test and Bucket_Hash_Run.
- The smoke run's database is the newest, so the negative control had been restored before it ran.

What remains is minor. Four items are document or test fixes the drafter makes, plus one two-word wording fix. One is a question on user-visible text for the author.

## Each condition

**F1, the simpset delta: partly met.**
- What is right:
  - The swap is described correctly: `Phi_Safe_Simps.equip ctxt0` before; now the run's simpset, plus `\<phi>guard_simp` (which has no declarations), plus the lemma list.
  - The argument for each family holds. LPR_ctrl_red_bool and cond_mapper_red are [simp], and SE_Has_or_Not_None is the only rule that makes C False.
  - Experiment (4) and the timing comparison are recorded.
- What is wrong: the list of `\<phi>safe_simp` rules "without [simp]" that "no longer reach" the guard names three families that ARE [simp]:
  - comb.K_app, K_comp and K_comp' (Phi_Aug.thy:18/22/27);
  - sublist_map_L_id/_R_id and their primed forms (Phi_Aug.thy:162-177), and list_upd_map_const_f (:73);
  - most of len_intvl.*: the datatype's sel, collapse and simps; plus_len_intvl and dom_of_add_len_intvl, which are [iff]; plus_len_intvl_start and plus_len_intvl_len, which are [simp].

  A reader could be led by this list to declare these rules [\<phi>guard_simp], which would strengthen every guard for no gain.
- The grep that option (a) asked for is not recorded.
- The conclusion of the paragraph is unaffected.

**F2, the build mechanism and digest evidence: met.**
- The mechanism is corrected (plan :4108-4122), and no trace of the old lesson is left.
- The gate and the heaps' fate are recorded.
- The digests are confirmed, as described above.
- Minor: :4120-4122 calls the run-(3)/(4) pair "the SHA1s of the working tree", which is no longer true. The smoke session's digest is not cited in section 40.

**F3, the smoke probes through the registrations: partly met.**
- What is right:
  - The probes go through `Phi_Reasoner.reason`.
  - `digest_of` uses the registered can_inst.
  - The SOMETRUE pair replaces the duplicate probe.
  - The negative control is recorded.
- What is missing:
  - Nothing shows that the `\<no>-\<inst>-\<safe>` registration is reached. Its only probe expects "not solved", and with no matching reasoner the engine also returns NONE silently (reasoner.ML:779, :851-854). So deleting the registration at PLPR.thy:2036-2037 still passes the section, although the section says it runs "through the two registrations".
  - Plan experiment (3) still gives "the no-inst twin solved" as coverage.

**F4, the per-antecedent mode comments: met as ruled.**
- The text is the judge's wording, verbatim, as the author approved.
- No other antecedent uses either mode.
- The 45-use count is correct.
- One clause of the approved wording is inaccurate (see the author item below).

**F5, "no undecided-guard warning": partly met.**
- What is right: the signature comment, the smoke header and section comment, and the loop-warning note in section 40.
- What is missing: the plan's rev-34 status line (:5-6) and section 40's defining sentence (:3997) still say "no warning", although the ruling named "plan status lines and section 40".

**F6, the three corrections of the `\<^descr>` block: met.** All three are true of the code:
- the warning prints only at trace level 1 or above;
- the store records refutations, undecided results and the lemmas a proof needed;
- the safe guard neither reads nor writes the store.

The lemma-list visibility is recorded in the signature comment and in section 40.

**F7, the smoke assertions: met.**
- The same-object check is a direct call with `pointer_eq`. This is correctly chosen, because a run would export and possibly rebuild the context it returns.
- The PP (LOOP _) probe reaches P-auto at trace level 3, so its warning assertion is meaningful.
- The header is reworded.

**F8, the in-run / out-of-run wording: partly met.**
- What is right: all the code comments and the listed places in the plan.
- What is wrong:
  - New in this fix: the OUT OF A RUN box now lists the safe reasoners as callers, but its body still sends failure to "the caller's error continuation" and says "all four sites raise error". For the safe reasoners a failure is a backtrack.
  - The glossary's factory entry still says "the in-run `\<condition>` reasoners" for the two that use the judge instance.

**F9, the Safe_Solver comment: met.** solver_mode itself is untouched, as ruled.

## Remaining

**For the author (one question).** The approved MODE_SAFE clause says "in \<simplify>[\<safe>], simplification by the \<phi>safe_simp rules only". But \<simplify>[\<safe>] runs the Phi_Safe_Simps simpset, which starts from HOL.List's whole simpset (simpset.ML:121-122). The words are the first judge's, not the drafter's. The options are:
- (a) Recommended: "in the \<phi>safe_simp simpset only (the simp rules of HOL.List plus the \<phi>safe_simp rules)".
- (b) Shorter: "in the \<phi>safe_simp simpset only". This is no longer false, but it does not say what the simpset contains.
- (c) Keep the approved text.

**For the drafter** (all plan edits are made by hand):
- F1: correct the list of dropped rules and record the grep.
- F3: add a ground `\<no>-\<inst>-\<safe>` probe expected solved, and rerun the smoke session within the existing cslh19 approval. Otherwise, reword the section comment and plan :4062. In either case, annotate experiment (3).
- F5: change "no warning" to "no undecided-guard warning" at plan :5-6 and :3997.
- F8: limit the failure clause of the OUT OF A RUN box to the command-level callers and add the backtrack for the safe reasoners. Name the two judge-instance reasoners in the glossary's factory entry.
- F2 (wording): "the working tree's SHA1s at that time"; optionally cite the smoke session's digest.

**Still standing from the first ruling (condition 5).** The commit stages an explicit pathspec: the three source files, the smoke theory and the plan documents. No `.proof-store` file and no `Phi_Examples/Bucket_Hash.C` enters it, and both kinds are modified in the working tree now. Experiment files in ai-artifacts stay uncommitted.

**Dismissed:**
- The "guard reasoners" wording at PLPR.thy:2024. It agrees with the amended glossary.
- The baseline anchor PLPR.thy:1773. Section 40 cites baseline anchors consistently, so this is nitpicking.

## Structured verdict

Acceptance: **MET_ON_CONDITION**

Verdict: MET_ON_CONDITION. The code is unchanged in substance and sound. The hard condition (F2) is met: I queried the cslh19 build databases read-only myself. Phi_Semantics_Framework.db and Guard_Decision_Smoke_Run.db record reasoners.ML 93764d68…, PLPR.thy 8891d280… and Guard_Decision_Smoke.thy 685eb7ba…, which are exactly the working tree's SHA1s. Every session in run (5) has return code 0, and the smoke run was the last build. The diff in brief section 5 is byte-identical to `git diff`. F6, F7 and F9 are fully met, and F2 is met apart from two words of wording. What remains is minor, and all of it is in documents or tests:
(1) F1: the plan's list of dropped \<phi>safe_simp-only rules names three families (comb.K_*, sublist_map_*, most of len_intvl.*) that are in fact [simp] and still reach the guard. The grep behind the "no product mapper for a \<circle> remainder" claim is not recorded.
(2) F3: nothing shows that the \<no>-\<inst>-\<safe> registration is reached. Its only probe expects "not solved", which an absent registration also gives. Experiment (3)'s "the no-inst twin solved" is not annotated.
(3) F5: the plan's rev-34 status line and section 40's defining sentence still say "no warning".
(4) F8: the OUT OF A RUN box of plan section 3 now lists the safe reasoners as callers, but its body still says failure goes to "the caller's error continuation"; for them it is a backtrack. The glossary's factory entry still uses "in-run" to pick out the two judge-instance reasoners.
(5) F4, one question for the author: the approved MODE_SAFE wording "simplification by the \<phi>safe_simp rules only" is not literally true. \<simplify>[\<safe>] runs the Phi_Safe_Simps simpset, which starts from HOL.List's whole simpset.
Commit condition 5 of the first ruling still stands: explicit pathspec, and no .proof-store or .C file.

### Per condition

- {
  "id": "F1",
  "ruling": "partly",
  "note": "Met:\n- The swap is stated correctly: the old solver used Phi_Safe_Simps.equip ctxt0; the new instance uses the run's simpset plus \\<phi>guard_simp, which has no declarations; and the lemma list is added.\n- The argument for each family holds. LPR_ctrl_red_bool is [simp, \\<phi>safe_simp] (PLPR.thy:1784 now, :1773 at 0110a6fa). SE_Has_or_Not_None is at Phi_Type.thy:2876, and cond_mapper_red [simp] at :68.\n- Experiment (4) and the timing comparison are recorded at plan :4046-4059.\n\nNot met:\n- The list of dropped rules at plan :4082-4086 is partly false.\n  - comb.K_app, K_comp and K_comp' are [simp] (Phi_BI/Phi_Aug.thy:18, :22, :27).\n  - sublist_map_L_id, sublist_map_L_id', sublist_map_R_id and sublist_map_R_id' are [simp] (Phi_Aug.thy:162-177), and so is list_upd_map_const_f (:73).\n  - Most of len_intvl.* are [simp] or [iff]: the datatype's sel, collapse, simps and size; plus_len_intvl and dom_of_add_len_intvl are [iff] (Len_Intvl.thy:76, :81); plus_len_intvl_start and plus_len_intvl_len are [simp] (:86, :90).\n  - I found no [simp del] for any of them.\n- Option (a) asked for the grep behind the claim that no rule yields a product mapper for a \\<circle> remainder. It is credited to the defender but not recorded.\n\nThe paragraph's conclusion is unaffected."
}
- {
  "id": "F2",
  "ruling": "met",
  "note": "The hard condition is verified independently. I ran a read-only sqlite query, in mode=ro, on cslh19 in ~/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux/log.\n- Phi_Semantics_Framework.db records PLPR.thy 8891d280fffb… and reasoners.ML 93764d6817…, with return code 0.\n- Guard_Decision_Smoke_Run.db records the same two files plus Guard_Decision_Smoke.thy 685eb7ba1904…, with return code 0.\n- `sha1sum` of the local working tree gives the same three values.\n- The smoke run's database is the newest, so the negative control was restored before it ran.\n- Phi_Examples, Phi_Test and Bucket_Hash_Run have return code 0.\n\nThe mechanism is corrected at plan :4108-4122, and no trace of the old lesson is left. The gate and the heaps' fate are recorded at :4051-4054.\n\nTwo minor points remain:\n- :4120-4122 calls 9ae22157…/f2e2e224… \"the SHA1s of the working tree\". That was true only at runs (3) and (4). The brief at :98-100 repeats it.\n- The smoke session's own digest is not recorded in section 40."
}
- {
  "id": "F3",
  "ruling": "partly",
  "note": "Met:\n- The probes go through Phi_Reasoner.reason NONE NONE on Thm.trivial of a schematic-mode proposition (Guard_Decision_Smoke.thy:796-802).\n- digest_of uses the can_inst that PLPR.thy registers (:814-816 against PLPR.thy:2034, :2037).\n- The duplicate probe is replaced by the SOMETRUE pair (:825-828).\n- The negative control is recorded at plan :4066-4068.\n\nNot met: nothing asserts that the \\<condition>[\\<no>-\\<inst>-\\<safe>] registration (PLPR.thy:2036-2037) is reached. Its only probe expects \"not solved\". If no reasoner matches, gen_reason gets [] from get_reasoners' and ends in NONE (reasoner.ML:779, :851-854), silently, with no entry, no record and no warning. So deleting that registration, or mistyping its pattern, still passes the section. Yet the section comment (:789-791) and plan :4062 say the probes run \"through the two registrations\". The first review's F10 dismissal relied on F3 for exactly this coverage.\n\nAlso not done: plan experiment (3) (:4041-4043) still gives \"the no-inst twin solved\" as coverage, with no note. The judge's fix step (4) asked for that phrase to be dropped or corrected."
}
- {
  "id": "F4",
  "ruling": "met",
  "note": "The wording at PLPR.thy:192-195 is the judge's recommended text, verbatim, as the author ruled (\"按你提议的来改\"). It is accurate for both \\<condition> uses. MODE_SAFE and MODE_NO_INST_SAFE are used only by \\<simplify>[\\<safe>], \\<condition>[\\<safe>] and \\<condition>[\\<no>-\\<inst>-\\<safe>] (plus cond_can_merge in PLPR_Syntax0.ML:42). The count of 45 uses of \\<simplify>[\\<safe>] in ten files is correct.\n\nOne clause of that wording is inaccurate, and it is my predecessor's text, not the drafter's. \"in \\<simplify>[\\<safe>], simplification by the \\<phi>safe_simp rules only\" does not match the registration: \\<simplify>[\\<safe>] runs Phi_Safe_Simps.equip (PLPR.thy:2164-2166), and that simpset starts from the whole global simpset of HOL.List (library/tools/simpset.ML:121-122). Since the author approved the text verbatim, this goes to the author (see must_discuss)."
}
- {
  "id": "F5",
  "ruling": "partly",
  "note": "Met:\n- reasoners.ML:121-127 reads \"no undecided-guard warning (guard_simp_tac's loop warning still applies)\". This is true: guard_simp_tac calls a bare `warning` on its 60 s timeout (:1107-1116), and p_auto_attempt runs it first (:1130-1131).\n- The smoke header at :12-13 and the section comment at :787-790 are changed.\n- The note in plan section 40 is at :4009-4012.\n\nNot met: the ruling listed \"plan status lines and section 40\", but two places still make the absolute claim:\n- plan :5-6, the rev 34 status line: \"no store, no refuter, no judge, no warning\";\n- plan :3997, section 40's defining sentence.\nThe brief's section 6 and the handoff say these places were changed."
}
- {
  "id": "F6",
  "ruling": "met",
  "note": "PLPR.thy:219-230 is checked against the code.\n\n(1) Trace-gated: undecided_guard_warning prints through warn_pretty … 1 (reasoners.ML:1422). warn_pretty prints only when the level is <= \\<phi>trace_reasoning (reasoner.ML:337-340), and the default is 0 (:317).\n\n(2) \"Refutations, undecided results and the lemmas a proof needed are recorded\" matches what prove_or_refute writes (keep Refuted, keep Unknown, and the judge's delta with Proved). The sentence does not claim that a first P-auto proof is written, and it is not (:1602-1603).\n\n(3) \"without reading or writing the proof store\": guard_condition_solver is the factory with K (K ()) over p_auto_solving, which touches no entry.\n\nThe lemma-list visibility is recorded in the signature comment (:124-125) and at plan :4013-4016."
}
- {
  "id": "F7",
  "ruling": "met",
  "note": "(a) The same-object check is a direct call of guard_condition_solver {can_inst = true} with pointer_eq (Guard_Decision_Smoke.thy:831-843). Calling it directly, rather than through a run, is correct: Phi_Reasoner.reason exports the state, and a check on the context a run returns would test the export rather than the instance.\n\n(b) The PP (LOOP _) probe (:822-824) reaches P-auto and fails there. The theory sets \\<phi>trace_reasoning = 3 (:40), so the warning assertion is meaningful. The judge-instance counterpart (:386-389) warns. The four-prefix assert_warnings loop is kept.\n\n(c) The header's reachability clause (:25-27) is reworded as ruled. BLIND_SPIN is kept.\n\nThe smoke session ran clean on 685eb7ba (I confirmed this on cslh19)."
}
- {
  "id": "F8",
  "ruling": "partly",
  "note": "Met:\n- The PLPR.thy registration comment (:2024-2026) names both functions.\n- reasoners.ML:107 says \"the judge instance\".\n- \"outside a run\" is removed at :1127.\n- The signature comment (:121-127) is amended.\n- In the plan: the section 3 caller list (:1061-1064), the wrap count (:1097-1100), the glossary guard entry (:235-240), the out-of-run instance clause (:448-452) and the \"挺好的\" ruling in section 40.\n\nNot met:\n- A new inaccuracy that this fix introduced: the OUT OF A RUN box now lists the safe reasoners as callers (:1061-1064), but its body (:1066-1073) still says \"not proved → Seq.empty → the caller's error continuation\" and \"all four sites raise `error` on failure\". For the safe reasoners, Seq.empty inside a run means a backtrack: the rule is skipped (PLPR.thy:228).\n- The glossary's factory entry (:441-444) still says guard_condition_judge is \"registered … by the in-run `\\<condition>` reasoners\". Four in-run reasoners now handle the \\<condition> family, and only two of them use the judge instance."
}
- {
  "id": "F9",
  "ruling": "met",
  "note": "reasoners.ML:272 reads `Safe_Solver (*the guard factory: every guard reasoner*)`. The only live Safe_Solver argument left is in the factory (:1699), which never runs clarsimp. solver_mode is untouched, as ruled: deleting it is open with the author and is not part of this change."
}

### Must be discussed with the author

- {
  "id": "F4-wording",
  "why": "This is user-visible text. The author approved the judge's MODE_SAFE wording verbatim, so only he can change it.\n\nThe clause \"in \\<simplify>[\\<safe>], simplification by the \\<phi>safe_simp rules only\" (PLPR.thy:192) is not literally true.\n- \\<simplify>[\\<safe>] is registered as PLPR_Simplifier over Phi_Safe_Simps.equip (PLPR.thy:2164-2166). That replaces the context's simpset with the Phi_Safe_Simps simpset.\n- That simpset starts from the whole global simpset of theory HOL.List (library/tools/simpset.ML:121-122). The rules declared [\\<phi>safe_simp] and two simprocs are added on top.\n- `thm \\<phi>safe_simp` lists only the declared rules.\n\nFailure scenario: a rule author runs `thm \\<phi>safe_simp` to see what \\<simplify>[\\<safe>] will rewrite. He concludes that a term with no [\\<phi>safe_simp] rule, such as `length [a, b]`, is left alone. In fact HOL's list [simp] rules rewrite it.\n\nThe error is in the first judge's own recommended text, so it is not the drafter's fault. It is minor.",
  "options": "(a) Recommended: \"in \\<simplify>[\\<safe>], simplification in the \\<phi>safe_simp simpset only (the simp rules of HOL.List plus the \\<phi>safe_simp rules)\".\n\n(b) Shorter: \"in \\<simplify>[\\<safe>], simplification in the \\<phi>safe_simp simpset only\". This is the plan's existing phrase at :4018. It is no longer false, but it does not tell the reader what the simpset contains.\n\n(c) Keep the approved text as it is, reading \"the \\<phi>safe_simp rules\" as \"the rules of the \\<phi>safe_simp simpset\".\n\nWhatever the author picks, the MODE_NO_INST_SAFE comment is unaffected."
}

### The drafter decides

- {
  "id": "F1-dropped-rules",
  "fix": "Edit plan section 40, paragraph \"The simpset delta\" (:4082-4086), by hand.\n\n1. Remove `comb.K_*` (:261) and `sublist_map_*` from the list of dropped rules. Also remove every len_intvl rule that is [simp] or [iff]. These rules are [simp] and still reach the guard through the run's simpset:\n   - K_app, K_comp and K_comp' at Phi_Aug.thy:18, :22, :27;\n   - sublist_map_L_id/_R_id and their primed forms at Phi_Aug.thy:162-177, and list_upd_map_const_f at :73;\n   - the datatype's sel, collapse and simps;\n   - plus_len_intvl and dom_of_add_len_intvl, which are [iff] (Len_Intvl.thy:76, :81);\n   - plus_len_intvl_start and plus_len_intvl_len, which are [simp] (:86, :90).\n\n2. For genuine \\<phi>safe_simp-only examples, use map_beta, map_pairewise_eq, map_unspec, map_unspec_eq and atLeastLessThan_singleton_alt, which are already listed. Optionally add:\n   - nested_case_prod and the prod.case_distrib instances (Phi_Preliminary.thy:285-293);\n   - Len_Intvl.set_def and shift_by_nat_nat_def / shift_by_nat_int_def (Phi_Algb_Pre.thy:52-54).\n   Check each one for a [simp] twin before listing it.\n\n3. Record the search behind \"no rule yields a product mapper for a \\<circle> remainder\": the exact grep command and the files it covered. Use /usr/bin/grep -rnI, because the default grep honours .gitignore.\n\nThis is text only and needs no rebuild. Leave the paragraph's advice about [\\<phi>guard_simp] as it is: it stays correct once the list is correct."
}
- {
  "id": "F3-no-inst-reachability",
  "fix": "In Guard_Decision_Smoke.thy, section \"The out-of-run instance\", add one ground probe:\n`check \"no-inst safe guard, provable: its registration is reached\" true (run no_inst_safe \\<^context> (\"\\<condition>[\\<no>-\\<inst>-\\<safe>] (CHAIN (\" ^ fresh () ^ \" # \" ^ intro_chain ^ \"))\"))`\nIt is expected solved, with no entry, no record and no warning. Experiment (3) measured that can_inst = false solves this ground body; measure it again through the registration rather than assuming it.\n\nRerun the smoke session on cslh19 within the author's existing build approval (\"批准你在 cslh19 上调用此构建指令\"). If the drafter is unsure whether that approval covers this rerun, ask the author first.\n\nIf the drafter decides not to add the probe, reword the section comment (:789-791) and plan :4062. They should say that the \\<no>-\\<inst>-\\<safe> probe shows only that this body is not solved under that spelling, and that it would also pass without the registration.\n\nEither way, annotate plan experiment (3) (:4041-4043) by hand: \"the no-inst twin solved\" was the first probe repeated with can_inst = false on a ground guard, and it was replaced in (5)."
}
- {
  "id": "F5-status-lines",
  "fix": "Edit Docs/GUARD_CACHE_QUICK_MODE_PLAN.md by hand (the project rule forbids scripted edits to plan documents):\n- at :5-6 (the rev 34 status line), change \"no warning\" to \"no undecided-guard warning\";\n- at :3997 (section 40, \"What changed\"), make the same change.\n\nThe loop-warning note at :4009-4012 stays. Then correct the brief's section 6 F5 line so that it names these places."
}
- {
  "id": "F8-out-of-run-box",
  "fix": "Edit the plan by hand.\n\n(1) In section 3's OUT OF A RUN box (:1066-1073), limit the failure clause \"not proved → Seq.empty → the caller's error continuation\" and the paragraph after it (the 35 ms gate, the 2000 ms budget, \"all four sites raise `error`\") to the command-level callers. Then add: for the two safe reasoners, not proved → Seq.empty → backtrack (the rule is skipped, PLPR.thy:228). The OBLIGATIONS box at :1086 already says this for its own case.\n\n(2) In the glossary's factory entry (:441-444), replace \"by the in-run `\\<condition>` reasoners\" with the names of the two reasoners, for example \"by the `\\<condition> ?P` and `\\<condition>[NO_INST] ?P` reasoners\".\n\nBoth edits are text only."
}
- {
  "id": "F2-wording",
  "fix": "By hand, at plan :4120-4122 (and the brief at :98-100), change \"the SHA1s of the working tree\" to \"the working tree's SHA1s at that time\". Add that run (5) recorded the final pair, 93764d68… and 8891d280… (see :4073-4074).\n\nOptionally, cite in (5) the smoke session's own digest, Guard_Decision_Smoke.thy 685eb7ba… in Guard_Decision_Smoke_Run.db. I confirmed on cslh19 that it matches the working tree. The first judge's F2 fix asked for this match to be recorded."
}

### Dismissed

- {
  "id": "F8-guard-reasoners-wording",
  "rebuttal": "The PLPR.thy:2024 comment says \"the four guard reasoners\" where the first judge's recommended text said \"the four reasoners below\". This is not a defect. The amended glossary guard entry (plan :235-240) counts the safe modes as guards, and the same phrase is used at PLPR.thy:1752 and reasoners.ML:272. Changing it would make the wording less consistent, not more."
}
- {
  "id": "F1-anchor-1773",
  "rebuttal": "The plan cites PLPR.thy:1773 for LPR_ctrl_red_bool; the rule is at :1784 in the working tree. :1773 is the line at baseline 0110a6fa, and section 40 cites baseline anchors consistently. The line is also not part of the text this re-review checks. Stale line anchors in a dated plan document are nitpicking, not a condition that is unmet."
}

## The verifiers' reports

### F1

```json
{
  "finding_id": "F1",
  "status": "partly",
  "evidence": "Checked against the working tree, with Isabelle2025-2 (the isabelle on PATH).\n\nWhat is right:\n- The swap is stated correctly (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:4076-4082). The old solver passed `Phi_Safe_Simps.equip ctxt0` into oblg_template (0110a6fa reasoners.ML:1772). Phi_Safe_Simps is the HOL.List simpset plus \\<phi>safe_simp (library/tools/simpset.ML, `structure Phi_Safe_Simps`), and `equip` is put_simpset (simpset.ML:78). The new factory passes ctxt0 to oblg_template, whose front rewrite is at reasoners.ML:407. p_auto_attempt runs in the guard context that enhance_for_guard builds, which adds \\<phi>guard_simp and the lemma list (reasoners.ML:1089-1090, :1130-1131, :1683-1699). \\<phi>guard_simp has only its binding (guard_cache.ML:144) and no declaration anywhere (checked with /usr/bin/grep -rnI).\n- These dropped rules are named correctly: they are [\\<phi>safe_simp] and not [simp]. prod.map_beta, map_pairewise_eq, map_unspec and map_unspec_eq are at Phi_BI/Phi_Preliminary.thy:522/526/531/536, and atLeastLessThan_singleton_alt is at Phi_System/Phi_Algb_Pre.thy:56.\n- The argument for each family of uses checks out:\n  - The field-name family has [simp] twins, each also listed as \\<phi>safe_simp (Phi_Preliminary.thy:338-353): fempty_iff and finsert_iff (FSet.thy:406, :487), fmdom_empty and fmdom_fmupd (Finite_Map.thy:239, :252), and symbol_digit_inject/_distinct/_neq_zero (Performant_Isabelle_ML/HOL/SSymb.thy:65/70/78).\n  - LPR_ctrl_red_bool is [simp, \\<phi>safe_simp]. The plan cites PLPR.thy:1773, which is the baseline line; in the working tree it is :1784. That follows the plan's convention of baseline anchors.\n  - SE_Has_or_Not_None (Phi_Type.thy:2876) is the only SE_Has_or_Not rule that gives C = False. The other rules are :2893 (True) and :2908 (passes C through).\n  - cond_mapper_red [simp] (Phi_Type.thy:68-70) rewrites `?\\<^sub>M False m f` to `(\\<lambda>_. unspec)`.\n  - The eleven uses are where the plan says: Phi_Type.thy:82/102/4227, PhiSem_Aggregate_Named_Tuple.thy:440, and seven in PhiSem_Mem_C_Ag_NT.thy.\n- Experiment (4) is recorded as run clean, in the plan at :4046-4054 and in the brief at section 3, item 4. Phi_Test/ROOT builds PhiTest_All and PhiTest_Arithmetic, PhiTest_All imports PhiTest_Mem_C, and ai-artifacts/bucket_root/ROOT wraps Bucket_Hash. The timing observation is at :4055-4059. I cannot verify the numbers from here.\n\nWhat is wrong: the paragraph (:4082-4086) says three more families are \\<phi>safe_simp rules without [simp] that \"no longer reach\" the safe guard. All three are [simp], so they still reach it through the run's simpset:\n- comb.K_* (Phi_Preliminary.thy:261): comb.K_app, K_comp and K_comp' are declared [simp] at Phi_BI/Phi_Aug.thy:18, :22 and :27.\n- sublist_map_* (Phi_Algb_Pre.thy:44): sublist_map_L_id, sublist_map_L_id', sublist_map_R_id and sublist_map_R_id' are [simp] at Phi_Aug.thy:162, :167, :172 and :177. list_upd_map_const_f, in the same list, is [simp] at Phi_Aug.thy:73.\n- len_intvl.* (Phi_Algb_Pre.thy:50-51):\n  - len_intvl.sel, .collapse, .pred_inject, .size and .simps are [simp] through the datatype package (Isabelle2025-2 src/Doc/Datatypes/Datatypes.thy:798, 804, 918, 3466, 1134; the datatype is declared at Phi_BI/Len_Intvl.thy:9).\n  - plus_len_intvl and dom_of_add_len_intvl are [iff] (Len_Intvl.thy:76, :81).\n  - plus_len_intvl_start and plus_len_intvl_len are [simp] (Len_Intvl.thy:86, :90).\n\nThis paragraph repeats the defender's list without checking it, although its heading says \"checked in the sources\".",
  "remaining": "1. Correct the list of dropped rules by hand at Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:4082-4086. Remove comb.K_*, sublist_map_* and len_intvl.*, because all of them are [simp] and still reach the guard. If more examples are wanted, these are genuinely \\<phi>safe_simp-only:\n   - nested_case_prod and the prod.case_distrib instances (Phi_Preliminary.thy:285-293);\n   - Len_Intvl.set_def, shift_by_nat_nat_def and shift_by_nat_int_def (Phi_Algb_Pre.thy:52-54);\n   - ExBI_split_prod and ExBI_subj_split_prod (Phi_BI.thy:1833, :1838).\n\n   As the paragraph stands, a reader who debugs a safe guard over `comb.K x y` or `sublist_map_L N id` would think these rules are gone. The paragraph's own advice would then lead that reader to propose declaring them [\\<phi>guard_simp]. That declaration strengthens every \\<condition> guard and gains nothing, because the rules are already in the run's simpset.\n\n2. A minor point: option (a) of the judge's ruling asked the paragraph to record the grep behind the claim that no rule yields a product mapper for a \\<circle> remainder. The paragraph cites the rule sites it found (IDE_CP_Reasoning2.thy:572-578, :1803, :1149-1165) and credits the defender, but it does not record the search itself.\n\nThe conclusion of the argument for each family is not affected by either point.",
  "new_issue": "",
  "needs_author": false
}
```

### F2

```json
{
  "finding_id": "F2",
  "status": "met",
  "evidence": "1. The mechanism is corrected in Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:4108-4122 (paragraph \"How a `reasoners.ML` edit reaches a leg\"). It says Phi_Logic_Programming_Reasoner and Phi_BI have no heap image, that their theories are compiled into Phi_Semantics_Framework, whose `isabelle_sources` table records reasoners.ML and PLPR.thy, and that an edit therefore invalidates that session and every session above it. I checked this against the sources:\n   - Phi_Semantics_Framework/ROOT: `= Phi_System_Base + sessions ... Phi_BI`.\n   - Phi_BI/ROOT: `sessions ... Phi_Logic_Programming_Reasoner`.\n   - Phi_System_Base/ROOT lists only foreign theories.\n   - The local build database (~/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux/log/Phi_Semantics_Framework.db, opened read-only) lists both files, plus 52 PLPR sources.\n   - cslh19 has no Phi_Logic_Programming_Reasoner or Phi_BI heap file, and Phi_Logic_Programming_Reasoner.db has an empty output_heap.\n2. The plan's new explanation is right: `isabelle build -n` prints its plan only with `-v`. In contrib/Isabelle2025-2/src/Pure/Build/build_process.scala:1196, \"Skipping X ...\" is echoed with `verbose = true`. In build.scala:302, \"Unfinished session(s)\" is printed only when `progress.verbose || !no_build`.\n3. No trace of the old lesson is left. Grepping the plan, the brief and the handoff for \"embed the reasoner\", \"does not invalidate\" and \"must move aside\" finds nothing. Brief :100-102 records the correction.\n4. The digest evidence matches. `sha1sum` of the working tree gives reasoners.ML 93764d68… and PLPR.thy 8891d280…, which are exactly the SHA1s the plan cites for run (5) at :4073-4074. I also queried the cslh19 databases read-only (python sqlite3, mode=ro):\n   - Phi_Semantics_Framework.db (15:35:02), Phi_Logic_Programming_Reasoner.db and Guard_Decision_Smoke_Run.db all record 93764d68… and 8891d280….\n   - Guard_Decision_Smoke_Run.db also records Guard_Decision_Smoke.thy 685eb7ba…, which equals the working tree.\n   - Every session in the run-(5) chain has return_code 0: PLPR, Phi_Semantics_Framework, Phi_System, Phi_Semantics, PhiStd, Phi_Examples, Phi_Test, Bucket_Hash_Run and the smoke run.\n   - The smoke run is the last build (15:46:45), so the PLPR.thy it compiled is the restored one, not the negative control. The sources were last edited at 15:31:55, before every one of these builds.\n5. The gate mechanism is recorded at plan :4051-4054: the `AOA_ALLOW_NONINTERACTIVE=yes` line in etc/settings is commented out for the build and restored by a trap. On cslh19, ~/.isabelle/Isabelle2025-2/etc/settings:13 is uncommented again, with mtime 15:46:46, one second after the last build. The gate itself reads `getenv \"AOA_ALLOW_NONINTERACTIVE\"` (Isa-Mini/Agent/agent_server.ML:573).\n6. The heaps' fate is recorded at plan :4054: the heaps moved aside in (3) were deleted. A find over ~ and /tmp on cslh19 turns up no leftover copies, and all five consumer heaps were rebuilt on 2026-09-28.\n7. Handoff §6 (:143-151) points to plan §40 for the corrected build mechanism and to run (5) for the digests.",
  "remaining": "Optional: plan §40 does not cite the smoke session's own digest (Guard_Decision_Smoke.thy 685eb7ba… in Guard_Decision_Smoke_Run.db), although the judge's fix asked for it to be recorded. I confirmed on cslh19 that it matches the working tree. Nothing else is missing.",
  "new_issue": "Minor stale claim. Plan :4120-4122, repeated in brief :98-100, calls reasoners.ML 9ae22157… and PLPR.thy f2e2e224… \"the SHA1s of the working tree\". The working tree now hashes to 93764d68… and 8891d280…; the older pair was the tree's hash at runs (3) and (4), before the F3-F9 edits. A reader who makes the check the paragraph itself prescribes will get a mismatch and may conclude the leg is void. Fix by saying \"the working tree's SHA1s at that time\" and pointing to run (5), which records the current matching pair at :4073-4074.",
  "needs_author": false
}
```

### F3

```json
{
  "finding_id": "F3",
  "status": "partly",
  "evidence": "Checked against the working tree, not the brief alone. Isabelle was not run, as the rules require.\n\n(1) The probes go through the registrations. Phi_Logic_Programming_Reasoner/Test/Guard_Decision_Smoke.thy:797-802: `run` reads the proposition in schematic mode, builds `Thm.trivial`, and calls `Phi_Reasoner.reason NONE NONE (ctxt, st)`. `solved` is `Thm.no_prems` of the result, with NONE counting as not solved. The call reaches the registered reasoner with the same (ctxt, st):\n- `\\<condition>[_]` is `Premise` (PLPR.thy:201) and is not deferable (library/syntax/pended_goals.ML:14-21), so `reason` really attacks the antecedent.\n- The engine hands the tactic (ctxt, th'), with th' = st when there is no beta/eta redex (reasoner.ML:846-854, :688).\n- PLPR.thy:2033-2037 are the only reasoners on these patterns.\n\n(2) The digest for the store and log checks uses the registered can_inst. :799 calls `digest_of can_inst`, and :814-816 set `safe = true` and `no_inst_safe = false`, matching PLPR.thy:2034 and :2037. `guard_digest` hashes the state after the template plus the context's assumptions (reasoners.ML:1720-1722). Since the engine passes the same ctxt and st, a registration pointed at `guard_condition_judge` would write or log under exactly this digest.\n\n(3) Each assertion is meaningful for the `\\<safe>` registration:\n- :818 (ground CHAIN, solved) and :825 (`CHAIN _ \\<and> SOMETRUE ?x`, solved) show that the registration is reached and instantiates.\n- Under a judge-instance registration, the record check at :803/:809 catches a first P-auto proof, which is logged even though no entry is written (compare :367-369). BLIND_SPIN (:820) would leave a Refuted entry. PP (LOOP) (:823) would leave an Unknown entry and the undecided-guard warning (compare :387-389).\n- The log check cannot pass vacuously: `log_file` raises when event logging is off (:47-48), and earlier sections already assert that records exist.\n\n(4) The duplicate probe is replaced by the SOMETRUE pair at :825-828. fix_level is 1 versus 2 (reasoners.ML:1684), and the judge-instance twin at :859-861 shows that this body reaches the solving function. The measured outcome and the negative control (the `\\<safe>` registration's can_inst flipped, failing on the instantiation probe) are recorded in Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:4060-4071, the brief (section 3, item 5) and the handoff (:143-149). The control validates itself: it failed on exactly the probe the flip should break.\n\n(5) The section comment at :787-794 is corrected and accurate.",
  "remaining": "(a) Nothing asserts that the `\\<no>-\\<inst>-\\<safe>` registration is reached. Its only probe (:827-828) expects \"not solved\". When no reasoner matches, `Phi_Reasoner.reason` also returns NONE (reasoner.ML:851-854 gives [] and the loop ends in NONE at :779), and in that case nothing is written, logged or warned. So deleting the registration at PLPR.thy:2036-2037, or mistyping its pattern, still passes the section. Yet the comment at :789-791 and plan §40 (5) at :4062 say the probes are driven through \"the two registrations\". The review itself noted that this section is that registration's only possible coverage. The pair does catch a swapped can_inst and a registration pointed at the judge instance, but not an absent one. Fix: add one ground probe, `\\<condition>[\\<no>-\\<inst>-\\<safe>] (CHAIN (fresh # intro_chain))` run with `no_inst_safe`, expected solved, with no entry, no record and no warning. Once driven through the engine, this probe no longer duplicates the `\\<safe>` one.\n\n(b) The judge's F3 fix included \"Correct section 40's coverage sentence\". Plan §40 experiment (3) (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:4041-4043) still lists \"the no-inst twin solved\" as evidence, with no note that it repeated the first probe (can_inst = false, called directly). Brief §6's F3 entry does not mention this. Experiment (5) at :4060-4068 carries the correct description, so the only fix needed is to annotate or reword (3).",
  "new_issue": "",
  "needs_author": false
}
```

### F4

```json
{
  "finding_id": "F4",
  "status": "partly",
  "evidence": "Checked the working tree against baseline 0110a6fa. The working-tree SHA1 of PLPR.thy is 8891d280, the hash that verification record (5) says was built.\n\n(1) The text is the judge's wording, word for word:\n- PLPR.thy:192-194, MODE_SAFE: \"in \\<simplify>[\\<safe>], simplification by the \\<phi>safe_simp rules only; in \\<condition>[\\<safe>], a guard decided only by the simplifier and a short automatic search (see the text on \\<condition>[\\<safe>] P below)\".\n- PLPR.thy:195, MODE_NO_INST_SAFE: \"as MODE_SAFE in \\<condition>[\\<safe>], prohibiting instantiation\".\n- Both are identical to the F4 \"options\" text in the review record. They replace the baseline comment, \"simplification where only selected safe rules are applied.\" (0110a6fa PLPR.thy:192-193).\n\n(2) Only two antecedents use the modes:\n- MODE_SAFE / MODE_NO_INST_SAFE appear only at PLPR.thy:192, :195 and PLPR_Syntax0.ML:42. That last one is cond_can_merge for Premise MODE_SAFE, which is still the \\<condition>[\\<safe>] use.\n- Once \\<simplify>[\\<safe>], \\<condition>[\\<safe>] and \\<condition>[\\<no>-\\<inst>-\\<safe>] are stripped out, grep finds no other \\<safe> except the syntax line PLPR.thy:19 and a smoke comment.\n- There is no \\<simplify>[\\<no>-\\<inst>-\\<safe>], so the MODE_NO_INST_SAFE comment is complete.\n\n(3) \\<simplify>[\\<safe>] has 45 uses in ten files outside PLPR.thy, counted with /usr/bin/grep -rnoI, excluding the untracked, gitignored *.unicode.thy and ai-artifacts:\n- IDE_CP_Reasoning2.thy 9, Phi_Type.thy 11, Phi_Algb_Pre.thy 7, Phi_BI.thy 5, CoP_simp.ML 3, PhiStd_Loop.thy 3, PhiStd_Loop_a.thy 3, Phi_Types.thy 2, PhiSem_Mem_C_Ag_Ar.thy 1, PhiSem_Mem_C_Ag_NT.thy 1.\n- Plan :4016-4019 says \"45 uses in ten files\", which matches. The judge's 46 also counts the registration.\n- The registration is PLPR.thy:2164-2166: PLPR_Simplifier.simplifier (K Seq.empty) Phi_Safe_Simps.equip. Per simplifier.ML:101-106 and simpset.ML:77 (equip = put_simpset (get' ctxt)), it replaces the context's simpset with Phi_Safe_Simps.\n\n(4) The \\<condition>[\\<safe>] clause is true:\n- PLPR.thy:2033/:2036 register guard_condition_solver {can_inst=true/false}.\n- reasoners.ML:1739-1740 is the factory over p_auto_solving (:1737), which is p_auto_attempt = guard_simp_tac THEN P-auto under guard_classic_prover_bound (:1130-1131).\n- The pointer to the \\<^descr> text is right: it is at PLPR.thy:226-230, and :2036 carries can_inst=false for the no-inst mode.\n\n(5) The \\<simplify>[\\<safe>] clause is true only under one reading:\n- Phi_Safe_Simps starts from the whole global simpset of HOL.List: simpset.ML:121-122, initial_ss = Give_SS (simpset_of (init_global HOL.List)).\n- The [\\<phi>safe_simp] declarations and two simprocs (Phi_BI.thy:4809-4810) are added on top of that. The named fact \\<phi>safe_simp (simpset.ML:94-96, :110-111) holds only the declared rules.\n- The change's own plan uses \"the \\<phi>safe_simp rules\" to mean the declared rules. At :4082 it writes \"the `\\<phi>safe_simp` rules without `[simp]`\". At :4078-4079 it writes \"Phi_Safe_Simps.equip ctxt0 (the `HOL.List` simpset plus `\\<phi>safe_simp`)\". The judge's F1 text says the same.\n- So \"by the \\<phi>safe_simp rules only\" leaves out the HOL.List simpset that \\<simplify>[\\<safe>] actually rewrites with. The comment is true only if \"\\<phi>safe_simp rules\" means the whole \\<phi>safe_simp simpset, which is the plan's phrase at :4018.\n- The baseline's vaguer \"only selected safe rules\" did not have this problem.",
  "remaining": "One clause is not literally true. PLPR.thy:192 says \"in \\<simplify>[\\<safe>], simplification by the \\<phi>safe_simp rules only\". In the change's own vocabulary (plan :4078-4082), that means only the rules declared [\\<phi>safe_simp].\n\nWhat \\<simplify>[\\<safe>] actually does (PLPR.thy:2164-2166, Phi_Safe_Simps.equip) is simplify in the Phi_Safe_Simps simpset. That simpset starts from the whole HOL.List global simpset (simpset.ML:121-122) and adds the declared rules and two simprocs (Phi_BI.thy:4809-4810).\n\nFailure scenario: a user reads the comment, runs `thm \\<phi>safe_simp` to see which rules \\<simplify>[\\<safe>] will use, and so expects that a term with no [\\<phi>safe_simp] rule for it (for example a `length` of a list literal) stays unchanged. In fact HOL's standard [simp] rules for lists rewrite it.\n\nA minimal fix, using the plan's existing phrase at :4018: \"simplification in the \\<phi>safe_simp simpset only\". The author approved the judge's wording verbatim, so any change to this user-visible sentence needs his word.\n\nEverything else in the condition is met:\n- the MODE_SAFE comment's \\<condition>[\\<safe>] clause and the MODE_NO_INST_SAFE comment are the judge's wording and are true;\n- no third antecedent uses either mode;\n- the 45-use count is correct.",
  "new_issue": "",
  "needs_author": true
}
```

### F5

```json
{
  "finding_id": "F5",
  "status": "partly",
  "evidence": "I checked each place against the working tree, the judge's F5 ruling in ai-artifacts/SAFE_GUARD_CODE_REVIEW_2026-09-28.md, and the defense's fix plan for F5 (item 4 there names \"status lines 5-6 and section 40\").\n\nMet:\n- reasoners.ML:121-127. The signature comment now reads \"no store read or written, no refuter, no judge, no undecided-guard warning (guard_simp_tac's loop warning still applies)\". That is true of the code: guard_simp_tac at :1107-1116 calls a bare `warning` on its 60 s timeout, and p_auto_attempt at :1127-1128 runs guard_simp_tac first.\n- Guard_Decision_Smoke.thy:12-13. The header reads \"reads and writes no entry and raises no undecided-guard warning\".\n- Guard_Decision_Smoke.thy:787-790. The section comment reads \"no judge, no undecided-guard warning, the context returned unchanged\".\n- PLPR.thy:192-195. The MODE_SAFE / MODE_NO_INST_SAFE comments use the F4 per-antecedent wording and make no warning claim.\n- PLPR.thy:228. The \\<^descr> sentence \"the rule is skipped without warning\" is unchanged, which the ruling allows.\n- The replacement text uses the glossary term \"the undecided-guard warning\" (plan :935) and coins no new word.\n- Plan section 40, :4009-4012, adds the required note: \"`guard_simp_tac`'s loop warning, unconditional on its 60 s bound, still applies — '不告警' is 'no warning when the guard fails', i.e. no undecided-guard warning\".\n\nNot met:\n- Plan :3995-3998 (section 40, \"What changed\"). The defining sentence still says \"under the same bounds as the judge instance — no store, no refuter, no judge, no warning, the context returned unchanged\". The absolute claim was left in place and only qualified twelve lines later. It was not replaced as the ruling requires.\n- Plan :4-6 (the rev 34 status line). It still says \"registered to `guard_condition_solver` — no store, no refuter, no judge, no warning — pending the commit\", with no qualification anywhere near it. The judge's F5 ruling lists \"plan status lines and section 40\", but these lines were not touched.\n- The review brief (section 6, F5) and the handoff §6 (:146) both say the replacement was done in plan section 40. That is only half true.",
  "remaining": "Two edits remain, both in Docs/GUARD_CACHE_QUICK_MODE_PLAN.md and both to be made by hand (the project rule forbids scripted edits to plan documents):\n(1) At :5-6, in the status line, replace \"no warning\" with \"no undecided-guard warning\".\n(2) At :3997, in section 40's \"What changed\" sentence, replace \"no warning\" with \"no undecided-guard warning\".\nThe existing loop-warning note at :4009-4012 can stay as it is.",
  "new_issue": "",
  "needs_author": false
}
```

### F6

```json
{
  "finding_id": "F6",
  "status": "met",
  "evidence": "I checked all three corrections against the working-tree source, not against the brief.\n\n(1) The warning is now said to depend on the trace level. PLPR.thy:221-223 says \"an undecided guard is reported as a warning when \\<phi>trace_reasoning is at least 1\". This is true:\n- The only call of undecided_guard_warning is at reasoners.ML:1638, and it fires only on an Unknown verdict, including when an entry already said Unknown.\n- undecided_guard_warning (reasoners.ML:1412-1424) prints through `Phi_Reasoner.warn_pretty (Context.Proof ctxt) 1`.\n- warn_pretty (reasoner.ML:337-340) prints only when `level <= Config.get_generic ctxt trace`.\n- `trace` is \\<phi>trace_reasoning with default `(K 0)` (reasoner.ML:317).\n\n(2) The text no longer says \"the decision is cached\". PLPR.thy has no \"cache\" wording in the \\<^descr> block or in the mode comments (grep: only lines 565, 573, 1995 and 2006, none of them in the block). The replacement sentence (PLPR.thy:221-222), \"Refutations, undecided results and the lemmas a proof needed are recorded in the theory's proof store\", matches what prove_or_refute writes:\n- Refutations: refuted_by → `keep Refuted` (:1525-1527), covering the simplifier, R-conv and R-nitpick (:1621-1623, :1628), and the judge's Unprovable (:1582-1584).\n- Undecided results: `keep Unknown` in judge_or_give_up (:1591-1592).\n- The lemmas a proof needed: the judge's delta, written with Proved (:1578).\n- A first P-auto proof writes nothing (:1602-1603, `if entry_verdict = SOME Proved orelse is_none entry then ()`), and the sentence does not claim that it does.\n- The store is the theory's: write_entry/lookup_entry on `Proof_Context.theory_of ctxt0` (:1485-1490). \\<phi>guard_cache defaults to true (guard_cache.ML:73).\n\n(3) \"Without the cache\" is replaced. PLPR.thy:226-228 now says \"without reading or writing the proof store\". This is true:\n- The only store reads and writes in the tree are in prove_or_refute (:1487, :1490; grep over *.ML and *.thy).\n- guard_condition_solver (:1739-1740) is the factory with digest_of = `K (K ())` and p_auto_solving (:1737). The factory (:1683-1700) touches no entry.\n\nThe lemma-list visibility is recorded in both places the condition names:\n- Signature comment, reasoners.ML:121-127: \"the search sees the lemma list the context carries, like every guard-side prover\".\n- Plan section 40, Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:4013-4016: the instance sees the lemma list through enhance_for_guard, its completeness can vary with what earlier \\<condition> guards brought in, and it neither reads nor writes the store. The \"simpset delta\" paragraph of the same section records the difference from the retired solver.\n\nBoth statements match the code. enhance_for_guard = `Phi_Guard_Cache.enhance_with_lemmas o Phi_Guard_Cache.Guard_Simp_SS.enhance` (reasoners.ML:1089-1090), and both guard_simp_tac (:1108) and p_auto_tac (:1122) use it. guard_ctxt comes from ctxt0 through oblg_template's Variable.import_inst (:428-432), which keeps the Guard_Lemmas proof data (guard_cache.ML:150-153).\n\nI found no factual error in the new sentences as a rule author would read them.",
  "remaining": "",
  "new_issue": "",
  "needs_author": false
}
```

### F7

```json
{
  "finding_id": "F7",
  "status": "met",
  "evidence": "All three parts of F7 are in the working tree, and the smoke diff is byte-identical to the one in brief section 5. I compared `git diff` of Guard_Decision_Smoke.thy with the brief's copy and they are the same.\n\n(a) Context check. In Phi_Logic_Programming_Reasoner/Test/Guard_Decision_Smoke.thy:831-843, a new ML block calls `Phi_Reasoners.guard_condition_solver {can_inst = true} (ctxt, st)` directly on a provable `\\<condition>[\\<safe>] (CHAIN ...)`. It raises an error unless `pointer_eq (ctxt', ctxt)` holds, and also if the guard is not solved.\n- The check can catch the regression the judge named. In p_auto_solving (reasoners.ML:1737), the `ctxt` argument is guard_ctxt. The factory builds guard_ctxt freshly at reasoners.ML:1691-1692 (`add_guess_inst_solver ... addsimps ...`), so if `pair ctxt0` became `pair ctxt`, the returned context would be a different object and `pointer_eq` would fail.\n- Calling the instance directly, rather than checking inside `run`, is the right choice. Phi_Reasoner.reason (reasoner.ML:943-949) sends its result through `PLPR_Context_Export.export_state`. That returns the outer context when inner and outer are the same object, and otherwise a context rebuilt by the hooks (context_export.ML:54-58). A check on the context returned by a run would therefore either always pass or fail for reasons unrelated to the instance. The comment at :831-832 says exactly this.\n\n(b) The PP (LOOP _) probe, at :822-824. It is expected not solved, with no entry, no record and no warning, through `check` (:805-814). `check` keeps the four-prefix `assert_warnings` loop, as the ruling asked, and does not switch to `null warnings`. The probe really reaches P-auto and fails there:\n- PP and LOOP have no simp rule (:296-305), and the file declares nothing but two config options (:40-41). So nothing adds a simp rule.\n- The front rewrite in oblg_template (reasoners.ML:404-406) leaves the guard as it is. The guard is not True, so the TrueI exit does not fire.\n- fast_inst (reasoners.ML:345-379) returns NONE: with can_inst = true the last case applies, and the head of the guard is the constant PP, not a Var. There are no variables to fix, and LPR_inst always returns NONE.\n- quick_cut keeps the state because the conclusion is not False. The factory then calls p_auto_solving, which runs p_auto_attempt (reasoners.ML:1130-1131).\n- guard_simp_tac cannot rewrite the guard. The lemma list is empty, because every probe uses a fresh `\\<^context>` and the file never changes the theory context.\n- PP_I, `PP (LOOP (LOOP (LOOP (LOOP x))))`, does not unify with `PP (LOOP <numeral>)`: the constants LOOP and numeral clash. So P-auto finds no proof, and the result is not solved.\n- The judge instance's counterpart (:386-389: no entry, no judge, trace level 3) ends Unknown with the undecided-guard warning. So if the `\\<safe>` registration were routed back to the judge instance, all three assertions would fail.\n- BLIND_SPIN is kept, renamed to name P-auto's bound (:820-821).\n\n(c) Header. :25-27 now reads \"The probes of the out-of-run instance meet the same constraint with p_auto_solving in place of prove_or_refute, and assert that prove_or_refute is never reached.\" This is the judge's wording. It is true for all five probes. Neither CHAIN probe hits an exit: for `CHAIN ... \\<and> SOMETRUE ?x`, `mk_boolean_inst` raises Match on CHAIN, so fast_inst returns NONE (reasoners.ML:317-324, 365-368). Under `\\<no>-\\<inst>-\\<safe>`, ?x is fixed, so the guard still reaches p_auto_solving.\n\nVerification record: brief section 3, item (5), records the smoke session as clean on the final bytes. The recorded SHA1s of reasoners.ML (93764d68...) and PLPR.thy (8891d280...) match the working tree. The smoke theory's own SHA1 is not recorded, but its diff matches the brief's section 5 exactly.",
  "remaining": "",
  "new_issue": "",
  "needs_author": false
}
```

### F8

```json
{
  "finding_id": "F8",
  "status": "partly",
  "evidence": "Every item the judge listed is applied, checked against the working tree and not against the brief.\nCODE:\n(1) PLPR.thy:2024-2026 now reads \"the four guard reasoners take the state directly: guard_condition_judge returns the incoming context plus the guard's lemmas, which Phi_Reasoners.wrap would drop; guard_condition_solver returns it unchanged\". It names both functions, and \"in-run\" / \"out-of-run\" are gone. It says \"guard reasoners\" where the judge wrote \"reasoners below\". That fits the amended glossary, which now calls the safe modes guards (plan :235-240), and the same wording appears at PLPR.thy:1752 and reasoners.ML:272. It is not a defect.\n(2) reasoners.ML:107 now says \"the judge instance\".\n(3) reasoners.ML:1127 reads \"(*one whole attempt: ...\"; \"outside a run\" is removed.\n(4) The signature comment at reasoners.ML:121-127 says \"named after their first callers ... guard_condition_solver is also the reasoner of \\<condition>[\\<safe>] P and \\<condition>[\\<no>-\\<inst>-\\<safe>] P inside runs (PLPR.thy)\". It is merged with F5's \"no undecided-guard warning\" and with the lemma-list sentence.\nPLAN (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md):\n- Section 3's OUT OF A RUN header at :1057-1064 adds the two safe reasoners, with \"INSIDE runs, §40 — the same instance, the term kept\".\n- The wrap sentence at :1096-1100 now says \"the guard reasoners (two until 2026-09-28, four since, §40)\".\n- The glossary guard entry at :235-240 says the safe modes are discharged by guard_condition_solver and never by prove_or_refute, so the document's statements about a guard's decision do not apply to them.\n- The out-of-run instance clause at :447-452 now says \"the term names its first callers, and since then it is also the reasoner of ... inside runs\".\n- In section 40, the Rulings paragraph at :4021-4027 records the name with \"挺好的\". No \"pending the author's word\" is left: I grepped for \"pending\", and the only other hit in the status line (:6) is \"pending the commit\".\n- The PLPR.thy:247 anchor is left as it was, which is allowed because the judge dismissed the F8-sub point.\nGREP: I ran /usr/bin/grep for \"in-run\", \"out-of-run\", \"outside a run\", \"inside a run(s)\" and \"OUT OF A RUN\" over *.ML, *.thy and the plan.\n- In the code, the remaining hits are all the glossary term itself: reasoners.ML:147, :1128, :1736 and the smoke test headers. They are acceptable.\n- PLPR.unicode.thy:2010 still contains the old sentence, but that file is git-ignored (.gitignore:16), is a generated copy from Sep 9, and is not part of the change.\n- The plan has the two stale spots described under remaining.",
  "remaining": "Two sentences in the plan still describe the safe reasoners wrongly. Both are text only, no code changes, and no re-verification is needed.\n(a) Glossary, the factory entry, Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:441-447: \"guard_condition_judge = the factory applied to prove_or_refute ... registered on the state by the in-run `\\<condition>` reasoners as guard_condition_judge {can_inst = …} o snd\".\n- There are now four in-run reasoners of the \\<condition> family, and the glossary guard entry at :235 counts the safe modes as guards.\n- Only two of those four register guard_condition_judge.\n- The same entry says so itself a few lines later (:447-452: guard_condition_solver is the reasoner of the safe modes inside runs).\n- So \"in-run\" is still used as the label that separates the two groups, and that is false. Fix: name them, for example \"by the \\<condition> ?P and \\<condition>[NO_INST] ?P reasoners\".\n(b) See new_issue: the body of the OUT OF A RUN box was not qualified for the callers the box now lists.",
  "new_issue": "The fix added the two safe reasoners to the OUT OF A RUN box of plan section 3 (Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:1061-1064) but left the box's body unchanged. The body at :1066-1073 still says \"not proved → Seq.empty → the caller's error continuation\", and after that the 35 ms gate / 2000 ms budget narrowing and \"all four sites raise `error` on failure\".\nFor the safe reasoners that first statement is false. When guard_condition_solver returns Seq.empty inside a run, the PLPR run backtracks: the rule is skipped silently, as PLPR.thy:227 says (\"the rule is skipped without warning\"). No error continuation is involved.\nFailure scenario: a reader uses section 3 to work out what happens when a \\<condition>[\\<safe>] guard fails. The box they are sent to says failure goes to an error continuation, so they conclude a failing safe guard aborts with an error, when it only skips the rule.\nFix: scope the body's failure clause and the narrowing paragraph to the command-level callers, and add \"for the two safe reasoners, Seq.empty → backtrack\", which is what the OBLIGATIONS box at :1086 already says for its own case.",
  "needs_author": false
}
```

### F9

```json
{
  "finding_id": "F9",
  "status": "met",
  "evidence": "The comment was changed and is now true. Phi_Logic_Programming_Reasoner/library/reasoners.ML:272 now reads `datatype solver_mode = Agressive_Solver (*the auto method*) | Safe_Solver (*the guard factory: every guard reasoner*)`. At baseline (0110a6fa:272) it read `(*by clarsimp*)`. The file contains no live \"clarsimp\" any more. The only hit, at :1756, is a Pretty string inside the commented-out block that starts at :1753.\n\nThe comment is true of the one place Safe_Solver is still passed. At 0110a6fa it was passed at two places: :1699 (the factory) and :1768 (safe_obligation_solver, which ran clarsimp and has been deleted). A tree-wide `/usr/bin/grep -rnI` over *.ML and *.thy finds Safe_Solver passed only at reasoners.ML:1699, inside `gen_guard_condition_solver` (the factory, :1683-1702), whose body runs `solve`, never clarsimp. All four guard reasoners reach the factory: `guard_condition_judge` (:1734), and `guard_condition_solver` (:1740), which the primed form wraps (:1742-1744). They are registered at PLPR.thy:2025-2038.\n\nsolver_mode stays, as required. The datatype (:272), `type arg = solver_mode` (:275), `apply_tac`'s mode parameter (:286-288) and the two constructor arguments (:976 Agressive_Solver, :1699 Safe_Solver) are all unchanged.\n\nThe brief's section 6 line for F9 (SAFE_GUARD_REVIEW_BRIEF_2026-09-28.md:151) matches the file. This hunk is only a comment edit (git diff 0110a6fa, hunk @@ -269 +269), so it changes no behaviour.",
  "remaining": "",
  "new_issue": "",
  "needs_author": false
}
```

