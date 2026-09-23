# Re-review of the applied conditions (2026-09-23) — the judge's report

Workflow `wf_4ce8ff13-774` (model `claude-opus-5-5`, xhigh; three verifiers — the ML, the smoke theory, the documents — and a judge), over the working tree after the code review's conditions (D1-D3, A1-A8, M1 by ruling 22, M2 and R5 by ruling 23, M3 by ruling 24, M4 by ruling 25) and their re-verification.

Verdict: **MET_ON_CONDITION**.

# Re-review of the check `\<check> \<premise> \<consistency>`: judge's report (2026-09-23)

**What was reviewed.** The uncommitted working tree of `contrib/phi-system`, on top of `90cbfabc`, after the first code review's conditions were applied. The first review's report is `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_CODE_REVIEW_2026-09-23.md`. The plan is `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md`, rev 10 ("the check plan"). "The guard plan" is `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md`. Three verifiers checked the code, the smoke theory and the documents. I read the code and every document where a verifier reported a residue. Everything below cites working-tree lines unless it says otherwise.

## Verdict: MET_ON_CONDITION

Every condition of the first review is either applied or settled by one of the author's rulings (22-25). **The code is correct, and no new code defect was found.**
- **D1: one test, one pull.** Step 1 1/2 and the judge path now share one pull, `simplified_in` (reasoners.ML:1525-1528), and one test, `refuted_by_simp` (:1532-1534). They cannot diverge.
- **M1: exactly one pattern.** `guard_kind_of` now reads exactly `Trueprop (Premise _ False)` (:1719-1727), as ruling 22 says. `concl_is_false` (:998-1001) still reads only the bare `False`, so the two predicates are disjoint.
- **M2: the user-visible text is true.** `PLPR.thy:221-226` no longer contains the false clause.
- **Behaviour is unchanged since the first review.** The first review's code patch, diffed against the current one, gives exactly the delta file. That delta holds only D1, the M1 deletion, the A6 clause, the D2/A7/A8 edits in the test, the M2 deletion and the R5 pointers.
- **Re-verification is done.** After the last edits, PLPR.thy is clean, and the smoke theory (828 lines) is clean twice in fresh processes. This is recorded in the stage-2 record :290-297 and was matched against the session log.

**What still stands:**
- **One item for the author.** D1 required that the new local names go to him: `simplified_in` and `by_simp` (N1).
- **Eight hand edits in documents and one comment**, all stale or inaccurate sentences (N2-N9). None touches code, a verdict or a test expectation.

## Status of each condition

- **D1**: applied exactly. The two sites share one closure over `kind` and one pull over `th0`. The error text and the verdicts are HEAD's. `guard_simp_tac` is untouched. The names still have to go to the author (N1), and the guard plan's §39 note still spells the old boolean (N6 b).
- **D2**: applied exactly (Guard_Decision_Smoke.thy:758-766 is the report's four lines). The probe fails in all three cases the report named. Its comment rightly disclaims the wiring inside `guard_condition_judge`. Remaining: §6 item 2 and §10 do not yet record it as a strengthening (N5 a), and the comment says "differ only in kind" (N8).
- **D3**: applied. The one flip is reported: Bucket_Hash.thy:222, digest `79d491a434b111b5`, kind Normal, 3380 ms, checked against the leg's event log. The records are described as tombstoned, the wall-clock bounds are stated, the Phi_Types loss is recorded, and the other changed files are named. Remaining: the cache-off leg's "not applicable" and, in the plan, the partial leg's 0 (N5 b); two sentences in the stage-2 record still expect M3's load (N9 b).
- **M1**: applied as ruling 22 settled it. The bare arm is deleted, and neither comment says "or bare". Remaining: §10 says "R1 taken" (N4 a), and the stage-2 record :33 still reports the old classification (N9 a).
- **M2**: applied exactly (PLPR.thy:222-224). Every remaining clause is true against reasoners.ML and guard_refute.ML. Remaining: plan §4.8 still quotes the old clause (N3).
- **M3**: settled by ruling 24. No store and no `.C` file enters the commit.
- **M4**: settled by ruling 25, and departure 5 is recorded (§10 :1412-1415). Remaining: the status line's "the departures stand" (N2).
- **A1**: applied. The line numbers are anchored to `1f3c2142`, and that anchor is true: `git diff 1f3c2142 HEAD -- Phi_Logic_Programming_Reasoner/` is empty. The stage-3 clause and departure 5 are in place. Remaining: the rest of the status paragraph is at rev 8 and contradicts its opening (N2).
- **A2**: applied exactly. This covers the §3 diagram (:1024-1026), the gloss on `kind`, and the end of step 4 (:1263-1268). The "above/below" directions are right.
- **A3**: applied (guard plan :284-286, now in the past tense).
- **A4**: applied. "The check plan" is the only name used, and no coined compound remains.
- **A5**: applied under R5. The R-conv comment (reasoners.ML:1614-1616) points at the guard plan's §5 step 4, which exists and says that R-conv is not run for the check. §10 records the choice.
- **A6**: applied word for word (reasoners.ML:1629-1632), and it is true: `undecided_guard_warning kind` prints the undecided-check warning for the check.
- **A7**: applied (smoke :19-24, :701-707). The count of three exceptions is right, and every probe's stated path matches the code and the post-edit event log.
- **A8**: applied exactly (smoke :214-217, using `remove (op =) line warning_lines`). No `expect` line changed.
- **R1**: the arm is dropped with M1. The `dest_premise_tag_opt` half was not taken, because the code keeps ruling 22's literal pattern. Only the record in §10 needs correcting (N4 a).
- **R2, R3, R6**: declined. **R4**: recorded as the rule for future legs.
- **R5**: applied. The seven pointers (guard_refute.ML:21, :188; reasoners.ML:100, :1101, :1616; the smoke theory's :10 and :701-702) all resolve to sections of the guard plan that say what each pointer claims. No committed source spells the retired word as a file name. Remaining: §10 cites them by working-tree line (N4 c).

## Residual items

**For the author (MUST_DISCUSS):**
- **N1.** Approve or rename the local names `simplified_in` and `by_simp` (reasoners.ML:1525, :1539). D1 said the helper's name "goes to the author with the stage-3 report, as §9 does for every new name". Neither name is in §9, although §4.3 a :461 says "§9". Then record them in §9.

**For the drafter, by hand (DRAFTER_APPLIES):**
- **N2.** The plan's status paragraph (:3-27) contradicts itself:
  - "the departures stand" (departure 4 was deleted by ruling 22);
  - "what remains is the re-verification" (it is done);
  - "M1-M4 and six relaxation proposals pending his rulings", and the departures "for the author to rule on" (all ruled);
  - "items 1-21" (the rulings now run to 25).
- **N3.** Plan §4.8 :747-748 still quotes "Unlike every other guard," as the approved paragraph.
- **N4.** Three statements in plan §10:
  - "R1 taken with M1" (:1465) overstates what was taken;
  - "parts of seven others" (:1457) should be eight: F1, F2, F3, F6, F7, F15, F16, F17;
  - the R5 sentence (:1469-1470) cites working-tree lines against the `1f3c2142` anchor.
- **N5.** Two records to complete:
  - D2 is not recorded as a strengthening of §6 item 2, which still describes the old probe (:962-965);
  - D3's per-leg floors are incomplete: the cache-off leg's "not applicable" is missing, and so is the partial leg's 0 in the plan.
- **N6.** Two stale passages in the guard plan:
  - the status header (:3-6) still says "pending its code review";
  - the §39 note (:3921-3926) still spells `refuted_by_simp` as the boolean over `th1`.
- **N7.** Both handoff addenda still say stage 3 waits for the author's go (CHECK_HYPOTHESIS_CONSISTENCY_HANDOFF_2026-09-23.md:4-7; GUARD_CACHE_RESUME_HANDOFF_2026-09-11.md:11).
- **N8.** The smoke comment at :754-755 says the two states "differ only in kind", but they also differ in their guard. After rewording it, evaluate the smoke theory once under Isabelle-MCP.
- **N9.** Two stale passages in the uncommitted stage-2 record:
  - :33 still says `guard_kind_of` reads the bare `False` as the check;
  - :186-188 and :217-218 still expect the confirmation load that ruling 24 cancelled.

By the project's rule, plan documents are edited by hand, not by script. Apart from N8's one smoke evaluation, none of these items needs re-verification. If the author renames anything under N1, restart the REPL/MCP session and evaluate the smoke theory once.

## Rejected residues

- **"The stage-2 record lacks the post-16:06 re-verification."** Refuted: the record's final section (:290-297, written at 16:20:48) records it.
- **"Smoke :692 'the judge path's own test' is stale."** The sentence is still true: the judge path does run the test on its own state `th'` (reasoners.ML:1579).
- **"Use `dest_premise_tag_opt` in `guard_kind_of`."** Asking for this as a code change would re-open ruling 22. Only the §10 record needs correcting.
- **The guard plan's "the check" entry citing rulings 1-21.** Still true; it never admitted a bare `False`.
- **The stage-2 record's section time ranges.** They are loose but contain the events, in an uncommitted record.
- **The optional first introduction of "the check plan" in the guard plan.** A matter of taste.
- **§10's present-tense quotation of A3.** Immaterial.

## What the commit should contain

**Code, five files:**
- `Phi_Logic_Programming_Reasoner/PLPR.thy`
- `Phi_Logic_Programming_Reasoner/Test/Guard_Decision_Smoke.thy`
- `Phi_Logic_Programming_Reasoner/library/guard_refute.ML`
- `Phi_Logic_Programming_Reasoner/library/phi_nitpick.ML`
- `Phi_Logic_Programming_Reasoner/library/reasoners.ML`

**Documents:**
- `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md`
- `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md`
- `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_HANDOFF_2026-09-23.md`
- `ai-artifacts/GUARD_CACHE_RESUME_HANDOFF_2026-09-11.md`
- The code review's report, `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_CODE_REVIEW_2026-09-23.md`. It is a review record: the plan's status line and §10 cite it by path, the author's rule of 2026-09-23 lets review records be committed, and `be16be02` committed the plan's reviews the same way.

**Not in the commit (ruling 24 and the rule that experiment results are not committed):**
- the seven modified `.proof-store` files (`Binary_Search`, `Binary_Trees`, `Bucket_Hash`, `Dynamic_Array`, `Linked_List`, `Matrix_Oprs`, `Phi_System/Phi_Types`);
- `Phi_Examples/Bucket_Hash.C`;
- the untracked `Guard_Decision_Smoke.proof-store`, `Guard_Export_Smoke.proof-store` and the `.o` files;
- the stage-2 record, which is an experiment result (§10 says so);
- the review patches and the delta file (git-ignored);
- `ai-artifacts/Check_Display_Probe.thy`.

Stage only the files named above. Leave everything else in the shared tree untouched.

## Disclosure

The code verifier reports that one shell redirect wrote a file into the session scratchpad, contrary to the read-only instruction: `/tmp/claude-1002/-home-qiyuan-Current-MLML/706a5b1c-5fbd-4da6-ba94-dc259cc72ae8/scratchpad/ml_now.diff`, a copy of the ML diff. Nothing in the repository was changed. I wrote no files.

