# Final round — judge's report (2026-09-15)

**Verdict: MET_ON_CONDITION.** Seven conditions, every one of them a hand edit to prose in two documents. No code change, no re-run, nothing for the author. Four filings are rejected as nitpicks and three more are duplicates folded into conditions.

The ML is right and the record is nearly right. What is left is bookkeeping: the plan does not say that the round which produced its current text ever happened, and a handful of sentences in §1, §3, §5, §10 and the review-context document still describe the world as it stood before ruling 10 or point at lines that moved.

---

## Method

Read-only. I ran no Isabelle process, started no session, and changed nothing. I read the two prior reports in full before looking at anything else, so that I would not re-file what they rejected, and I re-verified every decisive claim against the files rather than trusting a filing or its defender.

Two checks worth naming because they settle questions the filings argued over:

- **The patch under review is the tree.** I regenerated `git diff HEAD` over the four files the input patch covers and diffed it against `ai-artifacts/QUICKSORT_REGRESSION_FIX_REVIEW_INPUT_2026-09-15.patch` (ignoring `index` lines): identical. The patch was regenerated at 16:45:29, after the last source edit. Reviewers and the working tree agree.
- **The unevaluated comment edits are inert.** C8 and C9 reworded two comments in `Guard_Decision_Smoke.thy` at 16:08:17, after that theory's last evaluation (its store is 15:27:51). I checked the comment nesting of the whole file programmatically: final depth 0, minimum depth 0, and each edited region balances on its own. So the two rewordings cannot have broken the theory, and no re-run is required. That is what lets me reject `verification-record/V1` rather than order an evaluation.

---

## 1. Were C1–C9 applied faithfully and precisely?

Yes, with two edges. I checked each against the files:

| # | Verified |
|---|---|
| C1 | plan:317 now reads "the factory applied to `p_auto_attempt`"; plan:338 "Its one caller since 2026-09-15". Correct — a repo-wide grep finds `try_prove_or_give_up`'s only production caller at `PLPR.thy:1984` (the rest is one `ai-artifacts` probe). |
| C2 | plan:224-225 "two solving functions, `prove_or_refute` and `p_auto_solving`"; §33's bracketed note at plan:3033-3038 names the same two and excludes the obligation instance. |
| C3 | plan:320-328 now describes `fast_force_tac` as ruling 6 does; "clarifies" is gone. |
| C4 | plan:476-479 (§1's P-auto entry) and plan:1109-1112 (§5 step 4) both carry ruling 10. |
| C5 | `reasoners.ML:195` lists `R-conv/R-nitpick/guard_simp_tac/-`, which is exactly the set of values actually written (`:1548`, `:1549`, `:1555` through `simp_refuter` at `:1389`, and `the_default "-"` at `:1577`). |
| C6 | plan:147-148 now `PLPR.thy:2005-2006`, `:2008-2009`; plan:1062 now `reasoners.ML:1074`, `:1088` — both exact. No `PLPR.thy:1984`/`:1987` survives in the plan. **Partial** — see FR5 and FR6. |
| C7 | plan:3718-3740 records three runs keyed to rulings, and the context document's :109-115 no longer gives the false "confined to the judge path" reason. **Partial** — the context document's own headline block was left unlabelled; see FR2. |
| C8 | Smoke header :14-20 names the one deliberate exception. I checked it is accurate: the third-error probe also ends with `guard_simp_tac` rewriting the guard to `False`, but at step 6, not step 1½, so the header's constraint (which is about step 1½) has exactly one exception. |
| C9 | The P2 probe's comment at :673-676 says "the refuter guard_simp_tac in the record", matching `expect ("refuted", "proved", "guard_simp_tac", "-")` at :680. |

The two edges are FR5 and FR6, and they are different in kind. **FR5** is C6 applied to half of one sentence: the two anchors C6 named were fixed, the two beside them in the same clause were not, and the conditions patch shows them passing through as unchanged context. **FR6** is not C6 applied badly — it is a new inconsistency the C6 edit introduced. The patch added "re-anchored 2026-09-15" to §3's caller list while refreshing only the first pair, so a dated warranty now spans two entries that resolve to a blank line and an `ML \<open>` opener.

Nothing else in the C1–C9 round introduced an inconsistency. The three code edits (C5, C8, C9) are comments, they are accurate, and they changed no behaviour.

## 2. Is the verification record accurate?

**The plan's block is. The context document's is not, and the plan's status line is silent about the round.**

`plan:3718-3740` enumerates three verification rounds keyed to code states by ruling number — "(i) Under rulings 1-7" with 222 live records, "(ii) After the review's conditions", "(iii) After rulings 9 and 10" with "222 → 229 live records". I corroborated the decisive figure by reading the store on disk rather than the prose: `Phi_Examples/Quicksort.proof-store` is 860262 bytes and holds 229 record delimiters, 160 of them `PLPRGUARD`, with mtime 16:41:25 — later than `reasoners.ML` (16:08:11) and `Guard_Decision_Smoke.thy` (16:08:17). `git diff` on `Quicksort.thy` is empty, so the temporary `AoA_driver = "test"` declare is genuinely reverted. The block is an honest account.

Two gaps around it:

- **FR2.** The context document's `## Verification` heading carries no run label, so its bullets — "every probe passes unchanged", "CLEAN under the final code", "222 live records" — read as the current state. The same file then uses "the final code" again at :155 for a later state and gives 229 for it. The collision was created by the C7 edit itself.
- **FR1.** Neither the status line nor §39 mentions the re-review. `plan:3-6` still ends "pending re-review"; §39's only review paragraph covers `wf_cdb1c300-357`, and `wf_3ac0ec80-955` appears nowhere in the plan. Every earlier round has a record (§29, §32, §36, §39), and the drafter's own conditions patch rewrote this same status line when the first review closed. Once `ai-artifacts/` is archived, the plan alone would show no trace of the round that produced its text.

## 3. Leftovers of the pre-2026-09-15 pipeline in §1–§10

I swept §1–§10 for the retired names and the broken universals rather than only checking the filings. §7 is clean — every "until 2026-09-15" clause there is correctly tensed, and plan:1267-1275 and plan:1307-1313 are accurate. `p_auto_body`, `p_auto_search_tac`, `is_F`, `is_false`, `is_guard_mode` and `simpcut_tac` have no survivors in the sources (the one mention, `ai-artifacts/Guard_False_Probe.thy:13`, names `p_auto_body` as the former name in a dated note, which is correct usage).

Two clusters survive, and they are FR4 and FR7. **FR4** is the important one: §1 is the plan's declared authoritative glossary, and three of its entries still say that P-auto decides every call, that `Refuted` comes only from a refuter or the judge, and that it is silent on a hit — all of which ruling 10 broke, and all of which §1 itself contradicts at :242-244 and :476-479. **FR7** is §10's step list, which still names the "G.simpcut" bound and `p_auto_body` — the label in a section §1 explicitly excludes from the ones allowed to keep it, and in a section the drafter *did* sweep this round (plan:1499 and plan:1530 were rewritten) — and carries one parenthetical that is simply false: `PLPR.thy:1965` is `ML_file "library/phi_nitpick.ML"`, and `\<phi>log_guess_inst` occurs nowhere in `PLPR.thy` because §33 records the author's instruction to delete it.

---

## Where I drew the line between a condition and a nitpick

Four filings (`c1-c9/F8`, `c1-c9/F9`, `verification-record/V1`, `verification-record/V5`) are accurate and I am still not making any of them a condition. Three of the four say so themselves.

For the two anchor sweeps (`F8`, `V5`) the line is this: **a stale anchor becomes a condition when this round's own text touched or vouched for it.** FR5's clause was half re-anchored in this round; FR6's list was stamped "re-anchored 2026-09-15" in this round. `F8`'s and `V5`'s anchors sit in sentences nobody edited, are wrong at HEAD as well, name their symbol in the surrounding prose so a reader can grep, and are already owned by §10 step 0, which prescribes exactly the repair the filing proposes ("re-anchor it by symbol lookup, never by offset"). That is the same line the re-review drew when C6 named a specific handful rather than ordering a sweep. Making them conditions would put a ~30-anchor pass over a 3700-line document in front of a fix whose ML is verified right.

`F9` I reject because the correct value is undeterminable from the repository and the proposed change to 24 could easily make the record *less* accurate — the judge's prose count and the structured list it points at can legitimately differ, and the structured list is not here. `V1` I reject because I checked its soundness kernel directly and it is inert.

---

## Bottom line

The restructuring is right, the author's ten rulings are implemented as ruled, C1–C9 are applied, the patch under review is the working tree, and §39's verification block is an honest account of what ran under which rulings. Seven sentences and a handful of line numbers in two documents are behind the code. Apply FR1–FR7 by hand — the plan is a plan document, so no sed, no scripted replace — and commit.