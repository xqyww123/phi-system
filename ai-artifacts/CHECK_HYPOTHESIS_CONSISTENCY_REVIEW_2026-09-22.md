# Adversarial review of `CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md` rev 1 — the judge's report

- **Plan reviewed**: `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md`, rev 1 (2026-09-22),
  533 lines.  Line numbers in the plan are those of phi-system `1f3c2142`; the working
  tree is `6026b43e` and every file cited below was re-verified in it by the judge.
- **Date**: 2026-09-22.
- **Workflow**: six interrogation lenses (diagnosis, elegance, verification, consistency,
  symbols, relaxation) → a curator, who dropped four points and merged two → one fresh
  defender per surviving point, with no sight of the other points → this judge, who
  re-verified the decisive citation of every point before ruling.
- **26 findings (F1–F26) and 5 relaxation proposals (R1–R5) reached the judge.**
  11 upheld or partially upheld, 15 refuted; of the refuted, 8 are rejected as
  nitpicking and named as such below.  One relaxation is put to the author; four are
  dropped.
- Terms are the plan's glossary (§1) and the guard plan's (§1): the check, the flag
  `assume_consistent`, the three consumers, the template's rewrite, the hypotheses,
  the digest marker, the undecided-check warning, the factory, the solving function,
  P-auto, R-conv, R-nitpick, `guard_simp_tac`, `p_auto_attempt`, the out-of-run
  instance, the judge, entry, delta.

---

## Readiness: **MET_ON_CONDITION**

No blocker survived.  The plan's design is sound: the flag, the three consumers, the
digest marker, the entrance-computed `assume_consistent_of`, and the decision to leave
P-auto, the judge and the entries untouched all stand after adversarial attack.  What
the review found is (a) one class of genuine correctness defects in the plan's **prose**,
concentrated in §4.3(c), which is scheduled into a source comment and into user-visible
documentation, (b) a wrong mechanism in §4.8's display argument, (c) a scatter of
count, citation and checklist corrections, and (d) one relaxation, R1, whose acceptance
or rejection changes the shape of stage 1 and must therefore be settled before stage 1
begins.

The plan's most attacked claim — that the slice must come off for R-nitpick's answer to
mean anything — **survived and was strengthened**.  With the slice on, `slice`'s `grow`
starts from `frees_of concl`, the check's conclusion has no free variables, so `grow`
returns `[]` on its first call and Nitpick receives an **empty** premise list
(guard_refute.ML:135-150, called at :198).  The verdict today carries no information
whatever.  Turning the slice off is what turns a content-free refutation into a real
search.  That is the plan's central insight and nothing in this review touches it.

**Conditions gating stage P (the symbols)** — all three are drafter corrections, none
needs the author:

- P-1 (F24): make `python3 fonts/build_word_glyphs.py --check` on the **untouched** tree
  the first action of the stage, before `words.txt` is edited.
- P-2 (F23): stage P's "Nothing else changes in this stage" must give way to the five
  hand-maintained counts, and must exclude the sixth site, which records history.
- P-3 (F9): stage P's exit condition must be stated in terms this environment can
  observe; the jEdit rendering check is the author's, and the Isabelle-MCP restart moves
  to the head of stage 1.

With P-1 to P-3 applied, **stage P may start.**

**Conditions gating stage 1 (the code)**:

- 1-A (R1): the author rules on the relaxation "hoist the refutation shortcut out of
  `guard_simp_tac` into `prove_or_refute`".  Stage 1 items 2 and 3, §4.2, §4.3(a) and
  §7's fourth bullet all take a different shape under it, so it cannot be deferred.
- 1-B (F1, F2): the author rules on the three MUST_DISCUSS items — the word "exactly"
  in ruling 1 and §1, the trust rail as a third weakening in §7 (ruling 7 covered only
  two), §4.8's user-visible sentence, and the new §9 question about `trust_assms`.
- 1-C: the author rules on §9's pending list, which now also carries F4's raw
  right-hand side for the abbreviation and F15's corrected `\<condition> P` paragraph.
- 1-D: the drafter applies the fourteen DRAFTER_DECIDES corrections (F3, F4, F5, F8,
  F9, F10, F12, F13, F15, F17, F18, F19, F23, F25) and the plan is re-reviewed.

Stage P and stage 1 are independent: which three **words** stage P allocates does not
depend on any of 1-A to 1-D.

---

## The rulings

| id | title | severity | verdict | disposition |
|----|-------|----------|---------|-------------|
| F1 | A fourth place spells the assumption: `Phi_Nitpick`'s `trust_assms`, hard-coded `true` | major | PARTIALLY_UPHELD | MUST_DISCUSS_WITH_AUTHOR |
| F2 | §4.3(c)'s soundness sentence is false and is scheduled into a source comment | major | UPHELD | MUST_DISCUSS_WITH_AUTHOR |
| F4 | §4.8 names a function that does not exist and mis-describes the abbreviation's key | major | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F3 | "returns the residue's premises whole": the ML `slice` also does the conjunction splitting | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F5 | §6 item 2's "the second run meets the entries the first wrote" cannot happen | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F8 | §6 item 4's reason for expecting no check in the corpus is wrong | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F9 | Stage P's exit condition is not observable under Isabelle-MCP | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F10 | "exactly the three steps read the flag" is false by the plan's own §4.3(b), §4.5–§4.7 | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F12 | Eight live uses in `Phi_BI`, not twenty; four live callers, not five | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F13 | A second copy of `undecided_guard_warning`, where the file's sibling is parameterised | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F15 | The new `\<^descr>` will contradict the stale one in the same block | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F17 | Two body comments and the smoke header's reachability constraint are off the checklists | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F18 | No probe is named for the slice; the method is edited and probed nowhere | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F19 | §1's "registered patterns" reason covers one of the two readers; §3 cites a deletion utility | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F23 | Stage P leaves hand-maintained counts stale | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F24 | Stage P cannot separate "committed files stale" from "local fontTools differs" | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F25 | §8's open question about a cut mark can be closed from the source | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F6 | No check probe at `can_inst = true` | none | REFUTED | NO_ACTION |
| F7 | §6 item 4's corpus floor unobtainable: no baseline leg | none | REFUTED | NO_ACTION |
| F11 | The factory's front `quick_cut 1 th` is dead and should be deleted | none | REFUTED (nitpicking) | NO_ACTION |
| F14 | `assume_consistent_of` returns the bare bool §1 forbids | none | REFUTED (nitpicking) | NO_ACTION |
| F16 | Stage 1's order and its re-evaluation instruction contradict each other | none | REFUTED (nitpicking) | NO_ACTION |
| F20 | Give the flag to `nitpick`, not to `preprocess` | none | REFUTED (nitpicking) | NO_ACTION |
| F21 | P-auto may prove the check by instantiation | none | REFUTED (nitpicking) | NO_ACTION |
| F22 | The abbreviation also spells guards the template's rewrite turned into `False` | none | REFUTED (nitpicking) | NO_ACTION |
| F26 | `Check_Hypothesis_Consistency` is out of step with its three neighbours | none | REFUTED (nitpicking) | NO_ACTION |

| id | relaxation | recommendation |
|----|------------|----------------|
| R1 | Hoist the refutation shortcut out of `guard_simp_tac` into `prove_or_refute` | **PROPOSE_TO_AUTHOR** — recommend accepting |
| R2 | Skip R-nitpick for the check, as R-conv is already skipped | DROP |
| R3 | Make stage P a companion commit after the flag lands | DROP |
| R4 | Carry the flag as an ML-only `Config` value | DROP |
| R5 | Widen the factory's digest callback to take `th0` | DROP (a narrower refinement recommended instead) |

---

## F1 — A fourth place in the code base spells the assumption: `Phi_Nitpick`'s `trust_assms`

**PARTIALLY_UPHELD · major · MUST_DISCUSS_WITH_AUTHOR**

**Claim (condensed).**  §0 and §1 say the flag is consulted by *exactly* the three steps
whose validity rests on the assumption.  There is a fourth, one layer below the slice:
the vendored `Phi_Nitpick` carries a patch whose stated purpose is refutation *under the
assumption that the premises are jointly satisfiable*, and `Phi_Guard_Refute.nitpick`
turns it on with a hard-coded `true`.  Under it the premises ride the unknown-tolerant
rail while only the negated conclusion keeps the strict one — and for the check the
conclusion is `False`, so the strict rail is vacuous and the whole verdict rests on the
relaxed rail.  Therefore §4.3(c)'s "a model Nitpick finds satisfies all the hypotheses"
is false, and §5 stage 1 item 1 schedules that sentence into `guard_refute.ML` as a
comment.  Graded a blocker; proposed fix: pass `assume_consistent` through to
`pick_nits_in_term` in place of the literal `true`.

**Defence (condensed).**  Concedes the three plan-text defects and refutes the headline.
The slice's failure on the check is **total**: `grow` returns `[]`, so Nitpick receives an
empty premise list and every assignment refutes.  The trust rail is a different animal:
with the slice off, all premises reach Kodkod, and a premise Kodkod *can* evaluate and
that no assignment satisfies still blocks every model.  So the plan's change turns a
content-free verdict into a real search; it does not "move the unconditional refutation
down a layer".  "Blocker" is wrong because R-nitpick can only report Refuted or stand
down, so every premise-rail imprecision can only produce a spurious *Refuted* — a dead
branch left unpruned, which is today's behaviour and §7's accepted class.  The proposed
code change is not free: `max_potential = 0` is pinned, so `unsound` is always false and
`unsound orelse trust_assms` collapses to `trust_assms`; turning it off puts every kept
premise on the strict rail, and φ-System guard premises routinely carry atoms Kodkod
cannot evaluate, so most checks may end Unknown.  That is a measurement for stage 2 and
a ruling for the author, not a reviewer's remedy.

**Ruling.**  I verified every citation on both sides.  `guard_refute.ML:226` does pass a
literal `true`, and `phi_nitpick.ML:93-96` confirms it is `trust_assms`; the patch's own
header at `phi_nitpick.ML:14-22` names this plan's assumption verbatim ("refutation under
the guarantee that the premises are jointly satisfiable"); the per-formula split is at
`phi_nitpick.ML:519-533`.  The plan mentions none of this: `grep -n trust` over the whole
plan returns one line, and it is the word "trustworthy".  So §0's and §1's "exactly" is an
overclaim and §4.3(c)'s sentence is false — **upheld**, and it must not reach
`guard_refute.ML`, whose own comments at :82-84 and :170-173 already disclaim it.

The headline conclusion is **refuted**, and the defence's reading is the correct one.  I
read `slice` (guard_refute.ML:135-150) myself: `grow known pending` partitions on
`exists (member (op =) known) (frees_of p)`; for the check `known = frees_of (Trueprop
False) = []`, so `connected` is empty on the first call and `grow` returns `[]`.  The
premise list handed to Nitpick today is empty.  "Not trustworthy either way" is therefore
false: the two situations differ by everything.

Grade: **major, not blocker.**  Nothing unsound is reachable.  R-nitpick reports Refuted
or stands down (guard_refute.ML:16-18, :228-229), so every imprecision on the premise rail
costs completeness only — a dead branch not pruned, exactly the loss §7 already accepts in
terms.

On the classification of the trust rail I side with the defence, and the parent plan
settles it: `GUARD_NITPICK_FALSIFY_PLAN.md:1789-1792` records that the consistency
assumption **cannot** make a premise-side relaxation sound — "它保证 P 有模型,不保证 P'
的模型能延拓到 P".  The trust rail is therefore a *weakening of the premise rail*, in
the class of §7's two accepted weakenings, not a step whose validity the assumption
restores.  Calling it a fourth consumer would make the plan less accurate, not more.

**Resolution.**  The plan changes as follows; no code change follows from this finding.

1. §0, after "and the slice inside R-nitpick", records that a fourth place spells the same
   assumption and is deliberately *not* one of the three: `Phi_Nitpick`'s `trust_assms`,
   hard-coded `true` at guard_refute.ML:226, whose header is phi_nitpick.ML:14-22 — a
   weakening of the premise rail, in §7's class, not a step the assumption makes valid
   (GUARD_NITPICK_FALSIFY_PLAN.md:1789-1792).
2. §1's "the three consumers" entry says so too.
3. §7's first bullet gains the trust rail as a **third** weakening, with the note that for
   the check the negated conclusion is `\<not> False` and carries nothing, so the premise
   rail alone carries the verdict.  **Ruling 7 covered only two weakenings; this third is
   new to the author and needs his word.**
4. §9 gains the open question: should `assume_consistent` also be passed to
   `Phi_Nitpick.pick_nits_in_term` in place of the literal `true`, so that one name governs
   the assumption everywhere?  The gain is elegance — as the plan stands a reader of
   guard_refute.ML sees `preprocess {assume_consistent}` skip the slice on one line and
   `... params true ...` two lines below.  The cost is unmeasured and may be large, for
   the reason the defence gives (reasoners.ML:1254 pins `max_potential = 0`;
   GUARD_NITPICK_FALSIFY_PLAN.md:1632, :1803-1805).  **Recommendation to the author: leave
   `true` in stage 1 and decide on stage 2's evidence.**
5. §6 item 4 adds the checks' verdict split (proved / refuted / unknown) to what is
   measured, as the evidence for that question.

The rewrite of §4.3(c)'s sentence itself belongs to F2, which owns it.

---

## F2 — §4.3(c)'s soundness sentence contradicts §7 and the neighbouring code

**UPHELD · major · MUST_DISCUSS_WITH_AUTHOR**

**Claim (condensed).**  §4.3(c) says that with the slice off "a model Nitpick finds
satisfies all the hypotheses: the one positive witness of consistency in the pipeline, and
the reason a Refuted entry of a check is trustworthy".  §7's first accepted imprecision
says the opposite two pages later.  Three mechanisms falsify it independently of F1's
trust rail: `is_premise` drops untagged context assumptions, the `Preprocess_Hooks` rewrite
what survives, and the accepted verdict includes `quasi_genuineN`, which certifies nothing.
The same overclaim reaches the user in §4.8's `\<^descr>` ("decided without assuming the
hypotheses consistent"), and §5 stage 1 item 1 schedules the sentence into
`guard_refute.ML`.

**Defence (condensed).**  Full concession, with two corrections and a different repair.
Leg 1 is blunted by the plan's own glossary — §1 defines "the hypotheses" as what
`premises_of` collects, and the `is_premise` filter is *inside* `premises_of` — but that
exposes a real terminology defect instead: §7 uses "the hypotheses" with a second referent.
Leg 2 stands and is worse than stated: the sole registered hook is the scrub, which replaces
`Satisfiable (x : T)` by `True` and then **deletes** the premises that became `True`.  Leg 3
stands and understates: with `trust_assms = true`, `genuine_means_genuine` is false by
construction, so R-nitpick's Refuted is *always* quasi-genuine, never merely usually.  The
finding's own replacement wording ("must satisfy every premise that survives `is_premise`
and the hooks") is still false, for the trust patch's reason, and must not be adopted.

**Ruling.**  Upheld, and the defence's corrections are right on every point I checked.
`guard_refute_scrub.ML:161-163` is `map one prems |> filter_out vanished` and :165 registers
it as the sole `Preprocess_Hooks` entry; `guard_refute.ML:178` invokes the hooks strictly
after `premises_of` at :177.  `phi_nitpick.ML:665-668` is `genuine_means_genuine = ...
andalso not trust_assms  (*PHI-PATCH*)`, `:755-760` feeds it into `found_really_genuine`, and
`:954-957` returns `genuineN` only `if found_really_genuine` — so with `trust_assms = true`
every refutation R-nitpick can ever report is `quasi_genuineN`, and the downgrades listed at
reasoners.ML:1271-1281 ride along unconditionally.  The patch's header states the rest in one
sentence: a countermodel "may leave premises unevaluated".

A source comment asserting a soundness property that the three comments around it deny is
precisely the shape the author's first criterion rejects.  This one is scheduled into
`guard_refute.ML` by §5 stage 1 item 1.  It is not nitpicking; it is the most consequential
prose defect in the plan.

**Resolution.**

1. §4.3(c): delete "With every premise kept, a model Nitpick finds satisfies all the
   hypotheses: the one positive witness of consistency in the pipeline, and the reason a
   Refuted entry of a check is trustworthy."  In its place, say what is true where it will
   land — that keeping every premise buys **content, not certification**: with the slice on
   the premise list handed to Nitpick is *empty* (`grow` starts from the conclusion's free
   variables and `False` has none, guard_refute.ML:135-150) and every assignment refutes, so
   the verdict says nothing; with it off the search must exhibit an assignment under which no
   premise is definitely false, and a premise Kodkod can evaluate and that no assignment
   satisfies still blocks every model.  Then state plainly that the model is not a
   certificate: `trust_assms = true` (guard_refute.ML:226) lets an unevaluable premise through
   as if true, `is_premise` and the hooks weaken the rest (§7), `user_axioms = false`
   (reasoners.ML:1256) means nothing is certified genuine, and a check's Refuted is
   `quasi_genuine` by construction.  A wrong Refuted costs completeness only: the branch stays
   live.  **Do not adopt the finding's own replacement wording.**
2. §5 stage 1 item 1's checklist entry becomes "the comments (what keeping every premise buys,
   §4.3 c as revised — NOT a claim that the model satisfies the hypotheses)".
3. §4.8's `\<^descr>`: "Unlike every other guard it is decided without assuming the hypotheses
   consistent" becomes "Unlike every other guard, the three steps that presuppose consistent
   hypotheses are off for it", keeping the list and the reference.  **User-visible text: it
   goes to the author through §9 with the rest of §4.8.**
4. Terminology: §7 must stop using "the hypotheses" for a second referent.  One concept, one
   name — the glossary is authoritative.
5. §1's and ruling 1's word "exactly" in "the three consumers are exactly the steps whose
   validity rests on it" is the sentence F1 also touches.  **This is a ruling of §2 and only
   the author may soften it.**  The drafter proposes: "the three steps that refute every check
   unconditionally".

*(F1 and F2 overlap on §4.3(c) and on "exactly"; they are one conversation with the author,
not two.)*

---

## F4 — §4.8's display argument: a function that does not exist, a wrong key, a fallback that is not needed

**PARTIALLY_UPHELD · major · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  (a) §4.8 says `contract_abbrevs` rewrites top-down
"(`Pattern.rewrite_term_top`)"; no such function exists and `contract_abbrevs` uses
`rewrite_term_yoyo`.  (b) The new abbreviation will not be keyed on `Premise MODE_GUARD
False`: `abbreviation` certifies its right-hand side with `normalize = false`, so
`rev_abbrev` registers `(Simp_Premise False, …)`, which matches nothing at the top; the
display still comes out right, but by two accidents.  (c) The `translations` fallback names a
construction with the same failure mode.  Fix: write the right-hand side raw,
`\<equiv> Premise MODE_GUARD False`.

**Defence (condensed).**  (a) and (b) conceded, verified through the whole chain; (c)
refuted — the plan's hedge says a `translations` rule *from the concrete syntax*, i.e.
written `\<condition> False`, whose AST pattern is headed by `Constant "Simp_Premise"`, which
is exactly what `term_to_ast` produces from the contracted term, so such a rule *would* fire.
The sentence should still go, but as a consequence of the (b) fix.  One further caution: the
author's own opening design writes `\<equiv> \<condition> False`, so the raw right-hand side
belongs in §9's pending list, not in a silent drafter edit.

**Ruling.**  (a) and (b) **upheld**, verified independently at every link.
`more_pattern.ML:17-18` and `:139-141` export `rewrite_term`, `rewrite_term_topdown` and
`rewrite_term_yoyo` — there is no `rewrite_term_top`; `proof_context.ML:743` is
`|> Pattern.rewrite_term_yoyo thy [] [match_abbrev]`, and yoyo (`more_pattern.ML:119-130`)
tries the node, then the subterms, then the node again.  `proof_context.ML:701-703` gives
`certify_consts` `normalize = not (abbrev_mode ctxt)`, i.e. false inside `abbreviation`;
`consts.ML:196-200` then keeps the abbreviation constant unexpanded (`comb head`); and
`consts.ML:320-343` registers `rev_abbrev lhs rhs` on the **unexpanded** `rhs`.  So the key
really would be `Simp_Premise False`.  Neither rule matches at the top: `pattern.ML:349-352`
raises `MATCH` when two constants' names differ, and `pattern.ML:374-377` type-matches the
whole pattern against the whole object first, so `Simp_Premise`'s reverted left-hand side
(type `bool \<Rightarrow> bool`) cannot match a term of type `bool`.

(c) **refuted**: the defence's reading of the plan's hedge is the natural one, and I do not
accept a correction that would replace one false claim with another.

The fix is an elegance gain in the author's own terms, not a matter of taste: with the raw
right-hand side the reverted rule is keyed on the whole term, the first attempt at the top
matches, and the plan's claimed invariant becomes true by construction instead of resting on
two accidents nobody documented.  It is also the block's own idiom — PLPR.thy:203, :205 and
:207 all write `Premise default`, `Premise MODE_GUARD`, `Premise MODE_COLLECT` raw.

Severity major, because §4.8 is the one paragraph that flags itself "inferred from the source
and MUST be measured", and its inference is built on a function that does not exist.  No
behaviour of the reasoner changes either way.

**Resolution.**

1. §4.8: cite `Pattern.rewrite_term_yoyo` (proof_context.ML:743, more_pattern.ML:119-130) and
   drop "top-down"; replace the "tried before `Simp_Premise`'s" argument with the whole-term
   key, explaining that the key is the right-hand side **as certified with `normalize = false`**
   (consts.ML:320-343) and that this is why the right-hand side is written raw.
2. Change the declaration to `where "\<check> \<hypothesis> \<consistency> \<equiv> Premise
   MODE_GUARD False"`, and **record it in §9 as pending [drafter]**, with the note that the two
   spellings denote the identical term and only the reverted print key differs.  The drafter
   does not silently rewrite a formula the author wrote himself.
3. Delete the `translations` sentence — with the raw right-hand side there is nothing to fall
   back from.  Do **not** delete it on the finding's stated ground.
4. Keep §4.8's "MUST be measured in stage 1" and §6 item 1's two measurements exactly as they
   stand; they now confirm a prediction that is true for the stated reason.

---

## F3 — "returns the residue's premises whole": the ML `slice` also performs the conjunction splitting

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  §4.3(c) says `preprocess` "slices only under `assume_consistent` and
otherwise returns the residue's premises whole", adding that "`slice` itself is unchanged".
But the ML function `slice` also runs `split_conjunctions` over every premise before filtering,
in the same expression.  The two readings hand Nitpick different premise lists, and the
difference is observable, because the soundness flag is taken per formula: a premise
`A \<and> B` kept whole carries one flag where `A` and `B` would carry two.

**Defence (condensed).**  The half that carries the severity is fabricated.  The comment the
finding quotes (guard_refute.ML:202-205) is about premises-as-assumptions versus
premises-inside-the-goal, not premise-versus-premise granularity.  `phi_nitpick.ML:519-533` has
exactly **one** boundary — the negated conjecture versus every axiom — and every element of the
tail receives the identical flag value, so "one flag where there would be two" is true and
empty.  Worse for the finding: where premise granularity *is* visible
(`nitpick_preproc.ML:885-889`), splitting can move a conjunct of the form `Free = t` onto the
*definitional* rail, which `phi_nitpick.ML:517-518` encodes with the **strict** flag — so the
finding's proposed `maps split_conjunctions prems` is the shape that could change a premise's
rail, and the plan's shape cannot.  What survives is one clause of wording.

**Ruling.**  I verified both.  `slice` (guard_refute.ML:135-150) is
`Logic.list_implies (grow (frees_of concl) (maps split_conjunctions prems), concl)` — the
splitting is inside, as the finding says.  `phi_nitpick.ML:519-533` is
`choose_reps_in_nut scope unsound … conj_u :: map (choose_reps_in_nut scope (unsound orelse
trust_assms) …) axiom_us` — one boundary, one flag value for the whole tail.  And
`nitpick_preproc.ML:850-889` partitions on `assumption_exclusively_defines_free`, which matches
only a whole formula `Free = t`.  The defence is right on both counts, and its rejection of the
proposed fix is right.

What survives is real and small: the plan's prose term "the slice" (the free-variable filter)
and the ML function `slice` are not the same thing, and the plan — which elsewhere is meticulous
about exactly this kind of knock-on (see §4.3(a)'s three named unreachable paths) — never says
that the splitting falls with it.  By its own standard that sentence belongs there.  Severity
minor; no behaviour changes and the implementable reading is already unique.

**Resolution.**  In §4.3(c), after "`slice` itself is unchanged", add that for the check it is
simply not called, so the conjunction splitting (guard_refute.ML:126-133) does not run either;
that this is intended and costs nothing, because splitting exists only to let the filter keep or
drop the conjuncts of one premise separately (guard_refute.ML:121-124) and the soundness flag is
taken between the negated conclusion and the assumptions, not between one assumption and the
next (phi_nitpick.ML:519-533).  **Reject** the finding's `else maps split_conjunctions prems`.

---

## F5 — §6 item 2's "the second run meets the entries the first wrote"

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  §6 item 2 asserts two incompatible things in one parenthesis; the second
clause (the `fresh` numerals keep the digests apart) makes the first impossible.  And were it
attainable it would break every probe, because `decide` asserts the records carrying this
guard's digest are exactly `[path]` while every check probe's `path` carries `hit = "none"`.

**Defence (condensed).**  The parenthesis is wrong and must be rewritten — the parent plan uses
"meets an entry" for precisely what `fresh` prevents.  But "every check probe carries
`hit = none`" is false: §6's judge-overturn probe expects `("refuted", "proved", "-",
"Unprovable")`.  And the real hazard of a repeated digest is not the one named: an injected entry
is written *before* the call, so it would be overwritten, not met; what would break every probe is
that `decide` would find two records and `[path, path]` fails whatever the verdicts.  Severity
"major" is overstated: one parenthesis in the verification section, corrected by its own next
clause, with no design consequence.

**Ruling.**  Upheld on the sentence, refuted on the reasoning and the grade.  Verified:
`Guard_Decision_Smoke.thy:220-221` is `val run_tag = Time.toNanoseconds (Time.now ())` and
`fun fresh () = string_of_int (run_tag + serial ())`; the header states the design at :22-27;
`run_guard` writes the injected entry before the call at :120-124; `decide` filters at :140 and
asserts `observed = [path]` at :142-146.  The parent plan's `GUARD_CACHE_QUICK_MODE_PLAN.md`
uses "meet an earlier run's entry" for the very thing `fresh` exists to prevent.  So the first
clause is false and the second is why.

**Resolution.**  Rewrite the parenthesis to say what the second run actually establishes: it runs
against the store the first run's entries were written into and against the same `guard_decision`
log, and must be unaffected by both, **because** the `fresh` numerals give every probe a digest
no earlier run used — so no probe meets an entry, and no probe's digest filter sees an earlier
run's record.  Do not add a probe as part of this fix: §6's judge-overturn probe already exercises
a check meeting an injected entry.  (If the author separately wants §7 bullet 3's remaining warm
path — an Unknown entry of a check re-consulting the judge — covered, that is a one-line addition
in the same vocabulary, proposed on its own.)

---

## F6 — No check probe states `can_inst`

**REFUTED · none · NO_ACTION**

**Claim (condensed).**  Production dispatches every check at `can_inst = true`, where the
template's fix level 1 "fixes only the variables of the leading antecedent's CONCLUSION that do
not occur in its premises"; the check's conclusion has none, so every schematic in the hypotheses
survives as a `Var` and is `\<And>`-closed by `close_form` — a different question from
`can_inst = false`.  §6 names no probe at `can_inst = true`.

**Defence (condensed).**  The mechanism is read exactly backwards.  `subtract eq xs ys` removes
the elements of `xs` from `ys`, so fix level 1 computes **vars(premises) minus vars(conclusion)**.
For the check the conclusion has no variables, so level 1 fixes *all* of them — and level 2 fixes
the same set.  The two levels coincide on the check, `can_inst` cannot bite, and the proposed
probe would come out Refuted at both values.

**Ruling.**  Refuted, decisively.  `Pure/library.ML:852` is `fun subtract eq = fold (remove eq);`
over `:840` `fun remove eq x xs = … filter_out …` — the first argument is removed *from* the
second.  `reasoners.ML:403` is therefore vars(prems) \ vars(concl), and the author's own comment
at `:374-377` says the same in English: level 1 fixes "the conditions of the leading antecedent
only but leaves variables in the conclusion … free".  For the check, vars(concl) is empty, so level
1 fixes every hypothesis variable, and level 2 (`add_vars (leading_antecedent' th)`, :405) fixes
the same set.  `Variable.import_inst` maps each to a fresh `Free`, before `f ctxt' th2` is ever
called (reasoners.ML:409-420).  No residual `Var` reaches `close_form`, `r_nitpick` is not even
given `can_inst` (reasoners.ML:1306, called at :1549), and after the plan `can_inst` has no effect
on a check at all.

This is not nitpicking — it is a substantive, cleanly cited claim that is simply wrong about the
direction of one library function.  But the demanded probe is the hypothetical-with-no-path-to-occur
that follows from the error, and §6's silence about `can_inst` is safe.

**Resolution.**  Nothing changes.  *Optional*: when the drafter rewrites §4.3(c) for F1/F2, one
clause may record that the check's conclusion carries no schematic variable, so the two fix levels
coincide on it and §6's probes exercise the same state at either `can_inst` — a clarification the
defence volunteered, not a finding.  No new probe.

---

## F7 — §6 item 4's corpus floor "unobtainable as written"

**REFUTED · none · NO_ACTION**

**Claim (condensed).**  (a) The floor names `analyze.py`, whose flip analysis needs two legs, and
§6 schedules one run with no baseline; the legs on disk are dated 2026-09-14 and predate §39.
(b) `analyze.py` cannot produce a per-attribute breakdown, and §4.7 promises the readers are
unaffected — one of the two must give.  (c) Because §4.5 changes every check's key, a check never
appears as a flip, so "0 flips" is satisfied even if every check regressed.

**Defence (condensed).**  (a) is wrong twice.  The floor names its own baseline — "the committed
stores" — which is observable in one leg through the `hit` counter `analyze.py` already prints and
through the loud guard warnings; the parent plan states the same floor the same way.  And a
post-§39 leg *does* exist: `V_on_dbg`, 2026-09-21, on `PhiTest_Arithmetic` with its imports, listed
in the finding's own `ls` output and walked past.  (b) is a true fact with a false conclusion: the
attributes are already in memory; §4.7 is a compatibility statement, not a promise that the script
is frozen.  (c) attacks a claim the plan never makes: the floor's population is "every **ordinary**
guard", and §4.5 says ordinary digests are byte-for-byte unchanged, so a check cannot enter it —
the very next clause of the same item handles checks separately.

**Ruling.**  Refuted.  I verified the decisive fact myself: `ai-artifacts/step5/V_on_dbg/` has an
mtime of 2026-09-21 13:53, `ANALYSIS_2026-09-14.txt:227` labels it "after 97be6d75",
`git log -1 97be6d75` is "Guard cache: the Quicksort regression fixed (plan rev 28, section 39)"
dated 2026-09-15, and `git merge-base --is-ancestor 97be6d75 1f3c2142` exits 0 — so §39 is *in* the
plan's base commit and the leg was run on top of it.  `ANALYSIS_2026-09-14.txt:265-266` even records
the V-versus-C2 comparison: 0 flips, 22 digests only in A.  §39's effect on this corpus is a known,
subtracted quantity.

On (c) I read §4.5 and §6 item 4 again: the floor is "every ordinary guard's digest and verdict as
before", and the checks are counted in the *next* clause by their own attribute.  The scenario the
finding fears is excluded by construction.

The residue — that `analyze.py`'s five print lines cannot, as committed, group by the new attribute —
is true and trivial: the attributes are already loaded (`analyze.py:20`), and a `grep -c` answers it.
Demanding that a design plan add a throwaway `ai-artifacts/` analysis script to stage 1's product-file
list, at a level of instrumentation rigour neither §6's other four items nor the parent plan's §38
applies, **is nitpicking**, and I say so plainly.

**Resolution.**  Nothing changes.  *Optional, costing one clause*: §6 item 4 may name `V_on_dbg` as
the leg to compare digests against for the decisions the stores do not cover (a Proved first decision
writes no entry, reasoners.ML:1551-1553), and may say how the check's records are counted.  Neither is
a condition.

---

## F8 — Nothing in the verification exercises a check on realistic hypotheses

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  Turning the slice off is the consumer whose cost is unbounded; neither half
of §6 measures it.  Every smoke construct is Nitpick-evaluable, so no probe can distinguish a genuine
consistency witness from a trusted one.  And §6 item 4's escape clause rests on an incomplete survey:
`Phi_System` does use `case_sum` and is in the corpus's import closure.

**Defence (condensed).**  "Unbounded" is false — the slice runs *after* the expensive step: `preprocess`
collects every premise (:177), runs the hooks (:178) and simplifies the whole implication (:188-192)
*before* slicing (:197-198), and what grows is only the term handed to Nitpick, which is capped twice.
"Every construct is Nitpick-evaluable" is contradicted by `BLIND_SPIN`, built precisely so Nitpick can
never refute it.  §6 *does* probe the slice — the undecided probe is the discriminator.  A timing
assertion in a decision-path theory would manufacture a flake, against the file's own stated discipline.
Adding a theory to the corpus would weaken the one floor that leg exists for.  What survives is the
parenthetical in §6 item 4, and the right repair is a measurement that already exists: the `V_on_dbg`
leg logs `refuter: {'-': 357, 'guard_simp_tac': 20}`, and `guard_simp_tac` is the check's path today.

**Ruling.**  The surviving clause is upheld; everything else is refuted, and the defence's repair is
better than the finding's.  Verified: `guard_refute.ML:177-199` has the slice strictly after the
preprocessing simplification; `reasoners.ML:1288-1296` and `guard_refute.ML:220-223` are the two caps;
`Guard_Decision_Smoke.thy:250-259` is `BLIND_SPIN`, "false, yet TRUE IN EVERY FINITE MODEL, so the
model refuter … can never exhibit a countermodel"; `:307-314` is the comment explaining why a timing
assertion would be flaky.  `PhiTest_Arithmetic.thy:1-8` does import `Phi_Semantics.*`, and
`/usr/bin/grep -rln case_sum Phi_System Phi_Semantics` returns `Spec_Framework.thy`, `Phi_Types.thy`,
`Phi_Type.thy`, while the same grep over `Phi_Examples Phi_Test` returns nothing.  So §6 item 4's
parenthetical offers, as a reason to expect no check, a fact that is true of `Phi_Examples` and silent
about the leg that carries those theories.  That is a wrong reason in a verification section.

And `ANALYSIS_2026-09-14.txt:227-232` gives the number the plan should carry: 20 decisions with
`refuter = guard_simp_tac` on this exact corpus, which is an upper bound on how many checks it holds,
already measured.

**Resolution.**  Replace §6 item 4's parenthetical with that measurement: the latest recorded leg of
this corpus (`ai-artifacts/step5/ANALYSIS_2026-09-14.txt`, the `V_on_dbg` block of 2026-09-21, 377
decisions) logs 20 decisions with `refuter = guard_simp_tac`, which is the path a check takes today
(§3 item 2); `Phi_System`'s `case_sum` users are inside the import closure, so the sum rules may fire
there; at most twenty of those decisions are checks, and §4.7's record attribute separates them from
ordinary guards the template's rewrite turned into `\<condition> False`.  Keep the escape clause.  No
probe is added, no timing is asserted, no theory joins the corpus.

---

## F9 — Stage P's exit condition is not observable in the environment it names

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  Stage P ends with "restart the Isabelle-MCP session … and confirm the three
render", and stage P's entire content is this one check, so it can be declared done without anything
having been checked.  "Render" is a jEdit text-area property; a headless server rasterises nothing.
`WORD_GLYPHS.md:225` states the step for jEdit and the plan swapped the tool while keeping the criterion.

**Defence (condensed).**  The last clause is a real mismatch and should be fixed.  The rest is refuted:
stage P lists four machine-checkable conditions before it, and the finding's own proposed items (1)-(3)
are the plan's existing sentence handed back almost word for word.  The "symbol without a `font:` field"
failure has no path to occur — the generator writes that field into every entry it emits.  And whether
the three glyphs *draw* is already checked twice inside steps the stage lists: the generator's per-word
ink check runs on the written bytes in both modes, and the clipboard test rasterises under Xvfb.

**Ruling.**  Upheld on the one clause, refuted on the framing.  Verified: `build_word_glyphs.py:621-623`
is the per-word ink check ("U+%04X, which the clipboard text uses, draws nothing"), and `:874` runs
`check_font` unconditionally, *outside* `if args.check:`; `WORD_GLYPHS.md:219-224` says the clipboard test
"also draws the font, and fails if a word glyph or ordinary ASCII puts no ink on the page";
`WORD_GLYPHS.md:225` is "Restart the Isabelle/jEdit session and check the new symbol renders".
`build_word_glyphs.py:836-838` writes `font: %s` into every emitted line, so the blank-glyph hypothetical
cannot occur.  §4.9 says only "restart the Isabelle session" and needs no change — the finding mis-cites it.

Severity minor: this is one sentence in a preparatory stage that touches no ML and can produce no wrong
verdict.

**Resolution.**  In §5 stage P only: replace the final clause with a statement of what *is* observed —
the generator's ink check and the clipboard test's rasterisation carry the "do the glyphs draw" question,
and how the three look in a text area is checked by the author in his own jEdit after restarting it,
since a headless Isabelle-MCP server has no text area.  Move the Isabelle-MCP restart to the **head of
stage 1**, where `PLPR.thy` first uses the three symbols; a running session read `symbols-words` at
startup.  §4.9 is correct and stays.

---

## F10 — "exactly the three steps read the flag" is false by the plan's own §4.3(b), §4.5, §4.6, §4.7

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  The design has six reading sites and one of the three named consumers reads
nothing: `guard_digest` reads the flag (§4.5), `prove_or_refute` reads it three more times (§4.6, §4.7),
and R-conv never sees it, because §4.3(b) puts the test at the call site.  The asymmetry is the right
shape and should be kept — but the glossary must say so.

**Defence (condensed).**  Full concession.  §0:30-33, §1:77-79 and §4.1:180 all state the claim, and
§4.3(b), §4.5, §4.6, §4.7 all contradict it.  Four functions branch on the flag, not three.  The
propagation path is concrete: §5 stage 1 item 2 sends the signature block's comments to be rewritten from
this design.  Two trims: §4.3(b) already states the asymmetry's reason, so the glossary should point at it
rather than duplicate it; and the finding's own counts are off by one each, so the corrected text should
name the sites rather than count them.

**Ruling.**  Upheld.  This is an internal contradiction in the document under review, and there is no
reading under which both halves stand.  Verified in the plan itself and against the code:
`r_conv` is `reasoners.ML:1131` and the test would sit at `:1548`; `guard_digest` is `:1633-1634`;
the warning choice is `:1568` over `:1371-1378`; the record's attributes are `:1358-1364` and the trace
line `:1581-1587`.  A glossary whose normative clause the design's own §4.5 contradicts is not a matter of
wording preference: the glossary is the plan's terminology contract, and this one is on a direct path into
`reasoners.ML:80-198`.

The R-conv / R-nitpick asymmetry is right and stays: R-conv is switched off from outside because it has no
check-variant to write; R-nitpick is weakened from inside because its slice has one.

**Resolution.**  Split the two ideas in §0, §1 and §4.1.  Three steps whose **validity** rests on the
assumption — the `quick_cut` inside `guard_simp_tac`, R-conv, and the slice inside R-nitpick — and four
functions that **branch** on the flag: `guard_simp_tac`, `Phi_Guard_Refute.preprocess`, `prove_or_refute`
and `guard_digest`.  Name the sites rather than counting them; point at §4.3(b) for the asymmetry's reason
instead of restating it.  §5 stage 1 item 2's comments follow the corrected wording.

---

## F12 — Eight live uses in `Phi_BI`, not twenty; four live callers, not five

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  Twelve of the twenty `\<condition> False` in `Phi_BI.thy` sit inside comment
blocks and never load, so §6 item 3's floor ("the twenty uses load through the new display") is unmeetable.
Separately, the out-of-run instance has four live callers, not five.

**Defence (condensed).**  Conceded, with one addition and one refinement.  The four live lemmas are
exactly the ones registered (`Phi_BI.thy:6327`, `:6335`), and the primed variants are commented out
*inside those argument tuples* (`:6331`, `:6339`) — so the exclusion is recorded at the registration site
too.  The finding omits the fourth occurrence of "twenty" at §4.8, which must go as well, or the plan will
carry two senses of the same word.

**Ruling.**  Upheld; I counted it myself.  `/usr/bin/grep -c 'condition> False' Phi_BI/Phi_BI.thy` = 20;
the six comment blocks (:5953-5959, :6028-6034, :6231-6236, :6237-6247, :6248-6255, :6273-6279) hold
twelve of them; the eight live ones are two each in `ToA_case_sum_src` (:6217), `_R` (:6224), `_W` (:6257)
and `_WR` (:6264).  All four commented-out `if`-branching occurrences are among the twelve, so **no live
`if`-branching rule uses the check** — which, as the finding says, makes §6 item 4's escape clause more
likely, not less, and ties it entirely to whether the corpus performs a sum-type case split.  Callers:
`local_value.ML:169`, `toplevel0.ML:387`, `generic_variable_access2.ML:182` and `:272` are live;
`application.ML:137` sits inside the comment opened at `application.ML:112` and closed at `:141`.

**Resolution.**  §0 and §3: "the eight live uses", naming the four sum-type rules and recording that twelve
further occurrences sit in commented-out lemmas whose registrations are themselves commented out.  §4.8:
drop the number rather than restate it.  §6 item 3: "the eight live uses load through the new display".
§6 item 5: "one of its four callers".

---

## F13 — A second copy of `undecided_guard_warning`

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  §5 stage 1 item 2 adds `undecided_check_warning` beside
`undecided_guard_warning` — a second copy of the same eight-line function differing only in its two text
lines — and §4.6 then has to *require in prose* that the two agree.  The same file already contains the
answer: `loud_guard_warning ctxt who goals` parameterises instead of existing twice.

**Defence (condensed).**  Conceded without reservation, and with the decisive precedent the finding did not
have: the parent plan records that a duplicated undecided-guard warning was **already** found and removed
once by an earlier adversarial review.  The author has not ruled on the packaging (ruling 4 approves the
level and the wording, both of which survive byte-for-byte); neither warning is in the signature block, so
the change is internal; and the smoke test matches headline prefixes, so §6 is unaffected.

**Ruling.**  Upheld.  Verified: `reasoners.ML:1371-1378` and `:1382-1386` are the two functions, and
`loud_guard_warning` has **two** call sites (`:1565`, `:1567`) with two different values of `who` — a
better precedent than the finding's single-call-site claim.  `GUARD_CACHE_QUICK_MODE_PLAN.md:2628-2629`
records the earlier removal: "The undecided-guard warning existed twice in `reasoners.ML`; `guard_race`'s
inline copy now calls `undecided_guard_warning`, defined above it."  Re-creating deliberately what a
previous review of this same pipeline deleted is not defensible, and §4.6's "the same gate …, the same
rendering" is an invariant asked to be remembered where the file's own sibling shows how to make it
structural.  The author's first criterion decides it.

**Resolution.**  One function, taking the flag it is already holding and selecting its two texts from it:
the gate, the per-goal loop and `Goal_Display.pretty_a_goal` then exist once and §4.6's requirement becomes
structural rather than a promise.  Amend §5 stage 1 item 2; in §9's pending-names list, replace
`undecided_check_warning` with the merged name.  §4.6's approved four lines of text are untouched, colon
included, and §1's glossary term "the undecided-check warning" stays — it names the message the author
ruled on, not an ML identifier.

---

## F15 — The new `\<^descr>` will contradict the stale one in the same block

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  §4.8 adds a paragraph describing the modern pipeline to the text block that
documents `\<condition> P`.  The existing paragraph still says the assertion "is attempted with a weak but
safe solver (usually @{method clarsimp})", which is now true of `\<condition>[\<safe>] P` and false of
`\<condition> P`.  The block would tell a reader two incompatible stories, and the new paragraph's "Unlike
every other guard" would be measured against a wrong description of the others.

**Defence (condensed).**  Conceded, with two corrections.  The defect does not depend on adjacency — the
plan does not pin where the new `\<^descr>` lands.  And half the proposed fix cannot be carried out: the
block has **no** `\<^descr>` for `\<condition>[\<safe>] P`, so "move the clarsimp sentence there" would mean
writing a new paragraph about a guard variant this plan does not touch.  The clarsimp claim is dropped from
the `\<condition> P` paragraph and at most survives as a parenthetical.  Also: the plan cites the block as
:208-224; it is :210-226.

**Ruling.**  Upheld.  Verified: `PLPR.thy:210-226` is the block, with exactly two `\<^descr>`s, at :213
(`\<condition> P`) and :219 (`\<premise> P`); :214-217 carries the clarsimp sentence; `PLPR.thy:2005-2006`
registers `\<condition> ?P` to `guard_condition_judge` and `:2011-2012` registers `\<condition>[\<safe>] P`
to `safe_obligation_solver`, whose `clarsimp_tac` is built at `reasoners.ML:1657-1659` and applied at :1666.
No clarsimp appears anywhere on `\<condition> P`'s path.  Nothing in §2, §7 or §8 rules on this paragraph,
and `grep -n "weak but safe\|clarsimp" Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` returns nothing, so it is not a
re-argument of a decided point.

**Resolution.**  In the same edit, bring the `\<condition> P` `\<^descr>` up to date: the assertion is
decided by the guard machinery under its own bounds — the guard-side simplification, P-auto, the refuters
and the judge — so that an unprovable assertion cannot loop the reasoning; `\<condition>[\<safe>] P` is the
weak-but-safe variant, named in a parenthetical or dropped, **not** given a paragraph of its own.  Add the
correction to §5 stage 1 item 3 so it is not lost, and to §9's pending list so the author rules on it with
the rest of §4.8.  Correct the citation to :210-226.

---

## F17 — Two body comments and the smoke header's reachability constraint are off the checklists

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  (a) §5 stage 1 item 2 scopes its comment list to the signature block, but two
comments in the **body** of `reasoners.ML` state `prove_or_refute`'s argument list verbatim and become
wrong when the flag is prepended.  (b) §5 stage 1 item 4 mentions only the smoke header's summary line; the
header also carries a reachability constraint that every probe is asserted to obey, and two of §6's new
probes break it deliberately.

**Defence (condensed).**  Conceded.  The second body comment is the one that earns it: `reasoners.ML:1596-1600`
is the verbatim twin of the signature block's "UNSIMPLIFIED" sentence the plan already schedules, and §4.4's
"the factory … untouched" tells the implementer there is no reason to open that function.  The header's
existing wording forces the edit anyway: "The one exception" cannot survive the arrival of two more.

**Ruling.**  Upheld.  Verified: the signature block is `reasoners.ML:1-198` (`end` at :198, `structure` at
:201) and contains no occurrence of "warning"; `:1430-1432` is `prove_or_refute`'s own header comment spelling
out "can_inst, the guard-side context, the guard digest, then the run's state"; `:1596-1600` says the factory
ends "in the solving function `solve`, of prove_or_refute's type", which is true only once the flag is applied;
"UNSIMPLIFIED" occurs once, at :88.  `Guard_Decision_Smoke.thy:14-20` is the reachability constraint with its
single named exception, and §6's "simp finds the contradiction" probe is expected to be closed by
`guard_simp_tac` while "the regression probe" is an equation guard — both deliberately outside it.  Asking a
plan's checklist to be complete where it already enumerates six comment sites is asking it to be consistent
with itself, not asking for rigour it does not have.

**Resolution.**  Extend §5 stage 1 item 2's parenthesis to the two body comments (:1430-1432 and :1596-1600),
noting that the factory's **code** stays untouched (§4.4) and only that sentence of its comment changes.
Extend item 4: the header's reachability constraint gains a second exception — the check's probes are decided
by `guard_simp_tac` or by P-auto on a `False` conclusion, and the regression probe is an equation guard on
purpose.

---

## F18 — §6's probe assignments: no probe named for the slice, and the method probed nowhere

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  (a) Probe A ("simp finds the contradiction") guards nothing, because the subgoal
closes and `quick_cut` never runs, yet the plan presents it as the probe of consumer (a).  (b) No probe is
named for the slice; probe C cannot discriminate it, probe E can.  (c) Stage 1 edits the method
`\<phi>guard_P_auto` and §6 probes it nowhere.

**Defence (condensed).**  (a) refuted, and self-contradictory: the plan never says probe A guards consumer
(a), and it *does* name probe C as the probe that reads "guard_simp_tac" if the cut is still on — which the
finding itself quotes approvingly under (b).  (b) half conceded: probe E is indeed the slice's discriminator
and the plan should say so; making probe C "E's control" is refused, since probe C already carries two roles
and its title says "consistent hypotheses".  (c) the gap is real, but the proposed probe is wrong: the
method's context is **not** the factory's `guard_ctxt`, so it carries no `Premise_def`, the tag is never
unfolded, and `quick_cut` can only ever fire there on a **bare** `False` conclusion.

**Ruling.**  (a) refuted — I re-read §6 item 2 and the plan assigns consumers (a) and (b) to probe C in so
many words.  (b) upheld in its first half: with the slice on, `grow` starts from `frees_of (Trueprop False)`
= `[]`, every premise is dropped, Nitpick refutes `False` alone, and probe E would read `("refuted", "none",
"R-nitpick", "-")` instead of the asserted `("unknown", "none", "-", "-")`; probe C cannot discriminate,
because `CHAIN xs = True` (Guard_Decision_Smoke.thy:264-266) gives a model either way.  (c) upheld with the
defence's correction, which I verified: `Premise_def` is declared into `\<phi>guard_refute_simp` only
(PLPR.thy:1967) and added explicitly to the factory's `guard_ctxt` (reasoners.ML:1615); `enhance_for_guard`
(reasoners.ML:1059-1060) merges the ambient simpset with `\<phi>guard_simp`, which carries no `Premise_def`.
And `/usr/bin/grep -rn guard_P_auto --include='*.thy'` finds only the `method_setup` itself — the method has
no caller anywhere, so no corpus run can cover it.

**Resolution.**  Add one sentence to §6's undecided probe naming it as the probe of the slice, with the
reading it would give if the slice were still on.  Add a §6 item for the method: it has no caller, so it gets
a two-line probe of its own, and the probe must use a **bare** `False` conclusion, because the method's
context carries no `Premise_def` and `quick_cut` cannot fire on the tagged spelling there —
`lemma "FALLS <elim_chain> \<Longrightarrow> False" by \<phi>guard_P_auto` must now succeed, with a negative
control that must still fail.  Qualify §7's fourth bullet accordingly: for the method the cut is lost only on
a bare `False` conclusion.  Do **not** re-label probe A or probe C.

---

## F19 — §1's and §3's account of `assume_consistent_of`

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  (a) §1 defines the check "as written" under a premise tag and then says
`assume_consistent_of` is false for a `False` conclusion "tagged … or bare"; drop "or bare".  (b) §1's reason
"selected by the registered patterns (PLPR.thy:2005-2009)" holds for `guard_condition_judge` only;
`guard_condition_solver'` has no registration.  (c) §3 cites `reasoner.ML:308` for the runtime dispatch, but
that line belongs to a reasoner-deletion utility.

**Defence (condensed).**  (a) refuted, and the proposed fix is a regression: `assume_consistent_of` is total
on goal states, and the bare case is the one the method `\<phi>guard_P_auto` meets — its goal carries no tag
and it never passes through `oblg_template`.  Delete "or bare" and the method would fail on
`H \<Longrightarrow> False` through `quick_cut`, which is the behaviour §0 exists to remove.  (b) and (c)
conceded, with the correction that the finding's own replacement wording ("cannot change a verdict") is false:
the out-of-run instance's verdict *can* change, in the one safe direction — it has no refuter and no judge, so
losing the cut can only turn a failure into a proof.

**Ruling.**  (a) **refuted**, and the defence is right about the direction: the method is
`SIMPLE_METHOD (Phi_Reasoners.p_auto_attempt ctxt)` (PLPR.thy:1972-1974) applied to a raw Isar goal, and
`oblg_template` tags an untagged major premise only *after* the flag has been read (reasoners.ML:383-385,
with `Premise_D` at PLPR.thy:232).  "Or bare" is load-bearing.  (b) **upheld**: `PLPR.thy:2005-2009` registers
`guard_condition_judge` twice and nothing else; `guard_condition_solver'`/`solver1` have no registration and
are called from ML at four live sites.  (c) **upheld**: `reasoner.ML:306-311` is `match_reasoner_name`, whose
only callers are `:727` (deletion) and `:1078` (listing); the live dispatch is `:849-851` through
`Phi_Help.strip_meta_hhf_bvs`.  The plan's *claim* is true at that line too — only the pointer is wrong.

**Resolution.**  Keep "or bare" and explain it: the bullet above names guards, this function is total on goal
states, and the bare case is what the method meets and what the out-of-run instance meets on an untagged
antecedent.  Replace §1's first reason: into `guard_condition_judge` only `\<condition>` guards arrive, by the
registered patterns; `guard_condition_solver'` has no registration and is called from ML at four live sites,
where the flag's only reachable consumer is the cut inside `guard_simp_tac`, since that instance has no refuter
and no judge — so switching the cut off can only turn a failure into a proof, never the reverse, at the cost
of P-auto's bound.  Change §3's parenthetical to cite `reasoner.ML:849-851` and name
`Phi_Help.strip_meta_hhf_bvs`; keep `Logic.strip_assums_concl` in `assume_consistent_of` and say why — it is
what `quick_cut` uses (reasoners.ML:976), so the check and the cut it switches off read the goal the same way
by construction.  Correct §6 item 5's "five callers" to four (also F12).

---

## F23 — Stage P leaves hand-maintained counts stale

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  Three committed documents state the number of word symbols by hand and one also states
the code-point range; the generator writes none of them.  Adding three words makes them all wrong, and stage
P's "Nothing else changes in this stage" forecloses the fix.  `phi-font-readme.txt` travels with the bare
`.ttf`, so that one is user-visible outside the repository.

**Defence (condensed).**  The core is conceded, with the precedent the finding did not find: `UI_FONT_PLAN.md`
carries, as a numbered work item, "Fix the stale count at `:84`" — this exact number in this exact file has
gone stale once before and needed a dedicated plan item to repair.  The severity ground is refuted: the
generator's own comment says the notices go in the font's **name table** *because* the file travels alone; the
readme does not ship with the detached font.  The file list is incomplete — five sites, not three, and a sixth
must be **excluded** because it records the earlier stale value as history.  The "let the generator write the
count" alternative is declined: it cannot own a range sentence or a derived count, and it would enlarge
`--check` inside a preparatory stage of a guard plan.

**Ruling.**  Upheld on the core, refuted on the severity ground, and the defence's file list is the correct
one.  Verified: `build_word_glyphs.py:57` is `GENERATED = (ARTEFACT, SYMBOLS_OUT, CLIPBOARD_OUT)  # everything
a run writes`; the five hand-maintained sites are `fonts/WORD_GLYPHS.md:256` ("2048 code points, 135 in use"),
`fonts/phi-font-readme.txt:84` ("135 of them occupy U+E000..U+E086"), `jedit/WORD_CLIPBOARD_PLANS.md:20-21`
(count **and** range), `jedit/DRAG_AND_DROP_PLAN.md:221-222` (count and range) and `:457` ("13 of the 135
words"); `jedit/UI_FONT_PLAN.md:330-331` is the one to leave alone.  `symbols-words` line 2 reads
`0x00E086`, consistent with 135 contiguous points, so the numbers are exact today and will be wrong by three
the moment stage P runs.  The precedent settles whether these are live statements: they are, and nobody
remembered last time.

**Resolution.**  Replace stage P's "Nothing else changes in this stage" with the hand update of the five sites
(`WORD_GLYPHS.md:256`, `phi-font-readme.txt:84` including the range, `WORD_CLIPBOARD_PLANS.md:20-21`,
`DRAG_AND_DROP_PLAN.md:221-222` and `:457`), explicitly **excluding** `UI_FONT_PLAN.md:331`, and name those five
files in the stage's commit sentence beside the three the generator writes.  Add one clause to §4.9: `--check`
verifies the three generated files **and only the three**; the count and the range stated in the component's
prose are hand-maintained.  Do not adopt the generated-count alternative here; if the author wants that class
of staleness gone, the place is `WORD_GLYPHS.md`'s "Adding or changing a word" procedure, as a separate
proposal against the font pipeline.

---

## F24 — Stage P cannot separate "the committed files are stale" from "the local fontTools differs"

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  Stage P runs `--check` only *after* `words.txt` has been edited and the generator
re-run, so it cannot distinguish the two causes its own failure message names.  If the local fontTools differs
from the one that built the committed font, the regeneration rewrites the whole font, the later `--check`
passes, and a whole-artefact binary diff is committed silently under a change that was supposed to add three
words.

**Defence (condensed).**  The ordering fix is conceded and is cheap: `--check` writes nothing, every write
being under `if not args.check:`, so a pre-flight is safe in this shared working tree.  "Committed silently"
overstates: `check_font` runs unconditionally on the built bytes and the clipboard test rasterises, so a
toolchain change that *damages* the artefact is caught by steps the stage already performs; what escapes is
byte churn with no behavioural effect — a provenance and diff-hygiene defect, hence minor.  The pre-flight is
also more informative than the finding argues: the two text outputs are built from `rows`, so a stale
`words.txt` makes all three files stale while a fontTools change touches `PhiSymbols.ttf` alone.  A version
**pin** is refused: that changes the font component's contract and is not this plan's business.

**Ruling.**  Upheld on the ordering, refuted on the escalation.  Verified: `build_word_glyphs.py:861-871`
puts every write under `if not args.check:`, and `:874` runs `check_font` outside `if args.check:`;
`:688-695` is the failure text naming fontTools as the unpinned input; `fonts/PhiSymbols.ttf` is 484300 bytes
with an mtime of 2026-08-20 19:35.  A non-mutating pre-flight that makes every later result attributable to
the three words is exactly the shape the author's first criterion prefers, and it costs one command.  I also
agree the pin is out of scope.

**Resolution.**  Make `python3 fonts/build_word_glyphs.py --check` on the untouched tree the **first** action
of stage P, and say what its outcomes mean: a pass makes the whole `PhiSymbols.ttf` diff attributable to the
three words; a failure naming all three generated files means the committed files are stale; a failure naming
`fonts/PhiSymbols.ttf` alone means the local fontTools differs from the one that built it — the only unpinned
input, STIX being version-asserted (build_word_glyphs.py:79, :208-218) — and then stop and ask, because
regenerating would rewrite the whole font inside a commit that adds three words.  No version pin, no change to
`WORD_GLYPHS.md`'s procedure.

---

## F25 — §8's open question about a cut mark can be closed now

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  §8's first rejected alternative ends "Whether a cut mark on the dedicated reasoner
would stop the backtracking after a failure was not verified".  It can be settled from the source, and the
answer strengthens the rejection: no cut mark can stop backtracking after a failure, because the cut mode is
consulted only on the branch that pulled a result.

**Defence (condensed).**  Conceded, with one correction to the proposed wording: once the property is shown not
to exist, the trailing "the one-reasoner shape needs no such property" is vestigial and should be replaced by a
statement that the alternative's cost is therefore unconditional.

**Ruling.**  Upheld.  Verified decisively: `/usr/bin/grep -n cut_mode reasoner.ML` shows the loop reads
`cut_mode` at exactly one place, `:858`, and that `val Z = case cut_mode of GLOBAL_CUT => … ` block sits
entirely inside the branch opened at `:809`, `of NORMAL (SOME ((ctxt,th), seq')) =>`.  The no-result branch is
`:892`, `| NORMAL NONE => loop (N, iter, backtracking, L'::L, subgoal_statistics)`, which continues with the
remaining candidates for the same antecedent and never mentions `cut_mode`.  §8's declared purpose is that the
alternatives are not re-proposed, and this alternative is recorded as "the 2026-09-11 idea's shape", i.e. it has
been proposed once already.  A rejection resting on an unverified guess is the door the next reviewer pushes on,
and closing it costs three lines the plan's own standard (a cited file:line) already demands everywhere else.

**Resolution.**  Replace the bullet's last sentence with the verified fact and its citations: a cut mark on the
dedicated reasoner cannot help, because the registered cut mark is read only where a result was pulled
(reasoner.ML:786, :853-854, :858-887, inside the branch at :809), while a reasoner whose tactic yields nothing
falls through at :892 to the remaining candidates — here PLPR.thy:2005-2009.  The alternative's double
simplification and its digest from the other path are therefore unavoidable in that shape.  No design change.

---

## F11 — The factory's front `quick_cut 1 th` is dead and should be deleted

**REFUTED (nitpicking) · none · NO_ACTION**

**Claim (condensed).**  §3 item 1 justifies leaving the factory's `quick_cut 1 th` alone by a measurement; the
reason it never fires is structural and stronger — it can never fire on *any* guard.  Leaving a dead cut in
place is not neutral, because the check's immunity there *is* the deadness of that cut; delete both dead calls,
as the author did with `is_F`.

**Defence (condensed).**  The factual core is true and buys nothing.  §3 item 1 states the structural reason
**first** and labels the measurement "Evidence"; the tag invariant is already in §1's glossary with the same
citations.  Nothing is "remembered": the tagging is unconditional, two lines above, in the same function.  Both
escape hatches have no path to occur — untagging `oblg_template` would make the template's own rewrite raise
`CTERM`, break `fast_inst`'s dispatch and moot the `Premise_def` in the guard-side simpset, and the factory body
is an anonymous lambda with no other caller.  The `is_F` analogy is false: `is_F` was a *live* 250 ms branch
special-cased on the check; `quick_cut 1` is a no-op.  And deleting `:1661` drags `safe_obligation_solver`, which
is not on the check's path, under §6's corpus floor.

**Ruling.**  Refuted, and **this is nitpicking** — I say so plainly, as the author's third criterion asks.
The observation is correct and worth knowing: `major_prem_of` is `Logic.strip_assums_concl` of the first premise
(`Pure/thm.ML:541-544`), `oblg_template` wraps an untagged major premise with `Premise_D` (reasoners.ML:383-385),
`premise_tag_conv` keeps the tag (PLPR_Syntax.ML:39-44), so neither `quick_cut 1` call can ever see a bare
`Trueprop False`.  (Both calls are downstream of `oblg_template`: `safe_obligation_solver` goes through it too,
at reasoners.ML:1653.)  But a no-op is not an invariant anyone is asked to remember, the demanded change is
justified by a hypothetical that would demolish PLPR's central term invariant long before the cut mattered, the
factory body is unreachable except through the template that does the tagging, and the change is not free.
I also checked §3 item 1 and the finding mischaracterises it: the structural reason is stated first, in the same
sentence as the citation of `quick_cut`, and "Evidence:" introduces the measurement as corroboration.

**Resolution.**  Nothing changes.  §4.4's "untouched, including its front `quick_cut 1 th`" is the right
instruction to give an implementer: do not wire the flag into that call site.

---

## F14 — `assume_consistent_of` returns the bare bool §1 forbids

**REFUTED (nitpicking) · none · NO_ACTION**

**Claim (condensed).**  §1 forbids a bare bool "wherever it is passed", then defines
`assume_consistent_of : thm -> bool`, forcing `{assume_consistent = assume_consistent_of th}` to be written by
hand at four sites.  Give it type `thm -> {assume_consistent: bool}` and the record constructor occurs once.

**Defence (condensed).**  §1's rule governs **argument** positions and says why: `can_inst` survives as a bare
bool argument exactly where the flag joins it.  `assume_consistent_of`'s argument is a `thm`, so no call of it
can be confused with `can_inst`.  The proposed fix promises enforcement SML cannot deliver — record types are
structural, so `{assume_consistent = true}` stays well-typed from anywhere.  "Occurs exactly once" is false even
with the fix: §6's digest-marker probe writes both literals by hand.  And the local idiom argues the other way:
`{can_inst = …}` is a hand-written literal at every one of its sites and there is no `can_inst_of`.

**Ruling.**  Refuted, and **this is nitpicking**.  The point's load-bearing sentence — that the plan's rule is
"one people must remember rather than one the types enforce" — is false, because the proposed type enforces
nothing: `{assume_consistent = true}` remains constructible anywhere, and making it unconstructible would need
an abstract type incompatible with the plan's own pattern-destructuring consumers (`guard_simp_tac
{assume_consistent} ctxt th`).  I verified the idiom: `/usr/bin/grep -rn "{can_inst = \|{can_inst="` finds the
literal written by hand at fifteen sites across `PLPR.thy`, `reasoners.ML`, `local_value.ML`, `toplevel0.ML`,
`generic_variable_access2.ML` and the test theories, and `can_inst_of` does not exist.  Invoking the author's
first criterion for a change that leaves the invariant exactly as violable is criterion (3)'s case: a point of
taste wearing an enforced invariant's costume.  Four characters of spelling on four lines does not earn a
ruling-backed §1 being rewritten.

**Resolution.**  Nothing changes.

---

## F16 — Stage 1's file order and its re-evaluation instruction contradict each other

**REFUTED (nitpicking) · none · NO_ACTION**

**Claim (condensed).**  §5 stage 1 says "each file's edits complete before the next" and closes with
"Re-evaluate … after every `.ML` edit".  Item 1 changes `Phi_Guard_Refute.nitpick`'s arity and `reasoners.ML`
calls it four lines later in the same theory, so re-evaluating after item 1 is a guaranteed type error.

**Defence (condensed).**  The facts are right and the contradiction is manufactured.  The closing sentence fixes
the **tool, session and cadence** — Isabelle-MCP, `Phi_System_Base`, after each `.ML` edit rather than in one
batch, never `isabelle build`.  It nowhere says each re-evaluation returns clean; the contradiction needs the
premise "every re-evaluation must be clean", which is the reviewer's.  The intermediate evaluation is useful: it
typechecks the edited file against its own sealed signature and reports precisely one error at precisely one
line.  The hazard of "repairing" `reasoners.ML:1320` early requires writing the opposite of item 2, held in the
same list.  And the parent plan has **no** per-edit re-evaluation instruction at all, so this plan is already
stricter.

**Ruling.**  Refuted, and **this is nitpicking**.  Verified: `PLPR.thy` loads `library/guard_refute.ML` and then
`library/reasoners.ML` in the same theory, `guard_refute.ML:36` seals the structure opaquely, and
`reasoners.ML:1320` is the single call of `Phi_Guard_Refute.nitpick` outside the file
(`/usr/bin/grep -rn "Phi_Guard_Refute\."` finds only hook registrations besides it).  So the intermediate state
does not compile — and every ordered multi-file refactor has non-compiling intermediate states.  Asking a design
plan to certify which of them do is a demand for rigour beyond what the surrounding documents carry, and the
ordering sentence already communicates the dependency it is accused of hiding.

**Resolution.**  Nothing changes.

---

## F20 — Give the flag to `nitpick`, not to `preprocess`

**REFUTED (nitpicking) · none · NO_ACTION**

**Claim (condensed).**  Only `nitpick` needs the flag.  If `preprocess` returns the residue unsliced and
`nitpick` slices under the flag, one exported signature changes instead of two, and the justification sits where
the flag is read.

**Defence (condensed).**  Under the plan the flag is already read where the slice is applied — §4.1 says three
functions read it and §4.3(c) names `preprocess` as the one that slices, with §5 stage 1 item 1 sending the
comment to that same site; `nitpick` forwards, exactly as it already forwards `assms` and `goal`.  The proposal
does not "leave `preprocess` alone": it leaves its **type** alone while changing its **contract** — an exported
function advertising the same type with a different meaning, which is the shape criterion (1) rejects.  It also
breaks the file's one-place enumeration of weakenings inside `preprocess` (:44-47, :56-61, :170-173) and gives
`split_conjunctions`, which exists to serve the slice, a second caller in the search function.

**Ruling.**  Refuted, and **this is nitpicking**.  The defence's second argument is decisive and I verified the
signature: `guard_refute.ML:30` exports `preprocess : Proof.context -> term list -> term -> (term list * term)
option`, and under the proposal that type would be unchanged while the returned premises silently stop being
sliced.  The module's whole soundness story is that preprocessing only weakens, and today every weakening — the
hooks (:178), the simpset (:180-187), the slice (:198) — is enumerated inside one function under the header
`(*** The pipeline ***)` (:168).  Moving one out means a reader can no longer audit the chain by reading one
function.  Against that the point offers a diff count, and concedes in its own text that "nothing outside
guard_refute.ML sees the difference" — for a module with a single external caller (reasoners.ML:1320).  Arguing
about which of two functions inside one private module holds a conditional, in code that has not been written,
is a point of taste with no consequence.

**Resolution.**  Nothing changes.  (The build-then-strip round trip the point noticed at :197-199 is
pre-existing, untouched by this plan, and not removed by the point's own fix.)

---

## F21 — "Proving hyps ⟹ False IS finding the inconsistency" is not exact under `can_inst = true`

**REFUTED (nitpicking) · none · NO_ACTION**

**Claim (condensed).**  At `can_inst = true` the template's fix level 1 fixes nothing for the check, so
schematics in the hypotheses stay schematic and P-auto's instantiating steps can *choose* an instance under
which the hypotheses become inconsistent; a Proved check therefore asserts less than the plan says.

**Defence (condensed).**  The load-bearing sentence is exactly backwards — the same inversion as F6.  Fix level
1 fixes vars(premises) minus vars(conclusion); for the check the conclusion is closed, so it fixes *all* of them,
and they are imported to fresh `Free`s before the solving function is ever called.  There is nothing for
`Classical.instp_step_tac` to choose.  The remedy would also make the user-visible text worse: `\<condition> P`'s
existing `\<^descr>` carries no instantiation caveat, and the guard that *does* leave variables schematic is the
ordinary one — hedging only the check would tell the reader the opposite of the truth by contrast.

**Ruling.**  Refuted, and **this is nitpicking**: a hypothetical with no path to occur, built on the same
inverted reading of `subtract` as F6 (`Pure/library.ML:852`; reasoners.ML:403 with the author's own comment at
:374-377).  I verified that the fixing happens before `f ctxt' th2` (reasoners.ML:409-420) and that
`Variable.export_inst` runs only on the result (:421-424), so by the time `quick_cut`, `guard_simp_tac` and
P-auto see a check, its hypotheses carry no schematic term variable at all.  The only requested consequence is
to hedge three sentences — one of them user-visible — that are already true, with a hedge that would misinform.

**Resolution.**  Nothing changes.  §4.4's sentence, §1's verdict map and §4.8's `\<^descr>` stand as drafted.

---

## F22 — The abbreviation also spells guards the template's rewrite turned into `False`

**REFUTED (nitpicking) · none · NO_ACTION**

**Claim (condensed).**  The abbreviation folds the term, not its history, so after the template's rewrite an
ordinary `\<condition> (Suc n = 0)` *is* `Premise MODE_GUARD False` and prints as the new spelling while being
decided with the cut.  One clause in the `\<^descr>` removes the reader confusion.

**Defence (condensed).**  The plan already states the distinction three times, in the places that govern
behaviour (§1, §4.2, §4.5).  The cited path displays nothing: every probe asserts on the record's projection and
on counted warning lines, never on a printed goal.  Where the machinery does print goals, `prove_or_refute` takes
them from the state **after** `guard_simp_tac`, whose context carries `Premise_def`, so the tag is gone and only
`\<Longrightarrow> False` remains — which §4.6 says in the neighbouring paragraph.  And the proposed clause opens
"The spelling is display only", which is **false** in the direction that governs everything a user does:
`assume_consistent_of` reads the term as written, so a guard *written* with the spelling is always decided as the
check.

**Ruling.**  Refuted, and **this is nitpicking** on the path it cites.  Verified: `reasoners.ML:1479` takes
`goals` from the post-simplification state whenever one exists, and `:1615` puts `Premise_def` into the
guard-side context, so the printed goal is a bare `False`; §4.6 already says exactly this.  The probes assert on
`path_of` (Guard_Decision_Smoke.thy:63-68, :131-141) and on warning-line counts (:189-215) — the regression probe
prints no term.  The one residual path (the loud "by the simplifier" warning on an ordinary guard with a stale
Proved entry) needs an abnormal situation and reaches someone debugging the guard machinery, not a rule author.
Decisively, the proposed remedy would plant a false sentence in user-visible text.

**Resolution.**  Nothing changes.  §1 already draws the distinction for the reader who needs it.

---

## F26 — `Check_Hypothesis_Consistency` is out of step with its three neighbours

**REFUTED (nitpicking) · none · NO_ACTION**

**Claim (condensed).**  The three neighbouring abbreviations are noun phrases and — the observation billed as
removing the obvious counter-argument — not one of them transliterates its own symbol.
`Check_Hypothesis_Consistency` is an imperative and points the wrong way, since the proposition holds when the
hypotheses are *in*consistent.  Propose `Inconsistent_Hypotheses`.

**Defence (condensed).**  The factual lever is wrong: two of the three do echo their symbol's word.  Imperative
antecedent names are PLPR's house style.  The alleged consequence cannot occur through the proposed fix, because
the constant name appears at none of the sites cited — the twenty uses stay `\<condition> False` and print as the
spelling.  And the fix would give one concept a **third** vocabulary, pointing against the author's own chosen
spelling and his approved warning text.

**Ruling.**  Refuted, and **this is nitpicking**.  I checked the lever myself at `PLPR.thy:202-207`:
`Normal_Premise` / `\<premise>` and `Proof_Obligation` / `\<obligation>` both echo their symbol; only
`Simp_Premise` / `\<condition>` does not.  So the dominant pattern in the very three lines cited is the opposite
of what the point asserts, and a name echoing all three of the author's symbol words continues it.  Imperative
antecedent names are routine here — `Do` (:283), `Simplify` (:2092), `CHK_SUBGOAL` and `SOLVE_SUBGOAL`
(:2594-2597, both defined `\<longleftrightarrow> True`, i.e. named for the reasoner's action rather than the
proposition), `Push_Envir_Var` (:1275).  And the proposed rename would break the project's one-concept-one-name
rule against the author's approved warning text ("Fail to check the consistency of the hypotheses") and his own
spelling.  §9 already lists the constant name as pending the author, so the point's one operative instruction is
already what the plan does.

**Resolution.**  Nothing changes.  The name stays on §9's pending list, where the author rules on it.

---

## The relaxation proposals

### R1 — Hoist the refutation shortcut out of `guard_simp_tac` into `prove_or_refute`

**PROPOSE_TO_AUTHOR — recommend accepting, in the corrected form below.**

**Recommendation to the author.**  Take it.  `quick_cut` is the only part of `guard_simp_tac` whose validity
rests on the assumption and the only thing that can empty its sequence; moving it into `prove_or_refute` — the
one function that turns emptiness into a verdict — lets `guard_simp_tac`, `p_auto_attempt`, `p_auto_solving`,
`guard_condition_solver'` and the method `\<phi>guard_P_auto` keep today's signatures, removes PLPR.thy's ML edit
entirely, and puts the shortcut on the same line as the flag that authorises it.  What you are asked to give up
is the drafter's extension of your ruling 2 (the sentence about the out-of-run instance and the method computing
the flag at their own entrances — your own words covered only `guard_condition_judge`), plus accepting that those
two paths lose the cut for **ordinary** guards as well as for the check; §7 already accepts losing it there for
the check.

I verified the claims.  `guard_simp_tac` (reasoners.ML:1074-1084) is `Seq.take 1 (ALLGOALS (asm_full_simp_tac …
THEN_ALL_NEW quick_cut) th)` under a 60 s bound whose timeout path must return `SOME (th, Seq.empty)` precisely
because "an empty sequence would read as a refutation" (:1062-1068).  Nothing else there can empty the sequence:
`generic_rewrite_goal_tac` returns `Seq.single` for any in-range index (`Pure/raw_simplifier.ML:1518-1521`) and
`simp_loop_tac`'s continuation is `solve_tac i ORELSE TRY (…)` (`Pure/simplifier.ML:325-327`), which never fails.
`guard_simp_tac` has exactly three call sites, all in `reasoners.ML` (:1098, :1478, :1514).  And all four live
callers of the out-of-run instance are terminal: `guard_condition_solver1`'s failure callback is `error`
(reasoners.ML:1646-1650), and `generic_variable_access2.ML:182-185` supplies its own `error`.  So on any run that
does not abort, the cut never fires there and removing it costs nothing; when it does fire, the run was already
aborting and now waits at most `\<phi>guard_classic_prover_timeout` (400 ms) for its error message — and P-auto
may now prove such a goal, which is a completeness gain.  The method has no caller anywhere.

It also pays two debts you have already named: your ruling that `guard_simp_tac` is "standard simp" whose output
"is shared by P-auto, R-conv, R-nitpick and the judge — it is a step of the call" (guard plan §39 rulings 1-2) is
not quite true while its output for a `False`-concluded goal is *no state at all*; and it removes the one place
in the pipeline where a verdict is encoded as the absence of a result.

**Three corrections the drafter must apply before implementing, which the proposal as written gets wrong:**

1. The judge path's `NONE => error "The judge is broken…"` (reasoners.ML:1514-1516) must be guarded by the flag.
   Unguarded, it breaks the check: for a check, the judge answering `Provable` and the re-simplification leaving
   `hyps \<Longrightarrow> False` is the **normal** state.
2. Keep `goals` two-branched as it is today (reasoners.ML:1479: `th0` in the refuted-by-simplifier case, `th1`
   otherwise), so the loud guard warning and the record's `subgoals` field keep showing the guard as written.
3. Do not write `#1 (the (Seq.pull …))`; keep the total `case Seq.pull … of SOME (th,_) => th | NONE => th0`.

If you decline R1, the plan as drafted is sound and nothing else about it changes.

### R2 — Decide the check with the simplifier, P-auto and the judge only; skip R-nitpick

**DROP.**  Four reasons, three of them verified against the code.

1. **The symmetry with R-conv is false.**  R-conv is skipped because it has no assumption-free variant at all —
   its whole method is proving the negation of the conclusion, and stripping the assumption leaves nothing.
   R-nitpick's assumption-free form is the *stronger* procedure "find a model satisfying all the hypotheses at
   once", which is literally the question the check asks.  Skipping a component with no assumption-free content
   and skipping one whose assumption-free form is the procedure you need are not the same act.
2. **The judge is not installed.**  `reasoners.ML:1350` is
   `val judge : (judge_arg -> judgement) option Unsynchronized.ref = Unsynchronized.ref NONE`, with the comment
   "installed by ML code (phase 2: the LLM judge)".  Under R2, as of today, the check's commonest outcome would
   be decidable by nothing: P-auto can only prove, and the judge does not exist.  Ruling 3 puts the judge last,
   after the refuters; R2 would make an uninstalled phase-2 hook the check's primary decider.
3. **The cost comparison counts only the cold call.**  A Refuted check writes an entry, and a later run with a
   Refuted entry returns immediately (reasoners.ML:1557-1559) at about 1 ms.  An Unknown entry does not
   short-circuit: it goes to `judge_or_give_up` (:1547) after P-auto has already run.  So R2 does not lower the
   cost to 400 ms; it makes every live branch pay 400 ms on **every run, forever**, where the plan as written
   pays once and then hits warm.
4. R2's supporting worry about the level-1 warning is weaker than stated in the other direction too:
   `Phi_Reasoner.warn_pretty ctxt 1` is gated by `\<phi>trace_reasoning`, whose default is 0 (reasoner.ML:316,
   :337-340), so the undecided-check warning is silent unless the user raises the trace level.

R2 is a serious, honestly argued proposal raised in the right channel — it is not nitpicking — but it is wrong on
the merits.  Note that R2 and F1's code change were alternatives; with R2 dropped and F1's code change put to the
author as §9's open question, the plan's shape is unchanged.

### R3 — Make stage P a companion commit after the flag lands

**DROP.**  The form is legitimate — ruling 6 is exactly the kind of author preference a relaxation may test — but
the substance fails on four counts, and the proposal brings the author no information he lacks (decision 15, the
high-water rule and the pipeline are all his).

- It changes not one line of the result.  Criterion (4) admits a relaxation that makes the **result** markedly
  simpler or more elegant; this one reorders work.
- Every cost it prices is order-invariant: `WORD_GLYPHS.md:243-245` says the generator rewrites the font, the
  symbol table and the clipboard table together on **any** word change, and the clipboard round-trip is mandatory
  step 4 of the documented procedure whenever it happens.
- The one order-dependent item, the session restart, the reorder **adds**: §6 item 1 and item 3 measure the
  display, which needs the abbreviation, which R3 moves after stage 2 — one verification pass becomes two.
- It splits `PLPR.thy`'s edits across two commits, against stage 1's own "each file's edits complete before the
  next", and it postpones the plan's single flagged uncertainty (whether the abbreviation folds) until after the
  measurement that would have covered it.

The irreversibility framing is rejected as a hypothetical with no path to occur: the spelling is the author's own
from his opening design, the flag is computed from the term and not from the spelling, and the only flagged
uncertainty's fallback spells the same three words.  With F9 applied, stage P's exit condition is fully
machine-checkable, so R3's F9-based argument lapses as well.

### R4 — Carry the flag as an ML-only `Config` value

**DROP.**  Three reasons, the first decisive.

1. **It does not compile as proposed.**  `PLPR.thy` loads `library/guard_refute.ML` before
   `library/reasoners.ML` in the same theory, so `Phi_Guard_Refute.preprocess` cannot name a value declared in
   `Phi_Reasoners`.  The advertised gain "zero changes to guard_refute.ML's interface" would be bought by moving
   the flag's declaration *into* guard_refute.ML.
2. **"The smoke test needs no edit" is false, and fails silently.**  `Guard_Decision_Smoke.thy:74-79` computes
   the digest through the factory on the probe's own `ctxt`, which has passed no entrance, so `Config.get` would
   return the default `true` while `guard_condition_judge` computes the marked digest — the injected entry is
   written under a digest the guard never looks up, and every check probe with an entry silently takes the cold
   path.  Under the record that same omission is a compile error.
3. **The bit is goal-derived but the carrier is context-scoped, and the digest depends on it** (§4.5).
   `prove_or_refute` returns `ctxt0` plus the delta and PLPR.thy:2003-2006 says the run continues with it, so a
   `Config.put` at the entrance stamps the flag onto the ongoing context, and cache correctness would rest on
   "every path to a reader passes an entrance first" — the remembered invariant criterion (1) rejects.

The cited precedents are not precedents for this shape of value: `\<phi>guard_cache` is an attribute-backed user
switch and `ML_Options.debugger` is Isabelle's own, both constant across a run; and
`Phi_Reasoner_solve_obligation_and_no_defer` is user-reachable and is set with an explicit save-and-restore pair,
which demonstrates the ceremony a context-borne switch drags along.  Meanwhile `can_inst`, the flag's sibling, is
threaded as a parameter today.  Ruling 1's reason stands.

### R5 — Widen the factory's digest callback to take `th0`

**DROP as framed — but the drafter should apply the narrower refinement, which needs no relaxation.**

The observation is real: under §5 stage 1 item 4 the smoke helper `digest_of` would re-derive the flag by hand,
and a divergence would surface as "(no decision logged)" on every check probe rather than as a wrong flag.  But
the remedy damages an invariant the factory's type enforces today.  `reasoners.ML:1600-1602` states the contract —
the digest step computes, "on the state right after the case split and before the insertion", what `solve` is
given — and the callback type `Proof.context -> thm -> 'd` (:93) makes it impossible to violate.  Handing the
callback `th0` would say the digest may be keyed on the pre-template state, which is exactly the state
`guard_digest` deliberately does not hash.  Trading an engine-enforced invariant for a test-enforced one is the
wrong direction under criterion (1).

**The whole gain is available without relaxing anything.**  `guard_digest` has exactly two users in the
repository (reasoners.ML:1636 and Guard_Decision_Smoke.thy:76).  Let the judge instance export its digest step as
one value — `fun guard_digest_of th0 = guard_digest {assume_consistent = assume_consistent_of th0}` — and have
both `guard_condition_judge` and the test name that one value.  The factory's type, the two non-judge instances,
`solve`'s type and the obligation instance are all untouched, ruling 2's shape is preserved exactly, and the flag
line is written once in the system.  **The drafter applies this to §4.2 and §5 stage 1 item 4 as a plain
improvement; it is not a relaxation and needs no ruling.**

---

## Appendix A — dropped by the curator (one line each)

- *"For the check, an empty sequence out of `guard_simp_tac` still reads as 'refuted by the simplifier'"* — the
  mechanism is false: `asm_full_simp_tac` cannot empty the sequence (`Pure/raw_simplifier.ML:1518-1521`,
  `Pure/simplifier.ML:325-327`), so §4.3(a)'s unreachability holds by construction; two other lenses reached the
  same conclusion and self-dropped it.
- *"RELAXATION: spell the guard with the existing `\<premise>` word symbol"* — the spelling is the author's own,
  the gain is far below the "markedly simpler" bar, and `\<premise>` is already `Normal_Premise`'s notation, so
  the proposal introduces an ambiguity it does not examine.
- *"Sixteen live uses in `Phi_BI`, four live callers"* — the caller count is right and is kept in F12; the
  `Phi_BI` count was itself wrong (eight live, not sixteen).  Merged into F12 with the correct number.
- *"The method computes one flag from the first subgoal and applies it to every subgoal"* — a hypothetical with
  no path to occur: the method has no caller, writes no record, and can produce no refutation.  Its probe half is
  kept, in F18.

## Appendix B — self-dropped by the interrogators (one line each)

**diagnosis** — the undecided-check warning flooding the log (it is trace-gated, default 0); §4.3(a)'s
never-empty claim (holds, because `Premise_def` is in the guard-side simpset); `preprocess`'s `NONE` throwing away
a proof (no proof object exists); R-nitpick called with `ctxt` not `ctxt_g` (predates the plan);
`assume_consistent_of` on a premise-less state (§1 already rules it); the `\<r>if` rule's reachability
(unverifiable in session); one call mixing a check and an ordinary guard (no path to occur);
`Guard_Export_Smoke.thy:100` (unaffected, the type is unchanged).

**elegance** — the digest marker as a dirty hack (it is sound domain separation, and §4.5's need is stronger than
it claims); a dedicated constant instead of an abbreviation (superseded by the author on 2026-09-22);
`preprocess`'s `NONE` reported as "not refuted" (no elegant fix exists); the corpus possibly exercising no check
(speculative; §6 commits to reporting either outcome); the `.unicode.thy` twins (untracked generated artefacts);
"hypotheses" as a coined word (§1 records the mapping and the coinage is forced); the `\<^descr>` citing an ML
file (the file's own convention); `\<^computation_check>` (different namespace); the trace suffix's placement
(taste); dropping the flag from the out-of-run instance and the method (would make two paths decide the same
guard differently); the `:1511-1513` off-by-three (folded into evidence).

**verification** — §4.3(a)'s `simplified = NONE` (no path to occur); Nitpick choking on the 19-digit `fresh`
numeral (the committed probe already hands it one); probe H as a tautology (the only shape `run_guard` can
express); the new record attribute breaking existing readers (§4.7's claim is right); R-nitpick's worst case
(ruling 5 says 2000 ms **plus** the 5 s margin); §7's `\<r>if` bullet (a recorded accepted imprecision); the
plan's line numbers versus the working tree (within three lines throughout); §6 item 5 as vacuous (it is not —
`quick_cut` strips the premises before testing the conclusion).

**symbols** — `PLPR.unicode.thy` going stale (the author ruled it "完全不用管"); the `\<^descr>`'s bare cartouche
re-printing (it is the `cartouche` text antiquotation, not a term); §4.9 omitting the STIX requirements (both
installed at the asserted version); appending to `words.txt` out of alphabetical order (the file sanctions
appending); "the three" used for two referents in one paragraph; the `:208-224` off-by-two (kept, in F15); the
clipboard fold (no new word is in a proper-prefix relation with any of the 135); the judge's prompt (the
rendering is the hook's, outside this repository); a symbol-name clash (verified absent); a nullary
three-delimiter mixfix (`PhSm_Ag_Base.thy:551` already has the shape).

**relaxation** — no digest marker (the marker is load-bearing: the digest is computed **after** the template's
rewrite); not consulting the judge for the check (ruled "要问的", and the `max_potential = 0` variant is not
implementable); a definition instead of an abbreviation (superseded); the flag as a `Config.T` (raised as R4 and
dropped); splitting `Phi_Guard_Refute.nitpick` (would move the genuine/quasi-genuine handling into
`reasoners.ML`); making `r_conv` decline on a `False` conclusion by itself (the implicit-rule shape §8 rejects);
a check-specific solving function (would duplicate 150 lines of `prove_or_refute`); renaming so code and text
share one word (§1 records the split deliberately); the `:1511-1513` drift; §4.3(a)'s never-empty claim (holds);
the `*.unicode.thy` mirrors (gitignored); a shorter spelling (the author's own).

**consistency** — `guard_simp_tac` with `K all_tac` still emptying (false; §4.3(a) is correct); six off-by-one
citations that still land the reader on the right code; the method's one flag over several subgoals (no caller);
a Proved entry overturned by R-nitpick printing no loud warning (pre-existing for every guard);
`\<^computation_check>`; the `*.unicode.thy` mirrors; riding the flag inside `{can_inst}` (four of seven arity
changes would remain, and §8 rejected the factory route); dropping the digest marker; §3 item 1's stale
provenance (the claim is independently true by inspection); §5 stage 3's unnamed handoff file.
