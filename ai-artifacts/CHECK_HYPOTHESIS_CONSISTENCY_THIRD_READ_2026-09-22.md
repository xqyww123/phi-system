# Targeted third read of `CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md` rev 3 — the judge's report

- **Plan read**: `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md`, rev 3
  (2026-09-22), 1126 lines.  No code has been written.
- **Date**: 2026-09-22.
- **Shape**: three interrogation readers (mechanism, comment-fitness, consistency) →
  a curator, who dropped eight points → one fresh defender per surviving point → this
  judge.  Thirteen findings (F1–F13) and two relaxation proposals (R1, R2) reached me.
- **Why this read exists**: the second review's judge asked for it in as many words
  (`CHECK_HYPOTHESIS_CONSISTENCY_REREVIEW_2026-09-22.md:76-84`): "the passages that
  land in source comments and that this round found wrong … must be read once more
  before they are typed into `guard_refute.ML`.  That is a read of five passages, not
  another six-lens round."  The question is narrow: are these passages TRUE of the
  code, precise, and fit to be condensed into source comments beside the comments
  already there (`guard_refute.ML:82-84`, `:170-173`, `:202-208`;
  `reasoners.ML:1266-1286`)?
- **The five passages**:
  - **P1** — §4.3(a), the refutation by the simplifier moved into `prove_or_refute`
    (plan:348-422).
  - **P2** — §4.3(c), R-nitpick receiving the premises as antecedents (plan:425-496).
  - **P3** — §1's entry "the strict rail, the unknown-tolerant rail" (plan:134-155),
    read with `guard_kind` (:93-109), `guard_kind_of` (:110-124) and "the three steps"
    (:125-133).
  - **P4** — §7 whole (plan:874-932).
  - **P5** — §8's two bullets at plan:963-971.
  - **SECONDARY** (accuracy only) — §4.8's two `\<^descr>` paragraphs
    (plan:619-641).
- **Verification**: every citation this report relies on was re-read in this session
  with `/usr/bin/grep -n` and `sed -n`.  Nothing was built, no Isabelle, REPL or
  Isabelle-MCP was started, and no file was written but this report.  The working tree
  is at `6026b43e`; `git diff --stat 1f3c2142 HEAD` over
  `Phi_Logic_Programming_Reasoner/library/{reasoners,guard_refute,phi_nitpick}.ML`,
  `Phi_Logic_Programming_Reasoner/PLPR.thy` and
  `Phi_BI/library/tools/guard_refute_scrub.ML` is **empty**, so the plan's own line
  numbers (`1f3c2142`) are the ones below.
- **Vocabulary**: the plan's glossary (§1) and the guard plan's.  "Premises", never
  "hypotheses" (ruling 12).  Inferences are marked where they occur.

---

## Readiness: **MET_ON_CONDITION**

No blocker.  Nothing found in this read touches the design, and no ruling of §2 is
disturbed: ruling 9's hoist, ruling 10's antecedent shape, ruling 17's `false`, the
digest marker, the entrance-computed kind and the untouched factory all stand exactly
as rev 3 has them.  Every defect below is a sentence with an exact replacement.

Two of the thirteen are major and both are of one kind — a passage that says the
opposite of what the code does, in text scheduled to become user-visible or
source-comment text:

- **F6 (P1)**: §4.3(a) ends its account of `goals` with "so the loud guard warning and
  the record's `subgoals` field keep showing the guard as written" (plan:401-404).
  "The guard as written" is §1's and §4.2's defined phrase for the state *before*
  `oblg_template`, which §4.2 says "is visible there and nowhere later"
  (plan:321-323); no term inside `prove_or_refute` is that state.  And on the loud
  warning's judge branch `goals` is the *simplified* state, not `th0`.  The plan
  spends its own glossary phrase on the state the glossary excludes, and is false on
  one of the two branches it is summarising.
- **F7 (SECONDARY)**: §4.8's "light correction" replaces `PLPR.thy:214-215` and says
  "the rest of the paragraph stays" (plan:628-631) — which keeps `:216-217`,
  "Therefore, any rule protected by it is appliable only when the condition \<open>P\<close> is
  provable **using the safe solver**."  No safe solver runs on `\<condition> P`'s path,
  and after the replacement "the safe solver" has no antecedent left in the block.
  The user-visible paragraph would be left false *and* dangling.  Rev 2 had this
  right; rev 3's narrowing from two sentences to one lost it.

The remaining eleven are minor: one citation pointing at the wrong file (F10), one
comment attributed to the wrong function (F13), one glossary universal the rest of the
plan qualifies three times (F8), one summary clause that says an edited function is
unedited (F9), one missing link in an otherwise complete chain (F5), two enumerations
that are narrower than the code (F3, F4), two clauses that quantify more strongly than
the code warrants (F11 and half of F1), and one sentence filed where the previous
round ruled it must not go (F12).  One point is rejected outright as nitpicking (F2).

**Conditions gating stage 1:**

- **C-1 (F7, MUST_DISCUSS_WITH_AUTHOR).**  The author extends ruling 16's "light
  correction" to both sentences of the `\<condition> P` paragraph (`PLPR.thy:214-217`,
  not `:214-215`) and words the second one.  This is user-visible text and §9 already
  holds it open for him.  Without it the block ships a false, antecedent-less clause.
- **C-2 (the drafter applies, no re-review).**  F1, F3, F4, F5, F6, F8, F9, F10, F11,
  F12, F13 — each has one obviously right fix, stated below, and each is checked again
  in stage 3's code review with the code beside it.
- **C-3 (R1 and R2, the author's call).**  Both are put to him separately.  If R1 is
  **declined**, F4's and F10's edits to §4.3(c)'s enumeration are not optional: as it
  stands at plan:447-455 that enumeration is not true of the code.

With C-1 ruled and C-2 applied, the five passages are true, precise and fit to be
condensed into the comments §5 schedules.  Stage P is untouched by this read.

---

## The rulings

| id | passage | title | severity | verdict | disposition |
|----|---------|-------|----------|---------|-------------|
| F6 | P1 | "keep showing the guard as written" names a state `prove_or_refute` never holds, and is false on the judge branch | major | UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F7 | SECONDARY | §4.8's light correction leaves `PLPR.thy:216-217` standing — false, dangling, user-visible | major | UPHELD | MUST_DISCUSS_WITH_AUTHOR |
| F1 | P2 | "stays true and gains the check's case" / "extended" is the wrong verb; the rest of the charge fails | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F3 | P3 | §1 quotes the vendored patch comment's "typedef/class axioms", which §4.3(c) refutes sixty lines later | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F4 | P2, P3 | "the `user_axioms`-gated route is off" is not "no theory axiom in the tail"; §1 omits the assumptions' own generated axioms | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F5 | P1 | The totality chain proves non-emptiness; `Seq.take 1` is what caps the count, and the plan never names it | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F8 | P3 | "refute every check unconditionally today" is contradicted by §3 items 1-2 and §6 item 4 | minor | UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F9 | P1 | "Consequences: `guard_simp_tac` … keep today's code" — the one function in that list whose body changes | minor | UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F10 | P2 | `add_eq_axiom` is cited to a file it is not in | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F11 | P2, P5 | "the tolerant rail is the deliberate choice" / "the verdict would rest on it alone" over-quantify | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F12 | P4 | §7 carries the F18 measurement the second review ruled must not go there; §8 points back at §7 for it | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F13 | P2 | The assumption-parameter comment belongs to `nitpick`, not to `preprocess` | minor | UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F2 | P2 | "a countermodel makes every premise definitely true" allegedly contradicts §5's prohibition | none | NITPICK_REJECTED | NO_ACTION |

| id | passage | relaxation | recommendation |
|----|---------|------------|----------------|
| R1 | P2 | Record the routing RULE rather than the list of generated nondefinitional axioms | **PROPOSE_TO_AUTHOR** |
| R2 | P2 | Let stage 1 correct the two wrong COMMENT blocks of the vendored `phi_nitpick.ML` | **PROPOSE_TO_AUTHOR**, narrowed |

---

## F6 — "keep showing the guard as written" (P1)

**UPHELD · major · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(a) closes its account of `goals` with "`goals` stays
two-branched as today (:1479 — `th0` when the simplifier refuted, else the simplified
state), so the loud guard warning and the record's `subgoals` field keep showing the
guard as written" (plan:401-404).  Both halves fail.  (a) "The guard as written" is the
plan's own defined phrase for the state `guard_condition_judge` sees *before*
`oblg_template`; `prove_or_refute`'s `th0` is past the template's rewrite, past the
case split and past the aux-fact insertion.  (b) `goals` is `cprems_of th0` only on the
refuted-by-the-simplifier branch; on the loud warning's *other* branch — the entry said
Proved and the judge said Unprovable — the simplifier did not refute, so `goals` is the
simplified state.

**Defence (condensed).**  Conceded in full, having tried three defences.  On (a): §1
defines the check as concluding `False` "AS WRITTEN" and excludes a conclusion that
only *becomes* `False` by the template's rewrite (plan:76-80); §4.2 devotes a paragraph
to the distinction (plan:337-341) and fixes where the state is reachable (plan:321-323);
§8 records a rejected alternative that turns on the same fact (plan:950-952).  On (b):
every path to `judge_answer = SOME "Unprovable"` runs through `decide`, which is called
at one site only, in the `SOME (th, _)` arm.  The escape route "the sentence is merely
inherited from the first review's R1" is aggravating, not exculpating: REVIEW:1181-1182
was written before §4.2 made "as written" a defined phrase.  One refinement: `goals`
feeds four consumers, not two.

**Ruling.**  **Upheld**, and I traced both halves myself rather than take either side's
word.

(a) `gen_guard_condition_solver` opens with `oblg_template`
(reasoners.ML:1610-1611); inside it, an untagged major premise is tagged
(`@{thm' Premise_D[where mode=default]} RS th00`, :383-385) and the tag's content is
rewritten (`PLPR_Syntax.premise_tag_conv (K true) (Simplifier.full_rewrite ctxt)`,
:386-387).  The aux facts are inserted at :1622 and `solve` — that is,
`prove_or_refute` — is reached only at :1623, after the case split at :1619.  So the
`th0` `prove_or_refute` receives is post-rewrite, post-split, post-insertion.  §4.2
says "the guard as written … is visible there and nowhere later" (plan:321-323) and §1
says a conclusion that only becomes `False` "is not the check" (plan:78-80).  The
plan therefore asserts in three places that no term inside `prove_or_refute` is the
guard as written, and then says two of `prove_or_refute`'s outputs show exactly that.

(b) reasoners.ML:1479 is
`val goals = Thm.cprems_of (case simplified of SOME (th, _) => th | NONE => th0)`.
`judge = SOME "Unprovable"` is produced at exactly one site, `consult`'s `Unprovable`
arm (:1524-1526); `consult` is called only from `judge_or_give_up` (:1530-1532), which
is called only at :1547 and :1550, both inside `decide`; and `decide` is called at
exactly one site, :1556, the `SOME (th, _)` arm of `case simplified` (:1553-1556).  So
on the loud warning's judge branch (:1563-1565) `simplified` is necessarily `SOME` and
`goals` is the simplified state.  `refuter = SOME simp_refuter` is produced only at
:1555, the `NONE` arm — the sole branch where `goals` is `th0`.  The defence's fourth
point is right too: `goals` feeds `loud_guard_warning` (:1565, :1567),
`undecided_guard_warning` (:1568), the record's `subgoals` attribute (:1363 with
`n_goals = length goals` at :1578) and the trace line's "N subgoal(s)" (:1585).

This is not taste.  Under the project's terminology rule the glossary is authoritative,
and here a defined phrase is spent on its own negation in a passage §5 stage 1 item 2
sends into `reasoners.ML` beside the step-1½ region (plan:718-739).  A comment telling
a reader that a warning shows the guard as written points him at a term the function
never holds.  Major.

**Resolution.**  Replace plan:401-404's clause with what is true, in the file's own
word:

> `goals` keeps today's two branches (:1479) — the state `prove_or_refute` was given,
> UNSIMPLIFIED, when the simplifier refuted, and the simplified state otherwise — so
> the two warnings, the record's `subgoals` field and the trace line are unchanged.

"UNSIMPLIFIED" is `reasoners.ML`'s own word for that state (:88, again at :1599), and
plan:730 already lists :88's sentence among stage 1's edits, so the plan and the source
stay on one vocabulary by construction.  **The phrase "the guard as written" must not
be typed into `reasoners.ML` in any comment**: §1 and §4.2 own it for the
pre-`oblg_template` form.

---

## F7 — §4.8's light correction leaves `PLPR.thy:216-217` standing (SECONDARY)

**UPHELD · major · MUST_DISCUSS_WITH_AUTHOR**

**Claim (condensed).**  §4.8 repairs the `\<condition> P` `\<^descr>` by replacing one
sentence and says "the rest of the paragraph stays" (plan:628-631).  The rest includes
`PLPR.thy:216-217`, which repeats the very claim being repaired — and after the
replacement it has no antecedent at all, because the new sentence mentions no solver.
The first review named the span as ":214-217"; the second review's F5 rejection rested
on rev 2 having corrected this second half; rev 3's narrowing to :214-215 loses it.

**Defence (condensed).**  Conceded in full.  The prescribed edit produces a block whose
kept last sentence tells the user that a guarded rule fires only when clarsimp gets
`P` — strictly weaker than what the guard machinery decides, the identical error §4.8
exists to repair — and whose definite description "the safe solver" refers to a solver
the block no longer introduces.  Ruling 16 ("你可以适当稍微改一下") is a ruling about
scale, and deleting three words from the second sentence is smaller than the
replacement already approved for the first; ruling 15 is untouched, since the corrected
sentence names no safe variant.  One trim: do not also record the span in §5 stage 1
item 3, which already delegates to §4.8; a second copy is a sync hazard.

**Ruling.**  **Upheld.**  I read the block and the registrations myself.

`PLPR.thy:213-217` is the `\<condition> P` `\<^descr>`.  :214-215 is "The assertion
\<open>P\<close> is attempted with a weak but safe solver (usually @{method clarsimp}) in order / to
prevent infinite loop on unprovable propositions which is clearly unexpected."  :216-217
is "Therefore, any rule protected by it is appliable only when the condition \<open>P\<close> is
provable / using the safe solver."

No safe solver runs on `\<condition> P`'s path.  `PLPR.thy:2005-2006` registers
`\<condition> ?P` to `Phi_Reasoners.guard_condition_judge`, which is
`gen_guard_condition_solver guard_digest prove_or_refute` (reasoners.ML:1636).  The
only `clarsimp_tac` in this area is built inside `safe_obligation_solver`
(reasoners.ML:1657-1659) and applied at :1666, and `safe_obligation_solver` is
registered only for `\<condition>[\<safe>] ?P` and `\<condition>[\<no>-\<inst>-\<safe>] ?P`
(`PLPR.thy:2011-2012`, :2014-2015).

The dangling half is real: inside `PLPR.thy:210-226` the word "safe" occurs at :214 and
:217 and nowhere else, so after the prescribed replacement the block refers to a solver
it never introduces.

The regression is on the record.  `REREVIEW:899-901` quotes rev 2's corrected sibling
sentence — "a rule protected by it applies only when `P` is decided provable" — and
rests the F5 rejection on it ("so no reader can act wrongly on the sentence under
attack").  `/usr/bin/grep -n "decided provable"` over the plan and both reviews returns
exactly one hit, `REREVIEW:901`; the phrase is absent from rev 3.  `REVIEW:701` named
the span as ":214-217 carries the clarsimp sentence".

Not nitpicking by any of the author's three tests: the text is wrong about the code,
the path to occur is the plan itself (§5 stage 1 item 3 tells the implementer to edit
"the two `\<^descr>` paragraphs (§4.8)", plan:740-741, and §4.8 is the only
specification of what to type), and the rigour asked is the rigour §4.8 already applies
to the sentence one line above.  Major, because it is user-visible and false.

**Resolution.**  §4.8's first bullet must say that the light correction covers the
paragraph's **two** sentences, `PLPR.thy:214-217`, and that only :213 stays verbatim.
The first sentence keeps the drafter's approved replacement; the second becomes

> Therefore, any rule protected by it is applicable only when \<open>P\<close> is decided provable.

— three words deleted ("using the safe solver") and one adjective corrected.  That is
rev 2's wording, which the second review's judge vetted (`REREVIEW:901`); it stays
within ruling 16's "light", leaves `\<condition>[\<safe>] P` unmentioned under ruling
15, and restores the half a prior rejection depended on.

**For the author (C-1):** this is user-visible text and §9 (plan:1067-1068) holds the
wording of both `\<^descr>` paragraphs open for you, so the sentence above is a
proposal, not a ruling.  Two notes.  The original spells it "appliable"; since the
sentence is rewritten anyway, "applicable" is the correct word.  And "is decided
provable" is prose, not one of the plan's verdict names (Proved / Refuted / Unknown,
`string_of_verdict`, reasoners.ML:1365-1367); "is proved" would match the glossary more
tightly, at the cost of the echo with "is decided by the guard machinery" in the
preceding sentence.

Do **not** add the finding's third step (recording the span in §5 stage 1 item 3).  §5
item 3 already says "the abbreviation and the two `\<^descr>` paragraphs (§4.8)" and
delegates the content; a second copy of the line span is one more thing to keep in sync.

---

## F1 — "stays true and gains the check's case" / "extended" (P2)

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(c) says the comment at `guard_refute.ML:202-205` "stays
true and gains the check's case" (plan:489-490) and §5 stage 1 item 1 schedules it as
"extended" (plan:713-714).  It does not stay true: its first sentence is precisely what
the check stops doing, and its last sentence ("Passing them inside the goal turns the
trust patch silently off") is the retired claim §5 stage 1 item 1 forbids writing into
that very file.  §1's rails entry compounds it by quoting that last sentence as
corroboration (plan:151-155) twelve lines after saying the patch still relaxes the whole
tail (plan:145-148).

**Defence (condensed).**  Partially conceded: the verb, and only the verb.  "Stays true"
is an over-claim about a paragraph whose unqualified opening sentence becomes false for
one branch, and "extended" invites an implementer to append rather than rescope; the
remedy is two words, since §4.3(c)'s own continuation (plan:490-494) already prescribes
the right content.  Refuted: (a) the retired claim is on the record and is a *different*
proposition — "the patch has nothing to act on" is about the problem, while the
comment's "them" is the premises, for which the sentence is true and which the previous
judge adopted twice (REREVIEW:214-217, :1206-1208); moreover the prohibition sits inside
the **third** checklist item's parentheses, not the second's; (b) §1 defines head and
tail two sentences earlier, so saying the patch relaxes the tail and that antecedents
are in the head is not a contradiction.  The request to delete §1's quotation must be
refused.

**Ruling.**  **Partially upheld**, on the verb and on the closing warning; refuted on
both of the other charges.

*Upheld.*  `guard_refute.ML:202-205` reads, verbatim: "The premises go in through the
ASSUMPTION parameter, not inside the goal: / only then are they separate formulas
internally, and only per formula can / Phi_Nitpick take a soundness flag.  Passing them
inside the goal turns the / trust patch silently off."  Under §4.3(c) the check returns
`([], residue)` (plan:430-432) and the call is
`pick_nits_in_term … [] prems concl` with the premises inside the conjecture
(plan:436-438), so the opening sentence is false for that branch.  A sentence that must
be rescoped to survive has not stayed true.  And the closing sentence is a *warning*
against doing what the function immediately below it will now do on purpose
(`guard_refute.ML:216-230`, the literal `true` at :226).  "Extended" is the wrong
instruction for both.

*Refuted, charge (a).*  The retired claim is quoted at `REREVIEW:127-128` and
`:164-166`: "with no assumptions handed over, there is nothing to trust" / "the
assumption list is empty, so the patch has nothing to act on".  That is a claim about
the patch's effect on the whole problem, and it is false: `phi_nitpick.ML:527-533`
relaxes every element of `nondef_us` after the head with `unsound orelse trust_assms`,
and `nitpick_preproc.ML:1031-1040` builds that list from `add_axioms_for_term 1 neg_t`
(:1033) *as well as* from `nondef_assm_ts` (:1034), returning `neg_t :: nondefs`
(:1040); `add_axioms_for_sort` is ungated and ends in
`fold (add_nondef_axiom depth) monomorphic_class_axioms` (:1026).  The comment's
sentence, read with its only possible antecedent, says the *premises* lose the
relaxation, which is true for exactly the mechanism this plan spells out.  I verified
the prohibition's placement myself: at plan:712-717 the parenthetical "NOT a claim that
the model satisfies the premises, and NOT a claim that the patch has nothing to act on"
belongs to the third item ("what keeping every premise buys"), not to the
assumption-parameter item.

*Refuted, charge (b).*  §1's entry defines the list as head plus tail at plan:139-144,
says the patch relaxes the TAIL at :145-148, and says antecedents of the conjecture are
in the HEAD and strict at :151-155.  Head and tail are disjoint halves of one list the
entry has just introduced.  The quotation is scoped by the sentence that carries it and
was prescribed by the second review's judge in his own resolution item 1
(`REREVIEW:214-217`).  Deleting it would strip §1 of corroboration ordered into the
plan.  **Refused.**

Severity: minor, not major.  Nothing about the mechanism is wrong; the prescribed
content (plan:490-494) is already correct.  What is wrong is the label on it — but the
label has a straight path into `guard_refute.ML` in the one area where rev 2 already
went wrong, so it is not nothing either.

**Resolution.**  Two edits, and no third.

1. **plan:489-490.**  Replace "stays true and gains the check's case:" with "is
   REWRITTEN to state both cases — its rationale survives, its unqualified first
   sentence and its closing warning do not:".  The continuation at plan:490-494 stays
   exactly as it is.  (This is the same sentence F13 corrects; apply both together.)
2. **plan:713-714 (§5 stage 1 item 1).**  "extended as §4.3 c says" becomes "rewritten
   as §4.3 c says", and the parenthetical names the closing sentence so that nobody
   appends around it: "…; the closing sentence 'Passing them inside the goal turns the
   trust patch silently off' is a warning addressed to `Normal`'s path and is either
   scoped to it or dropped, since the check passes them inside the goal on purpose".
3. **§1's rails entry, plan:151-155: NO CHANGE.**

---

## F3 — §1 quotes the vendored patch comment's "typedef/class axioms" (P3)

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §1's rails entry makes `phi_nitpick.ML:519-522` the authority for
what the relaxed tail contains and quotes it verbatim — the tail is "the premises passed
in as `nondef_assm_ts` together with machine-generated typedef/class axioms"
(plan:146-148).  Typedef axioms never reach that tail, and §4.3(c) says so sixty lines
later (plan:452-455), so the glossary entry on which P1, P2, P4 and P5 all lean
re-imports, as a quotation, the false mechanism the second review's F1 was upheld for.

**Defence (condensed).**  Core conceded: the quoted clause is false and is left to speak
for itself, in a glossary entry that contradicts §4.3(c), and nothing in §2 or §8 covers
it.  Refuted: (1) §1 states the tail in its own voice first, correctly and with the
preprocessor citation (plan:139-144), so the quotation is corroboration, not foundation;
(2) the word has no route into a third file — §5 item 1 points at §4.3(c), whose
scheduled sentence says "Nitpick's generated axioms", and `grep -n typedef` over the plan
returns only :148, :452, :453; (3) the fix clause "No sentence containing 'typedef' may
be typed into `guard_refute.ML`" is a lexeme ban that contradicts the same fix's request
to warn a rebaser.  Better than deletion: keep the citation, cite the comment for the
split it states correctly (`:524-526`), and correct the clause it states wrongly in place.

**Ruling.**  **Partially upheld.**  The core is right and I re-derived it end to end.
`optimized_typedef_axioms` returns a single term ending `|> HOLogic.mk_Trueprop`
(nitpick_hol.ML:1974-1996, the term at :1991-1993), so its head is `Trueprop`.  Its only
route is `fold (add_maybe_def_axiom depth) (optimized_typedef_axioms ctxt z)`
(nitpick_preproc.ML:1003-1004), and `add_maybe_def_axiom depth t = (if head_of t <>
Pure.imp then add_def_axiom else add_nondef_axiom) depth t` (:907-909).  So typedef
axioms land in `defs`, and `def_us` is processed with the problem's own `unsound`
unconditionally (`phi_nitpick.ML:517-518`) — `trust_assms` never touches them.  Class
axioms, by contrast, *do* reach the tail (nitpick_preproc.ML:1026).  So "typedef" alone
is wrong, which is why a bare quotation cannot be left to speak for itself.

I uphold all three of the defence's refutations.  §1's own account at plan:139-144 is
correct and carries the code citation, so the entry does not rest on the comment.  I ran
the grep: "typedef" occurs in the plan at :148, :452 and :453 only, none of them inside
a scheduled comment text, so the "copied into a third file" charge is unsupported.  And
I reject the lexeme ban severely: a sentence is judged by whether it is true, not by
which nouns it contains, and a ban on the word would forbid the single most useful
sentence `guard_refute.ML` could carry on this subject.  That part of the fix is taste
with a perverse consequence.

Severity minor, not major: one parenthetical quotation, contradicted by the entry's own
preceding sentences and corrected by §4.3(c), with no demonstrated path into source.

**Resolution.**  At plan:146-148, cite the comment for what it gets right and correct it
in place.  For

    (phi_nitpick.ML:527-533; its comment at :519-522: the tail is "the
    premises passed in as nondef_assm_ts together with machine-generated
    typedef/class axioms"),

read

    (phi_nitpick.ML:527-533, and its comment at :524-526: "head keeps the
    problem's own flag, tail gets the relaxed one"; that comment's earlier
    clause at :520-521 names "typedef/class axioms" and is wrong on
    "typedef" — typedef axioms are definitional and reach `defs`, which
    `trust_assms` never touches, §4.3 c),

leaving plan:139-144 as the authority it already is.  Nothing else in §1 or §4.3(c)
changes.  **Rejected from the proposed fix**: the blanket prohibition on the word.

---

## F4 — what `trust_assms` still governs, as a closed set (P2, P3)

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(c) enumerates the tail's conjecture-generated content as
exactly three things (plan:446-452) and §7 repeats it.  Two further routes add
nondefinitional axioms with no `user_axioms` gate: `is_abs_fun` and `is_rep_fun`, both
performing the same `nondef_props_for_const thy false nondef_table x` lookup the plan
correctly calls off at :976-978.  Separately, §1 attributes the generated axioms to "the
conjecture's own constants and types" alone (plan:141-144); for an ordinary guard the
tail also carries the axioms generated from the assumptions.

**Defence (condensed).**  The two sites are real and ungated, but the finding puts the
defect in the wrong clause: `nondef_props_for_const` is a `Symtab` lookup of the
theory's *existing* axioms, not a generator, so the em-dash list of generators is not
holed by it.  What *is* over-claimed is the clause immediately after the list — "the
`user_axioms`-gated route (:976-978) is off under the pinned `false`" — read as the
account of why the theory's own nondefinitional axioms stay out.  The "typedef axioms
are definitional" charge is refuted (that sentence names `optimized_typedef_axioms` with
a line range and is exact).  "§7's bullet repeats it" is wrong: plan:889-892 is a
cross-reference.  Severity is over-claimed: no firing is demonstrated, and if one
occurred the cost is at worst a Refuted turned into an Unknown, the one-way direction the
passage already states.  The "chiefly …" hedge is rejected outright.  The §1 part stands
and is a four-word fix.

**Ruling.**  **Partially upheld**, in the defence's sharper placement, which is the
accurate one.

The two sites are exactly as described and I read them: nitpick_preproc.ML:949-951 is
`else if is_abs_fun ctxt x then accum |> fold (add_nondef_axiom depth)
(nondef_props_for_const thy false nondef_table x)`, :957-959 is the same body under
`is_rep_fun`, and neither carries a `user_axioms` condition — against :976-978's
`accum |> user_axioms <> SOME false ? fold (add_nondef_axiom depth)
(nondef_props_for_const thy false nondef_table x)`.  Same function, same table, same
accumulator slot, one gated and two not.  `nondef_table` is `const_nondef_table nondefs`
over `nondefs = all_nondefs_of ctxt subst` (phi_nitpick.ML:296-298), i.e. the theory's
own nondefinitional axioms (nitpick_hol.ML:1353-1358), and `nondef_props_for_const` is a
lookup (nitpick_hol.ML:1533-1534) — so the defence is right that these are not
generators, and right that the defective clause is plan:454-455, not the list at
:448-452.  The finding's own proposed insertion would have imported the error it was
correcting.

The other two legs fall.  plan:452-454's typedef sentence names
`optimized_typedef_axioms` with `nitpick_hol.ML:1974-1996` and the router with
`nitpick_preproc.ML:907-909`; scoped by its own citation it is exact.  And plan:889-892
reads "Nitpick's generated nondefinitional axioms (§4.3 c)" — a cross-reference with no
enumeration, so **nothing in §7 needs touching for this point**.

§1's leg stands.  `add_axiom` ends in `add_axioms_for_term (depth + 1) t' (seen, app
(cons t') axs)` (nitpick_preproc.ML:892-903, the recursion at :902), and :1034 folds
`add_nondef_axiom 1` over `nondef_assm_ts`, so each assumption contributes itself *and*
the axioms generated from its own constants and types.  plan:141-144 therefore
under-describes an ordinary guard's tail.  Nothing rides on it — everything so generated
lands in the tail either way, and for the check the assumption list is empty — but §1 is
a glossary entry that feeds comments and the fix is four words.

Severity minor.  Neither I nor the finding established that any phi-system axiom mentions
a typedef's `Abs_`/`Rep_` constant — that would need Isabelle, which this read may not
run **[inference boundary]** — and the source comment §5 schedules
(plan:489-494) carries no gate claim at all, so the consequence is confined to the plan
text.  I note in passing that `reasoners.ML:1231-1232` already makes the same closed-gate
statement in shipped code; that is pre-existing and outside this plan.

**Resolution.**  Two edits, none in §7.

1. **plan:454-455.**  Leave the generated-axiom list at :448-452 untouched.  Replace
   "and the `user_axioms`-gated route (:976-978) is off under the pinned `false`." with
   a clause that names what is gated and what is not, e.g. "and the route from an
   ordinary constant to the theory's OWN nondefinitional axioms (:976-978) is off under
   the pinned `false` — with two sites Nitpick leaves ungated: the same `nondef_table`
   lookup on a typedef's `Abs_`/`Rep_` constant (:949-951, :957-959).  No phi-system
   axiom is known to mention one, and one more tail formula only costs an Unknown."
2. **plan:142-144.**  "from the conjecture's own constants and types" becomes "from the
   conjecture's and the assumptions' own constants and types", with the citation
   extended to note that `nitpick_preproc.ML:1031-1040` builds the list from
   `add_axioms_for_term 1 neg_t` and then from `nondef_assm_ts`, each recursing through
   `add_axiom` at :902.

**Not accepted**: the "chiefly …" hedge (a vague enumeration in a source comment is
worse than a precise one with its exception named); placing the `Abs_`/`Rep_` route
inside the generated-axiom list; the "major" severity; and any edit to §7.

---

## F5 — the totality chain proves non-emptiness, not "exactly one state" (P1)

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(a) writes the new body as "`ALLGOALS (asm_full_simp_tac
(enhance_for_guard ctxt))` under its 60 s bound — and yields exactly one state"
(plan:349-351) and re-states "one state" as the post-condition (plan:363-364) and in §5
stage 1 item 2 (plan:724-725).  The chain that follows rules out zero states, not two.
The operator that caps the count, `Seq.take 1`, is in today's code, is load-bearing for
the 60 s bound, and is absent from the plan — while §5 item 2 orders the very comment
sentence that documents it to be rewritten.

**Defence (condensed).**  The precision half is conceded and should be applied: the last
link, `solve_tac i ORELSE TRY (…)`, only has to be non-empty, `ORELSE` hands back the
whole sequence of the first branch that yields anything, and `solve_tac` is `FIRST'` of
solvers that are nowhere shown single-valued.  `Seq.take 1` gives at most one element
*and an empty tail*, which is what makes one `cpu_bounded` wrap over the first pull cover
everything a caller can pull.  Refuted: plan:349-351 is a prose gloss, not a code
rendering (the plan's renderings are indented blocks), and plan:369-370 and :408-410 do
state what stays, so "the implementer is given no statement of what must stay" fails.
The statement "yields exactly one state" is *true* of the post-hoist code, so severity is
minor.  Do not half-render the body in plan:350.

**Ruling.**  **Partially upheld**, and I checked the whole chain rather than either
account of it.

The chain as written establishes non-emptiness: `asm_full_simp_tac` is
`PREFER_GOAL (simp_loop_tac 1)` (Pure/simplifier.ML:328), empty exactly out of range
(Pure/goal.ML:275-277); `ALLGOALS` fixes the count at entry (Pure/tactical.ML:236-240);
in range `generic_rewrite_goal_tac` returns `Seq.single`
(Pure/raw_simplifier.ML:1518-1521); the continuation is `solve_tac i ORELSE TRY (…)`
(Pure/simplifier.ML:325-327).  It does not establish uniqueness: `solve_tac` is
`FIRST' (map (solver ctxt) …)` (Pure/simplifier.ML:322-323), `FIRST'` folds `ORELSE'`
(Pure/tactical.ML:167, :110), and `ORELSE` returns the *whole* sequence of the first
non-empty branch (Pure/tactical.ML:85-88).  Rev 3 upgraded the second review's F12
wording ("never yields an empty sequence", `REREVIEW:596-597`, :613-630) to "exactly one
state" without adding the link that carries the upgrade.

That link is `Seq.take 1` at reasoners.ML:1075, and it is load-bearing.
`Seq.take n xq` is `make (fn () => (Option.map o apsnd) (take (n - 1)) (pull xq))`
(Pure/General/seq.ML:106-109), i.e. at most one element and an empty tail; the bound
wraps only the first pull (reasoners.ML:1076-1077), and `p_auto_attempt` (:1097-1098)
composes with `THEN`, which is `Seq.maps tac2 (tac1 st)` (Pure/tactical.ML:79) and so
ranges over that tail.  The file already says exactly this at reasoners.ML:1068: "The
first simplified state only (Seq.take 1), so the one bound covers the / whole
simplification."  `/usr/bin/grep -n "Seq.take"` over the plan returns **nothing** — the
operator is named nowhere in 1126 lines — while §5 stage 1 item 2 (plan:724-725) orders
that comment block rewritten naming only two items, "one state; the timeout path's
surviving reason".  An implementer following that could delete the one sentence that
records the cap, leaving a later reader free to delete the operator.

The defence's refutations hold.  plan:349-351 is inline backticked prose inside a
sentence; the plan's actual code renderings are indented blocks at :374-378 and :384-391,
and the gloss also drops `Simplifier.`, the argument `th`, the `Seq.make`, the
`cpu_bounded` call and the whole handler, which the next sentences discuss.  And
plan:369-370 names the one deletion while plan:408-410 states what stays (loosely — see
F9).  Severity minor: the claim is true of the post-hoist code; what is missing is one
clause of justification and one "stays" sentence.

**Resolution.**  Two edits, plus one word.

1. **After plan:359**, before "The one place that could still fail", add one clause:
   "— that rules out zero states; the cap is `Seq.take 1` (:1075), which yields at most
   one element and an empty tail (Pure/General/seq.ML:106-109), so the one 60 s bound
   over the first pull (:1076-1077) covers everything any caller can pull.  `Seq.take 1`
   and the sentence that records it (:1068) stay."  This is the move the paragraph
   already makes for the timeout path: name what stays and why.
2. **plan:724-725 (§5 stage 1 item 2)**, extend the parenthesis from two items to three:
   "(§4.3 a: one state — the cap and the bound it carries; the timeout path's surviving
   reason)", so the rewritten comment cannot lose reasoners.ML:1068.

**Not adopted**: rewriting plan:350 as a half-rendering of the body.  Either write the
whole body as an indented block or leave the prose gloss; a half-rendering reads more
like code than the present gloss does.

---

## F8 — "refute every check unconditionally today" (P3)

**UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §1's glossary entry states as fact that the three steps refute
EVERY check today (plan:125-129).  They do not: a check whose premises the guard-side
simplification collapses to `False` closes the goal and is Proved, and then none of the
three runs.  The plan says so itself three times — §3 item 2, §3 item 1's measurement,
§6 item 4 — so the glossary sentence is the odd one out, and it is the sentence a source
comment would be condensed from.

**Defence (condensed).**  Conceded, with every leg re-verified: `THEN_ALL_NEW` applies
its second tactic over an interval that is empty when the simplification closes the
subgoal, so `quick_cut` never sees it; `solved_states` accepts a premise-free state at
once; the outcome is Proved with refuter `-`.  The path is measured, not hypothetical
(guard plan §33 item 3).  The consequence is concrete: a comment reading "these three
steps refute every check unconditionally" licenses the inference §6 item 4 is written to
block.  Two refinements: keep the word "unconditionally", which the plan uses for this
property at four sites; and mend the third copy at plan:219-220 as well, by pointing at
the glossary term rather than restating the sentence in three places.

**Ruling.**  **Upheld**, and the mechanism is exactly as both sides describe it.
`guard_simp_tac` is `Seq.take 1 (ALLGOALS (Simplifier.asm_full_simp_tac
(enhance_for_guard ctxt) THEN_ALL_NEW quick_cut) th)` (reasoners.ML:1074-1075);
`THEN_ALL_NEW` runs its second tactic over `i .. i + Thm.nprems_of st' - Thm.nprems_of
st` (Pure/tactical.ML:302-304), which is empty when the simplification closes subgoal
`i`, so `quick_cut` (reasoners.ML:975-978) never sees a closed subgoal.  `simplified` is
then `SOME` of the closed state (:1478), `decide th` runs P-auto, whose acceptance
criterion is `Seq.filter Thm.no_prems` (`solved_states`, :1053) — a state with no
premises passes at once — and the outcome is Proved with `refuter = NONE` (:1538-1542),
printed as `-` by `the_default "-" refuter` (:1577).

The plan's three qualified statements are plan:265-271 (§3 item 2), plan:258-264 (§3 item
1, citing guard plan §33 item 3, which I read at
`Docs/GUARD_CACHE_QUICK_MODE_PLAN.md:3012-3022`: the `ToA_case_sum_src` idiom, "useful
facts `x = None`, `x = Some y` → PROVED in 1 ms") and plan:851-853 (§6 item 4).  §0 at
plan:47-48 already carries the safe subjunctive "would refute".  So §1 is the outlier.

Not a re-raise: §2 item 10 records the *wording* change (plan:217-220), and the first
review's F1 resolution item 5 (`REVIEW:265-268`) asked only that "exactly" be softened —
whether "every check" is true was never examined.  Not nitpicking: the path is measured
and §5 stage 1 item 2 sends the signature block's comments to be rewritten from this
design, where the neighbouring comments are careful about exactly this class of
qualification (reasoners.ML:112-117 spells out the timeout path rather than glossing over
it).

**Resolution.**  Mend the quantifier in three places, keeping "unconditionally".

1. **plan:125-129**: "… and which therefore refute unconditionally every check the
   guard-side simplification does not prove (§3 item 2): the refutation by the
   simplifier …".
2. **plan:180-182 (§2's gloss of ruling 1)**: point at the glossary term instead of
   restating — "the three steps (§1) are the ones whose validity rests on the
   assumption (the wording 'exactly' softened in the second round, item 10)".
3. **plan:219-220 (§2 item 10's record)**: same, so the corrected sentence exists once.

The author's own Chinese quotations in §2 are untouched; this corrects the drafter's
English gloss so that it is true.  No change to plan:47-48, plan:175 or plan:636-641,
which already carry a safe form.

---

## F9 — "Consequences: `guard_simp_tac` … keep today's code" (P1)

**UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(a)'s closing sentence lists `guard_simp_tac` first among
the things that "keep today's code" (plan:408-410).  Every other name in that list is a
caller; `guard_simp_tac` is the one function in it whose body the same paragraph has just
rewritten.  The ruling this transcribes said *signatures*, not code, and §4.4 gets it
right.

**Defence (condensed).**  Conceded; the sentence is indefensible.  Four places in one
document disagree with one, and the one is the summary a reader carries away.  It is a
transcription slip: R1's accepted text said "keep today's signatures"
(`REVIEW:1149-1153`), §4.4 kept the ruling's word, only §4.3(a) widened it.  But the
proposed fix's second half — dropping `guard_simp_tac` from the sentence — throws away
R1's actual payoff, that the signature and all three call sites are intact so no caller
is rewired and `PLPR.thy` needs no ML edit.  The sentence should say the true, useful
thing.

**Ruling.**  **Upheld.**  plan:349-351 says `guard_simp_tac` "becomes the simplification
alone" and plan:369-370 says "The `quick_cut` after the simplification (:1075) goes".  In
the file that is the `THEN_ALL_NEW quick_cut` inside the body at reasoners.ML:1074-1083
(the composition on :1075), plus the function comment at :1062-1073, which says
"asm_full_simp then quick_cut on every subgoal" and "A subgoal simplified to False stays
an empty sequence".  Deleting a combinator from a function's body is not keeping its
code.  §4.4 at plan:500 says "`guard_simp_tac`'s callers and signature" and is right; §5
stage 1 item 2 at plan:723-725 schedules "`guard_simp_tac` without the cut and with its
comment rewritten" and plan:731-732 schedules its signature-block comment :112-117.

I verified the call sites independently:
`/usr/bin/grep -rn "guard_simp_tac" /home/qiyuan/Current/MLML/contrib/phi-system/
--include='*.ML' --include='*.thy'` gives exactly three calls, all in `reasoners.ML`
(:1098 in `p_auto_attempt`, :1478 in `prove_or_refute`, :1514 on the judge path); the
other hits in that file are the signature (:118), comments and the refuter-name string
(:1389), and outside it only `PLPR.thy:1974`'s method description, the smoke test and an
`ai-artifacts` probe theory.  The five other names in the list do keep their code:
`p_auto_attempt` :1097-1098, `p_auto_solving` :1639, and nothing in §4.3(a) or §5 edits
those bodies.

Severity minor: §5 already carries the correct instruction, so no code would come out
wrong; what is wrong is the summary.  I accept the defence's refusal of the fix's second
half — going silent about `guard_simp_tac` would hide the reason R1 was accepted.

**Resolution.**  Split the one edited name out of the list and give it back the ruling's
word.  Replace plan:408-410's opening clause with

    Consequences: `guard_simp_tac` keeps today's signature (:118) and is
    called from the same three places (:1098, :1478, :1514) — only its body
    loses the cut and its comments are rewritten (§5 stage 1 item 2);
    `p_auto_attempt`, `p_auto_solving`, `guard_condition_solver'`, the
    method `\<phi>guard_P_auto` and `PLPR.thy`'s ML keep today's code;

leaving the rest of the sentence untouched.  "Called from the same three places" is the
right claim and must not be strengthened: two of the three sites sit inside code §4.3(a)
rewrites (:1478-1479 becomes plan:386, :1514-1516 becomes the total case of
plan:393-401), so only :1098 is literally untouched text.  §4.4 and §5 already read
correctly and need no change.

---

## F10 — `add_eq_axiom` cited to a file it is not in (P2)

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  The parenthetical "(`add_eq_axiom` routes those to
`add_nondef_axiom`, nitpick_hol.ML:1492-1506)" (plan:451-452) attaches the wrong file and
lines to the named function: those lines hold the constructor-pattern predicates, and
`add_eq_axiom` is in `nitpick_preproc.ML`.  In the same sentence the `is_descr` and
choice-specification routes carry no citation, while the sibling clause three lines down
cites both producer and router.

**Defence (condensed).**  The head is conceded: neither named function is in that file,
and the plan's own convention (demonstrated three lines below) is that a file:line after
a name cites that name.  The diagnosis of how it got there is right too — `REREVIEW:185-186`
put the citation after a clause whose last named entity was the predicate, and rev 3's
compression deleted that clause.  The consistency half is refuted: the tail list's
convention is name-without-line — `add_axioms_for_sort` at plan:449 carries no citation
either, which the finding does not notice — so adding three file:line pairs is a change
of convention, not a correction, in a sentence §5 requires to be condensed into a concise
comment.  The corrected pointer already lands the reader in `nitpick_preproc.ML` beside
the `else if` chain that holds every route in the list.

**Ruling.**  **Partially upheld**, exactly as the defence frames it.
`/usr/bin/grep -n add_eq_axiom` over both files returns only `nitpick_preproc.ML:910`,
`:944` and `:973`; `nitpick_hol.ML` has no hit.  `nitpick_preproc.ML:910-912` is
`and add_eq_axiom depth t = (if is_constr_pattern_formula ctxt t then add_def_axiom /
else add_nondef_axiom) depth t`, and `nitpick_hol.ML:1492-1506` is `is_constr_pattern`
(:1492-1498), `is_constr_pattern_lhs` (:1500-1501) and `is_constr_pattern_formula`
(:1503-1506).  The sibling clause at plan:452-454 shows the correct shape and I verified
both of its citations.

On the second leg I agree with the defence and reject the demand.  plan:449 cites
`add_axioms_for_sort` by name alone; so the sentence's convention for the tail list is
name-without-line and the single line range is the outlier.  Once the pointer says
`nitpick_preproc.ML:910-912`, every route in the list is in that one file within forty
lines — `is_descr` :940-942, the equational-function route :943-945, choice specification
:946-948, and `add_axioms_for_sort`'s own `fold (add_nondef_axiom depth)
monomorphic_class_axioms` at :1026.  The reader is landed beside them, not sent
searching.  Citation parity here is taste; the misplaced pointer is not.

**Resolution.**  One line.  At plan:452 replace

    `add_nondef_axiom`, nitpick_hol.ML:1492-1506); typedef axioms are

with

    `add_nondef_axiom` unless `is_constr_pattern_formula` holds,
    nitpick_preproc.ML:910-912); typedef axioms are

This points the citation at the file and lines that hold `add_eq_axiom` and restores the
condition rev 3's compression dropped — at no cost, because :911 is literally
`if is_constr_pattern_formula ctxt t then add_def_axiom`, so the cited lines show the
predicate by name at the point where it decides.  No citations are added for `is_descr`
or choice specification.  If the author takes R1 this clause disappears with the rest of
the list; the edit must still be made now, because rev 3 stands until he rules.

---

## F11 — "the tolerant rail is the deliberate choice" / "would rest on it alone" (P2, P5)

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  The clause scheduled into `guard_refute.ML` — "the premises go in
as assumptions under `Normal`, where the tolerant rail is the deliberate choice"
(plan:490-491) — is false of any handed-over premise of the form `x = e` with `x` a Free
not occurring in `e` and no other assumption defining `x`: Nitpick partitions such
assumptions out of the nondefinitional list before `trust_assms` can reach them, and
definitional formulas are processed with the problem's own `unsound`, which is `false`
here.  The same over-claim carries §3 item 5 and, through it, §8's first rejected
alternative.

**Defence (condensed).**  Mechanism conceded and verified; the headline and the evidence
refuted.  plan:490-492's two "where" clauses characterise the two *designs* — which flag
value the code deliberately passes against where the check puts its premises — not each
formula's fate, and the comment being extended already says "only per formula can
Phi_Nitpick take a soundness flag".  The liveness evidence (`Phi_BI.thy:6217`) is a
*check* site, where under ruling 10 the premises never pass through the assumption
parameter at all, so no `Normal`-side instance is offered.  On §3 item 5 the mechanism
cuts the other way and the finding's qualifier is the wrong one: the check's `neg_t` is
`False ⟹ False`, which has no Free, so a def-partitioned premise can be dropped outright
rather than being strict.  The proposed wording is unfit for `guard_refute.ML`, which
cites no line of unpatched Isabelle anywhere.  A one-word tightening of plan:491 is
offered instead.

**Ruling.**  **Partially upheld.**  The mechanism is real and I verified every step:
`preprocess_formulas` calls `axioms_for_term hol_ctxt assm_ts neg_t`
(nitpick_preproc.ML:1240-1249), whose first act is
`val (def_assm_ts, nondef_assm_ts) = List.partition (assumption_exclusively_defines_free
assm_ts) assm_ts` (:888-889) with `def_assm_table` built at :890;
`defined_free_by_assumption` matches `Trueprop (HOL.eq for (u as Free _) def)` when `u`
does not occur in `def` (:852-861) and `assumption_exclusively_defines_free` requires it
to be the only such assumption (:863-868); when the Free is met during the scan its
defining assumption is added by `add_def_axiom` (:981-986), landing in `defs`, not in
`neg_t :: nondefs` (:1031-1040).  `def_ts` becomes `def_us` (phi_nitpick.ML:354) and is
processed with the problem's own `unsound` unconditionally (:517-518), while only the
tail of `nondef_us` gets `unsound orelse trust_assms` (:527-533); `unsound` is false
(reasoners.ML:1254 `("max_potential", "0")` with phi_nitpick.ML:861-862).

So §3 item 5's "they would ride the unknown-tolerant rail" and "the verdict would rest on
the tolerant rail alone" (plan:282-286), and §8's first bullet's echo (plan:963-965), are
over-claims and should be repaired.  §8's bullet is one of the five passages; §3 item 5
is not, but the bullet cites it, so both move together.

The headline does **not** stand.  plan:490-492 reads "the premises go in as assumptions
under `Normal`, where the tolerant rail is the deliberate choice, and as antecedents
under `Check_Premise_Consistency`, where the strict rail is the question" — a contrast of
two designs, beside a comment that already distinguishes per-formula treatment
(`guard_refute.ML:203-204`).  It is loose, not false.  The liveness leg fails on its own
evidence: `Phi_BI.thy:6217-6219` is
`\<And>a. \<condition> x = Inl a \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> …`, a
*check* site, and under ruling 10 the check's premises go in as antecedents
(plan:430-438), so `axioms_for_term`'s partition never sees them.  No `Normal`-side
instance was produced, so "the shape is common, not hypothetical" is not carried.  The
proposed replacement wording is also unfit for its destination: `guard_refute.ML` cites
no distribution line anywhere — its one pointer at Nitpick internals names "the vendored
phi_nitpick.ML" (:221) — because distribution line numbers drift on every upgrade.

I also confirm the defence's sharper reading of the check's counterfactual: with
`falsify` pinned true (reasoners.ML:1252), `neg_t = Logic.mk_implies (orig_t, False)`
(phi_nitpick.ML:278-279), which for `orig_t = Trueprop False` is `False ⟹ False` and
contains no Free.  So with `x = Inl a` the sole premise, `nondef_assm_ts` is empty and
nothing ever meets the Free: the def-partitioned premise reaches neither rail.
**[Inference: term-level reasoning; neither the defender nor I ran Nitpick or the
simplifier.]**  Ruling 10's rejection is untouched and, if anything, strengthened.

Severity minor: §8 is plan-only, §3 item 5 is a diagnosis paragraph, and the one clause
bound for source is loose rather than wrong.

**Resolution.**  Three edits, all by hand.

1. **§3 item 5 (plan:282-286)** — repair to the stronger true statement, not the
   finding's: not one premise would be on the strict rail; those Nitpick keeps in its
   nondefinitional list ride the tolerant rail (`guard_refute.ML:226` passes the literal
   `true`); a premise that exclusively defines a free is partitioned out of that list
   (nitpick_preproc.ML:888-889) and enters the problem only when its free is met during
   the scan (:981-986), and the check's `neg_t` is `False ⟹ False`
   (phi_nitpick.ML:278-279), which has no free — so such a premise can be dropped
   outright.  For the check the head carries nothing either, so the verdict would rest
   on the tolerant rail and on whatever was not dropped, never on a model of the
   premises.
2. **§8's first bullet (plan:963-965)** — one clause: "the premises would ride the
   tolerant rail and the verdict would rest on it alone" becomes "no premise would be on
   the strict rail: those Nitpick keeps nondefinitional would ride the tolerant rail, and
   one that exclusively defines a free could be dropped outright (§3 item 5)".
3. **plan:491** — the one-word tightening: "where the tolerant rail is the deliberate
   choice" becomes "where `trust_assms = true` is the deliberate choice".  The clause
   then names the value the code passes (`guard_refute.ML:226`) instead of a rail, so
   nothing in it can be read as quantifying over the premises' individual fates, and the
   parallel with "where the strict rail is the question" survives.  **No
   `nitpick_preproc.ML` line numbers go into `guard_refute.ML`.**

If the def/nondef partition is to be recorded in source at all, the place is the vendored
patch's own header (`phi_nitpick.ML:20-22`), which today says "Premises reach this file as
nondef_assm_ts" without qualification — one clause there covers every caller at once.
That is R2's territory; see below.

---

## F12 — §7 carries the F18 measurement (P4)

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §7's out-of-run bullet closes with "The second review measured
the hoist's loss of the step-1½ short-circuit on the committed corpus records and found
it zero" (plan:919-922).  That review rejected the point as nitpicking and ruled
explicitly that if it goes anywhere it goes into §4.3(a), "not in §7"; §8's own F18 line
then sends the reader to §7 for it (plan:1025-1026).  The sentence also describes a
different mechanism from the bullet it sits in.

**Defence (condensed).**  Placement conceded on two grounds, one of which the finding does
not give.  (1) Topic: the bullet is headed by its losers — the out-of-run instance and
the method — and the step-1½ short-circuit lives inside `prove_or_refute`, a third site;
the bullet closes cleanly one sentence earlier.  (2) The sentence arrives with two terms
the reader has not met: "the hoist" and "the step-1½ short-circuit" are introduced only
in §4.3(a) and are in no glossary.  (3) The cross-document inconsistency is real and is
in the plan's own text.  Refuted: "in a register §5 stage 1 item 1 draws source comments
from" is false — stage 1 items 1 and 2 point at §4.3(c), §4.3(a), §4.2, §4.6 and §4.7 and
never at §7 — and the finding's own proposed fix concedes "Nothing of this reaches a
source comment", so that leg contradicts itself.  Prefers the smaller repair: let §8's
F18 entry carry the measurement itself.

**Ruling.**  **Partially upheld**, on placement, and on the defence's two grounds rather
than on the finding's comment-fitness leg, which I reject.

I verified: plan:907-908 heads the bullet "The out-of-run instance and the method lose
the refutation by the simplifier for every guard (R1, ruling 9)"; its body is about
`p_auto_attempt` (reasoners.ML:1097-1098) and the method; it closes at plan:918-919 with
"For the method the cut is lost only on a bare `False` conclusion (§6 item 6)"; the
disputed sentence then runs to :922.  `REREVIEW:1066-1068` is F18's resolution: "Nothing
changes.  If the author nevertheless wants the difference on the page, it belongs as half
a sentence in §4.3(a), where the shape is described, and it must carry the measurement —
not in §7."  plan:1025-1026 now reads "**The hoist gives up the step-1½ short-circuit**
(F18): measured zero on / the committed records (§7)" — a pointer into §7 for a sentence
§7 should not hold.

`/usr/bin/grep -n hoist` over the plan returns :363, :920 and :1025 only — never a
definition; "step-1½" appears at :384 inside the code sketch, then :770, :920, :1025.  So
in §4.3(a) both terms land warm and in §7 both land cold.  That is the defence's second
ground and it is the stronger one.

I reject the comment-fitness leg outright.  §5 stage 1 item 1 (plan:707-717) and item 2
(plan:718-739) name §4.3(c), §4.3(a), §4.2, §4.6 and §4.7 and nothing in §7; the finding's
own `proposed_fix` says so.  Nothing here reaches `guard_refute.ML` or `reasoners.ML`.  I
also note that §7 already cites a review id in prose at plan:908 ("R1, ruling 9"), so the
break is topical, not a break of §7's habit.

Severity minor, and the fix is deleting four lines.

**Resolution.**  Two edits.

1. **Delete plan:919-922** from §7's out-of-run bullet.  The bullet then ends at "For the
   method the cut is lost only on a bare `False` conclusion (§6 item 6)."  This is
   required either way.
2. **plan:1025-1026 must stop pointing at §7.**  Either let §8's own entry carry the
   measurement — "**The hoist gives up the step-1½ short-circuit** (F18): measured zero
   on the committed records — every `guard_simp_tac` refutation there has one subgoal." —
   which fits §8's stated job ("with the reason, so that they are not re-proposed") and
   keeps §4.3(a) free of a review-naming measurement; or put half a sentence with the
   measurement after plan:391 in §4.3(a), where "the hoist" is defined at :363 and
   reviews are already named in prose at :381 and :393, and re-point plan:1025-1026 there.
   The drafter picks; both satisfy the second review's one hard constraint.

---

## F13 — the assumption-parameter comment belongs to `nitpick` (P2)

**UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(c) calls `guard_refute.ML:202-205` "the comment `preprocess`
carries about the assumption parameter" (plan:489).  It is `nitpick`'s comment: it sits
after `preprocess`'s body ends and immediately before `fun nitpick`, and every clause of
it describes the `pick_nits_in_term` call inside `nitpick`.  `preprocess` has a comment of
its own that a reader might edit instead.

**Defence (condensed).**  Conceded on the substance; no reading of the code rescues the
sentence.  The file's convention for attaching a comment to a binding — comment, one
blank line, the `fun` — is used four lines above `preprocess` itself, and all three
paragraphs of :202-214 describe code inside `nitpick`'s body.  The collision is not
hypothetical in kind: §5 stage 1 item 1 schedules edits to *both* comment blocks in the
same breath.  Two limits: the misattribution is confined to plan:489 (plan:152-155 and
:713 name no function and stay correct), and the point's own aside "four lines earlier"
is wrong — `preprocess`'s comment is :170-173.

**Ruling.**  **Upheld.**  I read the file's structure line by line.  `fun preprocess ctxt
assms goal =` is `guard_refute.ML:175` and its body ends with `end` at :200; :201 is
blank; the three-paragraph comment runs :202-214; :215 is blank; `fun nitpick ctxt params
(i, n) (subst, assms, goal) =` is :216.  The comment's three paragraphs are about the
last positional arguments of the `Phi_Nitpick.pick_nits_in_term` call at :226-227
(:202-205), about `genuineN`/`quasi_genuineN` as tested at :228-229 (:207-208), and about
the model search's own bound, ending "see the note at the search call below" — and that
note is :220-224, inside `nitpick` (:210-214).  The only comment inside `preprocess`'s
body is :184-187, about deleting the `guess_inst` looper.  `preprocess`'s own comment is
:170-173, five lines above its `fun` and thirty-two lines above :202.

Minor, because the line citation disambiguates for anyone working by line number; but §5
stage 1 item 1 (plan:712-714) schedules "the pipeline comment (:168-174)" and "the
assumption-parameter comment (:202-205)" in one sentence, so the file has two scheduled
comments and §4.3(c) gives one of them the other's owner's name.

**Resolution.**  At plan:489 change only the owner: "The comment above `nitpick` about the
assumption parameter (:202-205) …".  This is the same sentence F1 edits — apply both
together, so that plan:489-490 reads "The comment above `nitpick` about the assumption
parameter (:202-205) is REWRITTEN to state both cases — its rationale survives, its
unqualified first sentence and its closing warning do not: …".  Do not copy the point's
aside "four lines earlier".  plan:152-155 and plan:713 cite :202-205 without naming a
function and need no change.

---

## F2 — "a countermodel makes every premise definitely true" (P2)

**NITPICK_REJECTED · none · NO_ACTION**

**Claim (condensed).**  §4.3(c) (plan:440-443) and §0 (plan:49-52) say a countermodel is
an assignment under which every premise is definitely true; §5 stage 1 item 1
(plan:715-716) orders the opposite, "NOT a claim that the model satisfies the premises".
Read against §1's definition of "the premises", neither side is right: the model
satisfies the premises *as they reach Nitpick* — after the `Preprocess_Hooks` and after
`preprocess`'s own simplification — not the premises §1 names, and not nothing.  The
implementer is handed the sentence and its prohibition in one checklist.

**Defence (condensed).**  Refuted on every leg.  The prohibition's referent is on the
record: it is the first review's resolution item 2 carried verbatim (`REVIEW:257-258`),
and what it was written to forbid is the rev-1 certificate sentence the same resolution
ordered deleted (`REVIEW:243-245`); the same resolution *prescribes* the positive half in
the same breath (`REVIEW:249-251`).  Inside §4.3(c) the attacked sentence is scoped by its
own grammar: the subsection opens "collects, weakens and simplifies exactly as today
(:177-192); then, on the residue" (plan:427-428), and "every premise" has its antecedent
three clauses back in its own sentence, P₁…Pₙ.  The reconciliation the finding says is
absent is the very paragraph the checklist points at (plan:473-487).  The substance was
ruled a nitpick one round ago at the neighbouring site (`REREVIEW:872-914`, §8's record at
plan:1019-1021) and returns with no new evidence against that reason.  The proposed
wording would drag a hook registry into the Essence section.

**Ruling.**  **Refuted, and I reject it plainly as nitpicking.**

The alleged contradiction dissolves on the record.  `REVIEW:243-245` is the sentence the
prohibition targets — "With every premise kept, a model Nitpick finds satisfies all the
hypotheses: the one positive witness of consistency in the pipeline, and the reason a
Refuted entry of a check is trustworthy" — a *certificate* claim.  `REVIEW:249-251`, in
the same resolution, prescribes "the search must exhibit an assignment under which no
premise is definitely false, and a premise Kodkod can evaluate and that no assignment
satisfies still blocks every model", which is plan:475-477 almost word for word.  So the
checklist entry has two halves, "content" and "not certification", exactly as §4.3(c)'s
third paragraph is headed (plan:473).

The sentence is true of the code.  The head of Nitpick's nondefinitional list keeps the
problem's own soundness flag while only the tail is relaxed (phi_nitpick.ML:527-533), and
that flag is strict here (`max_potential = 0` pinned at reasoners.ML:1254 with
phi_nitpick.ML:861-862), so the negated conjecture must come out definitely true, every
conjunct with it.

The hooks leg is factually right — `premises_of` (guard_refute.ML:107-116) does run before
`Preprocess_Hooks.invoke` (:178) and before the preprocessing simplification (:188-192),
and the sole registered hook does rewrite and delete premises
(guard_refute_scrub.ML:158-163, registered at :165) — and reaches nothing.  §4.3(c) says
so itself at plan:478-480, §7 says it again (plan:876-888), and the destination file
already carries the disclosure four lines above `preprocess` ("the hooks and the slice
weaken the premises", guard_refute.ML:170-173) and above `is_premise` ("Dropping a
premise ENLARGES the model space …", :82-84).  Demanding that a new comment beside those
re-declare the hook pipeline in its own sentence is rigour beyond the surrounding code.
And the identical attack on the neighbouring sentence was ruled "Refuted on both legs,
and both are nitpicking", severity none, one round ago (`REREVIEW:872-914`), with §8
recording the reason (plan:1019-1021).  The standing rule is that such a point returns
only with new evidence against the stated reason; F2's only new element is the §5
contradiction, which is a misreading of a ruling whose target is quoted above.

**Resolution.**  Nothing changes in §4.3(c), §0 or §5 stage 1 item 1.  One taste call is
available to the author and is **not** ordered: at plan:441-442, the appositive "a finite
model of the premises" is the one place in the sentence where the glossary phrase stands
without its residue antecedent, and writing "a finite model of them" would cost a word
and remove the ambiguity.  That option stops at §4.3(c); it must not be extended to §0,
which says what the change IS in one paragraph and names no internals.

---

## The relaxations

### R1 — record the routing RULE rather than the list (P2)

**PROPOSE_TO_AUTHOR**

**What is proposed.**  §4.3(c) currently records what `trust_assms` still governs as a
list of four enumerated sources with five citations (plan:447-455).  R1 proposes
recording instead the rule that decides the set, and keeping at most one or two examples
marked as examples.

**Why it clears the "already ruled" bar.**  The second review's judge wrote "That narrower
set is what the plan must record" (`REREVIEW:186-187`) and rev 3 adopted his list verbatim.
The new evidence against that reason is that the list, as ordered and as adopted, is
still not true of the code: F4's two ungated `nondef_table` routes
(nitpick_preproc.ML:949-951, :957-959) and F10's misplaced citation are both defects of
the *enumeration form*.  The remedy as ordered did not produce a true sentence.  That is
evidence against the stated reason, not a re-litigation of the ruling.

**Why the rule cannot acquire the same defect — verified.**  The accumulator is
`(string * typ) list * (term list * term list)` (nitpick_preproc.ML:891), the second
component being `nondefs`; `add_def_axiom` writes the first with `apfst` and
`add_nondef_axiom` the second with `apsnd` (:905-906); `add_maybe_def_axiom` (:907-909,
nondefinitional iff the head is `Pure.imp`) and `add_eq_axiom` (:910-912, definitional iff
`is_constr_pattern_formula`) are the only conditional routers into it; after the folds only
`defs` is appended to (`val defs = defs @ special_congruence_axioms hol_ctxt seen`,
**:1037**), and the function returns `(neg_t :: nondefs, defs, …)` at **:1040**.  So
`nondefs` is exactly the image of `add_nondef_axiom`, and no branch among the sixteen
router call sites can put a formula in the tail except through those three.  Exhaustive by
construction.

**Two corrections to the proposal's own evidence, which the author must not carry
forward.**  (i) "The routing is decided in one place" is not right as stated: the four
routers are defined in one place (:905-912), but which router each source uses is spread
over :935, :941, :944, :947, :950, :954, :958, :962, :967, :973, :977, :985, :1004, :1006,
:1008 and :1026.  The exhaustiveness comes from the accumulator, not from locality, so the
proposal should rest on the accumulator.  (ii) "a snapshot of a vendored file that will be
rebased" names the wrong file: `nitpick_preproc.ML` is the distribution's and is *not*
vendored — `phi_nitpick.ML:11-12` says "All other Nitpick modules are used unmodified from
the distribution".  The staleness risk is the distribution upgrade, which this tree has
performed once (`phi_nitpick.ML:10-11`), so the path exists; it is simply not the one the
claim describes.  (iii) The defender's own transcription of the tail lines was off by two:
the `special_congruence_axioms` line is :1037 and the return is :1040, as verified above.

**Comment fitness.**  The plan's sentence is the least comment-shaped in the paragraph —
four enumerated items with five citations, one of them wrong (F10) — while the destination
file's habit is a rule plus a pointer at a plan paragraph (`reasoners.ML:85`, :1058,
:1104), and §5 stage 1 item 1 itself asks for comments "each concise, pointing at this
plan" (plan:717).

**One refinement I ask the author to fold in.**  The proposed wording ends by singling out
the `user_axioms`-gated route as off under the pinned `false`.  Standing alone after a
rule-shaped sentence that reads as "no user axiom reaches the tail", which is false for
F4's reason.  Either drop that sentence or pair it with its ungated siblings.  The other
cost is that the reader loses the concrete examples; keeping one or two in a trailing
clause, marked as examples, answers it.

**If the author declines**, F4's and F10's edits to the list are mandatory: as it stands at
plan:447-455 the enumeration is not true of the code.

### R2 — let stage 1 correct the two wrong COMMENT blocks of the vendored `phi_nitpick.ML` (P2)

**PROPOSE_TO_AUTHOR, in the narrowed form below**

**What is proposed.**  §4.4 lists `phi_nitpick.ML` among the files stage 1 does not change
(plan:520).  R2 asks that stage 1 be allowed to edit two of its **comment** blocks — no
code, no behaviour, no distribution line.

**What survives, verified.**  (i) `phi_nitpick.ML:519-526` says the relaxed tail is "the
premises passed in as nondef_assm_ts together with machine-generated typedef/class axioms".
The typedef half is false, by F3's chain.  (ii) `phi_nitpick.ML:14-22` summarises the patch
as putting "the premises of the guard" on the unknown-tolerant rail and closes "Premises
reach this file as nondef_assm_ts, i.e. as separate elements of the nondefinitional formula
list, which is what makes a per-formula soundness flag possible at all."  That is an
under-claim: the patch relaxes every element of `nondef_us` after the head
(phi_nitpick.ML:527-533), and that list is built by `add_axioms_for_term 1 neg_t`
(nitpick_preproc.ML:1033) *before* the fold over `nondef_assm_ts` (:1034).  After stage 1
the closing sentence is also false of one of the two callers, since the check passes `[]`
for `nondef_assm_ts` and puts the premises in the conjecture (plan:435-438).

**Why it is slight.**  Both blocks are phi-system's own text.  I checked the distribution:
`HOL/Tools/Nitpick/nitpick.ML:1-6` is its whole header, and everything from
`phi_nitpick.ML:7` ("COPY NOTICE") onward has no counterpart there; `:519-526` is a
PHI-PATCH block that is already a divergence.  A diff-and-reapply rebase
(`phi_nitpick.ML:10-11`) diffs the distribution file against its next release, so it never
produces a hunk inside text the distribution does not have.  The COPY NOTICE's invariant —
"Everything else is untouched" — stays literally true of every distribution line.

**Why it is not taste.**  The consequence has been paid once already: rev 2 of this plan
wrote "with no assumptions handed over, there is nothing to trust" (`REREVIEW:214`), the
second review's F1/R1 overturned it, and the author had to re-rule (ruling 17).  §1 anchors
its rail vocabulary in that header (plan:134-135) while §4.3(c) contradicts one of its
clauses.  **[Inference: that the drafter read the header rather than the code is not
established; what is established is that the plan stakes its glossary on a comment it
elsewhere contradicts.]**

**Three corrections to the proposal's own rationale, which the author must not carry
forward.**  (i) "§5 stage 1 item 1 must put the whole corrected account into
`guard_refute.ML`" is an over-read: plan:713-717 schedules two clauses plus a pointer, and
§4.3(c)'s own prescription for that comment (plan:489-494) contains no enumeration of
Nitpick internals.  The promised gain is therefore not brevity.  (ii) "the typedef error
stops being copied forward into a third file" is false: the plan says the opposite at
plan:452-455 and the word has no route into a source comment (F3).  The real hazard is the
inverse — after stage 1 the tree holds two comments about one mechanism that disagree, and
the correct one points at the wrong one.  (iii) The evidence attributes the typedef
correction to the second review's "F3"; F3 there is "Where `guard_kind` is declared"
(`REREVIEW:93`, :253), and the typedef correction is inside F1/R1's ruling
(`REREVIEW:144`, :174-179).

**The question for the author, narrowed.**  May stage 1 add `phi_nitpick.ML` to its file
list for comment text only, to say (a) at :519-526 that the tail is the assumptions handed
in as `nondef_assm_ts` together with the nondefinitional axioms Nitpick generates from the
conjecture itself, and that typedef axioms are definitional and unaffected; and (b) at
:14-22 that the flag relaxes the whole TAIL of the nondefinitional list — every
nondefinitional formula but the negated conjecture — not only the premises, with one clause
saying that antecedents of the conjecture are in the head and are never relaxed?  Wording
constraints: keep phi-system's pinned parameter values out of the vendored header (they
belong at reasoners.ML:1254-1256 and guard_refute.ML:207-208); touch no distribution line
and not the `fun_box` paragraph at :24-28.  F11's optional clause — "except one that
exclusively defines a free, which Nitpick's own preprocessing moves to the definitional
list" — belongs in the same edit if the author wants it recorded in source at all.

If approved, §1's rails entry may point at the corrected header.  **If refused, F3's edit
to plan:146-148 is owed regardless**, because §1 would otherwise keep endorsing what
§4.3(c) refutes.

---

## Appendix A — dropped by the curator (one line each)

1. **"the caller reads neither label (guard_refute.ML:225, :228-229)" (plan:469-470)** —
   taste without consequence: `:225` binds `val (code, _)` and `:228-229` does read it, but
   the cited lines make the meaning (it does not *distinguish* the two codes) unambiguous,
   rev 2's judge used the same compression with the same citations (`REREVIEW:198-200`), and
   `guard_refute.ML:207-208` already carries the correct version.
2. **"`user_axioms = false` fixes `genuine_means_genuine` false whatever the flag says" is
   strictly true only because `mono_nondefs` is non-empty** — rigour beyond the surrounding
   code; phi-system has ten monomorphic user axioms (reasoners.ML:1232), so
   `got_all_mono_user_axioms` (nitpick_preproc.ML:1038-1039) is false regardless, and the
   repository already asserts the unconditional form at reasoners.ML:1271-1272 and
   guard_refute.ML:207-208.
3. **§7's `guard_refute_scrub.ML:161-165` misses the "replaces `Satisfiable (x : T)` by
   `True`" half at :158-159** — adjacent code in the same function, ruling 7's settled
   ground, nothing in §7 scheduled into a comment; the span would simply read better as
   :158-165.
4. **The totality chain omits `PREFER_GOAL`'s two `PRIMITIVE (rotate_prems …)` steps** —
   hypothetical with no path to occur: for an in-range `i` neither `permute_prems` call can
   raise, so the stated conclusion stands.
5. **`ALLGOALS` descends over goals the simplification cannot remove — but the looper can
   also ADD subgoals** — no consequence: `ALLGOALS` works downward from the entry count
   (Pure/tactical.ML:236-240) so the index stays in range, and
   `exists concl_is_false (Thm.prems_of th1)` covers added goals exactly as
   `THEN_ALL_NEW quick_cut` did.
6. **"`can_inst` has no effect on a check" (plan:487) is broader than the fix-level argument
   supports** — hypothetical with no path to occur: `judge` is `NONE` in shipped code
   (reasoners.ML:1350), and the fix-level half is correct (:403 subtracts the conclusion's
   vars from the premises', and a `False` conclusion has none).
7. **The record's refuter token stays `simp_refuter` = "guard_simp_tac" after the refutation
   moves** — taste without consequence: the plan faces it at plan:404-406,
   reasoners.ML:1388 stays true, and §6 item 4's corpus floor requires the string unchanged.
8. **Line-span slop of one or two lines in several citations** (`is_premise` :88-98 for
   :89-97, `premises_of` :104-116 for :107-116, `split_conjunctions` :122-133 for :126-133,
   `guard_simp_tac` :1074-1085 for :1074-1083, `Premise_def` PLPR.thy:1967 for :1968) —
   taste: every span contains the object it names and none lands on unrelated code.

*I affirm all eight drops.  I spot-checked three of them in this session: `is_premise` is
`guard_refute.ML:89-97` with :88 the last line of its comment; `guard_simp_tac`'s body ends
at :1083; `declare Premise_def [\<phi>guard_refute_simp]` is `PLPR.thy:1968`.  In each case
the cited span contains the object and no reader is misled.*

## Appendix B — self-dropped by the readers (one line each)

**Mechanism lens.**
1. "the caller reads neither label" — `code` *is* read at :228-229; what the caller does not
   do is distinguish the two codes.  Taste without consequence.
2. `genuine_means_genuine` is fixed false only because `mono_nondefs` is non-empty — no path
   to any consequence.  Rigour beyond the surrounding code.
3. `PREFER_GOAL`'s `PRIMITIVE (rotate_prems …)` steps can return `Seq.empty` on a THM
   exception — the arithmetic was checked; neither call can raise for an in-range `i`.
4. The simplifier's looper can ADD subgoals — the index stays in range and the hoisted test
   covers added goals.  No consequence.
5. Line-span slop in six citations — every span contains the cited object.  Taste.
6. §4.8's "Two `\<^descr>` paragraphs … (:210-226)" can be read as a count of the block's
   existing paragraphs — the two bullets disambiguate immediately.
7. The new `\<^descr>`'s pointer "(library/reasoners.ML, `guard_kind`)" sends the reader to
   the re-export rather than the declaration — but `reasoners.ML` is where the branches live.
8. "it holds exactly when the premises are inconsistent" is about discharge in the current
   context, not about the proposition — the surrounding block already speaks that way.
9. "`card 1-6` makes the model finite" — Nitpick's models are finite by construction;
   `card 1-6` fixes the range.  The conclusion drawn is right either way.
10. The refuter name `guard_simp_tac` survives the hoist — the plan faces it and the smoke
    test pins the token.

**Comment-fitness lens.**
11. P2's "`can_inst` has no effect on a check" is broader than the fix-level argument — but
    `judge` is `NONE` in shipped code.
12. P1's "The record's refuter name `guard_simp_tac` still names what happened" — taste
    without consequence; §6 item 4's corpus floor requires the string unchanged.
13. P4's bullet title over-claims for the method — the bullet says exactly that two sentences
    later (plan:918-919).  Correcting a title the body corrects is nitpicking.
14. The new `\<^descr>`'s pointer at `Phi_Reasoners.guard_kind` while §1 declares the
    datatype in `Phi_Guard_Refute` — not false; the re-export exists.
15. The new `\<^descr>` names four internals where its neighbours name none — out of the
    SECONDARY item's scope (accuracy only), and the author words this text.
16. P3's gloss "unknown (an atom it cannot evaluate)" — Nitpick's unknown comes from
    under-approximated representations; one parenthetical in a glossary.
17. P4's `is_premise` citation "guard_refute.ML:88-98" — the function is :89-97; inside the
    range.
18. P4's "a model of the weakened premises can be reported as consistency" — nothing reports
    consistency to anyone; wording only, the bullet's substance is right.
19. P5: nothing found.  Both §8 bullets' reasons check out, and §8 is plan-only.

**Consistency lens.**
20. Citation ranges opening one or two lines inside the preceding comment — every range
    covers the whole of the code it names.
21. `guard_refute_scrub.ML:161-165` misses the rewrite half at :158-159 — related code,
    ruling 7's settled ground.
22. "which Nitpick negates to `P₁ ∧ … ∧ Pₙ`" is not the literal term
    (phi_nitpick.ML:278 builds `Logic.mk_implies (orig_t, False)`) — classically equivalent
    and the plan's form is clearer for a comment.
23. The hoisted test is strictly more eager than today's per-index `THEN_ALL_NEW quick_cut`
    when a later subgoal instantiates a schematic in an earlier one — a hypothetical with no
    demonstrated path, and the direction is toward the correct verdict.
24. Source comments pointing at a plan under `ai-artifacts/` while the file's habit points at
    `Docs/` — `ai-artifacts/` is git-tracked and the location is ruling 8.
25. §4.1's "its read decides the rail of Nitpick's generated nondefinitional axioms"
    under-describes what `trust_assms = true` governs for an ordinary guard — it precisely
    names what the *read* changes, which is the check's case.
26. "The one place that could still fail is the 60 s timeout path" reads oddly, since that
    path is built never to fail — it resolves correctly in context.
27. `trust_assms = (kind = Normal)` rather than a `case` — refuted as nitpicking by the
    second review's F13; no new evidence against that reason.
28. §8's bullet 2 summarises only one of R1's four reasons — the cost half is recorded at
    plan:904-906 and :1013-1016.

*I affirm all twenty-eight self-drops.  Nos. 22 and 27 in particular would have been
rejected here: the first is a deliberate, clearer rendering of an equivalent term, and the
second was ruled one round ago on the codebase's own idiom with no new evidence offered.*
