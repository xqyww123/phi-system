# Second adversarial review of `CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md` rev 2 — the judge's report

- **Plan reviewed**: `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_PLAN.md`, rev 2
  (2026-09-22), 916 lines.  No code has been written.  Line numbers in the plan are
  those of phi-system `1f3c2142`; the working tree is `6026b43e`, and
  `git diff --stat 1f3c2142 HEAD -- Phi_Logic_Programming_Reasoner/ Phi_BI/` is empty,
  so every ML and theory file cited below carries the plan's own line numbers.  The
  judge re-verified the decisive citation of every point in this session with
  `/usr/bin/grep` and `sed`/`awk`; no Isabelle was launched and no file was edited but
  this report.
- **Date**: 2026-09-22.
- **Workflow**: interrogation lenses (`r1-hoist`, `r-nitpick-shape`, `elegance`,
  `verification-consistency`) → a curator, who dropped three points → one fresh
  defender per surviving point, with no sight of the other points → this judge.
- **22 findings (F1–F22) and 3 relaxation proposals (R1–R3) reached the judge.**
  Four upheld, eight partially upheld, ten refuted; of the refuted, eight are named
  as nitpicking below.  One relaxation is put to the author; two are dropped.
- **Round 1** is `ai-artifacts/CHECK_HYPOTHESIS_CONSISTENCY_REVIEW_2026-09-22.md`
  ("the first review" below).  Terms are the plan's glossary (§1) and the guard
  plan's (§1).  "Premises", never "hypotheses" (ruling 12).

---

## Readiness: **MET_ON_CONDITION**

No blocker survived, and the design is unchanged by this round.  Ruling 10's shape —
R-nitpick receives the check's premises as antecedents of its conjecture, with no
split and no slice — survived attack again and is right: the undecided probe of §6
item 2 does discriminate it, and no reviewer produced a reason to reshape it.  The
hoist of the refutation by the simplifier (ruling 9) survived with its sketch intact.
The digest marker, the entrance-computed kind, `guard_digest_of`, the one warning
function and the untouched factory, judge, entries and P-auto all stand.

What this round found is, again, concentrated in one place: **§4.3(c)'s account of
`trust_assms` is false in both directions** (F1), and the plan schedules it into a
source comment in `guard_refute.ML` *and* into a stage-1 "verification" that instructs
the implementer to confirm a false proposition by reading.  That is the same class the
first review ruled the most consequential prose defect in rev 1 (F2), one layer down,
and it is not a re-raise: rev 1's F1/F2 were about the premises' rail, this is about
what the flag still governs once the premises are off it.  Around it sit a seam
question (F6/F9), a declaration-site contradiction (F3), a vocabulary duplication
(F15), a wrong corpus forecast (F16) and a scatter of citation and checklist
corrections.

**Conditions gating stage P (the symbols): none.**  Not one point in this round
touches stage P, and the verification lens re-checked it clean (`symbols-words` 135
words, high water `0x00E086`, `\<premise>` = `0x00E04C`, the generator's allocation
order, the `--check` write guards at `build_word_glyphs.py:861-874`, no clash with
`\<checkmark>`, and the five hand-maintained counts).  **Stage P may start as soon as
the author allows it**, exactly as plan:598-600 says.

**Conditions gating stage 1 (the code):**

- **C-1 (F1 with R1 — one conversation, not two).**  The author rules on the value
  `Phi_Guard_Refute.nitpick` passes for `trust_assms` under
  `Check_Premise_Consistency`.  Ruling 10's second half ("在 Check_Premise_Consistency
  模式下不启动 trust rail 吗？我赞同", plan:185-186) was given on the stated premise
  that with the premises as antecedents "there is nothing to trust".  That premise is
  false: the patch relaxes the whole *tail* of the nondefinitional formula list, and
  that tail is also built from the conjecture itself.  The premises are off the
  tolerant rail either way, by the shape of the call; what the flag still decides is
  the rail of Nitpick's machine-generated nondefinitional axioms.  Whichever value the
  author chooses, §0 (:54-56), §1's rails entry (:122-124), §4.3(c) (:373-379,
  :386-389), §7 (:760-764), §8's bullet (:822-826), §5 stage 1 item 1 (:614-618) and
  §4.1's classification (:268-273) are rewritten.
- **C-2 (F3).**  The drafter decides where `guard_kind` is declared and makes §1
  (:88-89), §5 stage 1 item 1 (:609-613), §4.5 (:433) and §6's digest-marker probe
  (:706-707) say the same thing.  §1 as it stands names an arrangement the plan's own
  §8 proves cannot compile.
- **C-3 (F15, F22, F6/F9, F16 and the DRAFTER_APPLIES list).**  The drafter applies
  the corrections ruled below.
- **C-4 (§9).**  The author rules on §9's pending list, which F15 reshapes (one
  `string_of_guard_kind` token in place of two hand-written literals) and F3 extends
  (the owning structure).

**Is a third review of the plan text needed before stage 1?**  A *targeted* one, yes.
The rewritten §4.3(a) sketch (F6/F9's seam), §4.3(c) (F1, F13, F22 and the author's
C-1 ruling), §1's rails entry, §7 and §8's bullet are the passages that land in source
comments and that this round found wrong; they must be read once more before they are
typed into `guard_refute.ML`.  That is a read of five passages, not another six-lens
round.  **Everything else** — the citation fixes (F8, F12), the checklist extensions
(F7), the probe fixes (F2, F4), the timeout sentence (F11), the corpus forecast (F16)
— **is checked in stage 3's code review**, where the code and the checklist are read
side by side.

---

## The rulings

| id | title | severity | verdict | disposition |
|----|-------|----------|---------|-------------|
| F1 | §0/§4.3(c)/§5's `trust_assms` account is false in both directions | major | UPHELD | MUST_DISCUSS_WITH_AUTHOR |
| F3 | Where `guard_kind` is declared: §1 and §5 contradict each other | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F9 | The shared `False` predicate is cut at the wrong seam | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F6 | The judge path is prose-only; no probe reads a conclusion under a prefix | minor | PARTIALLY_UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F15 | The record attribute and the trace line spell the kind two ways | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F22 | §4.3(c)'s "not a certificate" list misattributes `user_axioms = false` | minor | UPHELD | DRAFTER_DECIDES_THEN_REREVIEW |
| F2 | §6 item 2's "P-auto finds it" probe carries no `fresh` argument | minor | UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F16 | "at most twenty of those decisions are checks" contradicts §3 item 2 | minor | UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F12 | The unreachability argument skips the link that returns `Seq.empty` | minor | UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F4 | §6's undecided probe cannot discriminate the unknown-tolerant rail | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F7 | Texts the change falsifies are off the stage 1 and stage 3 checklists | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F8 | Three line citations name the wrong code | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F11 | The timeout path's surviving reason is never stated | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F13 | `trust_assms` = `kind = Normal` and §4.1's classification | minor | PARTIALLY_UPHELD | DRAFTER_APPLIES_NO_REREVIEW |
| F5 | The `\<^descr>`'s "a model of the premises themselves" | none | NITPICK_REJECTED | NO_ACTION |
| F10 | The signature checklist and "exported where §6 needs them" | none | NITPICK_REJECTED | NO_ACTION |
| F14 | The smoke test's warning constants and helpers off the checklist | none | REFUTED | NO_ACTION |
| F17 | §6 item 6's negative control "cannot be written" | none | REFUTED | NO_ACTION |
| F18 | The hoist gives up the short-circuit; §7 does not record it | none | NITPICK_REJECTED | NO_ACTION |
| F19 | `GUARD_NITPICK_FALSIFY_PLAN.md` omitted from stage 3 | none | REFUTED | NO_ACTION |
| F20 | `guard_kind_of` re-spells `Thm.major_prem_of` | none | NITPICK_REJECTED | NO_ACTION |
| F21 | `preprocess`'s result pair keeps its type and its names | none | REFUTED | NO_ACTION |

| id | relaxation | recommendation |
|----|------------|----------------|
| R1 | Leave `trust_assms` at the literal `true` for both kinds, and re-put ruling 10's second half with the facts | **PROPOSE_TO_AUTHOR** — recommend accepting for stage 1 |
| R2 | Let `guard_simp_tac` return a state instead of a one-element sequence | DROP (a free alternative is offered under F9) |
| R3 | Rename the constructor `Normal` to `Ordinary` | DROP |

---

## F1 — §0, §4.3(c) and §5's account of `trust_assms` is false in both directions

**UPHELD · major · MUST_DISCUSS_WITH_AUTHOR**

**Claim (condensed).**  Rev 2 rests three passages on "with no assumptions handed
over, there is nothing to trust" (plan:54-56, :373-374, :760-762).  Both halves are
wrong.  (a) The flag does not read the assumption list: Phi_Nitpick's patched split
relaxes the whole *tail* of the nondefinitional formula list, and that tail also
carries the axioms Nitpick generates from the conjecture itself — so passing `false`
for the check moves those from the unknown-tolerant rail to the strict one, a real
divergence between the check and every ordinary guard.  (b) The stated gain cannot
occur: `user_axioms = false` is pinned, so nothing can be labelled genuine, and the
caller discards the label anyway.  §5 stage 1 item 1 schedules the false account into
`guard_refute.ML`, and §4.3(c) schedules stage 1 to "verif[y] … that with an empty
assumption list the flag affects nothing but that label" — an instruction to confirm a
false proposition by reading.

**Defence (condensed).**  PARTIALLY_CONCEDED, and the concession is the core.  The
mechanism claim is false and indefensible; the label rationale is doubly dead; both
scheduling defects follow; and the finding missed two further sites carrying the same
false reason (§8's bullet at plan:822-826 and §1's rails entry at plan:122-125).  What
does not stand: the finding's headline evidence item is wrong — typedef axioms reach
`defs`, not the nondefinitional tail — so the set the plan must record is narrower;
the divergence must **not** be filed in §7, which is a register of *weakenings*, while
`trust_assms = false` makes the check's problem *stricter*, so §7's sentence "the
tolerant rail is NOT among the check's weakenings" is true and keeps its place with a
new reason; the Unknown-direction cost is ruling 5's accepted territory and nothing
unsound follows; and §6 item 4's verdict split cannot be the instrument, because it
cannot attribute one Unknown to a rail rather than to `card 1-6`, the hooks or
preprocessing.

**Ruling.**  **Upheld**, on the core, with the defence's four corrections accepted.  I
verified the whole chain myself.

The patch is `phi_nitpick.ML:517-533`: `def_us` is processed with the problem's own
`unsound` unconditionally (:517-518), and `nondef_us` is split `conj_u :: axiom_us`,
the head keeping `unsound` and the tail getting `unsound orelse trust_assms`
(:527-533).  The patch's own comment at :519-522 says in as many words that the tail
is "the premises passed in as nondef_assm_ts **together with machine-generated
typedef/class axioms**" — and plan:379 cites exactly that block while asserting its
opposite.  The tail is built in `nitpick_preproc.ML:1031-1040`:
`([], ([], [])) |> add_axioms_for_term 1 neg_t |> fold_rev (add_nondef_axiom 1)
nondef_assm_ts |> …`, returning `(neg_t :: nondefs, …)`.  Emptying `nondef_assm_ts`
empties only the second fold.  `unsound` is always `false` here (`max_potential = 0`
pinned at reasoners.ML:1254; the problem list is built from `(if max_genuine > 0 then
[false] else []) @ (if max_potential > 0 then [true] else [])`, phi_nitpick.ML:860-862),
so `unsound orelse trust_assms` collapses to `trust_assms` and the flag alone decides
the tail's rail.  **So "the assumption list is empty, so the patch has nothing to act
on" is false, and "the check bypasses it by the shape of its call rather than by a
switch" is false of the plan's own code, which passes a switch (plan:614).**

The defence's correction to the finding's evidence is right and I adopt it.
`optimized_typedef_axioms` returns a single `HOLogic.mk_Trueprop (ALL x. Rep x ∈ S)`
(`nitpick_hol.ML:1974-1996`, the term at :1991-1993), whose head is `Trueprop`, and
`add_maybe_def_axiom` routes to `add_def_axiom` unless the head is `Pure.imp`
(`nitpick_preproc.ML:907-909`) — so typedef axioms land in `defs`, which
`trust_assms` never touches.  The `nondef_props_for_const` route at :976-978 is gated
by `user_axioms <> SOME false` and is therefore off under the pinned `false`.  What
survives as a conjecture-only source of *nondefinitional tail* formulas is narrower:
the monomorphic class axioms of a TFree's sort (`add_axioms_for_sort`, ungated, the
`fold (add_nondef_axiom depth) monomorphic_class_axioms` at the end of that function),
`is_descr` and choice-spec functions, and equational-function axioms whose left-hand
side is not a constructor pattern (`add_eq_axiom` → `add_nondef_axiom` when
`is_constr_pattern_formula` is false, `nitpick_hol.ML:1492-1506`).  **That narrower
set is what the plan must record — not the finding's sentence.**

The label rationale is dead twice over, and the file being edited already says so.
`genuine_means_genuine = got_all_user_axioms andalso … andalso not trust_assms`
(phi_nitpick.ML:665-668), `got_all_user_axioms = got_all_mono_user_axioms andalso
no_poly_user_axioms` (:328-329), `got_all_mono_user_axioms = (user_axioms = SOME true
orelse null mono_nondefs)` (`nitpick_preproc.ML:1038-1039`), with `("user_axioms",
"false")` pinned at reasoners.ML:1256 and phi-system's ten monomorphic user axioms
recorded at reasoners.ML:1232.  reasoners.ML:1271-1272 states the conclusion in the
repository's own words — "under user_axioms = false Nitpick can never certify a model
genuine" — and `guard_refute.ML:207-208` repeats it *in the target file, five lines
above the comment the plan schedules*.  And the label is unread:
`guard_refute.ML:225` binds `val (code, _)`, and :228-229 maps `genuineN` and
`quasi_genuineN` alike to `Refuted`.

This is not nitpicking, and I say so plainly.  Two false mechanism sentences and a
dead rationale, in a plan whose subject is which formula rides which rail, scheduled
into a source comment next to a comment that contradicts them, plus a stage-1
"verification" whose expected answer is written into the instruction — that is exactly
the shape the author's first criterion rejects and the class the first review upheld
as its most consequential prose defect.

**Resolution.**  The code choice is the author's (C-1, and R1 puts the alternative).
Whichever value he chooses, the following text repairs are required and are *not*
optional:

1. **§0, plan:54-56.**  Delete "the check bypasses it by the shape of its call rather
   than by a switch: with no assumptions handed over, there is nothing to trust."  Say
   what is true: the check's *premises* cannot ride the tolerant rail in any case,
   because they are antecedents of the conjecture — `guard_refute.ML:202-205` states
   this from the other side — and what the flag still governs is the nondefinitional
   axioms Nitpick generates from the conjecture itself.
2. **§1's rails entry, plan:122-125.**  It defines the patch as acting on "the
   premises handed over as ASSUMPTIONS" alone.  That incomplete definition is what the
   three false sentences lean on.  It must name the whole tail: every nondefinitional
   formula of the problem except the negated conjecture.
3. **§4.3(c), plan:373-379.**  Delete "the assumption list is empty, so the patch has
   nothing to act on", the whole label clause, and the stage-1 "verifies" sentence.
   Put in their place (i) what the flag still moves — the narrower set named above,
   with its citations — and (ii) that the label is not the reason, because
   `user_axioms = false` fixes it at `quasi_genuine` whatever the flag says and the
   caller reads neither.
4. **§7, plan:760-762.**  Keep the sentence; change its reason.  Do **not** file the
   divergence among the weakenings: under `false` the check's problem is *stricter*
   than an ordinary guard's, and a strengthening under a heading that reads "accepted
   imprecisions" would be a new error in place of an old one.  If the author keeps
   `false`, add a separate bullet recording the difference, its direction (it can only
   turn a Refuted into an Unknown, never into a wrong Proved) and the fact that it is
   **not probed**: neither §6 item 4's verdict split nor any smoke probe can separate
   it from `card 1-6`, the hooks or preprocessing, and isolating it would need a
   second corpus leg the plan does not schedule.
5. **§8, plan:822-826.**  The rejected-alternative bullet carries both errors, in the
   one section whose job is to stop the question being re-asked.  Rewrite it with the
   true reason.
6. **§5 stage 1 item 1, plan:615-618.**  The checklist entry for
   `guard_refute.ML:202-205` must say what the comment is to contain, and must not
   schedule a claim that the patch has nothing to act on.
7. **§4.3(c)'s stage-1 item** is replaced by "record what the flag moves", not
   "verify that it moves nothing".

I explicitly **reject** the finding's own instruction to record the divergence in §7
and to make §6 item 4's verdict split the instrument; both are wrong for the reasons
the defence gives and which I verified.

---

## F3 — Where `guard_kind` is declared: §1 and §5 contradict each other

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  §1 — the plan's own authoritative glossary — says the datatype
is declared "in `Phi_Reasoners`" (plan:88-89).  §5 stage 1 item 1 says it is declared
in `guard_refute.ML` "or in a small file both load; the implementer picks" (:609-613).
§8's own R4 rejection gives the reason the first is impossible (:864-867).  The choice
is not an implementer's detail: it fixes how the signature, the smoke test and §6's
digest-marker probe spell the type and both constructors.  Two further homes are
settled by evidence the plan does not record: `guard_refute.ML`'s header disclaims the
concept, and `Phi_Guard_Cache` is blocked by a `Normal` collision.  The user-visible
`\<^descr>` bets on §1 by citing "(library/reasoners.ML, `guard_kind`)".

**Defence (condensed).**  Concedes the contradiction and that leaving the owner to the
implementer fails criterion (1), since the owner's name is literally typed into §4.5's
sketch and §6's probe.  Refutes the rest: the `\<^descr>`'s citation is a reading
pointer of the same shape as the sibling paragraph's "(library/reasoners.ML,
prove_or_refute)" three lines above, and is true under every candidate arrangement;
demanding that §8 record why an unproposed home is excluded is criterion (3) work, and
`Phi_Guard_Cache`'s own header disclaims the scope while the `Normal` overlap is
same-structure shadowing of a kind this codebase already lives with across structures;
`guard_refute.ML`'s header disclaims the *object-level* meaning of a guard, not the
refuter's decision vocabulary, which that file already owns.  Proposes the point's own
option (ii): declare in `Phi_Guard_Refute`, re-export from `Phi_Reasoners` with
`datatype guard_kind = datatype Phi_Guard_Refute.guard_kind`.

**Ruling.**  **The contradiction is upheld; the three supporting arguments are
refuted.**  Verified: `PLPR.thy:1966` loads `library/guard_refute.ML` and `:1970`
loads `library/reasoners.ML`, so `signature PHI_GUARD_REFUTE` (guard_refute.ML:14-34)
cannot name a type declared in `Phi_Reasoners` — which is precisely §8's own stated
reason for rejecting R4.  §1 is the plan's definition site and it states an
arrangement the plan elsewhere proves cannot compile.  That must be fixed in the plan,
not in the implementer's head.

The `\<^descr>` sub-claim is **refuted**: plan:532-533 writes "(library/reasoners.ML,
prove_or_refute)" and plan:542-543 writes "(library/reasoners.ML, `guard_kind`)" —
the same "(file, identifier)" shape, pointing a reader at where the behaviour lives,
and §5 stage 1 item 2 (plan:619-626) puts `guard_kind_of`, `guard_digest kind`,
`prove_or_refute kind` and `r_nitpick kind` in that file under every arrangement.  No
user-visible text is at risk, and with it the finding's "major" grade goes.

The `Phi_Guard_Cache` sub-claim is **refuted**: the plan never proposes that home,
`guard_cache.ML:12` disclaims the scope ("prove_or_refute, the factory, the refuters
and the judge live in reasoners.ML"), and cross-structure constructor reuse is this
codebase's normal state — `Phi_Guard_Cache.verdict = Proved | Refuted | Unknown`
(guard_cache.ML:70) lives beside `Phi_Guard_Refute.verdict = Refuted | Provable |
Unknown` (guard_refute.ML:39), resolved by qualification at use (reasoners.ML:1321
writes `Phi_Guard_Refute.Refuted`).  Enumerating non-candidates in §8 is criterion (3)
work.  The header sub-claim is **refuted** on a reading of the whole sentence
(guard_refute.ML:8-11 is about what a guard's proposition *means*, not about the
refuter's own vocabulary, which that file already owns at :19).

**Resolution.**  The drafter decides and the plan says so with the reason.  The
defence's arrangement is the elegant one and I recommend it: declare `guard_kind` in
`Phi_Guard_Refute` — the earliest structure that must name it, since §4.3(c) gives the
kind to `preprocess` and `nitpick` — and re-export it from `Phi_Reasoners` as
`datatype guard_kind = datatype Phi_Guard_Refute.guard_kind`, so that §1's "in
`Phi_Reasoners`" becomes true as written and `Phi_Reasoners.Normal` is the spelling
everywhere outside `guard_refute.ML`.  That form is idiomatic Isabelle/ML — Pure does
it at `Isar/locale.ML:104`, `Isar/expression.ML:50`, `proofterm.ML:2243-2244`,
`zterm.ML:266-268` and `ML/ml_pretty.ML:9,15` — and `signature PHI_GUARD_REFUTE`
already carries a `datatype` spec (guard_refute.ML:19), so there is no open question
of form.  Then: delete "or in a small file both load; the implementer picks" from
plan:609-613; add the two replication lines to stage 1 item 2's reasoners.ML list;
qualify the constructors in §4.5's sketch (plan:433) and §6's digest-marker probe
(plan:706-707), as `Guard_Decision_Smoke.thy:76, :85-87, :319-328` qualifies
everything else; and add the owning structure to §9.  No §8 entry is owed.

---

## F9 — The shared `False` predicate is cut at the wrong seam

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  (a) `concl_is_false : term -> bool` is given the
already-stripped conclusion, so `Logic.strip_assums_concl` stays duplicated at three
sites — inside `quick_cut`, at step 1½, and a third time on the judge path.  The one
property the shared predicate exists to guarantee is exactly the half left outside it.
(b) `guard_kind_of` must also accept `Premise _ False`, whose content comes back from
the tag reader without the `Trueprop` wrapper, so `concl_is_false` cannot be applied to
it as typed, and the plan never says how the third function tests `False`.

**Defence (condensed).**  (a) conceded: `Logic.strip_assums_concl` occurs exactly once
in the whole of reasoners.ML today, at :976, and the plan would write it at three (or
four) places; folding the strip inside is free and cannot mis-apply, since it is the
identity on a prefix-free term.  (b) refuted on three counts: §1 names the shared
*reading*, not the shared `False` test, and that is verbatim what the first review's
F19 resolution ordered; the two predicates **must** differ, because `concl_is_false`
has to *reject* the tagged form (the factory's front `quick_cut 1 th` runs before
`Premise_def` is unfolded and must stay a no-op there, §4.4, plan:421-424) while
`guard_kind_of` has to *accept* it; and the finding's proposed `guard_kind_of` line
would, with the strip folded in, apply `dest_premise_tag_opt` to an unstripped subgoal
and answer `Normal` on all eight live uses, switching the whole feature off.

**Ruling.**  **(a) upheld, (b) refuted**, and I verified both.
`/usr/bin/grep -n strip_assums_concl` over reasoners.ML returns the single hit :976
(inside `quick_cut`, :975-978).  The plan's sketch at :323 composes the strip at the
caller, and the judge path (plan:330-331) will compose it a third time.  Duplicating
the reading at three sites in order to share the `False` test is the weaker half of
the invariant, and the author's first criterion decides it: put the strip inside.

(b) is refuted.  `PLPR_Syntax.ML:19-21` does return the bare `X`, as the finding says,
but the conclusion drawn is wrong.  `concl_is_false` and `guard_kind_of` ask different
questions on purpose — one reads the guard *as written*, before `Premise_def` is
unfolded; the other reads the state after the guard-side simpset unfolded it, which is
the distinction §4.2 (plan:293-297) exists to hold open.  Merging them would break the
factory's front cut.  And the finding's own expression, applied to the seam it is
moving, would classify every live use `Normal`: `dest_premise_tag_opt` matches only at
the head (PLPR_Syntax.ML:19-21) and every live use sits under a `\<And>`/`\<Longrightarrow>` prefix
(Phi_BI.thy:6217-6218).  **The proposed fix must not be applied verbatim.**

**Resolution.**  In §4.3(a) (plan:316-326) define `concl_is_false` on a **subgoal**:
it performs `Logic.strip_assums_concl` itself and then matches `Trueprop False`.  Then
`quick_cut i th` is `if concl_is_false (Logic.nth_prem (i, Thm.prop_of th)) then
Seq.empty else Seq.single th` — today's behaviour verbatim — step 1½ is
`exists concl_is_false (Thm.prems_of th1)`, and the judge path is the same expression
on `th'`, with no call site able to forget the strip.  §5 stage 1 item 2 (plan:620-621)
notes that the predicate takes a subgoal; §9's pending-name list may note it too, in
case the author prefers a name that says so.  §1's `guard_kind_of` entry (plan:98-108)
keeps `Logic.strip_assums_concl` and its "the same reading `quick_cut` uses" — that is
the first review's F19 resolution and stays true — and gains one clause saying that the
check's `False` test there is its own, accepting the tagged and the bare form, and is
deliberately **not** `concl_is_false`, with §4.4's reason.

---

## F6 — The judge path is prose-only, and no probe reads a conclusion under a prefix

**PARTIALLY_UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  Step 1½ is sketched in ML; the judge path — the other site
that must turn an empty sequence into an explicit `False`-conclusion test, and the
only site where the kind gates an `error` that aborts a build — is given as "changes
the same way" plus one sentence.  Nothing can catch a mistake there: the judge ref is
`NONE` in shipped code, and the only exercise is a prefix-free probe.  Neither the
existing simplifier-refutation probe nor the new regression probe has a prefix either.

**Defence (condensed).**  The headline is false: every one of §6 item 2's five check
probes carries a `\<Longrightarrow>` prefix (plan:680, :683, :686, :690-691, :692), and `run_guard`
makes that prefix the subgoal's prefix, so a `guard_kind_of` that failed to read under
the prefix would fail at least three of them outright.  The `\<And>`-versus-`\<Longrightarrow>` half
has no path at all, since `Logic.strip_assums_concl` recurses through both in one
definition.  The judge-path half is presentation: the first review's R1 correction 1
already required the kind gate and the plan applied it, with no branch an implementer
could resolve two ways, and a probe of a site the shipped `judge = NONE` never reaches
buys nothing.  Conceded narrowly: the caller-side strip at `concl_is_false`'s new call
site is not exercised with a prefix, and the right answer is F9's shape fix, not a
probe.

**Ruling.**  **Headline refuted, residue upheld.**  Verified:
`Guard_Decision_Smoke.thy:120-121` builds the state as `Thm.trivial (Thm.cterm_of ctxt
t)`, so the probe string *is* the subgoal, and the five check probes are all
`<premise> \<Longrightarrow> \<condition> False`.  plan:687-689 and :695-697 name two of them as
discriminators with the readings a wrong kind would give.  `Pure/logic.ML:532-534`
handles `Pure.imp` and `Pure.all` in one recursion, so nothing built on it can read one
and not the other.  `reasoners.ML:1350` is `judge … = Unsynchronized.ref NONE`, so the
judge path has no corpus exercise in any shipped configuration — asking for a probe
there is asking to test a site nothing reaches.

What survives is narrow and real: today the strip lives inside the callee (`quick_cut`
at :976, applied per subgoal through `THEN_ALL_NEW` at :1075), so no caller can forget
it; §4.3(a) moves the test to the caller, and both probes that exercise it
(Guard_Decision_Smoke.thy:677-681 and the new regression probe at plan:702-705) are
prefix-free, while every live `Phi_BI` use has a prefix.  A dropped strip would not
change the verdict — R-conv proves `premises \<Longrightarrow> \<not> False` at once — only the refuter
label and 400 ms, so §6 item 4's digest-and-verdict floor would not catch it either.

**Resolution.**  Take F9's shape fix, which closes this by construction: with the
strip inside `concl_is_false`, no call site carries the invariant and no probe has to
test for it.  Additionally, and at zero cost, give the already-planned regression probe
(plan:702-705) a premise, so that one probe of the new step-1½ test runs under a
prefix.  No new probe, and no ML sketch of the judge path beyond one clause at
plan:330 saying its `case Seq.pull` becomes total the same way step 1½'s does.

---

## F15 — The record attribute and the trace line spell the kind two ways

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  §4.7 gives the record an attribute `kind` = `normal` /
`check_premise_consistency` and, one sentence later, makes the trace line append
", Check_Premise_Consistency" (plan:476-481) — two hand-written spellings of one value
at two adjacent sites, where the file's established shape is one `string_of_*`
function feeding both.

**Defence (condensed).**  Conceded, with the evidence the point did not use: the
file's invariant holds for *all four* value-carrying attributes, not just the verdict.
`verdict` and `hit` both go through `string_of_verdict` (:1365-1367) into the record
(:1575-1576) and the trace (:1581); `refuter` and `judge` are each one string produced
at one place and rendered with each site's own framing (`the_default "-"` in the
record, a prefix or nothing in the trace).  The one defence considered — that the
record wants a lowercase machine token and the trace the constructor's name — is
refuted by the record itself, which carries the capitalized "Provable" at :1577.  The
drift has no functional victim today (neither `path_of` nor `analyze.py` reads the new
attribute), so this is elegance, which is what its severity says.

**Ruling.**  **Upheld.**  I verified every line.  This is the identical argument on
which the first review upheld F13 — "an invariant asked to be remembered where the
file's own sibling shows how to make it structural" — applied twenty lines later in the
same function, and rev 2 already accepted it once in §4.6 ("ONE function prints both
messages", plan:465-472).  Refusing it here would be indefensible.  It is not
nitpicking: the rigour demanded is the rigour the surrounding twelve lines already
have, which is the opposite of criterion (3)'s third clause.

**Resolution.**  §4.7: one `string_of_guard_kind` beside `string_of_verdict`
(reasoners.ML:1365-1367), used by both the record and the trace line, each framing it
as that site frames every other attribute — the record carrying both kinds, the trace
free to print nothing for `Normal`.  §9's pending item becomes the *one* token (and the
function's name), not two literals; its casing is a single open decision, and the
record already holds both a lowercased datatype rendering (`proved`) and a capitalized
one (`Provable`), so the author has a real choice.  Add `string_of_guard_kind` to §5
stage 1 item 2's list of new functions.

---

## F22 — §4.3(c)'s "not a certificate" list misattributes `user_axioms = false`

**UPHELD · minor · DRAFTER_DECIDES_THEN_REREVIEW**

**Claim (condensed).**  plan:386-389 offers "`user_axioms = false`
(reasoners.ML:1256) and the finite scopes (`card 1-6`)" as jointly meaning "a finite
model says nothing about the infinite types the premises quantify over".
`user_axioms = false` says nothing about infinite types: it keeps phi-system's own
axioms out of the problem.  §5 stage 1 item 1 schedules this paragraph into
`guard_refute.ML`, into the same file as a comment that says it right.  The paragraph
also omits that a check's Refuted is accepted at `quasi_genuine` like any other.

**Defence (condensed).**  Conceded on all three legs, with the additional finding that
the first review's F2 resolution item 1 prescribed the certification clause verbatim
and rev 2 dropped it in the rewrite — leaving the hole next to plan:374-377, whose
"so that the label of the result is honest" reads as a promise that a check's model
can come back genuine.  Refuses the finding's proposed replacement clause ("so it may
be no model of the theory the premises live in"), because reasoners.ML:1273-1275
records the opposite weight and a comment in `guard_refute.ML` contradicting the
verdict map it points at is the defect F2 was upheld for.

**Ruling.**  **Upheld, with the defence's refusal accepted.**  Verified:
reasoners.ML:1231-1237 says "user_axioms = false keeps phi-system's ten monomorphic
user axioms out of the problem", the verdict-map block at :1266-1286 says "under
user_axioms = false Nitpick can never certify a model genuine" *and* "all derivable
from HOL's own, so a model ignoring them models a theory no stronger than HOL's", and
`guard_refute.ML:207-208` says the same thing once more in the target file.  A
two-item list that hands one consequence to two causes, only one of which delivers it,
is not a point of taste when the list is scheduled into a source comment twelve lines
from the comment that gets it right.

**Resolution.**  Split the two clauses in plan:386-389: `card 1-6` makes the model
finite, so it says nothing about the infinite types the premises quantify over;
`user_axioms = false` keeps phi-system's own axioms out, so nothing is certified
genuine and a check's Refuted is `quasi_genuine`, as every R-nitpick refutation is —
pointing at the verdict map (reasoners.ML:1266-1286, not the ":1268-1281" the finding
cites) rather than restating it.  Do **not** write "may be no model of the theory the
premises live in" into `guard_refute.ML`.  Keep §7's bullet (plan:763-764) in step
with the split.  This repair is drafted together with F1's rewrite of the same
paragraph, and the third read covers both.

---

## F2 — §6 item 2's "P-auto finds it" probe carries no `fresh` argument

**UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §6 item 2 asserts that "the `fresh` numerals (:220-221) give
every probe a digest no earlier run used" and then writes a probe whose term contains
no `fresh ()` call: `FALLS <elim_chain> \<Longrightarrow> \<condition> False`.  `elim_chain` is a
constant and the check's conclusion cannot carry a numeral, so the digest is identical
on every evaluation; the `guard_decision` log is per process, so the second evaluation
sees two records under one digest and the probe's equality assertion fails — breaking
the same item's "clean twice in a row".

**Defence (condensed).**  Conceded in full, with every link re-checked: the digest is a
pure function of the goal state and the context's assumptions (reasoners.ML:1633-1634)
and this probe's term is closed; the log file is memoized per pid
(`event_log.ML:124-131, :155-162`; `Guard_Decision_Smoke.thy:41-50`); a record is
written on every path including a Proved first decision; and `decide` asserts equality
on the whole filtered list.  Two corrections: "major" is too high — one transcription
slip in the verification section with no design consequence, the grade rev 1's judge
set for the analogous F5 — and "every other new probe carries a `fresh`" is loose,
since §6 item 6's method probes correctly carry none (the method never enters the
factory, computes no digest and writes no record).

**Ruling.**  **Upheld, at minor.**  Verified: `Guard_Decision_Smoke.thy:140-146` is
`filter (fn r => attr "digest" r = Hasher.hex d) (decision_records ())` followed by
`if observed = [path] then () else error (…)`; :46 stamps the log file with the pid;
:24-27 is the theory's own freshness rule; :314 is `val elim_chain = chain_list 800`.
The defence's second correction is right and matters for the fix: §6 item 6's probes
must keep their constant terms.  This is not nitpicking — the consequence is certain,
not hypothetical, and the rigour demanded is the rigour the smoke theory imposes on
itself.

**Resolution.**  Write the probe as `FALLS (<fresh> # <elim_chain>) \<Longrightarrow> \<condition>
False`, the shape `Guard_Decision_Smoke.thy:360` already uses for a list argument, and
extend §6 item 2's invariant sentence with the reason a check probe differs: the
check's conclusion is the literal `False` and cannot carry the numeral, so it goes into
a premise.  `FALLS` has no simp rule and `FALLS_cons` ignores the head (:271-274), so
the probe still exercises P-auto.  §6 item 6's two method probes are unchanged.

---

## F16 — "at most twenty of those decisions are checks" contradicts §3 item 2

**UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §6 item 4 forecasts the corpus's check count from the
`refuter = guard_simp_tac` histogram cell (20).  But §3 item 2 itself describes two
endings for a check today, and the other one — the premises collapse and the goal
closes — is logged `proved` with refuter `-`, i.e. among that leg's 206 proved
decisions, invisible in the refuter histogram.  The same item already asks for the
checks' proved/refuted/unknown split, which only makes sense if proved checks exist.

**Defence (condensed).**  Conceded, with the one escape route closed: a *refuted*
check that hits a `Refuted` entry still shows `guard_simp_tac`, because the
simplification runs at :1478 before the entry branch at :1544-1546, so that cell does
bound the refuted checks exactly; only the proved ending leaks.  Refuses the finding's
behavioural aside that the proved ending is "the common one" on the live `Phi_BI`
rules — nobody has measured the ratio, and the parent plan's PROVED figure comes from a
purpose-built probe, not a corpus run.  The sentence is the first review's F8
resolution transcribed faithfully; the ruling's reason was the defective part.

**Ruling.**  **Upheld.**  Verified in the committed records:
`ai-artifacts/step5/V_on_dbg/…/2026-09-21T135355-2888750.xml` gives
`verdict: {'proved': 206, 'refuted': 166, 'unknown': 5}` and
`refuter: {'-': 357, 'guard_simp_tac': 20}`, and reasoners.ML:1538-1542 reports a
P-auto proof with `refuter = NONE`, logged "-" at :1577.  The parent plan measured the
proved ending on this very guard shape (guard plan §33 item 3), which plan:221-223
cites.  Correcting a first-review ruling with new evidence against its stated reason is
legitimate, and this is that case.

**Resolution.**  Rewrite plan:732-734: twenty bounds the checks that leg *refutes by
the simplifier*, not its checks; a check the guard-side simplification proves is
reported `proved` with refuter `-` and sits among the 206 proved decisions, where no
refuter histogram can see it; the leg's total number of checks is not known in advance
and is itself part of what §6 item 4 reports, through the `kind` attribute.  Do not
write that the proved ending is the common one — nothing measures the ratio.

---

## F12 — The unreachability argument skips the one link that returns `Seq.empty`

**UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(a) says `guard_simp_tac` without the cut "never yields an
empty sequence" and schedules a source comment saying the `NONE` arm is unreachable.
The cited `generic_rewrite_goal_tac` lines are the ones that *contain* the empty
branch; the wrapper that can actually produce it, `PREFER_GOAL`, is not cited; and the
premise that makes the index always in range, `ALLGOALS`, is never stated as a premise.

**Defence (condensed).**  Conceded on the core, with the sharper form: the claim
"`asm_full_simp_tac` cannot [be empty]" is false of the function itself —
`asm_full_simp_tac ctxt 5` on a two-goal state *is* `Seq.empty` — and true only of the
indices `ALLGOALS` supplies.  Two parts do not stand: `ALLGOALS` is named in the same
sentence, so what is missing is one clause, not a paragraph; and the comment must not
carry the derivation, because the project rule is that code comments are concise and
this file's own habit is to point at a plan section (reasoners.ML:85, :1021, :1058,
:1104), the one counter-example being a verbatim-copy sync marker.  Also notes that the
claim is not load-bearing for behaviour, since the plan keeps the case total with
`| NONE => th0`.

**Ruling.**  **Upheld.**  Verified every link myself: `raw_simplifier.ML:1518-1521`
ends in `else Seq.empty`; `simplifier.ML:328` is `PREFER_GOAL (simp_loop_tac 1)`;
`goal.ML:275-277` is empty exactly out of range; `tactical.ML:236-240` fixes the goal
count at entry and descends.  The conclusion holds — I followed the chain — but the
plan as written does not establish it, and it is written into a comment a future reader
will rely on.  This is not rigour beyond the surrounding standard: the parent plan
cites this very class of fact to the line (`GUARD_CACHE_QUICK_MODE_PLAN.md:2617-2619`,
`tactical.ML:320-321` for a `CONVERSION` empty on a missing subgoal).

**Resolution.**  Complete the chain in §4.3(a) (plan:305-310): `asm_full_simp_tac` is
`PREFER_GOAL (simp_loop_tac 1)` (Pure/simplifier.ML:328), which is empty only for an
out-of-range index (Pure/goal.ML:275-277); `ALLGOALS` (Pure/tactical.ML:236-240) fixes
the count at entry and descends over goals the simplification cannot remove, so the
index is always in range; within range `generic_rewrite_goal_tac` returns `Seq.single`
(Pure/raw_simplifier.ML:1518-1521 — noting that its `else Seq.empty` is the
out-of-range branch just excluded) and `simp_loop_tac`'s continuation cannot fail
(Pure/simplifier.ML:325-327).  The **source comment** keeps one concise clause plus a
pointer to §4.3(a), per the file's own habit; the derivation lives in the plan.

---

## F4 — §6's undecided probe cannot discriminate the unknown-tolerant rail

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §6 item 2 says of the undecided probe that "with the premise
still sliced away **or still on the tolerant rail** it would read ('refuted', …)".
The second disjunct is wrong: `BADN n = False` is a plain definition Kodkod evaluates
as definitely false, and the relaxed encoding only lifts *unknown*, so the tolerant
rail changes nothing there.  The probe guards the slice and only the slice; and since
every construct of the smoke theory is evaluable, no probe separates "premises as
antecedents" from "premises as assumptions on the tolerant rail" — the very change
ruling 10 made.

**Defence (condensed).**  Concedes the six-word clause and the reason.  Refutes the
headline: ruling 10's change in the code is one `case` arm in `preprocess`, and the
premises become antecedents precisely by not being split and sliced — there is no
second switch — so the undecided probe does exercise it (today "refuted / R-nitpick",
after the edit "unknown"), with `CHAIN [<fresh>]` as its positive counterpart.  What no
probe sees is the *rail*, a sub-aspect that is not a path of the planned code.
Refuses the proposed new probe: a construct whose defining property is "Kodkod cannot
evaluate it" would hold the smoke test hostage to Nitpick's finitization internals at
every rebase, where every existing construct rests on a stable mathematical property.

**Ruling.**  **Clause upheld, headline refuted.**  Verified: `BADN n = False`
(Guard_Decision_Smoke.thy:248) and the committed probe at :367-369 that relies on
Nitpick evaluating it; phi_nitpick.ML:519-524 states the relaxed flag as "encode
unknown at positive position as true rather than false", which cannot rescue a formula
that is definitely false.  And the first review's own F18 resolution asked for one
sentence "naming it as the probe of the slice, with the reading it would give if the
slice were still on" — the drafter over-extended that to the rail.  Severity minor, not
major: stripped of the false headline this is a six-word deletion.  I refuse the new
probe for the defence's reason, which is the author's criterion (2): a test resting on
an artefact of a vendored tool's representation choice is a dirty hack in test
clothing.

**Resolution.**  Delete "or still on the tolerant rail" from plan:696.  Add one
sentence saying that the rail is settled by inspection of the call shape rather than by
a probe — **but that sentence must be written against F1's corrected §4.3(c)**, not
against the present text: the plan may no longer say "the flag affects nothing", and
what stage 1 records is *what the flag moves*.  Alternatively, state plainly that the
rail is not probed at all, which is what §7 will say under F1.

---

## F7 — Texts the change falsifies are off the stage 1 and stage 3 checklists

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  Five live texts the change makes wrong are missing from the
checklists: (a) reasoners.ML:1021-1028, the file's overview of one `prove_or_refute`
call; (b) R-nitpick's doc comment at :1167-1190, three of whose sentences §4.3(c)
falsifies; (c) the *body* comment at :1355-1357 enumerating the record's fields, whose
signature twin is on the checklist; (d) `Guard_Decision_Smoke.thy:685-686`, still
explaining the judge's third error as "which quick_cut drops"; (e) the guard plan's §39
ruling 10, which states the mechanism as "`quick_cut` leaves no state" and repeats it
in its "Stated consequences", while stage 3 names §39 only for "the timeout path's
reason".

**Defence (condensed).**  (a) refuted — that overview already omits the refutation by
the simplifier today, so the change leaves a pre-existing elision exactly as elided,
and "the entry's verdict selects what runs next" becomes incomplete, not false.  (b)
one sentence of three, not three: :1169-1172 stands (the slice and "whose premises are
trusted rather than re-derived" both acquire a per-kind case, and `r_nitpick` itself
gains the kind while its doc comment is off the checklist); :1181-1184 and :1187-1190
stay true, since the call at :1320-1321 still assembles the full assumption set and
still threads `subst`, the divergence being one layer down inside `preprocess`, whose
comment is already scheduled.  (c), (d), (e) conceded, with two corrections: the
judge's third error runs through the *judge path's own* test, not the refutation by the
simplifier, so §6 item 2's blur (plan:710-712) must be corrected with it; and stage 3's
"§39 (the timeout path's reason)" is mis-aimed as well as narrow, since that reason
lives in the guard plan's §1 `guard_simp_tac` entry, which stage 3 already schedules.

**Ruling.**  **(a) refuted; (b) upheld for one sentence; (c), (d), (e) upheld.**
Verified all five.  reasoners.ML:1021-1028 reads "the guard is simplified once
(guard_simp_tac), P-auto proves the guard or fails, and on a failure the entry's
verdict selects what runs next" — no mention of the step-1½ ending today, so nothing
the change falsifies; holding an eight-line altitude map to the standard the plan
applies to verbatim enumerations is the one part of this point that asks for rigour the
surrounding code does not have.  reasoners.ML:1355-1357 is verbatim the twin of
:193-196, which plan:630 schedules, and §4.7 adds an attribute to both.
`Guard_Decision_Smoke.thy:685-686` says "which quick_cut drops", and the judge path is
reasoners.ML:1514-1516, which plan:330-337 replaces.  The guard plan's §39 carries
ruling 10's "`quick_cut` leaves no state" and the "Stated consequences" line, while the
timeout path's reason is in its §1 entry ("Not `timed_tac`, whose timeout is an empty
sequence and would read as that refutation by simplification").

**Resolution.**  Add to §5 stage 1 item 2: R-nitpick's doc comment, naming the one
sentence at reasoners.ML:1169-1172 that gains the check's case (and stating that
:1181-1184 and :1187-1190 stay true), and the body copy of the record's attribute list
at :1355-1357, the twin of :193-196.  Do **not** add reasoners.ML:1021-1028.  Add to
stage 1 item 4: the comment on the judge's third error
(`Guard_Decision_Smoke.thy:685-686`), whose "which quick_cut drops" becomes the judge
path's own test; the probe's expectation is unchanged.  Correct §6 item 2's sentence at
plan:710-712, which currently assigns both existing probes to the refutation by the
simplifier: the judge's third error runs through the judge path.  Widen stage 3's §39
item to name ruling 10's mechanism, the step-1½ and judge-path shapes and the "Stated
consequences" line, and move "the timeout path's reason" to the §1 entry where it
lives.

---

## F8 — Three line citations name the wrong code

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  (a) "`p_auto_attempt` :120" — :120 is the second line of
`p_auto_tac`'s comment.  (b) "`prove_or_refute` :102" — :102 is `val guard_digest`, so
the one signature line that must gain the kind alongside `guard_digest`'s is on no
checklist entry.  (c) "a Proved first decision writes none, :1551-1553" — that is
`end`, a blank line and `val outcome =`; the write suppression is :1540-1541.

**Defence (condensed).**  Concedes (c) — the citation points at nothing and is outside
the tolerance the first review's lenses used — while noting its consequence is nil
(the claim is restated without a citation at plan:722 and the misdirected reader lands
twelve lines from the branch).  Calls (a) and (b) nitpicking: in a signature block
every line is a different declaration, so "it lands on the neighbour" is what an
off-by-one *means* there, and the first review self-dropped exactly this class.  On
(b)'s escalation: the sub-list is introduced by "the comments:", `prove_or_refute` has
no comment in the signature block, the two type changes are named in the item's main
clause (plan:623, :626), and a stale declaration at :102/:103 is a signature-match
error at reasoners.ML:201 — so the consequence cannot occur.  Notes the same sub-list
carries two more slips the finding did not raise (`:112-116` for a comment running
:112-117; `:192-196` for one running :193-196).

**Ruling.**  **(c) upheld; (a) and (b) upheld as citations, refuted as escalations.**
Verified: :102 is `val guard_digest`, :103 is `val prove_or_refute`, :119-120 is
`p_auto_tac`'s comment and :122-123 `p_auto_attempt`'s; :1551 is `end`, :1553 is
`val outcome =`, the suppression is :1540-1541.  The defence is right that the
declaration changes are compiler-enforced — reasoners.ML:1 opens the signature, :198
closes it, :201 ascribes the structure to it — so F8(b)'s "covered by no checklist
entry at all" overstates a real citation slip into a hazard that cannot occur; by
criterion (1) an invariant the type checker enforces is the good case, not a gap.  But
under either reading the citation is wrong: `prove_or_refute` has no comment at :102,
and :102 is another function's declaration.  Three wrong numbers in a checklist an
implementer follows are worth two minutes.

**Resolution.**  Correct `p_auto_attempt` to :122-123, `prove_or_refute` to :103
(keeping `guard_digest` :98-102 so its own `val` line stays covered), and "a Proved
first decision writes none" to :1540-1541.  While in that sub-list, sweep the two the
finding did not raise: `guard_simp_tac` :112-117 and the record's attribute list
:193-196.

---

## F11 — The timeout path's surviving reason is never stated

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.3(a) retires the stated reason for the 60 s timeout path
and says it "loses that reason and keeps its shape", while §5 stage 1 item 2 schedules
the comment rewrite as "the timeout path's reason" — without ever saying what the
surviving reason is.  An implementer told only that the old reason is gone may call
the branch vestigial or delete it, and a 60 s simplification timeout would then abort a
build instead of warning.

**Defence (condensed).**  Concedes the gap: the plan orders the same retired reason
rewritten in three places (reasoners.ML:1066-1068, the parent plan's §1 entry and its
§39) and supplies no replacement text, in a document that hands over the exact wording
of every other text it touches.  Refutes the scenario — the same sentence asserts the
post-hoist invariant that `guard_simp_tac` never yields an empty sequence, which is
false unless the timeout path yields a state — and refutes the consequence twice: the
warning is emitted inside the handler before its value is returned (:1078-1082), and
`p_auto_tac` keeps only solved states (:1053, :1091), so the attempt still fails unless
P-auto proves the goal within 400 ms, exactly as today.  What the shape really buys is
one 400 ms P-auto attempt on the unsimplified state.  Refuses the finding's wording,
which pins a function's invariant to one caller's combinator.

**Ruling.**  **Gap upheld, consequence refuted.**  Verified: reasoners.ML:1078-1082 is
the handler, warning first; :1053 is `solved_states search st = Seq.filter Thm.no_prems
(search st)`, used by `p_auto_tac` at :1091; :1097-1098 is `p_auto_attempt`'s `THEN`;
the three call sites of `guard_simp_tac` are :1098, :1478 and :1514, and the plan makes
the latter two total.  "Would abort a build instead of warning" is wrong; the honest
residue is a narrow completeness chance on a path the comment itself describes as the
simplifier looping.  The gap is nonetheless real and cheap.

**Resolution.**  In §4.3(a) (plan:311-313) replace "loses that reason and keeps its
shape" with the surviving reason stated at the level of the function: after the hoist
`guard_simp_tac`'s post-condition is that it always yields exactly one state, and the
timeout path is the only place that could fail; the caller that would notice is
`p_auto_attempt` (:1097-1098), which composes with `THEN`, so an empty sequence there
is a failed attempt — the out-of-run instance's `error` (:1646-1650) and the method's
failure — not a verdict; inside `prove_or_refute` emptiness is already harmless because
both pulls are total.  Put that in the rewritten source comment.  In §5 stage 3, say
that the parent plan's §1 `guard_simp_tac` entry carries the retired reason
(`GUARD_CACHE_QUICK_MODE_PLAN.md`, §1, "Not `timed_tac` …") and gets the same
replacement — which is also F7(e)'s correction to the §39 item.

---

## F13 — `trust_assms` = `kind = Normal`, and §4.1's classification

**PARTIALLY_UPHELD · minor · DRAFTER_APPLIES_NO_REREVIEW**

**Claim (condensed).**  §4.1 states the discipline the datatype buys — "Every consumer
writes both cases in a `case`" — and four of five sites obey it.  The fifth collapses
the kind back into a bool by an equality test, `(kind = Normal)` (plan:368, :614), at
exactly the parameter whose bool form ruling 11 replaced and whose meaning is most
treacherous.

**Defence (condensed).**  §4.1 sorts the five functions into two classes in the same
sentence and §1 pins "consumer" to the three that *branch*, placing
`Phi_Guard_Refute.nitpick` among the pass-alongs, so no rule is broken.  `trust_assms`
is not the parameter ruling 11 replaced — that was phi-system's own
`assume_consistent`; `trust_assms` is a `bool` in the vendored Nitpick's signature
(phi_nitpick.ML:93-96), a foreign boundary stage 1 deliberately does not edit.  The
demand exceeds the surrounding rigour: PLPR's own engine writes
`bmode <> ALLOW_BACKTRACK` over a three-constructor datatype (reasoner.ML:879, :882),
the callee's file writes `mode = Normal`, `mode = Auto_Try`, `mode <> Normal`
(phi_nitpick.ML:119, :239, :263), and guard_refute.ML:228 collapses three values into
two by equality *two lines below the site under attack*.  The first review refuted F14
on the same ground.

**Ruling.**  **The spelling demand is refuted as nitpicking; one word of §4.1
survives.**  I verified the idiom at every site the defence names, and it is
overwhelming: this codebase steers behaviour by equality on datatypes in its own
engine, in the vendored copy and in the very function being edited.  A `case` here
makes nothing impossible that `=` allows; both are total and both yield the same bool.
Invoking criterion (1) for a change that leaves the invariant exactly as violable is
criterion (3)'s case, as the first review said of F14 in almost these words.  The
finding's two rhetorical props are also misattributions: ruling 11 replaced
`assume_consistent`, not `trust_assms`, and F1 did not rule that "its effect is not
what the plan says it is" in the sense the finding borrows.

What survives is one classification word, and it survives only because F1 changed what
that line means.  `Phi_Guard_Refute.nitpick` does not merely "pass the kind along"
(plan:268-271): it reads the kind to produce `trust_assms`, and under F1 that read is a
deliberate choice about which rail Nitpick's machine-generated axioms take — not a
label formality.

**Resolution.**  No `case` is prescribed; the spelling is the implementer's.  If the
author keeps `false` (C-1), §4.1's sentence gains `Phi_Guard_Refute.nitpick` among the
functions that *read* the kind, with one clause saying what its read decides, so that a
reader meets the choice where it is made.  If the author takes R1, the line disappears
and §4.1 is true as written.  Either way this is one sentence, applied with F1's
rewrite.

---

## F5 — The new `\<^descr>` tells the user R-nitpick is asked for a model of "the premises themselves"

**NITPICK_REJECTED · none · NO_ACTION**

**Claim (condensed).**  The user-visible paragraph ends "— R-nitpick is instead asked
for a model of the premises themselves", but what it is asked for is a model of the
premises *after* `is_premise` has dropped untagged context assumptions and after the
`Preprocess_Hooks` have rewritten and deleted premises — the weakening §7 records and
that §4.3(c) was rewritten to stop claiming.  Secondarily, the same sentence is a
fourth wording for one glossary concept.

**Defence (condensed).**  "Instead" points at the item immediately before it,
"R-nitpick's premise slice", and "themselves" contrasts with a *slice* of them, not
with "untransformed by every internal step".  The `is_premise` leg attacks a referent
the plan does not use — §1 defines "the premises" as what `premises_of` collects and
the filter is *inside* `premises_of` (guard_refute.ML:116) — which is exactly the
correction the first review's judge endorsed.  The hooks leg is factually right and
reaches nothing: the `\<^descr>` says what R-nitpick is *asked for*, and the worst
consequence is a branch that stays live, the conservative outcome, which the same block
states one paragraph up.  The proposed wording is worse: "as it preprocesses them"
names an ML function invisible to a user of PLPR.thy.  On terminology: the plan's
canonical phrase is used in every operative passage, and the `\<^descr>` is a different
document for a reader who has no antecedent for a bare definite description.

**Ruling.**  **Refuted on both legs, and both are nitpicking.**  I verified that
`is_premise` is applied at `guard_refute.ML:116`, inside `premises_of`, so §1's
definition of "the premises" already includes it — the first review ruled this at
:225-227 and this round brings no new evidence against that reason.  I verified
plan:533-534: the sibling paragraph, in the same edit, tells the user "a rule protected
by it applies only when `P` is decided provable" — so no reader can act wrongly on the
sentence under attack.  And I verified the ambient level of disclosure: the existing
`\<premise> P` paragraph (PLPR.thy:219-226) and the plan's own replacement for
`\<condition> P` (plan:529-535) name no internals at all.  Requiring the check's
paragraph alone to disclose a hook registry is a standard nothing around it meets —
criterion (3)'s third clause.  The terminology leg miscounts: plan:46-47, :179, :296,
:304, :623, :688 and :704 all use the glossary phrase, and the `\<^descr>` inlines its
defining content because in PLPR.thy the bare phrase has no antecedent.

**Resolution.**  Nothing changes.  One free offer, since the author rules on this
paragraph in §9 anyway: the plan's own glossary says "Refuted = a finite model of them
exists" (plan:128-130), so "asked for a finite model of the premises" costs one word
and matches the glossary.  That is the only content in the finding's wording; the rest
must be refused.

---

## F10 — The signature checklist and "exported where §6 needs them"

**NITPICK_REJECTED · none · NO_ACTION**

**Claim (condensed).**  §5 stage 1 item 2 never says that `val guard_digest` and
`val prove_or_refute` change type, nor how the datatype enters a signature that is an
`include` extension; and "exported where §6 needs them" is unresolved and, read
literally, over-exports `guard_kind_of`, working against §4.2's aim.

**Defence (condensed).**  "Exported where §6 needs them" is a *restriction*, not a
licence, and it resolves in one step: a grep of §6 finds no `guard_kind_of` and no
`concl_is_false` — the only occurrences are `guard_digest` with the two constructors in
the digest-marker probe — so the clause yields exactly the export set the point
proposes as its fix, and `guard_digest_of`'s export is stated in so many words at
plan:289-291.  The declaration edits are compiler-forced:
`structure Phi_Reasoners : PHI_REASONERS` (reasoners.ML:201) and
`structure Phi_Guard_Refute : PHI_GUARD_REFUTE` (guard_refute.ML:36) are
signature-ascribed, and the sole external caller of `guard_digest` is
`Guard_Decision_Smoke.thy:76`, which stage 1 item 4 rewrites.  The datatype's form has
an in-file precedent one screen above its insertion point (guard_refute.ML:19).

**Ruling.**  **Refuted, and this is nitpicking.**  I ran the grep myself over
plan:665-747: `guard_kind_of` and `concl_is_false` do not occur in §6 at all.  So the
claimed consequence — that the plan over-exports `guard_kind_of` and invites a second
site to compute the kind — has no path to occur under the plan as written; it is
manufactured by reading a restrictive clause as a permissive one.  And asking a plan to
enumerate declaration edits that the ML signature ascription makes impossible to omit
is precisely the inversion the author's first criterion warns against: it converts a
compiler-enforced invariant into a remembered one, and it would have to be kept in step
with §6 by hand.  Item 1 discharges the same work in three words ("the signature")
without enumerating either.

**Resolution.**  Nothing changes.  If the drafter wants items 1 and 2 to read
symmetrically, the whole remedy is the three words "the signature" added to plan:619-620
— not an enumerated export list.

---

## F14 — The smoke test's warning constants and helpers are off the checklist

**REFUTED · none · NO_ACTION**

**Claim (condensed).**  §5 stage 1 item 4 enumerates the smoke-test edits in detail but
not the warning machinery, and §6's undecided check probe asserts a combination the
file's three helpers cannot express: "There is no way to express 'the undecided-check
line once and the undecided-guard line zero' without a fourth constant and a fourth
helper."

**Defence (condensed).**  That load-bearing sentence is false.  The mechanism is not
the three helpers but one parametric function,
`fun assert_warnings name line expected ws` (Guard_Decision_Smoke.thy:202-206), which
takes the line *and* the expected count; four calls express §6's expectation exactly,
and whether the implementer wraps them is taste inside a test file.  Everything needed
is already in the plan: item 4's first clause is "the probes of §6", §6 states all four
counts, and §4.6 gives the warning's first line verbatim and approved.  Item 4's other
clauses are precisely the edits "write the probes of §6" does *not* imply — existing
text that becomes false or fails to compile if left alone.  The first review's F17
upheld a complaint of this shape because the named text became *wrong*; F14 names no
text at all.

**Ruling.**  **Refuted**, and it is also nitpicking.  Verified:
`Guard_Decision_Smoke.thy:202-206` is parametric in both the line and the count, and
:207-215 are three-line wrappers over it.  The finding's one operative sentence is
false, and with it the claimed gap.  The distinguishing line against F17 is exactly
right: a checklist owes the *existing* texts the change falsifies (`digest_of` at :76,
the reachability constraint at :14-20), not the new bindings a new probe cannot be
written without.  Applied uniformly, F14's standard would transcribe §6 into §5, giving
two places to keep in sync — the opposite of the shape the author's first criterion
prefers.

**Resolution.**  Nothing changes.  The plan must not dictate whether the assertion is
written as four `assert_warnings` calls or as a fourth wrapper; that is the
implementer's.

---

## F17 — §6 item 6's negative control "cannot be written as a theory command"

**REFUTED · none · NO_ACTION**

**Claim (condensed).**  A `lemma … by \<phi>guard_P_auto` that must *fail* leaves the
command in error, and §6 item 2 requires the smoke theory to be clean twice in a row.
"The repository has no 'this proof must fail' idiom", and the file's only failure idiom
captures an `ERROR` at the ML level.

**Defence (condensed).**  Isabelle ships exactly that idiom and it is already in scope:
`HOL-Eisbach`'s `fails` method (`Eisbach.thy:106-119`), whose tactic is
`case Seq.pull (method_evaluate m ctxt facts st') of SOME _ => Seq.empty | NONE =>
Seq.single st'` — precisely the failure mode the finding itself describes for
`\<phi>guard_P_auto`.  `PLPR.thy:2` imports `"HOL-Eisbach.Eisbach"` and the smoke
theory imports PLPR.  Written `apply (fails \<open>\<phi>guard_P_auto\<close>) oops`, with
`oops` used at eight sites in this repository, it is still two lines and leaves no
error.  The finding's grep was for English phrases, which a method named `fails` and a
command named `oops` cannot match.  Its proposed fix is a regression: an `ML` block
calling `Phi_Reasoners.p_auto_attempt` bypasses the `method_setup`, and covering that
wrapper is the entire reason §6 item 6 exists.

**Ruling.**  **Refuted**, and it is nitpicking.  Verified: `Eisbach.thy:106-119`
defines `fails` with that tactic and documents it as "succeeding only if the given
method would fail"; `PLPR.thy:2` imports Eisbach; `Guard_Decision_Smoke.thy:2` imports
PLPR.  The claimed consequence — an errored command in a theory §6 requires to be clean
— cannot arise, because the remedy is imported two lines above.  The demand is also
above the surrounding standard: §6 spells out no probe's source text anywhere, item 2's
eight bullets state assertions rather than syntax.  And the proposed remedy would
destroy the only coverage the item exists for, which the first review established by
grep (the method has no caller anywhere).

**Resolution.**  Nothing changes.  If the drafter wants to spare the implementer the
lookup, the whole of it is a parenthetical after "must still fail" — "(Eisbach's
`fails`, then `oops`)".  That is editorial, not a condition, and the finding's own
proposed ML replacement must be refused.

---

## F18 — The hoist gives up the short-circuit of the refutation by the simplifier

**NITPICK_REJECTED · none · NO_ACTION**

**Claim (condensed).**  Today `ALLGOALS (simp THEN_ALL_NEW quick_cut)` empties the
sequence at the first subgoal left as `False`, so the remaining subgoals are never
simplified; the new shape computes `th1` with every subgoal simplified and only then
reads the refutation off it.  On a multi-subgoal guard every refutation now pays the
simplification it used to skip, and §7 does not record it.

**Defence (condensed).**  Mechanism conceded and verified; consequence refuted by
measurement.  The extra work arises only on a decision that is both refuted by the
simplifier *and* has two or more subgoals, and that intersection is empty in the
committed records: in the `V_on_dbg` leg — the post-§39 baseline §6 item 4 itself cites
— all 20 refutations by the simplifier are on one-subgoal states and no record exceeds
one subgoal; across 3908 records in seven legs only 8 exceed one subgoal, all in one
theory and all with `refuter = "-"`.  Even where it would occur it is what a
non-refuting decision on the same state already pays today, still capped by the 60 s
bound, and the verdict, the reported `goals` and the record are identical.  §7's
bullets are all either a semantic weakening or a cost with a stated magnitude on a path
that runs.

**Ruling.**  **Refuted, and this is nitpicking.**  I ran the cross-tabulation myself
over `ai-artifacts/step5/*/event_log/guard_decision/*.xml`: in `V_on_dbg` all 20
`refuter="guard_simp_tac"` records carry `subgoals="1"` and nothing in that leg exceeds
1; in `G_examples` the 8 records with `subgoals="8"` all carry `refuter="-"`.  So the
loss has zero measured magnitude on the plan's own baseline, and the demanded §6 clause
asks stage 2 to re-report a number already committed to the tree — criterion (3)'s
first and third clauses at once.  Semantically nothing changes: both shapes refute
exactly when some subgoal's conclusion is `False`, and the plan keeps `goals`
two-branched.  A bullet whose loss is semantically nil and whose magnitude is measured
zero would lower §7's threshold, which by the author's first criterion makes the
register worse, not more complete.

**Resolution.**  Nothing changes.  If the author nevertheless wants the difference on
the page, it belongs as half a sentence in §4.3(a), where the shape is described, and
it must carry the measurement — not in §7.

---

## F19 — `GUARD_NITPICK_FALSIFY_PLAN.md` is omitted from stage 3's document list

**REFUTED · none · NO_ACTION**

**Claim (condensed).**  `guard_refute.ML`'s own header sends every reader of the file to
`Docs/GUARD_NITPICK_FALSIFY_PLAN.md` §19-§22, and this plan changes exactly what those
sections record — `preprocess`'s contract and the `trust_assms` argument of the
vendored Nitpick, whose patched line that document quotes verbatim.  After stage 1 a
reader following the header lands on a pipeline description that no longer matches.

**Defence (condensed).**  That document is a closed, dated, layered log whose own
convention is that a later section supersedes an earlier one (§22 says so of §19-§21;
§21.4 corrects §19.5 without editing it), and it is *already* stale against today's
code by a far wider margin: §22.1 defines the pipeline as a concurrent race, and
`Race` does not occur in reasoners.ML at all.  The precedent is explicit and goes the
other way: the guard plan — which dismantled that race — names the falsify plan once as
"Predecessor" and updates none of it.  One of the finding's two pillars is simply
false: this plan does not edit `phi_nitpick.ML` (stage 1's file list excludes it), so
the quoted patch line stays verbatim true; only the value the *caller* passes changes,
and under `Normal` that value is `true`.  The `preprocess` half is narrowed, not
contradicted, and is documented where it belongs — in the file's own comments, which
stage 1 item 1 already rewrites.

**Ruling.**  **Refuted**, and it is nitpicking.  Verified:
`DEBT_AXIOM_FILTER_PLAN.md:13-14` records the falsify plan as "the guard-race redesign,
closed 2026-09-01"; `GUARD_NITPICK_FALSIFY_PLAN.md:1869-1870` states the supersession
convention; §22.1 describes the race; `/usr/bin/grep -c "Race\." reasoners.ML` returns
0; and `GUARD_CACHE_QUICK_MODE_PLAN.md` mentions the falsify plan on exactly one line,
as its predecessor, with no update scheduled.  The divergence the finding fears already
exists and was not created here, and the demand holds this plan to a standard a much
larger predecessor project declined — criterion (3)'s third clause.  The `trust_assms`
pillar is false on the facts.

**Resolution.**  Nothing changes in stage 3.  If the author wants the archive
signposted, the honest act is one dated line in the falsify plan's own status block
saying the guard plan superseded the race — a repair owed by the guard plan, not by
this one.

---

## F20 — `guard_kind_of` re-spells `Thm.major_prem_of`

**NITPICK_REJECTED · none · NO_ACTION**

**Claim (condensed).**  §1 prescribes that `guard_kind_of` read the premise's
conclusion with `Logic.strip_assums_concl` and answer `Normal` for a state with no
premise.  That reading already has a name: `Thm.major_prem_of` *is*
`Logic.strip_assums_concl` of the first premise, it is in scope unqualified, and
reasoners.ML uses it at five live sites — including `oblg_template`, which reads the
same state one step later.

**Defence (condensed).**  Settled by the first review: F19's resolution ordered, in as
many words, "keep `Logic.strip_assums_concl` in `assume_consistent_of` and say why",
and the same judge stated the `major_prem_of` equality thirteen sections later, so the
fact was in front of him when he ruled.  The plan gives `guard_kind_of` **no body** —
the name occurs eight times and never as a definition — so nothing forbids the
implementer from writing `Thm.major_prem_of`; the finding's practical wish is already
available with no plan change.  Calling `Logic.strip_assums_concl` is not reinventing a
wheel, it is the wheel.  The proposed §1 wording hides the two decisions the glossary
exists to state — which premise, and that the read goes *under* the prefix — and the
`try` half would swallow unrelated exceptions into a silent `Normal` for an arm that
`oblg_template`'s own unguarded `major_prem_of th00` (reasoners.ML:383) shows is
unreachable.

**Ruling.**  **Rejected as nitpicking.**  Verified: `Pure/thm.ML:541-544` is exactly as
both sides say; `CHECK_HYPOTHESIS_CONSISTENCY_REVIEW_2026-09-22.md:822-824` is F19's
resolution ordering the present wording, and :952-953 is the same judge writing
"`major_prem_of` is `Logic.strip_assums_concl` of the first premise
(`Pure/thm.ML:541-544`)".  This round's rules say a point already ruled is re-raised
only with new evidence against the stated reason; a restatement of the fact the judge
himself used is not new evidence.  And the point attacks code that does not exist: the
plan constrains the reading, not its spelling.

**Resolution.**  Nothing changes.  If the drafter wishes, §5 stage 1 item 2 may note
that the read may be spelled `Thm.major_prem_of` — an optional clause, not a condition.

---

## F21 — `preprocess`'s result pair keeps its type and its names while its contract changes

**REFUTED · none · NO_ACTION**

**Claim (condensed).**  Under §4.3(c) `preprocess` returns (premises, conclusion) under
`Normal` and `([], residue)` under the check, where `residue` is a whole implication
chain; the caller binds `SOME (prems, concl)` and passes it positionally, so for the
check `concl` is not a conclusion and `prems` is not the premises, while the exported
type is unchanged — the objection on which the first review's F20 was rejected, now
applying to the accepted shape.

**Defence (condensed).**  The load-bearing premise is false: under the plan
`preprocess` takes the kind as its **first** parameter (plan:358, stage 1 item 1 lists
"the signature"), so the exported type changes and announces the dependency — which is
exactly the answer to F20's objection that the old proposal "leaves its type alone
while changing its contract".  The contract does not change with the kind either: the
pair has one use, spread positionally into `pick_nits_in_term`'s `nondef_assm_ts` and
`orig_t` under **both** kinds, and `prems` is read nowhere else in the function.  The
proposed rename would delete a true and useful fact under `Normal` and would put a
second assumption-flavoured name beside the existing `assms` parameter, against ruling
12's one word.  The place a reader meets the distinction is the comment block
immediately above the binding, which stage 1 already schedules.

**Ruling.**  **Refuted**, and it is nitpicking.  I verified the decisive facts:
plan:358 writes `Phi_Guard_Refute.preprocess kind ctxt assms goal` and plan:609-614
lists "the signature" among stage 1 item 1's edits, so the exported type changes;
`guard_refute.ML:216-227` shows `prems` and `concl` going into the same two positional
arguments under both kinds, with `prems` read nowhere else; `phi_nitpick.ML:977-978`
confirms those positions.  A point whose headline clause ("while the exported type is
unchanged") is false, and which then asks for two local variables inside one private
module to be renamed in code that has not been written, is a point of taste with no
consequence — and the first review refuted F20 on the same ground, that this is a
module with a single external caller.  The signature-block demand is also above the
file's own standard: `slice`, `preprocess` and `nitpick` carry no signature comment
today (guard_refute.ML:29-33); their rationale is body comments by design.

**Resolution.**  Nothing changes.  §4.3(c) and stage 1 item 1 already give `preprocess`
the kind as its first parameter and already schedule the per-kind account into both
comment blocks a reader of the binding meets (guard_refute.ML:168-174 and :202-214).

---

## The relaxation proposals

### R1 — Leave `Phi_Guard_Refute.nitpick`'s `trust_assms` at the literal `true` for both kinds, and re-put ruling 10's second half to the author with the facts

**PROPOSE_TO_AUTHOR — recommend accepting for stage 1.**

**The proposal.**  Ruling 10's second half — "所以你的建议是在 Check_Premise_Consistency
模式下不启动 trust rail 吗？我赞同" (plan:185-186) — is already honoured by the shape the
same ruling chose: with the premises as antecedents, the conjecture is the **head** of
Nitpick's nondefinitional list and the head never gets the relaxed flag, whatever
`trust_assms` says.  What passing `false` additionally does is (i) move Nitpick's own
machine-generated nondefinitional axioms from the unknown-tolerant rail to the strict
one and (ii) change a label that is forced to `quasi_genuine` here and that the caller
discards one line later.  The plan's only stated reason is (ii).  So as drafted the
plan pays an unmeasured change of the model search for a distinction nothing reads.

**What I verified, beyond F1's chain.**  `nitpick_preproc.ML:1040` returns
`(neg_t :: nondefs, …)`, so the negated conjecture is the head;
`phi_nitpick.ML:530` gives the head the problem's own `unsound`;
`guard_refute.ML:202-205` says the same from the other side.  So ruling 10's subject —
the premises — is off the tolerant rail under both values, and the author's approval
rested on a premise ("there is nothing to trust") that is false of everything else in
the problem.  **That is why it must be re-put rather than simply applied.**

**One correction to the proposal, which the author should have.**  R1 claims that with
`true`, §0's sentence "with no assumptions handed over, there is nothing to trust"
would become true as written.  It would not: under `true` the machine-generated axioms
*are* trusted.  §0 must be rewritten under either option (F1 resolution item 1).  R1's
mention of "F13's `case`" also mis-points; what vanishes under `true` is plan:368's
`(kind = Normal)`, plan:614's instruction and plan:373-379.

**My recommendation, and the honest case against it.**  Take `true` for stage 1.

- Nothing unsound is reachable either way: R-nitpick reports Refuted or stands down
  (guard_refute.ML:228-229), and for the check a Refuted only leaves the branch live.
- With `true` the check's Nitpick call is identical to an ordinary guard's in every
  respect but the one the design intends, so any difference in the stage-2 verdict
  split is attributable to the antecedents alone.  With `false`, the split mixes two
  changes and, as F1 establishes, no instrument in this plan can separate them.
- `false` can only turn a Refuted into an Unknown.  For the guard's *applicability*
  the two are the same (plan:128-131), so strictness buys no correctness; but an
  Unknown entry re-consults the judge on every run where a Refuted entry costs about
  1 ms (plan:766-768, and §8's own reason for rejecting R2 at :858-861), and it fires
  the undecided-check warning at level 1.  So the price of `false` is cost and noise.
- It is also the ordering the first review already recommended to the author: "leave
  `true` in stage 1 and decide on stage 2's evidence" (review:192-193).
- Cost of `true`, stated plainly so the author can weigh it: a check's Refuted may rest
  on a class or equational axiom that was merely "not definitely false", i.e. on a
  model of a theory weaker than the one the premises live in.  §7 must then record the
  machine-generated axioms' tolerant rail as a **third weakening** alongside
  `is_premise` and the hooks — which is exactly what the first review's F1 resolution
  item 3 flagged as new to the author and needing his word.  A reader who thinks a
  guard that *asks about consistency* deserves the strict treatment will prefer
  `false`, and that is a defensible position I am not entitled to overrule.

Either way, the text repairs of F1 are required; they are not contingent on this
choice.

### R2 — Let `guard_simp_tac` return a state instead of a one-element sequence

**DROP.**  The proposal's facts are right — after the hoist the function yields exactly
one state, its three call sites all pull immediately, and it has no caller outside
reasoners.ML — and I verified the totality chain myself (the same chain as F12).  But
the gain is two unreachable `case` arms, and the price is a name that stops meaning
what it says: every `*_tac` in the exported signature is a tactic (reasoners.ML:118,
:121, :124, :140, :168-169).  Renaming is the only clean repair and costs far more: the
name is the author's own ruling (guard plan §39 ruling 1), a parent-plan glossary term,
and — decisively — the literal string written into every decision record,
`val simp_refuter = "guard_simp_tac"` (reasoners.ML:1389), asserted verbatim by an
existing probe (Guard_Decision_Smoke.thy:680) and by this plan's new regression probe
(plan:702-705).  It also reopens the property that won ruling 9: R1 was accepted in the
form where `guard_simp_tac` and `p_auto_attempt` keep today's code (plan:16-19,
:180-181), and this edits both.  Under criterion (4) the bar is *markedly* simpler; two
arms bought with a lying suffix or a ruling-touching rename is not that.

**The free alternative, offered to the drafter under F9 rather than to the author.**
The concern behind R2 — one claim of totality instead of two — is obtainable with no
type change: `ctxt_g` and `th0` are in scope at both step 1½ (:1478) and the judge path
(:1514) inside one `let` body, so §4.3(a) may declare the unpacking once, with its
unreachability comment, and call it twice.  That is one arm, stated where it can be
justified, and it composes with F9's `concl_is_false`-takes-a-subgoal fix.

### R3 — Rename the constructor `Normal` to `Ordinary`

**DROP.**  The collision is real and inert.  I verified that **nothing in phi-system
opens `Phi_Guard_Cache`, `Phi_Nitpick` or `Phi_Guard_Refute`** — the only `open Phi_*`
of these four structures is `open Phi_Reasoners`, in seven files, none of which opens
the cache — and that `Guard_Decision_Smoke.thy` contains **zero** `open` declarations
and qualifies every constructor (`Phi_Guard_Cache.Normal` at :325-328,
`Phi_Guard_Cache.Proved` at :85-87, `Phi_Reasoners.guard_digest` at :76).  So the
reader hazard the proposal describes — two bare `Normal`s in one file meaning a tier
and a guard kind — cannot occur: in the smoke test neither can be bare, and in
reasoners.ML (`open Thm Term Phi_Reasoners`, :202) only one `Normal` is ever in scope,
since that file qualifies every cache name and never writes the tier constructor.

Decisively, `library/` already carries three unrelated `Normal` constructors —
`Phi_Guard_Cache.Normal` (a tier, guard_cache.ML:19, :66), `Phi_Nitpick.Normal` (a
Nitpick mode, phi_nitpick.ML:35, :117, used *bare* at :119 and :263 in a file this plan
edits) and `KK.Normal` (phi_nitpick.ML:743) — and nobody has ever asked for a note.
Renaming the fourth would discard the author's own word (ruling 11, approved in §9) to
buy nothing observable, and the project's one-term-one-concept rule forbids two words
for one concept, not one word in disjoint namespaces.  The fallback ask — a rule
requiring qualified use — must also be declined: ML already forces it, and writing it
into §1 would convert a compiler-enforced property into a remembered one.

The proposal's secondary claim, that the collision blocks `Phi_Guard_Cache` as the
datatype's home, is answered under F3: that home is excluded by scope
(guard_cache.ML:12), not by a name.  Its citation of "F3" for a new-file argument does
not match this round's F3 or the first review's.

---

## Appendix A — dropped by the curator

- *Two further asymmetries between premise-as-assumption and premise-as-antecedent
  (skolemization; `assumption_exclusively_defines_free`)* — both push toward finding a
  model, the direction the design wants; §4.3(c) describes `preprocess`, not Nitpick's
  internals.  **Correctly dropped**, and F1 has since given the plan the one asymmetry
  that does have a consequence.
- *`guard_digest_of` names a function, not a digest* — naming taste; the factory's own
  callback parameter is `digest_of` (reasoners.ML:1610), and the name is already on
  §9's pending list.  **Correctly dropped.**
- *After R1 the refuter string `guard_simp_tac` names a function that no longer
  refutes; §4.4 should record keeping it* — the decision is visible where it bites, in
  §6's probe expectations and the corpus floor.  **Correctly dropped**, and R2's ruling
  above shows what changing that string would cost.

## Appendix B — self-dropped by the interrogators

Recorded so that they are not re-raised.  I spot-checked several and agree with each
drop.

*`r1-hoist` lens*: §7's fourth bullet narrowing the loss to template-rewritten guards
(same kind and degree); calling what the out-of-run instance decides "an ordinary
guard" (a noun, no behaviour); PLPR.thy:1974's method description going stale (it
restricts itself to guards the simplification does not refute, where the two still
coincide); "the one place where a verdict was the absence of a result is gone" versus
`preprocess`'s `NONE` (a layer below, already in §7); a lower subgoal instantiating a
schematic in an already-tested higher one (no path, and the new shape is the more
faithful); replacing the unreachable `NONE => th0` arm with an `error` (settled by the
first review's correction 3); factoring the two `case kind of … => false` gates into
one predicate (§4.1 deliberately requires both cases at each site); "the simplifier's
refutation by a `False` conclusion" as a second vocabulary (the same words reordered).

*`r-nitpick-shape` lens*: `preprocess` reading only `Thm.cprem_of st 1`
(`asm_full_simp_tac` never splits a goal); `\<And>`-binders in the residue (`prepared`
is binder-free by construction); the axiom depth level shifting from 2 to 1
(`axioms_max_depth = 255`); the hooks deleting every premise (§7's first bullet, and no
path on the live users); `extract_fixed_frees` not substituting into surviving
assumptions (pre-existing, benign direction); "checks will time out" (bounded by
construction; ruling 5 accepts it); keeping the premises as assumptions with
`trust_assms = false` (contradicts the core of ruling 10 and trades a shape for a
flag); the `kind = Normal` equality test (folded into F1 — and raised separately as
F13, where I ruled it).

*`elegance` lens*: the abbreviation's placement after `Proof_Obligation`; writing the
left-hand side as the notation; §4.9's `PhSm_Ag_Base.thy:551` precedent having two
delimiters rather than three (the grammar question is identical); re-raising F11
(delete the dead `quick_cut`); re-raising the digest marker as a term-level encoding
(HASHER exports no digest-combining primitive); deriving `trust_assms` from
`null prems` (would silently flip an ordinary guard whose slice keeps no premise);
the `\<^descr>` using the internal refuter names; the `p_auto_attempt :120` citation
(raised and ruled as F8(a)); `\<premise>`'s two senses in the syntax namespace
(ruling 12, no grammar conflict); `guard_kind_of th0` evaluated twice (same pure
function, same input).

*`verification-consistency` lens*: a dozen off-by-one citations that still land the
reader on the right code (the class the first review self-dropped; I confirm the same
tolerance, and note that F8's three are outside it); §1's `PLPR.thy:185-194` for the
`mode` type synonym at :181; §3's parenthetical calling two live registrations
commented out (the load-bearing count of eight live uses is right); §4.3(a) changing
which subgoals get simplified (raised and ruled as F18); §6's `NO_INST` probe not
spelling its term; stage P missing `jedit/WORD_BOUNDARY_PLAN.md` (an unimplemented
work plan's measurement record, the class §5 already excludes with reason); and the
lens's own clean verification of the whole of stage P, which is why no condition gates
it.
