# Judge's report — the re-review of the Quicksort regression fix (2026-09-15)

**Verdict: MET_ON_CONDITION.** Nine conditions, all of which the drafter can apply
alone. Nothing needs the author. Three findings are rejected outright, and seven
further claims inside otherwise-upheld findings are rejected as overreach.

The ruling the first review escalated (MD1, now ruling 8) is implemented exactly as
the author ruled it, and so are the two proposals the author approved (P1 → ruling 9,
P2 → ruling 10). The twelve documentation conditions D1–D12 are applied, with two
unfinished tails. What is not ready is, again, the record: six live statements in the
plan still teach the pre-change rule, one glossary anchor points at the wrong
reasoner, and the revision's own verification block describes a run that predates the
code it sits beside.

---

## Method

I re-verified every decisive claim against the working tree, the Isabelle 2025-2
sources, the three patches and plan rev 28. I ran no Isabelle process, started no
session, and changed nothing. Where a defender and an interrogator disagreed on a
fact, I read the file rather than either summary.

---

## 1. Acceptance criteria

### (a) Rulings 1–7 still implemented exactly — **MET**

Nothing the conditions round did disturbed them. `p_auto_tac`
(`/home/qiyuan/Current/MLML/contrib/phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML:1088-1092`)
has no opening simplification; `guard_simp_tac` runs on `ctxt_g` (:1478) and again on
`ctxt_g'` (:1514) and its output feeds R-conv (:1548), R-nitpick (:1549), both
warnings (:1563-1569) and `n_goals` (:1578); the factory (:1610-1628) contains no
simplification and knows nothing of entries or deltas; `is_F`, `is_false`,
`is_guard_mode`, `p_auto_body` and `p_auto_search_tac` have no survivors anywhere in
the tree; the obligation instance runs `Clasimp.fast_force_tac` with no pass
(`PLPR.thy:1982-1988`); the bound is `Time.fromSeconds 60` (:1077).

### (b) Ruling 8 (MD1) implemented as ruled — **MET**

Step 6 re-simplifies the state the call was given: `val th' = case Seq.pull
(guard_simp_tac ctxt_g' th0)` at :1514, with `th0` the parameter of `prove_or_refute`
(:1433). The judge is still handed step 1½'s state: `consult` passes `thm = th`
(:1499), where `th` is `decide`'s parameter, bound from `simplified` at :1556. Both
halves are recorded where they belong — §5 step 6 (plan:1129-1140) states the rule and
its reason verbatim, and adds "the judge itself was handed step 1½'s state"; §39
ruling 8 (plan:3627-3633) repeats both. The third inheritance is named in the code
where the other two are: the `apply_delta` comment (reasoners.ML:1442-1446) now ends
"and both simplify th0, the state the call was given, never each other's result."

The new `error` the ruling creates — "The judge is broken: its lemmas rewrite the
guard to False." (:1516) — is probed (Guard_Decision_Smoke.thy:680-688), which is what
condition D10 asked for.

### (c) Ruling 9 (P1) implemented — **MET**

`p_auto_attempt ctxt = guard_simp_tac ctxt THEN cpu_bounded_tac
(guard_classic_prover_bound ctxt) (p_auto_tac ctxt)` (:1097-1098), exported at :123,
run by `p_auto_solving` (:1639) and by the method (`PLPR.thy:1973`). The two sites can
no longer drift. The composition is behaviour-preserving: the old
`try_prove_or_give_up (SOME bound) …` wrapper differed only by a `solved_states` /
`Seq.take 1` pair that `p_auto_tac` already performs internally, which the first
review examined and rejected as pre-existing (out-of-run/F8).

### (d) Ruling 10 (P2) implemented — **MET**

Every write, warning and record path matches plan §5 step 1½ and §1's
loud-guard-warning entry. `refuted_by name` (:1471-1473) writes `{delta, Refuted}`
through `keep` (:1464 → :1439-1440) and returns a `Refuted` outcome with `refuter =
SOME name`; step 1½'s `NONE` reaches it as `refuted_by simp_refuter` (:1555) with
`simp_refuter = "guard_simp_tac"` (:1389); `goals` is the simplified state's premises,
or `th0`'s on the refutation (:1479), exactly as §39's code plan says; the loud
warning takes the overturning party (`loud_guard_warning ctxt who goals`, :1382-1386),
with the judge's line byte-for-byte unchanged and the simplifier's the only new text;
the decision record carries the new refuter name (:1577). Steps 2–6 sit in a local
`decide th` and the outcome is chosen once, at :1553-1556.

I checked the one soundness question this ruling turns on, because it is what makes
the difference between a verdict and a bug: **can `guard_simp_tac` return the empty
sequence for any reason other than `quick_cut` finding `False`?** `ALLGOALS` is a
`THEN` chain (`Pure/tactical.ML:236-240`), so it fails if `asm_full_simp_tac` fails on
any subgoal — and a simplifier that changes nothing does fail. On the factory's path
that cannot happen: the guard-side context is built with `addsimps @{thms'
Premise_def}` (:1615), `Premise mode x ≡ x` (`PLPR.thy:199-200`) is an unconditional
rewrite, and every subgoal at that point is a guard with a `Premise`-headed
conclusion, so the simplifier always changes each one. The empty sequence therefore
has exactly one cause, and ruling 10's reading of it is correct.

The two new probes are correct. The step-1½ probe (Guard_Decision_Smoke.thy:674-678)
replays `⋀n. BADN n = False` at step 1, so the delta carries one lemma; step 1½
rewrites the conclusion to `False`; `refuted_by simp_refuter` writes that same delta
back with `Refuted` — which is why `("refuted", "proved", "guard_simp_tac", "-")` and
"Refuted with 1 lemma(s)" are both right. The judge-error probe (:680-688) reaches
`judge_or_give_up` only because P-auto genuinely runs and fails on the rule-free
atom, and its expected prefix matches the `error` text. The three `assert_*` helpers
(:205-213) now pin all three warning lines on every probe that uses them, and neither
loud line is a prefix of the other, so they cannot cross-count.

### (e) D1–D12 applied faithfully — **MET with two unfinished tails**

I checked each: §7's five sentences (plan:1197-1201, :1217-1219, :1252-1254,
:1261-1269) are corrected, the two inversions included; §1's "the goal state" entry
(:162-172) now says no simplification has acted; the three `reasoners.ML` comments
(:88-89, :104, :112-117) and the `guard_simp_tac` body comment (:1062-1073) name the
two solving functions that simplify and the obligation instance that does not; the
method description string is rewritten; §39 ruling 1's terminology sentence carries
its correction note (:3564-3567); the `is_F` justification lists the visible
differences (:237-247); §5 step 1½'s "nothing written" is now a correct historical
clause, since at HEAD the factory's pass ended such a call before `prove_or_refute`
ran at all; `ai-artifacts/Guard_False_Probe.thy` calls `p_auto_tac` with a dated note
(:10-13, :54); ruling 6's `fast_force_tac` sentence is fixed. The tails are D5
(condition **C2**) and D12 (condition **C3**).

### (f) The plan and the code agree — **NOT MET**

Conditions C1–C4 and C6. The pattern is the same one the first review found and is
narrower than it was: each stale sentence now has its correct twin nearby, so no
reader can reconstruct the removed pipeline — but §1 is the authoritative glossary,
and it currently contradicts §3, §39 and the code about four separate objects.

### (g) No behaviour change beyond the rulings — **MET**

I looked for one and found none. `refuted_by` was moved above `simplified` (pure code
motion, four callers unchanged); `p_auto` gained an explicit state parameter, matched
at both call sites; the four arms of the old outcome `case` are inside `decide`
verbatim; `loud_guard_warning`'s judge text is unchanged; the step-1½ exit still
returns `Seq.empty`. The one production-visible difference is ruling 10's own: a store
write, a trace line, an `ML_debugger` record and, on a `Proved` entry only, one loud
warning.

### (h) The verification record — **NOT MET**

Condition **C7**. This is the weightiest of the nine, because in this project the plan
is the contract and §39's verification block is the permanent record. The block was
written by the conditions patch itself, yet says "every probe unchanged" in the
revision that adds two probes, and closes "Next: the standard two-turn review" three
paragraphs below its own account of that review's completion. The context document's
reason for skipping the `Quicksort.thy` re-run — "confined to the judge path" — is
false of P2, whose step 1½ runs on every call with no judge in sight.

What is actually at risk is narrow, and I state it so the drafter can restate it
accurately: the exit's `result` is `Seq.empty` before and after, so no guard's
provability and no downstream reasoning can change; what is new is a store write into
`Quicksort.proof-store`, which is the very artifact the verification's "222 live
records, no tombstone" counts. File mtimes corroborate both sides:
`Guard_Decision_Smoke.proof-store` (15:27:51) postdates the last edits to the theory
(15:26:20) and to `reasoners.ML` (15:26:07), so the final smoke theory was evaluated;
`Quicksort.proof-store` (14:06:59) predates them, so that run is indeed the old one.

### (i) Elegance — **MET**

The shape improved under the conditions. `refuted_by` is one function serving four
refutation endings; `simp_refuter` is one named constant used both to write the field
(:1555) and to test it for the warning (:1566), so the warning cannot drift from the
writer; `loud_guard_warning ctxt who goals` parameterises instead of duplicating;
`p_auto_attempt` is the one definition two callers share, which is precisely the
"shape that makes an invariant impossible to violate" this project asks for. The local
`decide` keeps one call = one decision = one store write inside the `Timing.start ()`
bracket.

---

## 2. Conditions

Nine, all documentation or comments, all hand edits (never scripted — plan documents
in particular). Full statements and fixes are in the structured
`drafter_may_decide` list.

| # | Where | What |
|---|---|---|
| C1 | plan:316-319, :333-337 | §1 still defines the out-of-run instance as `guard_simp_tac` + `try_prove_or_give_up`, which P1 replaced; `try_prove_or_give_up`'s only remaining caller is `PLPR.thy:1984` |
| C2 | plan:224-225, :3029 | D5's residue — the false "three / every solving function" universal, in two wordings |
| C3 | plan:320-322 | D12 applied in §39 only; §1 still says `fastforce` "clarifies" |
| C4 | plan:471-474, :1103-1109 | Ruling 10 not carried into §1's P-auto entry or §5 step 4 (optionally also `PLPR.thy:1974`) |
| C5 | reasoners.ML:195 | The record's `refuter` enumeration omits the value P2 added |
| C6 | plan:147-148, :1056-1058, five dead anchors | D6 substituted the `\<safe>` reasoner for a guard reasoner; the §5 step 1 anchors miss their functions |
| C7 | plan:3711-3723, context doc :109-112 | The verification record describes a pre-P1/P2 run and gives a reason that is false of P2 |
| C8 | Guard_Decision_Smoke.thy:14-18 | Nitpick — the reworded header universal now has one deliberate exception |
| C9 | Guard_Decision_Smoke.thy:671-673 | Nitpick — "no refuter" above an assertion that the refuter is `guard_simp_tac` |

C6(a) deserves one note of fairness: the wrong pair `PLPR.thy:2008-2009`, `:2011-2012`
was prescribed verbatim by the first review's own rejected-repairs paragraph, so the
drafter applied D6 exactly as instructed. The error originates upstream, in the first
review. The correct pair is named by the code's own comment at `PLPR.thy:2003-2004`:
`:2005-2006` and `:2008-2009`.

---

## 3. Rejected

Three findings do not survive at all, and seven claims inside otherwise-upheld
findings are rejected as overreach; one-line rebuttals are in the structured
`rejected` list. The recurring shapes:

- **A wish for a finer message on an unreachable path** — md1-p2-code/F4. A step-6
  `guard_simp_tac` timeout does hand P-auto `th0` and end in the "judge is broken"
  error, but the looping simplifier is named loudly one line earlier, the attribution
  is right in the only case where the proposed fallback would differ, and the fallback
  itself contradicts binding ruling 8.
- **Findings refuted by reading the sentence they attack** — tests-and-comments/F4
  (the elided object of "no search is needed" is the lemma, fixed by the very next
  clause) and tests-and-comments/F6 ("step 1 and step 6" is the established name for
  the two `apply_delta` branches, and the sentence names `th0` explicitly).
- **Inflated severity** — every "major" filing. None touches code behaviour, and in
  each case the correct statement stands in the same bullet, in §3, or in §39.
- **Evidence that does not hold up** — "nothing records that P2's probe was ever
  evaluated" (the context document records the run and the store mtime confirms it);
  "two step-1½ refutation probes" (there is one; the other reaches P-auto and is
  closed at step 6); "no guard is an equation is broken" (it is not — the rewriting
  comes from the injected delta, not from any atom's declared rules).

---

## 4. Bottom line

The ML is right, the author's three new rulings are implemented as ruled, the two new
probes test what they claim, and nothing in the conditions round changed behaviour
beyond ruling 10. The gap is the same class as last time and roughly a third the size:
six sentences of a 3700-line contract still say what was true this morning, one
glossary anchor points one registration too far, and the revision's own verification
paragraph outran the code it describes. Apply C1–C9, correct the record honestly about
what has and has not been re-evaluated, and re-submit.