# The Debt-Ledger Filter Plan (`genuine_modulo_debt`)

Status: **CLOSED — project abandoned by author decision, 2026-09-02.**
No code was ever changed under this plan, and none will be: the ledger
filter in `phi_nitpick.ML`, the `user_axioms = "smart"` pin, and the
`genuine_modulo_debt` labeling are not going to be implemented; R-nitpick
keeps `user_axioms = "false"` and its current comments.  What this plan
called for in `Debt_Axiom.ML` was delivered separately and survives:
`Debt_Axiom.is_debt` (by the Polymorphic Debt Support project, phi-system
commit `2fa67ba6`).  The document is kept for the record; its pending
review-fix list is void.
Original status: draft rev 1, 2026-09-01, author approval pending.
Predecessor context: `Docs/GUARD_NITPICK_FALSIFY_PLAN.md` (the
guard-race redesign, closed 2026-09-01 at phi-system commit `bcdffbe4`).

> **2026-09-02 annotation — the Polymorphic Debt Support project landed**
> (`Docs/DEBT_AXIOM_POLY_SUPPORT_PLAN.md`, executed per its §10; see its §7
> for this list's rationale).  Corrections to this document, marked in place
> below with the same date:
> - §5.1's `is_debt` (bare `aconv`) is SUPERSEDED — `Debt_Axiom.is_debt` is
>   already delivered, export-shape-aware and total; checklist item 1 reduces
>   to "already delivered".
> - The premise that a monomorphic debt's `Spec_Rules` proposition equals the
>   ledger entry literally is FALSE: the export generalizes outer
>   `\<And>`-parameters into schematic variables (a premised or
>   variable-binding mono debt exports as `?n < ?m ==> ?n <= ?m`, not as the
>   ledger's `!!n m. ...`).  Bare `aconv` would have filtered almost nothing.
> - §8.1-1's round-trip clause is struck (the delivered `is_debt` does not
>   rely on type-variable name preservation); the census survives as the
>   shape-divergence tripwire.  §9 risk row 2 is struck likewise.
> - §4-4's zero-polymorphic-debts census has its cause: polymorphic
>   declaration CRASHED before the fix — it is a consequence of the old
>   defect, not a standing property, and polymorphic debts may appear any
>   time now.  (`is_debt` filters them before the mono/poly partition, so
>   `no_poly_user_axioms` stays true.)
> - The kernel line count: 59 physical lines, 48 excluding blanks, exactly
>   30 excluding blanks and comments — so "30 lines" was right as a code
>   count all along (an interim 2026-09-02 annotation here said "58"; that
>   was the `wc -l` newline count, one short of the 59 physical lines
>   because kernel.ML has no trailing newline; corrected).
> - Risk table: the residual `is_debt` failure mode is a consumer
>   transforming propositions beyond the export shape; the census tripwire
>   alarms on it.  The one known transformer (`all_nondefs_of`'s
>   `subst_atomic` of fixed-free equations) cannot touch a debt — debt
>   propositions carry no term Frees.
> This plan's own review-fix list remains pending the author's ruling.
> [Later the same day: the author closed the project — see the Status line;
> the review-fix list is void.]

## 0. Essence

Replace R-nitpick's blanket exclusion of user axioms (`user_axioms = false`)
with a precise one: exclude exactly the undischarged debt axioms recorded in
the `Debt_Axiom.debts` ledger, and let Nitpick's own relevance machinery
handle everything else (`user_axioms = smart`).  A countermodel then
witnesses falsity in the theory *minus its unpaid debts* — a guarantee we
name `genuine_modulo_debt` — instead of falsity in a theory with *all* user
axioms waived, which is what the code claims today and which is untrue in
rich contexts.

## 1. Rulings binding this plan (author, 2026-09-01)

These are settled.  A reviewer who believes relaxing one of them would make
the design substantially simpler or more elegant must mark the point as an
explicit **relaxation proposal addressed to the author** — never treat a
ruling as negotiable inside the plan itself.

1. `user_axioms` moves from `"false"` to `"smart"` (approved).
2. Debt axioms are excluded **uniformly** — the filter does not vary per
   guard (approved; the alternative "let relevant debts into debt-relevant
   guards' problems" was presented and not chosen).
3. **No per-guard debt-relevance judgment exists anywhere.**  The
   author rejected every possible consumer of such a flag: racer spawning
   gates, early-finish admission gates, verdict downgrading, warning
   layering, and pure recording.  The flag, its computation (dependency
   closure vs. ledger vocabulary), and its storage are all out of scope.
4. No probe token changes, no `verdict` datatype changes, no new
   configuration options.  `genuine_modulo_debt` is a canonical *name* used
   in comments and documents, not a runtime value.
5. Standing rules: never run `isabelle build` (REPL restart is the reload
   mechanism); commit on the main branch only; A/B replay on the cslh19
   harness before the change is called done.

## 2. Glossary

- **Debt axiom** — an axiom introduced by the `debt_axiomatization` command
  (`Debt_Axiom/Debt_Axiom.ML`).  Created via an oracle, recorded in a
  ledger, intended to be proved ("discharged") later.
- **The ledger** — `Debt_Axiom.debts : theory -> term Symtab.table`, mapping
  each *undischarged* debt's full name to its recorded proposition.
  Discharging deletes the entry.  (Distinct from the guard race's
  `refuted_by` ledger in `reasoners.ML`; this plan never touches that one.)
- **The debt-ledger filter** — the new patch: dropping every proposition
  that matches a ledger entry from the nondefinitional axiom list Nitpick
  collects.  "The filter" below always means this.
- **Nondefinitional axioms (nondefs)** — what Nitpick treats as user
  axioms: all `Spec_Rules` entries classified `Unknown`, minus built-in
  theories (`all_nondefs_of`, `nitpick_hol.ML:1353`).
  `debt_axiomatization` registers its axioms exactly there
  (`Debt_Axiom.ML:103`), which is why the filter has a single choke point.
- **Relevance pull** — Nitpick's per-constant axiom inclusion: walking the
  goal's constants, it pulls nondefs that mention an undefined constant
  from `nondef_table` (`nitpick_preproc.ML:976-978`, the
  `user_axioms <> SOME false` branch).  Active under `smart`, dead under
  `false`.
- **Blanket add** — under `user_axioms = true` only: *all* monomorphic
  nondefs are added regardless of relevance
  (`nitpick_preproc.ML:1035`).  Never active in this design.
- **Certification flags** — `got_all_mono_user_axioms` and
  `no_poly_user_axioms` (`nitpick_preproc.ML:1038-1040`): existence checks
  that decide whether Nitpick's own message says "genuine" or "quasi
  genuine".  They do not consult relevance.
- **Strict rail / tolerant rail** — the two encodings of the trust patch in
  `phi_nitpick.ML:519-533`: the negated conclusion must come out *definitely
  false* in the model (strict); every other nondefinitional formula —
  guard premises, machine-generated typedef/class axioms, and any pulled
  user axiom — only must *not come out definitely false* (tolerant).
- **`genuine_modulo_debt`** — the canonical name of the guarantee an
  R-nitpick refutation carries after this plan: the countermodel lives in
  the theory minus its undischarged debts (with the rail caveat, §6).

## 3. Why: the honesty gap

Today's justification comment (`reasoners.ML`, the verdict-map note) says:
"what is waived are phi-system's ten monomorphic user axioms, all derivable
from HOL's own, so a model ignoring them models a theory no stronger than
HOL's."  That was measured true in the §18.3 replay context of the
predecessor plan.  It is *false* in real corpus contexts: the raced test
theories import `Phi_Semantics/*`, which contribute dozens more debt axioms
(memory model, aggregate types, pointers), none derivable.  Under
`user_axioms = false` all of them are waived silently.

The fix is not to include them (measured routes to that are slow or
explosive — predecessor plan §18.3-3/8) but to *say precisely what is
waived* and make that statement structurally true in every context: the
waived set is exactly the undischarged debt ledger.  That is a set with a
name, an owner, and a shrinking lifecycle (discharge deletes entries, and
the filter then automatically stops excluding them).

Bonus honesty: the current setup also silently waives any future *ordinary*
`axiomatization` a downstream theory might add.  Under `smart` + the
filter, such an axiom would enter the problem via the relevance pull
instead of being waived.

## 4. Mechanism facts the design rests on (all verified in source)

1. Debt axioms reach Nitpick **only** through `Spec_Rules`-`Unknown` →
   `all_nondefs_of` → the `nondefs` list, computed once per invocation in
   `phi_nitpick.ML:296`, from which both `nondef_table` (relevance, line
   298) and `mono_nondefs`/certification flags (in `nitpick_preproc.ML`)
   derive.  Filtering that one list removes a debt from every road into
   the problem.  (Class axioms pulled per sort by `add_axioms_for_sort`
   are *class definition* axioms, not `Spec_Rules` entries; they are
   unaffected, same as today.)
2. `"smart"` is a legal pinned value — it is Nitpick's factory default for
   `user_axioms` (`nitpick_commands.ML:48`), parsed to `NONE`.
3. In the predecessor plan's replay context the mono user axioms were
   exactly ten and every one is a `debt_axiomatization` axiom (verified
   against sources: `Well_Type_disjoint`, `Well_Type_poison`,
   `zero_well_typ`, `can_eqcmp_sym`, `RES.sort`, `RES.ex_RES_not_1`,
   `FIC.sort`, three `sVAL_emb` axioms).  Hence, post-filter, the corpus
   problem construction is expected *byte-identical* to today's: the
   relevance pull finds an empty table where debts used to be, no blanket
   add, no scope growth.  A/B replay (§8) is the check.
4. The repository currently has **zero** polymorphic debt axioms and zero
   polymorphic user axioms (predecessor plan §18.3-1 census after the
   `unspec_prod` conversion; re-grepped 2026-09-01).
   **[2026-09-02: this was a CONSEQUENCE of the declaration crash the
   poly-support project fixed, not a standing property — polymorphic debts
   may appear any time now.  The delivered `is_debt` filters them before
   the mono/poly partition, so `no_poly_user_axioms` stays true.]**
5. `specify_type` (also in `Debt_Axiom.ML`) registers bijection axioms in
   `Spec_Rules`-`Unknown` *without* entering the ledger.  It has zero uses
   in the repository.  If ever used, its axioms count as ordinary user
   axioms (not filtered) — that is the correct treatment, since they are
   definitional in spirit but not debts; recorded here so nobody mistakes
   it for an oversight.
6. Nitpick's own result code stays `quasi_genuineN` either way: the trust
   patch conjoins `not trust_assms` into `genuine_means_genuine`
   (`phi_nitpick.ML:665-668`), so certification-flag improvements from the
   filter change no observable code.  The verdict map
   (`guard_refute.ML:280`) already accepts `genuineN` and
   `quasi_genuineN`; it does not change.

## 5. Design

### 5.1 `Debt_Axiom.is_debt` (new export, `Debt_Axiom/Debt_Axiom.ML`)

> **2026-09-02:** SUPERSEDED — `Debt_Axiom.is_debt` is already delivered by
> the poly-support project (export-shape-aware `match_form` + `Pattern.equiv`;
> see `DEBT_AXIOM_POLY_SUPPORT_PLAN.md` §5.3).  The design below is kept for
> the record; do not implement it.

The ledger stores each debt in the ledger normal form produced at axiomatization
time by `stripped_sorts` (sorts stripped off type frees and re-attached as
explicit of-sort premises, `Debt_Axiom.ML:37-46,57`).  The membership test
reproduces the ledger normal form for a candidate proposition and compares with
`aconv`:

```sml
(*the ledger normal form of a proposition: sorts stripped and re-attached
  as explicit of-sort premises -- the shape axiomize records.  Type
  variables are read as frees first, so a proposition that comes back
  varified (e.g. out of Spec_Rules) still matches its ledger entry.*)
fun ledger_form thy prop =
  let
    val prop = prop |> Term.map_types
          (Term.map_atyps (fn TVar ((a, _), S) => TFree (a, S) | T => T))
    val (strip, recover, prop') = stripped_sorts thy prop
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip
  in (strip, recover, constraints,
      Logic.list_implies (maps Logic.mk_of_sort constraints, prop'))
  end

fun is_debt thy t =
  Symtab.exists (fn (_, ax) => ax aconv #4 (ledger_form thy t))
                (Debt_Axiom_Kernel.debts thy)
```

`add_debt_axiom` is refactored to build its axiom term through the same
`ledger_form` helper (it already computes `strip`/`recover`/`constraints`;
the helper returns them), so the ledger normal form exists in exactly one place —
matching and recording cannot drift apart.

Signature addition:

```sml
val is_debt : theory -> term (*a proposition*) -> bool
  (*does the proposition match an UNDISCHARGED debt axiom?  Discharged
    debts no longer match: they are theorems and may re-enter any
    axiom collection that wants them.*)
```

Correctness notes:
- **Monomorphic debts** (all current ones): `stripped_sorts` is the
  identity (no type frees), so the test degenerates to a literal `aconv`
  against the ledger — the `Spec_Rules` proposition and the ledger entry
  are the same term.
  **[2026-09-02: FALSE — the export generalizes outer `\<And>`-parameters
  into schematic variables, so most mono entries would NOT have matched;
  measured in the poly-support project (its §4-5, suite 4).]**
- **Polymorphic debts** (none today): a `Spec_Rules` proposition comes
  back with schematic type variables; the `TVar -> TFree` step restores
  the fixed shape and `stripped_sorts` then renames deterministically
  (`Name.variant_list` over the traversal order of the same term
  structure), reproducing the recorded form.  This leans on Isabelle
  preserving type-variable base names through varification, which it
  does; §8.1 adds a runtime check so a silent mismatch cannot survive
  unnoticed.
- The `subst` that `all_nondefs_of` applies (fixed-free defining
  equations of the goal) cannot touch a debt: debt propositions are
  closed and free-variable-less.
- Cost: per Nitpick invocation, |nondefs| × |ledger| `aconv` comparisons
  on small terms (both counts are tens); noise next to a Kodkod call.
- No kernel change: `kernel.ML` stays its 30 lines **[2026-09-02: correct
  as a code count — 30 lines excluding blanks and comments; 59 physical]**;
  `is_debt` reads the ledger through the existing
  `Debt_Axiom_Kernel.debts`.

### 5.2 The filter patch (`phi_nitpick.ML`, second PHI-PATCH)

At the single collection point (`phi_nitpick.ML:296`, before
`nondef_table` and everything downstream is derived):

```sml
    val nondefs = all_nondefs_of ctxt subst
          (*PHI-PATCH 2, the debt-ledger filter: drop every undischarged
            debt_axiomatization axiom before the relevance table and the
            certification flags are computed.  A countermodel is then a
            model of the theory minus its undischarged debts
            (genuine_modulo_debt).  This one site covers both roads a user
            axiom takes into a problem: nondef_table (the per-constant
            relevance pull) and mono_nondefs (the user_axioms = true
            blanket add).*)
          |> filter_out (Debt_Axiom.is_debt thy)
```

The file-header COPY NOTICE gains one paragraph naming the second patch
(same style as the first: the patch in one sentence, plus the rebase note
that this is one marked block of three lines).

### 5.3 The dependency (`PLPR` ROOT + imports)

`phi_nitpick.ML` is loaded by `Phi_Logic_Programming_Reasoner/PLPR.thy`,
which today does not import `Debt_Axiom`.  Change:

- `Phi_Logic_Programming_Reasoner/ROOT`: add `"Debt_Axiom"` to `sessions`.
- `PLPR.thy`: add `Debt_Axiom.Debt_Axiom` to `imports`.

Justification: the dependency is semantically real — the refuter's
soundness statement now references the ledger.  `Debt_Axiom` imports only
`Pure` (three small files); no cycle (nothing in `Debt_Axiom` references
PLPR); downstream (`Phi_Semantics_Framework`) already imports it, so the
full system's import closure is unchanged.  Side effect: the
`debt_axiomatization`/`discharge_debt_axiom`/... outer-syntax keywords
become available from PLPR onward instead of from
`Phi_Semantics_Framework` onward — additive only.  Heap note: phi-system
theories load from source under the `Phi_System_Base` REPL setup, so the
change takes effect on REPL restart, no build.

### 5.4 The pinned value (`reasoners.ML`)

In `pinned_nitpick_params`: `("user_axioms", "false")` becomes
`("user_axioms", "smart")`.  The pin itself stays — the §2.3 ruling of the
predecessor plan (pin every string-settable key whose pollution could
change a verdict) is unaffected; only the pinned value changes.

### 5.5 Comment rewrites (exact drafts; review for truth, not style)

(a) `reasoners.ML`, in the `pinned_nitpick_params` block comment, the
`card and user_axioms` paragraph is replaced by:

> card carries a measured choice, not a default (plan §18.3, 84 replayed
> undecided guards).  user_axioms = smart restores Nitpick's default
> per-constant relevance pull; what that pull can reach is already
> debt-free — the debt-ledger filter (phi_nitpick.ML, PHI-PATCH 2) removes
> every undischarged Debt_Axiom entry from the collected axioms before the
> relevance table and the certification flags are computed.  In every
> measured corpus context all user axioms ARE debts, so the problem Kodkod
> sees is unchanged from the former user_axioms = false; what changed is
> the guarantee's name: a countermodel is genuine_modulo_debt — a model of
> the theory minus its undischarged debts — not a model of a theory with
> all user axioms waived.  A future ordinary axiomatization in scope would
> now enter the problem by relevance instead of being silently waived.
> card = 1-6 is an INTERVAL on purpose: ...(unchanged tail)...

(b) `reasoners.ML`, verdict-map comment: the `quasi_genuine counts as a
refutation` paragraph's justification clauses (a)-(c) are replaced by:

> quasi_genuine counts as a refutation (author rulings 2026-08-26 and
> 2026-09-01, plan §18.2 and Docs/DEBT_AXIOM_FILTER_PLAN.md).  It has to:
> the trust patch alone makes genuine unreachable (genuine_means_genuine
> conjoins "not trust_assms", phi_nitpick.ML), so the two codes together
> are the only refutation this racer can ever report.  What the code does
> NOT tell apart: (a) what is waived is exactly the undischarged
> Debt_Axiom ledger (the debt-ledger filter, phi_nitpick.ML) — the
> countermodel is genuine_modulo_debt, and a guard whose truth leans on
> debt-constrained vocabulary can still be "refuted" by a model that
> violates a debt; (b) a wrong refutation costs COMPLETENESS only — a
> guard judged false leaves one reasoning rule unapplied, the undecided
> exit already assumes the guard fails, and it cannot cancel a P-auto
> that was about to succeed; (c) quasi_genuine also covers downgrades
> from wf / finitize / total_consts / bisim_depth — over the replayed
> corpus only the axiom check ever fired, a property of that corpus, not
> a guarantee.

(c) `guard_refute.ML:210-211`:

> genuine and quasi_genuine both count, as in reasoners.ML's verdict map
> and for its reason: under the trust patch nothing is ever certified
> genuine.  What a countermodel waives is exactly the undischarged debt
> ledger (genuine_modulo_debt — the debt-ledger filter, phi_nitpick.ML).

(d) `GUARD_NITPICK_FALSIFY_PLAN.md` §18.2 gets a dated annotation (hand
edit, Chinese, matching that document's language) stating that the
`user_axioms = false` ruling is superseded by this plan: value now
`smart` + the debt-ledger filter, verdict named `genuine_modulo_debt`,
pointer to this file.

### 5.6 What is explicitly NOT changed

The `verdict` datatype and every probe token; the race protocol,
early-finish rule, and `refuted_by` ledger; the verdict map's accepted
codes; all warnings and diagnostics; `pinned_nitpick_params`' other pins;
`Debt_Axiom`'s kernel; Nitpick distribution files (the only vendored copy
remains `phi_nitpick.ML`).  No new configuration options.

## 6. The guarantee, stated honestly (goes into comments/docs as above)

A `genuine_modulo_debt` refutation means: Kodkod found a finite model in
which the negated guard conclusion is definitely true, every collected
definitional axiom holds, and every *other* nondefinitional formula
(guard premises, typedef/class axioms, relevance-pulled ordinary user
axioms) is not definitely false — in the theory **minus its undischarged
debt axioms**.  Two standing caveats, both accepted by ruling:

1. **Conservativity caveat.**  The countermodel shows the guard is not a
   theorem of theory-minus-debts.  If a debt axiom were false (or
   non-conservative over the guard's vocabulary), the full theory could
   still prove the guard.  The guarantee therefore presumes what the debt
   mechanism itself presumes: debts are true in the intended model and
   will be discharged.
2. **Rail caveat.**  Premises and pulled axioms ride the tolerant rail
   ("not definitely false"), not the strict one; this is the trust
   patch's deliberate design and is why `genuine` is unreachable.

## 7. Expected behavior delta

In current corpus contexts: **none** — the filter removes exactly the set
`user_axioms = false` used to waive, `smart`'s relevance pull finds
nothing new to pull, and Nitpick's phase structure is unchanged.
Refutation sets, latencies, and verdict distributions should replay
within established noise.  Any measured delta means an unmodeled axiom
source exists and must be explained before merging (§8.1's census is the
early warning).

## 8. Verification protocol

### 8.1 Static/REPL checks (before any full run; local REPL restart)

1. **Census**: in a representative corpus context (a `Phi_Test` theory's
   final context), enumerate `Spec_Rules`-`Unknown` entries minus
   built-ins; assert every one matches the ledger via `is_debt` (i.e.
   ordinary-user-axiom count = 0, matching §4.3) and that the number of
   matched entries equals the number of in-scope undischarged debts.
   This doubles as the runtime check for `ledger_form`'s round-trip
   (§5.1): any debt present in `Spec_Rules` but unmatched fails the
   census loudly.
   **[2026-09-02: the round-trip clause is struck — the delivered
   `is_debt` does not rely on type-variable name preservation.  The
   census stays, as the shape-divergence tripwire: a consumer
   transforming propositions beyond the export shape fails it loudly.]**
2. **Unit sanity** of `is_debt`: each ledger proposition → true; a
   definitional equation and an arbitrary theorem → false; after a
   `discharge_debt_axiom` in a scratch theory, the discharged
   proposition → false.
3. **Pin sanity**: `pinned_nitpick_params` with `"smart"` parses and
   yields `user_axioms = NONE` in the resulting params record.

### 8.2 A/B replay (cslh19 harness, the decisive check)

- Baseline: the four archived 2026-09-01 full-chain runs (commit
  `bcdffbe4`; data in
  `ai-archive/cslh19-guard-race-archives-2026-09-01.tar.zst`).
- New: two full-chain runs at the new configuration, same harness
  (`hard_restart.sh`; acceptance = `ERRORS RETURNED: None` + real
  ELAPSED; monitor cadence ≤ 10 min).
- Comparison discipline (fixed-denominator, per-key verdict multisets —
  the predecessor project's method): zero PROVED-flips required;
  refutation set identical up to the two known noise classes
  (proved-gate flicker: Binary_Trees:447/456/457; marginal
  refuted↔undecided jitter: Dynamic_Array:73/76,
  Dynamic_Array_arbi_len:100/102/108, Quicksort:39); race wall within
  the established ~900-920 s band; `nitpick_probe` per-leg
  outcome/latency distributions statistically indistinguishable.
- Any refutation flip outside the known noise classes blocks the merge
  until root-caused.

### 8.3 Rollback

Single-commit revert; or minimally: pin back `"false"` and delete the
three filter lines.  No data migration, no config surface.

## 9. Risks

| Risk | Assessment | Mitigation |
| --- | --- | --- |
| A corpus context contains a non-debt `Spec_Rules`-`Unknown` entry nobody counted | Would make `smart` pull it → problem changes → possible refutation delta | §8.1 census runs first and names the entry; author decides (include is the honest default) |
| Polymorphic debt added later; `ledger_form` round-trip fails on it | No occurrence today; failure mode is *under*-filtering (debt stays in, verdicts can only get more conservative — sound, but the label overclaims precision) | §8.1-1 census pattern is rerunnable; comment at `ledger_form` states the reliance |
| **[2026-09-02: row above struck with the round-trip clause.]** Residual `is_debt` failure mode: a consumer transforms propositions beyond the export shape | The one known transformer (`all_nondefs_of`'s `subst_atomic` of fixed-free equations) cannot touch a debt — debt propositions carry no term Frees | §8.1-1 census tripwire alarms on any such divergence |
| The PLPR→Debt_Axiom import surprises a downstream user of PLPR alone | Keywords appear earlier; no semantic change | Noted in commit message |
| Rebase burden growth on `phi_nitpick.ML` | +3 marked lines, one header paragraph | The COPY NOTICE already prescribes diff-and-reapply |

## 10. Implementation checklist (after author approval, in order)

1. `Debt_Axiom.ML`: `ledger_form` refactor + `is_debt` export (+ sig).
   **[2026-09-02: already delivered by the poly-support project.]**
2. `Phi_Logic_Programming_Reasoner/ROOT` + `PLPR.thy`: dependency.
3. `phi_nitpick.ML`: PHI-PATCH 2 + header paragraph.
4. `reasoners.ML`: pinned value + comment rewrites (a)(b).
5. `guard_refute.ML`: comment rewrite (c).
6. Local REPL restart; §8.1 checks.
7. Predecessor-plan annotation (d) by hand.
8. Push worktree state to cslh19; REPL restart there; §8.2 A/B (two runs,
   monitored ≤ 10 min cadence).
9. Report results to the author; on acceptance, commit (phi-system, then
   the outer-repo gitlink bump), push origin only.
