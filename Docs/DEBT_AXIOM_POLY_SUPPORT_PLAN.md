# Polymorphic Debt Support Plan

Status: rev 5, 2026-09-02 — the implementation revision.  Revs 1-4 each
passed a two-round adversarial review; rev 4's final-assurance round
returned **implement-after-listed-fixes** ("no design question remains
open and no further review round is needed"), and rev 5 applies every
listed fix.  The executed evidence is archived (§8 preamble); no
repository code has been changed yet.  Companion:
`Docs/DEBT_AXIOM_FILTER_PLAN.md` (implemented AFTER this plan, ruling 1).

## 0. Essence

`debt_axiomatization` was meant to support polymorphic axioms — both of
its ends carry machinery that exists only for that case — but the support
is unfinished at both ends, because the module was ported from
`more_thm.ML:add_axiom` onto an oracle-based storage backend without
carrying over one hidden invariant of the replaced backend.  This plan
delivers three fixes and one new predicate:

1. **Declaration fix**: one `Thm.varifyT_global` step restores the type
   half of the varification the oracle backend lost; the copied recovery
   chain then works as designed.
2. **Discharge fix (polymorphism)**: the certificate is internalized by
   `Thm.unconstrainT` and resolved against the ledger entry; every
   residual OFCLASS obligation is closed by a **subgoal-directed step**
   that reads the obligation's type off the subgoal itself — variable,
   composite, or ground alike — and reflects the class-order or arity
   fact through `Thm.of_class`.  A certificate proved at a weaker sort
   than the debt's discharges it; depth one, terminating by
   construction.
3. **Discharge fix (premises)**: the same closing step repairs a third,
   pre-existing defect — a single `ares_tac` application cannot
   discharge any debt whose proposition carries premises, the dominant
   corpus shape.  Approved as a behavior change (ruling 7).
4. **`Debt_Axiom.is_debt`**: matching a proposition against the ledger,
   with BOTH sides normalized the way the Spec_Rules export path
   normalizes (outer `⋀`-parameters generalized to schematic term
   variables, sorts internalized, type frees varified), compared as
   variants via `Pattern.equiv`.

The ledger normal form and the kernel (`kernel.ML`, 30 code lines, 59
physical) stay
untouched.  On the DECLARATION path every step is observationally
equivalent on monomorphic debts, the one delta being a maxidx bookkeeping
bound (§6-1).  On the DISCHARGE path the success set grows and loses
nothing: the head step is production's own `ares_tac` made non-fatal, so
every discharge that succeeds today still succeeds structurally (§6-2).
Execution status is inventoried precisely in §8.0.

## 1. Rulings binding this plan (author, 2026-09-01/02)

Settled; a reviewer who believes relaxing one would buy substantial
simplicity or elegance must mark the point as an explicit **relaxation
proposal addressed to the author**.

1. This project is implemented BEFORE the debt-ledger filter plan.
2. Declaration fix = varify the theorem (`Thm.varifyT_global`), NOT the
   storage: the ledger keeps its current form; `kernel.ML` untouched.
3. Discharge fix = internalize the certificate via `Thm.unconstrainT`,
   then resolution plus a closing step completed for the class order
   through `Thm.of_class` reflection.
4. The closing step is **subgoal-directed** (2026-09-02, after the
   executed shape-space suite): it builds its rule from each residual
   OFCLASS obligation's own type.  This supersedes the earlier
   pre-computed bridge-list design (incomplete on composite types,
   regressive on ground types).
5. `is_debt`'s comparison is insensitive to renaming of type variables
   AND to the export path's outer-`⋀` generalization of term variables
   (2026-09-02; deliberately revises the earlier "term schematics never
   match" semantics).  Precedents: `Thm.equiv_thm` (more_thm.ML:227);
   `Goal.norm_result` for the export shape.
6. `print_debt_axiom` is **unchanged**: it prints the stored form
   verbatim, one form only.  (The rulings' phrase "stored normal form"
   names what this document calls the ledger normal form.)
7. **Disclosure, explicitly approved**: premised debt axioms become
   dischargeable, which they are not today.  The only existing discharge
   site (`example/Debt_Axiom_Doc.thy:121`) is premise-free, so nothing
   in the field changes by that half.
8. The executed test scripts are archived under
   `ai-archive/debt-axiom-poly-support/` in an organized structure
   (README + suite subdirectories) — **done 2026-09-02**, before
   implementation, since the originals lived in a session tmpfs.
9. Standing rules: never run `isabelle build` (`repl_server.sh` is the
   allowed exception); no PRs; commit on the main branch only on the
   author's order.

## 2. Glossary

- **Debt axiom / the ledger / discharge** — axioms created by
  `debt_axiomatization` via an oracle, recorded undischarged in
  `Debt_Axiom.debts : theory -> term Symtab.table`, deleted by
  `discharge_debt_axiom` once certified.  "The ledger normal form" names
  the stored SHAPE; "a ledger entry" names one stored proposition.
- **Sort / type class / OFCLASS premise** — a sort is the set of type
  classes constraining a type variable; `Logic.mk_of_sort` renders a
  sort constraint as one `OFCLASS(T, c)` premise per class.
- **The ledger normal form** — the shape `add_debt_axiom` records: every
  fixed type variable renamed (via `Name.variant_list`'s fresh-name
  generation) and stripped to the empty sort, the stripped constraints
  re-attached as OFCLASS premises:
  `OFCLASS('a'::{}, c1) ⟹ ... ⟹ P['a'::{}]`.  Monomorphic
  propositions: the normal form is the proposition itself.
- **Varify / unvarify** — turning fixed type variables (`TFree`) into
  schematic ones (`TVar`) and back.  An empty sort on a SCHEMATIC
  variable means "no constraint"; on a FIXED variable it means "belongs
  to no class".  This asymmetry is the crux of the declaration defect.
- **Certificate** (short for certification theorem) — the proven theorem
  the user supplies to `discharge_debt_axiom`.
- **`Thm.unconstrainT`** — the official theorem-level internalization:
  sort constraints become OFCLASS premises, type variables become
  empty-sorted schematics, canonically renamed (`thm.ML:2035-2061`).
- **The closing step** — after the head step: each residual subgoal is
  attacked once by `assume_tac`, or by a rule manufactured FROM that
  subgoal — read its OFCLASS obligation `(T, c)`, rebuild `T` with the
  sorts its own OFCLASS hypotheses grant, reflect through
  `Thm.of_class` + `Thm.unconstrainT`, and apply with `Tactic.solve_tac`
  (`ofclass_close_tac`, §5.2).  `Thm.of_class` (thm.ML:2010-2031)
  performs the real `Sign.of_sort` check — class order for variables,
  arities for constructors and ground types — and records a genuine
  `PClass` proof node: signature content reflected into a theorem, no
  trust added.  Depth one; a rule manufactured for subgoal i can only
  apply to subgoal i.
- **The export shape** — what `Spec_Rules` stores for a noted closed
  theorem: `Goal.norm_result` (HHF normalization + `Variable.gen_all`,
  raw_simplifier.ML:1552-1563, + `zero_var_indexes`) turns
  `⋀xs. As ⟹ B` into `As[?xs] ⟹ B[?xs]`; the storage path's export
  morphism additionally varifies the type frees.  Verified end to end
  (§8.2): `⋀n m::nat. n < m ⟹ n ≤ m` is stored as `?n < ?m ⟹ ?n ≤ ?m`.
- **Variants** — two terms that match each other in both directions:
  equal up to renaming of schematic variables.  `Pattern.equiv`
  (more_pattern.ML:24-32) is mutual `Pattern.matches`.  (The only sense
  in which this document uses "variant".)

## 3. Why: the three defects

`add_debt_axiom` is a copy of `more_thm.ML:add_axiom` with the storage
backend swapped from `Theory.add_axiom` to the kernel's oracle
(`kernel.ML:13-15`, oracle function `I`).  The original backend varifies
on storage (`theory.ML:237`, `apsnd Logic.varify_global` — term frees AND
type frees; only the type half is in scope, §5.1).  Everything downstream
was copied verbatim and assumes varified input:

1. **Declaration defect.**  The recovery chain (`Debt_Axiom.ML:61-64`)
   receives the oracle theorem with FIXED empty-sorted type variables;
   `recover`'s keys are schematic, the instantiate step matches nothing,
   and `Thm.unvarify_global` raises on the leftover `TFree`.  Executed
   before-state (§8.1 C1): `THM "Illegal fixed variable: "'a""`.
   Consequence: **no polymorphic debt can be declared at all**.
2. **Discharge defect, polymorphism.**  `discharge_cmd`
   (`Debt_Axiom.ML:115-134`) proves the ledger entry as a goal with
   `ares_tac` over the certificate.  For a polymorphic entry the
   resolution must instantiate the certificate's `?'a::S` to the goal's
   fixed `'a'::{}`, which fails type unification's sort check.  With the
   internalized route, the residual OFCLASS obligations land on types of
   three shapes — a debt variable, a COMPOSITE type over debt variables
   (`'a set`), or a GROUND type (`nat`, when head resolution
   instantiates a polymorphic certificate at a monomorphic debt; that
   case works TODAY and must not regress).  All three are closed by the
   subgoal-directed step; the superseded bridge-list design handled only
   the first (§8.2 suite 3).
3. **Discharge defect, premises (pre-existing).**  Debt propositions are
   `⋀xs. As ⟹ B` in general (`Logic.close_prop`, `Debt_Axiom.ML:82`);
   the corpus is full of premised debts (`Well_Type_disjoint`,
   `Phi_Semantics_Framework.thy:153`).  `Tactic.ares_tac ... 1` is ONE
   application of `assume_tac ORELSE' resolve_tac` (tactic.ML:109), so a
   premised certificate's premises survive as residual subgoals and
   `Goal.prove_internal` raises "Proof failed." — premised debts are
   undischargeable today.  Executed (§8.2 suite 3 G3b).  Approved as a
   deliberate behavior change (ruling 7).

That the machinery was MEANT to be polymorphic is visible in the code:
`stripped_sorts`, the `constraints`/`of_sorts`/`recover` plumbing, and
the recovery chain are all identity on monomorphic input.

## 4. Mechanism facts the design rests on

Verified against Isabelle2025-2 sources; **[executed]** = additionally
confirmed by running code (§8.1/§8.2); unmarked = source-traced.

1. `Thm.varifyT_global` (`thm.ML:2063-2083`) via `Type.varify_global`:
   fresh names against existing TVar names, index 0, same base name when
   no clash (`type.ML:344-361`); the oracle theorem has no TVars, so the
   varified variables exactly match `recover`'s keys.  **[executed]**
   §8.1 C2 recovers the user's sorted proposition exactly.  Limitation
   (source-traced): it protects type frees occurring in hyps; a
   certificate whose hyps carry type frees is then rejected by
   `unconstrainT`, whose hyps check fires first — message "bad hyps"
   (thm.ML:2043); the §5.2 wrapper names debt and certificate.
2. `Thm.unconstrainT` requires no hyps, no flex-flex pairs, no fixed
   type variables; runs `strip_shyps` first; output canonically renamed.
   **[executed]** shape §8.1 A2/B4; idempotence of the preparation
   `Thm.unconstrainT o Thm.varifyT_global` on an already-internalized
   certificate **[executed]** (§8.2 suite 3 P3-3).  The prefix is the
   identity on the schematic theorems `Attrib.eval_thms` returns for
   global facts (`discharge_cmd` is a `Toplevel.theory` command).
3. Acceptance is the kernel's, not the tactic's: `Goal.prove_internal`
   proves the stated goal, and `Debt_Axiom_Kernel.discharge` re-checks
   literal equality (`eq_list (op =)`, `kernel.ML:25`) and oracle
   independence (`kernel.ML:22`).  **[executed]** at the harness level
   as `aconv` of the proved proposition against the goal term (§8.2);
   the stricter `op =` is exercised by the real command in §8.4.
4. All debt creators go through `add_debt_axiom_global`: the command and
   `resource_space_more.ML:122`.  `instantiate_type`/`specify_type` use
   `Theory.add_axiom` directly and are untouched — their axioms carry
   schematic term variables, one reason `is_debt` must be total on such
   input (§5.3).
5. **The export shape** (glossary) is what the filter's consumer path
   reads: `all_nondefs_of` maps `Thm.prop_of` over Spec_Rules-Unknown
   facts (nitpick_hol.ML:1353-1358).  **[executed]**: real
   `Spec_Rules.add` round trips (§8.2 suite 4) confirm outer-`⋀`
   generalization, type-free varification, premise-order preservation.
   Consequence: the filter plan's premise that a monomorphic debt's
   Spec_Rules proposition equals its ledger entry literally is FALSE
   today — §7 corrects it there.
6. Sort-stripping's rationale (ruling 2): a sort constraint is an
   implicit precondition tracked as a sort hypothesis; an axiom must not
   carry hidden premises whose force grows with later `instance`
   declarations, so the official convention stores axioms with
   constraints made explicit.

## 5. Design

### 5.1 Declaration fix — the changed lines

The recovery chain gains one line (`Thm.varifyT_global`), and one entry
check lands immediately after the existing `Sign.no_vars` (which already
rejects schematic type AND term variables, `sign.ML:346-356`).  Both
appear in context in §5.3's merged `add_debt_axiom`, which is the
finished function; the load-bearing comment reads:

> restores the TYPE half of the varification Theory.add_axiom performs
> on storage (theory.ML:237) and the oracle backend skips; the chain
> below is the verbatim more_thm.ML:add_axiom recovery and assumes
> schematic input.  The term half (Free -> Var) stays out of scope: both
> creators close term variables (Logic.close_prop); the entry check
> above rejects the rest loudly.  Identity on monomorphic axioms.

The entry check's error text is exactly
`"add_debt_axiom: free term variables in " ^ Syntax.string_of_term ctxt prop`
— message quality, not a new guarantee: a free term variable is the one
input class the module cannot process; unreachable from both real
creators (each closes its propositions), so the message names the ML
entry point, not the command.

### 5.2 Discharge fix (`Debt_Axiom.ML`, `discharge_cmd`)

Current code: `goal (K (Tactic.ares_tac ctxt (Attrib.eval_thms ctxt [C]) 1))`
over positionally-aligned lists.  New, printed once in final form
(REVISED 2026-09-02 with the author-approved implementation-review fixes:
the closing tactic lifted to a top-level private function (R3), the
duplicate-name rejection (m8) with the unreachable `Fail "unex"` arm
deleted, the position-aware certificate description (M4), the caught
exceptions' own messages instead of `Runtime.exn_message` (R2), and the
style items of m7):

```sml
(*the subgoal-directed closing step: read the residual OFCLASS
  obligation off the subgoal, rebuild its type with the sorts the
  subgoal's own OFCLASS hypotheses grant, and reflect the
  class-order/arity fact through Thm.of_class -- the real
  Sign.of_sort check, a genuine PClass proof, no trust added --
  internalized by the same unconstrainT the goal and the certificate
  went through.  Works uniformly for obligations on debt variables,
  composite types, and ground types; a rule manufactured for subgoal
  i can only apply to subgoal i; depth one, no recursion.  The
  handles wrap rule CONSTRUCTION only (reflection declined: not an
  OFCLASS subgoal, or Sign.of_sort refuses) -- the subgoal is then
  left open for the caller to display; interrupts are not among the
  caught constructors and always propagate.*)
fun ofclass_close_tac ctxt = SUBGOAL (fn (sg, i) =>
  let
    val thy = Proof_Context.theory_of ctxt
    val concl = Logic.strip_assums_concl sg
    val hyps = Logic.strip_assums_hyp sg
    val cs = map_filter (try Logic.dest_of_class) hyps
    fun sort_of a = map snd (filter (fn (T, _) => T = TFree (a, [])) cs)
    val (T, c) = Logic.dest_of_class concl
    val T' = T |> Term.map_atyps
          (fn TFree (a, []) => TVar ((a, 0), sort_of a) | A => A)
    val rule = Thm.unconstrainT (Thm.of_class (Thm.global_ctyp_of thy T', c))
  in Tactic.solve_tac ctxt [rule] i end
  handle TERM _ => no_tac | THM _ => no_tac | TYPE _ => no_tac)

fun discharge_cmd ax_certs thy =
  let
    val ax_names = map (Global_Theory.check_fact thy o fst) ax_certs
    val _ =
      (case duplicates (op =) ax_names of
        [] => ()
      | N :: _ => error (quote N ^ " is named twice in one discharge"))
    val ctxt = Proof_Context.init_global thy

    (*total where Facts.string_of_ref alone is not (it raises Fail on
      literal facts, facts.ML:112); an attributes-only certificate has no
      name of its own, so the fallback names the debt-name position --
      when the front end renders positions at all; the attribute list is
      deliberately not printed*)
    fun string_of_certificate _ (Facts.Fact s, _) = "literal fact " ^ quote s
      | string_of_certificate pos (r, _) =
          (case Facts.string_of_ref r of
            "" =>
              (case Position.here pos of
                "" => "the given certificate"
              | s => "the certificate given at" ^ s)
          | s => s)
    fun err_discharge N pos C msg =
      error ("discharge_debt_axiom: discharging " ^ quote N ^ " by " ^
             string_of_certificate pos C ^ " failed:\n" ^ msg)

    val debts_due =
      ax_names ~~ ax_certs |> map (fn (N, ((_, pos), C)) =>
        (case Symtab.lookup (Debt_Axiom_Kernel.debts thy) N of
          SOME ax => (N, pos, C, Thm.global_cterm_of thy ax)
        | NONE => error (N ^ " is not an undischarged debt axiom")))

    val certs = debts_due |> map (fn (N, pos, C, goal_ct) =>
      (let
         val rules = map (Thm.unconstrainT o Thm.varifyT_global)
                         (Attrib.eval_thms ctxt [C])
           (*unconstrainT mirrors the ledger normal form up to
             type-variable renaming; varifyT_global first makes its
             no-fixed-type-variables precondition hold unconditionally
             (identity on global facts)*)
       in
         Goal.prove_internal ctxt [] goal_ct
           (K (HEADGOAL (TRY o Tactic.ares_tac ctxt rules)
               THEN ALLGOALS (TRY o (Tactic.assume_tac ctxt
                      ORELSE' ofclass_close_tac ctxt))))
       end
       (*ERROR/THM/TYPE only -- a catch-all would swallow interrupts unless
         it re-raised them explicitly; the caught messages are already
         user-facing (e.g. goal.ML's "Proof failed." display)*)
       handle ERROR msg => err_discharge N pos C msg
            | THM (msg, _, _) => err_discharge N pos C msg
            | TYPE (msg, _, _) => err_discharge N pos C msg))
  in Debt_Axiom_Kernel.discharge (ax_names ~~ certs) thy
  handle Fail "dep" =>
         error "Some of the given certification theorems are based on axiomized debts!"
       | Fail "cert" =>
         error "Some of the given certification theorems fails to match the debt!"
  end
```

Design notes:

- **The head step is production's own `ares_tac`, made non-fatal.**
  `TRY` cannot block the first result, and the closing tail only closes
  FURTHER subgoals — so every discharge production performs today is
  still performed, structurally rather than empirically (measured by the
  rev-4 judge on eight cases including a tautological premised entry
  that plain `resolve_tac` would lose).  A non-resolving certificate
  reaches `Goal.prove_internal`'s finish check and the residue is
  DISPLAYED ("Proof failed." + goal) instead of the opaque
  `error "Tactic failed"`.
- **The closing step is the third fix** (§3-3): the certificate's
  genuine premises are met by the debt's own premises via `assume_tac`,
  the OFCLASS obligations by hypotheses or one reflected rule.
- **Completeness and termination by construction**: the rule is built
  from the very obligation it closes — no pre-computed list to be
  incomplete, no recursion to diverge.  Executed evidence §8.2 suite 3.
- **Failures are named, totally**: the guard wraps the per-certificate
  work (rule preparation and proof) but NOT the ledger lookup — a
  lookup error is not a discharge failure and keeps its own message.
  No `try`/`map_filter` over the rules: silently dropping a broken
  certificate would turn a diagnosable kernel error opaque.

### 5.3 `ledger_form`, `match_form`, `is_debt`, and the merged `add_debt_axiom`

One normalization source, three consumers — the recorded shape, the
recorder, and the matcher cannot drift apart.  REVISED 2026-09-02 with the
author-approved review adoption R5: `stripped_sorts` (only caller:
`ledger_form`) loses its eager sort-recovery computation, and `recover`
becomes a closure like `of_sorts` — the matching path then performs no
certification and `is_debt`'s totality holds unconditionally:

```sml
(*Copied and modified from more_thm.ML:add_axiom; the sort-recovery
  substitution is built lazily in ledger_form, so the matching path stays
  total.*)
fun stripped_sorts t =
  let
    val tfrees = build_rev (Term.add_tfrees t);
    val tfrees' = map (fn a => (a, [])) (Name.variant_list [] (map #1 tfrees));
    val strip = map (apply2 TFree) (tfrees ~~ tfrees');
    val t' = Term.map_types (Term.map_atyps (perhaps (AList.lookup (op =) strip))) t;
  in (tfrees, tfrees', strip, t') end;

(*devarify type schematics injectively (index folded into the name);
  identity on the declaration path, where Sign.no_vars has excluded
  schematics.  No Isabelle surface syntax can write a dot into a
  type-variable name, so the dotted name cannot collide with a real
  TFree; only an ML-constructed term could.*)
fun devarifyT t = t |> Term.map_types (Term.map_atyps
      (fn TVar ((a, i), S) => TFree (a ^ "." ^ string_of_int i, S) | A => A))

(*the ledger normal form of a proposition (the recorded shape), plus what
  the recorder needs to rebuild the user-facing theorem.  recover and
  of_sorts are closures: only the declaration path consumes them, and the
  matching path, which discards them, must not pay for them -- nor, for
  recover, risk the TYPE exception its certification can raise.*)
fun ledger_form thy prop =
  let
    val prop = devarifyT prop
    val (tfrees, tfrees', strip, prop') = stripped_sorts prop
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip
  in {recover = fn () =>
        map2 (fn (a', S') => fn (a, S) =>
          (((a', 0), S'), Thm.global_ctyp_of thy (TVar ((a, 0), S)))) tfrees' tfrees,
      of_sorts = fn ctxt =>
        maps (fn (T as TFree (_, S), _) => Thm.of_sort (Thm.ctyp_of ctxt T, S)) strip,
      prop = Logic.list_implies (maps Logic.mk_of_sort constraints, prop')}
  end

(*term-level mirror of Variable.gen_all (variable.ML:510): outer
  !!-parameters, as Drule.outer_params delivers them (names already made
  distinct), become schematic Vars at one fresh index*)
fun gen_all_term t =
  let
    val idx = Term.maxidx_of_term t + 1
    val vars = map (fn (a, T) => Var ((a, idx), T)) (Drule.outer_params t)
  in Term.subst_bounds (rev vars, Term.strip_all_body t) end

(*what both sides of the comparison are reduced to: the ledger normal form,
  HHF-normalized, outer !!-params generalized -- mirroring what the
  export did to the consumer's copy -- and type frees varified*)
fun match_form thy prop =
  #prop (ledger_form thy prop)
  |> Drule.norm_hhf thy
  |> gen_all_term
  |> Logic.varify_types_global

fun is_debt thy t =
  let val u = match_form thy t
  in Symtab.exists (fn (_, ax) => Pattern.equiv thy (u, match_form thy ax))
       (Debt_Axiom_Kernel.debts thy)
  end
```

The merged `add_debt_axiom` (the finished function; §5.1's comment
inlined; record field bound apart from the parameter):

```sml
fun add_debt_axiom ctxt (b, prop) thy =
  let
    val _ = Sign.no_vars ctxt prop;
    val _ = null (Term.add_frees prop [])
      orelse error ("add_debt_axiom: free term variables in " ^
                    Syntax.string_of_term ctxt prop);
    val form = ledger_form thy prop;
    val axm_name = Sign.full_name thy b;
    val (axm', thy') =
      Debt_Axiom_Kernel.axiomize (axm_name, Thm.global_cterm_of thy (#prop form)) thy;
    val thm =
      axm'
      |> Thm.varifyT_global
         (*restores the TYPE half of the varification Theory.add_axiom
           performs on storage (theory.ML:237) and the oracle backend
           skips; the chain below is the verbatim more_thm.ML:add_axiom
           recovery and assumes schematic input.  The term half
           (Free -> Var) stays out of scope: both creators close term
           variables (Logic.close_prop); the entry check above rejects
           the rest loudly.  Identity on monomorphic axioms.*)
      |> Thm.instantiate (TVars.make (#recover form ()), Vars.empty)
      |> Thm.unvarify_global thy'
      |> fold Thm.elim_implies (#of_sorts form ctxt);
  in ((axm_name, thm), thy') end;
```

Signature addition:

```sml
val is_debt : theory -> term (*a proposition*) -> bool
  (*does the proposition match an UNDISCHARGED debt axiom?  Both sides
    are compared in the ledger normal form with outer !!-parameters
    generalized -- so a debt is recognized both as declared and as the
    Spec_Rules export path stores it -- up to renaming of schematic
    variables (Pattern.equiv, as in Thm.equiv_thm).  An INSTANCE of a
    debt is not the debt and does not match.  Total: never raises on
    schematic input.  Discharged debts no longer match.*)
```

Notes:
- **Executed evidence** (§8.2 suite 4): all positives via REAL
  `Spec_Rules.add` round trips; every negative false without
  exceptions, including instance-vs-variant, same-statement-
  different-sort, `specify_type`'s meta-equality shape, permuted
  premises (real export preserves premise order), post-discharge; mass
  sweeps clean.  One measured unreachable boundary (H8b) in §9.
- **Cost**: per query, one `match_form` plus |ledger| × (`match_form` +
  `Pattern.equiv`) on small terms; the `recover` field is computed and
  dropped by `is_debt` — the price of single-sourcing; ledger-side
  forms are cacheable if a profile ever demands it.
- `ledger_form`/`match_form`/`gen_all_term`/`devarifyT` stay private.

### 5.4 Documentation

- `example/Debt_Axiom_Doc.thy` gains a polymorphic section: declare a
  debt with a nontrivial sort and two type variables, use it at two
  instance types, discharge it with a certificate at a weaker sort, and
  record `print_debt_axiom` output.  Three prose points the section must
  carry: the printed form is the ledger normal form, the exact text the
  kernel compares at discharge (ruling 6); an empty-sorted type variable
  PRINTS indistinguishably from `'a::type` under the default printer —
  the recorded transcript is the DEFAULT printer's output, with a
  `show_sorts` rendering shown beside it as an explicitly labelled
  second display; and the certificate of a `discharge_debt_axiom` must
  be a named global fact — a literal fact can never resolve there.
  Also correct the example's stale "30 lines" kernel claim to 58.
  [CORRECTED 2026-09-02, review finding kernel-line-count: 58 was itself
  wrong — measured, kernel.ML is 59 physical lines, 48 excluding blanks,
  and exactly 30 excluding blanks AND comments, so the original "30 lines
  of code" was right.  Shipped: the example keeps "30 lines of code only";
  Debt_Axiom.thy states the same 30 under the explicit metric "excluding
  blanks and comments".]
- `Debt_Axiom.ML` header: two sentences naming the port defect fixed
  (type half only) and the input contract (closed propositions).  The
  implementation must produce every comment shown in the §5.2/§5.3
  blocks, including the interrupt note above the handler.

### 5.5 What is explicitly NOT changed

`kernel.ML` (30 code lines, 59 physical); the ledger normal form as stored;
`print_debt_axiom` (its entry form; the review-adopted R4 makes only the
header line agree in number);
`Spec_Rules` registration; `instantiate_type`/`specify_type`/
`unspecified_type`; the command syntax; everything in the
guard-race/filter territory.  No new configuration options or commands.

## 6. Correctness arguments

1. **Monomorphic observational equivalence of the DECLARATION path.**
   Every added declaration-path step is proposition-level identity on
   monomorphic input.  The one non-propositional delta (§8.1 C3):
   maxidx -1 → 0 plus a no-op varifyT derivation node — unobservable
   because the proposition has no schematic variables for that bound to
   describe.  §8.3-1's dump diff makes this falsifiable field by field.
2. **The DISCHARGE path grows its success set and loses nothing, by
   construction.**  The head step IS production's `ares_tac`; `TRY`
   cannot block its first result; the closing tail only closes further
   subgoals.  Hence every discharge production performs today is still
   performed — a structural claim, spot-checked by the rev-4 judge on
   eight cases (including a tautological premised entry where a
   resolve-only head demonstrably loses).  What is added: premised
   debts (ruling 7) and polymorphic debts.
3. **Soundness of the declaration fix**: `Thm.varifyT_global` is
   kernel-derived generalization on a hyps-free theorem; the chain
   after it is unmodified official code on its intended shape (§8.1 C2).
4. **Discharge produces the ledger entry by construction**: acceptance
   is the kernel's literal comparison and oracle-dependency check,
   untouched; the closing step's reflected rules are `PClass` facts of
   the signature.  Proved-proposition exactness executed throughout
   §8.2.
5. **`is_debt` exactness**: shape agreement single-sourced; renaming of
   type variables and outer-`⋀` generalization absorbed by construction
   (ruling 5); instances rejected by the mutual-match requirement.  The
   residual failure mode is a consumer transforming propositions beyond
   the export shape — the filter plan's census tripwire alarms on it;
   the one known transformer (`all_nondefs_of`'s `subst_atomic` of
   fixed-free equations) cannot touch a debt (debt propositions carry
   no term Frees).

## 7. Interplay with the debt-ledger filter plan

When THIS plan lands, `DEBT_AXIOM_FILTER_PLAN.md` receives a dated
annotation and corrections: its §5.1 `is_debt` (bare `aconv`) is
superseded — delivered here, export-shape-aware and total; its premise
that a monomorphic debt's Spec_Rules proposition equals the ledger entry
literally is FALSE (the export generalizes outer `⋀`-parameters; §4-5) —
load-bearing for that plan, since bare `aconv` would have filtered
almost nothing; its §8.1-1 round-trip clause is struck by name (`is_debt`
no longer relies on type-variable name preservation; the census survives
as the shape-divergence tripwire) and its §9 risk row 2 is struck
likewise; its §4 census item gains its cause (the declaration crash) and
stops being a standing property; its kernel line count is corrected to 30
code lines (59 physical); its
checklist item 1 reduces to "already delivered"; its risk table gains
the `subst_atomic` note (§6-5).  The filter plan's own pending review
fixes remain a separate work item.  Nitpick synergy: `is_debt` filters a
polymorphic debt BEFORE the monomorphic/polymorphic partition, so
`no_poly_user_axioms` stays true.

## 8. Verification

Environment for all executed suites: stock HOL heap of
`contrib/Isabelle2025-2`, via `isabelle ML_process -l HOL` (`HOLogic`
not in scope at the raw toplevel; `stripped_sorts` compiles unchanged;
ASCII-only string literals).  **Archived (done 2026-09-02)** under
`ai-archive/debt-axiom-poly-support/`, copied from the authoring
session's scratchpad before implementation; the README gives one line
per file (what it asserts, how to re-run it).  Run forms: suite 1
`-f testX.ML` (self-contained); suites 2-3 `-f common.ML -f <group>.ML`;
suite 4 `-f <group>.ML` (self-contained; the session's split
harness/fragments are not duplicated).

### 8.0 Execution status of the plan's code, precisely

Executed character-for-character: `ofclass_close_tac`'s body with
`resolve_tac ... THEN_ALL_NEW assume_tac ...` — which tactic.ML:111
defines `Tactic.solve_tac` to be, so the evidence carries over to the
named form verbatim — and the closing tail (suite 3); `devarifyT`,
`match_form`'s pipeline with the session's `gen_all_term`, and
`is_debt`'s comparison (suite 4; the `Debt_Axiom_Kernel.debts` form is
its trivial instantiation); the declaration recovery chain with
`Thm.varifyT_global` (suite 1 C2).  Executed-equivalent: the printed
`gen_all_term` is the library-reuse form (`Drule.outer_params` +
`Term.strip_all_body`), measured equal to the executed form on 1945
Spec_Rules propositions and 24875 global-fact propositions
(enumerated via `Global_Theory.all_thms_of thy false`; script and
output archived at
`ai-archive/debt-axiom-poly-support/reuse-equivalence/`) with zero
disagreements — the two
differ only on an eta-contracted outer `Pure.all`, a shape no ledger
entry can carry and no fact in Main exhibits.  NOT executed (glue;
§8.3-0 exercises it first): the head combinator
(`TRY o Tactic.ares_tac` — suite 3 ran plain `resolve_tac` at the head),
`string_of_certificate`/`err_discharge`, the `debts_due` restructuring,
the entry check, `ledger_form`'s factoring, the merged `add_debt_axiom`
body.
[2026-09-02: all of these are now executed — through the real commands
and asserted message texts on the final post-review code; see
`ai-archive/debt-axiom-poly-support/real-command-transcripts/`
(the per-theory `.out.txt` captures and `AFTER_RESULTS.md`).]

### 8.1 Suite 1 — feasibility (rev 1)

A1-A3 (`of_class` across a subclass gap; `unconstrainT` shape; clean
THM failure on an underivable pair), B1-B8 (weaker-sort discharge via a
manually built bridge; negative and subset controls), C1-C3
(declaration chain: before-crash `Illegal fixed variable`, exact
recovery after the fix, mono identity with maxidx -1→0), D1-D3
(`Pattern.equiv` accepts renaming, rejects sort change and diagonal
collapse).  All PASS.

### 8.2 Suites 3 and 4 — the final design (suite 2 = superseded bridge design, archived for its divergence record)

Suite 3 (`suite3-closer/`, 26 side-by-side executions, each also run
under production `ares_tac`): G1a-d bare-variable cases incl.
two-variable and two-step class chain; G2a-c composite over variables
(`set`, `option`, `prod` with different hypothesis sorts); G3a-c ground
incl. the production-works regression guards (mono debt × polymorphic
library certificate; mono × mono) and premised×ground; G4 composite
over ground (`nat set`, also production-provable — no regression); G5
mixed `'a × nat`; N-a/b/c clean negatives; P3-1..7 adversarial hunt
(function types, multi-class recovery, idempotent preparation,
duplicate obligations, repeated variable, uninstantiated certificate
TVar, two different composites); E1-E4 extensions (`list`, nested
`option option`, premised×polymorphic, sort `{type}` itself).  Result:
22 positives proved with exact propositions; 4 negatives — N-a/b/c and
P3-6, a certificate whose sort obligation is not witnessable from its
statement (§9 row 1) — fail instantly with the residue displayed;
production proves exactly 3 (all monomorphic premise-free), all 3 also
proved by the new recipe; no timeout fired; result theorems carry clean
sort hypotheses.

Suite 4 (`suite4-is_debt/`): positives M1-M8 via REAL `Spec_Rules.add`
round trips (mono/poly × premised/premise-free, two-variable, ground,
declared and exported shapes, ledger entries as queries); negatives
N1-N8 (different sort, library facts, instance-vs-variant both
directions reported, diagonals both ways, `specify_type` meta-equality,
definitional equations, permuted premises with an order-preservation
control, post-discharge); hunt H1-H10 (nested `⋀` inside a premise,
shadowed parameter names, explicit `{}` sort, six-premise chain,
multi-class sort, object-`∀` with higher-order Var, mixed
partially-normalized input, dotted-name boundary); mass sweeps (Main's
15 Spec_Rules-Unknown props — the consumer's literal input space — 1945
spec-rule props, 6000 global facts): zero spurious matches, zero
exceptions.  H8b boundary in §9.

### 8.3 Regression at implementation: the declaration path

0. **Before anything else, on the UNPATCHED local worktree** (the
   archive copy of ruling 8 is already done): restart the REPL and
   record two before-transcripts through the real command — a premised
   monomorphic debt discharged via `discharge_debt_axiom` (expect
   "Proof failed.") and a monomorphic debt discharged by a polymorphic
   library certificate (expect success).  §8.3-4 compares against these
   recorded transcripts.
   Then, after the patch (§10 items 1-2), the glue checks: a failing
   discharge must produce the named error for all THREE certificate
   shapes — named fact, literal fact (`discharge_debt_axiom d : ‹...›`),
   and attributes-only — asserting the final message TEXT, not merely
   the absence of an internal `Fail`; the entry check must reject a
   free-term-variable proposition fed via ML with exactly
   `add_debt_axiom: free term variables in ...`, and one line confirms
   neither `debt_axiomatization` nor `resource_space_more.ML:122` can
   reach it; the head step must turn a non-resolving certificate into
   "Proof failed." with the goal displayed, and a debt whose conclusion
   is one of its own premises must still discharge (the `ares_tac` head
   at work).
1. **Ledger dump artifact**, one harness, both captures importing the
   SAME named theory set — `PhiEx_All` (the corpus context §8.3-2's
   full-chain run loads; earlier revisions misnamed it `PhiTest_All`,
   corrected 2026-09-02 at implementation), on the `Phi_System_Base`
   REPL heap, on cslh19.  Dump script (archived alongside the dumps): per LEDGER
   ENTRY (a term) — proposition with sorts, `Term.maxidx_of_term`;
   acceptance = byte-identical proposition AND unchanged maxidx.  Per
   DEBT FACT (a theorem) — proposition with sorts, `Thm.maxidx_of`,
   tags, shyps, hyps count; acceptance = all equal except
   maxidx' = `Int.max (0, maxidx)`.  Sequence: capture
   `ledger_dump.pre.txt` on the unpatched worktree; transport the patch
   by rsync of the phi-system worktree (the established convention);
   RESTART the REPL (an edited .ML is only picked up by a fresh REPL —
   do not reorder); capture `ledger_dump.post.txt`; diff.  If the two
   captures differ in heap, imported theory set, or worktree state
   beyond the patch, the diff is VOID and must be retaken.
   IMPLEMENTATION NOTE (2026-09-02): executed and PASSED with zero
   observable deviation — every debt-fact field including maxidx came
   back unchanged; the formula's allowed flip `Int.max (0, maxidx)`
   never reached the store.  Root cause (source trace): every noted fact
   passes through `Goal.norm_result` (generic_target.ML:363), which ends
   in `Drule.zero_var_indexes` (goal.ML:93-97), which ends in
   `Thm.adjust_maxidx_thm ~1` (drule.ML:206-220) — the cached bound is
   recomputed exactly, so §8.1 C3's chain-level flip (maxidx 0 on the
   theorem the recovery chain returns) never reaches the stored fact.
   `real-command-transcripts/MaxidxProbe.thy` exhibits the two endpoints
   (chain 0, noted -1); the trace above, not the probe, is the
   verification.  Verdict and method:
   `ai-archive/debt-axiom-poly-support/ledger_dump.diff`.
2. Full-chain corpus run on the cslh19 harness — mechanism and
   acceptance string as in `DEBT_AXIOM_FILTER_PLAN.md` §8.2
   (`hard_restart.sh` + `run_probe.py`; `ERRORS RETURNED: None`, real
   ELAPSED; monitor cadence ≤ 10 min).
   IMPLEMENTATION NOTE (2026-09-02): executed TWICE on the final
   post-review code, same day, same harness — clean tree (production):
   `ERRORS RETURNED: None`, `ELAPSED 900.3 s`
   (`ai-archive/debt-axiom-poly-support/corpus_run_baseline.out.txt`);
   patched tree: `ERRORS RETURNED: None`, `ELAPSED 885.3 s`
   (`corpus_run_patched.out.txt`).  The same-day baseline is the elapsed
   reference; an interim pre-review run (`ERRORS RETURNED: None`,
   `ELAPSED 833.9 s`, `corpus_run_interim.out.txt`) is kept for the
   record.  The corpus contains no `discharge_debt_axiom` command, so
   this run and §8.3-1's dump diff are declaration-path evidence only;
   the discharge path is evidenced by `real-command-transcripts/`.
3. Scratch monomorphic tests through the real commands: declare +
   discharge an unconditional debt; `is_debt` true → false on
   discharge.
4. The two §8.3-0 before-transcripts, re-run after the patch: the
   premised monomorphic discharge now succeeds (ruling 7's test); the
   mono × polymorphic-library-certificate discharge still succeeds.

### 8.4 The new capability at implementation (real commands)

1. Declare polymorphic debts (nontrivial sort; the two-variable
   different-sorts one); returned theorem = user-stated sorted form;
   ledger holds the normal form; `print_debt_axiom` output recorded in
   the example per §5.4's three prose points.
2. Use a polymorphic debt at two instance types.
3. Discharge at a strictly weaker certificate sort; and a
   composite-type obligation case (suite 3's G2a in situ).
4. NEGATIVE: certificate sort strictly exceeds the debt's — named
   error, residual obligation displayed.
5. NEGATIVE: a certificate derived FROM a debt is rejected by the
   kernel's oracle-dependency check (also exercises `op =` acceptance
   on the real command path).
6. `is_debt` units in situ, reading the query via
   `Spec_Rules.get`/`all_nondefs_of` — never via the theorem
   `debt_axiomatization` returns: matches the exported proposition of a
   mono premised debt AND a poly debt; rejects that debt's `nat`
   instance; returns false without raising on `add.commute` and on a
   `specify_type` bijection axiom; false after discharge.
7. The declaration crash retirement: §8.1 C1's input now succeeds.

### 8.5 Acceptance

All of §8.3 and §8.4 pass; §8.3-1's dump diff and §8.3-2's corpus run
show no unexplained deviation; any failure blocks the merge until
root-caused.

## 9. Risks

| Risk | Assessment | Mitigation |
| --- | --- | --- |
| A certificate carries a sort hypothesis not witnessable from its statement | `strip_shyps` keeps it; `unconstrainT` makes it an OFCLASS premise on a variable absent from the conclusion; closed soundly by a matching goal premise, else left as displayed residue (suite 3 P3-6 is exactly this case) | Wrapper names debt and certificate; kernel checks untouched |
| A certificate's hyps carry type frees | `varifyT_global` protects them; `unconstrainT` rejects — "bad hyps" (thm.ML:2043) — loud, never silent | Named by the wrapper; unreachable from stored global facts |
| A proposition with free TERM variables reaches `add_debt_axiom` | The one unprocessable input class; unreachable from both real creators | §5.1 entry check; §8.3-0 exercises it |
| The monomorphic declaration delta is larger than claimed | Only the maxidx bound and a no-op derivation node; every deviation that could matter raises loudly | §8.3-1 dump diff + §8.3-2 corpus run |
| The closing step misses a closable obligation or diverges | The rule is built FROM the obligation; depth one.  Executed over the obligation-shape space incl. an 11-construction adversarial hunt; the superseded bridge design's divergence is archived as suite 2 | §8.4-3/4 re-pin the boundary in situ |
| `devarifyT`'s dotted-name injectivity | Defeated only by an ML-constructed TFree literally named `'a.0` (suite 4 H8b); no surface syntax can write such a name, exported facts carry no TFrees | Recorded here; hardening path if ever needed: `Name.variant` against the term's tfree names |
| A consumer transforms propositions beyond the export shape | Known transformer `subst_atomic` cannot touch a debt (no term Frees in debt propositions) | Filter plan's census tripwire; noted in its risk table (§7) |
| A discharge campaign changes Nitpick behavior | Filter-plan territory | Its risk table |

## 10. Implementation checklist (in order)

0. DONE 2026-09-02: evidence archive assembled at
   `ai-archive/debt-axiom-poly-support/` (four suites + README; from
   the session scratchpad).  Remaining in this slot, before any edit:
   the two §8.3-0 before-transcripts on the unpatched local worktree.
1. `Debt_Axiom.ML`: `devarifyT`, `ledger_form`, `gen_all_term`,
   `match_form`, `is_debt` (+ signature), merged `add_debt_axiom`
   (§5.3, §5.1).
2. `Debt_Axiom.ML`: `discharge_cmd` — `ofclass_close_tac`,
   `string_of_certificate`/`err_discharge`, `debts_due`, the guarded
   per-certificate proof (§5.2).
3. Local REPL restart; §8.3-0 glue checks; §8.3-3/4 and §8.4 scratch
   runs.
4. `example/Debt_Axiom_Doc.thy`: polymorphic section + stale-fact
   corrections (§5.4), loaded through the REPL.
5. cslh19, one harness, theory set `PhiEx_All`: §8.3-1 pre-dump →
   rsync patch → REPL restart → post-dump → diff; then §8.3-2
   full-chain run (monitored ≤ 10 min).
6. Archive finalization: drop in the two ledger dumps and the dump
   script; README final pass.
7. Dated annotation + corrections in `DEBT_AXIOM_FILTER_PLAN.md` (§7).
8. Report results to the author; on acceptance, commit (phi-system,
   then the outer-repo gitlink bump), push origin only.
