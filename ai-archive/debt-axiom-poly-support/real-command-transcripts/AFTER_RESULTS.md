# Real-command results on the FINAL post-review code (plan 8.3-0, 8.3-3/4, 8.4)

- Date: 2026-09-02.  Prover: Isabelle2025-2, session heap `HOL`, headless PIDE
  (Isabelle-MCP), `Debt_Axiom.Debt_Axiom` loaded from the patched worktree
  source AFTER the implementation review's approved fixes landed (M4, m7, m8,
  R2-R5, and the re-review touch-ups K2/K3; final Debt_Axiom.ML md5
  d1e1d605...; see the plan's dated 2026-09-02 revision notes in sections
  5.2/5.3).
- Theory sources: this directory.  Raw per-command outputs: the `.out.txt`
  file beside each theory.  The pre-patch record is `TRANSCRIPTS.md`
  (Before_T1/T2 at phi-system commit bcdffbe4, Debt_Axiom/ clean).

## Section 8.3-4 — the two before-transcripts re-run after the patch

- `Before_T1.thy` (premised monomorphic debt x monomorphic certificate): the
  discharge that failed with "Proof failed." before the patch SUCCEEDS;
  theory CLEAN; final ledger empty.  (Ruling 7's test.)
- `Before_T2.thy` (unconditional monomorphic debt x polymorphic library
  certificate `add.commute`): still succeeds; theory CLEAN.

## Section 8.3-0 glue checks — `Glue.thy`

Message texts are now ASSERTED, not just transcribed: the ML block re-drives
`discharge_cmd` for each certificate shape and errors on any mismatch
(`String.isSubstring` over markup-stripped messages).  All assertions PASS;
the exact captured strings are in `Glue.out.txt`.  Highlights:

- named fact (non-resolving): `... by conj_commute failed:` + `Proof failed.`
  + the goal — and NO `exception THM` wrapper line (R2 verified by a negative
  assertion).
- literal fact: `... by literal fact "(1::nat) + 1 = 2" failed: Failed to
  retrieve literal fact: ...`
- attributes-only (M4, final K2 form — a case on `Position.here`'s own
  result): with no position at all (the ML assertion, `Position.none`) the
  fallback reads `... by the given certificate failed:` — asserted; at the
  real command under this front end, whose token positions are id-only,
  `Position.here` yields the clickable PIDE here-marker, so the message reads
  `by the certificate given at <here-marker>` (observed, marker invisible in
  plain capture); with a line/file position it reads
  `given at (line N of ...)` / `(file ...)` — reasoned from
  position.ML:278-287, not executed.
- duplicate debt name in one command: `"Glue.glue1" is named twice in one
  discharge` (m8; fires before any proof runs).
- entry check (ML-only; both real creators close their propositions via
  `Logic.close_prop`): `add_debt_axiom: free term variables in P` — exact.
- `glue2` (`A ==> A`, conclusion is its own premise) discharged by `refl` —
  the assume leg of the `ares_tac` head.

## Section 8.4 — the new capability — `Poly.thy`

As in the interim run, now on the final code (outputs in `Poly.out.txt`):
suite 1 C1's crashing input declares cleanly with the ledger normal form
printed; the debt is used at two instance types; discharged by a strictly
weaker-sort certificate; the composite obligation (`OFCLASS('a set,
preorder)`, suite 3 G2a in situ) closes; the sort-exceeding negative fails
with the named error and the residual obligation displayed — now WITHOUT the
exception-wrapper line (R2):
`discharge_debt_axiom: discharging "Poly.neg" by strong_comm failed:
 Proof failed.  1. !!x y. OFCLASS('a, ab_semigroup_add_class) ==>
 OFCLASS('a, comm_monoid_add_class)`.

## Section 8.4-5 — `Deps.thy`

A certificate derived FROM a debt is rejected by the kernel's
oracle-dependency check (`Some of the given certification theorems are based
on axiomized debts!`); its proposition equals the ledger entry, so the
kernel's `op =` acceptance is on the path.  Ledger unchanged.

## Sections 8.3-3 / 8.4-6 — `IsDebt.thy`

All checks are hard ML pattern bindings; theory CLEAN.  `is_debt` TRUE on the
exported propositions of the premised mono debt and the polymorphic debt
(queries via `Spec_Rules.get`); FALSE on the nat instance, `add.commute`, and
the `specify_type` bijection axiom; after discharging d1 through the real
command its surviving Spec_Rules entry flips to FALSE while d2 stays TRUE.

## Checklist item 4 — the example, loaded through the local front end

`example/Debt_Axiom_Doc.thy` evaluates CLEAN with zero warnings on the final
code, through the same headless PIDE front end (Isabelle-MCP) as everything
above; all six of its `print_debt_axiom` outputs are recorded in
`Debt_Axiom_Doc.out.txt`, and the two new polymorphic comment transcripts
(thy 151, 162) were re-verified verbatim against them.  This run is
the one exercise of the for-fixes declaration form (`for x :: 'a::linorder
and y :: 'b::comm_monoid_add` — the raw_fixes slot of `gen_axioms`) and of
the two-variable weaker-sort discharge (`preorder` for `linorder` AND
`monoid_add` for `comm_monoid_add`).

## Probes

- `MaxidxProbe.thy` — endpoint demonstration for the maxidx
  formula/observation gap (noted fact -1, chain theorem 0); the root cause is
  the source trace recorded in `ledger_dump.diff`, not this probe.
- `TypeRaiseProbe.thy` — the R5 totality boundary: a query whose sort names a
  class undeclared in the given theory value returned `false` (hard binding);
  before R5 this exact input raised `TYPE "Undeclared class"`.
