# Before-transcripts (plan section 8.3-0), recorded on the UNPATCHED worktree

- Date: 2026-09-02
- Worktree: `contrib/phi-system` at commit `bcdffbe4e6371569ae3be21a524e72fe3a84af90`,
  `Debt_Axiom/` unmodified (`git status --porcelain -- Debt_Axiom/` empty).
- Prover: Isabelle2025-2, session heap `HOL`, headless PIDE (Isabelle-MCP);
  `Debt_Axiom.Debt_Axiom` loaded dynamically from source via
  `session_dirs = [contrib/phi-system/Debt_Axiom]` — so the transcripts run the
  production `Debt_Axiom.ML` exactly as checked out.
- Theory sources: `Before_T1.thy`, `Before_T2.thy` (this directory).
- Section 8.3-4 re-runs these two theories after the patch and compares.

## Transcript 1 — premised monomorphic debt x monomorphic certificate

EXPECTED (plan): "Proof failed."  OBSERVED: exactly that; the production
tactic is a single `ares_tac` application, which resolves once and leaves the
premise subgoal open.  Note the failure surfaces as a raw uncaught THM
exception, not a clean ERROR.

```
print_debt_axiom
[normal] Good job! No debt axiom is recorded.

debt_axiomatization before1: <<n < m ==> n <= (m::nat)>>
(no output)

print_debt_axiom
[normal] 1 axiom debts are recorded: Before_T1.before1 : !!n m. n < m ==> n <= m

lemma before1_cert: <<n < m ==> n <= (m::nat)>>  by (rule less_imp_le)
(clean)

discharge_debt_axiom before1 : before1_cert
[error] exception THM 0 raised (line 83 of "goal.ML"): Proof failed.
 1. !!n m. n < m ==> n < m
(!!n m. n < m ==> n < m) ==> (!!n m. n < m ==> n <= m)

print_debt_axiom
[normal] 1 axiom debts are recorded: Before_T1.before1 : !!n m. n < m ==> n <= m
```

After the patch (section 8.3-4): this discharge must SUCCEED (the `assume_tac`
leg of the closing step closes the residual premise subgoal; ruling 7's test).

## Transcript 2 — unconditional monomorphic debt x polymorphic library certificate

EXPECTED (plan): success (the ground-instantiation case that already works
today via `ares_tac` resolution instantiating `?'a := nat`).  OBSERVED: success.

```
print_debt_axiom
[normal] Good job! No debt axiom is recorded.

debt_axiomatization before2: <<(x::nat) + y = y + x>>
(no output)

print_debt_axiom
[normal] 1 axiom debts are recorded: Before_T2.before2 : !!x y. x + y = y + x

discharge_debt_axiom before2 : add.commute
(no output; theory clean)

print_debt_axiom
[normal] Good job! No debt axiom is recorded.
```

After the patch (section 8.3-4): this discharge must STILL succeed.
