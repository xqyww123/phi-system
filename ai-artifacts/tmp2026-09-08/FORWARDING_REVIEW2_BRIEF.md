# Review brief, round two: the forwarding function after the first review's fixes

Read `FORWARDING_REVIEW_BRIEF.md` in this directory first: it explains the emitter, `new_fun`,
the routine hook, the owner's standards and the change. This brief only records what changed
since that review. The diff under review now is `forwarding_review2.diff` (the earlier
`forwarding_review.diff` is the state the first review saw).

## The first review's verdict and what was done with it

The judge accepted the change subject to two must-fix items (run it; bring the documents in
line) and five should-fix items; it rejected as wrong or hair-splitting the correctness scare
about restarting from `ftab`/`ss`, a request for a contract comment in `base.sig`, a comment
about the variable counter in forwarding mode, a glossary entry, and a request to route the
forwarding call through `pV`/`call`. The owner ruled on the remaining items:

- Shared "is this type void" test: refused (two sites, not worth trust-base lines).
- Alias in the forwarding branch: registered to `m` (not to the forwarding function), so
  internal call sites keep calling the function that holds the body. Adds one line.
- The plan document `ai-artifacts/CODEGEN_INSTANCE_NAMING_PLAN.md`: sealed, not corrected
  section by section. A note prepended at its head records the departures from the text,
  points at the commits, and holds the verification record of this change. Where the sealed
  text and the code disagree, the code is authoritative.
- The two-exports test: promoted to a permanent test. It is one line in
  `Phi_Test/PhiTest_Arithmetic.thy` (`declare GCD_def [\<phi>export gcd]`) rather than a new
  theory, because a new theory importing `Phi_Examples.Linked_List` would have made the
  `Phi_Test` session depend on `Phi_Examples`.

Applied since the first review (all in `forwarding_review2.diff`):

1. `base.ML`: the head comment of `new_fun` gained the soundness clause for the second hook
   call and the third cause of the branch (two different instances printing the same text).
2. `base.ML`: a comment above the case split saying both hit branches return to the table
   before the print.
3. `base.ML`: the forwarding branch registers the alias to `m`'s call printer; the alias
   binder is `a` in both branches (it was `m` in the define branch, colliding with the other
   uses of `m`).
4. `routine.ML`: `params` renamed to `vs`, the name the sibling hook `CF.ML` already uses for
   a list of `_vN` strings.
5. `Phi_Test/PhiTest_Arithmetic.thy`: the permanent test.
6. Documents: the sealing note at the head of the plan; a concluding paragraph at the head of
   Section 2 of `ai-artifacts/CODEGEN_FORWARDING_HANDOFF_2026-09-08.md`; the README of this
   directory.

## Verification, done (2026-09-09, one prover session)

`PhiTest_Arithmetic.thy` evaluated to its `end`: clean; the generated file holds `GCD` with
its recursive body and

```c
int gcd(int _v0, int _v1) {
return GCD(_v0, _v1);
}
```

The eight example theories regenerated: same function counts as before, text identical up to
typedef serial numbers (the serial counter is per prover process). All files pass
`gcc -x c -Wall -Wextra -fsyntax-only` with the same three pre-existing source-level
unused-value warnings. Trust base: 375 code lines by cloc, 366 before this change.

## What this round should judge

Whether the applied fixes are right and elegant, whether the comments are accurate and
load-bearing, whether the alias line and the `a` rename are correct, whether the permanent
test is placed well, whether the sealing note is accurate, and whether anything from the
first round was mis-applied or left out. The owner's earlier decisions above are not up for
debate.
