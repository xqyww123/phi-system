# Executed evidence for the Polymorphic Debt Support project

Companion of `Docs/DEBT_AXIOM_POLY_SUPPORT_PLAN.md` (§8 cites these files).
All suites ran on the stock HOL heap of `contrib/Isabelle2025-2`, 2026-09-01/02,
copied here from the authoring session's scratchpad
(`/tmp/claude-1002/-home-qiyuan-Current-MLML/0d7a3f0b-9e6f-4b94-904c-3b48067a9a97/scratchpad/`)
before implementation started.

Run commands (from this directory; `ML_PROCESS` =
`/path/to/contrib/Isabelle2025-2/bin/isabelle ML_process -l HOL`):

- suite 1: `ML_PROCESS -f suite1-feasibility/testX.ML` (each file self-contained)
- suite 2: `ML_PROCESS -f suite2-superseded-bridges/common.ML -f suite2-superseded-bridges/tN.ML`
- suite 3: `ML_PROCESS -f suite3-closer/common.ML -f suite3-closer/<group>.ML`
- suite 4: `ML_PROCESS -f suite4-is_debt/<group>.ML` (each file self-contained;
  the session's `harness.ML` + `*.part.ML` fragments are the same content
  split for interactive use and are deliberately NOT duplicated here)

## suite1-feasibility (plan §8.1) — rev-1 feasibility

- `testA.ML` — `Thm.of_class` across a subclass gap; `unconstrainT` output
  shape; clean THM failure on an underivable pair (A1-A3).
- `testB.ML` — weaker-sort discharge of a debt in the ledger normal form via a manually
  built bridge; negative control without the bridge; literal-subset control
  (B1-B8).
- `testC.ML` — declaration chain: before-crash `Illegal fixed variable`,
  fixed chain recovers the sorted proposition exactly, mono identity with
  maxidx -1 -> 0 (C1-C3).
- `testD.ML` — `Pattern.equiv`: accepts type-variable renaming, rejects a
  sort change and a diagonal collapse (D1-D3).

## suite2-superseded-bridges (plan §8.2 preamble) — SUPERSEDED design

Evidence for the rejected pre-computed bridge-list design, kept because it
documents that design's order-dependent divergence (t1/t2 contain the T1S/T2S
configurations where the unbounded closing tail hangs past its timeout).
`common.ML` holds the then-current `classrel_bridges`; `t1.ML`-`t5.ML` the
two-variable, reflexive-bridge, monomorphic, regression, and negative groups.

## suite3-closer (plan §8.2) — the final subgoal-directed closing step

`common.ML` holds `ofclass_close_tac` + `discharge_tac` exactly as the plan
prints them (head combinator aside, see plan §8.0).  Groups: `g1.ML`
bare-variable cases; `g2.ML` composite-over-variable; `g3.ML` ground
(incl. the production-baseline regression guards); `g4.ML` composite over
ground; `g5.ML` mixed; `n.ML` negatives (N-a/b/c); `p3.ML` adversarial hunt
(note: P3-6 is a DESIGNED NEGATIVE despite the P-name — an uninstantiated
certificate type variable must leave a residue); `extra.ML` E1-E4
extensions; `shyps.ML` sort-hypothesis cleanliness probe; `smoke.ML`
ground `of_class` probe.  `full_run.log` / `extra_run.log` are the recorded
outputs (26 side-by-side cases against production `ares_tac`).

## suite4-is_debt (plan §8.2) — the final `match_form`/`is_debt`

`g0_probe.ML` real `Spec_Rules.add` export-shape probe; `g1_positives.ML`
M1-M8 (all queries via real export round trips); `g2_negatives.ML` N1-N8
(incl. instance-vs-variant both directions); `g3_hunt.ML`/`g4_hunt2.ML`
H1-H10 (incl. the H8b dotted-name boundary); `g5_mass.ML` mass sweeps
(Main's 15 Spec_Rules-Unknown props, 1945 spec-rule props, 6000 global
facts: zero spurious matches, zero exceptions).

## real-command-transcripts (plan §8.3-0/3/4, §8.4) — added at implementation

Scratch theories run through the REAL commands on the local worktree
(Isabelle2025-2, HOL heap, headless PIDE, `Debt_Axiom.Debt_Axiom` loaded from
source).  Each theory has a matching `.out.txt` with its raw per-command
outputs, captured 2026-09-02 on the FINAL post-review code (review fixes M4,
m7, m8 and adopted proposals R2-R5 landed).

- `Before_T1.thy`/`Before_T2.thy` + `TRANSCRIPTS.md` — the §8.3-0
  before-transcripts on the UNPATCHED worktree (premised mono discharge fails
  "Proof failed."; mono × polymorphic library certificate succeeds);
  their `.out.txt` files record the §8.3-4 re-runs (both now succeed).
- `Glue.thy` — the three certificate-shape error texts (ASSERTED via
  `String.isSubstring` on markup-stripped messages), the entry-check message,
  the duplicate-name rejection (m8), and the `ares_tac`-head tautological
  case.
- `Poly.thy` (§8.4-1..4,7), `Deps.thy` (§8.4-5 oracle-dependency rejection),
  `IsDebt.thy` (§8.3-3, §8.4-6 — hard `val true/false` bindings).
- `Debt_Axiom_Doc.out.txt` — checklist item 4: the example loaded through
  the headless PIDE front end (Isabelle-MCP), clean, all six
  `print_debt_axiom` outputs recorded and the comment transcripts
  verbatim-verified; the one exercise of the for-fixes declaration form and
  the two-variable weaker-sort discharge.  `Poly.out.txt` additionally
  carries the §8.4-1 show_sorts witness (the returned fact keeps the
  user-stated sorts).
- `MaxidxProbe.thy` — maxidx endpoint demonstration (see `ledger_dump.diff`
  for the root-cause source trace); `TypeRaiseProbe.thy` — the R5 totality
  boundary (undeclared-sort query returns false instead of raising).
- `AFTER_RESULTS.md` — the narrative record of all of the above.

## ledger dumps (added at implementation, plan §8.3-1)

`ledger_dump.pre.txt` / `ledger_dump.post.txt` and the dump-producing
`Ledger_Dump.thy` + `ledger_dump.py` driver — the FINAL pair, captured on
cslh19 on the post-review code (Phi_System_Base REPL heap, both captures
importing `PhiEx_All`, worktree differing only by the two patched files).
`compare_dumps.py` is the field-by-field comparator (prop_ml byte equality
AND serial-normalized prop_pretty equality, both required);
`ledger_dump.diff` records its verdict (PASS, zero observable deviation),
the maxidx root-cause source trace, and the serial-family analysis.
`corpus_run_baseline.out.txt` / `corpus_run_patched.out.txt` are the
section 8.3-2 full-chain runs (clean tree 900.3 s / patched tree 885.3 s,
both `ERRORS RETURNED: None`), each quoting its `hard_restart.sh` output;
`corpus_run_interim.out.txt` is the pre-review interim run kept for the
record.  The harness itself is archived beside them (`hard_restart.sh`,
`run_probe.py`, from cslh19's home).

## reuse-equivalence (plan §8.0)

`reuse_equivalence.ML` + `reuse_equivalence.out.txt` — the shipped
library-reuse `gen_all_term` measured against the design-phase hand-rolled
form over 1945 Spec_Rules propositions and 24875 global-fact propositions
(`Global_Theory.all_thms_of thy false`), zero disagreements.
