# Question: why do phi-type property derivers need exhaustive reasoning?

Repository: `/home/qiyuan/Current/MLML/contrib/phi-system/` (all paths below are
relative to it).  Isabelle 2025-2 sources: `/home/qiyuan/Current/MLML/contrib/Isabelle2025-2/src/Pure/`.
Answer by reading the code; cite `file:line` for every claim.  Do not modify
any file and never run `isabelle build`.

## What is being asked

phi-system's logic-programming reasoner PLPR is a priority-guided depth-first
search that returns the first solution it reaches.  A separate mode,
*exhaustive reasoning*, traverses every branch and combines the proof
obligations of the branches by disjunction.  It has exactly one user: the
phi-type property derivers.  The question is:

**Why do the derivers need exhaustive reasoning, i.e. what would go wrong if
they used the ordinary first-solution search?  And why does nothing else in
the system (in particular the reasoning done for phi statements inside a
programming block) need it?**

Give a precise, mechanism-level answer with a concrete worked example taken
from the code (a real deriver, a real phi-type, real reasoning rules), showing
where the alternative branches come from, what each branch leaves behind, and
what the derivation does with the combined result.  If the drafter's
hypothesis in Section 3 is wrong or incomplete, say so and correct it.

## 1. Facts about the mechanism (verified)

- Ordinary run: `gen_reason'` (`Phi_Logic_Programming_Reasoner/library/reasoner.ML:910`),
  entered through `Phi_Reasoner.reason` (`:947-953`).  A run ends when it
  reaches a `\<r>Success` antecedent (the `Success` exception) or fails.
  Side conditions that a rule leaves behind are recorded into an
  `\<obligation> P` premise (`Premise MODE_COLLECT P`) rather than decided
  during the search (`defer_obligation_tac`, `PLPR.thy:1970-1978`).
- Exhaustive reasoning: `PLPR_Exhaustive.reason_exhaustively`
  (`Phi_Logic_Programming_Reasoner/library/exhaustive.ML:25-93`).  Documentation
  text: `PLPR.thy:2470-2472` "φ-LPR is a priority-guided depth-first reasoner
  giving the first reached solution.  This extension enables exhaustive
  reasoning traverses all branches and combines proof obligations for each
  branch by disjunction."  Mechanism: the success handler (`exhaustive.ML:64-67`)
  stores each branch's result theorem (exported with
  `Proof_Context.export ctxt' ctxt`) in a `Synchronized.var` and raises
  `Phi_Reasoner.Explorative_Backtrack`, which the engine turns into
  backtracking (`reasoner.ML:804-809`); when every path is exhausted the run
  returns `NONE` (`:68-71`); the stored branches are merged pairwise with
  `merge_oblg_divergence` (`:73-79`):

  ```
  lemma merge_oblg_divergence:                                (PLPR.thy:2474-2478)
    ⟨ PROP Pure.prop (\<obligation> Pa ⟹ C)
  ⟹ PROP Pure.prop (\<obligation> Pb ⟹ C)
  ⟹ PROP Pure.prop (\<obligation> Pa ∨ Pb ⟹ C)⟩
  ```
  The conclusions of all branches must agree (`exhaustive.ML:76-77`:
  "The conclusion in exhaustive φ-LPR reasoning diverges between branches.").
- The only caller: `Phi_System/library/phi_type_algebra/deriver_framework.ML:2093`
  inside `exhaustive_PLPR_reasoner` (`:2084-2096`; the `_by_rule` variant
  `:2098-2099` first resolves a given rule).  These two are passed as the
  `reasoner` argument of the deriver framework by 21 derivers in
  `Phi_System/library/phi_type_algebra/` (e.g. `identity_element.ML:228-230`,
  `transformation_functor.ML:201, :436`, `semimodule_scalar.ML:114`,
  `inhabited_type.ML:55`, `is_functional.ML:105`, `separation_homo.ML:125-126`).
- Deriver goal template (`deriver_framework.ML:175-181`):
  ```
  ( <the leading antecedent is the one to which induction applies> ⟹
    <some optional antecedents, but no induction will be applied on them> ⟹
    \<r>Success (*terminates the deriving successfully*) ) (*repeats*) ⟹
  \<obligation> True (*stores the generated proof obligations*) ⟹
  <derived property>
  ```
- After `reasoning` returns (`deriver_framework.ML:1474-1476`), the accumulated
  obligation is proved at derivation time by `oblg_solver`
  (`:1480-1482`, definition `:1274-1305`: simplification, an optional hinted
  method, then `Phi_Envir.solve_obligation`, i.e. the sledgehammer-backed
  obligation solver); the derived rule is then simplified, exported and
  returned (`:1483-1497`).
- An example rule used by the Identity_Element deriver
  (`Phi_System/Phi_Type.thy:6168-6172`):
  ```
  X ⇢ A ⟹ (\<condition> A ⟹ Identity_Element\<^sub>I X Q) ⟹ \<premise> (A ⟶ Q ⟶ P) ⟹ Identity_Element\<^sub>I X P
  ```

## 2. Facts about the other users of the engine

Phi statements inside a programming block reason on one concrete state
sequent (`Phi_Apply.apply1`, `Phi_System/library/system/application.ML:94-107`,
via `PLPR_Optimum_Solution.best_among`, `library/optimum_solution.ML:127-138`)
and never use exhaustive reasoning.  Obligations left by such a run are
either attacked at once by the guard solver or presented to the user.

## 3. The drafter's current hypothesis (to be checked)

A derivation reasons on a *generic* instance: the phi-type's parameters are
fixed variables and the abstract object is destructed by induction
(`deriver_framework.ML:1455-1470`).  Therefore the side conditions that rules
leave behind cannot be judged during the search — they mention only variables.
When two rules apply to the same subgoal and leave different conditions
(say `y = 1` vs. `D y`), a first-solution search commits to the first that
"succeeds", where success only means the condition was recorded, not proved.
If that condition is unprovable for this type, `oblg_solver` fails and the
derivation fails, although the other branch would have worked; the search
never returns to it because it believes it succeeded.  Exhaustive reasoning
defers the choice: it collects every branch's condition into
`\<obligation> (P₁ ∨ P₂ ∨ …) ⟹ C`, and `oblg_solver` only has to prove one
disjunct.  This works because the derived conclusion `C` is fixed and only
the condition varies.  Statement-level reasoning does not need this: its
objects are concrete, the obligation is attacked immediately or shown to the
user, and the user can redirect the search; a derivation runs unattended.

Points the hypothesis does not settle and that the answer should:

1. Is "several rules apply to the same subgoal and leave different
   conditions" really the source of the branches, or do branches also (or
   mainly) come from something else — e.g. the induction cases, different
   instantiations of schematic variables, the `\<A>_simp` rules used by
   `exhaustive_PLPR_reasoner_by_rule`?  Show a real instance.
2. Why is a *disjunction* the right combination (rather than, say, taking
   the weakest condition, or keeping the branches as separate rules)?
3. What does the `chk_unfolds` argument of `exhaustive_PLPR_reasoner`
   (`deriver_framework.ML:2084-2092`, `chk_unfolded`) check, and how does it
   relate to the exhaustiveness?
4. Would a first-solution search with backtracking on `oblg_solver` failure
   be an alternative, and why was it not chosen (cost of sledgehammer inside
   the search, or something structural)?
5. Are there situations where exhaustive reasoning is *harmful* for a
   deriver (e.g. exponential branch count, diverging conclusions), and how do
   the derivers cope?
