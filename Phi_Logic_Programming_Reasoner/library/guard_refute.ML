(*  Title:      guard_refute.ML
    Author:     the phi-system project

Refutation of guard conditions by finite model search: preprocessing plus the
patched Nitpick copy Phi_Nitpick.  Design and measurements in
Docs/GUARD_NITPICK_FALSIFY_PLAN.md, sections 19 to 22.

What the guard means is not known here: the rewrites come from the memory
model and from each struct, and any weakening of the premises comes from a
hook registered by the theory that owns the notion being weakened.  This file
is loaded from PLPR, which precedes all of them.
*)

signature PHI_GUARD_REFUTE =
sig
  (*Not reasoners.ML's race_result: Provable carries no proof object, only the
    news that this refuter should keep its hands off.  The caller maps into
    the race -- today Refuted wins, Provable and Unknown give up.*)
  datatype verdict = Refuted | Provable | Unknown

  (*arg = Proof.context, state = term list; see the structure below*)
  structure Preprocess_Hooks : HOOKS

  (*arg = unit, state = Proof.context; see the structure below*)
  structure Simpset_Hooks : HOOKS

  val premises_of : Proof.context -> term list -> term -> term list
  val slice : term list -> term -> term
  val preprocess : Proof.context -> term list -> term -> (term list * term) option

  val nitpick : Proof.context -> Phi_Nitpick.params -> int * int ->
                (term * term) list * term list * term -> verdict
end

structure Phi_Guard_Refute : PHI_GUARD_REFUTE =
struct

datatype verdict = Refuted | Provable | Unknown


(*** Stores ***)

(*Rewrites run over the guard before the search.  Registered rules must be
  THEOREMS: Provable below rests on the preprocessing being meaning-preserving.
  Do NOT register addr_gep_def -- its map_addr lambda defeats the [iff] gep
  lemmas and cost refutations when tried (plan 19.4).*)
structure Guard_Refute_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>guard_refute_simp\<close>
  val comment = "rewrites applied to a guard before refuting it by model search"
  val attribute = NONE
  val post_merging = I
)

(*Premise transformers, run in priority order before the simplifier.  A hook
  may only WEAKEN: the caller's soundness story (see the header) is that
  P ==> P', and nothing checks it -- a hook that strengthens or that touches
  the conclusion breaks this refuter silently.  The polarity discipline that
  makes a weakening legal belongs to the hook, which knows what it is
  weakening; see Phi_BI's satisfaction scrub for the reference shape.*)
structure Preprocess_Hooks = Hooks (
  type arg = Proof.context
  type state = term list
)

(*Simpsets the refuter must also consult, contributed by theories this file
  cannot name: it is loaded from PLPR, which precedes the memory model and
  every aggregate.  A contributor registers its ENHANCER, not its rules, so
  the store is read when the refuter runs and a rule declared later still
  arrives.  Copying the rules instead would be a snapshot, and no snapshot can
  work here: the aggregate kinds are siblings and no single theory sees them
  all.*)
structure Simpset_Hooks = Hooks (
  type arg = unit
  type state = Proof.context
)


(*** Which context assumptions travel with the guard ***)

(*Premise-tagged ones only (author ruling, plan 19.2); an obligation is a
  goal, not a fact.  Dropping a premise ENLARGES the model space, so this
  filter widens the misjudgment surface -- it is a ruling, not an
  optimisation.*)

fun is_premise (Const (\<^const_name>\<open>Trueprop\<close>, _) $
                    (Const (\<^const_name>\<open>Premise\<close>, _) $ mode $ _)) =
      (case mode of
         Const (\<^const_name>\<open>default\<close>, _) => true          (*\<premise>*)
       | Const (\<^const_name>\<open>MODE_GUARD\<close>, _) => true       (*\<condition>*)
       | _ => false)                                        (*\<obligation>: a goal*)
  | is_premise _ = false

fun premises_of _ assms goal =
  Logic.strip_imp_prems goal @ filter is_premise assms


(*** Conjunction splitting and variable-closure slicing ***)

(*A premise is kept or dropped whole, so splitting conjunctions first is what
  lets slicing separate an unrelated invariant from the conclusion's
  variables.  Both run on the simplifier's output, where unfolding a
  definition has just produced fresh conjunctions.*)

fun split_conjunctions prem =
  (case prem of
     Const (\<^const_name>\<open>Trueprop\<close>, _) $ t =>
       let
         fun split (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ a $ b) = split a @ split b
           | split t = [t]
       in map HOLogic.mk_Trueprop (split t) end
   | _ => [prem])

fun slice prems concl =
  let
    fun frees_of t = map fst (Term.add_frees t [])
    fun grow known pending =
      let
        val (connected, rest) =
          List.partition (fn p => exists (member (op =) known) (frees_of p)) pending
      in
        if null connected then []
        else
          let val known' = fold (union (op =) o frees_of) connected known
          in connected @ grow known' rest end
      end
  in
    Logic.list_implies (grow (frees_of concl) (maps split_conjunctions prems), concl)
  end


(*** Case distinctions ***)

(*A case over a FREE variable reduces by no rewrite, and neither clarsimp nor
  auto helps: both use the simplifier's splitter, whose only default rule is
  if_split.  The datatype's split theorem does it, and the goal's own case
  constants name the datatypes -- empty table, no cost, when there are none.*)

fun case_splits ctxt t =
  Term.add_consts t []
  |> map fst
  |> distinct (op =)
  |> map_filter (Ctr_Sugar.ctr_sugar_of_case ctxt)
  |> map #split


(*** The pipeline ***)

(*NONE means the simplifier closed the goal.  That is a real proof of the
  ORIGINAL guard: the hooks and the slice weaken the premises, and P ==> P'
  with a proof of P' ==> C gives P ==> C.  In the other direction the weakening only
  costs completeness -- see the verdict map in reasoners.ML.*)

fun preprocess ctxt assms goal =
  let
    val concl = Logic.strip_imp_concl goal
    val prems =
      Preprocess_Hooks.invoke (Context.Proof ctxt) ctxt (premises_of ctxt assms goal)
    val prepared = Logic.list_implies (prems, concl)
    val simp_ctxt =
      Guard_Refute_SS.enhance ctxt
        |> Simpset_Hooks.invoke (Context.Proof ctxt) ()
        |> fold Splitter.add_split (case_splits ctxt prepared)
    val st =
      (case SINGLE (Simplifier.asm_full_simp_tac simp_ctxt 1)
              (Goal.init (Thm.cterm_of ctxt prepared)) of
         SOME st => st
       | NONE => Goal.init (Thm.cterm_of ctxt prepared))
  in
    if Thm.nprems_of st = 0 then NONE
    else
      let
        val residue = Thm.term_of (Thm.cprem_of st 1)
        val sliced = slice (Logic.strip_imp_prems residue) (Logic.strip_imp_concl residue)
      in SOME (Logic.strip_imp_prems sliced, Logic.strip_imp_concl sliced) end
  end

(*The premises go in through the ASSUMPTION parameter, not inside the goal:
  only then are they separate formulas internally, and only per formula can
  Phi_Nitpick take a soundness flag.  Passing them inside the goal turns the
  trust patch silently off.

  genuine and quasi_genuine both count, as in reasoners.ML's verdict map and
  for its reason: under user_axioms = false nothing can be certified genuine.

  The model search gets its OWN timeout, independent of what preprocessing
  cost (author ruling 2026-08-28).  Charging preprocessing against the search
  makes the search's reach depend on a quantity that has nothing to do with
  it, and makes two measurements incomparable whenever preprocessing differs.
  The caller's watchdog must therefore allow preprocessing ON TOP of that
  timeout.*)

fun nitpick ctxt params (i, n) (subst, assms, goal) =
  (case preprocess ctxt assms goal of
     NONE => Provable
   | SOME (prems, concl) =>
       (case Phi_Nitpick.pick_nits_in_term (Proof.init ctxt) params true
               Phi_Nitpick.Auto_Try i n 0 subst [] prems concl of
          (code, _) =>
            if code = Phi_Nitpick.genuineN orelse code = Phi_Nitpick.quasi_genuineN
            then Refuted else Unknown))

end
