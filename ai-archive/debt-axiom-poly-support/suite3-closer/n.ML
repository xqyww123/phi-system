(* n.ML — N: negatives; must fail cleanly (no hang, no false success, residue visible) *)

val add_commute = Proof_Context.get_thm ctxt0 "add.commute";
val finite_UNIV = Proof_Context.get_thm ctxt0 "finite_UNIV";

(*N-a: underivable composite: obligation OFCLASS('a set, finite_class) with only 'a::type in hyps
  (set :: (finite) finite needs 'a::finite, which the debt does not grant)*)
val _ = case_run "N-a (underivable composite: 'a set :: finite from 'a::type)"
  (rp "finite (UNIV :: ('a set) set)") finite_UNIV;

(*N-b: cert sort strictly exceeds debt's on a bare variable (earlier T5)*)
val _ = case_run "N-b (debt semigroup_add, cert needs ab_semigroup_add)"
  (rp "!!x y::'a::semigroup_add. x + y = y + x") add_commute;

(*N-c: a TFree in the obligation with NO OFCLASS hypothesis at all.
  Cannot arise from ledger_form (every debt TFree, even at sort {type}, gets an OFCLASS
  premise; mk_of_sort emits nothing only for a literally empty debt sort). We engineer it
  by hand-building the goal as the sort-stripped prop WITHOUT its OFCLASS premise.*)
val nc_goal = #3 (stripped_sorts thy0 (rp "!!x y::'a::ab_semigroup_add. x + y = y + x"));
val _ = case_run_goal "N-c (obligation TFree with no OFCLASS hyp)" nc_goal add_commute;

val _ = writeln "N DONE";
