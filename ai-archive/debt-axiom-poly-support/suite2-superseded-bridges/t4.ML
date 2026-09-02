(* t4.ML — T4: regression — original single-variable weaker-sort case under the FIXED code *)

val _ = pr "==== T4: debt at 'a::comm_monoid_add, certificate add.commute (ab_semigroup_add) ====";

val debt_prop = comm_statement (TFree ("'a", S_cma));
val _ = pr "T4 debt proposition:";
val _ = prtm debt_prop;

val goal_term = ledger thy debt_prop;
val _ = pr "T4 ledger goal term:";
val _ = prtm goal_term;

val add_commute = Global_Theory.get_thm thy "add.commute";
val rules = map (Thm.unconstrainT o Thm.varifyT_global) [add_commute];
val _ = pr "T4 rule:";
val _ = prts (hd rules);

val bridges = classrel_bridges thy goal_term rules;
val _ = report_bridges "T4 pinned bridges (expect 1: comm_monoid_add ==> ab_semigroup_add)" bridges;

val _ = run_case "T4 discharge (fixed recipe)" goal_term (discharge_tac ctxt rules bridges);

val _ = pr "==== T4 done ====";
