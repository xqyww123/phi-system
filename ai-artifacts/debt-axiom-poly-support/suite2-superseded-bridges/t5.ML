(* t5.ML — T5: negative — certificate sort strictly EXCEEDS the debt's *)

val _ = pr "==== T5: debt at 'a::ab_semigroup_add, certificate proved at 'a::comm_monoid_add ====";

val debt_prop = comm_statement (TFree ("'a", S_asa));
val cert_prop = comm_statement (TFree ("'a", S_cma));
val _ = pr "T5 debt proposition:";
val _ = prtm debt_prop;

val goal_term = ledger thy debt_prop;
val _ = pr "T5 ledger goal term:";
val _ = prtm goal_term;

val add_commute = Global_Theory.get_thm thy "add.commute";
val cert = prove_cert "T5 certificate (at comm_monoid_add)" cert_prop
  (resolve_tac ctxt [add_commute] 1);
val rules = map (Thm.unconstrainT o Thm.varifyT_global) [cert];
val _ = pr "T5 rule (its premise demands OFCLASS comm_monoid_add):";
val _ = prts (hd rules);

val bridges = classrel_bridges thy goal_term rules;
val _ = report_bridges
  "T5 generator output (expect 0: ab_semigroup_add does not derive comm_monoid_add)" bridges;

val _ = run_case "T5 discharge attempt (expect clean failure, no hang)" goal_term
          (discharge_tac ctxt rules bridges);

val _ = pr "==== T5 done ====";
