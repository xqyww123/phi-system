(* t3.ML — T3: monomorphic behavior of the fixed recipe *)

val _ = pr "==== T3: monomorphic premised debt ====";

val natT = Type ("Nat.nat", []);
val lessC = Const ("Orderings.ord_class.less", natT --> natT --> boolT);
val leC = Const ("Orderings.ord_class.less_eq", natT --> natT --> boolT);
val n = Free ("n", natT);
val m = Free ("m", natT);
val debt_prop =
  fold_rev Logic.all [n, m]
    (Logic.mk_implies (mk_Trueprop (lessC $ n $ m), mk_Trueprop (leC $ n $ m)));
val _ = pr "T3 debt proposition:";
val _ = prtm debt_prop;

val goal_term = ledger thy debt_prop;
val _ = pr ("T3 ledger form aconv the debt itself (expect true): " ^
            Bool.toString (goal_term aconv debt_prop));

val less_imp_le = Global_Theory.get_thm thy "less_imp_le";
val cert = prove_cert "T3 certificate (monomorphic)" debt_prop
  (resolve_tac ctxt [less_imp_le] 1 THEN assume_tac ctxt 1);
val rules = map (Thm.unconstrainT o Thm.varifyT_global) [cert];
val _ = pr "T3 rule:";
val _ = prts (hd rules);

(* 1. generator on a monomorphic ledger entry *)
val bridges = classrel_bridges thy goal_term rules;
val _ = report_bridges "T3.1 bridges on monomorphic ledger (expect 0)" bridges;

(* 2. fixed recipe *)
val _ = run_case "T3.2 discharge_tac (fixed recipe, bridges=[])" goal_term
          (discharge_tac ctxt rules bridges);

(* 3. CONTRAST: current production recipe — ONE application of Tactic.ares_tac *)
val _ = run_case "T3.3 production recipe: Tactic.ares_tac rules 1 (single application)" goal_term
          (Tactic.ares_tac ctxt rules 1);

val _ = pr "==== T3 done ====";
