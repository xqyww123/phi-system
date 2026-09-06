(* t1.ML — T1: two-type-variable debt, different sorts, pinned vs unpinned, both orders *)

val _ = pr "==== T1: two-type-variable debt ('a::comm_monoid_add, 'b::comm_monoid_mult) ====";

fun t1_statement Ta Tb =
  let
    val x = Free ("x", Ta); val y = Free ("y", Ta);
    val u = Free ("u", Tb); val v = Free ("v", Tb);
    val body = mk_conj (mk_eq Ta (mk_plus Ta x y) (mk_plus Ta y x))
                       (mk_eq Tb (mk_times Tb u v) (mk_times Tb v u));
  in fold_rev Logic.all [x, y, u, v] (mk_Trueprop body) end;

val debt_prop = t1_statement (TFree ("'a", S_cma)) (TFree ("'b", S_cmm));
val cert_prop = t1_statement (TFree ("'a", S_asa)) (TFree ("'b", S_asm));
val _ = pr "T1 debt proposition:";
val _ = prtm debt_prop;

val add_commute = Global_Theory.get_thm thy "add.commute";
val mult_commute = Global_Theory.get_thm thy "mult.commute";

val cert = prove_cert "T1 certificate (weaker sorts ab_semigroup_add/ab_semigroup_mult)"
  cert_prop (asm_full_simp_tac (fold Simplifier.add_simp [add_commute, mult_commute] ctxt) 1);

val rules = map (Thm.unconstrainT o Thm.varifyT_global) [cert];
val _ = pr "T1 rule (unconstrainT o varifyT_global of certificate):";
val _ = prts (hd rules);

(* step 1: ledger normal form *)
val goal_term = ledger thy debt_prop;
val _ = pr "T1 ledger goal term (expect TWO OFCLASS premises):";
val _ = prtm goal_term;

(* step 2: pinned bridges *)
val bridges = classrel_bridges thy goal_term rules;
val _ = report_bridges "T1 pinned bridges (expect 2, each pinned to a different tfree)" bridges;

(* step 3: discharge, both bridge orders *)
val _ = run_case "T1.3 pinned, generated order" goal_term (discharge_tac ctxt rules bridges);
val _ = run_case "T1.3 pinned, reversed order" goal_term (discharge_tac ctxt rules (rev bridges));

(* step 4: CONTRAST — unpinned bridges, both orders *)
val ub = classrel_bridges_unpinned thy goal_term rules;
val _ = report_bridges "T1.4 unpinned bridges" ub;
val _ = run_case "T1.4 unpinned, generated order" goal_term (discharge_tac ctxt rules ub);
val _ = run_case "T1.4 unpinned, reversed order" goal_term (discharge_tac ctxt rules (rev ub));

(* ==== T1S (supplementary): make the wanted class COLLIDE across the two variables ====
   debt: 'a::comm_monoid_add, 'b::ab_semigroup_add, both conjuncts use +;
   cert at 'a::ab_semigroup_add, 'b::ab_semigroup_add — both rule premises demand
   ab_semigroup_add, so an unpinned bridge minted for one variable can resolve against
   the other variable's obligation (the D1 scenario). *)

val _ = pr "==== T1S: colliding wanted class (ab_semigroup_add needed at BOTH variables) ====";

fun t1s_statement Ta Tb =
  let
    val x = Free ("x", Ta); val y = Free ("y", Ta);
    val u = Free ("u", Tb); val v = Free ("v", Tb);
    val body = mk_conj (mk_eq Ta (mk_plus Ta x y) (mk_plus Ta y x))
                       (mk_eq Tb (mk_plus Tb u v) (mk_plus Tb v u));
  in fold_rev Logic.all [x, y, u, v] (mk_Trueprop body) end;

val s_debt = t1s_statement (TFree ("'a", S_cma)) (TFree ("'b", S_asa));
val s_cert_prop = t1s_statement (TFree ("'a", S_asa)) (TFree ("'b", S_asa));
val s_cert = prove_cert "T1S certificate" s_cert_prop
  (asm_full_simp_tac (fold Simplifier.add_simp [add_commute] ctxt) 1);
val s_rules = map (Thm.unconstrainT o Thm.varifyT_global) [s_cert];
val _ = pr "T1S rule:";
val _ = prts (hd s_rules);

val s_goal = ledger thy s_debt;
val _ = pr "T1S ledger goal term:";
val _ = prtm s_goal;

val s_b = classrel_bridges thy s_goal s_rules;
val _ = report_bridges "T1S pinned bridges (one is reflexive at 'b)" s_b;
val _ = run_case "T1S pinned, depth-1, generated order" s_goal (discharge_tac ctxt s_rules s_b);
val _ = run_case "T1S pinned, depth-1, reversed order" s_goal (discharge_tac ctxt s_rules (rev s_b));

val s_ub = classrel_bridges_unpinned thy s_goal s_rules;
val _ = report_bridges "T1S unpinned bridges" s_ub;
val _ = run_case "T1S unpinned, depth-1, generated order" s_goal (discharge_tac ctxt s_rules s_ub);
val _ = run_case "T1S unpinned, depth-1, reversed order" s_goal (discharge_tac ctxt s_rules (rev s_ub));

(* the two defects combined: unpinned bridges under the OLD unbounded tail *)
val _ = run_case "T1S unpinned, OLD tail, generated order" s_goal (old_discharge_tac ctxt s_rules s_ub);
val _ = run_case "T1S unpinned, OLD tail, reversed order" s_goal (old_discharge_tac ctxt s_rules (rev s_ub));

(* pinning alone under the OLD tail *)
val _ = run_case "T1S pinned, OLD tail, generated order" s_goal (old_discharge_tac ctxt s_rules s_b);
val _ = run_case "T1S pinned, OLD tail, reversed order" s_goal (old_discharge_tac ctxt s_rules (rev s_b));

val _ = pr "==== T1 done ====";
