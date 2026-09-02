(* t2.ML — T2: termination with a reflexive bridge; depth-1 vs the OLD unbounded tail *)

val _ = pr "==== T2: single-variable debt at 'a::ab_semigroup_add, cert at the SAME sort ====";

val debt_prop = comm_statement (TFree ("'a", S_asa));
val goal_term = ledger thy debt_prop;
val _ = pr "T2 ledger goal term:";
val _ = prtm goal_term;

val add_commute = Global_Theory.get_thm thy "add.commute";
val _ = pr "T2 certificate = add.commute:";
val _ = prts add_commute;
val rules = map (Thm.unconstrainT o Thm.varifyT_global) [add_commute];
val _ = pr "T2 rule:";
val _ = prts (hd rules);

val gen_bridges = classrel_bridges thy goal_term rules;
val _ = report_bridges "T2 generator output (expect the REFLEXIVE bridge, pinned)" gen_bridges;

val T_ledger =
  (case map_filter (try Logic.dest_of_class) (Logic.strip_imp_prems goal_term) of
     (T, _) :: _ => T
   | [] => raise Fail "T2: no OFCLASS premise in ledger goal");

val refl_bridge =
  (case gen_bridges of
     [b] => b
   | _ => raise Fail ("T2: expected exactly 1 generated bridge, got " ^
                      string_of_int (length gen_bridges)));

(* manufacture the "useful" bridge from T1's 'a-side: comm_monoid_add ==> ab_semigroup_add,
   pinned to this ledger variable *)
val useful_bridge = pin_bridge thy T_ledger (mk_bridge thy S_cma (hd S_asa));
val _ = pr "T2 manufactured useful bridge:";
val _ = prts useful_bridge;

(* 1. fixed depth-1 tail, both orders *)
val _ = run_case "T2.1 depth-1, [reflexive, useful]" goal_term
          (discharge_tac ctxt rules [refl_bridge, useful_bridge]);
val _ = run_case "T2.1 depth-1, [useful, reflexive]" goal_term
          (discharge_tac ctxt rules [useful_bridge, refl_bridge]);

(* 2. CONTRAST: OLD unbounded tail with [reflexive, useful] (and the other order) *)
val _ = run_case "T2.2 OLD tail, [reflexive, useful]" goal_term
          (old_discharge_tac ctxt rules [refl_bridge, useful_bridge]);
val _ = run_case "T2.2 OLD tail, [useful, reflexive]" goal_term
          (old_discharge_tac ctxt rules [useful_bridge, refl_bridge]);

(* ==== T2S (supplementary): the configuration where the OLD tail actually loops ====
   In T2 proper the residual OFCLASS subgoal is closed by assume_tac before any bridge is
   tried, so the reflexive bridge cannot loop there.  The divergence needs assume_tac to
   FAIL first: debt at 'a::comm_monoid_add, cert add.commute (ab_semigroup_add) — the T4
   configuration — with the bridge list [reflexive(asa=>asa), useful(cma=>asa)]. *)

val _ = pr "==== T2S: OLD tail on cma-debt with [reflexive, useful] ====";

val debt4 = comm_statement (TFree ("'a", S_cma));
val goal4 = ledger thy debt4;
val _ = pr "T2S ledger goal term:";
val _ = prtm goal4;

val T4v =
  (case map_filter (try Logic.dest_of_class) (Logic.strip_imp_prems goal4) of
     (T, _) :: _ => T
   | [] => raise Fail "T2S: no OFCLASS premise");

val refl4 = pin_bridge thy T4v (mk_bridge thy S_asa (hd S_asa));
val useful4 = pin_bridge thy T4v (mk_bridge thy S_cma (hd S_asa));
val _ = pr "T2S reflexive bridge:";
val _ = prts refl4;
val _ = pr "T2S useful bridge:";
val _ = prts useful4;

val _ = run_case "T2S OLD tail, [reflexive, useful]" goal4
          (old_discharge_tac ctxt rules [refl4, useful4]);
val _ = run_case "T2S OLD tail, [useful, reflexive]" goal4
          (old_discharge_tac ctxt rules [useful4, refl4]);
val _ = run_case "T2S depth-1, [reflexive, useful]" goal4
          (discharge_tac ctxt rules [refl4, useful4]);
val _ = run_case "T2S depth-1, [useful, reflexive]" goal4
          (discharge_tac ctxt rules [useful4, refl4]);

val _ = pr "==== T2 done ====";
