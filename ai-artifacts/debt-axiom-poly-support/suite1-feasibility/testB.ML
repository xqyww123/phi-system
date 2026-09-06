(* TEST GROUP B - end-to-end discharge simulation *)
val thy = (Thy_Info.get_theory "Main" handle ERROR _ => Thy_Info.get_theory "HOL.Main");
val ctxt = Proof_Context.init_global thy;
val ctxt_s = Config.put show_sorts true ctxt;
fun pr s = writeln ("### " ^ s);
fun prt th = writeln (Thm.string_of_thm ctxt th);
fun prts th = writeln (Thm.string_of_thm ctxt_s th);
fun prtm t = writeln (Syntax.string_of_term ctxt_s t);
fun prb name b = pr (name ^ " = " ^ (if b then "true" else "false"));

(* HOLogic is not in scope at the raw ML toplevel; use internal names directly *)
val boolT = Type ("HOL.bool", []);
fun mk_Trueprop t = Const ("HOL.Trueprop", boolT --> propT) $ t;
fun mk_eq (t, u) =
  Const ("HOL.eq", Term.fastype_of t --> Term.fastype_of u --> boolT) $ t $ u;

val _ = pr "B1: debt proposition at 'a::comm_monoid_add";
val aT_sorted = TFree ("'a", ["Groups.comm_monoid_add"]);
fun plus T = Const ("Groups.plus_class.plus", T --> T --> T);
val x = Free ("x", aT_sorted); val y = Free ("y", aT_sorted);
val eq = mk_Trueprop (mk_eq (plus aT_sorted $ x $ y, plus aT_sorted $ y $ x));
val prop = Logic.all x (Logic.all y eq);
val _ = prtm prop;

val _ = pr "B2: stripped_sorts ledger normal form";
(* copied verbatim from Debt_Axiom.ML lines 37-46 *)
fun stripped_sorts thy t =
  let
    val tfrees = build_rev (Term.add_tfrees t);
    val tfrees' = map (fn a => (a, [])) (Name.variant_list [] (map #1 tfrees));
    val recover =
      map2 (fn (a', S') => fn (a, S) => (((a', 0), S'), Thm.global_ctyp_of thy (TVar ((a, 0), S))))
        tfrees' tfrees;
    val strip = map (apply2 TFree) (tfrees ~~ tfrees');
    val t' = Term.map_types (Term.map_atyps (perhaps (AList.lookup (op =) strip))) t;
  in (strip, recover, t') end;

val (strip, recover, prop') = stripped_sorts thy prop;
val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
val goal_term = Logic.list_implies (maps Logic.mk_of_sort constraints, prop');
val _ = pr "B2 goal_term (show_sorts):";
val _ = prtm goal_term;

val _ = pr "B3: certificate add.commute";
val cert =
  (Global_Theory.get_thm thy "add.commute"
   handle ERROR _ => Global_Theory.get_thm thy "Groups.ab_semigroup_add_class.add_commute");
val _ = pr "B3 cert (show_sorts):";
val _ = prts cert;

val _ = pr "B4: rule = unconstrainT (varifyT_global cert)";
val rule = Thm.unconstrainT (Thm.varifyT_global cert);
val _ = pr "B4 rule (show_sorts):";
val _ = prts rule;

val _ = pr "B5: bridge";
val bridge = Thm.unconstrainT (Thm.of_class
  (Thm.global_ctyp_of thy (TVar (("'x",0), ["Groups.comm_monoid_add"])),
   "Groups.ab_semigroup_add"));
val _ = pr "B5 bridge (show_sorts):";
val _ = prts bridge;

val _ = pr "B6: the discharge";
val th = Goal.prove_internal ctxt [] (Thm.global_cterm_of thy goal_term)
  (fn _ => HEADGOAL (resolve_tac ctxt [rule])
           THEN ALLGOALS (REPEAT_ALL_NEW (assume_tac ctxt ORELSE' resolve_tac ctxt [bridge])));
val _ = pr "B6 proved theorem (show_sorts):";
val _ = prts th;
val exact = Thm.full_prop_of th aconv goal_term;
val _ = prb "B6 exact" exact;

val _ = pr "B7: negative control - no bridge";
val _ =
  (let val th_nb = Goal.prove_internal ctxt [] (Thm.global_cterm_of thy goal_term)
         (fn _ => HEADGOAL (resolve_tac ctxt [rule]) THEN ALLGOALS (assume_tac ctxt))
   in pr "B7 UNEXPECTED SUCCESS:"; prts th_nb end)
  handle ERROR msg => pr ("B7 raised ERROR: " ^ msg)
       | THM (msg, i, _) => pr ("B7 raised THM: \"" ^ msg ^ "\" (index " ^ string_of_int i ^ ")");

val _ = pr "B8: subset control - debt at ab_semigroup_add itself, no bridge needed";
val aT2 = TFree ("'a", ["Groups.ab_semigroup_add"]);
val x2 = Free ("x", aT2); val y2 = Free ("y", aT2);
val eq2 = mk_Trueprop (mk_eq (plus aT2 $ x2 $ y2, plus aT2 $ y2 $ x2));
val prop2 = Logic.all x2 (Logic.all y2 eq2);
val (strip2, recover2, prop2') = stripped_sorts thy prop2;
val constraints2 = map (fn (TFree (_, S), T) => (T, S)) strip2;
val goal_term2 = Logic.list_implies (maps Logic.mk_of_sort constraints2, prop2');
val _ = pr "B8 goal_term2 (show_sorts):";
val _ = prtm goal_term2;
val th2 = Goal.prove_internal ctxt [] (Thm.global_cterm_of thy goal_term2)
  (fn _ => HEADGOAL (resolve_tac ctxt [rule]) THEN ALLGOALS (assume_tac ctxt));
val _ = pr "B8 proved theorem (show_sorts):";
val _ = prts th2;
val exact2 = Thm.full_prop_of th2 aconv goal_term2;
val _ = prb "B8 exact2" exact2;

val _ = pr "GROUP B DONE";
