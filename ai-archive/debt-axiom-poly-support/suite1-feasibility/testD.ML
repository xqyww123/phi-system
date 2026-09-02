(* TEST GROUP D - Pattern.equiv matching *)
val thy = (Thy_Info.get_theory "Main" handle ERROR _ => Thy_Info.get_theory "HOL.Main");
val ctxt = Proof_Context.init_global thy;
val ctxt_s = Config.put show_sorts true ctxt;
fun pr s = writeln ("### " ^ s);
fun prtm t = writeln (Syntax.string_of_term ctxt_s t);
fun prb name b = pr (name ^ " = " ^ (if b then "true" else "false"));

(* ledger normal forms from group B *)
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

fun ledger_form thy prop =
  let
    val (strip, _, prop') = stripped_sorts thy prop;
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
  in Logic.list_implies (maps Logic.mk_of_sort constraints, prop') end;

(* HOLogic is not in scope at the raw ML toplevel; use internal names directly *)
val boolT = Type ("HOL.bool", []);
fun mk_Trueprop t = Const ("HOL.Trueprop", boolT --> propT) $ t;
fun mk_eq (t, u) =
  Const ("HOL.eq", Term.fastype_of t --> Term.fastype_of u --> boolT) $ t $ u;

fun plus T = Const ("Groups.plus_class.plus", T --> T --> T);
fun comm_prop T =
  let val x = Free ("x", T); val y = Free ("y", T);
  in Logic.all x (Logic.all y
       (mk_Trueprop (mk_eq (plus T $ x $ y, plus T $ y $ x)))) end;

val goal_term = ledger_form thy (comm_prop (TFree ("'a", ["Groups.comm_monoid_add"])));
val _ = pr "D goal_term (show_sorts):";
val _ = prtm goal_term;

val _ = pr "D1: renamed variant ('a -> 'zz)";
val renamed =
  Term.map_types (Term.map_atyps (fn TFree (_, S) => TFree ("'zz", S) | T => T)) goal_term;
val _ = prtm renamed;
val d1 = Pattern.equiv thy (Logic.varify_global goal_term, Logic.varify_global renamed);
val _ = prb "D1 Pattern.equiv (renamed variant)" d1;

val _ = pr "D2: non-variant control - vs ab_semigroup_add ledger form";
val goal_term2 = ledger_form thy (comm_prop (TFree ("'a", ["Groups.ab_semigroup_add"])));
val _ = prtm goal_term2;
val d2 = Pattern.equiv thy (Logic.varify_global goal_term, Logic.varify_global goal_term2);
val _ = prb "D2 Pattern.equiv (different sorts)" d2;

val _ = pr "D3: diagonal control - f x x vs f x y over distinct empty-sorted tfrees";
val aT0 = TFree ("'a", []);
val bT0 = TFree ("'b", []);
val diag =
  mk_Trueprop
    (Const ("f", aT0 --> aT0 --> boolT) $ Free ("x", aT0) $ Free ("y", aT0));
val offdiag =
  mk_Trueprop
    (Const ("f", aT0 --> bT0 --> boolT) $ Free ("x", aT0) $ Free ("y", bT0));
val _ = prtm diag;
val _ = prtm offdiag;
val d3 = Pattern.equiv thy (Logic.varify_global diag, Logic.varify_global offdiag);
val _ = prb "D3 Pattern.equiv (diagonal vs off-diagonal)" d3;
val d3a = Pattern.matches thy (Logic.varify_global offdiag, Logic.varify_global diag);
val _ = prb "D3a matches (offdiag pattern vs diag object, should be true)" d3a;
val d3b = Pattern.matches thy (Logic.varify_global diag, Logic.varify_global offdiag);
val _ = prb "D3b matches (diag pattern vs offdiag object, should be false)" d3b;

val _ = pr "GROUP D DONE";
