(* TEST GROUP C - declaration chain fix *)
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

(* debt proposition, as in group B *)
val aT_sorted = TFree ("'a", ["Groups.comm_monoid_add"]);
fun plus T = Const ("Groups.plus_class.plus", T --> T --> T);
val x = Free ("x", aT_sorted); val y = Free ("y", aT_sorted);
val eq = mk_Trueprop (mk_eq (plus aT_sorted $ x $ y, plus aT_sorted $ y $ x));
val prop = Logic.all x (Logic.all y eq);

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

val axm_term = Logic.list_implies (maps Logic.mk_of_sort constraints, prop');
val axm' = Skip_Proof.make_thm thy axm_term;
val of_sorts = maps (fn (T as TFree (_, S), _) => Thm.of_sort (Thm.ctyp_of ctxt T, S)) strip;
val _ = pr "C0 axm' (the oracle's verbatim thm, show_sorts):";
val _ = prts axm';

val _ = pr "C1: BEFORE-state - unfixed recovery chain";
val _ =
  (let val res_before =
         axm'
         |> Thm.instantiate (TVars.make recover, Vars.empty)
         |> Thm.unvarify_global thy
         |> fold Thm.elim_implies of_sorts
   in pr "C1 UNEXPECTED SUCCESS:"; prts res_before end)
  handle THM (msg, i, _) => pr ("C1 raised THM: \"" ^ msg ^ "\" (index " ^ string_of_int i ^ ")")
       | TERM (msg, _) => pr ("C1 raised TERM: \"" ^ msg ^ "\"")
       | TYPE (msg, _, _) => pr ("C1 raised TYPE: \"" ^ msg ^ "\"")
       | ERROR msg => pr ("C1 raised ERROR: " ^ msg);

val _ = pr "C2: AFTER-state - fixed chain with varifyT_global first";
val result =
  axm'
  |> Thm.varifyT_global
  |> Thm.instantiate (TVars.make recover, Vars.empty)
  |> Thm.unvarify_global thy
  |> fold Thm.elim_implies of_sorts;
val _ = pr "C2 result (show_sorts):";
val _ = prts result;
val _ = prb "C2 (Thm.full_prop_of result aconv prop)" (Thm.full_prop_of result aconv prop);

val _ = pr "C3: mono identity - 0 = 0 at nat";
val natT = Type ("Nat.nat", []);
val zero = Const ("Groups.zero_class.zero", natT);
val prop_m = mk_Trueprop (mk_eq (zero, zero));
val (strip_m, recover_m, prop_m') = stripped_sorts thy prop_m;
val constraints_m = map (fn (TFree (_, S), T) => (T, S)) strip_m;
val axm_term_m = Logic.list_implies (maps Logic.mk_of_sort constraints_m, prop_m');
val axm_m = Skip_Proof.make_thm thy axm_term_m;
val of_sorts_m = maps (fn (T as TFree (_, S), _) => Thm.of_sort (Thm.ctyp_of ctxt T, S)) strip_m;
val _ = pr ("C3 strip/recover/constraints sizes: "
  ^ string_of_int (length strip_m) ^ "/" ^ string_of_int (length recover_m)
  ^ "/" ^ string_of_int (length constraints_m));

val res_m_before =
  axm_m
  |> Thm.instantiate (TVars.make recover_m, Vars.empty)
  |> Thm.unvarify_global thy
  |> fold Thm.elim_implies of_sorts_m;
val _ = pr "C3 mono BEFORE-chain result (show_sorts):";
val _ = prts res_m_before;
val _ = pr ("C3 mono BEFORE maxidx = " ^ string_of_int (Thm.maxidx_of res_m_before));

val res_m_after =
  axm_m
  |> Thm.varifyT_global
  |> Thm.instantiate (TVars.make recover_m, Vars.empty)
  |> Thm.unvarify_global thy
  |> fold Thm.elim_implies of_sorts_m;
val _ = pr "C3 mono AFTER-chain result (show_sorts):";
val _ = prts res_m_after;
val _ = pr ("C3 mono AFTER maxidx = " ^ string_of_int (Thm.maxidx_of res_m_after));
val _ = prb "C3 mono props identical"
  (Thm.full_prop_of res_m_before aconv Thm.full_prop_of res_m_after);

val _ = pr "GROUP C DONE";
