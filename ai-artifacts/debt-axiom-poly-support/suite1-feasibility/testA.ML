(* TEST GROUP A - bridging rule construction *)
val thy = (Thy_Info.get_theory "Main" handle ERROR _ => Thy_Info.get_theory "HOL.Main");
val ctxt = Proof_Context.init_global thy;
val ctxt_s = Config.put show_sorts true ctxt;
fun pr s = writeln ("### " ^ s);
fun prt th = writeln (Thm.string_of_thm ctxt th);
fun prts th = writeln (Thm.string_of_thm ctxt_s th);
fun prtm t = writeln (Syntax.string_of_term ctxt_s t);

val _ = pr "A1: of_class from sort [comm_monoid_add] to class ab_semigroup_add";
val cT = Thm.global_ctyp_of thy (TVar (("'x",0), ["Groups.comm_monoid_add"]));
val b0 = Thm.of_class (cT, "Groups.ab_semigroup_add");
val _ = pr "A1 b0 (plain):";
val _ = prt b0;
val _ = pr "A1 b0 (show_sorts):";
val _ = prts b0;

val _ = pr "A2: unconstrainT b0";
val b = Thm.unconstrainT b0;
val _ = pr "A2 b (plain):";
val _ = prt b;
val _ = pr "A2 b (show_sorts):";
val _ = prts b;
val _ = pr "A2 Thm.prop_of b (show_sorts):";
val _ = prtm (Thm.prop_of b);

val _ = pr "A3: negative - of_class with class not derivable from sort [Groups.plus]";
val cT2 = Thm.global_ctyp_of thy (TVar (("'x",0), ["Groups.plus"]));
val _ =
  (let val bad = Thm.of_class (cT2, "Groups.comm_monoid_add")
   in pr "A3 UNEXPECTED SUCCESS:"; prts bad end)
  handle THM (msg, i, _) => pr ("A3 raised THM: \"" ^ msg ^ "\" (index " ^ string_of_int i ^ ")")
       | ERROR msg => pr ("A3 raised ERROR: " ^ msg);

val _ = pr "GROUP A DONE";
