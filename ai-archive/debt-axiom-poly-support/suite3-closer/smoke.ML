(* smoke.ML — probe API points, fact names, instances, and parsing before the real matrix *)

val natT = Type ("Nat.nat", []);
fun setT T = Type ("Set.set", [T]);
fun prodT (A, B) = Type ("Product_Type.prod", [A, B]);

fun probe_sort name T S =
  writeln ("of_sort " ^ name ^ ": " ^ Bool.toString (Sign.of_sort thy0 (T, S)));

val _ = probe_sort "('a::equal * nat) :: equal"
          (prodT (TFree ("'a", ["HOL.equal"]), natT)) ["HOL.equal"];
val _ = probe_sort "('a::type) set :: preorder"
          (setT (TFree ("'a", ["HOL.type"]))) ["Orderings.preorder"];
val _ = probe_sort "('a::finite) option :: finite"
          (Type ("Option.option", [TFree ("'a", ["Finite_Set.finite"])])) ["Finite_Set.finite"];
val _ = probe_sort "nat set :: preorder" (setT natT) ["Orderings.preorder"];
val _ = probe_sort "('a::{finite,linorder}) :: finite"
          (TFree ("'a", ["Finite_Set.finite", "Orderings.linorder"])) ["Finite_Set.finite"];

(*fact lookups*)
fun probe_fact s =
  let val th = Proof_Context.get_thm ctxt0 s
  in writeln ("fact " ^ s ^ ": " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of th)) end
  handle ERROR msg => writeln ("fact " ^ s ^ " LOOKUP FAILED: " ^ msg);

val _ = List.app probe_fact
  ["add.commute", "mult.commute", "order_refl", "less_imp_le", "add_0_right",
   "finite_UNIV", "equal_eq", "conjI", "refl"];

(*parsing with sort annotations*)
val p1 = rp "!!x y::'a::comm_monoid_add. x + y = y + x";
val _ = writeln ("parsed p1: " ^ Syntax.string_of_term ctxt0 p1);
val _ = writeln ("ledger p1: " ^ Syntax.string_of_term ctxt0 (ledger_form thy0 p1));

val p2 = rp "!!x::'a set. x <= x";
val _ = writeln ("parsed p2: " ^ Syntax.string_of_term ctxt0 p2);
val _ = writeln ("ledger p2: " ^ Syntax.string_of_term ctxt0 (ledger_form thy0 p2));

val p3 = rp "finite (UNIV :: (('a::finite) option) set)";
val _ = writeln ("parsed p3: " ^ Syntax.string_of_term ctxt0 p3);

val p4 = rp "!!x y::('a::equal) * nat. equal_class.equal x y = (x = y)";
val _ = writeln ("parsed p4: " ^ Syntax.string_of_term ctxt0 p4);

(*what does prep_cert produce on a library thm?*)
val u = prep_cert (Proof_Context.get_thm ctxt0 "add.commute");
val _ = writeln ("prep_cert add.commute: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of u));

val u2 = prep_cert (Proof_Context.get_thm ctxt0 "less_imp_le");
val _ = writeln ("prep_cert less_imp_le: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of u2));

(*of_class + unconstrainT on a ground type*)
val g1 = Thm.of_class (Thm.global_ctyp_of thy0 natT, "Groups.monoid_add");
val _ = writeln ("of_class nat monoid_add: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of g1));
val g1u = Thm.unconstrainT g1;
val _ = writeln ("unconstrainT of that: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of g1u));

(*of_class + unconstrainT on a composite over a sorted TVar*)
val g2 = Thm.of_class
  (Thm.global_ctyp_of thy0 (setT (TVar (("'a", 0), ["HOL.type"]))), "Orderings.preorder");
val _ = writeln ("of_class ?'a::type set preorder: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of g2));
val g2u = Thm.unconstrainT g2;
val _ = writeln ("unconstrainT of that: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of g2u));

val _ = writeln "SMOKE OK";
