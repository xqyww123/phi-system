(* extra.ML — additional P3 hunt cases beyond the first sweep *)

val equal_eq = Proof_Context.get_thm ctxt0 "equal_eq";
val finite_UNIV = Proof_Context.get_thm ctxt0 "finite_UNIV";
val refl = Proof_Context.get_thm ctxt0 "refl";

(*instance probe: ('a::equal) list :: equal*)
val _ = writeln ("of_sort ('a::equal) list :: equal: " ^
  Bool.toString (Sign.of_sort thy0
    (Type ("List.list", [TFree ("'a", ["HOL.equal"])]), ["HOL.equal"])));

(*E1: the list constructor originally suggested for G2b: OFCLASS('a list, equal_class)*)
val _ = case_run "E1 (composite 'a list, class equal)"
  (rp "!!x y::('a::equal) list. equal_class.equal x y = (x = y)") equal_eq;

(*E2: NESTED composite: OFCLASS('a option option, finite_class)*)
val _ = case_run "E2 (nested composite 'a option option, class finite)"
  (rp "finite (UNIV :: (('a::finite) option option) set)") finite_UNIV;

(*E3: poly AND premised debt (a combination the matrix does not list):
  residual OFCLASS subgoal carries a non-OFCLASS hypothesis with loose Bounds
  next to the real OFCLASS hypothesis*)
val cert_e3 = prove_cert "!!x y::'a::monoid_add. x = y ==> x + 0 = y"
  (fn ctxt => asm_full_simp_tac ctxt 1);
val _ = writeln ("cert_e3: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_e3));
val _ = case_run "E3 (poly + premised: debt comm_monoid_add, cert monoid_add)"
  (rp "!!x y::'a::comm_monoid_add. x = y ==> x + 0 = y") cert_e3;

(*E4: top-sort-only poly debt: obligation class is HOL.type itself*)
val _ = case_run "E4 (bare var at sort {type}, cert refl)"
  (rp "!!x::'a. x = x") refl;

val _ = writeln "EXTRA DONE";
