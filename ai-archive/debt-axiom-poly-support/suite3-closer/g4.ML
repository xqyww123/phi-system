(* g4.ML — G4: composite over ground: obligation OFCLASS(nat set, preorder_class) *)

val order_refl = Proof_Context.get_thm ctxt0 "order_refl";

val _ = case_run "G4 (composite over ground: nat set, class preorder)"
  (rp "!!x::nat set. x <= x") order_refl;

val _ = writeln "G4 DONE";
