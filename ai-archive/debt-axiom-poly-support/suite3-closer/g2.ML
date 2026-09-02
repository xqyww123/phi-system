(* g2.ML — G2: composite type over a debt variable (the hole that killed the bridge design) *)

val order_refl = Proof_Context.get_thm ctxt0 "order_refl";
val finite_UNIV = Proof_Context.get_thm ctxt0 "finite_UNIV";

(*G2a: obligation OFCLASS('a set, preorder_class), 'a::type*)
val _ = case_run "G2a (composite 'a set, class preorder)"
  (rp "!!x::'a set. x <= x") order_refl;

(*G2b: different constructor: obligation OFCLASS('a option, finite_class), 'a::finite*)
val _ = case_run "G2b (composite 'a option, class finite)"
  (rp "finite (UNIV :: (('a::finite) option) set)") finite_UNIV;

(*G2c: multi-argument constructor prod, different sorts on the two variables*)
val _ = case_run "G2c (composite 'a * 'b, 'a::finite, 'b::{finite,linorder})"
  (rp "finite (UNIV :: (('a::finite) * ('b::{finite,linorder})) set)") finite_UNIV;

val _ = writeln "G2 DONE";
