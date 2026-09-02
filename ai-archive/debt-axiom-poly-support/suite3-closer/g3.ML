(* g3.ML — G3: ground type (the regression that killed the bridge design) *)

val add_0_right = Proof_Context.get_thm ctxt0 "add_0_right";
val less_imp_le = Proof_Context.get_thm ctxt0 "less_imp_le";

(*G3a: mono premise-free debt, polymorphic library cert*)
val _ = case_run "G3a (mono debt, poly cert add_0_right)"
  (rp "!!n::nat. n + 0 = n") add_0_right;

(*G3b: mono premised debt, polymorphic library cert less_imp_le (class preorder)*)
val _ = case_run "G3b (mono premised debt, poly cert less_imp_le)"
  (rp "!!n m::nat. n < m ==> n <= m") less_imp_le;

(*G3c: mono debt, mono cert (same premise-free prop proved at nat)*)
val cert_g3c = prove_cert "!!n::nat. n + 0 = n"
  (fn ctxt => resolve_tac ctxt [add_0_right] 1);
val _ = writeln ("cert_g3c: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_g3c));
val _ = case_run "G3c (mono debt, mono cert)"
  (rp "!!n::nat. n + 0 = n") cert_g3c;

val _ = writeln "G3 DONE";
