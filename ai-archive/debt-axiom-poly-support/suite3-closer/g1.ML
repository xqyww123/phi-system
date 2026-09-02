(* g1.ML — G1: bare debt type variable (regression guard for the old ground) *)

val add_commute = Proof_Context.get_thm ctxt0 "add.commute";
val mult_commute = Proof_Context.get_thm ctxt0 "mult.commute";
val conjI = Proof_Context.get_thm ctxt0 "conjI";
val refl = Proof_Context.get_thm ctxt0 "refl";

(*G1a: poly debt at comm_monoid_add, cert add.commute at ab_semigroup_add (weaker)*)
val _ = case_run "G1a (bare var, debt sort stronger than cert's)"
  (rp "!!x y::'a::comm_monoid_add. x + y = y + x") add_commute;

(*G1b: debt sort literally equal to cert sort*)
val _ = case_run "G1b (bare var, debt sort = cert sort)"
  (rp "!!x y::'a::ab_semigroup_add. x + y = y + x") add_commute;

(*G1c: two variables, different sorts (earlier T1 shape)*)
val cert_g1c = prove_cert
  "!!(x::'a::ab_semigroup_add) (y::'a) (p::'b::ab_semigroup_mult) (q::'b). x + y = y + x \\<and> p * q = q * p"
  (fn ctxt => (resolve_tac ctxt [conjI] THEN_ALL_NEW resolve_tac ctxt [add_commute, mult_commute]) 1);
val _ = writeln ("cert_g1c: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_g1c));
val _ = case_run "G1c (two vars, different sorts)"
  (rp "!!(x::'a::comm_monoid_add) (y::'a) (p::'b::comm_monoid_mult) (q::'b). x + y = y + x \\<and> p * q = q * p")
  cert_g1c;

(*G1d: class chain: debt at comm_monoid_add, cert at plus (several subclass steps up)*)
val cert_g1d = prove_cert "!!x y::'a::plus. x + y = x + y"
  (fn ctxt => resolve_tac ctxt [refl] 1);
val _ = writeln ("cert_g1d: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_g1d));
val _ = case_run "G1d (chain: debt comm_monoid_add, cert plus)"
  (rp "!!x y::'a::comm_monoid_add. x + y = x + y") cert_g1d;

val _ = writeln "G1 DONE";
