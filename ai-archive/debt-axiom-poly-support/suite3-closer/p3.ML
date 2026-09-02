(* p3.ML — P3: hunt beyond the matrix *)

val add_commute = Proof_Context.get_thm ctxt0 "add.commute";
val finite_UNIV = Proof_Context.get_thm ctxt0 "finite_UNIV";
val conjI = Proof_Context.get_thm ctxt0 "conjI";
val refl = Proof_Context.get_thm ctxt0 "refl";

(*P3-1: obligation under a FUNCTION type: OFCLASS('a => 'b, finite_class)*)
val _ = case_run "P3-1 (function type 'a => 'b, class finite)"
  (rp "finite (UNIV :: (('a::finite) => ('b::finite)) set)") finite_UNIV;

(*P3-2: multiple classes on a composite argument: OFCLASS('a option, finite) with
  'a::{finite,linorder} — sort recovery must collect BOTH hyps, and the rebuilt rule's
  premises (one per class) must all close by assumption*)
val _ = case_run "P3-2 ('a::{finite,linorder} option, class finite)"
  (rp "finite (UNIV :: (('a::{finite,linorder}) option) set)") finite_UNIV;

(*P3-3: a certificate that ITSELF already has OFCLASS premises before unconstrainT
  (prep_cert applied to an already-unconstrained thm must be harmless)*)
val cert_p3 = prep_cert add_commute;
val _ = writeln ("cert_p3 (already unconstrained): " ^
                 Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_p3));
val _ = case_run "P3-3 (cert already carries OFCLASS premise)"
  (rp "!!x y::'a::comm_monoid_add. x + y = y + x") cert_p3;

(*P3-4: duplicate obligations: two cert type variables, both instantiated to the SAME
  debt variable -> the same OFCLASS subgoal appears twice*)
val cert_p4 = prove_cert
  "!!(x::'c::ab_semigroup_add) (y::'c) (u::'d::ab_semigroup_add) (v::'d). x + y = y + x \\<and> u + v = v + u"
  (fn ctxt => (resolve_tac ctxt [conjI] THEN_ALL_NEW resolve_tac ctxt [add_commute]) 1);
val _ = writeln ("cert_p4: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_p4));
val _ = case_run "P3-4 (duplicate obligations on one debt var)"
  (rp "!!(x::'a::ab_semigroup_add) (y::'a). x + y = y + x \\<and> x + y = y + x")
  cert_p4;

(*P3-5: obligation type containing the SAME variable twice: OFCLASS('a * 'a, finite)*)
val _ = case_run "P3-5 (same var twice: 'a * 'a, class finite)"
  (rp "finite (UNIV :: (('a::finite) * 'a) set)") finite_UNIV;

(*P3-6: cert type variable NOT occurring in the conclusion: after head resolution the
  obligation's type is an uninstantiated TVar; the closer must fail CLEANLY (such a cert
  does not certify the debt anyway)*)
val cert_p6 = prove_cert "finite (UNIV :: ('b::finite) set) ==> (0::nat) = 0"
  (fn ctxt => resolve_tac ctxt [refl] 1);
val _ = writeln ("cert_p6: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_p6));
val _ = case_run "P3-6 (cert TVar not in conclusion -> TVar obligation)"
  (rp "(0::nat) = 0") cert_p6;

(*P3-7: two DIFFERENT composite obligations over the same debt variable in one discharge*)
val cert_p7 = prove_cert
  "finite (UNIV :: (('c::finite) option) set) \\<and> finite (UNIV :: ('c set) set)"
  (fn ctxt => (resolve_tac ctxt [conjI] THEN_ALL_NEW resolve_tac ctxt [finite_UNIV]) 1);
val _ = writeln ("cert_p7: " ^ Syntax.string_of_term ctxt0 (Thm.full_prop_of cert_p7));
val _ = case_run "P3-7 (two composite obligations, same var: 'a option and 'a set)"
  (rp "finite (UNIV :: (('a::finite) option) set) \\<and> finite (UNIV :: ('a set) set)")
  cert_p7;

val _ = writeln "P3 DONE";
