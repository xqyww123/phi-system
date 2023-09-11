signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers



(*dest_source: True for applying the inductive destruction on the source, False for on the target*)
fun meta_gen_Tyops_Commute (dest_source, rule, parse_hint) F_term
                           (_, name) hint0 ctxt0 (phi0 : phi_type) thy =
  let val Const (const, _) = head_of (HOLogic.dest_Trueprop (Thm.prop_of rule))
      fun extract_oprs_from_hint (C $ D $ r) =
           (case head_of C
              of Const(const', _) => if const = const' then [D,r] else []
               | _ => [])
        | extract_oprs_from_hint _ = []

      val ind_conv_I = default_ind_conv (
            fn ctxt => fn _ =>
                Phi_Conv.meta_alls_conv (fn ctxt => Conv.implies_concl_conv (
                  Phi_Reasoners.asm_rewrite true (
                      Expansion.equip ctxt addsimps (@{thm' \<phi>TA_ind_target_strip} :: #equations phi0))
                )) ctxt,
            fn ctxt => fn _ =>
                Phi_Conv.meta_alls_conv (fn ctxt => Conv.implies_concl_conv (
                  Phi_Reasoners.asm_rewrite true (
                      Expansion.equip ctxt addsimps (@{thm' \<phi>TA_ind_target_strip} :: #equations phi0))
                )) ctxt
            )
      val ind_conv_E = default_ind_conv (
            fn ctxt => fn _ =>
                Phi_Conv.meta_alls_conv (fn ctxt => Conv.implies_concl_conv (
                  Phi_Reasoners.asm_rewrite true (
                      Expansion.equip ctxt addsimps (@{thm' Action_Tag_def} :: #equations phi0))
                )) ctxt,
            fn ctxt => fn _ =>
                Phi_Conv.meta_alls_conv (fn ctxt => Conv.implies_concl_conv (
                  Phi_Reasoners.asm_rewrite true (
                      Expansion.equip ctxt addsimps (@{thm' Action_Tag_def} :: #equations phi0))
                )) ctxt
            )
   in ()
  end

end
