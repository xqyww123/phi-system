signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_distrib_zip : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property (phi0 : phi_type) ctxt =
  let val (s_ty, x_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi0 (\<^sort>\<open>type\<close>, \<^sort>\<open>share_nun_semimodule\<close>)
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term
      val Sdom = infer_the_default_scalar_domain ctxt (s_ty, model_ty)
   in Seq.single ([], \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Semimodule_LDistr_Homo\<^sub>Z s_ty x_ty model_ty\<close>
                          $ F_term $ T_term $ Sdom ),
                  NONE :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end


end