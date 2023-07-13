signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val is_functional : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property (x_term, FT_term, (phi:phi_type)) ctxt =
  let val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun mk_prop (x_ty, m_ty, x, T) = \<^Const>\<open>Is_Functional m_ty\<close> $ (\<^Const>\<open>\<phi>Type x_ty m_ty\<close> $ x $ T)
      val ants = make_forall_quantified_property_for_parameters_of_a_phi_type mk_prop FT_term
   in Seq.single (ants, HOLogic.Trueprop $ mk_prop (x_ty, model_ty, x_term, FT_term),
                  x_term, FT_term, phi, ctxt)
  end


fun gen_is_functional hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val unify_hint = hint_unify_by_type (
            fn _ (*Trueprop*) $ (\<^Const>\<open>Is_Functional _\<close> $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ T)) => T )

      val ind_conv = default_ind_conv (
            fn ctxt => fn phi =>
                Conv.rewr_conv @{thm' \<phi>TA_IsFunc_rewr},
            fn ctxt => fn phi =>
                Conv.rewr_conv @{thm' \<phi>TA_IsFunc_rewr} then_conv
                Conv.implies_concl_conv (PLPR_Syntax.premise_tag_conv (
                  Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)))))
      val reasoning = gen_abstract_constraint_guided_reasoning (K NONE) (K (K [])) (PLPR_reasoner (SOME 1))

      val rules = mk_rule_by_guess_or_hint ("Is_Functional", unify_hint, guess_property,
                                            @{thm' \<phi>TA_IsFunc_rule}, [], SOME ind_conv,
                                            K reasoning, K NONE, K I)
                                           phi0 hint0 ctxt0
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 90
                                              ([],[]) NONE [Morphism.thm m rule])
        |> Phi_Type_Algebra.note_properties phi0 [("Is_Functional", [rule])]
    | _ => raise Automation_Fail
  end

val is_functional = accept_one "Is_Functional" gen_is_functional

end
