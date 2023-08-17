signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_zero : quiet -> hint list -> Phi_Type_Algebra.derive
val closed_semimodule_zero : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property closed (phi0 : phi_type) ctxt =
  let val (reversed_argtys', x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      fun err_parse () = raise Automation_Fail (fn () => let open Pretty in
                            [para "I can only the semimodule \<phi>-type giving its element \<phi>-type as \
                                  \its last parameter and the sclara as its second last paramter. \
                                  \However, the parameters of the given \<phi>-type does not seem to meet \
                                  \this requirement."]
                        end)
      val s_ty0 = case reversed_argtys'
                  of (\<^Type>\<open>fun T_x_ty \<^Type>\<open>set T_model_ty\<close>\<close> :: s_ty :: _) =>
                      if T_x_ty = x_ty0 andalso T_model_ty = model_ty0 then s_ty
                      else err_parse ()
                   | _ => err_parse ()

      val inst = (Phi_Help.lift_types_sort (Proof_Context.theory_of ctxt)
                                           [(s_ty0, \<^sort>\<open>zero\<close>), (model_ty0, \<^sort>\<open>share_one\<close>)]
                 handle TYPE _ => raise Automation_Fail (let open Pretty in fn () =>
                          [paragraph (text "Fail to lift the scalar of type " @
                                      [brk 1, Syntax.pretty_typ ctxt s_ty0, brk 1] @
                                      text "and the concrete algebra" @
                                      [brk 1, Syntax.pretty_typ ctxt model_ty0, brk 1] @
                                      text "onto sort \<open>zero\<close> and \<open>share_one\<close> respectively.")]
                          end))
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val s_ty = Term_Subst.instantiateT inst s_ty0
      val x_ty = Term_Subst.instantiateT inst x_ty0
      val model_ty = Term_Subst.instantiateT inst model_ty0

      val phi = instantiate_phi (inst',Vars.empty) phi0

      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term
   in Seq.single ([], \<^Const>\<open>Trueprop\<close> $ (
                          (if closed then \<^Const>\<open>Closed_Semimodule_Zero s_ty x_ty model_ty\<close>
                                     else \<^Const>\<open>Semimodule_Zero s_ty x_ty model_ty\<close>) $ F_term $ T_term),
                  NONE :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end

fun gen_M0 closed (der_id, name) hint0 (phi : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val parse_hint = parse_hint (fn (Const(\<^const_name>\<open>Semimodule_Identity\<close>, _) $ F1 $ _ ) => F1)
      val extract_oprs_from_hint = K []
      fun reasoning phi =
        default_reasoning false
          (default_reasoning_configure [])
          (K (K NONE))
          (exhaustive_PLPR_reasoner NONE)
      val simp = K I
      val ind_conv = default_ind_conv (
             fn _ => fn _ => Conv.rewr_conv @{thm \<phi>TA_M0_rewr},
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_M0_rewr} then_conv
                  Conv.arg_conv (Phi_Conv.may_action_tag_conv (
                    let val sctxt = Simps.equip ctxt addsimps (#equations phi @ #type_equations phi)
                     in Simplifier.rewrite sctxt
                    end)))
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint, guess_property closed,
                                      (if closed then @{thm' \<phi>TA_M0c_rule} else @{thm' \<phi>TA_M0_rule}),
                                      [(SOME ([0], ind_conv), reasoning)], K NONE, simp)
                                    phi hint0 ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_zero = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Zero") (gen_M0 false)
val closed_semimodule_zero = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Zero") (gen_M0 true)


end
