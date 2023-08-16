signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_scalar : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property (phi : phi_type) ctxt =
  let val (reversed_argtys', x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun err_parse () = raise Automation_Fail (fn () => let open Pretty in
                            [para "I can only the semimodule \<phi>-type giving its element \<phi>-type as \
                                  \its last parameter and the sclara as its second last paramter. \
                                  \However, the parameters of the given \<phi>-type does not seem to meet \
                                  \this requirement."]
                        end)
      val (s_ty, reversed_argtys) =
            case reversed_argtys'
              of (\<^Type>\<open>fun T_x_ty \<^Type>\<open>set T_model_ty\<close>\<close> :: s_ty :: reversed_argtys) =>
                  if T_x_ty = x_ty andalso T_model_ty = model_ty then (s_ty, reversed_argtys)
                  else err_parse ()
               | _ => err_parse ()

      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term
      val g_Sdom = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>default_domain_of_scalar s_ty model_ty\<close>
                                        $ \<^Const>\<open>Pure.type s_ty\<close>
                                        $ \<^Const>\<open>Pure.type model_ty\<close>
                                        $ Var(("p",0), s_ty --> HOLogic.boolT))
      val Sdom = Goal.init (Thm.cterm_of ctxt g_Sdom)
              |> Phi_Reasoner.reason NONE true ctxt
              |> (fn SOME ret => (case Thm.prop_of ret
                                    of _ (*Pure.prop*) $ (_ (*Trueprop*) $ (_ (*default_domain_of_scalar*) $ _ $ _ $ S)) => S
                                     | _ => error "BUG")
                   | _ => Abs("_", s_ty, \<^Const>\<open>True\<close>))
   in Seq.single ([], \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Semimodule_Scalar_Assoc s_ty x_ty model_ty\<close>
                                            $ F_term $ T_term $ Sdom),
                  NONE :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end

fun gen_MS (der_id, name) hint0 (phi : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val parse_hint = parse_hint (
              fn (Const(\<^const_name>\<open>Semimodule_Scalar_Assoc\<close>, _) $ F1 $ _ $ _) => F1)
      val extract_oprs_from_hint = K []
      fun reasoning phi =
        default_reasoning false
          (default_reasoning_configure [])
          (K (K NONE))
          (exhaustive_PLPR_reasoner NONE)
      val simp = K I
      val ind_conv = default_ind_conv (
             fn _ => fn _ => Conv.rewr_conv @{thm \<phi>TA_MS_rewr},
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_MS_rewr} then_conv
                  Conv.arg_conv (Conv.arg_conv (Phi_Conv.may_action_tag_conv (
                    let val sctxt = Simps.equip ctxt addsimps (#equations phi @ #type_equations phi)
                     in Phi_Syntax.transformation_conv
                            (Simplifier.rewrite sctxt)
                            (Simplifier.rewrite sctxt)
                            (Conv.all_conv)
                    end))))
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property, @{thm' \<phi>TA_MS_rule},
                                      [(SOME ([0,2,~1,~1], ind_conv), reasoning),
                                       (SOME ([0,2,~1], ind_conv), reasoning)], K NONE, simp)
                                    phi hint0 ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_scalar = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Scalar_Assoc") gen_MS

end