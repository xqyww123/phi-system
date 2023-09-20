signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_distrib_zip : quiet -> hint list -> Phi_Type_Algebra.derive
val semimodule_distrib_unzip : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun gen_MDz is_zip (_, name) hint0 ctxt0 (phi : phi_type) thy =
  let val parse_hint = parse_hint (
              fn (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, _) $ F1 $ T_term $ _ $ _ $ _) =>
                    F1 $ Term.dummy $ T_term
               | (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>U\<close>, _) $ F1 $ T_term $ _ $ _ $ _) =>
                    F1 $ Term.dummy $ T_term
               )
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, _) $ _ $ _ $ Ds $ Dx $ zi)
            = [Ds, Dx, zi]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>U\<close>, _) $ _ $ _ $ Ds $ Dx $ uz)
            = [Ds, Dx, uz]
        | extract_oprs_from_hint _ = []

      fun reasoning phi ctxt =
        default_reasoning false (default_reasoning_configure []) (K (K NONE))
                          (exhaustive_PLPR_reasoner NONE (K (chk_unfolded' ctxt phi))) phi ctxt
      val mode_infer = not (is_some hint0)

      fun simp (_, ctxt) thm =
        if mode_infer
        then Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                let val sctxt = ctxt
                    val simp = Simplifier.rewrite sctxt
                 in HOLogic.Trueprop_conv (
                    Conv.combination_conv (Conv.combination_conv (Conv.arg_conv simp) simp) simp)
                end
             ) ctxt) thm
        else thm

      val ind_conv = default_ind_conv (
             fn _ => fn _ => Conv.rewr_conv @{thm \<phi>TA_MD_rewr},
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_MD_rewr} then_conv
                  Conv.arg_conv (Conv.arg_conv (
                    let val sctxt = Expansion.equip ctxt addsimps (#equations phi @ map_filter I (#type_equations phi))
                     in Phi_Reasoners.asm_rewrite false sctxt
                    end)))

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      Guess_Zip_of_Semimodule is_zip, (if is_zip then @{thm' \<phi>TA_MD\<^sub>Z_rule} else @{thm' \<phi>TA_MD\<^sub>U_rule}),
                                      [(K (SOME (if is_zip then [0,2,~1,~1,~1] else [0,2,~1,~1])), ind_conv, reasoning)],
                                      K NONE, simp)
                                    phi hint0 ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties_s phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_distrib_zip = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_SDistr_Homo\<^sub>Z") (gen_MDz true)
val semimodule_distrib_unzip = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_SDistr_Homo\<^sub>U") (gen_MDz false)

end