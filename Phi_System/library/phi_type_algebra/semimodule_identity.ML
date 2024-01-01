signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_identity_I : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val semimodule_identity_E : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun gen_MI is_intro (_, name) instruction ctxt0 (phi : phi_type) thy =
  let val parse_hint = parse_hint (
            fn (Const(\<^const_name>\<open>Semimodule_One\<^sub>I\<close>, _) $ F $ _ $ _ $ _ $ _ $ _ ) => F
             | (Const(\<^const_name>\<open>Semimodule_One\<^sub>E\<close>, _) $ F $ _ $ _ $ _ $ _ $ _ ) => F )
      val extract_oprs_from_hint = K []
      fun reasoning phi ctxt =
        default_reasoning false default_reasoning_configure (K (K NONE))
                          (exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))) phi ctxt
      val simp = K I

      val equip_expansion = equip_expansion_ss phi
      val eqs = #equations phi @ map_filter I (#type_equations phi)
      val ind_conv = default_ind_conv (
             fn _ => fn _ =>
                  Conv.rewr_conv @{thm \<phi>TA_common_rewr_imp2_noact} then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv,
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_common_rewr_imp2'} then_conv
                  Phi_Reasoners.asm_rewrite true (equip_expansion ctxt addsimps eqs) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                                    (conv_hol_imp_to_meta_if_has Conv.all_conv))

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      Guess_Scalar_One is_intro,
                                      (if is_intro then @{thm' \<phi>TA_MI\<^sub>I_rule} else @{thm' \<phi>TA_MI\<^sub>E_rule}),
                                      [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning)],
                                      K NONE, K I, simp)
                                    phi instruction ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m => fn ctxt =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE'
                                    (SOME (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                       (#2 instruction)))
                                    ([],[]) NONE [Morphism.thm m rule'] ctxt)
        |> note_properties_s false phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_identity_I = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_One\<^sub>I") (gen_MI true)
val semimodule_identity_E = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_One\<^sub>E") (gen_MI false)


end