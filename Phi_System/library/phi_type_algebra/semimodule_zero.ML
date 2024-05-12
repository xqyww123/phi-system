signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_zero : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val closed_semimodule_zero : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun gen_M0 closed (der_id, name) instruction (phi : phi_type) thy =
  let val parse_hint = parse_hint (
          fn (Const(\<^const_name>\<open>Semimodule_Zero\<close>, _) $ F1 $ _ ) => F1
           | (Const(\<^const_name>\<open>Closed_Semimodule_Zero\<close>, _) $ F1 $ _ ) => F1)
      val extract_oprs_from_hint = K []
      fun reasoning phi ctxt =
        default_reasoning false default_reasoning_configure (K (K NONE))
                          (exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))) phi ctxt
      val simp = K I

      val equip_expansion = equip_expansion_ss phi
      (*val eqs = #equations phi @ map_filter I (#type_equations phi) *)
      val ind_conv = default_ind_conv (
             fn _ => fn _ =>
                  Conv.rewr_conv (if closed then @{thm' \<phi>TA_M0c_rewr_IH}
                                            else @{thm' \<phi>TA_M0_rewr_IH} ) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv,
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_common_rewr_imp1_noact} then_conv
                  Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv)

      val pre_simp = default_pre_simplifier (Phi_Conv.meta_alls_conv (fn ctxt => fn ctm =>
            (Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_rev}) ctm) o snd)

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint, Guess_Scalar_Zero closed,
                                      (if closed then @{thm' \<phi>TA_M0c_rule} else @{thm' \<phi>TA_M0_rule}),
                                      [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning)],
                                      K NONE, pre_simp, simp)
                                    phi instruction thy
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Local_Theory.declaration {syntax=false, pervasive=false, pos= #3 instruction} (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE'
                                    (SOME (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                       (#2 instruction)))
                                    ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties_s false phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_zero = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Zero") (gen_M0 false)
val closed_semimodule_zero = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Closed_Semimodule_Zero") (gen_M0 true)


end
