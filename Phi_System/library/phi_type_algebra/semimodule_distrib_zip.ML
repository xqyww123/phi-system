signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_distrib_zip : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val semimodule_distrib_unzip : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun gen_MDz is_zip (_, name) instruction ctxt0 (phi : phi_type) thy =
  let val parse_hint = parse_hint (
              fn (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, _) $ F1 $ _ $ _ $ _) =>
                    F1 $ Term.dummy
               | (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>S\<close>, _) $ F1 $ _ $ _ $ _) =>
                    F1 $ Term.dummy
               )
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, _) $ _ $ Ds $ Dx $ zi)
            = [Ds, Dx, zi]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Semimodule_SDistr_Homo\<^sub>S\<close>, _) $ _ $ Ds $ Dx $ uz)
            = [Ds, Dx, uz]
        | extract_oprs_from_hint _ = []

      fun reasoning phi ctxt =
        default_reasoning false default_reasoning_configure (K (K NONE))
            (if is_zip
             then exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))
             else exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__\<A>_simp_NToA}
                      (K (chk_unfolded [] ctxt phi))) phi ctxt
      val mode_infer = not (is_some (#1 instruction))

      val simp = if is_some (#1 instruction) then K I
                 else simplifier_by_cong (if is_zip then @{thms' \<phi>TA_MD\<^sub>Z_cong}
                                                    else @{thms' \<phi>TA_MD\<^sub>U_cong})

      val equip_expansion = equip_expansion_ss phi
      val ind_conv = default_ind_conv (
             fn ctxt => fn _ =>
                  Conv.rewr_conv (if is_zip then @{thm' \<phi>TA_MD\<^sub>Z_rewr_IH}
                                            else @{thm' \<phi>TA_MD\<^sub>U_rewr_IH}),
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_common_rewr_imp2'} then_conv
                  Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                                    (conv_hol_imp_to_meta_if_has Conv.all_conv))

      val pre_simp = default_pre_simplifier (Phi_Conv.meta_alls_conv (fn ctxt => fn ctm =>
            (Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.rewr_conv (if is_zip then @{thm' \<phi>TA_MD\<^sub>Z_rewr_pre}
                                      else @{thm' \<phi>TA_MD\<^sub>U_rewr_pre})) ctm) o snd)

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      Guess_Zip_of_Semimodule is_zip, (if is_zip then @{thm' \<phi>TA_MD\<^sub>Z_rule} else @{thm' \<phi>TA_MD\<^sub>U_rule}),
                                      [(SOME (if is_zip
                                              then default_ind_inst (fn [_,_,_,r,z] => [SOME r, NONE, SOME z])
                                              else default_ind_inst (fn [_,_,r,z] => [SOME r, NONE, SOME z])),
                                        ind_conv, reasoning)],
                                      K NONE, pre_simp, simp)
                                    phi instruction ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE'
                                    (SOME (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                       (#2 instruction)))
                                    ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties_s phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_distrib_zip = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_SDistr_Homo\<^sub>Z") (gen_MDz true)
val semimodule_distrib_unzip = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_SDistr_Homo\<^sub>S") (gen_MDz false)

end