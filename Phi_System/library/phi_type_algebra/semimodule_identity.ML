signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_identity : quiet * Position.T -> deriving_instruction list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun gen_MI (_, name) instruction ctxt0 (phi : phi_type) thy =
  let val parse_hint = parse_hint (
            fn (Const(\<^const_name>\<open>Semimodule_Identity\<close>, _) $ F $ _ $ _ $ _ $ _ ) => F)
      val extract_oprs_from_hint = K []
      fun reasoning phi ctxt =
        default_reasoning false default_reasoning_configure (K (K NONE))
                          (exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))) phi ctxt
      val simp = K I

      val eqs = #equations phi @ map_filter I (#type_equations phi)
      val ind_conv = default_ind_conv (
             fn _ => fn _ =>
                  Conv.rewr_conv @{thm \<phi>TA_common_rewr_imp2_noact} then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv,
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_common_rewr_imp2'} then_conv
                  Phi_Reasoners.asm_rewrite true (Expansion.equip ctxt addsimps eqs) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                                    (conv_hol_imp_to_meta_if_has Conv.all_conv))

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      Guess_Scalar_One_E, @{thm' \<phi>TA_MI\<^sub>E_rule},
                                      [(K (SOME [0]), ind_conv, reasoning),
                                       (K (SOME [0]), ind_conv, reasoning)], K NONE, simp)
                                    phi instruction ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE
                                    (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                 (#2 instruction))
                                    ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties_s phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_identity = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Identity") gen_MI


end