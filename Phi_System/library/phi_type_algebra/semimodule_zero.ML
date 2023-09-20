signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semimodule_zero : quiet -> hint list -> Phi_Type_Algebra.derive
val closed_semimodule_zero : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun gen_M0 closed (der_id, name) hint0 ctxt0 (phi : phi_type) thy =
  let val parse_hint = parse_hint (fn (Const(\<^const_name>\<open>Semimodule_Zero\<close>, _) $ F1 $ _ $ _ ) => F1)
      val extract_oprs_from_hint = K []
      fun reasoning phi ctxt =
        default_reasoning false (default_reasoning_configure []) (K (K NONE))
                          (exhaustive_PLPR_reasoner NONE (K (chk_unfolded' ctxt phi))) phi ctxt
      val simp = K I
      val ind_conv = default_ind_conv (
             fn _ => fn _ => Conv.rewr_conv @{thm \<phi>TA_M0_rewr},
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_M0_rewr} then_conv
                  Conv.arg_conv (Phi_Conv.may_action_tag_conv (
                    let val sctxt = Expansion.equip ctxt addsimps (#equations phi @ map_filter I (#type_equations phi))
                     in Simplifier.rewrite sctxt
                    end)))
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint, Guess_Scalar_Zero closed,
                                      (if closed then @{thm' \<phi>TA_M0c_rule} else @{thm' \<phi>TA_M0_rule}),
                                      [(K (SOME [0]), ind_conv, reasoning)], K NONE, simp)
                                    phi hint0 ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties_s phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_zero = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Zero") (gen_M0 false)
val closed_semimodule_zero = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Closed_Semimodule_Zero") (gen_M0 true)


end
