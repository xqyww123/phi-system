signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val carrier_set : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

val guess_property = guess_property__abst_domain (fn (x,m) => \<^Const>\<open>Carrier_Set x m\<close>, \<^sort>\<open>type\<close>, \<^sort>\<open>sep_carrier\<close>)

fun gen_carrier_set (_,name) hint0 ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn Const(\<^const_name>\<open>Carrier_Set\<close>, _) $ T $ _ => T )

      val ind_conv = default_ind_conv (
            fn _ => fn _ => Conv.rewr_conv @{thm' \<phi>TA_CarS_rewr},
            fn ctxt => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_CarS_rewr} then_conv
                Conv.arg_conv (Conv.arg_conv (Conv.arg_conv (Conv.arg_conv (
                    Simplifier.rewrite (Expansion.equip ctxt addsimps (#equations phi0))
                )))))
      fun reasoning phi ctxt =
            default_reasoning true (default_reasoning_configure []) (K (K NONE))
                              (exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded' ctxt phi))) ctxt

      val mode_infer = not (is_some hint0)
      val solver = if mode_infer then solver__abst_domain name else K NONE

      fun simp (_, ctxt) rule =
        if is_some hint0
        then rule
        else Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (Conv.arg_conv (
                  Simplifier.rewrite (Simplifier.add_cong @{thm' HOL.conj_cong} ctxt
                                      addsimps @{thms special_Ex_def} ))
                )) ctxt) rule

      val ctxt = ctxt0
      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' \<phi>TA_CarS_rule},
                                      [(SOME ([0], ind_conv), reasoning)], solver, simp)
                                    phi0 hint0 ctxt
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80
                                              ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val carrier_set = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Carrier_Set") gen_carrier_set

end
