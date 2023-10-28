signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val carrier_set : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

val guess_property = guess_property_like_abst_domain (
        false, false, true,
        fn (x,m) => \<^Const>\<open>Carrier_Set x m\<close>,
        fn (ctxt, x_ty, _, cond) => fn ants =>
             (case cond of Abs (_, _, \<^Const>\<open>True\<close>) => ants
                 | _ => maps (constrain_antecedents (
                            \<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_GUARD\<close> $ (simplified_exists_qualify ctxt x_ty cond))) ants),
        fn (ctxt, x_ty, oblg, cond) => fn pred =>
              Abs ("x", x_ty, \<^Const>\<open>HOL.implies\<close>
                        $ (cond $ Bound 0)
                        $ (\<^Const>\<open>HOL.conj\<close> $ (oblg $ Bound 0) $ (pred $ Bound 0))),
        \<^sort>\<open>type\<close>, \<^sort>\<open>sep_carrier\<close>)

fun gen_carrier_set (_,name) instruction ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn Const(\<^const_name>\<open>Carrier_Set\<close>, _) $ T $ _ => T )

      val ind_conv = default_ind_conv (
            fn _ => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_noact} then_conv
                Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv,
            fn ctxt => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_noact} then_conv
                Phi_Reasoners.asm_rewrite true (Expansion.equip ctxt addsimps (#equations phi0)) then_conv
                Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv)
      fun reasoning phi ctxt =
            default_reasoning true default_reasoning_configure (K (K NONE))
                              (exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded [] ctxt phi))) phi ctxt

      val mode_infer = not (is_some (#1 instruction)) andalso not (#is_recursive phi0)
      val solver =
            if mode_infer
            then predicate_infer false
                    (fn _ $ (_ $ Abs (_, _, \<^Const>\<open>HOL.conj\<close> $ _ $ (Var v $ Bound 0))) => v)
                    (oblg_solver' name)
            else K NONE

      val simp = if is_some (#1 instruction) then K I
                 else simplifier_by_cong @{thms' \<phi>TA_CarS_cong}

      val ctxt = ctxt0
      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' \<phi>TA_CarS_rule},
                                      [(K (SOME [0]), ind_conv, reasoning)], solver, simp)
                                    phi0 instruction ctxt
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %derived_carrier_set}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val carrier_set = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Carrier_Set") gen_carrier_set

end
