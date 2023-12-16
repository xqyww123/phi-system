signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semantic_type : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun guess_property phi ctxt =
  let val ((x_term, T_term), ctxt) = fix_phi_term_params phi ctxt
      val (arg_tys, x_ty, model_ty) = parameters_and_typs_of phi

      val _ = if exists (can dest_parameterized_phi_ty o snd) arg_tys
              then raise Automation_Fail (fn () => let open Pretty in
                  [para "Property gusser does not support type operators right now"]
                end)
              else ()

      val _ = if #is_recursive phi then raise Automation_Fail (fn () => let open Pretty in
                [para "Property gusser does not support recursive \<phi>-types right now"]
              end) else ()

   in Seq.single ([], HOLogic.Trueprop $ (
          \<^Const>\<open>\<phi>SemType\<close> $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ x_term $ T_term) $ Var (("TY", 0), \<^Type>\<open>TY\<close>)),
          SOME x_term :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end

fun gen_semantic_type (_, name) instruction ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const>\<open>\<phi>SemType\<close> $ (\<^Const_>\<open>\<phi>Type _ _\<close> $ x $ T) $ _ => T $ x)

      val equip_expansion = equip_expansion_ss phi0
      val ind_conv = default_ind_conv (
            fn _ => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_noact} then_conv
                Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv,
            fn ctxt => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp1_noact} then_conv
                Phi_Reasoners.asm_rewrite true (equip_expansion ctxt addsimps (#equations phi0)) then_conv
                Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv)

      val varifier = if is_some (#1 instruction) then K (K NONE)
                     else fn _ => fn (Trueprop $ (SemTyp $ TY)) =>
                            SOME ([TY], fn [TY'] => Trueprop $ (SemTyp $ TY'))
      fun reasoning phi ctxt =
            default_reasoning true default_reasoning_configure varifier
                              (exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded [] ctxt phi))) phi ctxt

      val solver = K NONE
      val simp = if is_some (#1 instruction) then K I
                 else simplifier_by_cong @{thms' \<phi>TA_SemTy_cong}

      val ctxt = ctxt0
              |> Config.put Phi_Reasoner.ignore_dup_reasoner true
              |> Bundle.includes ["Spec_Framework.\<phi>sem_type_sat_EIF"]
              |> Config.restore Phi_Reasoner.ignore_dup_reasoner ctxt0

      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' \<phi>TA_SemTy_rule},
                                      [(K (SOME []), ind_conv, reasoning)], solver, K I, simp)
                                    phi0 instruction ctxt
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
                  Phi_Reasoner.add_rule (#3 instruction) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %\<phi>sem_type_derived}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val semantic_type = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Semantic_Type") gen_semantic_type

end
