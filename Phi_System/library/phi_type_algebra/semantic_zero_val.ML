signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val semantic_zero_val : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun guess_property phi0 ctxt =
  let val (_, x_ty0, model_ty0) = parameters_and_typs_of phi0
      val inst = lift_types_sort (Proof_Context.theory_of ctxt) [(x_ty0, \<^sort>\<open>zero\<close>)]
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val phi = instantiate_phi (inst',Vars.empty) phi0

      val ((x_term, T_term), ctxt) = fix_phi_term_params phi ctxt
      val (_, x_ty, model_ty) = parameters_and_typs_of phi

      val TY = get_first (fn th => case Thm.concl_of th of _ (*Trueprop*) $ (_ (*SemTyp*) $ TY) => SOME TY
                                      | _ => error "BUG: Bad rule of \<phi>SemType")
                         (flat (lookup_derived_properties (Context.Proof ctxt) phi "Semantic_Type"))
            |> (fn SOME TY' => TY'
                 | NONE => raise Automation_Fail (fn () => let open Pretty in
                              [para "The semantic type of the \<phi>-type is unknown from the existing \<phi>SemType rules."]
                           end))

   in Seq.single ([], HOLogic.Trueprop $ (
          \<^Const>\<open>Semantic_Zero_Val x_ty\<close> $ TY $ T_term $ \<^Const>\<open>zero_class.zero x_ty\<close>),
          NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end

fun gen_semantic_zero_val (_, name) instruction ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const_>\<open>Semantic_Zero_Val _\<close> $ _ $ T $ _ => T)
      fun reasoning phi ctxt =
            default_reasoning true default_reasoning_configure (K (K NONE))
                              (exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded [] ctxt phi))) phi ctxt

      val solver = K NONE
      val simp = K I

      val ctxt = ctxt0
              |> Config.put Phi_Reasoner.ignore_dup_reasoner true
              |> Bundle.includes ["Spec_Framework.Semantic_Zero_Val_EIF_brute"]
              |> Config.restore Phi_Reasoner.ignore_dup_reasoner ctxt0

      val rules = deriving_framework (name, parse_hint, K [], guess_property,
                                      @{thm' \<phi>TA_Semantic_Zero_Val_rule},
                                      [(K NONE, K (K I), reasoning)],
                                      solver, simp)
                                    phi0 instruction ctxt
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
                  Phi_Reasoner.add_rule (#3 instruction) Phi_Reasoner.TO_BE_OVERRIDE
                                        (the_default @{reasoner_group %semantic_zero_val_derived}
                                                     (#2 instruction))
                                        ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val semantic_zero_val = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Semantic_Zero_Val")
                                          gen_semantic_zero_val

end


