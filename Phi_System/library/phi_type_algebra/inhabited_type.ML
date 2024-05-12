signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val inhabited_type : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun guess_property phi ctxt =
  let val ((x_term, T_term), ctxt) = fix_phi_term_params phi ctxt
      val (_, x_ty, model_ty) = parameters_and_typs_of phi
   in Seq.single ([], HOLogic.Trueprop $
          (\<^Const>\<open>Inhabited_Type x_ty model_ty\<close> $ T_term),
          SOME x_term :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end

fun gen_inhabited_type (_, name) instruction ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const>\<open>Inhabited_Type _ _\<close> $ T => T)
      val ind_conv = K (K I)
      val varifier = K (K NONE)

      fun reasoning phi ctxt sequent =
            default_reasoning true default_reasoning_configure varifier
                              (exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))) phi ctxt sequent

      val solver = K NONE
      val simp = K I

      val ctxt = ctxt0
            (*|> Config.put Phi_Reasoner.ignore_dup_reasoner true
              |> Bundle.includes ["Spec_Framework.inh_typ_derv_tool"]
              |> Config.restore Phi_Reasoner.ignore_dup_reasoner ctxt0*)

      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' inh_typ_derv_rule},
                                      [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning)],
                                      solver, K I, simp)
                                    phi0 instruction ctxt
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s false phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
                  Phi_Reasoner.add_rule (#3 instruction) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %\<phi>sem_type_derived}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val inhabited_type = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Inhabited_Type") gen_inhabited_type

end
