signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val STyp_Of : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun guess_property phi ctxt =
  let val ((x_term, T_term), ctxt) = fix_phi_term_params phi ctxt
      val (_, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of T_term)
      val concl = \<^Const>\<open>HOL.eq \<^Type>\<open>TY\<close>\<close> $ (\<^Const>\<open>SType_Of x_ty\<close> $ T_term) $ Var(("TY",0),\<^Type>\<open>TY\<close>)
   in Seq.single ([], HOLogic.Trueprop $ concl,
          SOME x_term :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end

fun gen_styp_of (_, name) instruction (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (
            fn \<^Const>\<open>HOL.eq _\<close> $ (\<^Const>\<open>SType_Of _\<close> $ T) $ _ => T)
      val ind_conv = K (K I)
      fun varifier _ (Trueprop $ (Eq $ ST $ TY)) =
            SOME ([TY], fn [TY'] => Trueprop $ (Eq $ ST $ TY'))

      fun reasoning phi ctxt sequent =
            default_reasoning true default_reasoning_configure varifier
                              (exhaustive_PLPR_reasoner_by_rule @{thm' styp_of_derv_rule'}
                                    (K (chk_unfolded [] ctxt phi))) phi ctxt sequent

      val solver = K NONE
      val simp = K I

      val thy' = thy
      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' styp_of_derv_rule},
                                      [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning)],
                                      solver, K I, simp)
                                    phi0 instruction thy'
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s false phi0 [(name, [rule])]
        |> Local_Theory.declaration {syntax=false,pervasive=false, pos = #3 instruction} (
              fn m => Context.mapping (Simplifier.map_theory_simpset (fn ctxt => ctxt addsimps [rule]))
                                      (fn ctxt => ctxt addsimps [rule]))
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val STyp_Of = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "\<t>\<y>\<p>\<e>\<o>\<f>") gen_styp_of
end
