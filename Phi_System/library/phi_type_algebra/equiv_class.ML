signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val equiv_class : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers


fun gen_equiv_class (_, name) instruction (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const>\<open>Equiv_Class _ _\<close> $ T $ _ => T)
      fun extract_oprs_from_hint (\<^Const>\<open>Equiv_Class _ _\<close> $ _ $ eq) = [eq]
        | extract_oprs_from_hint _ = []

      val ind_conv = K (K I)
      val varifier = K (K NONE)

      fun reasoning phi ctxt sequent =
            default_reasoning true default_reasoning_configure varifier
                              (exhaustive_PLPR_reasoner NONE (K (chk_unfolded [] ctxt phi))) phi ctxt sequent

      val solver = K NONE
      val simp = K I

      val thy' = thy
              |> Config.put Phi_Reasoner.ignore_dup_reasoner true
              |> Bundle.includes ["Phi_BI.deriving_intabited_type"]
              |> Config.restore Phi_Reasoner.ignore_dup_reasoner thy

      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' inh_typ_derv_rule},
                                      [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning)],
                                      solver, K I, simp)
                                    phi0 instruction thy'
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties_s false phi0 [(name, [rule])]
        |> Local_Theory.declaration {syntax=false,pervasive=false, pos = #3 instruction} (
              fn m => fn lthy => lthy
                  |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
                  |> Phi_Reasoner.add_rule (#3 instruction) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %inhabited_derived}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule]
                  |> Config.restore_generic Phi_Reasoner.trace lthy)
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val equiv_class = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Equiv_Class") gen_equiv_class


end
