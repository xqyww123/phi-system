signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val inhabited_type : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun guess_property phi ctxt =
  let val ((x_term, T_term), ctxt) = fix_phi_term_params phi ctxt
      val (rev_arg_tys, x_ty, model_ty) = parameters_and_typs_of phi

      fun collect_params ret [] _  = ret
        | collect_params ret ((_,arg_ty) :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] (rev rev_arg_tys) T_term

      val ants = map (fn ((rev_args, x, m), T'h) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_args T'h
             in \<^Const>\<open>Inhabited_Type x m\<close> $ T'
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params

   in Seq.single (ants, HOLogic.Trueprop $
          (\<^Const>\<open>Inhabited_Type x_ty model_ty\<close> $ T_term),
          SOME x_term :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end

fun gen_inhabited_type (_, name) instruction (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const>\<open>Inhabited_Type _ _\<close> $ T => T)
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
        |> Local_Theory.declaration {syntax=false,pervasive=false, pos = #3 instruction} (fn m =>
                  Phi_Reasoner.add_rule (#3 instruction) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %\<phi>sem_type_derived}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val inhabited_type = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Inhabited_Type") gen_inhabited_type

end
