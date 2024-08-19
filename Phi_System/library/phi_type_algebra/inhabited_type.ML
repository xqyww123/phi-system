signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val inh_rule_expr : bv_typs -> term -> term
val inhabited_type : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun inh_rule_expr' bvtys T_term =
  let val T_params = Phi_Syntax.typ_parameter_of_phi_ty bvtys T_term
      val (_, x_ty, m_ty) = dest_parameterized_phi_ty (Term.fastype_of1 (bvtys,T_term))

      val ants = map (fn ((rev_args, x, m), T'h) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_args T'h
             in \<^Const>\<open>Inhabited x m\<close> $ T'
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params
   in (ants, \<^Const>\<open>Inhabited x_ty m_ty\<close> $ T_term)
  end

fun inh_rule_expr bvtys T_term =
  let val (rev_argtys, x_ty, m_ty) = dest_parameterized_phi_ty (Term.fastype_of1 (bvtys, T_term))
      val N = length rev_argtys
      val T_term' = fold_index (fn (i,_) => fn X => X $ Bound (N - 1 - i)) rev_argtys
                      (Term.incr_boundvars N T_term)
      val (ants, concl) = inh_rule_expr' (rev_argtys @ bvtys) T_term'
      
   in fold_rev (fn ant => fn X =>
        \<^Const>\<open>Pure.imp\<close> $ (HOLogic.Trueprop $ ant) $ X) ants
        (HOLogic.Trueprop $ concl)
   |> fold_index (fn (i,ty) => fn X =>
          \<^Const>\<open>Pure.all ty\<close> $ Abs("T\<^sub>" ^ string_of_int (N-1-i), ty, X)) rev_argtys
  end

fun guess_property phi ctxt =
  let val ((x_term, T_term), ctxt) = fix_phi_term_params phi ctxt
      val (ants, concl) = inh_rule_expr' [] T_term

   in Seq.single (ants, HOLogic.Trueprop $ concl,
          SOME x_term :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end

fun gen_inhabited_type (_, name) instruction (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const>\<open>Inhabited _ _\<close> $ T => T)
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

val inhabited_type = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Inhabited") gen_inhabited_type

end
