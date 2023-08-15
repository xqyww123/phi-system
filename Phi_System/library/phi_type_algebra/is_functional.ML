signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val is_functional : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property_tyop (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (rev_arg_tys,x_ty,model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term
      val x_ttys = map (#2 o #1) T_params
      val preds = Name.invent_names (Variable.names_of ctxt) "P"
                                     (map (fn T => T --> HOLogic.boolT) x_ttys)
      val ctxt = Variable.add_fixes_direct (map fst preds) ctxt
      val preds = x_ttys ~~ map Free preds
      val ants = map2 (fn ((rev_args, x, m), T'h) => fn (_, pred) =>
            let val arity = length rev_args
                val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - i)) rev_args T'h
             in \<^Const>\<open>Functionality x m\<close> $ T' $ pred
             |> fold (fn ty => fn X => HOLogic.all_const ty $ Abs("A", ty, X)) rev_args
            end
          ) T_params preds
   in guess_predicate ctxt preds x_ty
   |> Seq.map (fn (pred, ctxt) =>
        (ants, HOLogic.Trueprop $ (\<^Const>\<open>Abstract_Domain x_ty model_ty\<close> $ T_term $ pred),
         NONE :: parse_parameters_of_phi_type T_term, phi, ctxt))
  end


fun guess_property (phi:phi_type) ctxt =
  let val ((x_term, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (_, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun mk_prop (x_ty, m_ty, x, T) = \<^Const>\<open>Is_Functional m_ty\<close> $ (\<^Const>\<open>\<phi>Type x_ty m_ty\<close> $ x $ T)
      val ants = make_forall_quantified_property_for_parameters_of_a_phi_type mk_prop FT_term
   in Seq.single (ants, HOLogic.Trueprop $ mk_prop (x_ty, model_ty, x_term, FT_term),
                  SOME x_term :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end


fun gen_is_functional (_,name) hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val parse_hint = parse_hint_has_object_and_type (
            fn \<^Const>\<open>Is_Functional _\<close> $ (\<^Const>\<open>\<phi>Type _ _\<close> $ x $ T) => (x, T) )

      val ind_conv = default_ind_conv (
            fn _ => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_IsFunc_rewr},
            fn ctxt => fn _ =>
                Conv.rewr_conv @{thm' \<phi>TA_IsFunc_rewr} then_conv
                Conv.implies_conv
                  (HOLogic.Trueprop_conv (Phi_Conv.conj_sequence_conv (
                    Conv.try_conv (Raw_Simplifier.rewrite ctxt true @{thms' \<phi>TA_IsFunc_rewr_ants}))))
                  (PLPR_Syntax.premise_tag_conv (
                    Phi_Reasoners.asm_rewrite false (Simps.equip ctxt addsimps (#equations phi0)))))
      val reasoning = default_reasoning true
                          (default_reasoning_configure [])
                          (K (K NONE))
                          (exhaustive_PLPR_reasoner (SOME 1))

      val rules = deriving_framework (name, parse_hint, K [], guess_property, @{thm' \<phi>TA_IsFunc_rule},
                                      [(SOME ([], ind_conv), K reasoning)], K NONE, K I)
                                    phi0 hint0 ctxt0
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> note_properties phi0 [(name, [rule])]
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80
                                              ([],[]) NONE [Morphism.thm m rule])
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val is_functional = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Is_Functional") gen_is_functional

end
