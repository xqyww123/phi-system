signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val identity_element_I : quiet -> hint list -> Phi_Type_Algebra.derive
val identity_element_E : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*** Identity Element Intro \& Elim ***)

fun guess_id_ele (typ as TFree (_, S)) ctxt =
      if Sign.subsort (Proof_Context.theory_of ctxt) (S, \<^sort>\<open>one\<close>)
      then (TVars.empty, \<^Const>\<open>one_class.one typ\<close>, ctxt)
      else raise Automation_Fail (let open Pretty in fn () =>
                  [paragraph (text "Fail to guess the identity element for type " @
                             [brk 1, Syntax.pretty_typ ctxt typ, brk 1] @
                              text "which is a fixed variable not of sort \<open>one\<close>")]
                 end)
  | guess_id_ele (typ as TVar _) ctxt =
      let val inst  = (Phi_Help.lift_types_sort (Proof_Context.theory_of ctxt) [(typ, \<^sort>\<open>one\<close>)]
                       handle TYPE _ => raise Automation_Fail (let open Pretty in fn () =>
                                [paragraph (text "Fail to guess the identity element for type" @
                                            [brk 1, Syntax.pretty_typ ctxt typ, brk 1] @
                                            text "because fail to constrain it by sort \<open>one\<close>")]
                                end))
          val typ' = Term_Subst.instantiateT inst typ
       in (Phi_Help.certify_tyvars (Context.Proof ctxt) inst,
           \<^Const>\<open>one_class.one typ'\<close>, ctxt)
      end
  | guess_id_ele (typ as Type _) ctxt =
      let val (inst, unit_simp, ctxt') =
                case eBNF_Info.identity_element_unify typ (Context.Proof ctxt)
                  of ([], _) => raise Automation_Fail (fn () => let open Pretty in
                                  [paragraph (text "Fail to guess the property, because no identity element and \
                                                   \its simplification rule found for type" @
                                              [brk 1, Syntax.pretty_typ ctxt typ])]
                                  end)
                   | ((inst, unit_simp) :: _, ctxt') => (inst, unit_simp, ctxt')
          val unit = case Thm.concl_of unit_simp
                       of _ (*Trueprop*) $ (_ (*eq*) $ LHS $ _) => LHS
       in (inst, unit,
           Context.the_proof (Simps.map (fn ctxt => ctxt addsimps [unit_simp]) ctxt'))
      end

(*strategy: lift the logic type of the abstract objects onto \<^sort>\<open>one\<close>. If fails, guess fails.
  We only support the \<phi>-type to a unital abstract algebra. We guess the identity abstract object
  if \<open>1\<close> (the identity of the algebra), because if it is not the identity, what else better it could be?

  If the \<phi>-type is parameterized, for any parameter $A$ whose logic type looks like a \<phi>-type, if
  the abstract domain of $A$ is also unital, the property of identity element of $A$ is declared
  as an antecedent of the guessed property.
*)
fun guess_property_id_ele is_left (phi0:phi_type) ctxt =
  let val thy = Proof_Context.theory_of ctxt
      val (_,x_ty0,model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val inst  = (Phi_Help.lift_types_sort (Proof_Context.theory_of ctxt)
                                            [(x_ty0, \<^sort>\<open>one\<close>), (model_ty0, \<^sort>\<open>one\<close>)]
                  handle TYPE _ => raise Automation_Fail (fn () => let open Pretty in
                          [paragraph (text "Fail to lift the type " @
                                      [brk 1, Syntax.pretty_typ ctxt x_ty0, brk 1] @
                                      text "and" @
                                      [brk 1, Syntax.pretty_typ ctxt model_ty0, brk 1] @
                                      text " into sort \<open>one\<close>.")]
                          end))
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val phi01 = instantiate_phi (inst',Vars.empty) phi0
      val subst = Term_Subst.instantiate (inst, Vars.empty)

      val (_, x_ty01, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi01))
      val (inst01, unit, ctxt) = guess_id_ele x_ty01 ctxt
      val subst01 = Term_Subst.instantiate (Phi_Help.uncertify_tyvars inst01, Vars.empty)
      val phi = instantiate_phi (inst01, Vars.empty) phi01

      val ((x_term, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt

      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun mk_P ctxt = if is_left
                      then Variable.add_fixes (Name.invent (Variable.names_of ctxt) "P" 1) ctxt
                      else ([""], ctxt)
      val thy = Proof_Context.theory_of ctxt
      fun mk_Ants (Ty::rev_arg_tys) ants (T_term $ A) ctxt =
       (case try dest_parameterized_phi_ty Ty
          of SOME (rev_arg_tys_A, x_ty_A, model_ty_A) =>
              if Sign.of_sort thy (x_ty_A, \<^sort>\<open>one\<close>)
              then let
                    val arity_A = length rev_arg_tys_A
                    val ([P], ctxt') = mk_P ctxt
                    val A' = fold_index (fn (i,_) => fn X => X $ Bound (arity_A-1-i)) rev_arg_tys_A
                                (Term.incr_bv (arity_A, 0, A))
                    val ant = (\<^Const>\<open>\<phi>Type x_ty_A model_ty_A\<close> $ \<^Const>\<open>one_class.one x_ty_A\<close> $ A')
                            |> (fn X => (if is_left then \<^Const>\<open>Identity_Element\<^sub>I model_ty_A\<close> $ X $ Free(P, HOLogic.boolT)
                                                    else \<^Const>\<open>Identity_Element\<^sub>E model_ty_A\<close> $ X))
                            |> fold (fn T => fn X =>
                                    Const(\<^const_name>\<open>All\<close>, (T --> HOLogic.boolT) --> HOLogic.boolT)
                                      $ Abs("",T,X)
                                   ) rev_arg_tys_A
                 in mk_Ants rev_arg_tys (ant::ants) T_term ctxt'
                end
              else mk_Ants rev_arg_tys ants T_term ctxt
           | NONE => mk_Ants rev_arg_tys ants T_term ctxt)
        | mk_Ants [] ants _ ctxt = (ants, ctxt)
        | mk_Ants _ _ _ _ = raise ListPair.UnequalLengths
      val (ants, ctxt) = mk_Ants rev_arg_tys [] T_term ctxt
      val xT = \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ unit $ T_term
   in Seq.single (ants, \<^Const>\<open>Trueprop\<close> $ (
        (if is_left then \<^Const>\<open>Identity_Element\<^sub>I model_ty\<close> $ xT $ Var(("P", 0), HOLogic.boolT)
                    else \<^Const>\<open>Identity_Element\<^sub>E model_ty\<close> $ xT)),
        (case x_term of Free _ => SOME x_term | _ => NONE) :: parse_parameters_of_phi_type T_term,
        phi, ctxt)
  end

fun gen_id_ele is_left (_,name) hint0 (phi0 : phi_type) generic =
  let val ctxt0 = Context.proof_of generic
      val parse_hint = parse_hint_has_object_and_type (
            fn Const(\<^const_name>\<open>Identity_Element\<^sub>I\<close>, _) $ (\<^Const>\<open>\<phi>Type _ _\<close> $ x $ T) $ _ => (x, T)
             | Const(\<^const_name>\<open>Identity_Element\<^sub>E\<close>, _) $ (\<^Const>\<open>\<phi>Type _ _\<close> $ x $ T) => (x, T)
             | _ => raise TERM ("",[]))
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Identity_Element\<^sub>I\<close>, _) $ _ $ P) = [P]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (K (K Conv.all_conv),
                       fn ctxt => fn _ =>
                            HOLogic.Trueprop_conv (Conv.rewr_conv @{thm Action_Tag_def}) then_conv
                            Phi_Reasoners.asm_rewrite true (Simps.equip ctxt addsimps (#equations phi0)))
      val varify_subgoal =
            if is_left
            then K (fn Trueprop $ (Identity_Element $ S $ P) =>
                        SOME ([P], fn [P'] => Trueprop $ (Identity_Element $ S $ P')))
            else K (K NONE)

      val prem_extractions =
        if def_contains_satisfaction phi0
        then [Phi_Reasoners.Extract_Rule (
                if is_left
                then @{lemma' \<open>Identity_Element\<^sub>I S P \<equiv> (\<forall>v. v \<Turnstile> S \<longrightarrow> v = 1 \<and> P) \<and> Identity_Element\<^sub>I S P\<close>
                         by (simp add: Identity_Element\<^sub>I_def Transformation_def)}
                else @{lemma' \<open>Identity_Element\<^sub>E S \<equiv> (1 \<Turnstile> S) \<and> Identity_Element\<^sub>E S\<close>
                         by (simp add: Identity_Element\<^sub>E_def Transformation_def)})]
        else []

      val reasoner =
            if is_left
            then (fn ctxt => fn th =>
              case Thm.major_prem_of th
                of _ (*Trueprop*) $ (_ (*Identity_Element\<^sub>I*) $ _ $ P) =>
                    let val rule = (case P of Var _ => @{thm' \<phi>TA_Ident_I_rule_step_infer}
                                            | _     => @{thm' \<phi>TA_Ident_I_rule_step})
                     in exhaustive_PLPR_reasoner_by_rule rule (K (chk_unfolded' ctxt phi0)) ctxt th
                    end
                 | _ => error "BUG nov8x6UqTBS3cQ6ZkP/L5w")
            else exhaustive_PLPR_reasoner (SOME 1)
      fun reasoning _ = default_reasoning true
                            (default_reasoning_configure prem_extractions) varify_subgoal reasoner

      fun set_the_infer_tail ctxt th =
        if is_left then
          case Thm.concl_of th
            of _ (*Trueprop*) $ (_ (*Identity_Element\<^sub>I*) $ _ $ P) =>
                (case P of Const(\<^const_name>\<open>HOL.disj\<close>, _) $ Var v $ _ =>
                              Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>False\<close>)]) th
                           |> Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                                      HOLogic.Trueprop_conv (Conv.arg_conv (Simplifier.rewrite ctxt))
                               ) ctxt)
                         | _ => th)
             | _ => error "BUG nov8x6UqTBS3cQ6ZkP/L5w"
        else th

      fun simp (_, ctxt) th = set_the_infer_tail ctxt th
        |> (if is_some hint0 then I
            else Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                  let val sctxt = Simps.enhance ctxt addsimps @{thms special_Ex_def}
                   in HOLogic.Trueprop_conv (
                        if is_left
                        then Conv.combination_conv (Conv.arg_conv (Simplifier.rewrite sctxt))
                                                   (Simplifier.rewrite sctxt)
                        else Conv.arg_conv (Simplifier.rewrite sctxt))
                  end) ctxt))

      val rule = if is_left then @{thm' \<phi>TA_1L_rule} else @{thm' \<phi>TA_1R_rule}
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                     guess_property_id_ele is_left, rule,
                                     [(SOME ([], ind_conv), reasoning)],
                                     K NONE, simp)
                                    phi0 hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
         | SOME (rule', _) => generic
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.NORMAL_MODE 40 ([],[]) NONE
                                              [Morphism.thm m rule'])
            |> note_properties phi0 [(name, [rule'])]
            |> pair [rule']
  end

val identity_element_I = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Identity_Element\<^sub>I") (gen_id_ele true)
val identity_element_E = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Identity_Element\<^sub>E") (gen_id_ele false)


end