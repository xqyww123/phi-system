signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val identity_element_I : hint list -> Phi_Type_Algebra.derive
val identity_element_E : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*** Identity Element Intro \& Elim ***)

fun guess_id_ele (typ as TFree (_, S)) ctxt =
      if Sign.subsort (Proof_Context.theory_of ctxt) (S, \<^sort>\<open>one\<close>)
      then (TVars.empty, \<^Const>\<open>one_class.one typ\<close>, ctxt)
      else raise Automation_Fail
  | guess_id_ele (typ as TVar _) ctxt =
      let val env  = Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (typ, \<^sort>\<open>one\<close>) Vartab.empty
                     handle TYPE _ => raise Automation_Fail
          val inst = Phi_Help.tyenv_to_tvars_table ctxt env
          val typ' = Term_Subst.instantiateT (Phi_Help.ty_table_no_c inst) typ
       in (inst, \<^Const>\<open>one_class.one typ'\<close>, ctxt)
      end
  | guess_id_ele typ ctxt =
  let val ((inst, unit_simp) :: _, ctxt') =
            BNF_FP_Sugar_More.identity_element_unify typ (Context.Proof ctxt)
      val unit = case Thm.concl_of unit_simp
                   of _ (*Trueprop*) $ (_ (*eq*) $ LHS $ _) => LHS
   in (inst, unit,
       Context.the_proof (Simps.map (fn ctxt => ctxt addsimps [unit_simp]) ctxt'))
  end

fun guess_property_id_ele is_left (x_term0, T_term0, (phi0:phi_type)) ctxt =
  let val (_,x_ty0,model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val inst0  = Vartab.empty
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (x_ty0, \<^sort>\<open>one\<close>)
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (model_ty0, \<^sort>\<open>one\<close>)
                   handle TYPE _ => raise Automation_Fail
      val inst = Phi_Help.tyenv_to_tvars_table_no_c inst0
      val inst' = TVars.map (K (Thm.ctyp_of ctxt)) inst
      val phi01 = instantiate_phi (inst',Vars.empty) phi0
      val subst = Term_Subst.instantiate (inst, Vars.empty)
      val (x_term01, T_term01) = (subst x_term0, subst T_term0)

      val (_, x_ty01, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi01))
      val (inst01, unit, ctxt) = guess_id_ele x_ty01 ctxt
      val subst01 = Term_Subst.instantiate (Phi_Help.ty_table_no_c inst01, Vars.empty)
      val phi = instantiate_phi (inst01, Vars.empty) phi01
      val (x_term, T_term) = (subst01 x_term01, subst01 T_term01)

      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun mk_P ctxt = if is_left
                      then Variable.add_fixes (Name.invent (Variable.names_of ctxt) "P" 1) ctxt
                      else ([""], ctxt)
      val thy = Proof_Context.theory_of ctxt
      fun mk_Ants (Ty::rev_arg_tys) ants (T_term $ A) ctxt =
       (let val (rev_arg_tys_A, x_ty_A, model_ty_A) = dest_parameterized_phi_ty Ty
         in if Sign.of_sort thy (x_ty_A, \<^sort>\<open>one\<close>)
            then let
                  val arity_A = length rev_arg_tys_A
                  val ([P], ctxt') = mk_P ctxt
                  val xA = \<^Const>\<open>\<phi>Type x_ty_A model_ty_A\<close> $ \<^Const>\<open>one_class.one x_ty_A\<close> $ A
                  val ant = (Term.incr_bv (arity_A, 0, xA))
                          |> fold_index (fn (i,_) => fn X => X $ Bound (arity_A-1-i)) rev_arg_tys_A
                          |> (fn X => (if is_left then \<^Const>\<open>Identity_Element\<^sub>I model_ty_A\<close> $ X $ Free(P, HOLogic.boolT)
                                                  else \<^Const>\<open>Identity_Element\<^sub>E model_ty_A\<close> $ X))
                          |> fold (fn T => fn X =>
                                  Const(\<^const_name>\<open>All\<close>, (T --> HOLogic.boolT) --> HOLogic.boolT)
                                    $ Abs("",T,X)
                                 ) rev_arg_tys_A
               in mk_Ants rev_arg_tys (ant::ants) T_term ctxt'
              end
            else mk_Ants rev_arg_tys ants T_term ctxt
        end handle TYPE _ => mk_Ants rev_arg_tys ants T_term ctxt)
        | mk_Ants [] ants _ ctxt = (ants, ctxt)
        | mk_Ants _ _ _ _ = raise ListPair.UnequalLengths
      val (ants, ctxt) = mk_Ants rev_arg_tys [] T_term ctxt
      val xT = \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ unit $ T_term
   in Seq.single (ants, \<^Const>\<open>Trueprop\<close> $ (
        (if is_left then \<^Const>\<open>Identity_Element\<^sub>I model_ty\<close> $ xT $ Var(("P", 0), HOLogic.boolT)
                    else \<^Const>\<open>Identity_Element\<^sub>E model_ty\<close> $ xT)),
        x_term, T_term, phi,
        ctxt)
  end

fun gen_id_ele is_left hint0 (phi0 : phi_type) generic =
  let val ctxt0 = Context.proof_of generic
      val name = if is_left then "Identity_Element\<^sub>I" else "Identity_Element\<^sub>E"
      val unify_hint_U = hint_unify_by_type (
            fn Const(\<^const_name>\<open>Identity_Element\<^sub>I\<close>, _) $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ T) $ _ => T
             | Const(\<^const_name>\<open>Identity_Element\<^sub>E\<close>, _) $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ T) => T
             | _ => raise TERM ("",[]))
      val ind_conv = default_ind_conv (K (K Conv.all_conv),
                       fn ctxt => fn _ =>
                            HOLogic.Trueprop_conv (Conv.rewr_conv @{thm Action_Tag_def}) then_conv
                            Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0)))
      val varify_subgoal = if is_left
            then (fn Trueprop $ (Identity_Element $ S $ P) =>
                        SOME ([P], fn [P'] => Trueprop $ (Identity_Element $ S $ P')))
            else K NONE

      val extract_prem =
        if def_contains_satisfaction phi0
        then extract_pure_prem_by_RS (if is_left
                                      then @{thms' \<phi>TA_Ident_I_extract_prem}
                                      else @{thms' \<phi>TA_Ident_E_extract_prem})
        else K (K [])

      fun reasoning _ = gen_abstract_constraint_guided_reasoning
                            varify_subgoal extract_prem (PLPR_reasoner (SOME 1))
      fun simp (_, ctxt) =
        if is_some hint0 then I
        else Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
              let val sctxt = ctxt addsimps @{thms special_Ex_def}
               in HOLogic.Trueprop_conv (
                    if is_left
                    then Conv.combination_conv (Conv.arg_conv (Simplifier.rewrite sctxt))
                                               (Simplifier.rewrite sctxt)
                    else Conv.arg_conv (Simplifier.rewrite sctxt))
              end) ctxt)
      val rule = if is_left
                 then if is_some hint0 then @{thm' \<phi>TA_1L_rule}
                      else @{thm' \<phi>TA_1L_rule'}
                 else @{thm' \<phi>TA_1R_rule}
      val rules = mk_rule_by_guess_or_hint (name, unify_hint_U, guess_property_id_ele is_left, rule, [],
                                            SOME ind_conv, reasoning, K NONE, simp)
                                           phi0 hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail
         | SOME (rule', _) => generic
            |> Phi_Type_Algebra.note_properties phi0
                  [((if is_left then "Identity_Element\<^sub>I" else "Identity_Element\<^sub>E"), [rule'])]
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.NORMAL 40 ([],[]) NONE
                                              [Morphism.thm m rule'])
  end

val identity_element_I = accept_one "Identity_Element\<^sub>I" (gen_id_ele true)
val identity_element_E = accept_one "Identity_Element\<^sub>E" (gen_id_ele false)


end