signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val object_equiv       : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers


(*** Object Equivalence ***)

local

fun set_last_schematic_var ctxt rule0 =
  let val rule = Phi_Help.beta_eta_contract rule0
      val (t1,t2,tm) =
        case Thm.concl_of rule
          of _ (*Trueprop*) $ (_ (*Object_Equiv*) $ _ $ Abs (_, t1, Abs (_, t2, tm)))
              => (t1,t2,tm)
           | _ => error "Internal bug cb9504e4-7db1-45f8-b1f6-ec37a5b75105"
      fun get_the_last_var (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ X) = get_the_last_var X
        | get_the_last_var (Var v $ Bound 0 $ Bound 1) = (v, Abs("",t2,Abs("",t1,\<^term>\<open>True\<close>)))
        | get_the_last_var (Var v $ Bound 1 $ Bound 0) = (v, Abs("",t1,Abs("",t2,\<^term>\<open>True\<close>)))
        | get_the_last_var _ = error "Internal bug 6160c2ee-6448-4654-b017-237c879c33a3"
      val last_var = get_the_last_var tm |> apsnd (Thm.cterm_of ctxt)
   in Thm.instantiate (TVars.empty, Vars.make [last_var]) rule
  end

fun set_eq_when_it_is_constant_true ctxt rule0 =
  let val rule = Phi_Help.beta_eta_contract rule0
      val v = case Thm.concl_of rule
                of _ (*Trueprop*) $ (_ (*\<phi>Equal_Obj*) $ Var v $ _) => v
                 | _ => error "Internal bug 5d769e14-74ca-4afb-8d43-672e0afc5470"
      val P = case snd v
                of \<^Type>\<open>fun a \<open>\<^Type>\<open>fun b _\<close>\<close>\<close> => Abs("",a,Abs("",b,\<^term>\<open>True\<close>))
                 | _ => error "Internal bug a74fc08c-d9c1-4b19-99b2-4f18a07b31aa"
   in Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt P)]) rule
  end

(*must be beta-eta normalized*)
fun infer_eq ctxt rule =
  let fun is_free_bound lev (Abs(_,_,X)) = is_free_bound (lev+1) X
        | is_free_bound lev (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ X $ _) = is_free_bound lev X
        | is_free_bound lev (A $ B) = is_free_bound lev A andalso is_free_bound lev B
        | is_free_bound lev (Bound i) = (i = lev)
        | is_free_bound _ _ = true
      fun is_free_bound' (Abs(_,_,X)) = is_free_bound 0 X
        | is_free_bound' _ = true
   in (case Thm.major_prem_of rule
        of _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (
                  Const(\<^const_name>\<open>Ex\<close>, _) $ (Abs(_,_, Const(\<^const_name>\<open>All\<close>, _) $ _)) ) $ _) =>
            Conv.fconv_rule (Phi_Conv.leading_antecedent_conv (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (
                  HOLogic.conj_conv (Phi_Conv.move_Ex_inside_All ctxt) Conv.all_conv
              )) ctxt)) rule
            |> infer_eq ctxt
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (
                  Const(\<^const_name>\<open>Ex\<close>, _) $ (Abs(_,_, Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ )) ) $ _) =>
            Conv.fconv_rule (Phi_Conv.leading_antecedent_conv (Phi_Conv.hhf_concl_conv (fn ctxt =>
                HOLogic.Trueprop_conv (
                  HOLogic.conj_conv (Conv.rewr_conv @{thm' HOL.ex_simps(6)[folded atomize_eq]}) Conv.all_conv
              )) ctxt)) rule
            |> infer_eq ctxt
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ (Const(\<^const_name>\<open>All\<close>, _) $ X ) $ _) =>
            infer_eq ctxt (if is_free_bound' X
                           then @{thm' Object_Equiv_rule_move_all2} RS rule
                           else @{thm' Object_Equiv_rule_move_all} RS rule)
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>, _)) =>
            (@{thm Object_Equiv_rule_move_set_eq_end} RS (@{thm' simp_thms(21)[THEN iffD2]} RS rule))
              |> set_last_schematic_var ctxt
         | _ (*Trueprop*) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
            infer_eq ctxt (@{thm' Object_Equiv_rule_move_set_eq} RS rule)
         | _ (*Trueprop*) $ Const(\<^const_name>\<open>True\<close>, _) =>
            (@{thm' TrueI} RS rule)
              |> set_eq_when_it_is_constant_true ctxt
         | _ => error "internal bug 7147bf3f-9e7d-4ffc-a40b-aa621a4fca21")
      handle THM _ =>
        raise Automation_Fail ("Fail to infer the object equivelance from the obtained obligation\n" ^
                 Thm.string_of_thm ctxt rule)
  end


fun guess_property_obj_eq (x_Term, T_term, (phi:phi_type)) ctxt0 =
  let val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi)) 
      fun mk_Ants ctxt (Ty::rev_arg_tys) (eq::eq_names) ants param_eqs (T_term $ A) =
           (let val (rev_arg_tys_A, x_ty_A, model_ty_A) = dest_parameterized_phi_ty Ty
                val arity_A = length rev_arg_tys_A
                val typ = x_ty_A --> x_ty_A --> \<^typ>\<open>bool\<close>
                val ant = (Term.incr_bv (arity_A, 0, A))
                        |> fold_index (fn (i,_) => fn X => X $ Bound (arity_A-1-i)) rev_arg_tys_A          
                        |> (fn X => \<^Const>\<open>Object_Equiv x_ty_A model_ty_A\<close> $ X $ Free(eq, typ))
                        |> fold (fn T => fn X =>
                            Const(\<^const_name>\<open>All\<close>, (T --> HOLogic.boolT) --> HOLogic.boolT)
                              $ Abs("",T,X)
                           ) rev_arg_tys_A
             in mk_Ants ctxt rev_arg_tys eq_names (ant::ants)
                        ((x_ty_A, Free(eq, typ))::param_eqs) T_term
            end
            handle TYPE _ => mk_Ants ctxt rev_arg_tys eq_names ants param_eqs T_term)
        | mk_Ants _ [] [] ants param_eqs _ = (ants, param_eqs)
        | mk_Ants _ _ _ _ _ _ = raise ListPair.UnequalLengths

      val arity = length rev_arg_tys
      val rev_eq_names' = Name.invent (Variable.names_of ctxt0) "eq" arity
      val (rev_eq_names, ctxt) = Variable.add_fixes rev_eq_names' ctxt0
      val (ants,param_eqs) = mk_Ants ctxt rev_arg_tys rev_eq_names [] [] T_term

      val eq_terms =
             if #is_recursive phi
             then guess_self_rel ctxt param_eqs x_ty
             else Seq.single (Var(("eq", 1), x_ty --> x_ty --> HOLogic.boolT), ctxt)
   in eq_terms
   |> Seq.map (fn (eq_term, ctxt') =>
        (ants, \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Object_Equiv x_ty model_ty\<close> $ T_term $ eq_term),
         x_Term, T_term, phi, ctxt'))
  end

fun OE_reasoning phi ctxt rule =
  let val ctxt' = Context.proof_map (Phi_Reasoner.add_pass (
            "\<phi>TA.OE", \<^pattern_prop>\<open>Object_Equiv _ _\<close>,
            fn _ => fn (rules, (_, priority), pats, guard, ctxt) =>
                       (rules, (Phi_Reasoner.LOCAL_CUT, priority), pats, guard, ctxt))) ctxt
      val extract_prem =
        if def_contains_satisfaction phi
        then extract_pure_prem_by_RS @{thms' \<phi>TA_OE_extract_prem}
        else K (K [])
   in gen_abstract_constraint_guided_reasoning true (K (K NONE)) extract_prem (ToA_reasoner phi) ctxt' rule
  end

fun gen_obj_equal' hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val unify_hint = hint_unify_by_type (
            fn \<^Const>\<open>Object_Equiv _ _\<close> $ T' $ _ => T')
      fun extract_oprs_from_hint (\<^Const>\<open>Object_Equiv _ _\<close> $ _ $ eq) = [eq]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (K (K (Conv.rewr_conv @{thm \<phi>TA_EO_rewr_IH})),
                       fn ctxt => fn _ => Conv.rewr_conv @{thm \<phi>TA_EO_rewr_C} then_conv
                            Conv.implies_concl_conv (
                              HOLogic.Trueprop_conv (fn ctm =>
                              Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0)) ctm
                            )))
      fun infer (phi, ctxt, rule) =
            if is_some hint0 orelse #is_recursive phi then NONE
            else (@{thm' Premise_I} RS rule)
                   |> Phi_Help.beta_eta_contract
                   |> Simplifier.rewrite_rule ctxt @{thms special_Ex_def}
                   |> infer_eq ctxt
                   |> SOME
      fun simp (_, ctxt) =
        if is_some hint0 then I
        else Conv.fconv_rule (Phi_Conv.hhf_concl_conv 
               (K (Conv.arg_conv (Conv.arg_conv (
                  Simplifier.rewrite (ctxt addsimps @{thms special_Ex_def}))))) ctxt)
      val rules = mk_rule_by_guess_or_hint ("Object_Equiv", unify_hint, extract_oprs_from_hint, guess_property_obj_eq,
                                            @{thm' Object_Equiv_rule}, [0],
                                            SOME ind_conv, OE_reasoning, infer, simp)
                                           phi0 hint0 ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail ""
        | SOME (rule', _) => thy
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 40
                                              ([],[]) NONE [Morphism.thm m rule'])
            |> Phi_Type_Algebra.note_properties phi0 [("obj_eq", [rule'])])
  end

in

val object_equiv = accept_one "Object_Equiv" gen_obj_equal'

end

end
