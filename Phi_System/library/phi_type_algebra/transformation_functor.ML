signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val transformation_functor            : hint list -> Phi_Type_Algebra.derive
val functional_transformation_functor : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers


(*** Transformation Functor ***)

fun mk_TF's_two_instantiations ctxt0 (_, FT_term0, phi0) =
  let val (inst0, phi, ctxt) = fix_phi_type true phi0 ctxt0
      val FT_term = Term_Subst.instantiate (Phi_Help.table_no_c inst0) FT_term0

      val (T_ty :: rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty T_ty
      val F_term = (case FT_term of F $ _ => F
                                  | _ => error "Internal bug: Not a Type Operator")

      val param_typs = Term.add_tfreesT element_ty []
      val (param_typs', ctxt'1) = Variable.invent_types (map snd param_typs) ctxt
                                |> apfst (map TFree)
      val inst_ty = TFrees.make (param_typs ~~ param_typs')
      val F'1_term = Term_Subst.instantiate_frees (inst_ty, Frees.empty) F_term

      val params = Term.add_frees F'1_term []      
      val (param_names', ctxt') = Variable.variant_fixes (map fst params) ctxt'1
      val params' = map2 (fn N => fn (_,T) => Free(N,T)) param_names' params
      val inst = Frees.make (params ~~ params')
      val F'_term = Term_Subst.instantiate_frees (TFrees.empty, inst) F'1_term

      val ants = map2 (fn (N,T) => fn p' =>
                      \<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_SIMP\<close> $ (\<^Const>\<open>HOL.eq T\<close> $ Free(N,T) $ p')
                 ) params params'

   in (ants, F_term, F'_term, inst_ty, phi, ctxt')
  end

fun guess_property_TF (x_term, FT_term, phi0) ctxt =
  let val (ants, F_term, F'_term, inst_ty, phi, ctxt') = mk_TF's_two_instantiations ctxt (x_term, FT_term, phi0)
      val (T_ty :: rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty T_ty

      val TF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                       of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                           \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                          \<^Const>\<open>Transformation_Functor a b c d e f\<close> $ F_term $ F'_term
                        | _ => error "Internal bug")
      val target_ty = Term_Subst.instantiateT_frees inst_ty
   in guess_set_opr ctxt' x_ty element_ty
   |> Seq.maps (fn (D_term, ctxt'2) =>
        guess_rel_mapper target_ty ctxt'2 x_ty element_ty
     |> Seq.map (fn (rel_mapper, ctxt'3) =>
          (ants, \<^Const>\<open>Trueprop\<close> $ (TF_head $ D_term $ rel_mapper),
           x_term, FT_term, phi, ctxt'3)))
  end


local

fun TF_reasoner ctxt sequent =
  case PLPR_Exhaustive.reason_exhaustively (SOME 2)
            (ctxt, @{thm' \<phi>TA_TF_rule_step} RS sequent)
    of SOME th => th
     | NONE => raise Automation_Fail

fun TF_reasoning _ ctxt =
      gen_abstract_constraint_guided_reasoning (K NONE) TF_reasoner ctxt

fun gen_TF hint0 (phi0 : phi_type) generic =
  let val _ = assert_Type_Opr "Transformation_Functor" (Term.fastype_of (#term phi0))
      val ctxt0 = Context.proof_of generic
      val unify_hint = hint_unify_by_type_operator (
              fn (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ F1 $ _ $ _ $ _) => F1)
      val ind_conv = default_ind_conv (K (K (Conv.rewr_conv @{thm \<phi>TA_TF_rewr})),
                        fn ctxt => fn phi =>
                          Conv.rewr_conv @{thm \<phi>TA_TF_rewr} then_conv
                            Conv.implies_concl_conv (Conv.implies_concl_conv (
                                  HOLogic.Trueprop_conv (Phi_Conv.action_tag_conv (
                              Phi_Syntax.transformation_conv
                              (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)) then_conv
                               conv_chk_unfolded phi)
                              (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)) then_conv
                               conv_chk_unfolded phi)
                              Conv.all_conv)))))
      fun simp (_, ctxt) =
        if is_some hint0 then I
        else Conv.fconv_rule (
                Phi_Conv.hhf_concl_conv (fn ctxt =>
                  let val sctxt = ctxt addsimps @{thms special_Ex_def}
                   in HOLogic.Trueprop_conv (Conv.combination_conv
                        (Conv.arg_conv (Simplifier.rewrite sctxt))
                        (Simplifier.rewrite sctxt))
                  end
               ) ctxt)
      val rules = mk_rule_by_guess_or_hint ("Transformation_Functor", unify_hint, guess_property_TF,
                                            @{thm' \<phi>TA_TF_rule}, [0,~1,~1,~1],
                                            SOME ind_conv, TF_reasoning, K NONE, simp)
                                           phi0 hint0 ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail
        | SOME (rule', _) =>
          let fun set_prem_to_True rule =
                case Thm.prop_of rule
                  of _ (*Trueprop*) $ (_ $ Var v) =>
                      Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>True\<close>)]) rule
                   | _ => rule
              val locale_rule = (rule' RS' (ctxt0, @{thm' Transformation_Functor_L.intro}))
                              |> (fn th => case Thm.nprems_of th
                                             of 0 => set_prem_to_True th
                                              | 1 => Seq.hd (Thm.assumption (SOME ctxt0) 1 th)
                                              | _ => error "Internal bug")

                
              fun setup_locale cmd lthy =
                let val ((_,[locale_rule']), _) = Variable.import true [locale_rule] lthy
                 in case Thm.concl_of locale_rule'
                      of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Transformation_Functor_L\<close>, _)
                            $ Fa $ Fb $ D $ m $ Pr) =>
                    cmd ([(\<^locale>\<open>Transformation_Functor_L\<close>, ((Term.term_name (#term phi0), true),
                          (Expression.Positional [SOME Fa, SOME Fb, SOME D, SOME m,
                                                  SOME (case Pr of Var _ => \<^Const>\<open>True\<close> | _ => Pr)],
                           [])))], []) [] lthy
                      |> Proof.refine_primitive (fn _ => fn th => locale_rule' RS th)
                      |> Proof.global_done_proof
                end
           in generic
         (*|> Phi_Type_Algebra.note_properties phi0 [("Transformation_Functor", [rule'])] *)
           |> Context.mapping (Named_Target.theory_map (setup_locale Interpretation.global_interpretation))
                              (setup_locale Interpretation.sublocale)
         (*|> Context.mapping (Named_Target.theory_map (setup_functional_TF Interpretation.global_interpretation))
                              (setup_functional_TF Interpretation.sublocale)*)
          end)
  end

in

val transformation_functor = accept_one "Transformation_Functor" gen_TF

end

(** Functional Transformation Functor **)


fun guess_property_FTF (x_term, FT_term, phi0) ctxt0 =
  let val (ants, F_term, F'_term, inst_ty, phi, ctxt) = mk_TF's_two_instantiations ctxt0 (x_term, FT_term, phi0)
      val (T_ty :: rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty T_ty
      
      val ant = Phi_Help.list_mk_conj ants
      val FTF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                        of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                            \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                           \<^Const>\<open>Functional_Transformation_Functor a b c d e f\<close> $ F_term $ F'_term
                              $ Var(("D",0), c --> \<^Type>\<open>set a\<close>)
                              $ Var(("mapper",0), (a --> e --> \<^Type>\<open>bool\<close>) --> c --> f --> \<^Type>\<open>bool\<close>)
                              $ ant
                         | _ => error "Internal bug")
      val target_ty = Term_Subst.instantiateT_frees inst_ty
   in guess_func_mapper target_ty ctxt x_ty element_ty
   |> Seq.maps (fn (fm, ctxt'2) =>
        guess_pred_mapper ctxt'2 x_ty element_ty
     |> Seq.map (fn (pm, ctxt'3) =>
          ([], \<^Const>\<open>Trueprop\<close> $ (FTF_head $ pm $ fm), x_term, FT_term, phi, ctxt'3)))
  end

fun gen_FTF hint0 (phi0 : phi_type) thy =
  let val _ = assert_Type_Opr "Functional_Transformation_Functor" (Term.fastype_of (#term phi0))
      val ctxt0 = Context.proof_of thy
      val unify_hint = hint_unify_by_type_operator (
            fn (Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _ ) => F1)
      val reasoning = PLPR_reasoner NONE
      fun simp (_, ctxt) thm =
        if is_some hint0 then thm
        else Conv.fconv_rule (
                Phi_Conv.hhf_concl_conv (fn ctxt => 
                  let val sctxt = ctxt addsimps @{thms special_Ex_def}
                   in HOLogic.Trueprop_conv (Conv.combination_conv
                        (Conv.arg_conv (Simplifier.rewrite sctxt))
                        (Simplifier.rewrite sctxt))
                  end
             ) ctxt) thm
      val rules = mk_rule_by_guess_or_hint ("Functional_Transformation_Functor", unify_hint, guess_property_FTF,
                                            @{thm' \<phi>TA_FTF_rule}, [],
                                            NONE, K reasoning, K NONE, simp)
                                            phi0 hint0 ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail
        | SOME (rule'0, _) =>
          let fun set_prem_to_True rule =
                case Thm.prop_of rule
                  of _ (*Trueprop*) $ (_ $ Var v $ _ $ _) =>
                      Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>True\<close>)]) rule
                   | _ => rule
              val rule' = set_prem_to_True rule'0
              
              fun setup_functional_TF cmd lthy =
                let val ((_,[locale_rule']), _) = Variable.import true [rule'] lthy
                 in case Thm.concl_of locale_rule'
                      of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _)
                            $ Fa $ Fb $ D $ m $ Pr $ pm $ fm) =>
                          cmd ([(\<^locale>\<open>Functional_Transformation_Functor\<close>,
                                ((Term.term_name (#term phi0), true),
                                (Expression.Positional [SOME Fa, SOME Fb, SOME D, SOME m,
                                                        SOME (case Pr of Var _ => \<^Const>\<open>True\<close> | _ => Pr),
                                                        SOME pm, SOME fm],
                                 [])))], []) [] lthy
                            |> Proof.refine_primitive (fn _ => fn th => locale_rule' RS th)
                            |> Proof.global_done_proof
                end
           in thy
           |> Phi_Type_Algebra.note_properties phi0 [("Functional_Transformation_Functor", [rule'])]
           |> Context.mapping (Named_Target.theory_map (setup_functional_TF Interpretation.global_interpretation))
                              (setup_functional_TF Interpretation.sublocale)
          end)
  end

val functional_transformation_functor = accept_one "Functional_Transformation_Functor" gen_FTF

end