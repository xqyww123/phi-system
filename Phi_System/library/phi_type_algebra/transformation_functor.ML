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
      val FT_term = Term_Subst.instantiate (Phi_Help.uncertify_vars inst0) FT_term0
   in Seq.of_list (separate_type_operator_and_its_non_parameterized_parameter FT_term)
   |> Seq.map (fn (T_term, F_term) => let
      val T_ty = Term.fastype_of T_term
      val ([],element_ty,_) = dest_parameterized_phi_ty T_ty

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

   in (ants, F_term, F'_term, T_term, inst_ty, phi, ctxt')
  end)
  end

fun guess_property_TF (x_term, FT_term, phi0) ctxt =
  mk_TF's_two_instantiations ctxt (x_term, FT_term, phi0)
    |> Seq.maps (fn (ants, F_term, F'_term, T_term, inst_ty, phi, ctxt') =>
  let val (_, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty (Term.fastype_of T_term)

      val TF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                       of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                           \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                          \<^Const>\<open>Transformation_Functor a b c d e f\<close> $ F_term $ F'_term
                        | _ => error "Internal bug")
      val target_ty = Term_Subst.instantiateT_frees inst_ty
      val Rng = Abs("_", x_ty, \<^Const>\<open>top \<^Type>\<open>set \<open>target_ty element_ty\<close>\<close>\<close>)
   in guess_set_opr ctxt' x_ty element_ty
   |> Seq.maps (fn (D_term, ctxt'2) =>
        guess_rel_mapper (fn (ty1,ty2) => if ty1 = ty2 then \<^Const>\<open>HOL.eq ty1\<close>
                                          else raise Automation_Fail "Fail to guess the relation mapper for dead type parameters"
                         ) target_ty ctxt'2 x_ty element_ty
     |> Seq.map (fn (rel_mapper, ctxt'3) =>
          (ants, \<^Const>\<open>Trueprop\<close> $ (TF_head $ D_term $ Rng $ rel_mapper),
           x_term, FT_term, phi, ctxt'3)))
  end)


local

fun TF_reasoner ctxt sequent =
  case PLPR_Exhaustive.reason_exhaustively (SOME 3)
            (ctxt, @{thm' \<phi>TA_TF_rule_step} RS sequent)
    of SOME th => th
     | NONE => raise Automation_Fail "\<phi>-LPR reasoning fails"

fun TF_reasoning phi ctxt =
  let val extract_prem =
        if def_contains_satisfaction phi
        then extract_pure_prem_by_RS @{thms' \<phi>TA_TF_extract_prem}
        else K (K [])
   in gen_abstract_constraint_guided_reasoning true
          (default_reasoning_configure extract_prem)
          (K (K NONE)) TF_reasoner ctxt
  end

fun gen_TF prop_i hint0 (phi0 : phi_type) generic =
  let val ctxt0 = Context.proof_of generic
            (*|> def_contains_satisfaction phi0 ? Context.proof_map (
                    Phi_Reasoners.Is_Premise_of_Obligation.add 123
                      (fn \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ _ $ _ $ _ $ _) => SOME true
                        | X => NONE)) *)
      val unify_hint = hint_unify_by_type_operator (
              fn (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ F1 $ _ $ _ $ _ $ _) => F1)
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ _ $ _ $ D $ R $ M) = [D,R,M]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (K (K (fn ctm => Conv.rewr_conv @{thm \<phi>TA_TF_rewr_C} ctm)),
                        fn ctxt => fn phi =>
                          (fn ctm => Conv.rewr_conv @{thm \<phi>TA_TF_rewr_C} ctm) then_conv
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
      val name = if prop_i = 0 then "Transformation_Functor"
                 else "Transformation_Functor/" ^ string_of_int prop_i
      val rules = mk_rule_by_guess_or_hint (name, unify_hint, extract_oprs_from_hint, guess_property_TF,
                                            @{thm' \<phi>TA_TF_rule}, [0,~1,~1,~1],
                                            SOME ind_conv, TF_reasoning, K NONE, simp)
                                           phi0 hint0 ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail ""
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
                    val interp_name = Term.term_name (#term phi0) ^
                                      (if prop_i = 0 then "" else string_of_int prop_i)
                 in case Thm.concl_of locale_rule'
                      of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Transformation_Functor_L\<close>, _)
                            $ Fa $ Fb $ D $ R $ m $ Pr) =>
                    cmd ([(\<^locale>\<open>Transformation_Functor_L\<close>, ((interp_name, true),
                          (Expression.Positional [SOME Fa, SOME Fb, SOME D, SOME R, SOME m,
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

val transformation_functor = accept gen_TF

end

(** Functional Transformation Functor **)

fun guess_property_FTF (x_term, FT_term, phi0) ctxt0 =
  mk_TF's_two_instantiations ctxt0 (x_term, FT_term, phi0)
    |> Seq.maps (fn (ants, F_term, F'_term, T_term, inst_ty, phi, ctxt) => let
      val (_, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty (Term.fastype_of T_term)
      
      val ant = Phi_Help.list_mk_conj ants
      val FTF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                        of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                            \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                           \<^Const>\<open>Functional_Transformation_Functor a b c d e f\<close> $ F_term $ F'_term
                              $ Var(("D",0), c --> \<^Type>\<open>set a\<close>)
                              $ Var(("R",0), c --> \<^Type>\<open>set e\<close>)
                              $ Var(("mapper",0), (a --> e --> \<^Type>\<open>bool\<close>) --> c --> f --> \<^Type>\<open>bool\<close>)
                              $ ant
                         | _ => error "Internal bug")
      val target_ty = Term_Subst.instantiateT_frees inst_ty
   in guess_func_mapper target_ty ctxt x_ty element_ty
   |> Seq.maps (fn (fm, ctxt'2) =>
        guess_pred_mapper ctxt'2 x_ty element_ty
     |> Seq.map (fn (pm, ctxt'3) =>
          ([], \<^Const>\<open>Trueprop\<close> $ (FTF_head $ pm $ fm), x_term, FT_term, phi,
               load_simpset [fm,pm] ctxt'3)))
  end)

fun gen_FTF prop_i hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val unify_hint = hint_unify_by_type_operator (
            fn Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _ $ _ => F1)
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _) $ _ $ _ $ D $ R $ M $ _ $ p $ f) = [D,R,M,p,f]
        | extract_oprs_from_hint _ = []

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
      val name = if prop_i = 0 then "Functional_Transformation_Functor"
                 else "Functional_Transformation_Functor/" ^ string_of_int prop_i
      val rules = mk_rule_by_guess_or_hint (name, unify_hint, extract_oprs_from_hint, guess_property_FTF, @{thm' \<phi>TA_FTF_rule}, [],
                                            NONE, K reasoning, K NONE, simp)
                                            phi0 hint0 ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail ""
        | SOME (rule'0, _) =>
          let fun set_prem_to_True rule =
                case Thm.prop_of rule
                  of _ (*Trueprop*) $ (_ $ Var v $ _ $ _) =>
                      Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>True\<close>)]) rule
                   | _ => rule
              val rule' = set_prem_to_True rule'0
              
              fun setup_functional_TF cmd lthy =
                let val ((_,[locale_rule']), _) = Variable.import true [rule'] lthy
                    val interp_name = Term.term_name (#term phi0) ^
                                      (if prop_i = 0 then "" else string_of_int prop_i)
                 in case Thm.concl_of locale_rule'
                      of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _)
                            $ Fa $ Fb $ D $ R $ m $ Pr $ pm $ fm) =>
                          cmd ([(\<^locale>\<open>Functional_Transformation_Functor\<close>,
                                ((interp_name, true),
                                (Expression.Positional [SOME Fa, SOME Fb, SOME D, SOME R, SOME m,
                                                        SOME (case Pr of Var _ => \<^Const>\<open>True\<close> | _ => Pr),
                                                        SOME pm, SOME fm],
                                 [])))], []) [] lthy
                            |> Proof.refine_primitive (fn _ => fn th => locale_rule' RS th)
                            |> Proof.global_done_proof
                end
           in thy
           |> Context.mapping (Named_Target.theory_map (setup_functional_TF Interpretation.global_interpretation))
                              (setup_functional_TF Interpretation.sublocale)
          end)
  end

val functional_transformation_functor = accept gen_FTF

end