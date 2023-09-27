signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val transformation_functor            : quiet -> deriving_instruction list -> Phi_Type_Algebra.derive
val functional_transformation_functor : quiet -> deriving_instruction list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers


(*** Transformation Functor ***)

fun mk_TF's_two_instantiations ctxt0 (FT_term0, phi0) =
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
      val (U_name :: param_names', ctxt') = Variable.variant_fixes ("U" :: map fst params) ctxt'1
      val params' = map2 (fn N => fn (_,T) => Free(N,T)) param_names' params
      val inst = Frees.make (params ~~ params')
      val F'_term = Term_Subst.instantiate_frees (TFrees.empty, inst) F'1_term
      val U_term = Free(U_name, Term_Subst.instantiateT_frees inst_ty T_ty)
      

      val ants = map2 (fn (N,T) => fn p' =>
                      \<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_GUARD\<close> $ (\<^Const>\<open>HOL.eq T\<close> $ Free(N,T) $ p')
                 ) params params'

   in (ants, F_term, F'_term, T_term, U_term, inst_ty, phi, ctxt')
  end)
  end

fun guess_property_TF phi0 ctxt =
  let val ((_,FT_term), ctxt) = fix_phi_term_params phi0 ctxt
   in mk_TF's_two_instantiations ctxt (FT_term, phi0)
   |> Seq.maps (fn (ants, F_term, F'_term, T_term, U_term, inst_ty, phi, ctxt') =>
  let val (_, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty (Term.fastype_of T_term)

      val TF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                       of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                           \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                          \<^Const>\<open>Transformation_Functor a b c d e f\<close> $ F_term $ F'_term $ T_term $ U_term
                        | _ => error "BUG")
      val target_ty = Term_Subst.instantiateT_frees inst_ty
      val Rng = Abs("_", x_ty, \<^Const>\<open>top \<^Type>\<open>set \<open>target_ty element_ty\<close>\<close>\<close>)
   in guess_set_opr ctxt' x_ty element_ty
   |> Seq.maps (fn (D_term, ctxt'2) =>
        guess_rel_mapper (fn (ty1,ty2) =>
            if ty1 = ty2 then \<^Const>\<open>HOL.eq ty1\<close>
            else raise Automation_Fail (fn () => let open Pretty in
                    [paragraph (text "Fail to guess the relation mapper for" @
                                [brk 1, Syntax.pretty_typ ctxt'2 x_ty])]
                 end)
        ) target_ty ctxt'2 x_ty element_ty
   |> Seq.map (fn (rel_mapper, ctxt'3) =>
        (ants, \<^Const>\<open>Trueprop\<close> $ (TF_head $ D_term $ Rng $ rel_mapper),
         NONE :: parse_inst_params_from_phi_term (F_term $ Bound 42 (*whatever*)), phi, ctxt'3)))
  end)
  end


local

fun TF_reasoning phi ctxt = default_reasoning true
      default_reasoning_configure
      (K (K NONE))
      (exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__\<A>_simp_NToA} (K (chk_unfolded' ctxt phi)))
      phi ctxt

fun gen_TF (der_id, name) instruction ctxt0 (phi0 : phi_type) generic =
  let       (*|> def_contains_satisfaction phi0 ? Context.proof_map (
                    Phi_Reasoners.Is_Premise_of_Obligation.add 123
                      (fn \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ _ $ _ $ _ $ _) => SOME true
                        | X => NONE)) *)
      val parse_hint = parse_hint (
              fn (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _) => F1)
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ _ $ _ $ _ $ _ $ D $ R $ M) = [D,R,M]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (
              K (K (Conv.rewr_conv @{thm \<phi>TA_TF_rewr_C} then_conv
                    Conv.implies_concl_conv (Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv))),
              fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_TF_rewr_C} then_conv
                  Conv.implies_concl_conv (
                      Phi_Reasoners.asm_rewrite true (Expansion.equip ctxt addsimps (#equations phi0)) then_conv
                      Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv))
      val simp = if is_some instruction then K I
                 else simplifier_by_cong @{thms' \<phi>TA_FT_deriver_cong}
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property_TF, @{thm' \<phi>TA_TF_rule},
                                      [(K (SOME [0,~1]), ind_conv, TF_reasoning)],
                                      K NONE, simp)
                                     phi0 (Option.map fst instruction) ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
        | SOME (rule', _) =>
          let (*fun set_prem_to_True rule =
                case Thm.prop_of rule
                  of _ (*Trueprop*) $ (_ $ Var v) =>
                      Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>True\<close>)]) rule
                   | _ => rule
              val rule'2 = PLPR_Syntax.contract_leading_antecedents true (Thm.nprems_of rule') ctxt0 rule'
              val locale_rule = (rule'2 RS' (ctxt0, @{thm' Transformation_Functor_L.intro}))
                              |> (fn th => case Thm.nprems_of th
                                             of 0 => set_prem_to_True th
                                              | 1 => Seq.hd (Thm.assumption (SOME ctxt0) 1 th)
                                              | _ => error "BUG")

                
              fun setup_locale cmd lthy =
                let val ((_,[locale_rule']), _) = Variable.import true [locale_rule] lthy
                    val interp_name = suffix_name_by_index der_id (Term.term_name (#term phi0))
                 in case Thm.concl_of locale_rule'
                      of \<^Const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Transformation_Functor_L\<close>, _)
                            $ Fa $ Fb $ D $ R $ m $ Pr) =>
                    cmd ([(\<^locale>\<open>Transformation_Functor_L\<close>, ((interp_name, true),
                          (Expression.Positional [SOME Fa, SOME Fb, SOME D, SOME R, SOME m,
                                                  SOME (case Pr of Var _ => \<^Const>\<open>True\<close> | _ => Pr)],
                           [])))], []) [] lthy
                      |> Proof.refine_primitive (fn _ => fn th => locale_rule' RS th)
                      |> Proof.global_done_proof
                end*)
           in generic
           |> note_properties_s phi0 [(name, [rule'])]
           |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE
                                        (the_default @{reasoner_group %ToA_derived_one_to_one_functor}
                                                     (Option.mapPartial snd instruction))
                                        ([],[]) NONE [Morphism.thm m rule'])
         (*|> Context.mapping (Named_Target.theory_map (setup_locale Interpretation.global_interpretation))
                              (setup_locale Interpretation.sublocale)*)
           |> pair [rule']
          end)
  end

in

val transformation_functor = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Transformation_Functor") gen_TF

end

(** Functional Transformation Functor **)

fun guess_property_FTF phi0 ctxt0 =
  let val ((_, FT_term), ctxt0) = fix_phi_term_params phi0 ctxt0
   in mk_TF's_two_instantiations ctxt0 (FT_term, phi0)
   |> Seq.maps (fn (ants, F_term, F'_term, T_term, U_term, inst_ty, phi, ctxt) => let
      val (_, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([],element_ty,_) = dest_parameterized_phi_ty (Term.fastype_of T_term)

      val FTF_head = (case (Term.fastype_of F_term, Term.fastype_of F'_term)
                        of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                            \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                           \<^Const>\<open>Functional_Transformation_Functor a b c d e f\<close> $ F_term $ F'_term $ T_term $ U_term
                              $ Var(("D",0), c --> \<^Type>\<open>set a\<close>)
                              $ Var(("R",0), c --> \<^Type>\<open>set e\<close>)
                         | _ => error "BUG")
      val target_ty = Term_Subst.instantiateT_frees inst_ty
   in guess_func_mapper target_ty ctxt x_ty element_ty
   |> Seq.maps (fn (fm, ctxt'2) =>
        guess_pred_mapper ctxt'2 x_ty element_ty
     |> Seq.map (fn (pm, ctxt'3) =>
          (ants, \<^Const>\<open>Trueprop\<close> $ (FTF_head $ Abs ("f", element_ty --> target_ty element_ty, pm)
                                             $ Abs ("f", element_ty --> target_ty element_ty,
                                                  Abs ("P", element_ty --> HOLogic.boolT, fm $ Bound 1))),
           NONE :: parse_inst_params_from_phi_term (F_term $ Bound 42), phi,
           load_simpset [fm,pm] ctxt'3)))
  end)
  end

fun gen_FTF (der_id,name) instruction ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (
            fn Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _ $ _ => F1)
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Functional_Transformation_Functor\<close>, _) $ _ $ _ $ _ $ D $ R $ M $ p $ f) = [D,R,M,p,f]
        | extract_oprs_from_hint _ = []

      fun reasoning phi ctxt = exhaustive_PLPR_reasoner NONE (K (chk_unfolded' ctxt phi)) ctxt
      val simp = if is_some instruction then K I
                 else simplifier_by_cong @{thms' \<phi>TA_FTF_deriver_cong}
    (*fun simp (_, ctxt) thm =
        if is_some instruction then thm
        else Conv.fconv_rule (
                Phi_Conv.hhf_concl_conv (fn ctxt => 
                  let val sctxt = ctxt addsimps @{thms special_Ex_def}
                   in HOLogic.Trueprop_conv (Conv.combination_conv
                        (Conv.arg_conv (Simplifier.rewrite sctxt))
                        (Simplifier.rewrite sctxt))
                  end
             ) ctxt) thm*)
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property_FTF, @{thm' \<phi>TA_FTF_rule},
                                      [(K NONE, K (K I), reasoning)], K NONE, simp)
                                    phi0 (Option.map fst instruction) ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
        | SOME (rule, _) =>
          let (*fun set_prem_to_True rule =
                case Thm.prop_of rule
                  of _ (*Trueprop*) $ (_ $ Var v $ _ $ _) =>
                      Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>True\<close>)]) rule
                   | _ => rule
              val rule' = set_prem_to_True rule'0
              
              fun setup_functional_TF cmd lthy =
                let val ((_,[locale_rule']), _) = Variable.import true [rule'] lthy
                    val interp_name = suffix_name_by_index der_id (Term.term_name (#term phi0))
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
                end*)
           in thy
           |> note_properties_s phi0 [(name, [rule])]
           |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE
                                        (the_default @{reasoner_group %ToA_derived_one_to_one_functor}
                                                     (Option.mapPartial snd instruction))
                                        ([],[]) NONE [Morphism.thm m rule])
           |> pair [rule]
          end)
  end

val functional_transformation_functor = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Functional_Transformation_Functor") gen_FTF

end