signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val trans_to_raw_abst : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property  (x_term, T_term, (phi:phi_type)) ctxt =
  let val _ = if #is_recursive phi
              then error "Trans_to_Raw_Abst: I cannot guess the rule for a recursive \<phi>-type\n\
                         \Please manually annotate the expression."
              else ()
      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term
      fun mk_prop r_term ((rev_arg_tys, x_ty, model_ty), T_term) =
        let val arity = length rev_arg_tys
            val T'_term = fold_index (fn (i,_) => fn X => X $ Bound (arity - i)) rev_arg_tys T_term
         in (HOLogic.all_const x_ty $ Abs ("x", x_ty,
              \<^Const>\<open>Action_Tag\<close>
                $ (\<^Const>\<open>Transformation model_ty\<close>
                    $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ T'_term)
                    $ (\<^Const>\<open>ExSet model_ty model_ty\<close> $ Abs ("y", model_ty,
                          \<^Const>\<open>Subjection model_ty\<close>
                            $ (\<^Const>\<open>\<phi>Type model_ty model_ty\<close> $ Bound 0 $ \<^Const>\<open>Itself model_ty\<close>)
                            $ (r_term $ Bound 1 $ Bound 0)))
                    $ \<^Const>\<open>True\<close>)
                $ (\<^Const>\<open>to \<open>Term.fastype_of \<^Const>\<open>Itself model_ty\<close>\<close>\<close> $ \<^Const>\<open>Itself model_ty\<close>)))
         |> fold (fn T => fn X => HOLogic.all_const T $ Abs ("A", T, X)) rev_arg_tys
        end
      val r_types = map (fn ((_,x,m),_) => x --> m --> HOLogic.boolT) T_params
      val r_fixes = Name.invent_names (Variable.names_of ctxt) "r" r_types
      val ctxt' = Variable.add_fixes_direct (map fst r_fixes) ctxt
      val ants = map2 (mk_prop o Free) r_fixes T_params 
      val idx = phi_maxidx_of phi ~1 + 1
      val prop = mk_prop (Var(("r",idx), x_ty --> model_ty --> HOLogic.boolT)) (([], x_ty, model_ty), T_term)
   in Seq.single (ants, HOLogic.Trueprop $ prop, x_term, T_term, phi, ctxt')
  end

fun reasoning phi ctxt =
  let (*val extract_prem =
        if def_contains_satisfaction phi
        then (fn _ => fn th => [])
        else K (K [])*)
   in gen_abstract_constraint_guided_reasoning (K NONE) (K (K [])) (fn ctxt => fn sequent => (
         (case Thm.major_prem_of sequent
            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ (
                    Const(\<^const_name>\<open>Transformation\<close>, _)
                        $ X $ _ $ _))
                 => chk_unfolded phi X
             | _ => ()) ;
          case PLPR_Exhaustive.reason_exhaustively (SOME 2) (ctxt, @{thm' \<phi>TA_TF_rule_step} RS sequent)
            of SOME th => th
             | NONE => raise Automation_Fail "\<phi>-LPR reasoning fails"
      )) ctxt
  end

fun instantiate_the_var var ctxt sequent0 =
  let val (x_ty, y_ty) = case snd var
                           of \<^Type>\<open>fun x_ty \<^Type>\<open>fun y_ty \<^Type>\<open>bool\<close>\<close>\<close> => (x_ty, y_ty)
                            | _ => error "BUG qC2wYScnQXiFvdGaUF/mBA"
      val [x,y] = Name.invent_names (Variable.names_of ctxt) "x" [x_ty, y_ty]
               |> map Free

      fun normalize_Ex ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
              (Conv.arg1_conv (normalize_Ex ctxt) then_conv
               Conv.arg_conv (normalize_Ex ctxt)) ctm
           | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
              Conv.arg_conv (normalize_Ex ctxt) ctm
           | Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
              Phi_Conv.hol_all_conv (normalize_Ex o snd) ctxt ctm
           | Const(\<^const_name>\<open>special_Ex\<close>, \<^Type>\<open>fun \<^Type>\<open>fun T _\<close> _\<close>) $ _ =>
                if T = y_ty
                then (Phi_Conv.quant_conv \<^const_name>\<open>special_Ex\<close> (fn (_, ctxt) => fn ctmxx =>
                        Simplifier.rewrite (Simplifier.clear_simpset ctxt
                          addsimps @{thms' HOL.imp_conjR[symmetric] HOL.simp_thms}) ctmxx) ctxt) ctm
                else let
                  fun norm_Ex ctxt ctm =
                    case Thm.term_of ctm
                      of Const(\<^const_name>\<open>special_Ex\<close>, _) $ (Abs(_,_, Const(\<^const_name>\<open>HOL.All\<close>, _) $ _)) =>
                          (Phi_Conv.move_sp_Ex_inside_All ctxt then_conv
                           Phi_Conv.hol_all_conv (normalize_Ex o snd) ctxt) ctm
                       | _ => error "Deriving Trans_to_Raw_Abst fails: Cannot normalize the generated proof oblgiation"
                   in (Phi_Conv.quant_conv \<^const_name>\<open>special_Ex\<close> (fn (_, ctxt) =>
                          Simplifier.rewrite (Simplifier.clear_simpset ctxt
                                addsimps @{thms' HOL.all_conj_distrib[symmetric] all_simps(3-6)[symmetric]
                                                 "_all_simps_plus_" HOL.simp_thms}
                                addsimprocs [\<^simproc>\<open>NO_MATCH\<close>])) ctxt
                       then_conv Drule.beta_eta_conversion
                       then_conv norm_Ex ctxt) ctm
                  end
           | _ => Conv.all_conv ctm

      val sequent = Conv.gconv_rule (HOLogic.Trueprop_conv (PLPR_Syntax.premise_tag_conv (
              normalize_Ex ctxt
            ))) 1 sequent0
      val oblg = case Thm.prop_of sequent
                   of \<^Const>\<open>Pure.imp\<close> $ (\<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_COLLECT\<close> $ X)) $ _
                        => X
                    | _ => error "BUG zfkezUm3Rm62IQTK0kglKQ"

      fun mk_disj_inst concls (quants, prems) =
        fold (fn (N,ty) => fn X => HOLogic.exists_const ty $ Abs(N,ty,X))
          quants (Phi_Help.list_mk_conj (prems @ concls))

      fun mk_conj_inst concls (quants, prems) =
        Phi_Help.list_mk_conj concls
          |> fold (fn P => fn X => HOLogic.imp $ P $ X) prems
          |> fold (fn (N,ty) => fn X => HOLogic.exists_const ty $ Abs(N,ty,X)) quants
      fun mk_conj_inst' [] _ rets = rets
        | mk_conj_inst' concls qp rets = mk_conj_inst concls qp :: rets

      val has_the_var = Term.exists_subterm (fn Var v' => v' = var | _ => false)

      fun pass_conjs qp concls_meet (\<^Const>\<open>HOL.conj\<close> $ A $ B)
            = pass_conjs qp (pass_conjs qp concls_meet A) B
        | pass_conjs _ (concls,meet) (Var v' $ _ $ _)
            = if v' = var then (concls,true)
              else error "Phi_Type_Algebra_Derivers.instantiate_the_var: unexpected schematic variables"
        | pass_conjs _ (concls,meet) P
            = (fold_aterms (fn Var v' =>
                if v' = var then raise Automation_Fail "fail to infer the transformation relation: fail to normalize the obligation"
                else error "Phi_Type_Algebra_Derivers.instantiate_the_var: unexpected schematic variables"
                  | _ => I) P () ;
               (P::concls, meet))

      fun inst_body ret (quants, prems) (\<^Const>\<open>HOL.implies\<close> $ P $ X)
            = inst_body ret (quants, P::prems) X
        | inst_body ret (quants, prems) (\<^Const>\<open>HOL.All _\<close> $ Abs (N, ty, X))
            = inst_body ret ((N,ty)::quants, map (Term.incr_boundvars 1) prems) X
        | inst_body (disj, conj) qp P
            = case pass_conjs qp ([],false) P
                of (concls, true)  => (mk_disj_inst concls qp :: disj, conj)
                 | (concls, false) => (disj, mk_conj_inst concls qp :: conj)

      fun inst_single ret (quants, prems) (\<^Const>\<open>HOL.implies\<close> $ P $ X)
            = inst_single ret (quants, P::prems) X
        | inst_single ret (quants, prems) (\<^Const>\<open>HOL.All _\<close> $ Abs (N, ty, X))
            = inst_single ret ((N,ty)::quants, map (Term.incr_boundvars 1) prems) X
        | inst_single ret qp (\<^Const>\<open>special_Ex _\<close> $ Abs (_, ty, X))
            = if ty = y_ty
              then inst_body ret qp (Term.subst_bounds ([y], X))
              else error "BUG rmAIEDSmSJ6Y7ZuviDwskw"
        | inst_single (disj, conj) qp P
            = (disj, mk_conj_inst [P] qp :: conj)

      fun inst_toplevel ret (\<^Const>\<open>conj\<close> $ (\<^Const>\<open>HOL.All _\<close> $ Abs (_, ty, X)) $ Y)
            = if ty = x_ty
              then inst_toplevel (inst_single ret ([],[]) (Term.subst_bounds ([x], X))) Y
              else error "BUG rmAIEDSmSJ6Y7ZuviDwskw"
        | inst_toplevel ret (\<^Const>\<open>HOL.All _\<close> $ Abs (_, ty, X))
            = if ty = x_ty
              then inst_single ret ([],[]) (Term.subst_bounds ([x], X))
              else error "BUG rmAIEDSmSJ6Y7ZuviDwskw"
        | inst_toplevel ret \<^Const>\<open>True\<close> = ret
        | inst_toplevel _ _ = error "BUG rmAIEDSmSJ6Y7ZuviDwskw"

      val (disj,conj) = inst_toplevel ([],[]) oblg
      val inst = Term.lambda x (Term.lambda y (
                    Phi_Help.list_mk_conj (Phi_Help.list_mk_disj disj :: conj)))
              |> Thm.cterm_of ctxt
   in Thm.instantiate (TVars.empty, Vars.make [(var, inst)]) sequent
  end

fun solver (phi, ctxt, sequent) =
  case Thm.concl_of sequent
    of _ (*Trueprop*) $ (\<^Const>\<open>All _\<close> $ Abs (_, _, \<^Const>\<open>Action_Tag\<close> $
           (\<^Const>\<open>Transformation _\<close> $ _
               $ (\<^Const>\<open>ExSet _ _\<close> $ Abs (_, _,
                   \<^Const>\<open>Subjection _\<close> $ _ $ X ))
               $ _)
           $ _))
         => (case X of Var v $ _ $ _ =>
                          SOME ( instantiate_the_var v ctxt sequent
                            |> oblg_solver (#proof_id phi ^ "/Trans_to_Raw_Abst") ctxt)
                     | _ => NONE)
     | _ => error "Internal bug"


fun gen_trans_to_raw_abst hint00 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val hint0 = Option.map (quantifies_abstract_object (
            let fun target (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = target X
                  | target (\<^Const>\<open>Transformation _\<close> $ (\<^Const>\<open>\<phi>Type _ _\<close> $ X $ T) $ _ $ _) =
                        if Term.exists_subterm (fn x => x = X) T
                        then error "Fail to infer the implication when the \<phi>-type depends on its abstract object."
                        else SOME X
             in target
            end
            )) hint00

      val unify_hint = hint_unify_general (fn hint => fn (_,T) =>
            let fun extract (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = extract X
                  | extract (Const(\<^const_name>\<open>All\<close>, _) $ X) = extract X
                  | extract (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = extract X
                  | extract (Abs (_, _, X)) = extract X
                  | extract (\<^Const>\<open>Action_Tag\<close>
                              $ (\<^Const>\<open>Transformation _\<close>
                                  $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ T)
                                  $ (\<^Const>\<open>ExSet _ _\<close> $ Abs (_, _, (\<^Const>\<open>Subjection _\<close>
                                        $ (\<^Const>\<open>\<phi>Type _ _\<close> $ _ $ itself')
                                        $ _)))
                                  $ _)
                              $ (\<^Const>\<open>to _\<close> $ itself))
                      = (T, (itself, itself'))
                val (T', pair) = extract (Logic.strip_imp_concl hint)
             in (T',T) :: pair :: (map (snd o extract) (Logic.strip_imp_prems hint))
            end)
      val ind_conv = default_ind_conv (
            fn ctxt => fn phi =>
                Conv.rewr_conv @{thm' \<phi>TA_TrRA_rewr},
            fn ctxt => fn phi =>
                Conv.rewr_conv @{thm' \<phi>TA_TrRA_rewr} then_conv
                Conv.implies_concl_conv (Phi_Conv.action_tag_conv (
                  Phi_Syntax.transformation_conv
                    (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)))
                    Conv.all_conv Conv.all_conv)))
      fun simp (_, ctxt) rule = rule
         |> Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt => HOLogic.Trueprop_conv (Phi_Conv.hol_all_conv (fn (_, ctxt) =>
              Phi_Conv.action_tag_conv (Phi_Syntax.transformation_conv Conv.all_conv
                (Phi_Syntax.ExSet_conv (fn (bvar, ctxtxx) =>
                  let val turn_bvar_eq = Drule.infer_instantiate ctxtxx [(("b",0),bvar)] @{thm' HOL.eq_commute}
                   in Phi_Syntax.Subjection_conv Conv.all_conv (
                        Simplifier.rewrite (ctxtxx addsimps [turn_bvar_eq, @{thm special_Ex_def}]
                                              |> Simplifier.add_cong @{thm HOL.conj_cong}))
                  end) ctxt)
                Conv.all_conv)
            ) ctxt)) ctxt)
         |> (fn rule => (rule RS' (ctxt, @{thm' spec})))
      val rules = mk_rule_by_guess_or_hint ("Trans_to_Raw_Abst", unify_hint, guess_property,
                                            @{thm' \<phi>TA_TrRA_rule}, [0],
                                            SOME ind_conv, reasoning, solver, simp)
                                           phi0 hint0 ctxt0
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 90
                                              ([],[]) NONE [Morphism.thm m rule])
        |> Phi_Type_Algebra.note_properties phi0 [("Trans_to_Raw_Abst", [rule])]
    | _ => raise Automation_Fail ""
  end

val trans_to_raw_abst = accept_one "Trans_to_Raw_Abst" gen_trans_to_raw_abst

end

