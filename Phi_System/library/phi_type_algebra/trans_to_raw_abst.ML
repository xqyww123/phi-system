signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val trans_to_raw_abst : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun guess_property  (x_term, T_term, (phi:phi_type)) ctxt =
  let val _ = if #is_recursive phi
              then error "Trans_to_Raw_Abst: I cannot guess the rule for a recursive \<phi>-type\n\
                         \Please manually annotate the rule."
              else ()
      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term
      fun mk_prop r_term ((rev_arg_tys, x_ty, model_ty), T_term) =
            HOLogic.all_const x_ty $ Abs ("x", x_ty,
              \<^Const>\<open>Action_Tag\<close>
                $ (\<^Const>\<open>Transformation model_ty\<close>
                    $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ T_term)
                    $ (\<^Const>\<open>ExSet model_ty model_ty\<close> $ Abs ("y", model_ty,
                          \<^Const>\<open>Subjection model_ty\<close>
                            $ (\<^Const>\<open>\<phi>Type model_ty model_ty\<close> $ Bound 0 $ \<^Const>\<open>Itself model_ty\<close>)
                            $ (r_term $ Bound 1 $ Bound 0)))
                    $ \<^Const>\<open>True\<close>)
                $ (\<^Const>\<open>to model_ty model_ty\<close> $ \<^Const>\<open>Itself model_ty\<close>))
      val r_types = map (fn ((_,x,m),_) => x --> m --> HOLogic.boolT) T_params
      val r_fixes = Name.invent_names (Variable.names_of ctxt) "r" r_types
      val ctxt' = Variable.add_fixes_direct (map fst r_fixes) ctxt
      val ants = map2 (mk_prop o Free) r_fixes T_params 
      val idx = phi_maxidx_of phi ~1 + 1
      val prop = mk_prop (Var(("r",idx), x_ty --> model_ty --> HOLogic.boolT)) ((rev_arg_tys, x_ty, model_ty), T_term)
   in Seq.single (ants, HOLogic.Trueprop $ prop, x_term, T_term, phi, ctxt')
  end

fun reasoning phi ctxt =
      gen_abstract_constraint_guided_reasoning (K NONE) (fn ctxt => fn sequent => (
         (case Thm.major_prem_of sequent
            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ (
                    Const(\<^const_name>\<open>Transformation\<close>, _)
                        $ X $ _ $ _))
                 => chk_unfolded phi X
             | _ => ()) ;
          case PLPR_Exhaustive.reason_exhaustively (SOME 2) (ctxt, @{thm' \<phi>TA_TF_rule_step} RS sequent)
            of SOME th => th
             | NONE => raise Automation_Fail
      )) ctxt

fun gen_trans_to_raw_abst hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val unify_hint = hint_unify_by_type_operator (
            fn _ (*All*) $ (Abs (_, _,
                  _ (*Action_Tag*) $ (_ (*trans*) $ (_ (*\<phi>-Type*) $ _ $ T) $ _ $ _) $ _))
                 => T
             | _ => raise TERM ("",[]))
      val ind_conv = default_ind_conv (
            fn ctxt => fn phi =>
                Conv.rewr_conv @{thm' \<phi>TA_TrRA_rewr},
            fn ctxt => fn phi =>
                Conv.rewr_conv @{thm' \<phi>TA_TrRA_rewr} then_conv
                Conv.implies_concl_conv (Phi_Conv.action_tag_conv (
                  Phi_Syntax.transformation_conv
                    (Simplifier.rewrite (Simps.equip ctxt addsimps (#equations phi0)))
                    Conv.all_conv Conv.all_conv)))
      fun simp (_, ctxt) rule =
        (rule RS' (ctxt, @{thm' spec}))
         |> Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt => HOLogic.Trueprop_conv (
              Phi_Conv.action_tag_conv (Phi_Syntax.transformation_conv Conv.all_conv
                (Phi_Syntax.ExSet_conv (fn (_, ctxt) =>
                    Phi_Syntax.Subjection_conv Conv.all_conv (
                        Simplifier.rewrite (ctxt addsimps @{thms special_Ex_def})
                      )) ctxt)
                Conv.all_conv)
            )) ctxt)
      val rules = mk_rule_by_guess_or_hint ("Trans_to_Raw_Abst", unify_hint, guess_property,
                                            @{thm' \<phi>TA_TrRA_rule}, [0],
                                            SOME ind_conv, reasoning, K NONE, simp)
                                           phi0 hint0 ctxt0
   in Seq.pull rules; thy
  end

val trans_to_raw_abst = accept_one "Trans_to_Raw_Abst" gen_trans_to_raw_abst

end

