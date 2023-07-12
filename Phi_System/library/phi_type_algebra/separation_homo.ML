signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val separation_homo_I : hint list -> Phi_Type_Algebra.derive
val separation_homo_E : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*** Separation Homo ***)

fun guess_property_SH flag (x_term0, FT_term0, (phi0:phi_type)) ctxt =
  let val (T_ty0 :: _, x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val ([],element_ty0, ele_model0) = dest_parameterized_phi_ty T_ty0
      val inst0  = Vartab.empty
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (model_ty0, \<^sort>\<open>sep_magma\<close>)
                |> Phi_Help.lift_type_sort (Proof_Context.theory_of ctxt) (ele_model0, \<^sort>\<open>sep_magma\<close>)
                   handle TYPE _ => raise Automation_Fail
      val inst = Phi_Help.tyenv_to_tvars_table_no_c inst0
      val inst' = TVars.map (K (Thm.ctyp_of ctxt)) inst
      val phi = instantiate_phi (inst',Vars.empty) phi0
      val subst = Term_Subst.instantiate (inst, Vars.empty)
      val (x_term, FT_term) = (subst x_term0, subst FT_term0)

      val (T_ty :: _, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([], element_ty, _) = dest_parameterized_phi_ty T_ty

      val target = case element_ty
                     of \<^Type>\<open>prod a b\<close> => (a,b)
                      | _ => error "Internal bug #8522d8e9-57a1-4ad9-800e-1c1222fcabfc"
      val ((dom,zip), ctxt) = guess_zip_guided flag target (unzip_typ ctxt x_ty) ctxt
      val F_term = (case FT_term of F $ _ => F
                                  | _ => error "Internal bug: Not a Type Operator")

      fun subst_ty residue t =
            if t = element_ty then residue
            else case t
                   of Type(Tname, targs) => Type(Tname, map (subst_ty residue) targs)
                    | t' => t'

      val Fa = Term.map_types (subst_ty (fst target)) F_term
      val Fb = Term.map_types (subst_ty (snd target)) F_term
      val SH = (case (Term.fastype_of Fa, Term.fastype_of Fb)
                  of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>set b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>set d\<close>\<close>\<close>,
                      \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>set _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>set _\<close>\<close>\<close>) =>
                    (if flag
                     then \<^Const>\<open>Separation_Homo\<^sub>I a b c d e f x_ty\<close>
                       $ Fa $ Fb $ F_term
                       $ (\<^Const>\<open>Collect \<^Type>\<open>prod c f\<close>\<close> $ (\<^Const>\<open>case_prod c f \<^Type>\<open>bool\<close>\<close> $ dom))
                       $ zip
                     else \<^Const>\<open>Separation_Homo\<^sub>E a b c d e f x_ty\<close>
                       $ Fa $ Fb $ F_term $ zip)
                   | _ => error "Internal bug")
   in Seq.single ([], HOLogic.Trueprop $ SH, x_term, FT_term, phi, ctxt)
  end

fun make_phi_for_pair ctxt0 (phi0 : phi_type) =
  let val (rev_ty_args, _, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val ([],element_ty,_) = dest_parameterized_phi_ty (hd rev_ty_args)
      val idx = phi_maxidx_of phi0 ~1 + 1
      val ty_x'dest = Term.add_tvarsT element_ty []
      val thy0 = Context.theory_of ctxt0
      val SS = map (Sign.arity_sorts thy0 \<^type_name>\<open>prod\<close> o snd) ty_x'dest
      val instTy = fold_index (fn (i, (K, [S1,S2])) =>
                      TVars.add (K, \<^Type>\<open>prod \<open>TVar(("xa",idx+i),S1)\<close> \<open>TVar(("xb",idx+i),S2)\<close>\<close>)
                   ) (ty_x'dest ~~ SS) TVars.empty
      val instTy'= TVars.map (K (Thm.global_ctyp_of thy0)) instTy
      val phi = instantiate_phi (instTy', Vars.empty) phi0
   in phi
  end

fun SHu_reasoner ctxt sequent =
  case PLPR_Exhaustive.reason_exhaustively (SOME 2)
            (ctxt, @{thm' \<phi>TA_SHu_rule_step} RS sequent)
    of SOME th => th
     | NONE => raise Automation_Fail

fun SH_reasoning is_intro phi ctxt =
  gen_abstract_constraint_guided_reasoning (K NONE) (K (K [])) (fn ctxt => fn sequent => (
         (case Thm.major_prem_of sequent
            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Transformation\<close>, _)
                        $ (Const(\<^const_name>\<open>times\<close>, _) $ X1 $ X2) $ _ $ _)
                 => (chk_unfolded phi X1; chk_unfolded phi X2)
             | _ => ()) ;
          if is_intro
          then ToA_reasoner phi ctxt sequent
          else SHu_reasoner ctxt sequent
      )) ctxt

fun gen_SH is_intro hint0 (phi0 : phi_type) generic =
  let val _ = assert_first_parameter_is_type "Separation_Homo" (Term.fastype_of (#term phi0))
      val ctxt0 = Context.proof_of generic
      val phi0pr = make_phi_for_pair generic phi0
      val unify_hint_SH = hint_unify_by_type_operator (
            fn Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, _) $ _ $ _ $ F $ _ => F
             | Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, _) $ _ $ _ $ F $ _ => F
             | _ => raise TERM ("",[]))
      val ind_conv_z = default_ind_conv (
            fn ctxt => fn phi =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHz_rewr_IH}) then_conv
                Phi_Conv.meta_alls_conv (fn ctxt =>
                Conv.implies_concl_conv (Conv.implies_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                ) Conv.all_conv
               )) ctxt,
            fn ctxt => fn phi =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHz_rewr_C}) then_conv
                Conv.implies_concl_conv (
                  HOLogic.Trueprop_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                ))
            )
      val ind_conv_u = default_ind_conv (
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHu_rewr_IH}),
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHu_rewr_C}) then_conv
                Conv.implies_concl_conv (
                  HOLogic.Trueprop_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                ))
            )
      val ind_conv = if is_intro then ind_conv_z else ind_conv_u
      fun simp (_, ctxt) =
        if is_some hint0 then I
        else Conv.fconv_rule (
               Phi_Conv.hhf_concl_conv (fn ctxt =>
                 let val sctxt = ctxt addsimps @{thms special_Ex_def}
                  in Conv.arg_conv (Conv.combination_conv
                        (Conv.arg_conv (Simplifier.rewrite sctxt))
                        (Simplifier.rewrite sctxt))
                 end
             ) ctxt)

      val rules = mk_rule_by_guess_or_hint (if is_intro then "Separation_Homo\<^sub>I" else "Separation_Homo\<^sub>E",
                                            unify_hint_SH, guess_property_SH is_intro,
                                            (if is_intro then @{thm' \<phi>TA_SHz_rule} else @{thm' \<phi>TA_SHu_rule}), [0,~1,~1],
                                            SOME ind_conv, SH_reasoning is_intro, K NONE, simp)
                                           phi0pr hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail
         | SOME (rule', _) => generic
             |> Phi_Type_Algebra.note_properties phi0
                    [(if is_intro then "Separation_Homo\<^sub>I" else "Separation_Homo\<^sub>E", [rule'])]
             |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_intro_rule (#pos phi0) Phi_Reasoner.NORMAL 40 ([],[]) NONE
                                              [Morphism.thm m rule'])
  end

val separation_homo_I = accept_one "Separation_Homo\<^sub>I" (gen_SH true)
val separation_homo_E = accept_one "Separation_Homo\<^sub>E" (gen_SH false)


end
