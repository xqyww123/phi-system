signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val subst_ty : (typ * typ) list -> typ -> typ
val instantiate_phi_to_pair_x : Proof.context -> term * Phi_Type_Algebra.phi_type ->
        typ TVars.table * ctyp TVars.table * Phi_Type_Algebra.phi_type

val separation_homo_I : hint list -> Phi_Type_Algebra.derive
val separation_homo_E : hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*** Separation Homo ***)

(*
fun make_phi_for_pair ctxt0 (x_term0, FT_term0, (phi0:phi_type)) =
  Seq.of_list (separate_type_operator_and_its_non_parameterized_parameter FT_term0)
    |> Seq.map (fn (T_term, F_term) =>
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
  end)*)

fun instantiate_phi_to_pair_x ctxt (T_term0, phi0) =
  let val ([], element_ty0, _) = dest_parameterized_phi_ty (Term.fastype_of T_term0)

      val idx = phi_maxidx_of phi0 ~1 + 1
      val ty_x'dest = Term.add_tvarsT element_ty0 []
      val thy = Proof_Context.theory_of ctxt
      val SS = map (Sign.arity_sorts thy \<^type_name>\<open>prod\<close> o snd) ty_x'dest
      val instTy = fold_index (fn (i, (K, [S1,S2])) =>
                      TVars.add (K, \<^Type>\<open>prod \<open>TVar(("xa",idx+i),S1)\<close> \<open>TVar(("xb",idx+i),S2)\<close>\<close>)
                   ) (ty_x'dest ~~ SS) TVars.empty
      val instTy'= TVars.map (K (Thm.global_ctyp_of thy)) instTy
      val phi'1 = instantiate_phi (instTy', Vars.empty) phi0
   in (instTy, instTy', phi'1)
  end

fun subst_ty redex_residue t =
  case AList.lookup (op =) redex_residue t
    of SOME residue => residue
     | _ => (case t
               of Type(Tname, targs) => Type(Tname, map (subst_ty redex_residue) targs)
                | t' => t')

fun guess_property_SH flag (phi0:phi_type) ctxt =
  let val ((_,FT_term0), ctxt) = fix_phi_term_params (#term phi0) ctxt
   in Seq.of_list (separate_type_operator_and_its_non_parameterized_parameter FT_term0)
  |> Seq.maps (fn (T_term0, F_term0) =>
  let val (instTy, _, phi'1) = instantiate_phi_to_pair_x ctxt (T_term0, phi0)

      val thy = Proof_Context.theory_of ctxt
      val (_, x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val ([], _, ele_model0) = dest_parameterized_phi_ty (Term.fastype_of T_term0)
      
      val (model_ty'1, ele_model'1) = (
              Term_Subst.instantiateT instTy model_ty0,
              Term_Subst.instantiateT instTy ele_model0
            )
      
      val target_sort = if Sign.of_sort thy (model_ty'1, \<^sort>\<open>one\<close>) then \<^sort>\<open>sep_magma_1\<close> else \<^sort>\<open>sep_magma\<close>
      val inst  = Phi_Help.lift_type_sort' thy [(model_ty'1, target_sort), (ele_model'1, target_sort)]
                  handle TYPE _ => raise Automation_Fail ("Fail to guess the property because fail to \
                                    \constrain the type " ^ Syntax.string_of_typ ctxt model_ty'1 ^ " and "
                                    ^ Syntax.string_of_typ ctxt ele_model'1 ^ " by sort \<open>sep_magma\<close>")
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst

      val phi = instantiate_phi (inst',Vars.empty) phi'1
      val subst = Term_Subst.instantiate (instTy, Vars.empty)
               #> Term_Subst.instantiate (inst, Vars.empty)

      val (FT_term, F_term, T_term) = (subst FT_term0, subst F_term0, subst T_term0)
      val x_ty = x_ty0
              |> Term_Subst.instantiateT instTy
              |> Term_Subst.instantiateT inst

      val ([], element_ty, _) = dest_parameterized_phi_ty (Term.fastype_of T_term)

      val target = case element_ty
                     of \<^Type>\<open>prod a b\<close> => (a,b)
                      | _ => error "BUG 5fUVN91qSGOppdg3fOp49A"
      val ((dom,zip), ctxt) = guess_zip_guided flag target (unzip_typ (Context.Proof ctxt) x_ty) ctxt

      val Fa = Term.map_types (subst_ty [(element_ty, fst target)]) F_term
      val Fb = Term.map_types (subst_ty [(element_ty, snd target)]) F_term
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

   in Seq.single ([], HOLogic.Trueprop $ SH, NONE :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end)
  end


fun SHu_reasoner ctxt sequent =
  case PLPR_Exhaustive.reason_exhaustively (SOME 2)
            (ctxt, @{thm' \<phi>TA_reason_rule__simp_NToA} RS sequent)
    of SOME th => th
     | NONE => raise Automation_Fail "\<phi>-LPR reasoning fails"

fun SH_reasoning is_intro phi ctxt =
  default_reasoning true
      (default_reasoning_configure (K (K [])))
      (K (K NONE))
      (fn ctxt => fn sequent => (
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
  let val ctxt0 = Context.proof_of generic
      (*val phi0pr = make_phi_for_pair generic phi0*)
      val parse_hint = parse_hint_has_type_operator_only (
            fn Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, _) $ _ $ _ $ F $ _ $ _ => F
             | Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, _) $ _ $ _ $ F $ _ => F)
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, _) $ _ $ _ $ _ $ D $ z) = [D,z]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, _) $ _ $ _ $ _ $ u) = [u]
        | extract_oprs_from_hint _ = []

      val ind_conv_z = default_ind_conv (
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHz_rewr_IH}) then_conv
                Phi_Conv.meta_alls_conv (fn ctxt =>
                Conv.implies_concl_conv (Conv.implies_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))
                ) Conv.all_conv
               )) ctxt,
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SHz_rewr_C}) then_conv
                Conv.implies_concl_conv (HOLogic.Trueprop_conv (
                  Simplifier.asm_rewrite (Simps.equip ctxt addsimps (#equations phi0))) then_conv
                Phi_Conv.hol_alls_to_meta_alls (fn _ => fn ctm =>
                  conv_hol_imp_to_meta_if_has (Conv.rewr_conv @{thm' Action_Tag_def[symmetric, where A=\<phi>TA_pure_facts]}) ctm
                ) ctxt)
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

      val rules = deriver_framework (if is_intro then "Separation_Homo\<^sub>I" else "Separation_Homo\<^sub>E",
                                     parse_hint, extract_oprs_from_hint, guess_property_SH is_intro,
                                     (if is_intro then @{thm' \<phi>TA_SHz_rule} else @{thm' \<phi>TA_SHu_rule}), [0,~1,~1],
                                     SOME ind_conv, SH_reasoning is_intro, K NONE, simp)
                                    phi0 hint0 ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail "Fail to derive any property"
         | SOME (rule', _) => generic
             |> Phi_Type_Algebra.note_properties phi0
                    [(if is_intro then "Separation_Homo\<^sub>I" else "Separation_Homo\<^sub>E", [rule'])]
             |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.NORMAL_MODE 40 ([],[]) NONE
                                              [Morphism.thm m rule'])
  end

val separation_homo_I = accept_one "Separation_Homo\<^sub>I" (gen_SH true)
val separation_homo_E = accept_one "Separation_Homo\<^sub>E" (gen_SH false)


end
