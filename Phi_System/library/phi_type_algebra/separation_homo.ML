signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val subst_ty : (typ * typ) list -> typ -> typ
val instantiate_phi_to_pair_x : Proof.context -> term * Phi_Type.phi_type ->
        typ TVars.table * ctyp TVars.table * Phi_Type.phi_type

val separation_homo_I : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val separation_homo_E : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

(*** Separation Homo ***)

(*
fun make_phi_for_pair ctxt0 (x_term0, FT_term0, (phi0:phi_type)) =
  Seq.of_list (separate_tyopr_and_its_non_parameterized_typ_param FT_term0)
    |> Seq.map (fn (T_term, F_term) =>
  let val (rev_ty_args, _, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val ([],element_ty,_) = dest_parameterized_phi_ty (hd rev_ty_args)
      val idx = maxidx_of_phi phi0 ~1 + 1
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

      val idx = maxidx_of_phi phi0 ~1 + 1
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
  let val ((_,FT_term0), ctxt) = fix_phi_term_params phi0 ctxt
   in separate_tyopr_and_its_non_parameterized_typ_param [] FT_term0
  |> Seq.maps (fn (T_term0, F_term0) =>
  let val (instTy, _, phi'1) = instantiate_phi_to_pair_x ctxt (T_term0, phi0)

      val thy = Proof_Context.theory_of ctxt
      val (_, x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val ([], _, ele_model0) = dest_parameterized_phi_ty (Term.fastype_of T_term0)
      
      val (model_ty'1, ele_model'1) = (
              Term_Subst.instantiateT instTy model_ty0,
              Term_Subst.instantiateT instTy ele_model0
            )

      val inst  = lift_types_sort thy [(model_ty'1, \<^sort>\<open>sep_magma_1\<close>), (ele_model'1, \<^sort>\<open>sep_magma_1\<close>)]
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
      val ([T_name, U_name], ctxt) = Variable.variant_fixes ["T","U"] ctxt
      val T = Free (T_name, subst_ty [(element_ty, fst target)] (Term.fastype_of T_term))
      val U = Free (U_name, subst_ty [(element_ty, snd target)] (Term.fastype_of T_term))
      val SH = (case (Term.fastype_of Fa, Term.fastype_of Fb)
                  of (\<^Type>\<open>fun \<^Type>\<open>fun a \<^Type>\<open>BI b\<close>\<close> \<^Type>\<open>fun c \<^Type>\<open>BI d\<close>\<close>\<close>,
                      \<^Type>\<open>fun \<^Type>\<open>fun e \<^Type>\<open>BI _\<close>\<close> \<^Type>\<open>fun f \<^Type>\<open>BI _\<close>\<close>\<close>) =>
                    (if flag
                     then \<^Const>\<open>Separation_Homo\<^sub>I a b c d e f x_ty\<close>
                       $ Fa $ Fb $ F_term $ T $ U
                       $ (\<^Const>\<open>Collect \<^Type>\<open>prod c f\<close>\<close> $ (\<^Const>\<open>case_prod c f \<^Type>\<open>bool\<close>\<close> $ dom))
                       $ zip
                     else \<^Const>\<open>Separation_Homo\<^sub>E a b c d e f x_ty\<close>
                       $ Fa $ Fb $ F_term $ T $ U
                       $ \<^Const>\<open>top \<^Type>\<open>set x_ty\<close>\<close> $ zip)
                   | _ => error "Internal bug")

   in Seq.single ([], HOLogic.Trueprop $ SH, NONE :: parse_inst_params_from_phi_term FT_term, phi, ctxt)
  end)
  end

fun SH_reasoning is_intro phi ctxt =
  default_reasoning true
      (pass_make_ToA_default oo default_reasoning_configure)
      (K (K NONE))
      (fn ctxt => fn sequent =>
         let val bads = [\<^const_name>\<open>MAKE\<close>, \<^const_name>\<open>OPEN\<close>]
             fun chk 0 (Const(\<^const_name>\<open>times\<close>, _) $ X1 $ X2) =
                    (chk_unfolded bads ctxt phi X1; chk_unfolded bads ctxt phi X2)
               | chk 0 X = chk_unfolded bads ctxt phi X
               | chk _ _ = ()
          in if is_intro
          then exhaustive_PLPR_reasoner (SOME 1) chk ctxt sequent
          else exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__simp} chk ctxt sequent
         end) phi ctxt

fun gen_SH is_intro (_,name) instruction (phi0 : phi_type) thy =
  let (*val phi0pr = make_phi_for_pair generic phi0*)
      val parse_hint = parse_hint (
            fn Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, _) $ _ $ _ $ F $ _ $ _ $ _ $ _ => F
             | Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, _) $ _ $ _ $ F $ _ $ _ $ _ $ _ => F
             | Const(\<^const_name>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I\<close>, _) $ _ $ _ $ F $ _ $ _ $ _ $ _ => F
             | Const(\<^const_name>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E\<close>, _) $ _ $ _ $ F $ _ $ _ $ _ $ _ => F)
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, _) $ _ $ _ $ _ $ _ $ _ $ D $ z) = [D,z]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, _) $ _ $ _ $ _ $ _ $ _ $ D $ u) = [D,u]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I\<close>, _) $ _ $ _ $ _ $ _ $ _ $ D $ z) = [D,z]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E\<close>, _) $ _ $ _ $ _ $ _ $ _ $ D $ u) = [D,u]
        | extract_oprs_from_hint _ = []

      val parameterized =
            case #1 instruction
              of SOME (H, _) =>
                  (case Term.head_of (HOLogic.dest_Trueprop (Logic.strip_imp_concl H))
                     of Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, _) => false
                      | Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, _) => false
                      | Const(\<^const_name>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I\<close>, _) => true
                      | Const(\<^const_name>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E\<close>, _) => true)
               | _ => false (*TODO: guessing the form of parameterized SH is not supported yet*)

      val equip_expansion = equip_expansion_ss phi0
      val ind_conv_z = default_ind_conv (
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SH\<^sub>I_rewr_IH}),
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_common_rewr_imp1_noact}) then_conv
              Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
              Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                (Phi_Conv.hol_alls_to_meta_alls (fn _ =>
                  conv_hol_imp_to_meta_if_has (Conv.rewr_conv @{thm' Premise_def[symmetric, where mode=MODE_GUARD]})
                ) ctxt)
            )
      val ind_conv_u = default_ind_conv (
            fn ctxt => fn _ => fn ctm =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SH\<^sub>E_rewr_IH}) ctm,
            fn ctxt => fn _ => fn ctm =>
             (Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_common_rewr_imp1}) then_conv
              (@{print} o Phi_Reasoners.asm_rewrite true (equip_expansion ctxt)) then_conv
              Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                (conv_hol_imp_to_meta_if_has (Conv.rewr_conv @{thm' Premise_def[symmetric, where mode=MODE_GUARD]}))) ctm
            )
      val ind_conv = if is_intro then ind_conv_z else ind_conv_u

      val pre_simp = default_pre_simplifier (Phi_Conv.meta_alls_conv (fn ctxt => fn ctm =>
            (Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.rewr_conv (if is_intro then @{thm' \<phi>TA_common_rewr_imp1_rev}
                                        else @{thm' \<phi>TA_SH\<^sub>E_rewr_pre})) ctm) o snd)

      val simp = if is_some (#1 instruction) then K I
                 else simplifier_by_cong (if is_intro then if parameterized then @{thms' \<phi>TA_SH\<^sub>\<Lambda>\<^sub>I_DV_cong}
                                                                            else @{thms' \<phi>TA_SH\<^sub>I_DV_cong}
                                                      else if parameterized then @{thms' \<phi>TA_SH\<^sub>\<Lambda>\<^sub>E_DV_cong}
                                                                            else @{thms' \<phi>TA_SH\<^sub>E_DV_cong})

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint, guess_property_SH is_intro,
                                     (if is_intro then if parameterized then @{thm' \<phi>TA_SH\<^sub>\<Lambda>\<^sub>I_rule}
                                                                        else @{thm' \<phi>TA_SH\<^sub>I_rule}
                                                  else if parameterized then @{thm' \<phi>TA_SH\<^sub>\<Lambda>\<^sub>E_rule}
                                                                        else @{thm' \<phi>TA_SH\<^sub>E_rule}),
                                     [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, SH_reasoning is_intro)],
                                     K NONE, pre_simp, simp)
                                    phi0 instruction thy
   in case Seq.pull rules
        of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
         | SOME (rule', _) => thy
             |> note_properties_s false phi0 [(name, [rule'])]
             |> Local_Theory.declaration {syntax=false, pervasive=false, pos= #3 instruction} (
                  fn m => fn lthy => lthy
                    |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
                    |> Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE'
                                             (SOME (the_default @{reasoner_group %\<phi>TA_derived_properties}
                                                                (#2 instruction)))
                                             ([],[]) NONE [Morphism.thm m rule']
                    |> Config.restore_generic Phi_Reasoner.trace lthy)
             |> pair [rule']
  end

val separation_homo_I = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Separation_Homo\<^sub>I") (gen_SH true)
val separation_homo_E = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Separation_Homo\<^sub>E") (gen_SH false)


end
