signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val sigma_trivial_homomorphism : quiet -> Phi_Type.hint list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers


fun guess_projector bnf i insts =
  let val (Tname, targs) = case eBNF_Info.T_of_bnf bnf
                             of Type (N, args) => (N, args)
                              | _ => error "BUG yovXA3RKT76zCozhObW5NQ"
      val target = List.nth (targs, i)
      val casex = eBNF_Info.case_of bnf
      val case_args = Phi_Help.front (Term.binder_types (Term.fastype_of casex))
      val ret_ty = Term.body_type (Term.fastype_of casex)
      val comb = \<^Const>\<open>combine_options target\<close> $ Abs ("x", target, Abs ("y", target, Bound 1))
      fun mk_comb x (Const(\<^const_name>\<open>None\<close>, _)) = x
        | mk_comb x body = comb $ x $ body
      fun mk_one ty =
        let val args = Term.binder_types ty
            fun prj i body (ty :: tys) =
                  Abs ("x", ty, prj (i-1) (if ty = target then mk_comb (\<^Const>\<open>Some target\<close> $ Bound (i-1)) body else body) tys)
              | prj _ body [] = body
            (*fun pred i (ty :: tys) = Abs ("x", ty, pred (if ty = target then 0 else i+1) tys)
              | pred i [] = if i >= arity then \<^Const>\<open>False\<close> else \<^Const>\<open>True\<close>*)
         in prj (length args) \<^Const>\<open>None target\<close> args (*pred arity args*)
        end
      val subst = targs ~~ insts
      val target' = Term.typ_subst_atomic subst target
   in fold (fn ty => fn X => X $ mk_one ty) case_args casex
   |> Term.subst_atomic_types ((ret_ty, \<^Type>\<open>option target'\<close>) :: subst)
      (*fold (fn ty => fn (X1, X2) => case mk_one ty of (Pj,Pd) => (X1 $ Pj, X2 $ Pd))
           case_args (casex, casex)
   |> apfst (Term.subst_atomic_types ((ret_ty, target') :: subst))
   |> apsnd (Term.subst_atomic_types ((ret_ty, HOLogic.boolT) :: subst))*)
  end

fun fail () = raise Automation_Fail (fn () => [Pretty.str "Fail to guess the \<Sigma> trivial homomorphism."])

fun guess_ssp ctxt (sigma_ty, sigma) (T as \<^Type>\<open>prod ta tb\<close>) =
      if ta = sigma_ty
      then SOME (Abs ("x", T, \<^Const>\<open>HOL.eq sigma_ty\<close> $ (\<^Const>\<open>fst ta tb\<close> $ Bound 0) $ sigma),
                 Abs ("x", T, \<^Const>\<open>Some sigma_ty\<close> $ (\<^Const>\<open>fst ta tb\<close> $ Bound 0)),
                 \<^Const>\<open>snd ta tb\<close>,
                 [],
                 ctxt)
      else NONE
  | guess_ssp ctxt (sigma_ty, sigma) (T as Type(Tname, args0)) =
      if exists_subtype (fn ty => ty = sigma_ty) T
      then let val bnf = eBNF_Info.get_bnf1 (Context.Proof ctxt) Tname
               fun pass_args _ (Ps, sels, rev_maps, rev_lives', cd_rules, ctxt) [] = (Ps, sels, rev_maps, rev_lives', cd_rules, ctxt)
                 | pass_args i (Ps, sels, rev_maps, rev_lives', cd_rules, ctxt) ((is_live, arg) :: args) =
                     if arg = sigma_ty then fail ()
                     else if is_live
                     then case guess_ssp ctxt (sigma_ty, sigma) arg
                       of SOME (P, sel, mapper, cd_rules', ctxt) =>
                            let val prj = guess_projector bnf i args0 $ Bound 0
                                val t' = Term.body_type (Term.fastype_of mapper)
                             in pass_args (i+1) (P :: Ps,  (*(\<^Const>\<open>HOL.conj\<close> $ (P $ prj) $ pred)*)
                                                 (\<^Const>\<open>case_option \<^Type>\<open>option sigma_ty\<close> arg\<close>
                                                    $ \<^Const>\<open>None sigma_ty\<close> $ sel $ prj) :: sels,
                                                 mapper :: rev_maps,
                                                 t' :: rev_lives',
                                                 cd_rules' @ cd_rules,
                                                 ctxt) args
                            end
                        | NONE => pass_args (i+1) (Abs ("x", arg, \<^Const>\<open>True\<close>) :: Ps, sels,
                                                   (Abs("x", arg, Bound 0)) :: rev_maps,
                                                   arg :: rev_lives', cd_rules, ctxt) args
                     else pass_args (i+1) (Ps, sels, rev_maps, rev_lives', cd_rules, ctxt) args
               val (Ps', sels', rev_maps, rev_lives', cd_rules, ctxt) =
                      pass_args 0 ([], [], [], [], [], ctxt) (eBNF_Info.tyargs_is_live_or_dead bnf ~~ args0)
               val (deads, lives) = eBNF_Info.classify_bnf_dead_live bnf args0
               val P = eBNF_Info.mk_pred_of_bnf deads lives bnf
                    |> fold (fn P => fn X => X $ P) Ps'
               val S = let val comb = \<^Const>\<open>combine_options sigma_ty\<close> $ Abs ("x", sigma_ty, Abs ("y", sigma_ty, Bound 1))
                        in Abs("x", T, foldr1 (fn (a,b) => comb $ a $ b) sels')
                       end               
               val mapper = eBNF_Info.mk_map_of_bnf deads lives (rev rev_lives') bnf
                         |> fold (fn M => fn X => X $ M) rev_maps
               val ctxt = load_ss (false,true,true,true,false) bnf ctxt
               
               fun inst_case_distrib th =
                 let val idx = Thm.maxidx_of th + 1
                     val f = \<^schematic_cterm>\<open>case_option None ?f :: ?'b option \<Rightarrow> ?'a option\<close>
                                |> Thm.incr_indexes_cterm idx
                     val f'= \<^schematic_cterm>\<open>the :: ?'a option \<Rightarrow> ?'a\<close>
                                |> Thm.incr_indexes_cterm idx
                  in case Thm.concl_of th
                       of _ (*Trueprop*) $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ (Var (h, _) $ _) $ _) =>
                                [Drule.infer_instantiate ctxt [(h, f)] th,
                                 Drule.infer_instantiate ctxt [(h, f')] th]
                        | Const(\<^const_name>\<open>Pure.eq\<close>, _) $ (Var (h, _) $ _) $ _ =>
                                [Drule.infer_instantiate ctxt [(h, f)] th,
                                 Drule.infer_instantiate ctxt [(h, f')] th]
                        | _ => (warning ("The rule is not a case-distribution rule\n" ^
                                         Thm.string_of_thm ctxt th) ;
                                [])
                 end
               val cd_rules' = eBNF_Info.case_distribs_of_safe bnf
                            |> maps inst_case_distrib
            in SOME (P, S, mapper, cd_rules' @ cd_rules, ctxt)
           end
      else NONE
  | guess_ssp _ (sigma_ty, _) T =
      if T = sigma_ty then fail () else NONE

fun guess_ssp_top ctxt sigma_ty T =
  let val [sigma] = Name.invent_names (Variable.names_of ctxt) "\<sigma>" [sigma_ty]
                 |> map Free
   in guess_ssp ctxt (sigma_ty, sigma) T
   |> Option.map (fn (P, S, M, cd_ruls, ctxt) =>
        let val sctxt = Expansion.equip ctxt addsimps (@{thms' option.case option.sel} @ cd_ruls)
            val S' = Thm.cterm_of ctxt (Abs ("x", T, \<^Const>\<open>the sigma_ty\<close> $ (S $ Bound 0)))
                  |> Simplifier.rewrite sctxt
                  |> Thm.cprop_of
                  |> Thm.dest_arg
                  |> Thm.term_of
            val P' = Abs ("\<sigma>", sigma_ty, Phi_Help.subst_with_loose_bounds [(sigma, Bound 0)] P)
         in (P', S', M, ctxt)
        end)
  end


fun guess_property_SgTH phi0 ctxt =
  let val ((_, FT_term0), ctxt) = fix_phi_term_params (#term phi0) ctxt
   in Seq.of_list (separate_tyopr_and_its_non_parameterized_typ_param FT_term0)
   |> Seq.map (fn (T_term0, F_term0) =>
  let val (instTy, _, phi) = instantiate_phi_to_pair_x ctxt (T_term0, phi0)

      val inst = Term_Subst.instantiate (instTy, Vars.empty)
      val (FT_term, F_term, T_term) = (inst FT_term0, inst F_term0, inst T_term0)

      val (_, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val ([], element_ty, _) = dest_parameterized_phi_ty (Term.fastype_of T_term)
      val (sigma_ty, _) = case element_ty
                            of \<^Type>\<open>prod a b\<close> => (a,b)
                             | _ => error "BUG wN93cAxkQ2e4WYDsi8LfVA"

      val (P, sel, mapper, ctxt) = case guess_ssp_top ctxt sigma_ty x_ty
                                     of SOME X => X
                                      | NONE => fail ()

      val SSP = (case (Term.fastype_of F_term, Term.fastype_of mapper)
                  of (\<^Type>\<open>fun \<^Type>\<open>fun \<^Type>\<open>prod a b\<close> \<^Type>\<open>set c\<close>\<close> \<^Type>\<open>fun d \<^Type>\<open>set e\<close>\<close>\<close>, \<^Type>\<open>fun _ f\<close>) =>
                    let val Fb = Term.map_types (subst_ty [(element_ty, b), (d, f)]) F_term
                     in \<^Const>\<open>Trivial_\<Sigma> a b c d e f\<close> $ F_term $ Fb $ P $ sel $ mapper
                    end
                   | _ => error "BUG")

   in ([], HOLogic.Trueprop $ SSP, NONE :: parse_inst_params_from_phi_term FT_term, phi, ctxt)
  end)
  end

fun reasoning_configure (subgoal, lsequent) (local_prems, ctxt) =
  let val SOME T_tm = AList.lookup (op =) (#params subgoal) "T"
      val T_idx = Thm.maxidx_of_cterm T_tm + 1
      val inst = Thm.incr_indexes T_idx
              #> try (Drule.infer_instantiate ctxt [(("T",T_idx), T_tm)])
      val T_rules = map_filter inst @{thms' \<phi>TA_SgH_T_intro \<phi>TA_SgH_T_intro'}
      fun mk_black ((T as Free _) $ Var (_, Ty)) = T $ Var (("var",0), Ty)
        | mk_black (X $ Y) = (mk_black X $ mk_black Y)
        | mk_black (Abs (N,Ty,X)) = Abs (N,Ty, mk_black X)
        | mk_black X = X
      fun mk_black' th = mk_black (Thm.concl_of th)
      val ctxt = Context.proof_map (
            Phi_Reasoner.add_rules (map (fn rule =>
                ([rule], \<^here>, (Phi_Reasoner.LOCAL_CUT, Phi_Reasoner.ALLOW_BACKTRACK), 300, [], [mk_black' rule], NONE)) T_rules)
          ) ctxt
   in default_reasoning_configure [] (subgoal, lsequent) (local_prems, ctxt)
  end

fun SgTH_reasoning phi ctxt =
  default_reasoning true
      reasoning_configure
      (K (K NONE))
      (exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__simp_NToA}
         (K (chk_unfolded ctxt phi)))
      ctxt

fun gen_SgTH (_,name) hint0 ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (
            fn Const(\<^const_name>\<open>Trivial_\<Sigma>\<close>, _) $ F $ _ $ _ $ _ $ _ => F)
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Trivial_\<Sigma>\<close>, _) $ _ $ _ $ D $ s $ z) = [D,s,z]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SgH_rewr_IH}),
            fn ctxt => fn _ =>
              Conv.rewr_conv (Thm.transfer' ctxt @{thm' \<phi>TA_SgH_rewr_C}) then_conv
                Conv.implies_concl_conv (Conv.implies_conv
                  (PLPR_Syntax.premise_tag_conv (K true) (
                    Phi_Reasoners.asm_rewrite true (Expansion.equip ctxt addsimps (#equations phi0))))
                  (Phi_Conv.action_tag_conv (
                    Phi_Reasoners.asm_rewrite true (Expansion.equip ctxt
                        addsimps (@{thms' \<phi>Dependent_Sum.unfold \<phi>Dependent_Sum.unfold[folded \<phi>Auto_\<Sigma>_def]}
                                  @ #equations phi0))
                  )))
        )
      fun simp (_, ctxt) =
        if is_some hint0 then I
        else Conv.fconv_rule (
               Phi_Conv.hhf_concl_conv (fn ctxt =>
                 let val sctxt = ctxt addsimps @{thms special_Ex_def}
                  in Conv.arg_conv (Conv.combination_conv (Conv.combination_conv
                        (Conv.arg_conv (Simplifier.rewrite sctxt))
                        (Simplifier.rewrite sctxt))
                        (Simplifier.rewrite sctxt))
                 end
             ) ctxt)

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                     guess_property_SgTH, @{thm' \<phi>TA_SgH_rule},
                                     [(SOME [0,~1,~1], ind_conv, SgTH_reasoning)],
                                     K NONE, simp)
                                    phi0 hint0 ctxt0
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80
                                              ([],[]) NONE [Morphism.thm m rule])
        |> note_properties_s phi0 [(name, [rule])]
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val sigma_trivial_homomorphism = deriver_framework (ACCEPT_ONE_HINT, ONLY_ONCE, "Trivial_\<Sigma>") gen_SgTH

end
