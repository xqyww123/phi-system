signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val conv_hol_imp_to_meta_if_has : conv -> conv
val conv_hol_imps_to_metas_if_has : conv -> conv -> conv
val object_equiv : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
(*val object_equiv_singular : quiet -> deriving_instruction list -> Phi_Type.derive*)

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

fun conv_hol_imps_to_metas_if_has Cant Cconcl ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =>
          (Conv.rewr_conv @{thm' atomize_imp[symmetric]} then_conv
           Conv.implies_conv Cant (conv_hol_imps_to_metas_if_has Cant Cconcl)) ctm
     | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
          (Conv.implies_conv Cant (conv_hol_imps_to_metas_if_has Cant Cconcl)) ctm
     | _ => Cconcl ctm

fun conv_hol_imp_to_meta_if_has Cant ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =>
          (Conv.rewr_conv @{thm' atomize_imp[symmetric]} then_conv
           Conv.arg1_conv (HOLogic.Trueprop_conv Cant)) ctm
     | _ => Conv.all_conv ctm


(*** Object Equivalence ***)

local

fun need_infer sequent =
  case Thm.concl_of sequent
    of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $ Var _) => true
     | _ (*Trueprop*) $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $
            Abs (_, _, Abs (_, _,
              Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Var _ $ Bound 1 $ Bound 0) $ _))) => true
     | _ => false

fun infer_equiv ctxt sequent =
  let val var = case Thm.concl_of sequent
                  of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $ Var v) => v
                   | _ (*Trueprop*) $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $
                          Abs (_, _, Abs (_, _,
                            Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Var v $ Bound 1 $ Bound 0) $ _))) => v
                   | _ => error "BUG gZvGQ6CHTG+D2d27jtExHQ"
      val (tya, tyb) = case snd var of \<^Type>\<open>fun a \<^Type>\<open>fun b _\<close>\<close> => (a,b)
      val (_,oblg) = PLPR_Syntax.dest_premise_tag (Thm.major_prem_of sequent)
      
      val exists_bad = exists_subterm (fn Const(\<^const_name>\<open>Inhabited\<close>, _) => true
                                        | Const(\<^const_name>\<open>Satisfaction\<close>, _) => true
                                        | _ => false)

      fun refine_term default (\<^Const>\<open>HOL.implies\<close> $ A $ B) =
            if exists_bad A then refine_term default B
                            else \<^Const>\<open>HOL.implies\<close> $ A $ refine_term default B
        | refine_term _ (\<^Const>\<open>HOL.disj\<close> $ A $ B) =
            \<^Const>\<open>HOL.disj\<close> $ refine_term \<^Const>\<open>False\<close> A $ refine_term \<^Const>\<open>False\<close> B
        | refine_term default X = if exists_bad X then default else X

      fun infer lev (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ (Var v' $ x $ y) $ Y) =
            if v' = var
            then Phi_Help.subst_with_loose_bounds [(x, Bound (lev+1)), (y, Bound lev)] Y
              |> refine_term \<^Const>\<open>True\<close>
            else \<^Const>\<open>True\<close>
        | infer lev (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ Y) =
            \<^Const>\<open>HOL.conj\<close> $ infer lev X $ infer lev Y
        | infer lev (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ X $ Y) =
            \<^Const>\<open>HOL.disj\<close> $ infer lev X $ infer lev Y
        | infer lev ((H as Const(\<^const_name>\<open>HOL.All\<close>, _)) $ Abs (N, Ty, X)) =
            H $ Abs (N, Ty, infer (lev+1) X)
        | infer lev (\<^Const>\<open>HOL.All ty\<close> $ X) =
            infer lev (\<^Const>\<open>HOL.All ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | infer lev ((H as Const(\<^const_name>\<open>HOL.Ex\<close>, _)) $ Abs (N, Ty, X)) =
            H $ Abs (N, Ty, infer (lev+1) X)
        | infer lev (\<^Const>\<open>HOL.Ex ty\<close> $ X) =
            infer lev (\<^Const>\<open>HOL.Ex ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | infer lev ((H as Const(\<^const_name>\<open>special_Ex\<close>, _)) $ Abs (N, Ty, X)) =
            H $ Abs (N, Ty, infer (lev+1) X)
        | infer lev (\<^Const>\<open>special_Ex ty\<close> $ X) =
            infer lev (\<^Const>\<open>special_Ex ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | infer _ _ = \<^Const>\<open>True\<close>

      val eq = Abs ("x", tya, Abs ("y", tyb, infer 0 oblg))
            |> Thm.cterm_of ctxt
   in Thm.instantiate (TVars.empty, Vars.make [(var, eq)]) sequent
  end

(*if the \<phi>-type is recursive, guess the reachability relation from the relation operator of the BNF,
  or else, leave it as a schematic variable because we can infer it from the proof obligation later.

  If the \<phi>-type has any parameters whose logic type looks like a \<phi>-type, the reachability relations
  of the parameters are also assumed as antecedents of the guessing property, and also used in
  above guessing the reachability relations of the target \<phi>-type.*)
fun guess_property_obj_eq (phi:phi_type) ctxt =
  let val ((_,T_term), ctxt) = fix_phi_term_params phi ctxt
      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi)) 
      fun mk_Ants ctxt (Ty::rev_arg_tys) (eq::eq_names) ants param_eqs (T_term $ A) =
           (case try dest_parameterized_phi_ty Ty
              of SOME (rev_arg_tys_A, x_ty_A, model_ty_A) =>
                  let val arity_A = length rev_arg_tys_A
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
               | NONE => mk_Ants ctxt rev_arg_tys eq_names ants param_eqs T_term)
        | mk_Ants _ [] [] ants param_eqs _ = (ants, param_eqs)
        | mk_Ants _ _ _ _ _ _ = raise ListPair.UnequalLengths

      val arity = length rev_arg_tys
      val rev_eq_names' = Name.invent (Variable.names_of ctxt) "eq" arity
      val (rev_eq_names, ctxt) = Variable.add_fixes rev_eq_names' ctxt
      val (ants,param_eqs) = mk_Ants ctxt rev_arg_tys rev_eq_names [] [] T_term

      val eq_terms =
            if #is_recursive phi
            then guess_self_rel ctxt param_eqs x_ty
            else Seq.single (Var(("eq", 1), x_ty --> x_ty --> HOLogic.boolT), ctxt)

      val (_, _, cond_T) =
              guess_conditions ctxt (\<^Const>\<open>Object_Equiv x_ty model_ty\<close>, false) phi T_term
      val (ants_U, oblg_U, _) =
              guess_conditions ctxt (\<^Const>\<open>Object_Equiv x_ty model_ty\<close>, true) phi T_term
      fun pass_eq eq =
        case oblg_U of Abs (_, _, \<^Const>\<open>True\<close>) => eq
          | _ => Abs ("x", x_ty, Abs ("y", x_ty,
                    \<^Const>\<open>HOL.conj\<close> $ (eq $ Bound 1 $ Bound 0)
                                    $ (\<^Const>\<open>HOL.implies\<close> $ (cond_T $ Bound 1) $ (oblg_U $ Bound 0))))

   in eq_terms
   |> Seq.map (fn (eq_term, ctxt') =>
        (ants_U @ ants,
         \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Object_Equiv x_ty model_ty\<close> $ T_term $ pass_eq eq_term),
         NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt'))
  end


fun OE_reasoning phi ctxt rule =
  let val ctxt' = Context.proof_map (Phi_Reasoner.add_pass (
            Const("\<phi>TA.OE",TFree("",[])), \<^pattern_prop>\<open>Object_Equiv _ _\<close>,
            fn _ => fn (rules, (_, priority), pats, guard, ctxt) =>
                       (rules, (Phi_Reasoner.NORMAL_LOCAL_CUT', priority), pats, guard, ctxt))) ctxt
      
   in default_reasoning true
          (pass_make_ToA [(@{reasoner_group %deriving_local_rules}, @{thm' mk_ToA_rule}),
                          (@{reasoner_group %deriving_local_rules}, @{thm' mk_ToA_rule'})]
           oo default_reasoning_configure)
          (K (K NONE))
          (exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded [\<^const_name>\<open>OPEN\<close>] ctxt' phi)))
          phi ctxt' rule
  end


fun gen_obj_equal' (_,name) instruction ctxt0 (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (fn \<^Const>\<open>Object_Equiv _ _\<close> $ T' $ _ => T')
      fun extract_oprs_from_hint (\<^Const>\<open>Object_Equiv _ _\<close> $ _ $ eq) = [eq]
        | extract_oprs_from_hint _ = []

      val _ = conv_chk_unfolded
      val equip_expansion = equip_expansion_ss phi0
    (*val phitm = Thm.cterm_of ctxt0 (#term phi0)
      val OE_IND_I = Drule.infer_instantiate ctxt0 [(("T",0), phitm)]
                        \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm phitm\<close> and T=phitm in
                            lemma \<open>OE_IND T \<equiv> T\<close> by (simp add: OE_IND_def)\<close>
                  |> @{print}*)
      val ind_conv =
            default_ind_conv (
               fn ctxt => fn _ =>
                    Conv.rewr_conv @{thm' \<phi>TA_OE_rewr_IH} then_conv
                    Phi_Conv.meta_all_conv (fn _ => Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv) ctxt,
               fn ctxt => fn _ =>
                    (Conv.rewr_conv @{thm' \<phi>TA_OE_rewr_CL}) then_conv
                     Phi_Conv.meta_all_conv (fn (_, ctxt) =>
                       Phi_Reasoners.asm_full_rewrite true (
                          equip_expansion ctxt addsimps @{thms' ex_pure_imp conj_imp_eq_imp_imp Pure.norm_hhf_eq}) then_conv
                       Phi_Conv.meta_alls_conv (fn ctxt =>
                          Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                              (conv_hol_imps_to_metas_if_has
                                  (HOLogic.Trueprop_conv (
                                      Conv.rewr_conv @{thm' Premise_def[symmetric, where mode=MODE_GUARD]}))
                                  (wrap_ind_target phi0 ctxt))) ctxt
                     ) ctxt
                    (*(Conv.implies_concl_conv (
                       Conv.rewr_conv @{thm' atomize_all[symmetric]} then_conv
                       Phi_Conv.meta_alls_conv (fn _ => Conv.rewr_conv @{thm' atomize_imp[symmetric]}) ctxt then_conv
                      ))*)
                  (*Conv.implies_conv
                      (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT})
                      (Phi_Conv.hol_alls_to_meta_alls (fn _ =>
                          conv_hol_imp_to_meta_if_has (Conv.rewr_conv @{thm' Action_Tag_def[symmetric, where A=\<phi>TA_pure_facts]})
                        ) ctxt)*))
      val pre_simp = default_pre_simplifier (Phi_Conv.meta_all_conv (fn (_,ctxt) =>
           (Phi_Conv.meta_all_conv (Phi_Reasoners.asm_rewrite true o equip_expansion o snd) ctxt) then_conv
            Conv.rewr_conv @{thm' \<phi>TA_OE_rewr_pre}) o snd)

      val infer = if not (is_some (#1 instruction)) andalso not (#is_recursive phi0)
                  then predicate_infer false
                          (fn _ $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $ Var v) => SOME v
                            | _ $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $
                                    Abs (_, _, Abs (_, _,
                                        Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Var v $ Bound 1 $ Bound 0) $ _))) => SOME v
                            | _ $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $ X) =>
                                  if Term.is_schematic X then raise Match else NONE )
                          (oblg_solver' name)
                  else K NONE
(*      fun infer (_, ctxt, rule) =
            if need_infer rule
            then rule
                   |> Phi_Help.beta_eta_contract
                   |> Simplifier.rewrite_rule ctxt @{thms special_Ex_def}
                   |> infer_equiv ctxt
                   |> oblg_solver name ctxt
                   |> SOME
            else NONE*)

      val simp = if is_some (#1 instruction) then K I
                 else simplifier_by_LPR' @{thm' \<phi>TA_OE_simp}

      val ctxt = if def_contains_satisfaction phi0 then ctxt0
                      |> Config.put Phi_Reasoner.ignore_dup_reasoner true
                      |> Bundle.includes ["Phi_BI.ToA_extract_pure_sat"]
                      |> Config.restore Phi_Reasoner.ignore_dup_reasoner ctxt0
                 else ctxt0

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property_obj_eq, @{thm' Object_Equiv_rule},
                                      [(NONE, K (K I), K (pure_PLPR_reasoning 2)),
                                       (SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, OE_reasoning)],
                                      infer, pre_simp, simp)
                                     phi0 instruction
                                     ((*Config.put search_CSTR_rules true*) ctxt)
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
        | SOME (rule', _) => thy
            |> Phi_Help.generic_theory_mapping (#3 instruction) (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %derived_object_equiv}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule'])
            |> note_properties_s false phi0 [(name, [rule'])]
            |> pair [rule'])
  end

(*
fun chk_is_singular ctxt tm =
  let fun chk_None (Const(\<^const_name>\<open>\<phi>None\<close>, _)) = true
        | chk_None (Abs (_, _, X)) = chk_None X
        | chk_None _ = false
   in case Logic.strip_assums_concl tm
   of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ T $ eq) =>
            exists chk_None (snd (Term.strip_comb (Envir.beta_eta_contract T)))
     | _ => malformed_hint ctxt tm (K [])
  end

fun gen_obj_equal'' name NONE ctxt_derv phi thy = gen_obj_equal' name NONE ctxt_derv phi thy
  | gen_obj_equal'' name (SOME (H, group)) ctxt_derv phi thy =
      if chk_is_singular ctxt_derv H
      then gen_obj_equal_singular name (SOME (H, group)) ctxt_derv phi thy
      else gen_obj_equal' name (SOME (H, group)) ctxt_derv phi thy
*)
in

(*val object_equiv_singular = deriver_framework (ACCEPT_NO_HINT, ONLY_ONCE, "Object_Equiv\<^sub>O") gen_obj_equal_singular*)
val object_equiv = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Object_Equiv") gen_obj_equal'

end

end
