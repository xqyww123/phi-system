signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val conv_hol_imp_to_meta_if_has : conv -> conv
val object_equiv : quiet -> hint list -> Phi_Type_Algebra.derive
val object_equiv_singular : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

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
     | _ => false

fun infer_equiv ctxt sequent =
  let val var = case Thm.concl_of sequent
                  of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $ Var v) => v
                   | _ => error "BUG gZvGQ6CHTG+D2d27jtExHQ"
      val (tya, tyb) = case snd var of \<^Type>\<open>fun a \<^Type>\<open>fun b _\<close>\<close> => (a,b)
      val (_,oblg) = PLPR_Syntax.dest_premise_tag (Thm.major_prem_of sequent)
      
      fun infer lev (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ (Var v' $ x $ y) $ Y) =
            if v' = var
            then Phi_Help.subst_free_with_loose_bounds [(x, Bound (lev+1)), (y, Bound lev)] Y
            else \<^Const>\<open>True\<close>
        | infer lev (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ Y) =
            \<^Const>\<open>HOL.conj\<close> $ infer lev X $ infer lev Y
        | infer lev (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ X $ Y) =
            \<^Const>\<open>HOL.disj\<close> $ infer lev X $ infer lev Y
        | infer lev ((H as Const(\<^const_name>\<open>HOL.All\<close>, _)) $ Abs (N, Ty, X)) =
            H $ Abs (N, Ty, infer (lev+1) X)
        | infer lev ((H as Const(\<^const_name>\<open>HOL.Ex\<close>, _)) $ Abs (N, Ty, X)) =
            H $ Abs (N, Ty, infer (lev+1) X)
        | infer lev ((H as Const(\<^const_name>\<open>special_Ex\<close>, _)) $ Abs (N, Ty, X)) =
            H $ Abs (N, Ty, infer (lev+1) X)
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
  let val ((_,T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
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
   in eq_terms
   |> Seq.map (fn (eq_term, ctxt') =>
        (ants, \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Object_Equiv x_ty model_ty\<close> $ T_term $ eq_term),
         NONE :: parse_parameters_of_phi_type T_term, phi, ctxt'))
  end

(*The reachability relation of many type operators at singular point \<open>F \<circle>\<close> can become \<open>\<lambda>_. True\<close>*)
fun guess_obj_eq_singular_None (phi0:phi_type) ctxt =
  let val thy = Proof_Context.theory_of ctxt
      val ((_, FT_term0), ctxt) = fix_phi_term_params (#term phi0) ctxt
   in separate_type_operator_and_its_parameter_safe FT_term0
   |> Seq.of_list
   |> Seq.map_filter (fn (T_term0, F_term0) =>
  let val (rev_args_T0,x_ty_T0,model_ty_T0) = dest_parameterized_phi_ty (Term.fastype_of T_term0)
      val inst = (Sign.typ_match thy (x_ty_T0, \<^Type>\<open>unit\<close>) Vartab.empty
                    handle Type.TYPE_MATCH => raise Automation_Fail (fn () => let open Pretty in
                        [str "Fail to instantiate the abstract type to \<^typ>\<open>unit\<close>"]
                      end))
              |> (fn env => Phi_Help.lift_type_sort thy (model_ty_T0, \<^sort>\<open>one\<close>) env
                    handle TYPE _ => raise Automation_Fail (fn () => let open Pretty in
                      [paragraph (text "Fail to lift" @
                                  [brk 1, Syntax.pretty_typ ctxt model_ty_T0, brk 1] @
                                  text "to sort\<open>one\<close>")]
                    end))
              |> Phi_Help.subst_tyenv
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val phi = instantiate_phi (inst', Vars.empty) phi0
      val subst = Term_Subst.instantiate (inst, Vars.empty)
      val substT= Term_Subst.instantiateT inst
      val (F_term, model_ty_T, rev_args_T) = (subst F_term0, substT model_ty_T0, map substT rev_args_T0)
      val (_, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val FT_term = F_term $ (fold (fn T => fn X => Abs ("x", T, X)) rev_args_T \<^Const>\<open>\<phi>None model_ty_T\<close>)
      val property = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Object_Equiv x_ty model_ty\<close>
                                            $ FT_term
                                            $ Abs ("x", x_ty, Abs ("y", x_ty, \<^Const>\<open>True\<close>)))
   in SOME ([], property, NONE :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end handle Automation_Fail _ => NONE)
  end


fun OE_reasoning phi ctxt rule =
  let val ctxt' = Context.proof_map (Phi_Reasoner.add_pass (
            "\<phi>TA.OE", \<^pattern_prop>\<open>Object_Equiv _ _\<close>,
            fn _ => fn (rules, (_, priority), pats, guard, ctxt) =>
                       (rules, (Phi_Reasoner.NORMAL_LOCAL_CUT, priority), pats, guard, ctxt))) ctxt

      val prem_extractions =
        if def_contains_satisfaction phi
        then [Phi_Reasoners.Extract_Rule
                @{lemma' \<open>Object_Equiv T eq \<Longrightarrow> (\<forall>x y v. eq x y \<longrightarrow> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> v \<Turnstile> (y \<Ztypecolon> T))\<close>
                    by (simp add: Object_Equiv_def Transformation_def)}]
        else []

   in default_reasoning true
          (default_reasoning_configure prem_extractions)
          (K (K NONE))
          (exhaustive_PLPR_reasoner_by_rule @{thm' Action_Tag_D[where A=NToA]} (K (chk_unfolded' ctxt' phi)))
          ctxt' rule
  end

fun gen_obj_equal_singular (_,name) hint (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val rule0 = @{thm' \<phi>TA_OE\<^sub>O_rule}
      val rule = if #is_recursive phi0
                 then let val base = Thm.prems_of (#ind phi0)
                                  |> get_first (fn tm =>
                                       case Logic.strip_assums_concl tm
                                         of _ (*Trueprop*) $ (_ $ X) =>
                                             if exists_subterm (fn Bound _ => true | _ => false) X then NONE else SOME X
                                          | _ => NONE)
                                  |> (fn SOME X => X
                                       | NONE => raise Automation_Fail (fn () =>
                                                    [Pretty.str "The induction rule has no base step?!"]))
                                  |> Thm.cterm_of ctxt0
                                  |> Thm.incr_indexes_cterm (Thm.maxidx_of rule0 + 1)
                       in Drule.infer_instantiate ctxt0 [(("base",0),base)] rule0
                      end
                 else rule0

      val parse_hint = parse_hint_has_type_only (fn \<^Const>\<open>Object_Equiv _ _\<close> $ T $ _ => T)
      fun extract_oprs_from_hint (\<^Const>\<open>Object_Equiv _ _\<close> $ _ $ eq) = [eq]
        | extract_oprs_from_hint _ = []

      fun simp_conv ex_quantified_single_var ctxt phi = 
        let val sctxt = Simps.equip ctxt addsimps (#equations phi)
         in Phi_Conv.may_action_tag_conv (Phi_Syntax.transformation_conv
                (Simplifier.rewrite sctxt)
                (if ex_quantified_single_var
                 then Simplifier.rewrite sctxt then_conv Phi_Conv.embed_BI_assertion sctxt
                                               then_conv Phi_Conv.type_form_to_ex_quantified_single_var sctxt
                 else Simplifier.rewrite sctxt)
                Conv.all_conv)
        end

      fun ind_conv step1 = default_ind_conv (
                       fn ctxt => fn phi =>
                            Phi_Conv.may_action_tag_conv (Phi_Conv.hol_imp_conv Conv.all_conv (simp_conv step1 ctxt phi)) then_conv
                            Conv.rewr_conv (if step1 then @{thm \<phi>TA_OE\<^sub>O_rewr_IH1} else @{thm \<phi>TA_OE\<^sub>O_rewr_IH2}),
                       fn ctxt => fn phi =>
                            Phi_Conv.may_action_tag_conv (Phi_Conv.hol_imp_conv Conv.all_conv (simp_conv step1 ctxt phi)) then_conv
                            Conv.rewr_conv @{thm \<phi>TA_OE\<^sub>O_rewr})

      fun OEO_reasoning1 phi ctxt = default_reasoning false
            (default_reasoning_configure [])
            (K (K NONE))
            (exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__\<A>_NToA} (K (chk_unfolded' ctxt phi)))
            ctxt

      fun OEO_reasoning2 phi ctxt = default_reasoning false
            (default_reasoning_configure [])
            (K (K NONE))
            (exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_reason_rule__NToA} (K (chk_unfolded' ctxt phi)))
            ctxt

      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_obj_eq_singular_None, rule,
                                      [(SOME ([0], ind_conv true ), OEO_reasoning1),
                                       (SOME ([0], ind_conv false), OEO_reasoning2)],
                                      K NONE, K I)
                                     phi0 hint ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
        | SOME (rule', _) => thy
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80 ([],[]) NONE [Morphism.thm m rule'])
            |> note_properties phi0 [(name, [rule'])]
            |> pair [rule'])
  end


fun gen_obj_equal' (_,name) hint0 (phi0 : phi_type) thy =
  let val ctxt0 = Context.proof_of thy
      val parse_hint = parse_hint_has_type_only (fn \<^Const>\<open>Object_Equiv _ _\<close> $ T' $ _ => T')
      fun extract_oprs_from_hint (\<^Const>\<open>Object_Equiv _ _\<close> $ _ $ eq) = [eq]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (K (K (Conv.rewr_conv @{thm \<phi>TA_OE_rewr_IH})),
                       fn ctxt => fn _ => Conv.rewr_conv @{thm \<phi>TA_OE_rewr_C} then_conv
                            Conv.implies_concl_conv (HOLogic.Trueprop_conv (fn ctm =>
                              Phi_Reasoners.asm_rewrite true (Simps.equip ctxt addsimps (#equations phi0)) ctm)
                              then_conv Phi_Conv.hol_alls_to_meta_alls (fn _ =>
                                  conv_hol_imp_to_meta_if_has (Conv.rewr_conv @{thm' Action_Tag_def[symmetric, where A=\<phi>TA_pure_facts]})
                                ) ctxt))
      fun infer (_, ctxt, rule) =
            if need_infer rule
            then rule
                   |> Phi_Help.beta_eta_contract
                   |> Simplifier.rewrite_rule ctxt @{thms special_Ex_def}
                   |> infer_equiv ctxt
                   |> oblg_solver name ctxt
                   |> SOME
            else NONE
      fun simp (_, ctxt) =
        if is_some hint0 then I
        else Conv.fconv_rule (Phi_Conv.hhf_concl_conv 
               (K (Conv.arg_conv (Conv.arg_conv (
                  Simplifier.rewrite (ctxt addsimps @{thms special_Ex_def}))))) ctxt)
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property_obj_eq, @{thm' Object_Equiv_rule},
                                      [(SOME ([0], ind_conv), OE_reasoning)], infer, simp)
                                     phi0 hint0 ctxt0
   in Seq.pull rules
   |> (fn NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
        | SOME (rule', _) => thy
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [Morphism.thm m rule'])
            |> note_properties phi0 [(name, [rule'])]
            |> pair [rule'])
  end

fun chk_is_singular ctxt tm =
  case Logic.strip_assums_concl tm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Object_Equiv\<close>, _) $ _ $ eq) =>
        (case Envir.beta_eta_contract eq
           of Abs (_, _, Abs (_, _, \<^Const>\<open>True\<close>)) => true
            | _ => false)
     | _ => malformed_hint ctxt tm

fun gen_obj_equal'' name NONE phi thy = gen_obj_equal' name NONE phi thy
  | gen_obj_equal'' name (SOME H) phi thy =
      if chk_is_singular thy H
      then gen_obj_equal_singular name (SOME H) phi thy
      else gen_obj_equal' name (SOME H) phi thy

in

val object_equiv_singular = deriver_framework (ACCEPT_NO_HINT, ONLY_ONCE, "Object_Equiv\<^sub>O") gen_obj_equal_singular
val object_equiv = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Object_Equiv") gen_obj_equal''

end

end
