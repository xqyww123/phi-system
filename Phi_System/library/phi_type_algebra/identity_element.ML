signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val identity_element_I : quiet -> deriving_instruction list -> Phi_Type_Algebra.derive
val identity_element_E : quiet -> deriving_instruction list -> Phi_Type_Algebra.derive
val id_ele_properties : bool -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

(*** Identity Element Intro \& Elim ***)

fun guess_id_ele (typ as TFree (_, S)) ctxt =
      if Sign.subsort (Proof_Context.theory_of ctxt) (S, \<^sort>\<open>one\<close>)
      then (TVars.empty, \<^Const>\<open>one_class.one typ\<close>, ctxt)
      else raise Automation_Fail (let open Pretty in fn () =>
                  [paragraph (text "Fail to guess the identity element for type " @
                             [brk 1, Syntax.pretty_typ ctxt typ, brk 1] @
                              text "which is a fixed variable not of sort \<open>one\<close>")]
                 end)
  | guess_id_ele (typ as TVar _) ctxt =
      let val inst  = lift_types_sort (Proof_Context.theory_of ctxt) [(typ, \<^sort>\<open>one\<close>)]
          val typ' = Term_Subst.instantiateT inst typ
       in (Phi_Help.certify_tyvars (Context.Proof ctxt) inst,
           \<^Const>\<open>one_class.one typ'\<close>, ctxt)
      end
  | guess_id_ele (typ as Type _) ctxt =
      let val (inst, unit_simp, ctxt') =
                case eBNF_Info.identity_element_unify typ (Context.Proof ctxt)
                  of ([], _) => raise Automation_Fail (fn () => let open Pretty in
                                  [paragraph (text "Fail to guess the property, because no identity element and \
                                                   \its simplification rule found for type" @
                                              [brk 1, Syntax.pretty_typ ctxt typ])]
                                  end)
                   | ((inst, unit_simp) :: _, ctxt') => (inst, unit_simp, ctxt')
          val unit = case Thm.concl_of unit_simp
                       of _ (*Trueprop*) $ (_ (*eq*) $ LHS $ _) => LHS
       in (inst, unit,
           Context.the_proof (Expansion.map (fn ctxt => ctxt addsimps [unit_simp]) ctxt'))
      end

(*
(*strategy: lift the logic type of the abstract objects onto \<^sort>\<open>one\<close>. If fails, guess fails.
  We only support the \<phi>-type to a unital abstract algebra. We guess the identity abstract object
  if \<open>1\<close> (the identity of the algebra), because if it is not the identity, what else better it could be?

  If the \<phi>-type is parameterized, for any parameter $A$ whose logic type looks like a \<phi>-type, if
  the abstract domain of $A$ is also unital, the property of identity element of $A$ is declared
  as an antecedent of the guessed property.
*)
fun guess_property_sing is_left (phi0:phi_type) ctxt =
  let val thy = Proof_Context.theory_of ctxt
      val (rev_argtys0,x_ty0,model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val is_type_opr = exists (can dest_parameterized_phi_ty) rev_argtys0

      val inst  = lift_types_sort (Proof_Context.theory_of ctxt)
                                  (if is_type_opr
                                   then [(x_ty0, \<^sort>\<open>one\<close>), (model_ty0, \<^sort>\<open>one\<close>)]
                                   else [(model_ty0, \<^sort>\<open>one\<close>)])

      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val phi01 = instantiate_phi (inst',Vars.empty) phi0

      val (_, x_ty01, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi01))
      val (inst01, unit, ctxt) = guess_id_ele x_ty01 ctxt
      val subst01 = Term_Subst.instantiate (Phi_Help.uncertify_tyvars inst01, Vars.empty)
      val phi = instantiate_phi (inst01, Vars.empty) phi01

      val ((x_term, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt

      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun mk_P ctxt = if is_left
                      then Variable.add_fixes (Name.invent (Variable.names_of ctxt) "P" 1) ctxt
                      else ([""], ctxt)
      val thy = Proof_Context.theory_of ctxt
      fun mk_Ants (Ty::rev_arg_tys) ants (T_term $ A) ctxt =
       (case try dest_parameterized_phi_ty Ty
          of SOME (rev_arg_tys_A, x_ty_A, model_ty_A) =>
              if Sign.of_sort thy (x_ty_A, \<^sort>\<open>one\<close>)
              then let
                    val arity_A = length rev_arg_tys_A
                    val ([P], ctxt') = mk_P ctxt
                    val A' = fold_index (fn (i,_) => fn X => X $ Bound (arity_A-1-i)) rev_arg_tys_A
                                (Term.incr_bv (arity_A, 0, A))
                    val ant = (\<^Const>\<open>\<phi>Type x_ty_A model_ty_A\<close> $ \<^Const>\<open>one_class.one x_ty_A\<close> $ A')
                            |> (fn X => (if is_left then \<^Const>\<open>Identity_Element\<^sub>I model_ty_A\<close> $ X $ Free(P, HOLogic.boolT)
                                                    else \<^Const>\<open>Identity_Element\<^sub>E model_ty_A\<close> $ X))
                            |> fold (fn T => fn X =>
                                    Const(\<^const_name>\<open>All\<close>, (T --> HOLogic.boolT) --> HOLogic.boolT)
                                      $ Abs("",T,X)
                                   ) rev_arg_tys_A
                 in mk_Ants rev_arg_tys (ant::ants) T_term ctxt'
                end
              else mk_Ants rev_arg_tys ants T_term ctxt
           | NONE => mk_Ants rev_arg_tys ants T_term ctxt)
        | mk_Ants [] ants _ ctxt = (ants, ctxt)
        | mk_Ants _ _ _ _ = raise ListPair.UnequalLengths
      val (ants, ctxt) = mk_Ants rev_arg_tys [] T_term ctxt
      val unit_sing = \<^Const>\<open>insert x_ty\<close> $ unit $ \<^Const>\<open>bot \<^Type>\<open>set x_ty\<close>\<close>
   in Seq.single (ants, \<^Const>\<open>Trueprop\<close> $ (
        (if is_left then \<^Const>\<open>Identity_Elements\<^sub>I x_ty model_ty\<close> $ T_term $ unit_sing
                            $ (if #is_recursive phi
                               then \<^Const>\<open>True\<close>
                               else Var(("P", 0), HOLogic.boolT))
                    else \<^Const>\<open>Identity_Elements\<^sub>E x_ty model_ty\<close> $ T_term $ unit_sing)),
        SOME unit :: parse_inst_params_from_phi_term T_term,
        phi, ctxt)
  end
*)

fun guess_property is_intro (phi0:phi_type) ctxt =
  let val thy = Proof_Context.theory_of ctxt
      val (rev_argtys0,x_ty0,model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val is_type_opr = exists (can dest_parameterized_phi_ty) rev_argtys0
      
      val inst  = lift_types_sort (Proof_Context.theory_of ctxt)
                                  (if is_type_opr
                                   then [(model_ty0, \<^sort>\<open>one\<close>)]
                                   else [(x_ty0, \<^sort>\<open>one\<close>), (model_ty0, \<^sort>\<open>one\<close>)])
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
      val phi't1 = instantiate_phi (inst',Vars.empty) phi0

      val (phi, unit, ctxt) =
            if is_type_opr then (phi't1, Term.dummy, ctxt)
            else let val (_, x_ty2, _) = dest_parameterized_phi_ty (Term.fastype_of (#term phi't1))
                     val (inst2, unit, ctxt) = guess_id_ele x_ty2 ctxt
                  in (instantiate_phi (inst2, Vars.empty) phi't1, unit, ctxt)
                 end

      val (args, x_ty, model_ty) = parameters_and_typs_of phi
      val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (ants_Ds_Ps, ctxt) = fold_map (fn ((info,ty), A_term0) => fn ctxt =>
            case try dest_parameterized_phi_ty ty
              of SOME (rev_atys, x_ty, m_ty) =>
                  if Sign.of_sort thy (m_ty, \<^sort>\<open>one\<close>) then
                    let fun name s s' = the_default s (Option.map (suffix s') (#name info))
                        val ([D,P], ctxt) = Variable.variant_fixes [name "D" "\<^sub>D", name "P" "\<^sub>P"] ctxt
                        val D = Free(D, x_ty --> HOLogic.boolT)
                        val P = Free(P, x_ty --> HOLogic.boolT)
                        val A_term = fold_index (fn (i,_) => fn X => X $ Bound i) rev_atys A_term0
                     in (SOME ((if is_intro then \<^Const>\<open>Identity_Elements\<^sub>I x_ty m_ty\<close> $ A_term $ D $ P
                                       else \<^Const>\<open>Identity_Elements\<^sub>E x_ty m_ty\<close> $ A_term $ D)
                                  |> fold_rev (fn T => fn X => \<^Const>\<open>All T\<close> $ Abs ("A", T, X)) rev_atys,
                               (x_ty, D),
                               (x_ty, P)),
                         ctxt)
                    end
                  else (NONE, ctxt)
               | _ => (NONE, ctxt))
            (args ~~ snd (Term.strip_comb T_term)) ctxt
      val (ants, Ds, Ps) = (map_filter (Option.map #1) ants_Ds_Ps,
                            map_filter (Option.map #2) ants_Ds_Ps,
                            map_filter (Option.map #3) ants_Ds_Ps)

      val seq = if is_type_opr
            then guess_predicate ctxt Ds x_ty
              |> Seq.maps (fn (D,ctxt) =>
                  if is_intro then guess_predicate ctxt Ps x_ty |> Seq.map (fn (P,ctxt) => (D,P,ctxt))
                              else Seq.single (D,D,ctxt))
            else Seq.single (\<^Const>\<open>HOL.eq x_ty\<close> $ unit,
                             if #is_recursive phi then Abs ("x", x_ty, \<^Const>\<open>True\<close>)
                                                  else Var(("P", 0), x_ty --> HOLogic.boolT),
                             ctxt)
   in seq |> Seq.map (fn (D,P,ctxt) =>
        (ants, HOLogic.Trueprop $   
                  (if is_intro then \<^Const>\<open>Identity_Elements\<^sub>I x_ty model_ty\<close> $ T_term $ D $ P
                               else \<^Const>\<open>Identity_Elements\<^sub>E x_ty model_ty\<close> $ T_term $ D ),
         NONE :: parse_inst_params_from_phi_term T_term,
         phi, ctxt))
  end


fun gen_id_ele is_left (_,name) instruction ctxt0 (phi0 : phi_type) generic =
  let val parse_hint = parse_hint (
            fn Const(\<^const_name>\<open>Identity_Elements\<^sub>I\<close>, _) $ T $ _ $ _ => T
             | Const(\<^const_name>\<open>Identity_Elements\<^sub>E\<close>, _) $ T $ _ => T
             | _ => raise TERM ("",[]))
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Identity_Elements\<^sub>I\<close>, _) $ _ $ D $ P) = [D,P]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Identity_Elements\<^sub>E\<close>, _) $ _ $ D) = [D]
        | extract_oprs_from_hint _ = []

      val ind_conv = default_ind_conv (
              fn _ => fn _ =>
                  Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_noact} then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv,
              fn ctxt => fn _ =>
                  Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_noact} then_conv
                  Phi_Reasoners.asm_rewrite true (Expansion.equip ctxt addsimps (#equations phi0)) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv)

      val varify_subgoal =
            if is_left
            then K (fn Trueprop $ (Identity_Elements $ P) =>
                        SOME ([P], fn [P'] => Trueprop $ (Identity_Elements $ P')))
            else K (K NONE)

      fun reasoning phi =
        let val reasoner =
              if is_left
              then (fn ctxt => fn th =>
                case Thm.major_prem_of th
                  of _ (*Trueprop*) $ (_ (*Identity_Element\<^sub>I*) $ _ $ P) =>
                      let val rule = (case P of Var _ => @{thm' \<phi>TA_Ident_I_rule_step_infer}
                                              | _     => @{thm' \<phi>TA_Ident_I_rule_step})
                       in exhaustive_PLPR_reasoner_by_rule rule (K (chk_unfolded' ctxt phi)) ctxt th
                      end
                   | _ => error "BUG nov8x6UqTBS3cQ6ZkP/L5w")
              else (fn ctxt => exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded' ctxt phi)) ctxt)
         in default_reasoning true default_reasoning_configure varify_subgoal reasoner phi
        end

      fun set_the_infer_tail ctxt th =
        if is_left then
          case Thm.concl_of th
            of _ (*Trueprop*) $ (_ (*Identity_Element\<^sub>I*) $ _ $ P) =>
                (case P of Const(\<^const_name>\<open>HOL.disj\<close>, _) $ Var v $ _ =>
                              Thm.instantiate (TVars.empty, Vars.make [(v, \<^cterm>\<open>False\<close>)]) th
                           |> Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                                      HOLogic.Trueprop_conv (Conv.arg_conv (Simplifier.rewrite ctxt))
                               ) ctxt)
                         | _ => th)
             | _ => error "BUG nov8x6UqTBS3cQ6ZkP/L5w"
        else th

      fun simp (_, ctxt) th = set_the_infer_tail ctxt th
        |> (if is_some instruction then I
            else Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                  let val sctxt = Expansion.enhance ctxt addsimps @{thms special_Ex_def}
                   in HOLogic.Trueprop_conv (
                        if is_left
                        then Conv.combination_conv (Conv.arg_conv (Simplifier.rewrite sctxt))
                                                   (Simplifier.rewrite sctxt)
                        else Conv.arg_conv (Simplifier.rewrite sctxt))
                  end) ctxt))

      val rule = if is_left then @{thm' \<phi>TA_1L_rule} else @{thm' \<phi>TA_1R_rule}
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                     guess_property is_left, rule,
                                     [(K (SOME [0]), ind_conv, reasoning)],
                                     K NONE, simp)
                                    phi0 (Option.map fst instruction) ctxt0
   in case Seq.pull rules
        of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
         | SOME (rule', _) => generic
            |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.NORMAL_MODE
                                        (the_default @{reasoner_group %derived_identity_element}
                                                     (Option.mapPartial snd instruction))
                                        ([],[]) NONE [Morphism.thm m rule'])
            |> note_properties_s phi0 [(name, [rule'])]
            |> pair [rule']
  end

fun id_ele_properties is_intro ctxt0 (phi0 : phi_type) thy =
  let val (_,_,m_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val inst = lift_types_sort (Proof_Context.theory_of ctxt0) [(m_ty0, \<^sort>\<open>one\<close>)]
      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt0) inst
      val phi = instantiate_phi (inst', Vars.empty) phi0

      val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt0
      val (_,x_ty,m_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val trigger = (if is_intro then \<^Const>\<open>Identity_Elements\<^sub>I x_ty m_ty\<close>
                                 else \<^Const>\<open>Identity_Elements\<^sub>E x_ty m_ty\<close>) $ T_term
                 |> singleton (Variable.export_terms ctxt ctxt0)
                 |> Thm.cterm_of ctxt
                 |> Drule.mk_term

      val _ = if not (null (Phi_Type_Template_Properties.lookup_property_match (Context.Proof ctxt0) (Thm.concl_of trigger)))
              then raise Automation_Fail (fn () => let open Pretty in
                      [para "The deriver of Identity_Element_Properties can only be invoked once\
                            \ for each \<phi>-type."]
                    end)
              else ()
   in thy
   |> Phi_Help.generic_theory_mapping (fn m =>
        Phi_Type_Template_Properties.add_property (#pos phi, Morphism.thm m trigger))
  end

val identity_element_I = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Identity_Element\<^sub>I") (gen_id_ele true)
val identity_element_E = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Identity_Element\<^sub>E") (gen_id_ele false)


end