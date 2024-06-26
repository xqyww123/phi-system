signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val identity_element_I : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val identity_element_E : quiet * Position.T -> deriving_instruction list -> Phi_Type.derive
val id_ele_properties : Position.T -> bool -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

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
      val ((_, T_term), ctxt) = fix_phi_term_params phi ctxt
      val (ants_Ds_Ps, ctxt) = fold_map (fn ((info,ty), A_term0) => fn ctxt =>
            case try dest_parameterized_phi_ty ty
              of SOME (rev_atys, x_ty, m_ty) =>
                  if Sign.of_sort thy (m_ty, \<^sort>\<open>one\<close>) then
                    let fun name s s' = the_default s (Option.map (suffix s') (#name info))
                        val ([D,P], ctxt) = Variable.variant_fixes [name "D" "\<^sub>D", name "P" "\<^sub>P"] ctxt
                        val atys = rev rev_atys
                        val D = Free(D, atys ---> x_ty --> HOLogic.boolT)
                             |> fold_index (fn (i,_) => fn X => X $ Bound i) atys
                        val P = Free(P, atys ---> x_ty --> HOLogic.boolT)
                             |> fold_index (fn (i,_) => fn X => X $ Bound i) atys
                        val A_term = fold_index (fn (i,_) => fn X => X $ Bound i) atys A_term0
                     in (SOME ((if is_intro then \<^Const>\<open>Identity_Elements\<^sub>I x_ty m_ty\<close> $ A_term $ D $ P
                                       else \<^Const>\<open>Identity_Elements\<^sub>E x_ty m_ty\<close> $ A_term $ D)
                                  |> fold_rev (fn T => fn X => \<^Const>\<open>All T\<close> $ Abs ("A", T, X)) rev_atys,
                               (x_ty, D),
                               (x_ty, P)),
                         ctxt)
                    end
                  else (NONE, ctxt)
               | _ => (NONE, ctxt))
            (args ~~ Phi_Help.take_last (length args) (snd (Term.strip_comb T_term))) ctxt
      val (ants, Ds, Ps) = (map_filter (Option.map #1) ants_Ds_Ps,
                            map_filter (Option.map #2) ants_Ds_Ps,
                            map_filter (Option.map #3) ants_Ds_Ps)

      val seq =
            if is_type_opr andalso #is_recursive phi
            then guess_predicate ctxt Ds x_ty
              |> Seq.maps (fn (D,ctxt) =>
                  if is_intro then guess_predicate ctxt Ps x_ty |> Seq.map (fn (P,ctxt) => (D,P,ctxt))
                              else Seq.single (D,D,ctxt))
            else Seq.single (Abs ("x", x_ty, \<^Const>\<open>True\<close>), Abs ("x", x_ty, \<^Const>\<open>True\<close>), ctxt)

      val prop_head = if is_intro then \<^Const>\<open>Identity_Elements\<^sub>I x_ty model_ty\<close>
                                  else \<^Const>\<open>Identity_Elements\<^sub>E x_ty model_ty\<close>
      val (ants_delta, oblg_delta, cond_delta) =
              guess_conditions ctxt (prop_head, not is_intro) phi T_term

      fun pass_D D =
        case oblg_delta of Abs (_,_,\<^Const>\<open>True\<close>) => D
          | _ => Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (oblg_delta $ Bound 0) $ (D $ Bound 0))

      fun pass_P (Var v) = Var v
        | pass_P P =
            case cond_delta of Abs (_,_,\<^Const>\<open>True\<close>) => P
              | _ => Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (cond_delta $ Bound 0) $ (P $ Bound 0))

      val infer_P = if #is_recursive phi then I
                    else fn P => Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (P $ Bound 0) $ (Var(("P", 0), x_ty --> HOLogic.boolT) $ Bound 0))
      val infer_D = if #is_recursive phi then I
                    else fn D => Abs ("x", x_ty, \<^Const>\<open>HOL.conj\<close> $ (D $ Bound 0) $ (Var(("D", 0), x_ty --> HOLogic.boolT) $ Bound 0))

   in seq |> Seq.map (fn (D,P,ctxt) =>
        (maps (constrain_antecedents_by_boolean (simplified_exists_qualify ctxt x_ty cond_delta))
              (ants_delta @ ants),
         HOLogic.Trueprop $   
              (if is_intro then \<^Const>\<open>Identity_Elements\<^sub>I x_ty model_ty\<close> $ T_term $ infer_D (pass_D D) $ infer_P (pass_P P)
                           else \<^Const>\<open>Identity_Elements\<^sub>E x_ty model_ty\<close> $ T_term $ infer_D (pass_D D) ),
         NONE :: parse_inst_params_from_phi_term T_term,
         phi, ctxt))
  end

fun gen_id_ele is_left (_,name) instruction (phi0 : phi_type) thy =
  let val parse_hint = parse_hint (
            fn Const(\<^const_name>\<open>Identity_Elements\<^sub>I\<close>, _) $ T $ _ $ _ => T
             | Const(\<^const_name>\<open>Identity_Elements\<^sub>E\<close>, _) $ T $ _ => T
             | _ => raise TERM ("",[]))
      fun extract_oprs_from_hint (Const(\<^const_name>\<open>Identity_Elements\<^sub>I\<close>, _) $ _ $ D $ P) = [D,P]
        | extract_oprs_from_hint (Const(\<^const_name>\<open>Identity_Elements\<^sub>E\<close>, _) $ _ $ D) = [D]
        | extract_oprs_from_hint _ = []

      val equip_expansion = equip_expansion_ss phi0
      val ind_conv = default_ind_conv (
              fn ctxt => fn _ => fn ctm =>
                 (Conv.top_rewrs_conv @{thms' MAKE_def OPEN_def} ctxt then_conv
                  Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_noact} then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv) ctm,
              fn ctxt => fn _ => fn ctm =>
                 (Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_noact} then_conv
                  Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
                  Conv.implies_conv (Conv.rewr_conv @{thm' intro_\<phi>TA_ANT}) Conv.all_conv) ctm)

      val pre_simp = default_pre_simplifier (Phi_Conv.meta_alls_conv (fn ctxt => fn ctm =>
           (Phi_Reasoners.asm_rewrite true (equip_expansion ctxt) then_conv
            Conv.rewr_conv @{thm' \<phi>TA_common_rewr_imp2_rev}) ctm) o snd)

      val mode_infer = not (is_some (#1 instruction)) andalso not (#is_recursive phi0)
      val varify_subgoal = K (K NONE)

      fun reasoning phi =
        let val reasoner =
              if is_left
              then (fn ctxt => fn th =>
                      exhaustive_PLPR_reasoner_by_rule @{thm' \<phi>TA_Ident_I_rule_step}
                          (K (chk_unfolded [] ctxt phi)) ctxt th)
              else (fn ctxt => exhaustive_PLPR_reasoner (SOME 1) (K (chk_unfolded [] ctxt phi)) ctxt)
         in default_reasoning true default_reasoning_configure varify_subgoal reasoner phi
        end

      fun parse_abs (Abs (_, _, \<^Const>\<open>HOL.conj\<close> $ _ $ (Var v $ Bound 0))) = SOME v
        | parse_abs (Abs (_, _, \<^Const>\<open>HOL.conj\<close> $ _ $ Var v)) = SOME v
        | parse_abs X = if Term.is_schematic X then raise Match else NONE
      val id_ele_infer =
            if mode_infer
            then if is_left
            then predicate_infer true  (fn _ $ (_ $ _ $ P) => parse_abs P) (
                 predicate_infer false (fn _ $ (_ $ D $ _) => parse_abs D) (oblg_solver' name) )
            else predicate_infer false (fn _ $ (_ $ D ) => parse_abs D) (oblg_solver' name)
            else K NONE

      val simp = simplifier_by_cong [
              @{lemma' \<open> D \<equiv> D'
                    \<Longrightarrow> (\<And>x. D' x \<Longrightarrow> Satisfiable (x \<Ztypecolon> T) \<Longrightarrow> P x \<equiv> P' x)
                    \<Longrightarrow> Identity_Elements\<^sub>I T D P \<equiv> Identity_Elements\<^sub>I T D' P' \<close>
                      by (clarsimp simp add: Identity_Elements\<^sub>I_def Identity_Element\<^sub>I_def
                                             Transformation_def Satisfiable_def atomize_eq, blast)},
              @{lemma' \<open> D \<equiv> D'
                    \<Longrightarrow> Identity_Elements\<^sub>E T D \<equiv> Identity_Elements\<^sub>E T D' \<close>
                      by simp}
            ]

      val thy = thy
              |> Bundle.includes ["IDE_CP_Applications1.abstract_domain_OPEN_MAKE"]

      val rule = if is_left then @{thm' \<phi>TA_1L_rule} else @{thm' \<phi>TA_1R_rule}
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                     guess_property is_left, rule,
                                     [(SOME (default_ind_inst (fn [x] => [SOME x]), K I), ind_conv, reasoning)],
                                     id_ele_infer, pre_simp, simp)
                                    phi0 instruction thy
   in case Seq.pull rules
        of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
         | SOME (rule', _) => thy
            |> Local_Theory.declaration {syntax=false,pervasive=false, pos = #3 instruction} (
                fn m => fn lthy => lthy
                  |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
                  |> Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE'
                                        (SOME (the_default @{reasoner_group %derived_identity_element}
                                                           (#2 instruction)))
                                        ([],[]) NONE [Morphism.thm m rule']
                  |> Config.restore_generic Phi_Reasoner.trace lthy)
            |> note_properties_s false phi0 [(name, [rule'])]
            |> pair [rule']
  end

fun id_ele_properties pos is_intro (phi0 : phi_type) thy0 =
  let val (_,_,m_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      val inst = lift_types_sort (Proof_Context.theory_of thy0) [(m_ty0, \<^sort>\<open>one\<close>)]
      val inst' = Phi_Help.certify_tyvars (Context.Proof thy0) inst
      val phi = instantiate_phi (inst', Vars.empty) phi0

      val ((_, T_term), thy) = fix_phi_term_params phi thy0
      val (_,x_ty,m_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val trigger = (if is_intro then \<^Const>\<open>Identity_Elements\<^sub>I x_ty m_ty\<close>
                                 else \<^Const>\<open>Identity_Elements\<^sub>E x_ty m_ty\<close>) $ T_term
                 |> singleton (Variable.export_terms thy thy0)
                 |> Thm.cterm_of thy
                 |> Drule.mk_term

      val _ = if not (null (PLPR_Template_Properties.lookup_properties_match (Context.Proof thy0) (Thm.concl_of trigger)))
              then raise Automation_Fail (fn () => let open Pretty in
                      [para "The deriver of Identity_Element_Properties can only be invoked once\
                            \ for each \<phi>-type."]
                    end)
              else ()
   in thy0
   |> Local_Theory.declaration {syntax=false,pervasive=false, pos=pos} (
      fn m => fn lthy => lthy
        |> Config.map_generic Phi_Reasoner.trace (fn i=>i-1)
        |> PLPR_Template_Properties.add_property_instance (pos, Morphism.thm m trigger)
        |> Config.restore_generic Phi_Reasoner.trace lthy)
  end

val identity_element_I = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Identity_Element\<^sub>I") (gen_id_ele true)
val identity_element_E = deriver_framework (ACCEPT_ANY_HINTS, ONLY_ONCE_IF_NO_HINT, "Identity_Element\<^sub>E") (gen_id_ele false)


end