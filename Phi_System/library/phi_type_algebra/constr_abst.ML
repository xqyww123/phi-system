signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val Make_Abstraction_from_Raw : quiet -> hint list -> Phi_Type.derive

end

structure Phi_Type_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type Phi_Type_Derivers

(*Guessing is not supported for recursive \<phi>-types*)

fun guess_property (phi:phi_type) ctxt =
  let val ((_, T_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val _ = if #is_recursive phi
              then raise Automation_Fail (fn () => [
                      Pretty.para "Guessing is not supported for recursive \<phi>-type. \
                                  \May manually annotate the expression."])
              else ()
      val (rev_arg_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun collect_params ret [] _  = ret
        | collect_params ret (arg_ty :: rev_arg_tys) (F' $ T') =
            case try dest_parameterized_phi_ty arg_ty
              of SOME dest => collect_params ((dest,T') :: ret) rev_arg_tys F'
               | NONE => collect_params ret rev_arg_tys F'
      val T_params = collect_params [] rev_arg_tys T_term

      fun mk_prop (P_term, f_term) ((rev_arg_tys, x_ty, model_ty), T_term) =
        let val arity = length rev_arg_tys
            val T'_term = fold_index (fn (i,_) => fn X => X $ Bound (arity - i)) rev_arg_tys T_term
         in HOLogic.all_const model_ty $ Abs ("x", model_ty,
              \<^Const>\<open>HOL.implies\<close>
                $ (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>default\<close> $ (P_term $ Bound 0))
                $ (\<^Const>\<open>Transformation model_ty\<close>
                    $ (\<^Const>\<open>\<phi>Type model_ty model_ty\<close> $ Bound 0 $ \<^Const>\<open>Itself model_ty\<close>)
                    $ (\<^Const>\<open>\<phi>Type x_ty model_ty\<close>
                          $ (f_term $ Bound 0)
                          $ (\<^Const>\<open>MAKE_from_RAW x_ty model_ty\<close> $ T'_term))
                    $ \<^Const>\<open>True\<close>))
         |> fold (fn T => fn X => HOLogic.all_const T $ Abs ("A", T, X)) rev_arg_tys
        end

      val P_types = map (fn ((_,_,m),_) => m --> HOLogic.boolT) T_params
      val P_fixes = Name.invent_names (Variable.names_of ctxt) "P" P_types
      val f_types = map (fn ((_,x,m),_) => m --> x) T_params
      val f_fixes = Name.invent_names (Variable.names_of ctxt) "f" f_types
      val ctxt = Variable.add_fixes_direct (map fst P_fixes @ map fst f_fixes) ctxt
      val fixes = map2 (fn P => fn f => (Free P, Free f)) P_fixes f_fixes

      val ants = map2 mk_prop fixes T_params 
      val idx = maxidx_of_phi phi ~1 + 1
      val prop = mk_prop (Var(("P",idx), model_ty --> HOLogic.boolT),
                          Var(("f",idx), model_ty --> x_ty))
                         (([], x_ty, model_ty), T_term)
   in Seq.single (ants, HOLogic.Trueprop $ prop,
                  NONE :: parse_inst_params_from_phi_term T_term, phi, ctxt)
  end

fun reasoning phi ctxt =
  let (*val extract_prem =
        if def_contains_satisfaction phi
        then (fn _ => fn th => [])
        else K (K [])*)
   in default_reasoning false
         (default_reasoning_configure [])
         (K (K NONE))
         (exhaustive_PLPR_reasoner NONE (K (chk_unfolded ctxt phi)))
         ctxt
  end

fun instantiate_the_var (vP, vf) ctxt sequent =
  let fun fail () = raise Automation_Fail (fn () => let open Pretty in
                      [para "The reasoning has succeeded, but I fail to infer the expression of the property\
                            \ from the generated proof obligations. Sorry but you have to indicate the \
                            \expression manually."] @
                      [Thm.pretty_thm ctxt sequent]
                    end)
      val target = case Phi_Help.leading_antecedent' sequent
                     of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_COLLECT\<close> $ X) => X
                      | _ => fail ()

      fun join_opt (SOME a, SOME b) = if a = b then SOME a else fail ()
        | join_opt (SOME a, _) = SOME a
        | join_opt (_, SOME b) = SOME b
        | join_opt _ = NONE
      fun conj_join ((Pa, fa), (Pb, fb)) = (Pa @ Pb, join_opt (fa, fb))
      fun disj_join ((Pa, fa), (Pb, fb)) =
            ([\<^Const>\<open>HOL.disj\<close> $ Phi_Help.list_mk_conj Pa $ Phi_Help.list_mk_conj Pb],
             join_opt (fa, fb))

      fun pass c (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) =
            conj_join (pass c A, pass c B)
        | pass c (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ A $ B) =
            disj_join (pass c A, pass c B)
        | pass (bvs,prems,meet) (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (N, Ty, X)) =
            pass ((N,Ty) :: bvs, map (Term.incr_boundvars 1) prems, Option.map (fn i => i + 1) meet) X
        | pass (bvs,prems,meet) (\<^Const>\<open>HOL.All T\<close> $ X) =
            pass (bvs,prems,meet) (\<^Const>\<open>HOL.All T\<close> $ Abs ("_", T, Term.incr_boundvars 1 X $ Bound 0))
        | pass (bvs,prems,meet) (Const(\<^const_name>\<open>HOL.implies\<close>, _)
                $ (P as (Const(\<^const_name>\<open>HOL.conj\<close>, _)
                            $ (Var vP' $ Bound i)
                            $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ (Var vf' $ Bound i'))))
                $ X) =
            if vP' = vP andalso vf' = vf
            then if i = i' andalso is_none meet then pass (bvs, prems, SOME i) X
                 else fail ()
            else fail ()
        | pass (bvs,prems,meet) (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ Pr $ X) =
            if Term.is_schematic Pr then fail ()
            else pass (bvs, Pr :: prems, meet) X
        | pass (_,_,meet) (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ (Var vf' $ Bound i') $ RHS) =
            if vf' = vf andalso is_some meet andalso the meet = i' andalso
               Term.loose_bnos RHS = [i']
            then ([], SOME (Term.subst_bounds (
                        List.tabulate (i'+1, fn i => if i = i' then Bound 0 else Term.dummy), RHS)))
            else fail ()
        | pass (bvs, prems, SOME i) Pr =
            if Term.is_schematic Pr
            then fail ()
            else let val cl = fold (fn P => fn X => \<^Const>\<open>HOL.conj\<close> $ P $ X) prems Pr
                           |> fold_index (fn (j,(N,Ty)) => fn X =>
                                  if j = i
                                  then Abs(N, Ty, X) $ Bound (length bvs - 1 - i)
                                  else \<^Const>\<open>HOL.Ex Ty\<close> $ Abs (N, Ty, X)
                              ) bvs
                  in ([cl], NONE)
                 end
        | pass _ _ = ([], NONE)

      val m_ty = Term.domain_type (snd vP)
      fun mk_P Ps = Abs ("c", m_ty, Phi_Help.list_mk_conj Ps)
      fun mk_F f  = Abs ("c", m_ty, f)
      val (P,f) = case pass ([], [], NONE) target
                    of (Ps, SOME f) => (mk_P Ps, mk_F f)
                     | (Ps, NONE  ) => (mk_P Ps, Abs ("x", m_ty, Bound 0))
      
   in Thm.instantiate (TVars.empty, Vars.make [(vP, Thm.cterm_of ctxt P),
                                               (vf, Thm.cterm_of ctxt f)]) sequent
  end

val rewr_CL = @{lemma \<open> Trueprop (Ant \<longrightarrow> P \<longrightarrow> X @action \<phi>TA_subgoal \<A>)
                       \<equiv> (Ant \<Longrightarrow> P \<Longrightarrow> X @action \<A>)\<close>
                     by (unfold Action_Tag_def atomize_imp)}

val rewr_IH = @{lemma \<open> Trueprop (Ant \<longrightarrow> P \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) @action \<phi>TA_subgoal \<A>)
                     \<equiv> (\<And>A. Ant \<Longrightarrow> P \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)\<close>
                   by (unfold Action_Tag_def atomize_imp Transformation_def, rule, blast, blast)}

val rewr_ant = @{lemma \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x @action to A \<equiv> \<forall>A y. \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = x \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X) \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T) \<close>
                    by (simp add: Transformation_def atomize_eq Action_Tag_def Premise_def, rule, blast, blast)}

fun gen_constr_from_raw (_,name) hint00 ctxt0 (phi0 : phi_type) thy =
  let fun chk_hint H =
        let fun chk_Tr (origin as Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ P) = (
                  (case Y of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _
                                $ (Const(\<^const_name>\<open>MAKE_from_RAW\<close>, _) $ _) => ()
                           | _ => raise Fail "") ;
                  (case X of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ Bound _ $ _ => ()
                           | Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _ =>
                                malformed_hint ctxt0 H (fn () => let open Pretty in
                                      [block (text "The abstract object" @
                                              [brk 1, Syntax.pretty_term ctxt0 x, brk 1] @
                                              text "must be universally quantified")]
                                  end)
                           | _ => malformed_hint ctxt0 H (K [])) ;
                  origin
                  )
              | chk_Tr _ = raise Fail ""
            fun chk_imp _ ((H as Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _) $ X) = H $ (chk_Tr X)
              | chk_imp premised ((H as Const(\<^const_name>\<open>HOL.All\<close>, _)) $ Abs (N,Ty,X))
                  = H $ Abs (N, Ty, chk_imp premised X)
              | chk_imp true  X = chk_Tr X
              | chk_imp false X = \<^Const>\<open>HOL.implies\<close>
                                    $ (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>default\<close> $ \<^Const>\<open>True\<close>)
                                    $ chk_Tr X
            fun chk _ (Const(\<^const_name>\<open>Pure.imp\<close>, _)
                      $ (A as (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ _)))
                      $ B)
                  = \<^Const>\<open>Pure.imp\<close> $ A $ chk true B
              | chk premised (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ A $ B)
                  = \<^Const>\<open>Pure.imp\<close> $ chk true A $ chk premised B
              | chk premised ((H as Const(\<^const_name>\<open>Pure.all\<close>, _)) $ Abs (N,Ty,X))
                  = H $ Abs (N,Ty, chk premised X)
              | chk premised (origin as (\<^Const>\<open>Trueprop\<close> $ X))
                  = (\<^Const>\<open>Trueprop\<close> $ chk_imp premised X
                     handle Fail _ => origin)
              | chk _ X = X
         in chk false H
        end

      val hint0 = Option.map chk_hint hint00

      val parse_hint = parse_hint (
            fn Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, _, Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _
                  $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ _
                      $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _
                          $ (Const(\<^const_name>\<open>MAKE_from_RAW\<close>, _) $ T))
                      $ _))
                => T
             | X => X)

      fun extract_oprs_from_hint
           (Const(\<^const_name>\<open>HOL.All\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _)
                  $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ Px)
                  $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ _
                      $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ fx $ _))
                      $ _ )) = [Px, fx]
        | extract_oprs_from_hint _ = []

      val equip_expansion = equip_expansion_ss phi
      val ind_conv = default_ind_conv (
            fn _ => fn _ =>
                Conv.rewr_conv rewr_IH,
            fn ctxt => fn phi =>
                Conv.rewr_conv rewr_CL then_conv
                Conv.implies_conv
                  (Conv.top_rewrs_conv [rewr_ant] ctxt)
                  (let val sctxt = equip_expansion ctxt addsimps (#equations phi)
                    in Phi_Reasoners.asm_rewrite false sctxt
                   end))

      val mode_infer = not (is_some hint0)
      fun simp (_, ctxt) rule =
        if mode_infer
        then rule
         |> Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
              HOLogic.Trueprop_conv (Phi_Conv.hol_all_conv (fn (_, ctxt) =>
                let val sctxt = Simplifier.add_cong @{thm HOL.conj_cong} ctxt
                                addsimps [@{thm special_Ex_def}]
                 in fn ctm => Phi_Conv.hol_imp_conv
                      (Simplifier.rewrite sctxt)
                      (Phi_Syntax.transformation_conv
                          Conv.all_conv
                          (Conv.arg1_conv (Simplifier.rewrite sctxt))
                          Conv.all_conv) ctm
                end
              ) ctxt)) ctxt)
         |> (fn rule => (rule RS' (ctxt, @{thm' spec})))
        else rule

      fun solver (phi, ctxt, sequent) =
            case Thm.concl_of sequent
              of _ (*Trueprop*) $ (\<^Const>\<open>All _\<close> $ Abs (_, _,
                      \<^Const>\<open>HOL.implies\<close>
                        $ (\<^Const>\<open>Premise\<close> $ _ $ P)
                        $ (\<^Const>\<open>Transformation _\<close> $ _ $ (\<^Const>\<open>\<phi>Type _ _\<close> $ f $ _) $ _ )
                      ))
                   => (case (P,f) of (Var vP $ _ , Var vf $ _) =>
                                    instantiate_the_var (vP,vf) ctxt sequent
                                 |> oblg_solver (#proof_id phi ^ "/" ^ name) ctxt
                                 |> SOME
                         | _ => NONE)
               | _ => error "BUG"


      val ctxt0' = if is_some hint0 then ctxt0
                   else Config.put Phi_Reasoners.existential_obligation 2 ctxt0
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property, @{thm' \<phi>TA_TrCstr_rule},
                                      [(SOME ([0,~1], ind_conv), reasoning)],
                                      solver, simp)
                                    phi0 hint0 ctxt0'
   in case Seq.pull rules
   of SOME (rule, _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
                  Phi_Reasoner.add_rule (#pos phi0) Phi_Reasoner.TO_BE_OVERRIDE 80
                                              ([],[]) NONE [Morphism.thm m rule])
        |> note_properties phi0 [(name, [rule])]
        |> pair [rule]
    | _ => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
  end

val Make_Abstraction_from_Raw = deriver_framework
      (ACCEPT_ONE_HINT, ONLY_ONCE, "Make_Abstraction_from_Raw") gen_constr_from_raw

end

