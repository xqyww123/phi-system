signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val infer_the_default_scalar_domain : Proof.context -> typ * typ * typ -> term
val Guess_Zip_of_Semimodule : Proof.context -> Phi_Type_Algebra.phi_type
                           -> typ * typ * typ * term -> term * term * term * term list * ctyp TVars.table
val Guess_Unzip_of_Semimodule : Proof.context -> Phi_Type_Algebra.phi_type
                           -> typ * typ * typ * term -> term * term * term * term list * ctyp TVars.table
val semimodule_assoc_I : quiet -> hint list -> Phi_Type_Algebra.derive
val semimodule_assoc_E : quiet -> hint list -> Phi_Type_Algebra.derive

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers


fun reason_tracing_inst ctxt reason goal_term =
  let val tvars = Term.add_tvars goal_term []
      val vars  = Term.add_vars goal_term []
      val goal_term = goal_term
              |> fold_rev (fn NS => fn X => Logic.mk_conjunction (Logic.mk_term (Logic.mk_type (TVar NS)), X)) tvars
              |> fold_rev (fn NT => fn X => Logic.mk_conjunction (Logic.mk_term (Var NT), X)) vars
      val goal = Thm.cterm_of ctxt goal_term
              |> Goal.init
              |> funpow (length tvars) (fn th => Drule.termI RS (Conjunction.conjunctionI RS th))
              |> funpow (length vars) (fn th => Drule.termI RS (Conjunction.conjunctionI RS th))
   in reason goal
   |> Option.map (fn th =>
        let val th = Goal.conclude th
            val (tm_insts, th) = funpow_yield (length  vars) Conjunction.elim th
            val (ty_insts, th) = funpow_yield (length tvars) Conjunction.elim th
            val tm_insts = map Drule.dest_term tm_insts
            val ty_insts = map (Thm.dest_ctyp0 o Thm.ctyp_of_cterm o Drule.dest_term) ty_insts
         in ((TVars.make (tvars ~~ ty_insts), Vars.make (vars ~~ tm_insts)), th)
        end)
  end

fun reason_tracing_tyinst ctxt reason goal_term =
  let val tvars = Term.add_tvars goal_term []
      val goal_term = goal_term
              |> fold_rev (fn NS => fn X => Logic.mk_conjunction (Logic.mk_term (Logic.mk_type (TVar NS)), X)) tvars
      val goal = Thm.cterm_of ctxt goal_term
              |> Goal.init
              |> funpow (length tvars) (fn th => Drule.termI RS (Conjunction.conjunctionI RS th))
   in reason goal
   |> Option.map (fn th =>
        let val th = Goal.conclude th
            val (ty_insts, th) = funpow_yield (length tvars) Conjunction.elim th
            val ty_insts = map (Thm.dest_ctyp0 o Thm.ctyp_of_cterm o Drule.dest_term) ty_insts
         in (TVars.make (tvars ~~ ty_insts), th)
        end)
  end

fun Guess_Scalar_Assoc ctxt (phi : phi_type) =
  let val (T_ty :: s_ty :: rev_param_tys, x_ty, model_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      fun unsupported_ty () = raise Automation_Fail (fn () => let open Pretty in
              [para "Right now we only support semimodule \<phi>-type \<open>F s T\<close> whose element \<phi>-type is its \
                    \last parameter and the scalar is the last second."]
            end)
      val x_ele_ty = case dest_parameterized_phi_ty T_ty
                       of ([], x_ele_ty, model_ty') =>
                            if model_ty' = model_ty then x_ele_ty else unsupported_ty ()
                        | _ => unsupported_ty ()
      val idx = phi_maxidx_of phi ~1 + 1
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term

      val (ss, st) = (TVar (("s\<^sub>s", idx), \<^sort>\<open>type\<close>), TVar (("s\<^sub>t", idx), \<^sort>\<open>type\<close>))
      val (at, as_t) = (TVar (("a\<^sub>t", idx), \<^sort>\<open>type\<close>), TVar (("a\<^sub>s\<^sub>_\<^sub>t", idx), \<^sort>\<open>type\<close>))
      val (Fs, Ft) = (Var (("F\<^sub>s", idx), ss --> mk_phi_type_ty(model_ty, at) --> mk_phi_type_ty(model_ty, as_t)),
                      Var (("F\<^sub>t", idx), st --> mk_phi_type_ty(model_ty, x_ele_ty) --> mk_phi_type_ty(model_ty, at)))
      val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Scalar_Assoc s_ty model_ty x_ele_ty x_ty ss at as_t st\<close>
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ele_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ Fs $ Ft $ F_term $ F_term $ T_term
                $ Var(("Ds",0), ss --> HOLogic.boolT)
                $ Var(("Dt",0), st --> HOLogic.boolT)
                $ Var(("Dx",0), ss --> st --> as_t --> HOLogic.boolT)
                $ Var(("smul",0), ss --> st --> s_ty)
                $ Var(("f", 0), s_ty --> s_ty --> x_ty --> \<^Type>\<open>prod x_ty x_ty\<close>)
                $ Var(("antecedents", 0), HOLogic.boolT)
                $ Var(("conditions", 0), HOLogic.boolT))
      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 4 Conv.fun_conv (Conv.arg1_conv (
                      Conv.top_rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                               (#equations phi)) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case reason_tracing_tyinst ctxt reason goal_term
   of SOME (inst, ret) =>
        (case Thm.prop_of ( ret
                         |> Simplifier.simplify (ctxt addsimps
                                @{thms' Premise_norm[where mode=\<open>default\<close>]
                                        Premise_norm[where mode=\<open>MODE_SIMP\<close>]
                                        Ant_Seq_reduct
                                        HOL.imp_conjR[folded Ant_Seq_def]
                                        HOL.all_conj_distrib[folded Ant_Seq_def]}) )
           of _ (*Trueprop*) $ (_ (*Guess_Unzip_of_Semimodule*)
                    $ _ $ _ $ _ $ _ $ Ds $ Dx $ zi $ ants $ cond)
                => (Ds, Dx, zi, constrain_antecedents cond ants, inst)
            | _ => error "BUG")
    | NONE => raise Automation_Fail (fn () => let open Pretty in
              [block (text "Fail to guess the semimodule unzip operation as there is no registered \
                           \record giving the semimodule between scalar algebra" @
                      [brk 1, Syntax.pretty_typ ctxt s_ty, brk 1] @
                      text "abstrct algebra" @
                      [brk 1, Syntax.pretty_typ ctxt x_ty, brk 1] @
                      text "and concrete algebra" @
                      [brk 1, Syntax.pretty_typ ctxt model_ty, str ".", brk 1] @
                      text "You may either annotate the form of the rule or provide the record by"),
               block ([keyword1 "lemma", brk 1, str "[\<phi>reasoner]", brk 1,
                       str "\<open>", Syntax.pretty_term ctxt goal_term, str "\<close>"])]
            end)
  end

(*
fun infer_the_default_scalar_domain ctxt (s_ty, x_ty, model_ty) =
  let val g_Sdom = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>guess_domain_of_scalar s_ty model_ty x_ty\<close>
                                        $ \<^Const>\<open>Pure.type s_ty\<close>
                                        $ \<^Const>\<open>Pure.type model_ty\<close>
                                        $ \<^Const>\<open>Pure.type x_ty\<close>
                                        $ Var(("p",0), s_ty --> HOLogic.boolT))
   in Goal.init (Thm.cterm_of ctxt g_Sdom)
   |> Phi_Reasoner.reason NONE NONE ctxt
   |> (fn SOME ret => (case Thm.prop_of ret
                         of _ (*Pure.prop*) $ (_ (*Trueprop*) $ (_ (*guess_domain_of_scalar*)
                                    $ _ $ _ $ _ $ S)) => S
                          | _ => error "BUG")
        | _ => Abs("_", s_ty, \<^Const>\<open>True\<close>))
  end
*)


fun Guess_Unzip_of_Semimodule ctxt (phi : phi_type) (s_ty, x_ty, model_ty, typ_expr) =
  let val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Unzip_of_Semimodule s_ty model_ty x_ty\<close>
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ typ_expr
                $ Var(("scalar_domain",0), s_ty --> HOLogic.boolT)
                $ Var(("abstract_domain",0), s_ty --> s_ty --> x_ty --> HOLogic.boolT)
                $ Var(("zip", 0), s_ty --> s_ty --> x_ty --> \<^Type>\<open>prod x_ty x_ty\<close>)
                $ Var(("antecedents", 0), HOLogic.boolT)
                $ Var(("conditions", 0), HOLogic.boolT))
      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 4 Conv.fun_conv (Conv.arg1_conv (
                      Conv.top_rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                               (#equations phi)) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case reason_tracing_tyinst ctxt reason goal_term
   of SOME (inst, ret) =>
        (case Thm.prop_of ( ret
                         |> Simplifier.simplify (ctxt addsimps
                                @{thms' Premise_norm[where mode=\<open>default\<close>]
                                        Premise_norm[where mode=\<open>MODE_SIMP\<close>]
                                        Ant_Seq_reduct
                                        HOL.imp_conjR[folded Ant_Seq_def]
                                        HOL.all_conj_distrib[folded Ant_Seq_def]}) )
           of _ (*Trueprop*) $ (_ (*Guess_Unzip_of_Semimodule*)
                    $ _ $ _ $ _ $ _ $ Ds $ Dx $ zi $ ants $ cond)
                => (Ds, Dx, zi, constrain_antecedents cond ants, inst)
            | _ => error "BUG")
    | NONE => raise Automation_Fail (fn () => let open Pretty in
              [block (text "Fail to guess the semimodule unzip operation as there is no registered \
                           \record giving the semimodule between scalar algebra" @
                      [brk 1, Syntax.pretty_typ ctxt s_ty, brk 1] @
                      text "abstrct algebra" @
                      [brk 1, Syntax.pretty_typ ctxt x_ty, brk 1] @
                      text "and concrete algebra" @
                      [brk 1, Syntax.pretty_typ ctxt model_ty, str ".", brk 1] @
                      text "You may either annotate the form of the rule or provide the record by"),
               block ([keyword1 "lemma", brk 1, str "[\<phi>reasoner]", brk 1,
                       str "\<open>", Syntax.pretty_term ctxt goal_term, str "\<close>"])]
            end)
  end

fun Guess_Zip_of_Semimodule ctxt (phi : phi_type) (s_ty, x_ty, model_ty, typ_expr) =
  let val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Zip_of_Semimodule s_ty model_ty x_ty\<close>
                $ \<^Const>\<open>Pure.type s_ty\<close>
                $ \<^Const>\<open>Pure.type model_ty\<close>
                $ \<^Const>\<open>Pure.type x_ty\<close>
                $ typ_expr
                $ Var(("scalar_domain",0), s_ty --> HOLogic.boolT)
                $ Var(("abstract_domain",0), s_ty --> s_ty --> \<^Type>\<open>prod x_ty x_ty\<close> --> HOLogic.boolT)
                $ Var(("zip", 0), s_ty --> s_ty --> \<^Type>\<open>prod x_ty x_ty\<close> --> x_ty)
                $ Var(("antecedents", 0), HOLogic.boolT)
                $ Var(("conditions", 0), HOLogic.boolT))
      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 4 Conv.fun_conv (Conv.arg1_conv (
                      Conv.top_rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                               (#equations phi)) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case reason_tracing_tyinst ctxt reason goal_term
   of SOME (inst, ret) =>
        (case Thm.prop_of ( ret
                         |> Simplifier.simplify (ctxt addsimps
                                @{thms' Premise_norm[where mode=\<open>default\<close>]
                                        Premise_norm[where mode=\<open>MODE_SIMP\<close>]
                                        Ant_Seq_reduct
                                        HOL.imp_conjR[folded Ant_Seq_def]
                                        HOL.all_conj_distrib[folded Ant_Seq_def]}) )
           of _ (*Trueprop*) $ (_ (*Guess_Zip_of_Semimodule*)
                    $ _ $ _ $ _ $ _ $ Ds $ Dx $ zi $ ants $ cond)
                => (Ds, Dx, zi, constrain_antecedents cond ants, inst)
            | _ => error "BUG")
    | NONE => raise Automation_Fail (fn () => let open Pretty in
              [block (text "Fail to guess the semimodule zip operation as there is no registered \
                           \record giving the semimodule between scalar algebra" @
                      [brk 1, Syntax.pretty_typ ctxt s_ty, brk 1] @
                      text "abstrct algebra" @
                      [brk 1, Syntax.pretty_typ ctxt x_ty, brk 1] @
                      text "and concrete algebra" @
                      [brk 1, Syntax.pretty_typ ctxt model_ty, str ".", brk 1] @
                      text "You may either annotate the form of the rule or provide the record by"),
               block ([keyword1 "lemma", brk 1, str "[\<phi>reasoner]", brk 1,
                       str "\<open>", Syntax.pretty_term ctxt goal_term, str "\<close>"])]
            end)
  end

fun guess_property is_intro (phi0 : phi_type) ctxt =
  let val (s_ty, x_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi0 (\<^sort>\<open>type\<close>, \<^sort>\<open>sep_carrier\<close>)
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term
      (*val ([Dx_name], ctxt) = Variable.add_fixes ["Dx"] ctxt
      val Dx = Free(Dx_name, x_ty --> HOLogic.boolT)
      val AD = \<^Const>\<open>Abstract_Domain\<^sub>M\<^sub>C x_ty model_ty\<close> $ T_term $ Dx*)
      val Ds = infer_the_default_scalar_domain ctxt (s_ty, x_ty, model_ty)
   in Seq.single ([], \<^Const>\<open>Trueprop\<close> $ (xxxx (*(if is_intro then \<^Const>\<open>Semimodule_Scalar_Assoc\<^sub>I s_ty x_ty model_ty\<close>
                                                      else \<^Const>\<open>Semimodule_Scalar_Assoc\<^sub>E s_ty x_ty model_ty\<close>)*)
                                            $ F_term $ T_term $ Ds (* $ Dx *)),
                  NONE :: parse_parameters_of_phi_type FT_term, phi, ctxt)
  end

fun gen_MS is_intro (_, name) hint0 ctxt0 (phi : phi_type) thy =
  let val parse_hint = parse_hint (
            fn (Const(\<^const_name>\<open>Semimodule_Scalar_Assoc\<^sub>I\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _) => F1
             | (Const(\<^const_name>\<open>Semimodule_Scalar_Assoc\<^sub>E\<close>, _) $ F1 $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _) => F1
          )
      val extract_oprs_from_hint = K []
      fun reasoning phi ctxt =
        default_reasoning false (default_reasoning_configure []) (K (K NONE))
                          (exhaustive_PLPR_reasoner NONE (K (chk_unfolded' ctxt phi))) ctxt
      val simp = K I
      val ind_conv = default_ind_conv (
             fn _ => fn _ => Conv.rewr_conv @{thm \<phi>TA_MS_rewr},
             fn ctxt => fn phi =>
                  Conv.rewr_conv @{thm \<phi>TA_MS_rewr} then_conv
                  Conv.arg_conv (Conv.arg_conv (Phi_Conv.may_action_tag_conv (
                    let val sctxt = Expansion.equip ctxt addsimps (#equations phi @ #type_equations phi)
                     in Phi_Syntax.transformation_conv
                            (Simplifier.rewrite sctxt)
                            (Simplifier.rewrite sctxt)
                            (Conv.all_conv)
                    end))))
      val rules = deriving_framework (name, parse_hint, extract_oprs_from_hint,
                                      guess_property, (if is_intro then @{thm' \<phi>TA_MS\<^sub>I_rule} else @{thm' \<phi>TA_MS\<^sub>E_rule}),
                                      [(SOME ([0,2,~1,~1], ind_conv), reasoning),
                                       (SOME ([0,2,~1], ind_conv), reasoning)], K NONE, simp)
                                    phi hint0 ctxt0
   in case Seq.pull rules
   of NONE => raise Automation_Fail (fn () => [Pretty.str "Fail to derive any property"])
    | SOME (rule', _) => thy
        |> Phi_Help.generic_theory_mapping (fn m =>
              Phi_Reasoner.add_rule (#pos phi) Phi_Reasoner.TO_BE_OVERRIDE 40 ([],[]) NONE [Morphism.thm m rule'])
        |> note_properties_s phi [(name, [rule'])]
        |> pair [rule']
  end

val semimodule_assoc_I = deriver_framework
        (ACCEPT_ONE_HINT, ONLY_ONCE, "Semimodule_Scalar_Assoc\<^sub>I") gen_MS

end