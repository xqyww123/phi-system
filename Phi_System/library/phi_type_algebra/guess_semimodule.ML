signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS

val parse_semimodule_phityp : Proof.context
                           -> Phi_Type_Algebra.phi_type
                           -> (sort * sort) option (*optionally lift the types to (sort_scalar, sort_model)*)
                           -> typ * typ * typ * typ * Phi_Type_Algebra.phi_type

val Guess_Zip_of_Semimodule : Proof.context -> Phi_Type_Algebra.phi_type
                           -> typ * typ * typ * term -> term * term * term * term list * ctyp TVars.table

val Guess_Unzip_of_Semimodule : Proof.context -> Phi_Type_Algebra.phi_type
                           -> typ * typ * typ * term -> term * term * term * term list * ctyp TVars.table

val Guess_Scalar_One_E : guess_property

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

fun simplify_guessing_reasoning ctxt = Simplifier.simplify (Simplifier.clear_simpset ctxt addsimps
      @{thms' Premise_norm[where mode=\<open>default\<close>]
              Premise_norm[where mode=\<open>MODE_SIMP\<close>]
              Ant_Seq_reduct
              HOL.imp_conjR[folded Ant_Seq_def]
              HOL.all_conj_distrib[folded Ant_Seq_def]})

fun parse_semimodule_phityp ctxt phi0 lift_sorts =
  let val (reversed_argtys', x_ty0, model_ty0) = dest_parameterized_phi_ty (Term.fastype_of (#term phi0))
      fun err_parse () = raise Automation_Fail (fn () => let open Pretty in
                            [para "I only accept the semimodule \<phi>-type giving its element \<phi>-type as \
                                  \its last parameter and the sclara as its second last paramter. \
                                  \However, the parameters of the given \<phi>-type does not seem to meet \
                                  \this requirement."]
                        end)
      val (x_ele_ty0, s_ty0) = case reversed_argtys'
                  of (\<^Type>\<open>fun x_ele_ty \<^Type>\<open>set T_model_ty\<close>\<close> :: s_ty :: _) =>
                      if T_model_ty = model_ty0 then (x_ele_ty, s_ty) else err_parse ()
                   | _ => err_parse ()

      val (s_ty, x_ele_ty, x_ty, model_ty, phi) =
            case lift_sorts
              of SOME (sort_scalar, sort_model) =>
                  let val inst = lift_types_sort (Proof_Context.theory_of ctxt)
                                                 [(s_ty0, sort_scalar), (model_ty0, sort_model)]
                      val inst' = Phi_Help.certify_tyvars (Context.Proof ctxt) inst
                      val s_ty = Term_Subst.instantiateT inst s_ty0
                      val x_ty = Term_Subst.instantiateT inst x_ty0
                      val model_ty = Term_Subst.instantiateT inst model_ty0
                      val phi = instantiate_phi (inst',Vars.empty) phi0
                   in (s_ty, x_ele_ty0, x_ty, model_ty, phi)
                  end
               | NONE => (s_ty0, x_ele_ty0, x_ty0, model_ty0, phi0)

   in (s_ty, x_ele_ty, x_ty, model_ty, phi) (*TODO: extend me! return x_ele_ty!*)
  end

fun Guess_Scalar_One_E (phi : phi_type) ctxt =
  let val (s_ty, x_ele_ty, x_ty, model_ty, phi) = parse_semimodule_phityp ctxt phi NONE
      val idx = phi_maxidx_of phi ~1 + 1
      val ((_, FT_term), ctxt) = fix_phi_term_params (#term phi) ctxt
      val (F_term $ _ $ T_term) = FT_term

      val eta_F_term = Abs ("s", s_ty, Abs ("T", Term.fastype_of T_term, Abs ("x", x_ty,
                          \<^Const>\<open>\<phi>Type x_ty model_ty\<close> $ Bound 0 $ (Term.incr_boundvars 3 F_term $ Bound 2 $ Bound 1))))

      val goal_term =
            \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>Guess_Scalar_One\<^sub>E s_ty model_ty x_ele_ty x_ty\<close>
              $ \<^Const>\<open>Pure.type s_ty\<close>
              $ \<^Const>\<open>Pure.type model_ty\<close>
              $ \<^Const>\<open>Pure.type x_ele_ty\<close>
              $ \<^Const>\<open>Pure.type x_ty\<close>
              $ F_term $ eta_F_term $ T_term
              $ Var (("one", idx), s_ty)
              $ Var (("Dx", idx), x_ty --> HOLogic.boolT)
              $ Var (("f", idx), x_ty --> x_ele_ty)
              $ Var (("ants", idx), HOLogic.boolT)
              $ Var (("conds", idx), HOLogic.boolT))

      val reason = Conv.gconv_rule (HOLogic.Trueprop_conv (funpow 5 Conv.fun_conv (Conv.arg1_conv (
                      Conv.abs_conv (Conv.abs_conv (Conv.abs_conv (fn (_, ctxt) =>
                      fn ctm => Conv.rewrs_conv (map (fn th => th RS' (ctxt, @{thm' HOL.eq_reflection}))
                                           (#equations phi)) ctm) o snd) o snd) ctxt
                      )))) 1
                #> Phi_Reasoner.reason NONE NONE ctxt
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
        |> Option.map (apsnd (simplify_guessing_reasoning ctxt))
   of SOME (inst, ret) =>
       (case Thm.prop_of ret
          of _ (*Trueprop*) $ (_ (*Guess_Scalar_One\<^sub>E*) $ _ $ _ $ _ $ _
                $ F $ _ $ T $ one $ Dx $ f $ ants $ conds) =>
            let val ants = constrain_antecedents conds ants
                val head = \<^Const>\<open>Semimodule_Identity\<^sub>E s_ty x_ele_ty model_ty x_ty\<close>
                val prop = HOLogic.Trueprop $ (head $ F $ T $ one $ Dx $ f)
             in Seq.single (ants, prop,
                            NONE :: parse_parameters_of_phi_type (F $ Term.dummy $ T),
                            instantiate_phi (inst, Vars.empty) phi,
                            ctxt)
            end
           | _ => error "BUG")
    | NONE => guess_fail ctxt phi (K [])
  end

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
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
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
   in case Phi_Help.reason_tracing_tyinst ctxt reason goal_term
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



end