signature PHI_TYPE_ALGEBRA_DERIVERS = sig

(*lame!
val guess_entire_property : Proof.context -> Phi_Type_Algebra.phi_type -> term -> term option*)

val guess_antecedent : Proof.context -> Phi_Type_Algebra.phi_type
                    -> term (*constant of the property predicate*) -> term
                    -> term list (*existing guessed antecedents*)
                    -> term list (*augmented antecedents*)


end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra

fun flt tm = not (Term.is_schematic tm) andalso
             not (Term.exists_Const (fn (\<^const_name>\<open>Satisfaction\<close>, _) => true | _ => false) tm)
(*lame! DO NOT REMOVE
fun guess_entire_property ctxt0 (phi : phi_type) property_const =
  let val idx = phi_maxidx_of phi ~1 + 1
      val property_const = Logic.incr_indexes ([], [], idx) property_const
      val ((x_term,T_term), ctxt) = fix_phi_term_params (#term phi) ctxt0
      val (_, x_ty, m_ty) = dest_parameterized_phi_ty (Term.fastype_of (#term phi))
      val assertion = \<^Const>\<open>\<phi>Type x_ty m_ty\<close> $ x_term $ T_term
      val goal = ( HOLogic.Trueprop $ (
            \<^Const>\<open>Guess_Property \<open>Term.fastype_of property_const\<close> \<open>Phi_Syntax.dest_BI_ty (Term.fastype_of assertion)\<close>\<close>
              $ property_const
              $ Var (("variantness", 0), HOLogic.boolT)
              $ assertion
              $ Var (("guessed_ant", 0), HOLogic.boolT)
              $ Var (("cond_of_ant", 0), HOLogic.boolT)
              $ (\<^Const>\<open>Some HOLogic.boolT\<close> $ Var (("guessed_concl",0), HOLogic.boolT)) ) )
            |> Thm.cterm_of ctxt
            |> Goal.init
            |> Conv.gconv_rule (HOLogic.Trueprop_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg1_conv (
                  Simplifier.rewrite (ctxt addsimps #equations phi)))))) 1

   in Phi_Reasoner.reason NONE NONE ctxt goal
   |> Option.map (fn ret =>
        case Thm.prop_of ( Goal.conclude ret
                        |> Simplifier.simplify (ctxt addsimps
                              @{thms' Premise_norm[where mode=\<open>default\<close>]
                                      Premise_norm[where mode=\<open>MODE_SIMP\<close>]
                                      Ant_Seq_reduct
                                      HOL.imp_conjR[folded Ant_Seq_def]
                                      HOL.all_conj_distrib[folded Ant_Seq_def]})
                        |> singleton (Variable.export ctxt ctxt0) )
          of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Guess_Property\<close>, _) $ _ $ _ $ _ $ GA $ CA $ (Const(\<^const_name>\<open>Some\<close>, _) $ GC))
               => let val (GA,CA) = apply2 (filter flt o PLPR_Syntax.dest_ant_sequence_or_HOL_conj) (GA,CA)
                      val cond' = PLPR_Syntax.mk_ant_sequence CA
                      fun agument_cond (\<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, X))
                            = \<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, agument_cond X)
                        | agument_cond X = \<^Const>\<open>HOL.implies\<close> $ cond' $ X
                      val ants = GA |> not (null CA) ? map agument_cond
                   in fold (fn P => fn X => Logic.implies $ (HOLogic.Trueprop $ P) $ X)
                           ants (HOLogic.Trueprop $ GC)
                  end
           | _ => error "BUG")
  end
*)

fun guess_antecedent ctxt0 phi const assertion existing_antecedents =
  let val ([assertion], ctxt) = Variable.import_terms false [assertion] ctxt0
      val goal = ( HOLogic.Trueprop $ (
            \<^Const>\<open>Guess_Property \<open>Term.fastype_of const\<close> \<open>Phi_Syntax.dest_BI_ty (Term.fastype_of assertion)\<close>\<close>
              $ const
              $ Var (("variantness", 0), HOLogic.boolT)
              $ assertion
              $ Var (("g", 0), HOLogic.boolT)
              $ Var (("c", 0), HOLogic.boolT)
              $ \<^Const>\<open>None HOLogic.boolT\<close>) )
            |> Thm.cterm_of ctxt
            |> Goal.init
            |> Conv.gconv_rule (HOLogic.Trueprop_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg1_conv (
                  Simplifier.rewrite (ctxt0 addsimps #equations phi)))))) 1
   in case Phi_Reasoner.reason NONE NONE ctxt goal
   of NONE => existing_antecedents
    | SOME ret =>
        let val (guessed, cond) = @{print} (
            case ret
              |> Simplifier.simplify (ctxt addsimps @{thms' Premise_norm[where mode=\<open>default\<close>]
                                                            Premise_norm[where mode=\<open>MODE_SIMP\<close>]
                                                            Ant_Seq_reduct
                                                            HOL.imp_conjR[folded Ant_Seq_def]
                                                            HOL.all_conj_distrib[folded Ant_Seq_def]})
              |> singleton (Variable.export ctxt ctxt0)
              |> Thm.prop_of
              of _ (*Pure.protect*) $ (_ (*Trueprop*) $ (
                  Const(\<^const_name>\<open>Guess_Property\<close>, _) $ _ $ _ $ _
                    $ guessed $ cond $ _))
                   => (guessed, cond)
                   |> apply2 (filter flt o PLPR_Syntax.dest_ant_sequence_or_HOL_conj)
               | _ => error "BUG" )

            val cond' = PLPR_Syntax.mk_ant_sequence cond
            fun agument_cond (\<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, X))
                  = \<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, agument_cond X)
              | agument_cond X = \<^Const>\<open>HOL.implies\<close> $ cond' $ X

         in (maps PLPR_Syntax.dest_ant_sequence_or_HOL_conj existing_antecedents @ guessed)
         |> not (null cond) ? map agument_cond
        end
  end

end
