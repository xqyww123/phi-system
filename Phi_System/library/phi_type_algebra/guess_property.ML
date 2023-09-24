signature PHI_TYPE_ALGEBRA_DERIVERS = sig
include PHI_TYPE_ALGEBRA_DERIVERS
(*lame!
val guess_entire_property : Proof.context -> Phi_Type_Algebra.phi_type -> term -> term option*)

val guess_antecedent : Proof.context
                    -> term (*constant of the property predicate*)
                     * bool (*True for covariant, False for contra-variant*)
                    -> Phi_Type_Algebra.phi_type -> term (*the target \<phi>-type term*)
                    -> term list (*augmented antecedents*)
                     * term (*augmented boolean antecedents*)
                     * term (*conditions*)

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct
open Phi_Type_Algebra Phi_Type_Algebra_Derivers

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
                                      Premise_norm[where mode=\<open>MODE_GUARD\<close>]
                                      Ant_Seq_reduct
                                      HOL.imp_conjR[folded Ant_Seq_def]
                                      HOL.all_conj_distrib[folded Ant_Seq_def]})
                        |> singleton (Variable.export ctxt ctxt0) )
          of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Guess_Property\<close>, _) $ _ $ _ $ _ $ GA $ CA $ (Const(\<^const_name>\<open>Some\<close>, _) $ GC))
               => let val (GA,CA) = apply2 (filter flt o PLPR_Syntax.dest_ant_sequence_or_HOL_conj) (GA,CA)
                      val cond' = PLPR_Syntax.mk_ant_sequence CA
                      fun agument_cond (\<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, X)) (*TODO: eta reduction!*)
                            = \<^Const>\<open>HOL.All t\<close> $ Abs (N, ty, agument_cond X)
                        | agument_cond X = \<^Const>\<open>HOL.implies\<close> $ cond' $ X
                      val ants = GA |> not (null CA) ? map agument_cond
                   in fold (fn P => fn X => Logic.implies $ (HOLogic.Trueprop $ P) $ X)
                           ants (HOLogic.Trueprop $ GC)
                  end
           | _ => error "BUG")
  end
*)

fun guess_antecedent ctxt0 (const, is_covar) phi T_term0 =
  let val ([T_term], ctxt) = Variable.import_terms false [T_term0] ctxt0
      val (x_ty, c_ty) = Phi_Syntax.dest_phi_type_ty (Term.fastype_of T_term)
      val goal = ( HOLogic.Trueprop $ (
            \<^Const>\<open>Guess_Property \<open>Term.fastype_of const\<close> x_ty c_ty\<close>
              $ const
              $ (if is_covar then \<^Const>\<open>True\<close> else \<^Const>\<open>False\<close>)
              $ T_term
              $ Var (("uT", 0), Term.fastype_of T_term)
              $ Var (("a", 0), HOLogic.boolT) $ Var (("g", 0), x_ty --> HOLogic.boolT)
              $ Var (("c", 0), x_ty --> HOLogic.boolT)
            ))
            |> Thm.cterm_of ctxt
            |> Goal.init
            |> Conv.gconv_rule (HOLogic.Trueprop_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg1_conv (
                  Simplifier.rewrite (ctxt0 addsimps #equations phi)))))) 1
   in case goal
        |> Phi_Reasoner.reason NONE NONE ( Config.map Phi_Reasoner.trace (fn i=>i-1) ctxt
                                        |> Phi_Type_Algebra_Derivers.Expansion.map' (fn ctxt => ctxt addsimps (#equations phi)))
   of NONE => raise Automation_Fail (fn () => let open Pretty in
                      [para "Fail to guess the property. \<phi>-LPR process of \<open>Guess_Property\<close> fails."]
                end)
    | SOME ret =>
        let val filter' = filter flt o PLPR_Syntax.dest_ant_sequence_or_HOL_conj
            val name = Term.declare_term_frees (Thm.prop_of ret) Name.context
            val (x_name, _) = Name.variant "\<x>" name
            val x = Free (x_name, x_ty)
            fun filter_lambda func =
              Term.lambda x (Phi_Help.list_mk_conj (filter' (Envir.beta_eta_contract (func $ x))))
         in case ret
         |> Simplifier.simplify (ctxt addsimps @{thms' Premise_norm[where mode=\<open>default\<close>]
                                                       Premise_norm[where mode=\<open>MODE_GUARD\<close>]
                                                       Ant_Seq_reduct
                                                       HOL.imp_conjR[folded Ant_Seq_def]
                                                       HOL.all_conj_distrib[folded Ant_Seq_def]})
         |> singleton (Variable.export ctxt ctxt0)
         |> Thm.prop_of
         of _ (*Pure.protect*) $ (_ (*Trueprop*) $ (
             Const(\<^const_name>\<open>Guess_Property\<close>, _) $ _ $ _ $ _ $ _
               $ ant $ oblg $ cond))
              => (filter' ant, filter_lambda oblg, filter_lambda cond)
          | _ => error "BUG"
        end
  end

end
