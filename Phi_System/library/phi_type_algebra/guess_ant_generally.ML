signature PHI_TYPE_ALGEBRA_DERIVERS = sig

val guess_antecedent : Proof.context -> Phi_Type_Algebra.phi_type
                    -> term (*constant of the property predicate*) -> term
                    -> term list (*existing guessed antecedents*)
                    -> term list (*augmented antecedents*)

end

structure Phi_Type_Algebra_Derivers : PHI_TYPE_ALGEBRA_DERIVERS = struct

fun guess_antecedent ctxt0 phi const assertion existing_antecedents =
  let val ([assertion], ctxt) = Variable.import_terms false [assertion] ctxt0
      val goal = ( HOLogic.Trueprop $ (
            \<^Const>\<open>Guess_Antecedent \<open>Term.fastype_of const\<close> \<open>Phi_Syntax.dest_BI_ty (Term.fastype_of assertion)\<close>\<close>
              $ const
              $ assertion
              $ Var (("g", 0), HOLogic.boolT)
              $ Var (("c", 0), HOLogic.boolT)) )
            |> Thm.cterm_of ctxt
            |> Goal.init
            |> Conv.gconv_rule (HOLogic.Trueprop_conv (Conv.fun_conv (Conv.arg1_conv (
                  Simplifier.rewrite (ctxt0 addsimps #equations phi))))) 1
   in case Phi_Reasoner.reason NONE NONE ctxt goal
   of NONE => existing_antecedents
    | SOME ret =>
        let fun flt tm = not (Term.is_schematic tm) andalso
                         not (Term.exists_Const (fn (\<^const_name>\<open>Satisfaction\<close>, _) => true | _ => false) tm)
            val (guessed, cond) = @{print} (
            case ret
              |> Simplifier.simplify ctxt
              |> singleton (Variable.export ctxt ctxt0)
              |> Thm.prop_of
              of _ (*Pure.protect*) $ (_ (*Trueprop*) $ (
                  Const(\<^const_name>\<open>Guess_Antecedent\<close>, _) $ _ $ _
                    $ guessed $ cond))
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