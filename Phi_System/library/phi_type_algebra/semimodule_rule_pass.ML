(*the pass adds an excluding-pattern to prevent applying the rule on any scalar algebra of
  partial_ab_semigroup_add *)
val phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar =
  (PLPR_Template_Properties.no_rule_generation_pass,
   fn _ => fn (data as ([rule], mode_prio, (pats, except), guard, ctxt)) =>
     (case PLPR_Syntax.find_premise (
             fn Const(\<^const_name>\<open>Action_Tag\<close>, _) $ (\<^Const_>\<open>HOL.eq ty\<close> $ _ $ _) $ Const(\<^const_name>\<open>\<A>arith_eq\<close>, _) =>
                  SOME ty
              | Const(\<^const_name>\<open>dabc_equation\<close>, \<^Type>\<open>fun ty _\<close>) $ _ $ _ $ _ $ _ =>
                  SOME ty
              | Const(\<^const_name>\<open>equation\<^sub>3\<^sub>1_cond\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>fun ty _\<close>\<close>\<close>) $ _ $ _ $ _ $ _ $ _ $ _ $ _ =>
                  SOME ty
              | _ => NONE
           ) rule
        of SOME ty =>
           (let val inst = Phi_Help.lift_types_sort (Context.theory_of ctxt)
                                                    [(ty, \<^sort>\<open>partial_ab_semigroup_add\<close>)]
                val bad = Term_Subst.instantiate (inst, Vars.empty) (Thm.concl_of rule)
                       |> Phi_Reasoner.the_default_pattern_of ctxt
             in ([rule], mode_prio, (pats, bad @ except), guard, ctxt)
            end
            handle Phi_Help.LIFT_FAIL _ => data)
         | NONE => raise THM ("No valid \<A>arith_eq nor dabc_equation found", 0, [rule])
      ) | data => data)