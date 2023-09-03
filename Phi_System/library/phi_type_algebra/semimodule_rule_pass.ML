(*it excludes scalar algebra of partial_ab_semigroup_add by adding excluding-pattern list*)
val phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar =
  (Phi_Type_Template_Properties.no_rule_generation_pass,
   fn _ => fn (data as ([rule], mode_prio, (pats, except), guard, ctxt)) =>
     (case PLPR_Syntax.find_tagged_premise \<^const_name>\<open>\<A>arith_eval\<close> rule
        of SOME (_, ret) =>
            (case ret of \<^Const_>\<open>HOL.eq ty\<close> $ _ $ _ =>
               (let val inst = Phi_Help.lift_types_sort (Context.theory_of ctxt)
                                                        [(ty, \<^sort>\<open>partial_ab_semigroup_add\<close>)]
                    val bad = Term_Subst.instantiate (inst, Vars.empty) (Thm.concl_of rule)
                           |> Phi_Reasoner.the_default_pattern_of ctxt
                 in ([rule], mode_prio, (pats, bad @ except), guard, ctxt)
                end
                handle Phi_Help.LIFT_FAIL _ => data)
              | _ => error "Malformed \<A>arith_eval: not an equation")
         | NONE => error "No \<A>arith_eval tag found"
      ) | data => data)