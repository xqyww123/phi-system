signature PHI_SYNTHESIS = sig

val gen_rule : Proof.context -> thm -> thm
val declare_rule : Position.T -> int -> thm list -> Context.generic -> Context.generic

end

structure Phi_Synthesis : PHI_SYNTHESIS = struct

fun gen_rule ctxt proc_thm0 =
  let val proc_thm = case Thm.concl_of proc_thm0
                       of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>All\<close>, _) $ _) => proc_thm0
                        | _ => Procedure_Syntax.package_argument ctxt proc_thm0
      val idx = Thm.maxidx_of proc_thm + 1
      val rule = Thm.instantiate (TVars.empty,
                                  Vars.make [((("G",0),\<^typ>\<open>prop\<close>), Thm.cprop_of proc_thm),
                                             ((("R",0),\<^typ>\<open>prop\<close>), Thm.var (("R", idx), \<^ctyp>\<open>prop\<close>))])
                     @{thm Gen_Synthesis_Rule}
   in (ctxt, Thm.implies_elim rule proc_thm)
   |> Phi_Reasoner.reason NONE
   |> (fn SOME (_, sequent) => sequent
        | NONE => Phi_Reasoner.error "Fail to extract the synthesis rule.")
   |> Raw_Simplifier.rewrite_rule ctxt @{thms True_implies_equals conjunction_imp}
   |> (fn sequent => (
            Phi_Reasoner.debug_pretty ctxt (fn () => Pretty.chunks [
                  Pretty.para "Obtain synthesis rule:",
                  Thm.pretty_thm ctxt sequent
                ]);
            sequent))
  end

fun declare_rule pos priority proc_thms0 ctxt0 =
  let val ctxt = Context.proof_of ctxt0
      val proc_thms = map (Drule.zero_var_indexes o gen_rule ctxt) proc_thms0
   in Phi_Reasoner.add_intro_rule pos priority ([],[]) NONE proc_thms ctxt0
  end



end