signature PHISEM_CONTROL_FLOW = sig
include PHISEM_CONTROL_FLOW

val routine_mod : context_state -> context_state

end

structure PhiSem_Control_Flow : PHISEM_CONTROL_FLOW = struct

open PhiSem_Control_Flow

fun routine_mod (ctxt0,sequent) =
  let
    val (_,proc01,ctxt) = fix_leading_antecedent_meta_quantifiers ctxt0 sequent
    val proc0 = case proc01
                  of \<^const>\<open>Trueprop\<close> $ (X as Const(\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _)
                       => X
                   | X => raise TERM ("The leading subgoal is not a procedure", [X])
    val (_,X,Y,_) = Phi_Syntax.dest_procedure proc0
    val (v,X') = Procedure_Syntax.package_values "" \<^typ>\<open>unit\<close> true NONE X

    val sem_args  = Procedure_Syntax.dest_arg_tuple v
    val names = map (Variable.revert_fixed ctxt o Term.term_name) sem_args
    val names_ty  = Thm.ctyp_of ctxt (Phi_Syntax.mk_name_tylabels names)

    val arg_ty = fastype_of v                    |> Procedure_Syntax.dest_argT
    val ret_ty = domain_type (Term.fastype_of Y) |> Procedure_Syntax.dest_argT
    val f' = mk_parameterized_schematic_proc I (K I) ctxt arg_ty ret_ty "F"

    val simp_ctxt = clear_simpset ctxt
              addsimps (@{thms \<phi>V_simps named.case prod.sel id_apply} @
                        QuantExpansion.aux_expansions ctxt)
              addsimprocs [QuantExpansion.named_metaAll]
    val rule = @{thm "__routine__"}
            |> Thm.instantiate (TVars.make [((("'names",0), \<^sort>\<open>type\<close>), names_ty)], Vars.empty)
            |> Drule.infer_instantiate ctxt [(("X" ,0), Thm.cterm_of ctxt X'),
                                             (("vs",0), Thm.cterm_of ctxt v),
                                             (("F", 0), Thm.cterm_of ctxt f')]
            |> Simplifier.full_simplify simp_ctxt
            |> singleton (Proof_Context.export ctxt ctxt0)

    val norm_sequent = Phi_Helper_Conv.rewrite_leading_antecedent_hhf_concl simp_ctxt sequent
    val sequent1 = (rule RS norm_sequent)
   in (ctxt0, sequent1)
   |> Phi_Reasoner.reason NONE
   |> (fn SOME ret => ret
                   |> apfst (Context.proof_map (
                        Generic_Variable_Access.Process_of_Argument.put
                           (SOME Generic_Variable_Access.store_value_and_clean)))
        | NONE => Phi_Reasoner.error "Fail to apply the routine modifier.")
  end

end