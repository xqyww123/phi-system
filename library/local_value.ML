signature LOCAL_VALUE = sig
  val mk_var_scope : Binding.binding list -> context_state -> context_state
end

structure Local_Value : LOCAL_VALUE = struct
open NuHelp PhiSyntax NuSys

fun local_value_export rule vars sequent =
  (Drule.forall_intr_list vars sequent) COMP rule
  handle e => Exn.reraise (@{print} e) 

fun mk_var_scope names (ctxt,sequent) =
  let
    val blk_var as (Free (blk_name,_)) = current_block_var sequent
    val blk_name = Variable.revert_fixed ctxt blk_name
    val arity = length names

    val op_var_scope = Proof_Context.get_thm ctxt "local.__\<phi>op_var_scope__"
    val op_var_scope0= Proof_Context.get_thm ctxt "local.__\<phi>op_var_scope__0"
    val op_var_scope' = op_var_scope
          |> ntimes (arity - 1) (fn _ => fn th => th RS op_var_scope)
          |> (fn thm => op_var_scope0 RS thm)
    val (ctxt,sequent) = NuApply.apply [op_var_scope'] (ctxt,sequent)

    val prem = Thm.cprem_of sequent 1
    (*declare fixes for local values*)
    val (vnames,ctxt) =
          Proof_Context.add_fixes (map (fn x => (x, SOME \<^typ>\<open>varname\<close>, NoSyn)) names) ctxt

    val vterms = map (fn name => Thm.cterm_of ctxt (Free (name, \<^typ>\<open>varname\<close>))) vnames
    val prem' = fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) vterms prem
    val (_,arg_nu,_) = dest_procedure_c prem'

    val ([], ctxt) =
      Proof_Context.add_assms (fn _ => fn [] => (local_value_export sequent vterms, I)) [] ctxt
  in
    start_proc blk_name arg_nu ctxt
  end

end

