signature LOCAL_VALUE = sig
end

structure Local_Value (* : LOCAL_VALUE *) = struct
open NuHelp NuBasics NuSys

fun local_value_export rule var [asm] major =
  (((Thm.implies_intr asm (finish_proc major) COMP @{thm impI})
    |> Thm.forall_intr var) COMP rule)
    |> accept_proc_naive
  |> @{print}

fun mk_let name meta ctx =
  let
    val blk_var as (Free (blk_name,_)) = current_block_var meta
    val meta = rename_blk_var
      ("\<nu>hide_"^(string_of_int (length (codeblocks_of meta)))^blk_name) meta
    val (major, aux) = elim_SPEC meta
    val major = apply_proc_naive @{thm op_let} major
    val prem = Thm.cprems_of major |> hd
    val (binder $ Abs (_, vty, body)) = term_of prem
    val ([name'],ctx) = Proof_Context.add_fixes [(name, SOME vty, NoSyn)] ctx
    val var_p = Thm.cterm_of ctx (Free (name', vty))
    val prem = Drule.beta_conv (Thm.dest_arg prem) var_p
    val (asm,proc) = dest_Trueprop_c prem
          |> dest_binop_c @{const_name implies}
    val (_,arg_nu,_) = dest_procedure_c proc
    val major' = start_proc ctx blk_name arg_nu
    val ([(_,[local_value_thm])], ctx) =
      Proof_Context.add_assms (fn _ => fn As => (local_value_export major var_p As, I))
        [((name,[]), [(term_of asm |> mk_Trueprop,[])])] ctx
    val push_local_value = local_value_thm RS @{thm op_local_value}
    val (_,ctx) = Proof_Context.note_thms ""
      ((Binding.suffix_name "_\<nu>proc" name,[]), [([push_local_value],[])]) ctx
  in
    (intro_SPEC (major', aux), ctx)
  end

end

