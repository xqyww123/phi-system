signature LOCAL_VALUE = sig
  val mk_let : bool (*whether push local values back to the stack*)
    -> Binding.binding list -> thm -> Proof.context -> thm * Proof.context
end

structure Local_Value : LOCAL_VALUE = struct
open NuHelp NuBasics NuSys

fun local_value_export rule vars asms major =
  ((fold_rev Thm.implies_intr asms (finish_proc major) |> Drule.forall_intr_list vars) COMP rule)
    |> accept_proc_naive

fun mk_let flag_push_back names meta ctx =
  let
    val blk_var as (Free (blk_name,_)) = current_block_var meta
    val (old_codeblock, meta) = rename_blk_var
      ("\<nu>hide_"^(string_of_int (length (codeblocks_of meta)))^blk_name) meta
    val arity = length names
    val op_let = ntimes (arity - 1) (fn _ => fn th => th RS @{thm op_let}) @{thm op_let}
    val meta = NuSys.apply ctx [op_let] meta |> @{print}
    val (major, aux) = elim_SPEC meta
    val prem = Thm.cprems_of major |> hd
    val lrep_tys = strip_binder_vars @{const_name Pure.all} (term_of prem) |> map #2
    val (lrep_names,ctx) = Proof_Context.add_fixes
          (map (Binding.suffix_name "\<^sub>v") names ~~ lrep_tys
              |> map (fn (a,b) => (a,SOME b,NoSyn))
          ) ctx
    val lrep_terms = map (Thm.cterm_of ctx o Free) (lrep_names ~~ lrep_tys)
    val prem = fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) lrep_terms prem
    val asm_proc = strip_binop_r_c @{const_name Pure.imp} prem
    val (asms,proc) = (front asm_proc, last asm_proc)
    val (_,arg_nu,_) = dest_procedure_c proc
    val major' = start_proc ctx blk_name arg_nu
    val (asm_thms, ctx) =
      Proof_Context.add_assms (fn _ => fn As => (local_value_export (@{print}
      major) lrep_terms As, I))
        (names ~~ asms |> map (fn (n,a) => ((n,[]), [(term_of a,[])]))) ctx
    val local_value_thms = map (snd #> hd) asm_thms
    val push_local_values = map (fn th => th RS @{thm op_local_value}) local_value_thms
    val (_,ctx) = Proof_Context.note_thmss ""
      (names ~~ push_local_values |> map (fn (n,th) =>
        ((Binding.suffix_name "_\<nu>proc" n,[]), [([th],[])]))) ctx
    val (_,ctx) = Assumption.add_assms (fn _ => fn _ => (I,I)) [old_codeblock] ctx
    val meta = intro_SPEC (major', aux)
    val meta = if flag_push_back then
          fold_rev (accept_proc_naive oo apply_proc_naive) push_local_values meta
      else meta
  in
    (meta, ctx)
  end

end

