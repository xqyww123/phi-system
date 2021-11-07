signature LOCAL_VALUE = sig
  val mk_let : Binding.binding list -> thm -> Proof.context -> thm * Proof.context
end

structure Local_Value : LOCAL_VALUE = struct
open NuHelp NuBasics NuSys

fun local_value_export rule vars asms major =
  ((fold_rev Thm.implies_intr asms (finish_proc major) |> Drule.forall_intr_list vars) COMP rule)
    |> accept_proc_naive

fun mk_let names meta ctx =
  let
    val blk_var as (Free (blk_name,_)) = current_block_var meta
    val meta = rename_blk_var
      ("\<nu>hide_"^(string_of_int (length (codeblocks_of meta)))^blk_name) meta
    val (major, aux) = elim_SPEC meta
    val arity = length names
    val op_let = ntimes (arity - 1) (fn th => th RS @{thm op_let}) @{thm op_let}
    val major = apply_proc_naive op_let major
    val prem = Thm.cprems_of major |> hd
    val vtys = strip_binder_vars @{const_name Pure.all} (term_of prem) |> map #2
    val (names',ctx) = Proof_Context.add_fixes
      (names ~~ vtys |> map (fn (a,b) => (a,SOME b,NoSyn))) ctx
    val var_ps = map (Thm.cterm_of ctx o Free) (names' ~~ vtys)
    val prem = fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) var_ps prem
    val asm_proc = strip_binop_r_c @{const_name Pure.imp} prem
    val (asms,proc) = (front asm_proc, last asm_proc)
    val (_,arg_nu,_) = dest_procedure_c proc
    val major' = start_proc ctx blk_name arg_nu
    val (asm_thms, ctx) =
      Proof_Context.add_assms (fn _ => fn As => (local_value_export major var_ps As, I))
        (names ~~ asms |> map (fn (n,a) => ((n,[]), [(term_of a,[])]))) ctx
    val local_value_thms = map (snd #> hd) asm_thms
    val push_local_values = map (fn th => th RS @{thm op_local_value}) local_value_thms
    val (_,ctx) = Proof_Context.note_thmss ""
      (names ~~ push_local_values |> map (fn (n,th) =>
        ((Binding.suffix_name "_\<nu>proc" n,[]), [([th],[])]))) ctx
  in
    (intro_SPEC (major', aux), ctx)
  end

end

