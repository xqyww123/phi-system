signature LOCAL_VALUE = sig
  val mk_let : bool (*whether push local values back to the stack*)
    -> Binding.binding list -> thm -> Proof.context -> thm * Proof.context
end

structure Local_Value : LOCAL_VALUE = struct
open NuHelp NuBasics NuSys

fun local_value_export rule vars asms sequent =
  (fold_rev Thm.implies_intr asms sequent
      |> Drule.forall_intr_list vars) COMP rule
  handle e => Exn.reraise (@{print} e) 

fun mk_var_scope flag_push_back names sequent ctxt =
  let
    val blk_var as (Free (blk_name,_)) = current_block_var sequent
    val blk_name = Variable.revert_fixed ctxt blk_name
    val arity = length names

    val op_var_scope = Proof_Context.get_thm ctxt "local.op_var_scope"
    val op_let = ntimes (arity - 1) (fn _ => fn th => th RS op_var_scope) op_var_scope
    val (ctxt,sequent) = NuSys.apply [op_let] (ctxt,sequent)

    val prem = Thm.cprem_of sequent 1
    (*declare fixes for local values*)
    val (lrep_names,ctxt) =
          Proof_Context.add_fixes (map (fn x => (x, SOME \<^typ>\<open>varname\<close>, NoSyn)) names) ctxt


    (*assume local values*)
    val rule = sequent
    val (asm_thms, ctxt) =
      Proof_Context.add_assms (fn _ => fn As => (local_value_export rule lrep_terms As, I))
        (names ~~ asms |> map (fn (n,a) => ((n,[]), [(term_of a,[])]))) ctxt
    val local_value_thms = map (snd #> hd) asm_thms


    (*set local fact - \<phi>local_values*)
    val inhabit_local_values = map (fn th => th RS @{thm typing_inhabited}) local_value_thms
    val exisiting_local_values = Proof_Context.get_thms ctxt "\<phi>local_values"
    val ctxt = Proof_Context.put_thms true ("\<phi>local_values",
                SOME (inhabit_local_values @ exisiting_local_values)) ctxt

    (*declare term bindings*)
    val imgs = map (Thm.prop_of #> dest_Trueprop
                      #> dest_binop @{const_name Set.member} #> #2
                      #> dest_binop @{const_name "\<phi>Type"} #> #1
                   ) local_value_thms
    val ctxt = fold Proof_Context.bind_term
                    (map (rpair 0 o Binding.name_of) names ~~ imgs)
                    ctxt

    (*the successive sequent*)
    val (sequent,ctxt) = start_proc NONE blk_name arg_nu ctxt
  in
    if flag_push_back
    then fold_rev (fn app => apfst (apply_proc_naive app) #-> accept_proc)
                  push_local_values (sequent, ctxt)
    else (sequent, ctxt)
  end

end

