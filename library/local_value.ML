signature LOCAL_VALUE = sig
  val mk_let : bool (*whether push local values back to the stack*)
    -> Binding.binding list -> thm -> Proof.context -> thm * Proof.context
end

structure Local_Value : LOCAL_VALUE = struct
open NuHelp NuBasics NuSys

fun local_value_export rule vars asms sequent =
  ((fold_rev Thm.implies_intr asms sequent |> @{print})
        |> Drule.forall_intr_list vars) COMP rule
  handle e => Exn.reraise (@{print} e) 

fun mk_let flag_push_back names sequent ctxt =
  let
    val blk_var as (Free (blk_name,_)) = current_block_var sequent
    val blk_name = Variable.revert_fixed ctxt blk_name
    val arity = length names

    val op_let = ntimes (arity - 1) (fn _ => fn th => th RS @{thm op_let}) @{thm op_let}
    val sequent = NuSys.apply ctxt [op_let] sequent

    val prem = Thm.cprem_of sequent 1
    val lrep_tys = strip_binder_vars @{const_name Pure.all} (term_of prem) |> map #2
    (*declare fixes for local values*)
    val (lrep_names,ctxt) = Proof_Context.add_fixes
          (map (Binding.suffix_name "\<^sub>v") names ~~ lrep_tys
              |> map (fn (a,b) => (a,SOME b,NoSyn))
          ) ctxt

    val lrep_terms = map (Thm.cterm_of ctxt o Free) (lrep_names ~~ lrep_tys)
    val prem = fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) lrep_terms prem
    val asm_proc = strip_binop_r_c @{const_name Pure.imp} prem
    val (asms,proc) = (front asm_proc, last asm_proc)
    val (_,arg_nu,_) = dest_procedure_c proc

    (*assume local values*)
    val rule = sequent
    val (asm_thms, ctxt) =
      Proof_Context.add_assms (fn _ => fn As => (local_value_export rule lrep_terms As, I))
        (names ~~ asms |> map (fn (n,a) => ((n,[]), [(term_of a,[])]))) ctxt
    val local_value_thms = map (snd #> hd) asm_thms

    (*set local \<nu>procedures - pushing the local value*)
    val push_local_values    = map (fn th => th RS @{thm op_local_value}) local_value_thms
    val (_,ctxt) = Proof_Context.note_thmss ""
      (names ~~ push_local_values |> map (fn (n,th) =>
        ((Binding.suffix_name "_\<nu>app" n,[]), [([th],[])]))) ctxt

    (*set local fact - \<nu>local_values*)
    val inhabit_local_values = map (fn th => th RS @{thm typing_inhabited}) local_value_thms
    val exisiting_local_values = Proof_Context.get_thms ctxt "\<nu>local_values"
    val ctxt = Proof_Context.put_thms true ("\<nu>local_values",
                SOME (inhabit_local_values @ exisiting_local_values)) ctxt

    (*declare term bindings*)
    val imgs = map (#3 o dest_triop @{const_name Refining}
                       o dest_Trueprop o Thm.prop_of) local_value_thms
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

