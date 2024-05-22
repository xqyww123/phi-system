signature GENERIC_ELEMENT_ACCESS = sig
include GENERIC_ELEMENT_ACCESS

type final_hook = cterm (*the term of the hook action like \<E>\<I>\<H>\<O>\<O>\<K>_none*)
               -> bool (*true for read or false for write*)
               -> Phi_Opr_Stack.opr_frame list * context_state
               -> Phi_Opr_Stack.opr_frame list * context_state

val evaluate_hook : final_hook
val register_hook : string * final_hook -> Context.generic -> Context.generic

end

structure Generic_Element_Access : GENERIC_ELEMENT_ACCESS = struct
open Generic_Element_Access

type final_hook = cterm (*the term of the hook action like \<E>\<I>\<H>\<O>\<O>\<K>_none*)
               -> bool (*true for read or false for write*)
               -> Phi_Opr_Stack.opr_frame list * context_state
               -> Phi_Opr_Stack.opr_frame list * context_state

structure Hooks = Generic_Data (
  type T = final_hook Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge pointer_eq
)

fun evaluate_hook action_term cfg oprs_stat =
  let val hook_name = case Term.head_of (Thm.term_of action_term)
                        of Const (N, _) => N
                         | _ => raise CTERM ("Bad action_term in Generic_Element_Access.evaluate_hook",
                                             [action_term])
   in case Symtab.lookup (Hooks.get (Context.Proof (#1 (#2 oprs_stat)))) hook_name
   of NONE => raise CTERM ("Bad action_term in Generic_Element_Access.evaluate_hook",
                           [action_term])
    | SOME hk => hk action_term cfg oprs_stat
  end

val register_hook = Hooks.map o Symtab.update_new


end