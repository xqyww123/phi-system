signature PHI_MODIFIER = sig

val by_rule : thm -> context_state -> context_state

val wrap_to_attribute : (context_state -> context_state) -> attribute
val apply_wrapped_attribute : attribute -> context_state -> context_state

end

structure Phi_Modifier : PHI_MODIFIER = struct

fun by_rule rule s =
  case Phi_Reasoner.single_RS' rule s
    |> Option.mapPartial (Phi_Reasoner.reason (SOME (Thm.nprems_of rule)))
    of NONE => Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
          Pretty.para "Fail to apply modifier rule:",
          Thm.pretty_thm (fst s) rule
        ]))
     | SOME s' => s'

fun wrap_to_attribute f (Context.Proof c, th) =
      (case f (c,th) of (c',th') => (SOME (Context.Proof c'), SOME th'))
  | wrap_to_attribute _ (Context.Theory _, _) =
      error ("This is a wrapped attribute from \<phi>modifier which cannot be applied on global theory.")

fun apply_wrapped_attribute attr (ctxt,sequent)
      = case attr (Context.Proof ctxt, sequent)
          of (SOME (Context.Proof ctxt'), SOME sequent') => (ctxt', sequent')
           | (SOME (Context.Proof ctxt'), _) => (ctxt', sequent)
           | (NONE, SOME sequent') => (ctxt, sequent')
           | (NONE, NONE) => (ctxt, sequent)
           | _ => error ("Bad attribute: it does not return a Context.Proof")

end