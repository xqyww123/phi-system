signature PHI_DELAY_APPLICATION = sig

val delay_app : thm list -> Proof.context -> Proof.context
val invoke_delayed_one : context_state -> context_state
val delayed_apps : Proof.context -> thm list list
val comma : context_state -> context_state

end

structure Phi_Delay_Application : PHI_DELAY_APPLICATION = struct

structure Parenthesis_Stack = Proof_Data (
  type T = thm list list
  val init = K []
)

fun delay_app app = Parenthesis_Stack.map (fn L => app :: L)


fun invoke_delayed_one s =
  let val that = hd (Parenthesis_Stack.get (fst s))
   in s
   |> apfst (Parenthesis_Stack.map tl)
   |> Phi_Apply.apply that
  end
val delayed_apps = Parenthesis_Stack.get

val _ = Theory.setup (Context.theory_map (
  Phi_Toplevel.End_of_Statement.add 998 (K (fn (ctxt,sequent) => (
    if not (null (delayed_apps ctxt))
       andalso Phi_Toplevel.previous_statement_is_finished ctxt
    then warning "parenthesis is inbalanced!"
    else () ;
    (ctxt,sequent)
  )))
#>Phi_Toplevel.Begining_of_Statement.add 1 (K (fn (ctxt,sequent) => (
    if not (null (delayed_apps ctxt))
       andalso Phi_Toplevel.previous_statement_is_finished ctxt
    then error "parenthesis is inbalanced!"
    else () ;
    (ctxt,sequent)
  )))
))

val comma = I (*not implemented yet*)

end