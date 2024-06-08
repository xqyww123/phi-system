signature PHI_DELAY_APPLICATION = sig

val delay_app : thm list -> Proof.context -> Proof.context
val invoke_delayed_one : context_state -> context_state
val delayed_apps : Proof.context -> thm list list
val comma : context_state -> context_state

end

structure Phi_Delay_Application : PHI_DELAY_APPLICATION = struct

structure Delayed_Apps = Proof_Data (
  type T = thm list list
  val init = K []
)

fun delay_app app = Delayed_Apps.map (fn L => app :: L)
fun invoke_delayed_one s =
  let val that = hd (Delayed_Apps.get (fst s))
   in s
   |> apfst (Delayed_Apps.map tl)
   |> NuApply.apply that
  end
val delayed_apps = Delayed_Apps.get

val _ = Theory.setup (Context.theory_map (
  Phi_Toplevel.End_of_Statement.add 998 (K (fn s => (
    if null (delayed_apps (fst s)) then ()
    else warning "parenthesis is inbalanced!" ;
    s
  )))
#>Phi_Toplevel.Begining_of_Statement.add 1 (K (fn s => (
    if null (delayed_apps (fst s)) then ()
    else error "parenthesis is inbalanced!" ;
    s
  )))
))

val comma = I (*not implemented yet*)

end