signature PHI_DELAY_APPLICATION = sig

structure Synt_No_Delayed_Apply : GENERIC_DATA
  val synt_can_delay_apply  : Context.generic -> Symtab.key -> bool
  val synt_can_delay_apply' : Context.generic -> Facts.ref -> bool

datatype delay_action = Apply of thm list | End_Block
val delay_app : delay_action -> Proof.context -> Proof.context
val invoke_delayed_one : context_state -> context_state
val delayed_apps : Proof.context -> delay_action list
val comma : context_state -> context_state

end

structure Phi_Delay_Application : PHI_DELAY_APPLICATION = struct

datatype delay_action = Apply of thm list | End_Block

structure Parenthesis_Stack = Proof_Data (
  type T = delay_action list
  val init = K []
)

fun delay_app app = Parenthesis_Stack.map (fn L => app :: L)

fun invoke_delayed_action (Apply rules) s = Phi_Apply.apply rules s
  | invoke_delayed_action End_Block s =
      raise Phi_Processor.Process_State_Call (s,
             Phi_Toplevel.end_block_auto_proof_cmd NONE false
          #> Proof.map_context (Parenthesis_Stack.map tl))

fun invoke_delayed_one s =
  let val that = hd (Parenthesis_Stack.get (fst s))
   in s
   |> apfst (Parenthesis_Stack.map tl)
   |> invoke_delayed_action that
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




structure Synt_No_Delayed_Apply = Generic_Data (
  type T = Symtab.set
  val empty = Symtab.empty
  val merge = Symtab.merge (op =)
)

fun synt_can_delay_apply ctxt sym =
  not (Symtab.defined (Synt_No_Delayed_Apply.get ctxt) sym)

fun synt_can_delay_apply' ctxt (Facts.Named ((name,_),_)) = synt_can_delay_apply ctxt name
  | synt_can_delay_apply' _ _ = true

val _ = Theory.setup (Context.theory_map (Synt_No_Delayed_Apply.map (
   Symtab.insert_set "if"
#> Symtab.insert_set "while"
)))

end