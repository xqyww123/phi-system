signature PHI_CP_IDE = sig

type processing_id = int (*Unique id of each step of processing syntactic command*)

structure Post_App : HOOKS

val proof_state_call : (Proof.state -> Proof.state) -> context_state -> context_state

end

structure Phi_CP_IDE : PHI_CP_IDE = struct

type processing_id = int

structure Post_App = Hooks (
  type arg = {id : processing_id, config : string Symtab.table, toks: Token.T list}
  type state = context_state
)

structure Proof_State_Call = Proof_Data (
  type T = Proof.state option
  val init = K NONE
)

fun proof_state_call f (ctxt,sequent) =
  case Proof_State_Call.get ctxt
    of SOME s => let val s' = s |> Proof.map_context (K ctxt)
                                |> Phi_Envir.set_state_sequent sequent
                                |> f
                     val ctxt' = Proof.context_of s'
                              |> Proof_State_Call.put (SOME s') 
                  in (ctxt', Phi_Envir.the_state_sequent s')
                 end
     | NONE => error "The environment of Proof_State_Call is not setup"

end