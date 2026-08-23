signature PHI_CP_IDE = sig

type expr_id = Phi_ID.ID (*the address of each step of processing syntactic command*)

type config = string Symtab.table
type eval_cfg = { id : expr_id,
                  config : config,
                  toks: Token.src (*subsequent user inputs, may suppress certain automation
                                    such as the implicit existential quantification fixer when
                                    annotation \<open>\<exists>names...\<close> is given as the immediate user input.*)
                }

val set_expr_id : expr_id -> eval_cfg -> eval_cfg
val set_tokens : Token.src -> eval_cfg -> eval_cfg

structure Post_App : HOOKS

val call_of_state_sequent : (context_state -> context_state) -> Proof.state -> Proof.state
val proof_state_call : (Proof.state -> Proof.state) -> context_state -> context_state
val proof_state_call_result : (Proof.state -> 'a * Proof.state) -> context_state -> 'a * context_state

end

structure Phi_CP_IDE : PHI_CP_IDE = struct

type expr_id = Phi_ID.ID

type config = string Symtab.table
type eval_cfg = {id : expr_id, config : string Symtab.table, toks: Token.src}

(*set_expr_id carries an existing ID value and never rebuilds its counter: obligation
  streams sharing one address share its numbering exactly because they share the value.
  A counter that outlives its command -- a frame born in one command, minting in a later
  one -- is ticked again when only the later command re-executes: orphan keys, never
  collisions (plan §7 R4).*)
fun set_expr_id id' {id=_, config, toks} =
      {id=id', config=config, toks=toks}
fun set_tokens toks' {id, config, toks=_} =
      {id=id, config=config, toks=toks'}

structure Post_App = Hooks (
  type arg = eval_cfg
  type state = context_state
)

structure Proof_State_Call = Proof_Data (
  type T = Proof.state option
  val init = K NONE
)

fun call_of_state_sequent f s =
  let val sequent = Phi_Envir.the_state_sequent s
      val ctxt = Proof.context_of s
              |> Proof_State_Call.put (SOME s)
      val (ctxt', sequent') = f (ctxt, sequent)
      val s' = the (Proof_State_Call.get ctxt')
            |> Proof.map_context (K (Proof_State_Call.put NONE ctxt'))
            |> Phi_Envir.set_state_sequent sequent'
   in s'
  end

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

fun proof_state_call_result f (ctxt,sequent) =
  case Proof_State_Call.get ctxt
    of SOME s => let val (result, s') = s |> Proof.map_context (K ctxt)
                                          |> Phi_Envir.set_state_sequent sequent
                                          |> f
                     val ctxt' = Proof.context_of s'
                              |> Proof_State_Call.put (SOME s') 
                  in (result, (ctxt', Phi_Envir.the_state_sequent s'))
                 end
     | NONE => error "The environment of Proof_State_Call is not setup"


end