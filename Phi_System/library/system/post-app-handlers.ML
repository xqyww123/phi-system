signature PHI_CP_IDE = sig

type expr_id = int list (*Unique id of each step of processing syntactic command*)

val initial_expr_id : expr_id
val uptick_expr_id : expr_id -> expr_id
val subspace_expr_id : expr_id -> expr_id

type config = string Symtab.table
type eval_cfg = { id : expr_id,
                  oblg_no : int (*Which obligation this is within ONE Post_App.invoke.  A hook
                                  that solves an obligation re-enters the table from the top
                                  carrying the same arg (Hook.ML:100-105), so a second
                                  obligation of one operator application would otherwise
                                  compute the same proof id as the first -- and silently
                                  overwrite its proof in the store.  0 is the first, and its
                                  id is left exactly as it was, so no existing record moves.*),
                  config : config,
                  toks: Token.src (*subsequent user inputs, may suppress certain automation
                                    such as the implicit existential quantification fixer when
                                    annotation \<open>\<exists>names...\<close> is given as the immediate user input.*)
                }

val set_expr_id : expr_id -> eval_cfg -> eval_cfg
val set_tokens : Token.src -> eval_cfg -> eval_cfg
val uptick_oblg_no : eval_cfg -> eval_cfg

structure Post_App : HOOKS

val call_of_state_sequent : (context_state -> context_state) -> Proof.state -> Proof.state
val proof_state_call : (Proof.state -> Proof.state) -> context_state -> context_state
val proof_state_call_result : (Proof.state -> 'a * Proof.state) -> context_state -> 'a * context_state

end

structure Phi_CP_IDE : PHI_CP_IDE = struct

type expr_id = int list

val initial_expr_id = [0]
fun uptick_expr_id (i::L) = (i+1::L)
  | uptick_expr_id [] = error "BUG: expr_id cannot be empty"
fun subspace_expr_id L = 0 :: L

type config = string Symtab.table
type eval_cfg = {id : expr_id, oblg_no : int, config : string Symtab.table, toks: Token.src}

(*A new expression counts obligations afresh; new tokens of the same expression do not.*)
fun set_expr_id id' {id=_, oblg_no=_, config, toks} =
      {id=id', oblg_no=0, config=config, toks=toks}
fun set_tokens toks' {id, oblg_no, config, toks=_} =
      {id=id, oblg_no=oblg_no, config=config, toks=toks'}
fun uptick_oblg_no {id, oblg_no, config, toks} =
      {id=id, oblg_no=oblg_no+1, config=config, toks=toks}

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