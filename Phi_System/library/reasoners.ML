signature NU_REASONERS = sig
  exception Attemption_Fail of Proof.context * thm
  val auto_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val auto_obligation_solver' : Proof.context * thm -> Proof.context * thm
  val safer_obligation_solver : Proof.context -> thm -> thm Seq.seq
  val safer_obligation_solver' : Proof.context * thm -> Proof.context * thm
  val premise_tac : Proof.context -> thm -> thm Seq.seq
  val asm_simp_tac : Proof.context -> thm -> thm Seq.seq
  val single_return : tactic -> tactic
  val wrap : (Proof.context -> thm -> thm Seq.seq) -> (context_state -> context_state Seq.seq)
end

structure Nu_Reasoners : NU_REASONERS = struct
open Thm Term

(** Preliminary **)

exception Attemption_Fail of Proof.context * thm

fun wrap tac (ctxt,thm) = tac ctxt thm |> Seq.map (pair ctxt)

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg prompt th = Seq.make (fn () => (@{print} prompt; @{print} th; SOME (th, Seq.empty))) *)

fun aux_thms ctxt = Named_Theorems.get ctxt \<^named_theorems>\<open>useful\<close>
                  @ Named_Theorems.get ctxt \<^named_theorems>\<open>\<phi>lemmata\<close>

(** Tactics **)

(*** Auxiliaries ***)

(*protects the remaining goals and only attach the first one*)
fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude

fun raw_auto' ctxt =
  let
    val imp = Proof_Context.get_thms ctxt "\<phi>implication_GE"
  in Method.insert_tac ctxt (aux_thms ctxt) 1
     THEN (if null imp then all_tac else resolve_tac ctxt imp 1)
     THEN Clasimp.auto_tac ctxt
  end
(*the classical 'auto' method that
  attacks only the first goal and returns only if the goal is solved*)
fun raw_auto ctxt =
  head_only (raw_auto' ctxt
          #> Seq.filter (fn st' => Thm.nprems_of st' = 0 (*check the only goal is solved*)))

(*Wrap a context tactic of type `Proof.context -> thm -> thm Seq.seq` to the
  transition between states, of type `Proof.context * thm -> Proof.context * thm`.
  *It only adopts the first result of applying the tactic, and drops other alternatives.*
  Because reasoners in the file only attack the first sub-goal and solves it totally or fails,
  this short-cut makes differences only when the sub-goal to be solved has some schematic variables
  to be instantiated during the tactic application.

  The semantics of schematic variables in these reasoners is, any possible instantiation is
  acceptable. Therefore, we choose the first result that a tactic returns.

  If the schematic variables are not able to be chosen arbitrarily, additional mechanisms have
  to be applied previously, for the case of state
  transition `Proof.context * thm -> Proof.context * thm`.*)
fun context_tactic_to_state_transition tac (ctxt, sequent) =
  case Seq.pull (tac ctxt sequent)
    of SOME (th', _) => (ctxt, th')
     | NONE => raise Attemption_Fail (ctxt, sequent)

(*** Premise tac ***)

(*Attack antecedents @{term "Premise mode P"} using the classical auto tactic.
It is the default tactic in the system intended to solve simple proof obligations.*)
fun auto_obligation_solver ctxt th =
  case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
    of SOME (_, \<^const>\<open>True\<close>) => Seq.single (@{thm Premise_True} RS th)
     | SOME _ => raw_auto ctxt th
     | NONE => Seq.empty

val auto_obligation_solver' = context_tactic_to_state_transition auto_obligation_solver

(*It is another tactic using 'clarsimp' method. It is weaker than 'auto' but much safer
and will usually terminate (if no loop is encountered in the simplification)*)
fun safer_obligation_solver ctxt th =
  case try PLPR_Syntax.dest_premise_tag (major_prem_of th)
    of SOME (_, \<^const>\<open>True\<close>) => Seq.single (@{thm Premise_True} RS th)
     | SOME _ => HEADGOAL (Clasimp.clarsimp_tac ctxt) th
     | NONE => Seq.single th

val safer_obligation_solver' = context_tactic_to_state_transition safer_obligation_solver

(*Insert a premise into a proof obligation*)
fun contract_obligations ctxt thm =
let open Conv in
  gconv_rule (bottom_conv (K (try_conv (rewrs_conv
    @{thms contract_premise_true
           contract_premise_imp contract_premise_all
     }))) ctxt) 1 thm
  |> fconv_rule (rewr_conv @{thm contract_obligations})
end

fun premise_tac ctxt thm =
  let
    val idx = tl (Thm.prems_of thm) |> find_index (fn tm =>
          case tm of (_ $ (@{term Proof_Obligation} $ _)) => true
                   | _ => false)
    val n = Thm.nprems_of thm
  in
    if idx = ~1
    then auto_obligation_solver ctxt thm
    else Thm.permute_prems 1 idx thm
      |> contract_obligations ctxt
      |> Thm.permute_prems 0 (~idx)
      |> (fn thm' => if Thm.nprems_of thm' = n - 1 then thm'
                     else raise Fail "BUG!!!")
      |> Seq.single
  end


fun asm_simp_tac ctxt =
  REPEAT (HEADGOAL (resolve_tac ctxt @{thms Premise_I})) THEN
  HEADGOAL (SOLVED' (Simplifier.asm_simp_tac (ctxt addsimps aux_thms ctxt)))
  

fun single_return tac s =
  Seq.make (fn () => 
    case Seq.chop 2 (tac s)
      of ([s'], _) => SOME (s', Seq.empty)
       | _ => NONE
  )


end
