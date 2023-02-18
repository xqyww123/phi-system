signature PLPR_SIMPLIFIER = sig

val simplifier : (Proof.context -> Proof.context) -> context_state -> context_state Seq.seq
val simplifier_only: (Proof.context -> thm list) -> context_state -> context_state Seq.seq

end

structure PLPR_Simplifier : PLPR_SIMPLIFIER = struct

fun simplifier F (ctxt,sequent) =
  (@{thm Do_Simplification} RS sequent)
    |> Tactical.HEADGOAL (Simplifier.simp_tac (F ctxt))
    |> Seq.map_filter (fn th =>
          case Phi_Reasoner.single_RS' @{thm End_Simplification} (ctxt,th)
            of NONE => Phi_Reasoner.single_RS' @{thm End_Simplification'} (ctxt,th)
             | some => some)

fun simplifier_only thms = simplifier (fn ctxt => clear_simpset ctxt addsimps (thms ctxt))

end