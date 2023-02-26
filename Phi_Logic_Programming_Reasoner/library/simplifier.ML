signature PLPR_SIMPLIFIER = sig

val default_simp_rule : thm

val simplifier : thm option -> (Proof.context -> Proof.context)
              -> context_state -> context_state Seq.seq
val simplifier_by_ss : thm option -> simpset -> context_state
                    -> context_state Seq.seq
val simplifier_by_ss' : thm option -> (Proof.context -> simpset)
                     -> context_state -> context_state Seq.seq
val simplifier_only: thm option -> (Proof.context -> thm list)
                  -> context_state -> context_state Seq.seq

end

structure PLPR_Simplifier : PLPR_SIMPLIFIER = struct

val default_simp_rule = @{thm Do_Simplification}

fun simplification rule F (ctxt,sequent) =
  (the_default default_simp_rule rule RS sequent)
    |> Tactical.HEADGOAL (Simplifier.simp_tac (F ctxt))
    |> Seq.map_filter (fn th =>
          case Phi_Reasoner.single_RS' @{thm End_Simplification} (ctxt,th)
            of NONE => Phi_Reasoner.single_RS' @{thm End_Simplification'} (ctxt,th)
             | some => some)

fun simp_premis F (ctxt,sequent) =
  (@{thm Premise_I} RS sequent)
    |> Tactical.HEADGOAL (Tactical.SOLVED' (Simplifier.simp_tac (F ctxt)))
    |> Seq.map (pair ctxt)

fun simplifier rule F (ctxt,sequent) =
  case Thm.major_prem_of sequent
    of _ (*Trueprop*) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =>
            simp_premis F (ctxt,sequent)
     | _ (*Trueprop*) $ (Const (\<^const_name>\<open>Simplify\<close>, _) $ _ $ _ $ _) =>
            simplification rule F (ctxt,sequent)
     | _ => Seq.empty


fun simplifier_only rule thms = simplifier rule (fn ctxt => clear_simpset ctxt addsimps (thms ctxt))
fun simplifier_by_ss  rule ss = simplifier rule (Raw_Simplifier.put_simpset ss)
fun simplifier_by_ss' rule ss = simplifier rule (fn ctxt => Raw_Simplifier.put_simpset (ss ctxt) ctxt)

end