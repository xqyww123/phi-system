signature PLPR_SIMPLIFIER = sig

val simplifier : (Proof.context -> Proof.context)
              -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss : simpset -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss' : (Proof.context -> simpset)
                     -> Proof.context -> thm -> thm Seq.seq
val simplifier_only: (Proof.context -> thm list)
                  -> Proof.context -> thm -> thm Seq.seq

end

structure PLPR_Simplifier : PLPR_SIMPLIFIER = struct

fun simplification F ctxt sequent = Seq.make (fn () =>
  sequent
    |> Conv.gconv_rule (HOLogic.Trueprop_conv (Conv.arg_conv (
          Simplifier.rewrite (F ctxt)))) 1
    |> (fn th => Phi_Reasoner.single_RS' @{thm End_Simplification} ctxt th
                  |> Option.map (rpair Seq.empty))
)
(*    |> Tactical.HEADGOAL (Simplifier.simp_tac (F ctxt))
    |> Seq.map_filter (fn th =>
          (*case*) Phi_Reasoner.single_RS' @{thm End_Simplification} ctxt th
          (*of NONE => Phi_Reasoner.single_RS' @{thm End_Simplification'} ctxt th
             | some => some*))*)

fun simp_premis F ctxt sequent =
  (@{thm Premise_I} RS sequent)
    |> Tactical.HEADGOAL (Tactical.SOLVED' (Simplifier.simp_tac (F ctxt)))

fun simplifier F ctxt sequent =
  case Thm.major_prem_of sequent
    of _ (*Trueprop*) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =>
            simp_premis F ctxt sequent
     | _ (*Trueprop*) $ (Const (\<^const_name>\<open>Simplify\<close>, _) $ _ $ _ $ _) =>
            simplification F ctxt sequent
     | _ => Seq.empty


fun simplifier_only thms = simplifier (fn ctxt => clear_simpset ctxt addsimps (thms ctxt))
fun simplifier_by_ss  ss = simplifier (Raw_Simplifier.put_simpset ss)
fun simplifier_by_ss' ss = simplifier (fn ctxt => Raw_Simplifier.put_simpset (ss ctxt) ctxt)

end