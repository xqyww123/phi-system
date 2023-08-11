signature PLPR_SIMPLIFIER = sig

(* The simplification only uses premises tagged by \<open>Premise default\<close> or \<open>Premise MODE_SIMP\<close>,
   or any extracted premises by means of Phi_Reasoners.extract_prem *)

val simplifier : (thm -> thm Seq.seq) -> (Proof.context -> Proof.context)
              -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss : (thm -> thm Seq.seq) -> simpset -> Proof.context -> thm -> thm Seq.seq
val simplifier_by_ss' : (thm -> thm Seq.seq) -> (Proof.context -> simpset)
                     -> Proof.context -> thm -> thm Seq.seq
val simplifier_only: (thm -> thm Seq.seq) -> (Proof.context -> thm list)
                  -> Proof.context -> thm -> thm Seq.seq

end

structure PLPR_Simplifier : PLPR_SIMPLIFIER = struct

fun simplification fallback F ctxt sequent = Seq.make (fn () =>
  sequent
    |> Conv.gconv_rule (Phi_Reasoners.asm_rewrite false (F ctxt)) 1
    |> (fn th => case Phi_Reasoner.single_RS' @{thm End_Simplification} ctxt th
                   of SOME ret => SOME (ret, Seq.empty)
                    | NONE => Seq.pull (fallback th))
)
(*    |> Tactical.HEADGOAL (Phi_Reasoners.simp_tac (F ctxt))
    |> Seq.map_filter (fn th =>
          (*case*) Phi_Reasoner.single_RS' @{thm End_Simplification} ctxt th
          (*of NONE => Phi_Reasoner.single_RS' @{thm End_Simplification'} ctxt th
             | some => some*))*)

fun simp_premis F ctxt sequent =
  (@{thm Premise_I} RS sequent)
    |> Tactical.HEADGOAL (Tactical.SOLVED' (Phi_Reasoners.asm_simp_tac false (F ctxt)))

fun simplifier fallback F ctxt sequent =
  case Thm.major_prem_of sequent
    of _ (*Trueprop*) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =>
            simp_premis F ctxt sequent
     | _ (*Trueprop*) $ (Const (\<^const_name>\<open>Simplify\<close>, _) $ _ $ _ $ _) =>
            simplification fallback F ctxt sequent
     | _ => Seq.empty


fun simplifier_only fallback thms = simplifier fallback (fn ctxt => clear_simpset ctxt addsimps (thms ctxt))
fun simplifier_by_ss  fallback ss = simplifier fallback (Raw_Simplifier.put_simpset ss)
fun simplifier_by_ss' fallback ss = simplifier fallback (fn ctxt => Raw_Simplifier.put_simpset (ss ctxt) ctxt)

end