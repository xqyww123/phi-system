signature PLPR_EXHAUSTIVE_DIVERGENCE = sig

val begin : (context_state list -> context_state Seq.seq) -> context_state -> context_state Seq.seq
val stop  : context_state -> context_state Seq.seq
val exit  : context_state -> context_state Seq.seq

end

structure PLPR_Exhaustive_Divergence : PLPR_EXHAUSTIVE_DIVERGENCE = struct

structure Data = Proof_Data (
  type T = context_state list Synchronized.var option list
  val init = K []
)

fun map_rev ret _ [] = ret
  | map_rev ret f (X::L) = map_rev (f X :: ret) f L

fun begin cb (ctxt,sequent) = Seq.make (fn () =>
  let val var = Synchronized.var "PLPR_Exhaustive_Divergence.collection" []
      val (suc, ctxt) = ctxt
               |> Data.map (fn L => SOME var :: L)
               |> Phi_Reasoner.disable_success
                            "Exceptional termination during PLPR_Exhaustive_Divergence"
      val (gcut, ctxt) = ctxt
               |> Phi_Reasoner.disable_global_cut
                            "Global Cut is prohibited during PLPR_Exhaustive_Divergence"
      val final = Seq.make (fn () =>
            Seq.pull (cb (Synchronized.value var
                       |> map_rev [] (apfst (Phi_Reasoner.Success_Handlers.remove suc
                                          #> Phi_Reasoner.Global_Cut_Handlers.remove gcut))
          )))
   in SOME ((ctxt,sequent), final)
  end)

fun stop (ctxt,sequent) = Seq.make (fn () =>
  case Data.get ctxt
    of [] => error "Inbalanced PLPR_Exhaustive_Divergence!"
     | (NONE :: _) => SOME ((ctxt,sequent), Seq.empty)
     | (SOME var :: _) =>
        let val ctxt' = Data.map (fn L => NONE :: tl L) ctxt
            val _ = Synchronized.change var (fn L => (ctxt',sequent) :: L)
         in NONE
        end)

fun exit (ctxt,sequent) = Seq.make (fn () =>
  let val ctxt' = Data.map tl ctxt
   in SOME ((ctxt', sequent), Seq.empty)
  end)

end