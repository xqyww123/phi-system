signature PLPR_OPTIMUM_SOLUTION = sig

val reason : context_state -> context_state Seq.seq
val report_cost : int (*incremental*) * int (*threshold*) -> Proof.context -> Proof.context

end

structure PLPR_Optimum_Solution : PLPR_OPTIMUM_SOLUTION = struct

structure Data = Proof_Data (
  type T = (int (*incremental*) * int (*threshold*)) list
  val init = K []
)

fun bad_envir () = Phi_Reasoner.bad_config "Not in Optimum_Solution reasoning!"

val enter = Data.map (fn L => (0,0) :: L)
val exit  = Data.map tl

fun report_cost (INC,THR) =
  Data.map (fn [] => bad_envir ()
             | ((INC',THR') :: L) => (INC' + INC, Int.max (THR',THR)) :: L)

fun cost ctxt =
  case Data.get ctxt
    of [] => bad_envir ()
     | (INC_THR :: _) => Int.max INC_THR

fun minimum ret [] = Option.map snd ret
  | minimum NONE (X::L) = minimum (SOME (cost (fst X), X)) L
  | minimum (SOME (C,X)) (X'::L) =
      let val C' = cost (fst X')
          val next = if C' < C then (C',X') else (C,X)
       in minimum (SOME next) L
      end

fun reason (ctxt,sequent) =
  let val (gsuc, ctxt) = ctxt
        |> enter
        |> Phi_Reasoner.disable_success "\<r>Sucess is disabled during Optimum_Solution reasoning!"
   in (ctxt,sequent)
   |> PLPR_Exhaustive_Divergence.begin (fn L => L
        |> minimum NONE
        |> (fn SOME X => Seq.single (X
                                  |> apfst (exit
                                         #> Phi_Reasoner.Success_Handlers.remove gsuc))
             | NONE   => Seq.empty ))
   end

end