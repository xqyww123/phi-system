signature PLPR_OPTIMUM_SOLUTION = sig

val start  : context_state -> context_state Seq.seq
val report_cost : int (*incremental*) * int (*threshold*) -> context_state -> context_state Seq.seq
val finish : context_state -> context_state Seq.seq

val best_among : (Proof.context * thm list) -> context_state option

end

structure PLPR_Optimum_Solution : PLPR_OPTIMUM_SOLUTION = struct

type cost = int (*incremental*) * int (*threshold*)
val eval : cost -> int = Int.max

structure Data = Proof_Data (
  type T = (cost * (int * context_state) option Synchronized.var) list
  val init = K []
)

fun report_cost (INC,THR) (ctxt,sequent) = Seq.make (fn _ =>
  case Data.get ctxt
    of [] => SOME ((ctxt,sequent), Seq.empty)
     | (((INC',THR'), optimum) :: L) =>
        let val next = (INC' + INC, Int.max (THR',THR))
            val cost = eval next
         in case Synchronized.value optimum
              of SOME (opt, _) =>
                  if opt < cost
                  then (Phi_Reasoner.debug_pretty ctxt (fn () => Pretty.block [
                        Pretty.str "PLPR_OPTIMUM_SOLUTION: Current score (",
                        Pretty.str (string_of_int cost),
                        Pretty.str ") exceeds the optimum score already reached (",
                        Pretty.str (string_of_int opt),
                        Pretty.str ") thus trimming the branch."
                      ])
                    ; NONE)
                  else SOME ((Data.put ((next, optimum) :: L) ctxt, sequent), Seq.empty)
               | NONE => SOME ((Data.put ((next, optimum) :: L) ctxt, sequent), Seq.empty)
        end
)

fun finish (ctxt,sequent) = Seq.make (fn _ => (
  case Data.get ctxt
    of [] => ()
     | (((INC',THR'), optimum) :: _) =>
        let val v = eval (INC',THR')
            val _ = Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.block [
                      Pretty.str "The search reaches a solution with cost ",
                      Pretty.str (string_of_int v)])
         in Synchronized.change optimum
               (fn x as SOME (opt, _) =>
                    if v < opt
                    then SOME (v, (ctxt,sequent))
                    else x
                 | NONE => SOME (v, (ctxt,sequent)))
            ; ()
        end
; NONE
))

fun init ctxt =
  let val var = Synchronized.var "PLPR_Optimum_Solution" NONE
      val frame = ((0,0), var)
   in (var, Data.map (fn L => frame :: L) ctxt)
  end

fun result var =
      case Synchronized.value var
        of NONE => NONE
         | SOME (_, (ctxt, sequent)) => SOME (Data.map tl ctxt, sequent)

fun start (ctxt,sequent) = Seq.make (fn () => Seq.pull
  let val (var, ctxt) = init ctxt
      val (sh, ctxt) = ctxt
        |> Phi_Reasoner.disable_success "Exceptional termination during Optimum_Solution reasoning!"
   in Seq.append
        (PLPR_Exhaustive_Divergence.begin Seq.of_list (ctxt,sequent))
        (Seq.make (fn () => result var
                         |> Option.map (apfst (Phi_Reasoner.Success_Handlers.remove sh)
                                     #> rpair Seq.empty)))
   end
)

fun best_among (_, []) = NONE
  | best_among (ctxt, [thm]) = Phi_Reasoner.reason NONE (ctxt,thm)
  | best_among (ctxt,candidates) =
      let val _ = Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.chunks (
            Pretty.str "Reasoning the optimal solution from candidates:" ::
            map (Thm.pretty_thm_item ctxt) candidates
          ))
          val (var, ctxt) = init ctxt
          val (sh, ret) = Phi_Reasoner.reason_s ctxt (fn ctxt => ctxt
                |> Phi_Reasoner.Success_Handlers.push_local (fn s => SOME [(0, \<^here>, finish s)])
                |> apsnd (fn ctxt => [(0, Seq.of_list (map (pair ctxt) candidates))]))
          val _ = if is_some ret then error "BUG #f1j90[3" else ()
       in result var
       |> Option.map (apfst (Phi_Reasoner.Success_Handlers.remove sh))
      end

end