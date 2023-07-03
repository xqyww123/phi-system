signature PLPR_OPTIMUM_SOLUTION = sig

val internal_start  : context_state -> context_state Seq.seq
val internal_finish : context_state -> context_state Seq.seq
(* val choices: context_state -> context_state Seq.seq *)
val report_cost : int (*incremental-distance*) * int (*maximal-distance*)
              -> context_state -> context_state Seq.seq

val best_among : (Proof.context * thm list) -> thm option

end

structure PLPR_Optimum_Solution : PLPR_OPTIMUM_SOLUTION = struct

exception REACH of context_state
exception SUPER_REACH of context_state

type cost = int (*incremental-distance*) * int (*maximal-distance*)
val eval : cost -> int = Int.max
val timestamp_counter = Counter.make ()
fun timestamper () = ~ (timestamp_counter ())

structure Candidates = Heap (
  type elem = (int (*evaluated cost*) * int (*timestamp*) * context_state Seq.seq)
  fun ord ((c1,t1,_),(c2,t2,_)) = prod_ord int_ord int_ord ((c1,t1),(c2,t2))
)

structure Cost = Proof_Data (
  type T = cost
  val init = K (0,0)
)

structure Stack = Proof_Data (
  type T = ((int * Candidates.T) Synchronized.var * serial * serial) list
  val init = K []
)

(*fun choices (ctxt,sequent) = Seq.make (fn () =>
  case Stack.get ctxt
    of [] => SOME ((ctxt,sequent), Seq.empty)
     | ((heap_sync,_,_) :: _) => (
        let val cost = eval (Cost.get ctxt)
            val states = Phi_Reasoner.call_reasoners (ctxt,sequent)
                         |> map snd
                         |> Seq.of_list
                         |> Seq.flat
         in case Seq.pull states
              of NONE => NONE
               | SOME (s', states') =>
                    (Synchronized.change heap_sync
                                  (Candidates.insert ((cost,timestamper()), states'));
                     SOME (s', Seq.empty))
        end)) *)

fun report_cost (INC,THR) (ctxt,sequent) = Seq.make (fn _ =>
  let val (INC',THR') = Cost.get ctxt
      val next = (INC' + INC, Int.max (THR',THR))
      val cost = eval next
      val ctxt = Cost.put next ctxt
      fun prt () = Phi_Reasoner.info_pretty ctxt 1 (fn _ => Pretty.block [
                      Pretty.str "PLPR_Optimum_Solution: current score: ",
                      Pretty.str (string_of_int cost),
                      Pretty.str ", swithcing to another search branch..."
                   ])
   in case Stack.get ctxt
        of [] => SOME ((ctxt,sequent), Seq.empty)
         | ((heap_sync,_,_) :: _) =>
              Synchronized.change_result heap_sync (fn (min_cost, heap) =>
                 if cost <= min_cost
                 then (SOME ((ctxt,sequent), Seq.empty), (min_cost, heap))
                 else (prt (); (NONE, (min_cost, Candidates.insert (cost,timestamper(),
                                                Seq.single (ctxt,sequent)) heap))))
  end)

fun gen_finish reach (ctxt,sequent) = Seq.make (fn _ => (
  case Stack.get ctxt
    of [] => raise Fail "Not in a PLPR_Optimum_Solution environment"
     | ((_,sh,gcut) :: L ) =>
        let val _ = Phi_Reasoner.info_pretty ctxt 1 (fn _ => Pretty.block [
                      Pretty.str "PLPR_Optimum_Solution reaches a solution with cost ",
                      Pretty.str (string_of_int (eval (Cost.get ctxt)))])
            val ctxt' = ctxt
                 |> Stack.put L
                 |> Phi_Reasoner.Success_Handlers.remove sh
                 |> Phi_Reasoner.Global_Cut_Handlers.remove gcut
         in raise reach (ctxt',sequent)
        end
))

val internal_finish = gen_finish REACH

fun gen_start ctxt candidates = Seq.make (fn () =>
  let val var = Synchronized.var "PLPR_Optimum_Solution" (0, Candidates.empty)
      val (sh, ctxt) = ctxt
        |> Phi_Reasoner.Success_Handlers.push_localctxt 1 (fn s =>
                    SOME [ (\<^here>, gen_finish SUPER_REACH s) ])
      val (gcut, ctxt) = ctxt
        |> Phi_Reasoner.disable_global_cut 1
                    "Global Cut is prohibited during Optimum_Solution reasoning"
      val ctxt = Stack.map (fn L => (var,sh,gcut) :: L) ctxt
      val _ = Synchronized.change var (apsnd (
                  Candidates.insert (0, 0, Seq.of_list (map (pair ctxt) candidates))))
      fun get_heap (mc,heap) =
        if Candidates.is_empty heap
        then (NONE, (mc,heap))
        else let val ((cost,_,next), heap') = Candidates.min_elem heap
              in case Seq.pull next
                   of NONE => get_heap (cost,heap')
                    | SOME (s, remain) =>
                        if pointer_eq (remain, Seq.empty)
                        then (SOME s, (cost,heap'))
                        else (SOME s, (cost,Candidates.insert (cost,timestamper(),remain) heap'))
             end
      fun next_candidate () =
        case Synchronized.change_result var get_heap
          of NONE => (
              Phi_Reasoner.info_print ctxt 2 (fn _ =>
                "PLPR_Optimum_Solution: all choices are traversed, no solution found.");
              NONE)
           | SOME s =>
               (case Phi_Reasoner.internal_reason NONE s
                  of NONE => (Phi_Reasoner.info_print ctxt 2 (fn _ =>
                                "PLPR_Optimum_Solution: the search branch fails, try another");
                              next_candidate ())
                   | SOME s' => SOME (s', Seq.make next_candidate))
                handle REACH s => SOME (s, Seq.make next_candidate)
                     | SUPER_REACH s => raise Phi_Reasoner.Success s
   in next_candidate ()
   end
)

fun internal_start (ctxt,sequent) = gen_start ctxt [sequent]

fun best_among (_, []) = NONE
  | best_among (ctxt, [thm]) = Phi_Reasoner.reasonXXX NONE ctxt thm
  | best_among (ctxt,candidates) =
    ( Phi_Reasoner.info_pretty ctxt 1 (fn _ => Pretty.chunks (
          Pretty.str "PLPR_Optimum_Solution: reasoning the optimal solution from candidates:" ::
          map (fn th => Pretty.item [Thm.pretty_thm ctxt th]) candidates
        ));
      Phi_Reasoner.reason_sXXX ctxt (fn ctxt => ((), gen_start ctxt candidates))
        |> snd)

end
