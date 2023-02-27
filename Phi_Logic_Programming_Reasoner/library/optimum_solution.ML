signature PLPR_OPTIMUM_SOLUTION = sig

val start  : context_state -> context_state Seq.seq
val finish : context_state -> context_state Seq.seq
val report_cost : int (*incremental-distance*) * int (*maximal-distance*)
              -> context_state -> context_state Seq.seq

val best_among : (Proof.context * thm list) -> context_state option

end

structure PLPR_Optimum_Solution : PLPR_OPTIMUM_SOLUTION = struct

exception YIELD

type cost = int (*incremental-distance*) * int (*maximal-distance*)
val eval : cost -> int = Int.max

structure Candidates = Heap (
  type elem = (int (*evaluated cost*) * context_state Seq.seq)
  fun ord ((c1,_),(c2,_)) = int_ord (c1,c2)
)

structure Cost = Proof_Data (
  type T = cost
  val init = K (0,0)
)

structure Stack = Proof_Data (
  type T = (Candidates.T Synchronized.var * serial * serial) list
  val init = K []
)

fun choices (ctxt,sequent) = Seq.make (fn () =>
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
                    (Synchronized.change heap_sync (Candidates.insert (cost, states'));
                     SOME (s', Seq.empty))
        end))

fun report_cost (INC,THR) (ctxt,sequent) = Seq.make (fn _ =>
  let val (INC',THR') = Cost.get ctxt
      val next = (INC' + INC, Int.max (THR',THR))
      val cost = eval next
      val ctxt = Cost.put next ctxt
      fun prt () = Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.block [
                      Pretty.str "PLPR_Optimum_Solution: current score: ",
                      Pretty.str (string_of_int cost),
                      Pretty.str ", swithcing to another search branch..."
                   ])
      val ret = case Stack.get ctxt
                  of [] => SOME ((ctxt,sequent), Seq.empty)
                   | ((heap_sync,_,_) :: _) =>
                        Synchronized.change_result heap_sync (fn heap =>
                          if Candidates.is_empty heap
                          then (prt ();
                                (NONE, Candidates.insert (cost, Seq.single (ctxt,sequent)) heap))
                          else let val (min_cost, _) = Candidates.min heap
                            in if cost <= min_cost
                               then (SOME ((ctxt,sequent), Seq.empty), heap)
                               else (prt ();
                                   (NONE, Candidates.insert (cost, Seq.single (ctxt,sequent)) heap))
                            end)
   in if is_some ret
      then ret
      else raise YIELD
  end)

fun finish (ctxt,sequent) = Seq.make (fn _ => (
  case Stack.get ctxt
    of [] => SOME ((ctxt,sequent), Seq.empty)
     | ((_,sh,gcut) :: L ) =>
        let val _ = Phi_Reasoner.debug_pretty ctxt (fn _ => Pretty.block [
                      Pretty.str "The search reaches a solution with cost ",
                      Pretty.str (string_of_int (eval (Cost.get ctxt)))])
            val ctxt' = ctxt
                 |> Stack.put L
                 |> Phi_Reasoner.Success_Handlers.remove sh
                 |> Phi_Reasoner.Global_Cut_Handlers.remove gcut
         in SOME ((ctxt',sequent), Seq.empty)
        end
))

fun init candidates ctxt =
  let val var = Synchronized.var "PLPR_Optimum_Solution" Candidates.empty
      val (sh, ctxt) = ctxt
        |> Phi_Reasoner.Success_Handlers.push_local (fn s => SOME [(\<^here>, finish s)])
      val (gcut, ctxt) = ctxt
        |> Phi_Reasoner.disable_global_cut
                    "Global Cut is prohibited during Optimum_Solution reasoning"
      val ctxt = Stack.map (fn L => (var,sh,gcut) :: L) ctxt
      val _ = Synchronized.change var (
                  Candidates.insert (0, Seq.of_list (map (pair ctxt) candidates)))
   in var
  end

fun gen_start ctxt candidates = Seq.make (fn () =>
  let val var = init candidates ctxt
      fun get_heap heap =
        if Candidates.is_empty heap
        then (NONE, heap)
        else let val ((cost,next), heap') = Candidates.min_elem heap
              in case Seq.pull next
                   of NONE => get_heap heap'
                    | SOME (s, remain) =>
                        if pointer_eq (remain, Seq.empty)
                        then (SOME s, heap')
                        else (SOME s, Candidates.insert (cost,remain) heap')
             end
      fun next_candidate () =
        Synchronized.change_result var get_heap
          |> Option.mapPartial (fn s =>
                Phi_Reasoner.reason NONE s
                  |> Option.map (rpair (Seq.make next_candidate))
                handle YIELD => next_candidate ()
             )
   in next_candidate ()
   end
)

fun start (ctxt,sequent) = gen_start ctxt [sequent]

fun best_among (_, []) = NONE
  | best_among (ctxt, [thm]) = Phi_Reasoner.reason NONE (ctxt,thm)
  | best_among (ctxt,candidates) =
      Phi_Reasoner.reason_s ctxt (fn ctxt => ((), [gen_start ctxt candidates]))
        |> snd

end
