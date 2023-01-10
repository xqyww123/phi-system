signature HOOK = sig
val add: int -> (context_state -> context_state) -> Context.generic -> Context.generic
val invoke : context_state -> context_state
end

structure Hook : HOOK = struct
structure Data = Generic_Data (
  type T = (context_state -> context_state) PriorityTab.table
  val empty = PriorityTab.empty
  val merge = PriorityTab.merge (K true)
)

fun add priority f ctxt =
  Data.map (PriorityTab.update_new ((priority, Context.theory_id (Context.theory_of ctxt)), f)) ctxt

fun invoke (ctxt,sequent) =
      PriorityTab.fold (fn (_,f) => fn s => f s) (Data.get (Context.Proof ctxt)) (ctxt,sequent)

end