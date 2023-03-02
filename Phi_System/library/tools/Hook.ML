signature HOOK_ARG = sig
type arg
end

signature HOOKS = sig

type arg
type priority = int

(*One theory is not allowed to have two hooks having the identical priority.
  But the restriction is not applied between theories.*)
val add: priority -> (arg -> context_state -> context_state) -> Context.generic -> Context.generic
val remove: priority * string (*theory name*) -> Context.generic -> Context.generic
val invoke : arg -> context_state -> context_state

exception Success of context_state
val invoke_until_success : (arg -> context_state -> context_state) (*fallback*)
                        ->  arg -> context_state -> context_state
end

functor Hooks (Arg : HOOK_ARG) : HOOKS = struct

type arg = Arg.arg
type priority = int

structure PriorityTab = Table (
  type key = priority * serial
  val ord = prod_ord int_ord int_ord
)

structure Data = Generic_Data (
  type T = (arg -> context_state -> context_state) PriorityTab.table
  val empty = PriorityTab.empty
  val merge = PriorityTab.merge (K true)
)

fun add priority f ctxt =
  Data.map (PriorityTab.update_new (
      (priority, Context.theory_identifier (Context.theory_of ctxt)), f)) ctxt

fun remove (priority,thy) =
  Data.map (PriorityTab.delete_safe (priority, Context.theory_identifier (Thy_Info.get_theory thy)))

fun invoke arg (ctxt,sequent) =
      PriorityTab.fold (fn (_,f) => fn s => f arg s) (Data.get (Context.Proof ctxt)) (ctxt,sequent)

exception Success of context_state

fun invoke_until_success fallback arg (ctxt,sequent) =
  (PriorityTab.fold (fn (_,f) => fn s => f arg s) (Data.get (Context.Proof ctxt)) (ctxt,sequent)
   |> fallback arg)
  handle Success ret => ret

end