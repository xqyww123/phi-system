signature HOOK_ARG = sig
type arg
end

type priority = int (*small value is in higher priority to be executed*)

signature HOOKS = sig

type arg

(*In one theory two hooks having the identical priority are not allowed.
  But the restriction is not applied between theories.*)
val add: priority -> (arg -> context_state -> context_state) -> Context.generic -> Context.generic
val add': priority * theory (*the theory that the hook belongs to. A theory cannot contain
                              two hook having the identical priority*)
      -> (arg -> context_state -> context_state) -> Context.generic -> Context.generic
val remove: priority * string (*name of the theory belonging the hook*)
         -> Context.generic -> Context.generic
val remove': priority * theory (*the theory belonging the hook*)
         -> Context.generic -> Context.generic
val invoke : arg -> context_state -> context_state
val clean : Context.generic -> Context.generic

exception Success of context_state
val invoke_until_success : (arg -> context_state -> context_state) (*fallback*)
                        ->  arg -> context_state -> context_state
end

structure PriorityTab = Table (
  type key = priority * string
  val ord = prod_ord int_ord fast_string_ord
)

functor Hooks (Arg : HOOK_ARG) : HOOKS = struct

type arg = Arg.arg

structure Data = Generic_Data (
  type T = (arg -> context_state -> context_state) PriorityTab.table
  val empty = PriorityTab.empty
  val merge = PriorityTab.merge (K true)
)

fun add'' (priority, thy_id) f ctxt =
  Data.map (PriorityTab.update_new ((priority, thy_id), f)) ctxt

fun add' (priority, thy) f ctxt = add'' (priority, Context.theory_long_name thy) f ctxt

fun add priority f ctxt = add' (priority, Context.theory_of ctxt) f ctxt

fun remove' (priority,thy) =
  Data.map (PriorityTab.delete_safe (priority, Context.theory_long_name thy))

fun remove (priority,thy) = remove' (priority, Thy_Info.get_theory thy)

val clean = Data.map (K PriorityTab.empty)

fun invoke arg (ctxt,sequent) =
      PriorityTab.fold (fn (_,f) => fn s => f arg s) (Data.get (Context.Proof ctxt)) (ctxt,sequent)

exception Success of context_state

fun invoke_until_success fallback arg (ctxt,sequent) =
  (PriorityTab.fold (fn (_,f) => fn s => f arg s) (Data.get (Context.Proof ctxt)) (ctxt,sequent)
   |> fallback arg)
  handle Success ret => ret

end