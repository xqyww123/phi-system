signature HOOK_ARG = sig
type arg
type state
end

type priority = int (*small value is in higher priority to be executed*)

signature HOOKS = sig

type arg
type state

(*In a theory two hooks having the identical priority are not allowed.
  But the restriction is not applied between theories.*)
val add: priority -> (arg -> state -> state) -> Context.generic -> Context.generic
val add': priority * theory (*the theory that the hook belongs to. A theory cannot contain
                              two hook having the identical priority*)
      -> (arg -> state -> state) -> Context.generic -> Context.generic
val remove: priority * string (*name of the theory belonging the hook*)
         -> Context.generic -> Context.generic
val remove': priority * theory (*the theory belonging the hook*)
         -> Context.generic -> Context.generic
val invoke : Context.generic -> arg -> state -> state
val clean : Context.generic -> Context.generic

exception Success of state
exception Redo_Entirely of arg * state
exception Return of state

val invoke_until_success : Context.generic
                        -> (arg -> state -> state) (*fallback*)
                        ->  arg -> state -> state
end

signature HANDLER_ARG = sig
type arg
type ret
end

signature HANDLERS = sig

type arg
type ret

(*In a theory two hooks having the identical priority are not allowed.
  But the restriction is not applied between theories.*)
val add: priority -> (arg -> ret option) -> Context.generic -> Context.generic
val add': priority * theory (*the theory that the hook belongs to. A theory cannot contain
                              two hook having the identical priority*)
      -> (arg -> ret option) -> Context.generic -> Context.generic

val remove: priority * string (*name of the theory belonging the hook*)
         -> Context.generic -> Context.generic
val remove': priority * theory (*the theory belonging the hook*)
         -> Context.generic -> Context.generic
val invoke : Context.generic -> arg -> ret option
val clean : Context.generic -> Context.generic

end

structure PriorityTab = Table (
  type key = priority * string
  val ord = prod_ord int_ord fast_string_ord
)

functor Hooks (Arg : HOOK_ARG) : HOOKS = struct

type arg = Arg.arg
type state = Arg.state

structure Data = Generic_Data (
  type T = (arg -> state -> state) PriorityTab.table
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

exception Success of state
exception Redo_Entirely of arg * state
exception Return of state

fun invoke ctxt =
  let val hooks = Data.get ctxt
      fun work arg s = PriorityTab.fold
                          (fn (_,f) => fn s => f arg s handle Return s' => s') hooks s
          handle Redo_Entirely (a,s) => work a s
   in work
  end

fun invoke_until_success ctxt fallback arg s =
  (PriorityTab.fold (fn (_,f) => fn s => f arg s) (Data.get ctxt) s
   |> fallback arg)
  handle Success ret => ret

end

functor Handlers (Arg : HANDLER_ARG) : HANDLERS = struct

type arg = Arg.arg
type ret = Arg.ret

structure Data = Generic_Data (
  type T = (arg -> ret option) PriorityTab.table
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

exception Success of ret
fun invoke ctxt arg =
     (PriorityTab.fold (fn (_,f) => fn () =>
          case f arg of SOME ret => raise Success ret | NONE => ())
      (Data.get ctxt) () ;
      NONE
     ) handle Success ret => SOME ret


end
