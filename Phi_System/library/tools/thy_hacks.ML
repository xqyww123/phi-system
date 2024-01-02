signature PHI_HACKS = sig

structure Thy_At_Begin : HOOKS

end

structure Phi_Hacks : PHI_HACKS = struct

type thy_at_begin = theory -> theory option

structure Thy_At_Begin = Hooks (
  type arg = unit
  type state = theory
)

structure Thy_At_Begin_Version = Theory_Data (
  type T = string
  val empty = ""
  val merge = K ""
)

val _ = Theory.setup (Theory.at_begin (fn thy =>
  if Thy_At_Begin_Version.get thy = Context.theory_long_name thy
     orelse Thy_At_Begin.is_empty (Context.Theory thy)
  then NONE
  else SOME (thy |> Thy_At_Begin_Version.put (Context.theory_long_name thy)
                 |> Thy_At_Begin.invoke (Context.Theory thy) () )))

end