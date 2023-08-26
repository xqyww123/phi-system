signature PHI_REASONERS = sig

val pass_checks_priority : string (*name of the kind of the rules*)
                        -> int (*priority lower bound*)
                        -> Phi_Reasoner.rule_pass

end

structure Phi_Reasoners : PHI_REASONERS = struct

fun pass_checks_priority name prio = (fn pos => fn data =>
  if prio < #2 (#2 data)
  then data
  else error (let open Pretty in string_of (
          block (text "The priority of a" @
                 [brk 1, str (if name = "" then "reasoning" else name), brk 1] @
                 text "must be greater than" @
                 [brk 1, str (string_of_int prio), brk 1] @
                 here pos)
      )end)
  )

end