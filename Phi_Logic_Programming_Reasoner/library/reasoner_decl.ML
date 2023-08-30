signature NU_REASONER = sig

type priority = int
type pattern = term
type name = term
type ML_guard = context_state -> bool
type action = cterm

  datatype cut_mode = NO_CUT | LOCAL_CUT | GLOBAL_CUT
  datatype backtrack_mode = ALLOW_BACKTRACK | NO_BACKTRACK | NO_EXPLORATIVE_BACKTRACK
  type mode = cut_mode * backtrack_mode
  (* declare by NO_BACKTRACK to disable applying the reasoner during backtracking.
        It causes the reasoner will not be applied once there is another reasoner of a higher priority,
        no matter if that reasoner's application succeeds.
        It is therefore useful to declare `default' rules which works when user does not give any
        specific rule and to be overrided once any rule is given.

     In exhaustive reasoning mode, in order to obtain all reachable solution of a reasoning goal,
     the reasoning will not terminate even when a success is reached. Instead, a special `explorative'
     backtrack is triggered to backtrack to other branches.
     NO_EXPLORATIVE_BACKTRACK disables the rule to be applied in this explorative backtracking.
     It can be for consideration of performance.
 *)
  val mode_ord : mode * mode -> order
  val NORMAL_MODE : mode
  val NORMAL_LOCAL_CUT : mode
  val TO_BE_OVERRIDE : mode

  datatype backtracking = NO_BACKTRACKING | BACKTRACKING | EXPLORATIVE_BACKTRACKING

  val cut_mode_parser : cut_mode parser
  val backtrack_mode_parser : backtrack_mode parser
  val default_mode_of : priority -> cut_mode

end

structure Phi_Reasoner : NU_REASONER = struct

type priority = int
type pattern = term
type name = term
type ML_guard = context_state -> bool
type action = cterm

datatype cut_mode = NO_CUT | LOCAL_CUT | GLOBAL_CUT
datatype backtrack_mode = ALLOW_BACKTRACK | NO_BACKTRACK | NO_EXPLORATIVE_BACKTRACK
type mode = cut_mode * backtrack_mode

val NORMAL_MODE = (NO_CUT, ALLOW_BACKTRACK)
val NORMAL_LOCAL_CUT = (LOCAL_CUT, ALLOW_BACKTRACK)
val TO_BE_OVERRIDE = (NO_CUT, NO_BACKTRACK)

(* NO_CUT < LOCAL_CUT < GLOBAL_CUT *)
fun cut_mode_ord (GLOBAL_CUT, GLOBAL_CUT) = EQUAL
  | cut_mode_ord (LOCAL_CUT, GLOBAL_CUT) = LESS
  | cut_mode_ord (LOCAL_CUT, LOCAL_CUT) = EQUAL
  | cut_mode_ord (NO_CUT, NO_CUT) = EQUAL
  | cut_mode_ord (NO_CUT, _) = LESS
  | cut_mode_ord _ = GREATER

(* ALLOW_BACKTRACK < NO_EXPLORATIVE_BACKTRACK < NO_BACKTRACK *)
fun backtrack_mode_ord (NO_BACKTRACK, NO_BACKTRACK) = EQUAL
  | backtrack_mode_ord (NO_EXPLORATIVE_BACKTRACK, NO_BACKTRACK) = LESS
  | backtrack_mode_ord (NO_EXPLORATIVE_BACKTRACK, NO_EXPLORATIVE_BACKTRACK) = EQUAL
  | backtrack_mode_ord (ALLOW_BACKTRACK, ALLOW_BACKTRACK) = EQUAL
  | backtrack_mode_ord (ALLOW_BACKTRACK, _) = LESS
  | backtrack_mode_ord _ = GREATER

val mode_ord = prod_ord cut_mode_ord backtrack_mode_ord


datatype backtracking = NO_BACKTRACKING | BACKTRACKING | EXPLORATIVE_BACKTRACKING

val cut_mode_parser = (\<^keyword>\<open>!\<close> |-- \<^keyword>\<open>!\<close> >> K GLOBAL_CUT)
                   || (\<^keyword>\<open>!\<close> >> K LOCAL_CUT)
                   || (\<^keyword>\<open>?\<close> >> K NO_CUT)

val backtrack_mode_parser = (Args.$$$ "default" >> K NO_BACKTRACK)
                         || ((Args.$$$ "no" -- Args.$$$ "backtrack") >> K NO_BACKTRACK)
                         || ((Args.$$$ "no" -- Args.$$$ "explorative" -- Args.$$$ "backtrack") >> K NO_EXPLORATIVE_BACKTRACK)

fun default_mode_of priority =
      if priority >= 1000000 then GLOBAL_CUT
      else if priority >= 1000 then LOCAL_CUT
      else NO_CUT

end