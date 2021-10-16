signature NU_PATH = sig
  datatype T = L | R | Reg | Stack
  val getter_thm : T -> thm
  val getter : T list -> thm
  val mapper_thm : T -> thm
  val mapper : T list -> thm
end
structure NuPath = struct

datatype T = L | R | Reg | Stack

fun getter_thm L = @{thm NuSys.index_left_getter}
  | getter_thm R = @{thm NuSys.index_right_getter}
  | getter_thm Reg = @{thm NuSys.index_reg_getter}
  | getter_thm Stack = @{thm NuSys.index_stack_getter}
fun getter adr =
      fold_rev (fn a => fn b => b RS a) (map getter_thm adr) @{thm NuSys.index_here_getter}

fun mapper_thm L = @{thm NuSys.index_left_mapper}
  | mapper_thm R = @{thm NuSys.index_right_mapper}
  | mapper_thm Reg = @{thm NuSys.index_reg_mapper}
  | mapper_thm Stack = @{thm NuSys.index_stack_mapper}
fun mapper adr =
      fold_rev (fn a => fn b => b RS a) (map mapper_thm adr) @{thm NuSys.index_here_mapper}

end
