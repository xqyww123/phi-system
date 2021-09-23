signature NU_PATH = sig
  datatype T = L | R
  val getter_thm : T -> thm
  val getter : T list -> thm
  val mapper_thm : T -> thm
  val mapper : T list -> thm
end
structure NuPath = struct

datatype T = L | R

fun getter_thm L = @{thm NuPrim.address_left_getter}
  | getter_thm R = @{thm NuPrim.address_right_getter}
fun getter adr =
      fold_rev (fn a => fn b => b RS a) (map getter_thm adr) @{thm NuPrim.address_here_getter}

fun mapper_thm L = @{thm NuPrim.address_left_mapper}
  | mapper_thm R = @{thm NuPrim.address_right_mapper}
fun mapper adr =
      fold (fn a => fn b => b RS a) (map mapper_thm adr) @{thm NuPrim.address_here_mapper}

end
