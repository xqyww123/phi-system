signature PLPR_SYNTAX = sig
include PLPR_SYNTAX

val is_deferable : term -> bool

val non_deferable_subgoals  : term -> int
val non_deferable_subgoals' : thm  -> int

end

structure PLPR_Syntax : PLPR_SYNTAX = struct
open PLPR_Syntax

fun is_deferable (Const (\<^const_name>\<open>ParamTag\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Argument\<close>, _) $ _) = true
  | is_deferable (Const (\<^const_name>\<open>Do\<close>, _) $ _) = true
  | is_deferable (\<^const>\<open>Trueprop\<close> $ X) = is_deferable X
  | is_deferable (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_,_,X)) = is_deferable X
  | is_deferable (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_deferable X
  (*| is_deferable (Const (\<^const_name>\<open>Premise\<close>, _) $ _) = true *)
  | is_deferable _ = false

val non_deferable_subgoals =
  let fun calc ret (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ C) =
            calc (if is_deferable G then ret else ret+1) C
        | calc ret _ = ret
   in calc 0
  end

fun non_deferable_subgoals' st = non_deferable_subgoals (Thm.prop_of st)

end