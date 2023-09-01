signature PLPR_SYNTAX = sig
include PLPR_SYNTAX

val dest_With_Pattern : term -> term * term
val dest_Except_Pattern : term -> term * term
val elim_With_Pattern : thm -> term * thm
val elim_Except_Pattern : thm -> term * thm

val strip_embedded_patterns : term -> (term list * term (*except*) list * indexname list) * term
val elim_embedded_patterns : thm -> (term list * term (*except*) list * indexname list) * thm

end

structure PLPR_Syntax : PLPR_SYNTAX = struct
open PLPR_Syntax

fun dest_With_Pattern (Const(\<^const_name>\<open>With_Pattern\<close>, _) $ X $ Pat) = (Pat, X)
  | dest_With_Pattern X = raise TERM ("PLPR_Syntax.dest_With_Pattern",[X])

fun dest_Except_Pattern (Const(\<^const_name>\<open>Except_Pattern\<close>, _) $ X $ Pat) = (Pat, X)
  | dest_Except_Pattern X = raise TERM ("PLPR_Syntax.dest_With_Pattern",[X])

fun strip_embedded_patterns tm =
  let fun strip (pat,ex,inargs) (Const(\<^const_name>\<open>With_Pattern\<close>, _) $ X $ P)
            = strip (P :: pat, ex, inargs) X
        | strip (pat,ex,inargs) (Const(\<^const_name>\<open>Except_Pattern\<close>, _) $ X $ P)
            = strip (pat, P :: ex, inargs) X
        | strip (pat,ex,inargs) (tm as Const(\<^const_name>\<open>With_IN_Arg\<close>, _) $ _ $ _)
            = let val (args', X') = dest_with_IN_arg tm
               in strip (pat, ex, args' @ inargs) X'
              end
        | strip ret X = (ret, X)
   in strip ([],[],[]) tm
  end

fun elim_With_Pattern thm =
  let val (pat, _) = dest_With_Pattern (Thm.concl_of thm)
   in (pat, @{thm' With_Pattern_I} RS thm)
  end

fun elim_Except_Pattern thm =
  let val (pat, _) = dest_Except_Pattern (Thm.concl_of thm)
   in (pat, @{thm' Except_Pattern_I} RS thm)
  end

fun elim_embedded_patterns thm =
  let val (ret, _) = strip_embedded_patterns (Thm.concl_of thm)
      fun elim thm =
        case Thm.concl_of thm
          of Const(\<^const_name>\<open>With_Pattern\<close>, _) $ _ $ _ => elim (@{thm' With_Pattern_I} RS thm)
           | Const(\<^const_name>\<open>Except_Pattern\<close>, _) $ _ $ _ => elim (@{thm' Except_Pattern_I} RS thm)
           | Const(\<^const_name>\<open>With_IN_Arg\<close>, _) $ _ $ _ => elim (@{thm' With_IN_Arg_I} RS thm)
           | _ => thm
   in (ret, elim thm)
  end


end