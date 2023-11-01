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
  let fun strip (pat,ex,inargs) (Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ X)
            = strip (pat,ex,inargs) X
        | strip (pat,ex,inargs) (Const(\<^const_name>\<open>With_Pattern\<close>, _) $ X $ P)
            = strip (P :: pat, ex, inargs) X
        | strip (pat,ex,inargs) (Const(\<^const_name>\<open>Except_Pattern\<close>, _) $ X $ P)
            = strip (pat, P :: ex, inargs) X
        | strip (pat,ex,inargs) (Const(\<^const_name>\<open>With_IN_Arg\<close>, _) $ X $ arg)
            = (case arg of Var (v,_) => strip (pat, ex, v::inargs) X
                  | tm => raise TERM ("An IN-argument must be a schematic variable", [tm]))
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
      fun elim ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ _ =>
                (Conv.rewr_conv @{thm' NO_SIMP'_def} then_conv elim) ctm
           | Const(\<^const_name>\<open>With_Pattern\<close>, _) $ _ $ _ =>
                (Conv.rewr_conv @{thm' With_Pattern_def} then_conv elim) ctm
           | Const(\<^const_name>\<open>Except_Pattern\<close>, _) $ _ $ _ =>
                (Conv.rewr_conv @{thm' Except_Pattern_def} then_conv elim) ctm
           | _ => Conv.all_conv ctm
   in (ret, Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) elim) thm)
  end

end