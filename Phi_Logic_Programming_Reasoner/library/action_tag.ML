signature PHI_HELPER_CONV = sig
include PHI_HELPER_CONV

val action_tag_conv : conv -> conv
val may_action_tag_conv : conv -> conv

end

structure Phi_Helper_Conv : PHI_HELPER_CONV = struct
open Phi_Helper_Conv

fun action_tag_conv C ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ _ => Conv.arg_conv C ctm
     | _ => raise CTERM ("action_tag_conv", [ctm])

fun may_action_tag_conv C ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ _ => Conv.arg1_conv C ctm
     | _ => C ctm

end
