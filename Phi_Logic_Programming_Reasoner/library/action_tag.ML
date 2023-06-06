signature PHI_HELPER_CONV = sig
include PHI_HELPER_CONV

val action_tag_conv : conv -> conv
val may_action_tag_conv : conv -> conv
val may_Trueprop_conv : conv -> conv
val tag_conv : conv -> conv

val pure_imp_antecedents_conv : conv -> conv

end

structure Phi_Helper_Conv : PHI_HELPER_CONV = struct
open Phi_Helper_Conv

fun action_tag_conv C ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Action_Tag\<close> , _) $ _ $ _ => Conv.arg_conv C ctm
     | _ => raise CTERM ("action_tag_conv", [ctm])

fun may_action_tag_conv C ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Action_Tag\<close> , _) $ _ $ _ => Conv.arg1_conv C ctm
     | _ => C ctm

fun may_Trueprop_conv cv ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv cv ct
  | _ => cv ct)

fun tag_conv cv = may_Trueprop_conv (may_action_tag_conv cv)

fun pure_imp_antecedents_conv C ctm =
  case Thm.term_of ctm of Const ("Pure.imp", _) $ _ $ _ => 
          Conv.implies_conv C (pure_imp_antecedents_conv C) ctm
     | _ => Conv.all_conv ctm

end
