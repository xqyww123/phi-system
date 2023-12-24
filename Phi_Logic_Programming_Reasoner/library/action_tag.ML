signature PHI_CONV = sig
include PHI_CONV

val action_tag_conv : conv -> conv
val may_action_tag_conv : conv -> conv
val tag_conv : conv -> conv

val pure_imp_antecedents_conv : conv -> conv

end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

fun action_tag_conv C ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Action_Tag\<close> , _) $ _ $ _ => Conv.arg1_conv C ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (action_tag_conv C) ctm
     | _ => raise CTERM ("action_tag_conv", [ctm])

fun may_action_tag_conv C ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Action_Tag\<close> , _) $ _ $ _ => Conv.arg1_conv C ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (may_action_tag_conv C) ctm
     | _ => C ctm

fun tag_conv C ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (tag_conv C) ctm
     | Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ _ => Conv.arg1_conv (tag_conv C) ctm
     | Const(\<^const_name>\<open>Meta_Tag\<close>, _) $ _ $ _ => Conv.arg1_conv (tag_conv C) ctm
     | Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _ => Conv.arg_conv (tag_conv C) ctm
     | _ => C ctm

fun pure_imp_antecedents_conv C ctm =
  case Thm.term_of ctm of Const ("Pure.imp", _) $ _ $ _ => 
          Conv.implies_conv C (pure_imp_antecedents_conv C) ctm
     | _ => Conv.all_conv ctm

end
