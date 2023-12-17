signature PHI_SYNTAX = sig
include PHI_SYNTAX

val wrap_equation_by_MAKE : thm -> thm
val wrap_equation_by_OPEN : thm -> thm

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

fun wrap_equation_by_MAKE thm =
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) (Phi_Conv.LHS_conv (
    fn ctm => case Thm.term_of ctm
                of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const(\<^const_name>\<open>MAKE\<close>, _) $ _ $ _) => Conv.all_conv ctm
                 | Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ =>
                      Conv.arg_conv (Conv.rewr_conv @{thm' MAKE_def[symmetric]}) ctm
                 | Const(\<^const_name>\<open>MAKE\<close>, _) $ _ $ _ => Conv.all_conv ctm
                 | _ => if can Phi_Syntax.dest_phi_type_ty (Thm.typ_of_cterm ctm)
                        then Conv.rewr_conv @{thm' MAKE_def[symmetric]} ctm
                        else raise CTERM ("Not an equation about \<phi>-Type", [ctm])
    ))) thm

fun wrap_equation_by_OPEN thm =
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of thm) (Phi_Conv.LHS_conv (
    fn ctm => case Thm.term_of ctm
                of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const(\<^const_name>\<open>OPEN\<close>, _) $ _ $ _) => Conv.all_conv ctm
                 | Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ =>
                      Conv.arg_conv (Conv.rewr_conv @{thm' OPEN_def[symmetric]}) ctm
                 | Const(\<^const_name>\<open>OPEN\<close>, _) $ _ $ _ => Conv.all_conv ctm
                 | _ => if can Phi_Syntax.dest_phi_type_ty (Thm.typ_of_cterm ctm)
                        then Conv.rewr_conv @{thm' OPEN_def[symmetric]} ctm
                        else raise CTERM ("Not an equation about \<phi>-Type", [ctm])
    ))) thm

end