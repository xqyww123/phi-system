signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_procedure   : term -> term * term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm * cterm
  val proc_monad_conv : conv -> conv

  val dest_view_shift   : term  -> term * term * term
  val dest_view_shift_c : cterm -> cterm * cterm * cterm

  val dest_sem_value_T: typ -> typ
  val mk_sem_value_T: typ -> typ

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Thm Term HOLogic Phi_Help Phi_Syntax

val dest_procedure   =
     PLPR_Syntax.dest_tags
  #> dest_quadop @{const_name \<phi>Procedure}
val dest_procedure_c =
     PLPR_Syntax.dest_tags_c
  #> dest_quadop_c @{const_name \<phi>Procedure}

fun proc_monad_conv C =
  Phi_Conv.tag_conv (fn ctm =>
    case Thm.term_of ctm
      of (Const (\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _)
           => Conv.fun_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg_conv C))) ctm
       | _ => raise CTERM ("proc_monad_conv", [ctm])
     )

val dest_view_shift    =
         PLPR_Syntax.dest_tags
      #> dest_triop @{const_name View_Shift}
val dest_view_shift_c  =
         PLPR_Syntax.dest_tags_c
      #> dest_triop_c @{const_name View_Shift}

val dest_sem_value_T = dest_monop_ty \<^type_name>\<open>\<phi>arg\<close>
fun mk_sem_value_T T = Type(\<^type_name>\<open>\<phi>arg\<close>, [T])

end

val mk_phi_type_ty = Phi_Syntax.mk_phi_type_ty
