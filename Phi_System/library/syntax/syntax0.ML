signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_tags   :  term ->  term
  val dest_tags_c : cterm -> cterm

  val dest_procedure   : term -> term * term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm * cterm

  val dest_view_shift   : term  -> term * term * term
  val dest_view_shift_c : cterm -> cterm * cterm * cterm

  val dest_implication   : term  -> term * term * term
  val dest_implication_c : cterm -> cterm * cterm * cterm
  
  val strip_separations : term -> term list
  val mk_separations : term list -> term

  val dest_sem_value_T: typ -> typ
  val mk_sem_value_T: typ -> typ

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Thm Term HOLogic Phi_Help Phi_Syntax

val dest_action_tag   = dest_binop   \<^const_name>\<open>Action_Tag\<close> #> #1
val dest_action_tag_c = dest_binop_c \<^const_name>\<open>Action_Tag\<close> #> #1


fun dest_tags X = X
  |> perhaps (try dest_action_tag)
  |> perhaps (try dest_Trueprop)
fun dest_tags_c X = X
  |> perhaps (try dest_action_tag_c)
  |> perhaps (try dest_Trueprop_c)

val dest_procedure   =
     dest_tags
  #> dest_quadop @{const_name \<phi>Procedure}
val dest_procedure_c =
     dest_tags_c
  #> dest_quadop_c @{const_name \<phi>Procedure}

val dest_view_shift    =
         dest_tags
      #> dest_triop @{const_name View_Shift}
val dest_view_shift_c  =
         dest_tags_c
      #> dest_triop_c @{const_name View_Shift}

val dest_implication   =
         dest_tags
      #> dest_triop @{const_name "Imply"}
val dest_implication_c =
         dest_tags_c
      #> dest_triop_c @{const_name "Imply"}

fun strip_separations (Const (@{const_name Subjection}, _) $ T) = strip_separations T
  | strip_separations (Const (@{const_name ExSet}, _) $ T) = strip_separations T
  | strip_separations (Abs (_, _, T)) = strip_separations T
  | strip_separations T = strip_binop_l @{const_name times} T

fun mk_separations [] = \<^term>\<open>Void\<close>
  | mk_separations L = foldr1 (fn (A,X) => @{const times(assn)} $ A $ X) L

val dest_sem_value_T = dest_monop_ty \<^type_name>\<open>\<phi>arg\<close>
fun mk_sem_value_T T = Type(\<^type_name>\<open>\<phi>arg\<close>, [T])


end