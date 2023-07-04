signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_tags   :  term ->  term
  val dest_tags_c : cterm -> cterm

  val dest_procedure   : term -> term * term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm * cterm
  val proc_monad_conv : conv -> conv

  val dest_view_shift   : term  -> term * term * term
  val dest_view_shift_c : cterm -> cterm * cterm * cterm

  val dest_implication   : term  -> term * term * term
  val dest_implication_c : cterm -> cterm * cterm * cterm
  val implication_conv : conv -> conv -> conv -> conv

  val strip_separations : term -> term list
  val mk_separations : term list -> term

  val dest_sem_value_T: typ -> typ
  val mk_sem_value_T: typ -> typ

  val mk_phi_type_ty : typ (*abstract*) * typ (*concrete*) -> typ
  val mk_phi_type : term * term -> term
  val dest_phi_type_ty : typ -> typ (*abstract*) * typ (*concrete*)
  val dest_phi_type_ty_c : ctyp -> ctyp (*abstract*) * ctyp (*concrete*)  

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Thm Term HOLogic Phi_Help Phi_Syntax

val dest_action_tag   = dest_binop   \<^const_name>\<open>Action_Tag\<close> #> #1
val dest_action_tag_c = dest_binop_c \<^const_name>\<open>Action_Tag\<close> #> #1


fun dest_tags X = X
  |> perhaps (try dest_Trueprop)
  |> perhaps (try dest_action_tag)
fun dest_tags_c X = X
  |> perhaps (try dest_Trueprop_c)
  |> perhaps (try dest_action_tag_c)

val dest_procedure   =
     dest_tags
  #> dest_quadop @{const_name \<phi>Procedure}
val dest_procedure_c =
     dest_tags_c
  #> dest_quadop_c @{const_name \<phi>Procedure}

fun proc_monad_conv C =
  Phi_Conv.tag_conv (fn ctm =>
    case Thm.term_of ctm
      of (Const (\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _)
           => Conv.fun_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg_conv C))) ctm
       | _ => raise CTERM ("proc_monad_conv", [ctm])
     )

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

fun implication_conv C_s C_t C_p ctm = (
  dest_implication_c ctm;
  Phi_Conv.may_Trueprop_conv (
    Conv.combination_conv (Conv.combination_conv (Conv.combination_conv Conv.all_conv C_s) C_t) C_p) ctm
)

fun strip_separations (Const (@{const_name Subjection}, _) $ T) = strip_separations T
  | strip_separations (Const (@{const_name ExSet}, _) $ T) = strip_separations T
  | strip_separations (Abs (_, _, T)) = strip_separations T
  | strip_separations T = strip_binop_l @{const_name times} T

fun mk_separations [] = \<^term>\<open>Void\<close>
  | mk_separations L = foldr1 (fn (A,X) => @{const times(assn)} $ A $ X) L

val dest_sem_value_T = dest_monop_ty \<^type_name>\<open>\<phi>arg\<close>
fun mk_sem_value_T T = Type(\<^type_name>\<open>\<phi>arg\<close>, [T])

fun mk_phi_type (x,T) =
  let val \<^Type>\<open>fun \<open>a\<close> \<open>\<^Type>\<open>set \<open>b\<close>\<close>\<close>\<close> = Phi_Help.safe_fastype_of  T
   in \<^Const>\<open>\<phi>Type a b\<close> $ x $ T end

fun mk_phi_type_ty (tx, tm) = \<^Type>\<open>fun tx \<^Type>\<open>set tm\<close>\<close>

fun dest_phi_type_ty \<^Type>\<open>fun x \<^Type>\<open>set model\<close>\<close> = (x, model)
  | dest_phi_type_ty T = raise TYPE ("dest_phi_type_ty", [T], [])

fun dest_phi_type_ty_c T =
  (dest_phi_type_ty (Thm.typ_of T) ;
   (Thm.dest_ctyp0 T, dest_ctyp0 (dest_ctyp1 T)))


end
