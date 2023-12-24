signature PLPR_SYNTAX = sig
include PLPR_SYNTAX

val dest_premise_tag : term -> term * term
val dest_premise_tag_opt : term -> (term * term) option
val dest_premise_tag_c : cterm -> cterm * cterm
val add_premise_tag_conv : cterm (*mode*) -> conv
val premise_tag_conv : (term -> bool) -> conv -> conv

val provide_premise_condition : thm -> thm -> thm

val dest_Trueprop_c : cterm -> cterm

end

structure PLPR_Syntax : PLPR_SYNTAX = struct
open PLPR_Syntax

fun has_head c (Const (c', _)) = (c = c')
  | has_head c (h $ _) = has_head c h
  | has_head _ _ = false

fun dest_monop const (tm as h $ a) =
      if has_head const h then a else raise TERM ("dest_monop "^const, [tm])
  | dest_monop const tm = raise TERM ("dest_monop "^const, [tm])
fun dest_monop_c const tm =
      (dest_monop const (Thm.term_of tm); Thm.dest_arg tm)

fun dest_binop const (tm as h $ a $ b) =
      if has_head const h then (a,b) else raise TERM ("dest_binop "^const, [tm])
  | dest_binop const tm = raise TERM ("dest_binop "^const, [tm])
fun dest_binop_c const tm =
      (dest_binop const (Thm.term_of tm); Thm.dest_binop tm)

val dest_Trueprop_c = dest_monop_c "HOL.Trueprop"

fun dest_premise_tag_opt (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest_premise_tag_opt X
  | dest_premise_tag_opt (Const(\<^const_name>\<open>Premise\<close>, _) $ tag $ X) = SOME (tag, X)
  | dest_premise_tag_opt _ = NONE
fun dest_premise_tag tm =
  case dest_premise_tag_opt tm of SOME ret => ret
     | NONE => raise TERM ("dest_premise_tag", [tm])
val dest_premise_tag_c= dest_binop_c @{const_name "Premise"} o perhaps (try dest_Trueprop_c)



fun add_premise_tag_conv mode =
  let val rule = Thm.instantiate (TVars.empty, Vars.make [((("mode",0),\<^typ>\<open>mode\<close>),mode)])
                    @{thm Premise_def[folded atomize_eq,symmetric]}
   in Conv.rewr_conv rule
  end

fun premise_tag_conv P C =
  Phi_Conv.tag_conv (fn ctm =>
    case Thm.term_of ctm
      of Const(\<^const_name>\<open>Premise\<close>, _) $ mode $ _ =>
              if P mode then Conv.arg_conv C ctm else raise CTERM ("premise_tag_conv",[ctm])
       | _ => raise CTERM ("premise_tag_conv",[ctm]))

fun provide_premise_condition C th =
  case Thm.prop_of C
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Premise\<close>, _) $ _ $ _) =>
        C RS (@{thm' provide_premise_condition_p} RS th)
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
        C RS (@{thm' provide_premise_condition} RS th)
     | _ => raise THM ("provide_premise_condition", 0, [C])

end