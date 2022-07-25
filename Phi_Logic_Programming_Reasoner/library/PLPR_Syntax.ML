signature PLPR_SYNTAX = sig
val dest_premise_tag : term -> term * term
val dest_premise_tag_c : cterm -> cterm * cterm
end

structure PLPR_Syntax = struct

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

val dest_premise_tag  = dest_binop   @{const_name "Premise"} o perhaps (try HOLogic.dest_Trueprop)
val dest_premise_tag_c= dest_binop_c @{const_name "Premise"} o perhaps (try dest_Trueprop_c)

end