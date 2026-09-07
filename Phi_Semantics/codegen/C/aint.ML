structure C'G_PhiSem_Int_ArbiPrec = struct local open Phi_C'G in

val T = pair ["int"]; val sem_aint_T_ = T; val sem_mk_aint_ = string_of_int
val op_aadd_ = binop "+" T; val op_asub_ = binop "-" T; val op_aneg_ = unop "-" T
val op_amul_ = binop "*" T

(*C's / and % truncate toward zero; op_adiv and op_amod are HOL's div and mod, which round
  toward negative infinity, so the quotient is lowered by one and the remainder raised by the
  divisor whenever the division is inexact and the operands differ in sign.  op_asdiv and
  op_asmod are the truncating division itself.*)
fun inexact_sign_differs a b = ["((", a, " % ", b, " != 0) && ((", a, " < 0) != (", b, " < 0)))"]
fun op_adiv_ (V2(a,b)) = var T (puts'' ([dV a, " / ", dV b, " - "] @ inexact_sign_differs (dV a) (dV b)) #> snd)
fun op_amod_ (V2(a,b)) = var T (puts'' ([dV a, " % ", dV b, " + ("] @ inexact_sign_differs (dV a) (dV b) @ [" ? ", dV b, " : 0)"]) #> snd)
val op_asdiv_ = binop "/" T; val op_asmod_ = binop "%" T

val op_alshr_= binop ">>" T; val op_alshl_ = binop "<<" T; val op_a_lt_ = binop "<" T
val op_a_gt_ = binop ">" T; val op_a_le_ = binop "<=" T; val op_a_ge_ = binop ">=" T

end end
