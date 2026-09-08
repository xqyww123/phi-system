structure C'G_PhiSem_Int_ArbiPrec = struct local open Phi_C'G in

val T = pair ["int"]; val sem_aint_T_ = T; val sem_mk_aint_ = string_of_int
val op_aadd_ = binop "+" T; val op_asub_ = binop "-" T; val op_aneg_ = unop "-" T
val op_amul_ = binop "*" T
(*C's / and % truncate toward zero, which is op_asdiv and op_asmod; the floor division
  op_adiv and op_amod has no hook, so a procedure using it cannot be emitted*)
val op_asdiv_ = binop "/" T; val op_asmod_ = binop "%" T

val op_alshr_= binop ">>" T; val op_alshl_ = binop "<<" T
val op_a_lt_ = binop "<"  C'G_PhiSem_Generic_Boolean.B; val op_a_gt_ = binop ">"  C'G_PhiSem_Generic_Boolean.B
val op_a_le_ = binop "<=" C'G_PhiSem_Generic_Boolean.B; val op_a_ge_ = binop ">=" C'G_PhiSem_Generic_Boolean.B

end end
