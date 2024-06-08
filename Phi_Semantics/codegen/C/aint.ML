structure C'G_PhiSem_Int_ArbiPrec = struct local open Phi_C'G in

val T = pair ["int"]; val a_i_n_t__ = T; val sem_mk_aint_ = string_of_int
val op_aadd_ = binop "+" T; val op_asub_ = binop "-" T; val op_aneg_ = unop "-" T
val op_amul_ = binop "*" T; val op_adiv_ = binop "/" T; val op_amod_ = binop "%" T
val op_alshr_= binop ">>" T; val op_alshl_ = binop "<<" T; val op_a_lt_ = binop "<" T
val op_a_gt_ = binop ">" T; val op_a_le_ = binop "<=" T; val op_a_ge_ = binop ">=" T

end end
