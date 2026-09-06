structure C'G_PhiSem_Generic_Boolean = struct local open Phi_C'G in

val sem_bool_T_ : T = pair ["bool"] ; val B = sem_bool_T_
fun op_const_bool_ b c = (V (if b then "true" else "false"), c);
val op_not_ = unop "!" B; val op_and_ = binop "&&" B; val op_or_ = binop "||" B;
val op_xor_ = binop "^"  B; fun op_equal_ _ = binop "==" B

end end
