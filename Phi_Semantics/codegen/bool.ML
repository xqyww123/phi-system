structure C'G_PhiSem_Generic_Boolean = struct local open Phi_C'G in

val b_o_o_l__ : T = pair ["bool"] ; val B = b_o_o_l__
fun op_const_bool_ b c = (V (if b then "true" else "false"), c);
val op_not_ = unop "!" B; val op_and_ = binop "&&" B; val op_or_ = binop "||" B;
val op_xor_ = binop "^"  B; fun op_equal_ _ = binop "==" B

end end
