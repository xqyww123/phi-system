structure CG_PhiSem_Generic_Boolean = struct local open Phi_CG in

val b_o_o_l_ = ["bool"]
val op_const_bool = unop "" ["bool"]; val op_not = unop "!" ["bool"]
val op_and = binop "&&" ["bool"]; val op_or = binop "||" ["bool"];
val op_xor = binop "^"  ["bool"]; val op_equal = binop "==" ["bool"];

end end
