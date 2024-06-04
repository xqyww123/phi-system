structure CG_PhiSem_Generic_Boolean = struct local open Phi_CG in

val b_o_o_l__ = ["bool"]
fun op_const_bool_ b c = (V (if b then "true" else "false"), c); val op_not_ = unop "!" ["bool"]
val op_and_ = binop "&&" ["bool"]; val op_or_ = binop "||" ["bool"];
val op_xor_ = binop "^"  ["bool"]; fun op_equal_ _ = binop "==" ["bool"]

end end
