structure CG_PhiSem_Generic_Boolean = struct local open Phi_CodeGen in

val b_o_o_l_ = ["bool"]
fun op_const_bool v = var ["bool"] (puts'' v)
fun op_not v = var ["bool"] (puts'' ["!", v])
fun op_and a b = var ["bool"] (puts'' [a, "&&", b])
fun op_or a b = var ["bool"] (puts'' [a, "||", b])
fun op_xor a b = var ["bool"] (puts'' [a, "^", b])
fun op_equal a b = var ["bool"] (puts'' [a, "==", b])

end end

structure CG_HOL = struct val True = ["True"]; val False = ["False"] end