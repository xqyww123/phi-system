structure C'G_PhSm_Ag_Base = struct local open Phi_C'G in

fun op_get_aggregate_ idx T U v = var U (puts (dV v :: ele idx @ [";\n"]))
fun op_set_aggregate_ _ _ idx (V2(a,b)) = puts'' ([dV a] @ ele idx @ ["=",dV b,";\n"])

val op_construct_aggregate_ = I

fun AgIdx_VN_ v = C'G_Phi_Element_Path.AgIdx_V_ (dV v)

end end