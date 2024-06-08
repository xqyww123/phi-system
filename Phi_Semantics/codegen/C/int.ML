structure C'G_Numeral_Type = struct local open Phi_C'G in
val num0_T = 0; val num1_T = 1; fun bit0_T i = i+i; fun bit1_T i = i+i+1
end end

structure C'G_PhiSem_Machine_Integer = struct local open Phi_C'G in

fun iT ~1 = ["int"]  | iT i = ["int",  string_of_int i, "_t"]
fun uT ~1 = ["uint"] | uT i = ["uint", string_of_int i, "_t"]
val i_n_t__T = ~1 ; val mk_int_T_ : int -> T = pair o iT ; val bT = K ["bool"]

fun sem_mk_int_ (_,i) = string_of_int i

fun bin opr m U i (V2(a,b)) = var (pair (U i))
      (puts'' (["("]@U i@[")(("]@ m i @[")",dV a," ",opr," ("]@ m i @[")",dV b,")"]) #> snd)

val op_add_ = bin "+"  iT iT; val op_sub_ = bin "-"  iT iT ; val op_mul_ = bin  "*"  iT iT
val op_udiv_ = bin "/" uT iT; val op_sdiv_ = bin "/" iT iT ; val op_umod_ = bin "%"  uT iT
val op_smod_ = bin "%" iT iT; val op_lshr_ = bin ">>" uT iT; val op_lshl_ = bin "<<" uT iT
val op_ult_ = bin "<"  uT bT; val op_ule_  = bin "<=" uT bT; val op_slt_  = bin "<"  iT bT
val op_sle_ = bin "<=" iT bT;

end end
