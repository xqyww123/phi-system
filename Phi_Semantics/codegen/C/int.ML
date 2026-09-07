structure C'G_Numeral_Type = struct local open Phi_C'G in
val num0_T = 0; val num1_T = 1; fun bit0_T i = i+i; fun bit1_T i = i+i+1
end end

structure C'G_PhiSem_Machine_Integer = struct local open Phi_C'G in

(*A machine integer is stored as its bit pattern, whose canonical reading is unsigned; the
  storage type is therefore unsigned and the signed operations cast their operands.
  Width codes: ~1 = the C int width, ~2 = the address width, otherwise the bit width.*)
fun iT ~1 = ["int"]      | iT ~2 = ["intptr_t"]  | iT i = ["int",  string_of_int i, "_t"]
fun uT ~1 = ["unsigned"] | uT ~2 = ["uintptr_t"] | uT i = ["uint", string_of_int i, "_t"]
val int_t_T = ~1 ; val mk_int_T_ : int -> T = pair o uT ; val bT = K ["bool"]

fun sem_mk_int_ (_,i) = string_of_int i

fun bin opr m U i (V2(a,b)) = var (pair (U i))
      (puts'' (["("]@U i@[")(("]@ m i @[")",dV a," ",opr," ("]@ m i @[")",dV b,")"]) #> snd)

val op_add_ = bin "+"  uT uT; val op_sub_ = bin "-"  uT uT ; val op_umul_ = bin  "*"  uT uT
val op_udiv_ = bin "/" uT uT; val op_sdiv_ = bin "/" iT uT ; val op_umod_ = bin "%"  uT uT
val op_smod_ = bin "%" iT uT
(*the shift count has its own width, which C does not need*)
fun op_lshr_ b _ = bin ">>" uT uT b; fun op_lshl_ b _ = bin "<<" uT uT b
val op_ult_ = bin "<"  uT bT; val op_ule_  = bin "<=" uT bT; val op_slt_  = bin "<"  iT bT
val op_sle_ = bin "<=" iT bT;

end end
