structure NuCG_NuPrime = struct open NuCG

fun instr_comp_gen f g x = g (f x);  val nop_gen = I

val llty_int = T_int; val llty_pointer = T_ptr; val llty_tup = T_tup; val llty_array = T_array
val llty_nil = T_nil; fun llty_fusion t1 t2 = <*> (t1,t2)

end
