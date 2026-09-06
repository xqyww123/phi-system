structure C'G_PhiSem_Mem_C = struct local open Phi_C'G in

fun op_load_mem_ T v = T #-> (fn t => unop ("*(" ^ cat t ^ "*)") (pair t) v)
fun op_store_mem_ T (V2(a,b)) = T #-> (fn t => puts'' (["*("]@t@["*)", dV a, "=", dV b]))
fun calloc1_ T = T #-> (fn t => var (pair ["void*"]) (puts(["calloc(1, sizeof("] @t@ ["));\n"])))
fun mfree_ v = puts'' ["free(", dV v, ")"]

end end