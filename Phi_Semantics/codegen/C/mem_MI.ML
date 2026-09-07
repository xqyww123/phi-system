structure C'G_PhiSem_Mem_C_MI = struct local open Phi_C'G in
fun calloc_ T v = T #-> (fn t => var (pair ["void*"]) (puts(["calloc(", dV v, ", sizeof("] @t@ ["));\n"])))
end end
