structure C'G_PhiSem_Mem_C_AI = struct local open Phi_C'G in
fun calloc_aN_ T v = T #-> (fn t => var (pair ["void*"]) (puts(["calloc(", dV v, ", sizeof("] @t@ ["));\n"])))
fun calloc_aN2_ T (V2(n,m)) = T #-> (fn t => var (pair ["void*"]) (puts(["calloc(", dV n, " * ", dV m, ", sizeof("] @t@ ["));\n"])))
end end
