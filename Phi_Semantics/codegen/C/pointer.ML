structure C'G_PhiSem_Mem_Pointer = struct local open Phi_C'G in
val sem_pointer_T_ = pair ["void*"]; val P = sem_pointer_T_; val NULL_ : M = pair (V "NULL")
fun op_get_element_pointer_ T idx v = T #-> (fn t => var P (puts(["(void*)&((*("]@ t @["*)",dV v,")"] @ ele idx @ [");\n"])))
end end
