structure C'G_PhiSem_Mem_C_Ag_Ar = struct local open Phi_C'G in
fun op_get_element_pointer_arr_ T idx v = T #-> (fn t =>
      var C'G_PhiSem_Mem_Pointer.sem_pointer_T_ (puts(["(void*)&((("]@ t @["*)",dV v,")"] @ ele idx @ [");\n"])))
end end
