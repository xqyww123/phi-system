structure C'G_PhiSem_Mem_Pointer = struct local open Phi_C'G in
val sem_pointer_T_ = pair ["void*"]; val P = sem_pointer_T_
(*the only raw-address literal a program can spell is the null pointer; the procedure NULL
  is unfolded to this literal by procedure_simps (PhiSem_Mem_Pointer.thy)*)
fun sem_mk_pointer_ 0 = "NULL"
  | sem_mk_pointer_ raw = error ("Cannot emit the raw address literal " ^ string_of_int raw ^ "; only the null pointer 0 is representable in C")
val size_t_T = ~2; val addrspace_bits_ = ~2  (*width code understood by C'G_PhiSem_Machine_Integer.iT/uT*)
fun op_get_element_pointer_ T idx v = T #-> (fn t => var P (puts(["(void*)&((*("]@ t @["*)",dV v,")"] @ ele idx @ [");\n"])))
end end
