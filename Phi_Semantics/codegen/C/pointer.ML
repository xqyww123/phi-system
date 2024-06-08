structure C'G_PhiSem_Mem_Pointer = struct local open Phi_C'G in
val p_o_i_n_t_e_r__ = pair ["void*"]; val P = p_o_i_n_t_e_r__; val NULL_ : M = pair (V "NULL")
fun op_get_element_pointer_ T idx v = T #-> (fn t => var P (puts(["(void*)&((*("]@ t @["*)",dV v,")"] @ ele idx @ [");\n"])) #> @{print})
end end
