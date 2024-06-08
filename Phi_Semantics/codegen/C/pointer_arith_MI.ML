structure C'G_PhiSem_Mem_C_Ar_MI = struct local open Phi_C'G C'G_PhiSem_Machine_Integer in
fun op_add_ptr_ b T (V2(p,i)) = T #-> (fn t =>
      var (pair (t@["*"])) (puts(["("]@t@["*)",dV p," + ("]@ iT b @[")",dV i,";\n"])))
fun op_add_ptr_unsigned_ b T (V2(p,i)) = T #-> (fn t =>
      var (pair (t@["*"])) (puts(["("]@t@["*)",dV p," + ("]@ uT b @[")",dV i,";\n"])))
end end