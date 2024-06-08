structure C'G_PhiSem_Variable = struct local open Phi_C'G in
fun chkT (SOME T) = T | chkT NONE = error "you must turn on \<open>\<phi>variable_is_typed\<close>"
fun op_var_scope_ _ T F = newvar (chkT T) #-> F
(* fun op_var_scope_ _ T F = puts' (chkT T) #> assign_var #-> (fn v => puts [v, ";\n"] #> F v) *)
fun op_set_var_ _ va _ idx v = puts'' ([va]@ ele idx @[" = ", dV v])
fun op_get_var_ va _ idx T = if null idx then pair (V va) else var T (puts([va]@ ele idx) #> put ";\n")
end end
