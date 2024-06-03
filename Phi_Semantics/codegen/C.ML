structure CG_PhiSem_Aggregate_Base = struct local open Phi_CG CG_Phi_Element_Path Phi_CG_Emit in

fun ele [] = [] | ele (AgIdx_N i::L) = "["::string_of_int i::"]"::ele L
  | ele (AgIdx_S s::L) = tr_str s::"."::ele L | ele (AgIdx_V v::L) = "["::v::"]"::ele L
fun op_get_aggregate idx ty v = var ty (puts (v :: ele idx))
fun op_set_aggregate _ _ idx (v1,v2) = puts'' ([v1] @ ele idx @ ["=",v2])

end end

structure CG_PhiSem_Aggregate_Array = struct fun mk_array_T n T = T @ ["[",string_of_int n,"]"] end
structure CG_PhiSem_Aggregate_Named_Tuple =
  struct fun semty_ntup ts = ["struct {"] @ maps (fn (n,t) => t@[" ",n,";"]) ts @ ["}"] end

structure CG_PhiSem_Void = struct val v_o_i_d_ = ["void"] end

structure CG_PhiSem_CF_Routine = struct local open Phi_CG in

fun op_routine () = ()

end end