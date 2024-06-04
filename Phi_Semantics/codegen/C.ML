
structure Phi_CG = struct open Phi_CG; local open CG_Phi_Element_Path Phi_CG_Emit in
fun pV (V s) = [s] | pV (V2(a,b)) = pV a @ pV b
fun chkV0 (v,c) = if v = V0 then c else error "if-statement or while-statement cannot have return value"
fun bk s (_:ty) (_:ty) v = puts'' [s, dV v] 

fun ele [] = [] | ele (AgIdx_N_ i::L) = "["::string_of_int i::"]"::ele L
  | ele (AgIdx_S_ s::L) = tr_str s::"."::ele L | ele (AgIdx_V_ v::L) = "["::v::"]"::ele L

end end

structure CG_PhiSem_Aggregate_Base = struct local open Phi_CG in

fun op_get_aggregate_ idx ty v = var ty (puts (v :: ele idx))
fun op_set_aggregate_ _ _ idx (v1,v2) = puts'' ([v1] @ ele idx @ ["=",v2])

end end

structure CG_PhiSem_Mem_Pointer = struct local open Phi_CG in
fun op_get_element_pointer T idx v = var T (puts(["&(", dV v] @ ele idx @ [")"]))
end end

structure CG_PhiSem_Aggregate_Array = struct fun mk_array_T_ n T = T @ ["[",string_of_int n,"]"] end
structure CG_PhiSem_Aggregate_Named_Tuple =
  struct fun semty_ntup_ ts = ["struct {"] @ maps (fn (n,t) => t@[" ",n,";"]) ts @ ["}"] end

structure CG_PhiSem_Void = struct val v_o_i_d__ = ["void"] end

structure CG_PhiSem_CF_Routine = struct local open Phi_CG in

fun call name T v = var T (puts([name,"("] @ pV v @ [")"]))

fun op_rec_routine_ aG _ ta tb F = fun_name () (new_fun (fn N =>
  let fun chk1 [x] = x | chk1 [] = ["void"] | chk1 _ = error ("multi-return in "^N)
      val args = catw ", " (map_index (fn (i,t) => cat t ^" v"^ string_of_int i) ta)
      val call = call N (chk1 tb)
   in puts (chk1 tb @[" ",N,"(", args, ") {\n"]) #> aG #-> F call (bk "return") #> snd #> put "}\n" #> pair call end))

fun op_routine_ aG rG ta tb F = op_rec_routine_ aG rG ta tb (K F)

end end

structure CG_PhiSem_CF_Basic = struct local open Phi_CG in

val op_sel_ = trinop "?" ":"
fun op_if_ pT pF v = puts ["if (", dV v, ") {\n"] #> pT #> chkV0 #> put "} {\n" #> pF #> chkV0 #> put "}\n" #> pair V0
fun if_ pT pF v = puts ["if (", dV v, ") {\n"] #> pT #> chkV0 #> put "} {\n" #> pF #> chkV0 #> put "}\n" #> pair V0
fun op_do_while_ p = put "do {\n" #> p #-> (fn v => puts'' ["} while (", dV v, ")"])
fun while_ c b = c #-> (fn v => puts ["while (", dV v, ") {\n"]) #> b #> chkV0 #> put "}\n" #> pair V0

end end

signature CG_PHISEM_CF_BREAK = sig val op_break_ : Phi_CG.ty -> Phi_CG.ty -> (Phi_CG.ty -> Phi_CG.ty -> Phi_CG.V -> Phi_CG.ctxt -> Phi_CG.V * Phi_CG.ctxt) -> Phi_CG.V -> Phi_CG.ctxt -> Phi_CG.V * Phi_CG.ctxt end
structure CG_PhiSem_CF_Break : CG_PHISEM_CF_BREAK = struct fun op_break_ tr ta F v = F tr ta v end

structure CG_PhiSem_CF_Breakable = struct local open Phi_CG in

fun while_ c b = c #-> (fn v => puts ["while (", dV v, ") {\n"]) #> b (bk "break ") (bk "continue") #> chkV0 #> put "}\n" #> pair V0

end end

structure CG_PhiSem_Int_ArbiPrec = struct local open Phi_CG in

val a_i_n_t__ = ["int"]; val sem_mk_aint_ = string_of_int
val op_aadd_ = binop "+" ["int"]; val op_asub_ = binop "-" ["int"]; val op_aneg_ = unop "-" ["int"]
val op_amul_ = binop "*" ["int"]; val op_adiv_ = binop "/" ["int"]; val op_amod_ = unop "%" ["int"]
val op_alshr_ = binop ">>" ["int"]; val op_alshl_ = binop "<<" ["int"]; val op_a_lt_ = unop "<" ["bool"]
val op_a_gt_ = unop ">" ["bool"]; val op_a_le_ = unop "<=" ["bool"]; val op_a_ge_ = unop ">=" ["bool"]

end end

structure CG_PhiSem_Mem_C = struct local open Phi_CG in

val op_load_mem = unop "*"; fun op_store_mem T (V2(a,b)) = puts'' ["*", dV a, "=", dV b]
fun calloc1 T v = var T (puts(["calloc(1, size_of("] @T@ [dV v]))
fun mfree v = puts'' ["mfree(", dV v, ")"]

end end

structure CG_PhiSem_Variable = struct local open Phi_CG in
fun chkT (SOME T) = T | chkT NONE = error "you must turn on \<open>\<phi>variable_is_typed\<close>"
fun op_var_scope_ _ T F = puts' (chkT T) #> assign_var #-> (fn v => puts' [v, ";\n"] #> F v)
fun op_set_var_ _ va _ idx v = puts'' ([va]@ ele idx @["=", dV v])
fun op_get_var_ va T idx = var T (puts([va]@ ele idx))
end end


