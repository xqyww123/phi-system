structure C'G_PhiSem_CF_Basic = struct local open Phi_C'G in

val op_sel_ = trinop "?" ":"

fun setv (v::vs) (V2(a,b)) = puts[v," = ",dV a,";\n"] #> setv vs b
  | setv [v] a = puts[v," = ",dV a,";\n"]
  | setv [] V0 = I

fun op_if_ Ts pT pF v = fold_map newvar Ts #-> (fn vs =>
      puts ["if (",dV v,") {\n"] #> pT #-> setv vs #> put "} {\n" #> pF #-> setv vs #> put "}\n" #> pair(lV(map V vs)))

(* fun if_ pT pF v = puts ["if (", dV v, ") {\n"] #> pT #> chkV0 #> put "} {\n" #> pF #> chkV0 #> put "}\n" #> pair V0 *)

fun op_do_while_ p = put "do {\n" #> p #-> (fn v => puts'' ["} while (", dV v, ")"])
fun while_ c b = c #-> (fn v => puts ["while (", dV v, ") {\n"] #> b #> chkV0
        #> c #-> (fn u => puts [dV v," = ",dV u,";\n}\n"]) #> pair V0)

end end
