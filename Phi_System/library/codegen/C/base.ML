structure Phi_C'G : PHI_C'G = struct open Phi_CG local open C'G_Phi_Element_Path  in

type T = ctxt -> string list * ctxt ; exception TY of string

fun defty expr (c as (os,pf,tab,ss,vc)) = case Symtab.lookup tab expr of SOME (TY t) => ([t],c)
      | NONE => let val t = serial "T"
                 in ([t], (os,pf,Symtab.update_new (expr,TY t) tab, ["typedef ",expr," ",t,";\n\n"]::ss, vc)) end

fun var T F = T #-> (fn t => if t = ["void"] then F #> pair V0
      else puts' t #> assign_var #-> (fn v => puts [v, " = "] #> F #> pair (V v)))

fun newvar T = T #-> (fn t => puts' t #> assign_var #-> (fn v => puts [v, ";\n"] #> pair v))

fun unop opr ty a = var ty (puts'' [opr, dV a] #> snd)
fun binop opr ty (V2(a,b)) = var ty (puts'' [dV a," ",opr," ",dV b] #> snd)
fun trinop opr1 opr2 ty (V2(a,V2(b,c))) = var ty (puts'' [dV a," ",opr1," ",dV b," ",opr2," ",dV c] #> snd)

val codegen = codegen' "#include <stdbool.h>\n#include <stdint.h>\n#include <stdlib.h>\n\n"

fun pV (V s) = [s] | pV (V2(a,b)) = pV a @ [","] @ pV b
fun chkV0 (v,c) = if v = V0 then c else error "if-statement or while-statement cannot have return value"
fun bk s (_:ty) (_:ty) v = puts'' [s, " ", dV v] 

fun ele [] = [] | ele (AgIdx_N_ i::L) = "["::string_of_int i::"]"::ele L
  | ele (AgIdx_S_ s::L) = "."::Phi_CG_Emit.tr_str s::ele L
  | ele (AgIdx_V_ v::L) = "["::v::"]"::ele L

end end
