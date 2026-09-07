structure Phi_C'G : PHI_C'G = struct open Phi_CG local open C'G_Phi_Element_Path  in

type T = ctxt -> string list * ctxt ; exception TY of string

(*a typedef, memoised by its key; the line printer receives the fresh type name*)
fun defty' key line (c as (os,pf,tab,ss,vc)) = case Symtab.lookup tab key of SOME (TY t) => ([t],c)
      | NONE => let val t = serial "T"
                 in ([t], (os,pf,Symtab.update_new (key,TY t) tab, line t::ss, vc)) end
fun defty expr = defty' expr (fn t => ["typedef ",expr," ",t,";\n\n"])
(*C spells an array type around the declared name, so an array type is always a typedef*)
fun defty_array elem dim = defty' (cat elem ^ "[" ^ dim ^ "]") (fn t => ["typedef "] @ elem @ [" ",t,"[",dim,"];\n\n"])

fun var T F = T #-> (fn t => if t = ["void"] then F #> pair V0
      else puts' t #> assign_var #-> (fn v => puts [v, " = "] #> F #> pair (V v)))

fun newvar T = T #-> (fn t => puts' t #> assign_var #-> (fn v => puts [v, ";\n"] #> pair v))

fun unop opr ty a = var ty (puts'' [opr, dV a] #> snd)
fun binop opr ty (V2(a,b)) = var ty (puts'' [dV a," ",opr," ",dV b] #> snd)
fun trinop opr1 opr2 ty (V2(a,V2(b,c))) = var ty (puts'' [dV a," ",opr1," ",dV b," ",opr2," ",dV c] #> snd)

val codegen = codegen' "#include <stdbool.h>\n#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n\n"

(*the argument list of a call; V0 is "no value" and contributes nothing*)
fun pV (V s) = [s] | pV V0 = []
  | pV (V2(a,b)) = (case (pV a, pV b) of ([], y) => y | (x, []) => x | (x, y) => x @ [","] @ y)
fun chkV0 (v,c) = if v = V0 then c else error "if-statement or while-statement cannot have return value"
fun bk s (_:ty) (_:ty) v = puts'' [s, " ", dV v] 

fun ele [] = [] | ele (AgIdx_N_ i::L) = "["::string_of_int i::"]"::ele L
  | ele (AgIdx_S_ s::L) = "."::Phi_CG_Emit.tr_str s::ele L
  | ele (AgIdx_V_ v::L) = "["::v::"]"::ele L

end end
