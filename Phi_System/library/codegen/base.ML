structure Phi_CG = struct

type ctxt = string list * string option * string list Symtab.table * int
            (*current buffer*)
            (*used to pass the names of functions to be defined*)
            (*function table*)
            (*variable counter*)

val serial_c = Synchronized.var "Phi_CG" 1
fun serial pr = Synchronized.change_result serial_c (fn i => (pr ^ string_of_int i,i+1))
fun puts s (out,pf,ftab,vc) = (s@out,pf,ftab,vc); fun put s = puts [s]
fun puts' s = puts s #> put " " ; fun put' s = put s #> put " "
fun puts'' s = puts s #> put ";\n"; fun put'' s = put s #> put ";\n";
fun fun_name () =
  let val id = Unsynchronized.ref NONE
   in fn F => case !id of SOME id' => F id'
       | NONE => (fn (out,SOME pf,ftab,vc) => (id := SOME pf; F pf (out,NONE,ftab,vc))
                   | (out,NONE,ftab,vc) => (id := SOME (serial "f"); F (the (!id)) (out,NONE,ftab,vc))) end

fun assign_var (out,pf,ftab,vc) = ("v" ^ string_of_int vc, (out,pf,ftab,vc+1))
fun var ty F = puts' ty #> assign_var #-> (fn v => puts' [v, "="] #> F #> pair v)
fun unop opr ty a = var ty (puts'' [opr, a]);  fun binop opr ty a b = var ty (puts'' [a, opr, b])

end