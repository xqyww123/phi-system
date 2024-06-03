signature PHI_CG = sig

type ctxt = string list list * string option * string list Symtab.table * int
datatype V = V of string | V2 of V * V
val dV : V -> string

val puts : string list -> ctxt -> ctxt
val put  : string -> ctxt -> ctxt
val puts': string list -> ctxt -> ctxt
val put' : string -> ctxt -> ctxt
val puts'': string list -> ctxt -> ctxt
val put'' : string -> ctxt -> ctxt
val fun_name : unit -> (string -> ctxt -> ctxt) -> ctxt -> ctxt
val new_fun : (string -> ctxt -> ctxt) -> string -> ctxt -> ctxt
val assign_var : ctxt -> string * ctxt
val var : string list -> (ctxt -> ctxt) -> ctxt -> V * ctxt
val unop : string -> string list -> V -> ctxt -> V * ctxt
val binop : string -> string list -> V -> V -> ctxt -> V * ctxt
val cat  : string list -> string
val catw : string -> string list -> string

end

structure Phi_CG : PHI_CG = struct

type ctxt = string list list * string option * string list Symtab.table * int
            (*current buffer*)
            (*used to pass the names of functions to be defined*)
            (*function table*)
            (*variable counter*)
datatype V = V of string | V2 of V * V
fun dV (V s) = s | dV _ = error "dV"

val serial_c = Synchronized.var "Phi_CG" 1
fun serial pr = Synchronized.change_result serial_c (fn i => (pr ^ string_of_int i,i+1))
fun puts s (out::outs,pf,ftab,vc) = ((s@out)::outs,pf,ftab,vc); fun put s = puts [s]
fun puts' s = puts s #> put " " ; fun put' s = put s #> put " "
fun puts'' s = puts s #> put ";\n"; fun put'' s = put s #> put ";\n";
fun fun_name () =
  let val id = Unsynchronized.ref NONE
   in fn F => case !id of SOME id' => F id'
       | NONE => (fn (out,SOME pf,ftab,vc) => (id := SOME pf; F pf (out,NONE,ftab,vc))
                   | (out,NONE,ftab,vc) => (id := SOME (serial "f"); F (the (!id)) (out,NONE,ftab,vc))) end

fun new_fun F name (outs,pf,ftab,vc) = F name ([]::outs,pf,ftab,0)
        |> (fn (out::outs,pf,ftab,_) => (outs,pf, Symtab.update (name, out) ftab,vc))

fun assign_var (out,pf,ftab,vc) = ("v" ^ string_of_int vc, (out,pf,ftab,vc+1))
fun var ty F = puts' ty #> assign_var #-> (fn v => puts' [v, "="] #> F #> pair (V v))
fun unop opr ty a = var ty (puts'' [opr, dV a]);  fun binop opr ty a b = var ty (puts'' [dV a, opr, dV b])

val cat = String.concat; val catw = String.concatWith

end