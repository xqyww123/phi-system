signature PHI_CG = sig

datatype V = V of string | V2 of V * V | V0
datatype ctxt = C of string list list * string option * (string list * (V -> ctxt -> V * ctxt)) Symtab.table * int
type ty = ctxt -> V * ctxt

val dV : V -> string
val puts : string list -> ctxt -> ctxt
val put  : string -> ctxt -> ctxt
val puts': string list -> ctxt -> ctxt
val put' : string -> ctxt -> ctxt
val puts'': string list -> ctxt -> V * ctxt
val put'' : string -> ctxt -> V * ctxt
val fun_name : unit -> (string -> V -> ctxt -> V * ctxt) -> V -> ctxt -> V * ctxt
val new_fun : (string -> ctxt -> (V -> ctxt -> V * ctxt) * ctxt) -> string -> V -> ctxt -> V * ctxt
val interf  : string -> (V -> ctxt -> V * ctxt) -> ctxt -> ctxt
val assign_var : ctxt -> string * ctxt
val var : string list -> (ctxt -> ctxt) -> ctxt -> V * ctxt
val unop : string -> string list -> V -> ctxt -> V * ctxt
val binop : string -> string list -> V -> ctxt -> V * ctxt
val trinop : string -> string -> string list -> V -> ctxt -> V * ctxt
val cat  : string list -> string
val catw : string -> string list -> string
val codegen : string -> (ctxt -> ctxt) -> unit

end

structure Phi_CG : PHI_CG = struct

datatype V = V of string | V2 of V * V | V0 ;
fun dV (V s) = s | dV V0 = "" | dV _ = error "dV"
datatype ctxt = C of string list list * string option * (string list * (V -> ctxt -> V * ctxt)) Symtab.table * int
            (*current buffer*)
            (*used to pass the names of functions to be defined*)
            (*function table*)
            (*variable counter*)
type ty = ctxt -> V * ctxt

val serial_c = Synchronized.var "Phi_CG" 1
fun serial pr = Synchronized.change_result serial_c (fn i => (pr ^ string_of_int i,i+1))
fun puts s (C(out::outs,pf,ftab,vc)) = C((s@out)::outs,pf,ftab,vc); fun put s = puts [s];
fun puts' s = puts s #> put " " ; fun put' s = put s #> put " "
fun puts'' s = puts s #> put ";\n" #> pair V0; fun put'' s = put s #> put ";\n" #> pair V0
fun fun_name () =
  let val id = Unsynchronized.ref NONE
   in fn F => fn v => case !id of SOME id' => F id' v
       | NONE => (fn (C(out,SOME pf,ftab,vc)) => (id := SOME pf; F pf v (C(out,NONE,ftab,vc)))
                   | (C(out,NONE,ftab,vc)) => (id := SOME (serial "f"); F (the (!id)) v (C(out,NONE,ftab,vc)))) end

fun new_fun F name v (c as C(outs,pf,ftab,vc)) =
  case Symtab.lookup ftab name of SOME (_, G) => G v c
     | NONE => F name (C([]::outs,pf,ftab,0))
        |> (fn (G,C(out::outs,pf,ftab,_)) => G v (C(outs,pf, Symtab.update (name, (out,G)) ftab,vc)))

fun interf name F (C([],NONE,ftab,0)) =
  case F V0 (C([[]],SOME name,ftab,0)) of (_,C(_,_,ftab',_)) => C([],NONE,ftab',0)

fun codegen path G =
  let val os = TextIO.openOut path; fun out s = TextIO.output (os, s)
      val C(_,_,ftab,_) = G(C([],NONE,Symtab.empty,0))
   in Symtab.fold (fn (_,(ss,_)) => fn () => List.app out ss) ftab () ; TextIO.closeOut os end

fun assign_var (C(out,pf,ftab,vc)) = ("v" ^ string_of_int vc, C(out,pf,ftab,vc+1))
fun var ["void"] F = F #> pair V0
  | var ty F = puts' ty #> assign_var #-> (fn v => puts' [v, "="] #> F #> pair (V v))

fun unop opr ty a = var ty (puts'' [opr, dV a] #> snd)
fun binop opr ty (V2(a,b)) = var ty (puts'' [dV a, opr, dV b] #> snd) | binop _ _ V0 = pair V0
fun trinop opr1 opr2 ty (V2(a,V2(b,c))) = var ty (puts'' [dV a, opr1, dV b, opr2, dV c] #> snd) | trinop _ _ _ V0 = pair V0

val cat = String.concat; val catw = String.concatWith

end