structure Phi_CG : PHI_CG = struct

datatype V = V of string | V2 of V * V | V0 ;
fun dV (V s) = s | dV V0 = "" | dV _ = error "dV" ; fun lV[] = V0 | lV[v] = v | lV(a::b) = V2(a,lV b)


type ctxt = string list list * string option * exn Symtab.table * string list list  * int
            (*current buffer*)
            (*used to pass the names of functions to be defined*)
            (*elements table*)
            (*outputs*)
            (*variable counter*)
type M = ctxt -> V * ctxt; type ty = M

val serial_c = Synchronized.var "Phi_CG" 1
fun serial pr = Synchronized.change_result serial_c (fn i => (pr ^ string_of_int i,i+1))
fun puts s (out::outs,pf,ftab,ss,vc) = ((rev s@out)::outs,pf,ftab,ss,vc); fun put s = puts [s];
fun puts' s = puts s #> put " " ; fun put' s = put s #> put " "
fun puts'' s = puts s #> put ";\n" #> pair V0; fun put'' s = put s #> put ";\n" #> pair V0
fun fun_name () =
  let val id = Unsynchronized.ref NONE
   in fn F => fn v => case !id of SOME id' => F id' v
       | NONE => (fn (out,SOME pf,ftab,ss,vc) => (id := SOME pf; F pf v (out,NONE,ftab,ss,vc))
                   | (out,NONE,ftab,ss,vc) => (id := SOME(serial "f"); F (the (!id)) v (out,NONE,ftab,ss,vc))) end

exception FUN of V -> M 

fun new_fun F name v (c as (outs,pf,ftab,ss,vc) : ctxt) =
  case Symtab.lookup ftab name of SOME (FUN G) => G v c
     | NONE => F name ([]::outs,pf,ftab,ss,0)
        |> (fn (G,(out::outs,pf,ftab,ss,_)) => G v (outs,pf, Symtab.update (name,FUN G) ftab,rev out::ss,vc))

fun interf name F ([],NONE,ftab,ss,0) =
  case F V0 ([[]],SOME name,ftab,ss,0) of (_,(_,_,ftab',ss,_)) => ([],NONE,ftab',ss,0)

fun codegen' prelude path G =
  let val os = TextIO.openOut path; fun out s = TextIO.output (os, s)
      val (_,_,_,ss,_) = G([],NONE,Symtab.empty,[],0)
   in out prelude; List.app (List.app out) (rev ss); TextIO.flushOut os; TextIO.closeOut os end

fun assign_var (out,pf,ftab,ss,vc) = ("v" ^ string_of_int vc, (out,pf,ftab,ss,vc+1))

val cat = String.concat; val catw = String.concatWith

end
