signature PHI_CG = sig

datatype V = V of string | V2 of V * V | V0
type ctxt = string list list * string option * exn Symtab.table * string list list * int
type M = ctxt -> V * ctxt
type ty = M
exception FUN of V -> M

val dV : V -> string
val lV : V list -> V

val serial : string -> string

val puts : string list -> ctxt -> ctxt
val put  : string -> ctxt -> ctxt
val puts': string list -> ctxt -> ctxt
val put' : string -> ctxt -> ctxt
val puts'': string list -> M
val put'' : string -> M
val fun_name : unit -> (string -> V -> M) -> V -> M
val new_fun : (string -> ctxt -> (V -> M) * ctxt) -> string -> V -> M
val interf  : string -> (V -> M) -> ctxt -> ctxt
val assign_var : ctxt -> string * ctxt
val cat  : string list -> string
val catw : string -> string list -> string
val codegen' : string -> string -> (ctxt -> ctxt) -> unit

end
