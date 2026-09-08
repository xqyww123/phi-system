signature PHI_CG = sig

datatype V = V of string | V2 of V * V | V0
datatype frame = Named of string | Anonymous
type ctxt = string list list * string option * exn Symtab.table * string list list * int * frame
type M = ctxt -> V * ctxt
type ty = M
type keyp = ctxt -> string option * ctxt
exception FUN of V -> M
exception KEY of string

val dV : V -> string
val lV : V list -> V

val serial : string -> string

val puts : string list -> ctxt -> ctxt
val put  : string -> ctxt -> ctxt
val puts': string list -> ctxt -> ctxt
val put' : string -> ctxt -> ctxt
val puts'': string list -> M
val put'' : string -> M
val get_frame : ctxt -> frame
val set_frame : frame -> ctxt -> ctxt
val fun_entry : string -> string
val key_entry : string -> string
val the_fun : exn Symtab.table -> string -> V -> M
val content_key : string -> string list -> string
val spell : string -> string
val key_int  : int -> keyp
val key_bool : bool -> keyp
val key_strs : (ctxt -> string list * ctxt) -> keyp
val mangle : string -> keyp list -> ctxt -> string option * ctxt
val frame  : (ctxt -> string option * ctxt) -> M -> M
val frame' : (ctxt -> string option * ctxt) -> (V -> M) -> V -> M
val new_fun : (string -> ctxt -> (V -> M) * ctxt) -> V -> M
val interf  : string -> (V -> M) -> ctxt -> ctxt
val assign_var : ctxt -> string * ctxt
val cat  : string list -> string
val catw : string -> string list -> string
val codegen' : string -> string -> (ctxt -> ctxt) -> unit

end
