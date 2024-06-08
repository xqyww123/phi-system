signature PHI_C'G = sig
include PHI_CG
type T = ctxt -> string list * ctxt

val var : T -> (ctxt -> ctxt) -> ctxt -> V * ctxt
val unop : string -> T -> V -> ctxt -> V * ctxt
val binop : string -> T -> V -> ctxt -> V * ctxt
val trinop : string -> string -> T -> V -> ctxt -> V * ctxt

val codegen : string -> (ctxt -> ctxt) -> unit

val pV : V -> string list
val chkV0 : V * 'a -> 'a
val bk : string -> ty -> ty -> V -> ctxt -> V * ctxt

val ele : C'G_Phi_Element_Path.agidx list -> string list
val newvar : T -> ctxt -> string * ctxt
val defty : string -> T

end
