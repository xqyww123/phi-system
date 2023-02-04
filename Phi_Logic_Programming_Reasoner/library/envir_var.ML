signature PLPR_ENVIR_VAR = sig

val name_of : term -> string
val push : string -> cterm -> Proof.context -> Proof.context
val pop  : string -> Proof.context -> Proof.context
val get  : string -> Proof.context -> cterm option

end

structure PLPR_Envir_Var : PLPR_ENVIR_VAR = struct

structure Data = Proof_Data (
  type T = cterm list Symtab.table
  val init = K Symtab.empty
)

fun name_of (Const (N,_)) = N
  | name_of X = raise TERM ("envir_var_name has to be a constant", [X])

fun push N V = Data.map (Symtab.map_default (N,[]) (fn L => V::L))

fun pop N = Data.map (Symtab.map_entry N tl)

fun get N ctxt = Symtab.lookup (Data.get ctxt) N
              |> Option.mapPartial (fn [] => NONE | x::_ => SOME x)

end