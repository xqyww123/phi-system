signature PLPR_ENVIR_VAR = sig

val name_of : term -> string
val push : string -> cterm -> Proof.context -> Proof.context
val pop  : string -> Proof.context -> Proof.context
val get  : string -> Proof.context -> cterm option

val boolean_flag : string -> bool -> Proof.context -> bool

end

structure PLPR_Env : PLPR_ENVIR_VAR = struct

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

fun boolean_flag N default ctxt =
  let fun parse (Const (\<^const_name>\<open>True\<close>, _)) = true
        | parse (Const (\<^const_name>\<open>Trueprop\<close>, _) $ X) = parse X
        | parse (Const (\<^const_name>\<open>False\<close>, _)) = false
        | parse X = Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
              Pretty.block [Pretty.str "Environement variable ", Pretty.str N,
                            Pretty.str " is not a literal boolean:"],
              Syntax.pretty_term ctxt X
            ]))
   in case get N ctxt
        of NONE => default
         | SOME X => parse (Thm.term_of X)
  end
end