signature PLPR_ENVIR_VAR = sig

val name_of : term -> string
val push : string -> term -> Context.generic -> Context.generic
val pop  : string -> Context.generic -> Context.generic
val get  : string -> Context.generic -> term option

type effect = term -> Context.generic -> Context.generic
val set_effect : string -> effect option -> Context.generic -> Context.generic

val boolean_flag : string -> bool -> Context.generic -> bool

end

structure PLPR_Env : PLPR_ENVIR_VAR = struct

type effect = term -> Context.generic -> Context.generic

structure Data = Generic_Data (
  type T = (term list * effect option) Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (fn _ => fn ((L1,e1),(L2,e2)) =>
                ((case (L1,L2) of ([], L2) => L2 | (L1,[]) => L1 | (L1,_) => L1),
                 merge_options (e1,e2)))
)

fun name_of (Const (N,_)) = N
  | name_of X = raise TERM ("envir_var_name has to be a constant", [X])

fun push N V ctxt =
  let val effect = Unsynchronized.ref NONE
   in ctxt
   |> Data.map (Symtab.map_default (N, ([], NONE))
               (fn (L, e) => (effect := e; (V::L, e))))
   |> is_some (!effect) ? the (!effect) V
  end

fun pop N ctxt =
  let val effect = Unsynchronized.ref NONE
   in ctxt
   |> Data.map (Symtab.map_entry N
               (fn (L, e) => (case tl L of v :: _ => effect := Option.map (fn f => f v) e
                                         | _ => () ;
                              (tl L, e))))
   |> is_some (!effect) ? the (!effect)
  end

fun set_effect N e = Data.map (Symtab.map_default (N, ([], NONE)) (fn (L, _) => (L, e)))

fun get N ctxt = Symtab.lookup (Data.get ctxt) N
              |> Option.mapPartial (fn ([], _) => NONE | (x::_, _) => SOME x)

fun boolean_flag N default ctxt =
  let fun parse (Const (\<^const_name>\<open>True\<close>, _)) = true
        | parse (Const (\<^const_name>\<open>Trueprop\<close>, _) $ X) = parse X
        | parse (Const (\<^const_name>\<open>False\<close>, _)) = false
        | parse X = Phi_Reasoner.error (Pretty.string_of (Pretty.chunks [
              Pretty.block [Pretty.str "Environement variable ", Pretty.str N,
                            Pretty.str " is not a literal boolean:"],
              Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt X
            ]))
   in case get N ctxt
        of NONE => default
         | SOME X => parse X
  end
end