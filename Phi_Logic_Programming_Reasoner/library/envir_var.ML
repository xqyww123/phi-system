signature PLPR_ENVIR_VAR = sig

val name_of : term -> string
val push : string -> term -> Context.generic -> Context.generic
val pop  : string -> Context.generic -> Context.generic
val get  : string -> Context.generic -> term option


type assign_effect = term -> Context.generic -> term * Context.generic
                     (*invoked when pushing an environment variable*)
type clean_effect  = term -> Context.generic -> Context.generic
                     (*invoked when popping an environment variable*)
type effect = assign_effect * clean_effect

val set_effect : string -> effect option -> Context.generic -> Context.generic


val boolean_flag : string -> bool -> Context.generic -> bool

end

structure PLPR_Env : PLPR_ENVIR_VAR = struct

type assign_effect = term -> Context.generic -> term * Context.generic
                     (*invoked when pushing an environment variable*)
type clean_effect  = term -> Context.generic -> Context.generic
                     (*invoked when popping an environment variable*)
type effect = assign_effect * clean_effect

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
  let val (L, effect) = the_default ([], NONE) (Symtab.lookup (Data.get ctxt) N)
      val (V', ctxt') = case effect of SOME (e, _) => e V ctxt | _ => (V, ctxt)
   in Data.map (Symtab.update (N, (V'::L, effect))) ctxt'
  end

fun pop N ctxt =
  let fun err () = error ("Fail to pop-out environment variable " ^ N ^ " which hasn't been assigned!" )
      val (V, L, effect) = case (Symtab.lookup (Data.get ctxt) N)
                             of SOME (V::L, e) => (V, L, e)
                              | _ => err ()
      val ctxt' = case effect of SOME (_, e) => e V ctxt | _ => ctxt
   in Data.map (Symtab.update (N, (L, effect))) ctxt'
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