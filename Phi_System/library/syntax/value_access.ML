signature VALUE_ACCESS_SYNTAX = sig

(* Value Context *)
val open_value_context : term list (*arguments*) -> Proof.context -> Proof.context
val assign_local_val : typ option -> Proof.context -> string * Proof.context

(* Parser *)
type value_parser_key =
  ( int (*priority, descend order, the higher one is attempted first*)
  * string (*name*))

type value_parser = (Proof.context -> term -> term option)

val add_parser : value_parser_key * value_parser -> Context.generic -> Context.generic
val translate_value : Proof.context -> term -> term

end

structure Value_Access_Syntax : VALUE_ACCESS_SYNTAX = struct

(*** Value Context ***)

type value_context =
        ( term list (*values of arguments, of type 'a sem_value*)
        * term Symtab.table (*binding table of local values,
                              key: internal name of the fixed variable*)
        * int (*a counter assigning identities to intermediate local values*))

structure Value_Ctxt = Proof_Data (
  type T = value_context option
  val init = K NONE
)

fun value_context_of ctxt =
  case Value_Ctxt.get ctxt
    of SOME c => c
     | _ => raise Fail "Value context has not been set. Not under a programming context."

fun open_value_context arguments =
  Value_Ctxt.map (fn SOME (_, LV, CNT) => SOME (arguments, LV, CNT)
                   | NONE => SOME (arguments, Symtab.empty, 0))

fun assign_local_val ty ctxt =
  let
    val (ARG, LV, CNT) = value_context_of ctxt
    val name = "\<v>" ^ string_of_int CNT
  in ctxt
    |> Value_Ctxt.put (SOME (ARG, LV, CNT + 1))
    |> Proof_Context.add_fixes [(Binding.name name, ty, NoSyn)]
    |> apfst hd
  end

(*** Parsers ***)

(* Data *)

type value_parser_key =
  ( int (*priority, descend order, the higher one is attempted first*)
  * string (*name*))

val value_parser_key_ord = prod_ord int_ord string_ord

type value_parser = (Proof.context -> term -> term option)

structure ParserTab = Table(type key = value_parser_key val ord = value_parser_key_ord)

structure Value_Parsers = Generic_Data (
  type T = value_parser ParserTab.table
  val empty = ParserTab.empty
  val merge = ParserTab.merge (K true)
)

fun add_parser parser = Value_Parsers.map (ParserTab.update_new parser)


(* Translation *)

fun index_val ctxt i =
  let
    val (A,_,_) = case Value_Ctxt.get ctxt
                      of SOME c => c
                       | _ => error ("Cannot access the " ^ string_of_int i ^ "th argument.\n\
                                     \Not under a programming context.")
  in
  if 1 <= i andalso i <= length A
  then List.nth (A, i-1)
  else error ("The programmign context only has " ^ string_of_int (length A) ^
              " arguments, but it attempts to access the " ^ string_of_int i ^ "th argument.")
  end


fun fallback_trans ctxt (V as Free (s, _)) =
      if can Value.parse_int s
      then index_val ctxt (Value.parse_int s)
      else (case Symtab.lookup (#2 (value_context_of ctxt)) s
              of SOME s' => s'
               | _ => error (Pretty.string_of (Pretty.block [
                     Pretty.str "Variable or local value named ",
                     Syntax.pretty_term ctxt V, Pretty.str "is not found."
                    ])))
  | fallback_trans _ X = X


fun translate_value ctxt X =
  let
    val tab = Value_Parsers.get (Context.Proof ctxt)
  in
    case ParserTab.fold_rev (fn (_, f) => (fn NONE => f ctxt X
                                            | some => some)) tab NONE
      of SOME ast => ast
       | _ => fallback_trans ctxt X
  end


local open Ast in

fun ident X = Appl[Constant \<^const_syntax>\<open>\<phi>identifier\<close>, X]

val _ = Theory.setup (Sign.parse_ast_translation ([
  (\<^syntax_const>\<open>_identifier_\<close>, (fn _ => fn [X] => ident X)),
  (\<^syntax_const>\<open>_identifier_1_\<close>, (fn _ => fn _ => Variable "1")),
  (\<^syntax_const>\<open>_identifier_num_\<close>, (fn _ => fn [X] => X)),
  (\<^syntax_const>\<open>_get_identifier_\<close>, (fn _ => fn [X] =>
      Appl[Constant \<^const_syntax>\<open>Value_of\<close>, Constant \<^const_syntax>\<open>Pure.dummy_pattern\<close>, ident X])),
  (\<^syntax_const>\<open>_set_identifier_\<close>, (fn _ => fn [V,Y] =>
      Appl[Constant \<^const_syntax>\<open>Set_Value\<close>, Y, ident V])),
  (\<^syntax_const>\<open>_identifier_id_\<close>, (fn _ => fn [X] => X)),
  (\<^syntax_const>\<open>_identifier_logic_\<close>, (fn _ => fn [X] => X))
]) #> Sign.parse_translation ([
  (\<^const_syntax>\<open>\<phi>identifier\<close>, (fn ctxt => fn [X] => translate_value ctxt X))
]))

end
  




end