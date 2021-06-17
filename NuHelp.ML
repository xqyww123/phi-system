(*  Title:      NuHelp.ML
    Author:     Qiyuan Xu

Application-irrelevant basic tools.

*)

signature NU_HELP = sig
  type state = Proof.state

  exception NotFree of term
  exception Syntax of term

  val UI_top_handler (* process error presentation *) : Context.generic -> ('a -> 'b) -> 'a -> 'b
  val UI_top_handler_local : (Proof.context -> 'a) -> Proof.context -> 'a
  val UI_top_handler_global : (Context.theory -> 'a) -> Context.theory -> 'a

  val same_const : string (* const name *) -> term -> bool
  (* map all Free term to the Fixed term if the name is fixed.*)
  val free_to_fix : Proof.context -> term -> term

  val string_of_term_generic : Context.generic -> term -> string

  val dest_binop : string (* const name *) -> term -> term * term
  val strip_binop_r (* right associative *) : string (* const name *) -> term -> term list
  val mk_binop : string (* const name *) -> term * term -> term
  val list_mk_binop_r  (* right associative *) : string (* const name *) -> term list -> term
  val list_mk_binop_r0 (* right associative *) : string (* const name *)
        -> term (* initial term *) -> term list -> term

  val fix_frees : Position.T -> term list (* free terms *) -> state -> state
end
structure NuHelp : NU_HELP = struct
type state = Proof.state
exception NotFree of term
exception Syntax of term

fun string_of_term_generic (Context.Theory thy) = Syntax.string_of_term_global thy
  | string_of_term_generic (Context.Proof ctx) = Syntax.string_of_term ctx

fun error s = Exn.reraise (ERROR s)
fun UI_top_handler ctx f x =
  let
    val term = string_of_term_generic ctx
  in
    f x
  handle 
      NotFree tm => error ("Free varaible is expected, "^ (term tm))
    | Syntax tm => error ("Syntax error, " ^ (term tm))
  end

fun UI_top_handler_local  f c = UI_top_handler (Context.Proof  c) f c
fun UI_top_handler_global f c = UI_top_handler (Context.Theory c) f c

fun same_const c (Const (c', _)) = (c = c')
  | same_const _ _ = false;
fun dest_binop c (tm as Const (c', _) $ a $ b) = if c' = c then (a,b) else raise Syntax tm
  | dest_binop _ tm = raise Syntax tm
fun strip_binop_r c tm =
  case try (dest_binop c) tm of SOME (a,b) => a::(strip_binop_r c b) | _ => [tm]

fun mk_binop name (lhs,rhs) = Const (name, Term.dummyT) $ lhs $ rhs
fun list_mk_binop_r _  [] = raise Empty
  | list_mk_binop_r _  [x] = x
  | list_mk_binop_r mk (h::r) = mk_binop mk (h, list_mk_binop_r mk r)
fun list_mk_binop_r0 _  x0 [] = x0
  | list_mk_binop_r0 mk x0 (h::r) = mk_binop mk (h, list_mk_binop_r0 mk x0 r)

fun fix_frees pos = map (Term.dest_Free #> (fn (name,ty) =>
        (Binding.make (name, pos), (if ty = Term.dummyT then NONE else SOME ty), Mixfix.NoSyn)
      )) #> Proof.fix

fun free_to_fix_1 ctx (tm as Term.Free (name,ty)) =
      (case Variable.lookup_fixed ctx name of SOME name' => Term.Free (name', ty) | _ => tm)
  | free_to_fix_1 _ tm = tm
fun free_to_fix ctx = Term.map_aterms (free_to_fix_1 ctx)
end
