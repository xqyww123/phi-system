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
  (* map all free terms and free types inside to variables *)
  val free_to_var_ty : typ -> typ
  val free_to_var : term -> term
  (* map all Free term to the Fixed term if the name is fixed.*)
  val free_to_fix : Proof.context -> term -> term

  val string_of_term_generic : Context.generic -> term -> string

  val dest_monop   : string (* const name *) -> term -> term
  val dest_monop_c : string (* const name *) -> cterm -> cterm
  val dest_binop   : string (* const name *) -> term -> term * term
  val dest_binop_c : string (* const name *) -> cterm -> cterm * cterm
  val dest_triop   : string (* const name *) -> term -> term * term * term
  val dest_triop_c : string (* const name *) -> cterm -> cterm * cterm * cterm
  val dest_quadop   : string (* const name *) -> term -> term * term * term * term
  val dest_quadop_c : string (* const name *) -> cterm -> cterm * cterm * cterm * cterm
  val strip_binop_r (* right associative *) : string (* const name *) -> term -> term list
  val mk_binop : string (* const name *) -> term * term -> term
  val list_mk_binop_r  (* right associative *) : string (* const name *) -> term list -> term
  val list_mk_binop_r0 (* right associative *) : string (* const name *)
        -> term (* initial term *) -> term list -> term

  val dest_Trueprop_c : cterm -> cterm
  (*  Γ |- A ==> B
  * ---------------
  *   Γ, A |- B *)
  val undisch : thm -> thm

  val fix_frees : Position.T -> term list (* free terms *) -> state -> state
end
structure NuHelp : NU_HELP = struct
open Term Thm

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
fun dest_monop const (tm as Const (const', _) $ a) =
      if const' = const then a else raise TERM ("dest_monop "^const, [tm])
  | dest_monop const tm = raise TERM ("dest_monop "^const, [tm])
fun dest_monop_c const tm =
      (dest_monop const (term_of tm); Thm.dest_arg tm)
fun dest_binop const (tm as Const (const', _) $ a $ b) =
      if const' = const then (a,b) else raise TERM ("dest_binop "^const, [tm])
  | dest_binop const tm = raise TERM ("dest_binop "^const, [tm])
fun dest_binop_c const tm =
      (dest_binop const (term_of tm); Thm.dest_binop tm)
fun strip_binop_r c tm =
  case try (dest_binop c) tm of SOME (a,b) => a::(strip_binop_r c b) | _ => [tm]
fun dest_triop const (tm as Const (const', _) $ a $ b $ c) =
      if const' = const then (a,b,c) else raise TERM ("dest_triop "^const, [tm] )
  | dest_triop const tm = raise TERM ("dest_triop "^const, [tm])
fun dest_triop_c const tm =
      let
        val _ = dest_triop const (term_of tm)
        val (f,a3) = Thm.dest_comb tm
        val (f,a2) = Thm.dest_comb f
        val (f,a1) = Thm.dest_comb f
      in (a1,a2,a3) end
fun dest_quadop const (tm as Const (const', _) $ a $ b $ c $ d) =
      if const' = const then (a,b,c,d) else raise TERM ("dest_quadop "^const, [tm] )
  | dest_quadop const tm = raise TERM ("dest_quadop "^const, [tm])
fun dest_quadop_c const tm =
      let
        val _ = dest_quadop const (term_of tm)
        val (f,a4) = Thm.dest_comb tm
        val (f,a3) = Thm.dest_comb f
        val (f,a2) = Thm.dest_comb f
        val (f,a1) = Thm.dest_comb f
      in (a1,a2,a3,a4) end
val dest_Trueprop_c = dest_monop_c "HOL.Trueprop"

fun mk_binop name (lhs,rhs) = Const (name, Term.dummyT) $ lhs $ rhs
fun list_mk_binop_r _  [] = raise Empty
  | list_mk_binop_r _  [x] = x
  | list_mk_binop_r mk (h::r) = mk_binop mk (h, list_mk_binop_r mk r)
fun list_mk_binop_r0 _  x0 [] = x0
  | list_mk_binop_r0 mk x0 (h::r) = mk_binop mk (h, list_mk_binop_r0 mk x0 r)

fun undisch th = cprem_of th 1 |> assume |> implies_elim th

fun fix_frees pos = map (Term.dest_Free #> (fn (name,ty) =>
        (Binding.make (name, pos), (if ty = Term.dummyT then NONE else SOME ty), Mixfix.NoSyn)
      )) #> Proof.fix

fun free_to_fix_1 ctx (tm as Term.Free (name,ty)) =
      (case Variable.lookup_fixed ctx name of SOME name' => Term.Free (name', ty) | _ => tm)
  | free_to_fix_1 _ tm = tm
val free_to_var_ty = map_type_tfree (fn (name,sort) => TVar ((name,0),sort))
fun free_to_fix ctx = Term.map_aterms (free_to_fix_1 ctx)
val free_to_var = map_aterms (fn tm =>
      case tm of Free (name,ty) => Var ((name,0), free_to_var_ty ty)
         | Const (name,ty) => Const (name, free_to_var_ty ty)
         | Var (name,ty) => Var (name, free_to_var_ty ty))
end
