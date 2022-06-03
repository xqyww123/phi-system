(*  Title:      NuHelp.ML

Application-irrelevant basic tools.

*)

signature NU_HELP = sig
  val debug_term : Proof.context -> string -> term -> term
  val debug_term_global : theory -> string -> term -> term
  val last : 'a list -> 'a
  val front : 'a list -> 'a list

  type state = Proof.state

  exception NotFree of term
  exception Syntax of term

  val UI_top_handler (* process error presentation *) : Context.generic -> ('a -> 'b) -> 'a -> 'b
  val UI_top_handler_local : (Proof.context -> 'a) -> Proof.context -> 'a
  val UI_top_handler_global : (Context.theory -> 'a) -> Context.theory -> 'a

  val int_of_string : string -> int
  val dummy_c : cterm
  val has_head : string (* const name *) -> term -> bool
  (* map all free terms and free types inside to variables *)
  val free_to_var_ty : typ -> typ
  val free_to_var : term -> term
  (* map all Free term to the Fixed term if the name is fixed.*)
  val free_to_fix : Proof.context -> term -> term

  val string_of_term_generic : Context.generic -> term -> string

  val dest_monop_ty: string (* const name *) -> typ -> typ
  val dest_monop   : string (* const name *) -> term -> term
  val dest_monop_c : string (* const name *) -> cterm -> cterm
  val dest_binop   : string (* const name *) -> term -> term * term
  val dest_binop_c : string (* const name *) -> cterm -> cterm * cterm
  val dest_binop_ty  : string (* const name *) -> typ -> typ * typ
  val dest_binop_ty_c: string (* const name *) -> ctyp -> ctyp * ctyp
  val dest_triop   : string (* const name *) -> term -> term * term * term
  val dest_triop_c : string (* const name *) -> cterm -> cterm * cterm * cterm
  val dest_quadop   : string (* const name *) -> term -> term * term * term * term
  val dest_quadop_c : string (* const name *) -> cterm -> cterm * cterm * cterm * cterm
  val dest_quinop   : string (* const name *) -> term -> term * term * term * term * term
  val dest_quinop_c : string (* const name *) -> cterm -> cterm * cterm * cterm * cterm * cterm
  val strip_binop_r   (* right associative *) : string (* const name *) -> term -> term list
  val strip_binop_r_c (* right associative *) : string (* const name *) -> cterm -> cterm list
  val strip_binop_ty   (* right associative *) : string (* const name *) -> typ -> typ list
  val strip_binop_ty_c (* right associative *) : string (* const name *) -> ctyp -> ctyp list
  val strip_binop_l (* left associative *) : string (* const name *) -> term -> term list
  val mk_monop : string (* const name *) -> term -> term
  val mk_binop : string (* const name *) -> term * term -> term
  val mk_binop_ty : string (* const name *) -> typ * typ -> typ
  val list_mk_binop_l  (* left associative *) : string (* const name *) -> term list -> term
  val list_mk_binop_l0 (* left associative *) : string (* const name *)
        -> term (* initial term *) -> term list -> term
  val list_mk_binop_r  (* right associative *) : string (* const name *) -> term list -> term
  val list_mk_binop_r_ty  (* right associative *) : string (* type name *) -> typ list -> typ
  val list_mk_binop_r0 (* right associative *) : string (* const name *)
        -> term (* initial term *) -> term list -> term
  (*val dest_binder    : string (*binder name*) -> term -> term * term
  val dest_binder_c  : string (*binder name*) -> cterm -> cterm * cterm
  (* one wrapped by `BinderNameTag` *)
  val mk_abstract  : term (*var*) -> term (*body*) -> term
  val mk_binder    : string (*binder name*) -> term -> term -> term
  val strip_binder_n   : int (*number of binders to be destructed*) ->
        string -> term -> term list * term
  val strip_binder_nc : int -> string -> cterm -> cterm list * cterm
  val strip_binder   : string -> term -> term list * term
  val strip_binder_c : string -> cterm -> cterm list * cterm
  val strip_binder_vars : string -> term -> (string * typ) list
  val strip_binder_raw_body : string -> term -> term (* term containing raw bounds! *)
  val strip_binder_raw : string -> term -> (string * typ) list * term
  val list_mk_binder   : string -> term list -> term -> term *)
  val list_mk_abstract : term list -> term -> term
  val strip_implies_c : cterm -> cterm
  val tuple_abs : (string * (string * typ)) list -> term -> term

  val mk_Trueprop : term -> term
  val dest_Trueprop_c : cterm -> cterm
  (*  Γ |- A ==> B
  * ---------------
  *   Γ, A |- B *)
  val undisch : thm -> thm
  val undisch_all : thm -> cterm list * thm
  (*  Γ1 |- A ==> B      Γ2 |- A1 ==> A2 ==> ... A
  *  ------------------------------------------------
  *     Γ1 ∪ Γ2 |- A1 ==> A2 ==> ... ==> B
  * *)
  val implies_elim_with_prems : thm -> thm -> thm
  (* val forall_intr_by_names : string list -> thm -> thm *)
  val open_schematic_term : term -> term

  val map_fixes : ('a -> 'b) ->
        (binding * 'a option * mixfix) list -> (binding * 'b option * mixfix) list
  val fix_frees : Position.T -> term list (* free terms *)
        -> Proof.context -> (term -> term) * Proof.context
  val fix_frees_lst : Position.T -> term list (* free terms *)
        -> (binding * typ option * mixfix) list
end
structure NuHelp : NU_HELP = struct
open Term Thm

fun debug_term ctxt prompt term =
  (tracing (prompt ^ Syntax.string_of_term ctxt term); term)
fun debug_term_global thy prompt term =
  (tracing (prompt ^ Syntax.string_of_term_global thy term); term)

fun last [] = raise Fail "last"
  | last [x] = x
  | last (h::ls) = last ls
fun front [] = raise Fail "front"
  | front [x] = []
  | front (h::ls) = h :: front ls

type state = Proof.state
exception NotFree of term
exception Syntax of term

fun string_of_term_generic (Context.Theory thy) = Syntax.string_of_term_global thy
  | string_of_term_generic (Context.Proof ctxt) = Syntax.string_of_term ctxt

fun error s = Exn.reraise (ERROR s)
fun UI_top_handler ctxt f x =
  let
    val term = string_of_term_generic ctxt
  in
    f x
  handle 
      NotFree tm => error ("Free varaible is expected, "^ (term tm))
    | Syntax tm => error ("Syntax error, " ^ (term tm))
  end

fun UI_top_handler_local  f c = UI_top_handler (Context.Proof  c) f c
fun UI_top_handler_global f c = UI_top_handler (Context.Theory c) f c

fun has_head c (Const (c', _)) = (c = c')
  | has_head c (h $ _) = has_head c h
  | has_head _ _ = false

fun dest_monop_ty c (T as Type (c', [ty])) =
      if c = c' then ty else raise TYPE ("should be "^c, [T], [])
  | dest_monop_ty c T = raise TYPE ("should be "^c, [T], [])

fun dest_monop const (tm as h $ a) =
      if has_head const h then a else raise TERM ("dest_monop "^const, [tm])
  | dest_monop const tm = raise TERM ("dest_monop "^const, [tm])
fun dest_monop_c const tm =
      (dest_monop const (term_of tm); Thm.dest_arg tm)

fun dest_binop const (tm as h $ a $ b) =
      if has_head const h then (a,b) else raise TERM ("dest_binop "^const, [tm])
  | dest_binop const tm = raise TERM ("dest_binop "^const, [tm])
fun dest_binop_c const tm =
      (dest_binop const (term_of tm); Thm.dest_binop tm)
fun dest_binop_ty const (ty as Type (const', [a, b])) =
      if const' = const then (a,b) else raise TYPE ("dest_binop_ty "^const, [ty], [])
  | dest_binop_ty const ty = raise TYPE ("dest_binop_ty "^const, [ty], [])
fun dest_binop_ty_c const ty = (dest_binop_ty const (typ_of ty);
      (dest_ctyp0 ty, dest_ctyp1 ty))

fun strip_bin_r_assoc strip tm =
  case try strip tm of SOME (a,b) => a :: (strip_bin_r_assoc strip b) | _ => [tm]
val strip_binop_r   = strip_bin_r_assoc o dest_binop
val strip_binop_r_c = strip_bin_r_assoc o dest_binop_c
val strip_binop_ty   = strip_bin_r_assoc o dest_binop_ty
val strip_binop_ty_c = strip_bin_r_assoc o dest_binop_ty_c
fun strip_bin_l_assoc strip tm =
  case try strip tm of SOME (a,b) => b :: (strip_bin_l_assoc strip a) | _ => [tm]
val strip_binop_l = strip_bin_l_assoc o dest_binop

fun dest_triop const (tm as h $ a $ b $ c) =
      if has_head const h then (a,b,c) else raise TERM ("dest_triop "^const, [tm] )
  | dest_triop const tm = raise TERM ("dest_triop "^const, [tm])
fun dest_triop_c const tm =
      let
        val _ = dest_triop const (term_of tm)
        val (f,a3) = Thm.dest_comb tm
        val (f,a2) = Thm.dest_comb f
        val (_,a1) = Thm.dest_comb f
      in (a1,a2,a3) end

fun dest_quadop const (tm as h $ a $ b $ c $ d) =
      if has_head const h then (a,b,c,d) else raise TERM ("dest_quadop "^const, [tm] )
  | dest_quadop const tm = raise TERM ("dest_quadop "^const, [tm])
fun dest_quadop_c const tm =
      let
        val _ = dest_quadop const (term_of tm)
        val (f,a4) = Thm.dest_comb tm
        val (f,a3) = Thm.dest_comb f
        val (f,a2) = Thm.dest_comb f
        val (_,a1) = Thm.dest_comb f
      in (a1,a2,a3,a4) end

fun dest_quinop const (tm as h $ a $ b $ c $ d $ e) =
      if has_head const h then (a,b,c,d,e) else raise TERM ("dest_quinop "^const, [tm] )
  | dest_quinop const tm = raise TERM ("dest_quinop "^const, [tm])
fun dest_quinop_c const tm =
      let
        val _ = dest_quinop const (term_of tm)
        val (f,a5) = Thm.dest_comb tm
        val (f,a4) = Thm.dest_comb f
        val (f,a3) = Thm.dest_comb f
        val (f,a2) = Thm.dest_comb f
        val (f,a1) = Thm.dest_comb f
      in (a1,a2,a3,a4,a5) end

fun mk_Trueprop (tm as (Const (@{const_name Trueprop}, _) $ _)) = tm
  | mk_Trueprop tm = HOLogic.Trueprop $ tm
val dest_Trueprop_c = dest_monop_c "HOL.Trueprop"

fun mk_monop name arg = Const (name, Term.dummyT) $ arg
fun mk_binop name (lhs,rhs) = Const (name, Term.dummyT) $ lhs $ rhs
fun mk_binop_ty name (lhs,rhs) = Type (name, [lhs, rhs])
fun gen_list_mk_binop_r _  [] = raise Empty
  | gen_list_mk_binop_r _  [x] = x
  | gen_list_mk_binop_r mk (h::r) = mk (h, gen_list_mk_binop_r mk r)
val list_mk_binop_r = gen_list_mk_binop_r o mk_binop
val list_mk_binop_r_ty = gen_list_mk_binop_r o mk_binop_ty
fun list_mk_binop_r0 _  x0 [] = x0
  | list_mk_binop_r0 mk x0 (h::r) = mk_binop mk (h, list_mk_binop_r0 mk x0 r)
fun list_mk_binop_l _  [] = raise Empty
  | list_mk_binop_l _  [x] = x
  | list_mk_binop_l mk (h::r) = mk_binop mk (list_mk_binop_l mk r, h)
fun list_mk_binop_l0 _  x0 [] = x0
  | list_mk_binop_l0 mk x0 (h::r) = mk_binop mk (list_mk_binop_l0 mk x0 r, h)

(* fun dest_binder binder (tm as (Const (const,_) $ Abs (var,vty,body))) =
      if const = binder
      then Term.dest_abs (var,vty,body) |> apfst (fn var' => Free (var', vty))
      else raise TERM ("dest_binder "^binder, [tm])
  | dest_binder binder tm = raise TERM ("dest_binder "^binder, [tm])
fun dest_binder_c binder = dest_monop_c binder #> dest_abs NONE
val dest_binder_name_tag   = dest_binop   "NuPrime.BinderNameTag"
val dest_binder_name_tag_c = dest_binop_c "NuPrime.BinderNameTag" *)
fun mk_abstract (Free namty) body = absfree namty body
  | mk_abstract tm _ = raise TERM ("mk_abstract: should be a free variable", [tm])
fun mk_binder binder var body = mk_monop binder (mk_abstract var body)

fun gen_strip_binder num dest tm =
  if num = 0 then ([],tm)
  else case try dest tm
    of SOME (var,body) => gen_strip_binder (num - 1) dest body |> apfst (fn l => var :: l)
     | NONE =>
        if num > 0 then raise Fail "strip_binder: insufficient binders"
        else ([],tm)

(* fun strip_binder_n  n = gen_strip_binder n o dest_binder
fun strip_binder_nc n = gen_strip_binder n o dest_binder_c
val strip_binder   = strip_binder_n ~1
val strip_binder_c = strip_binder_nc ~1
fun list_mk_binder binder = fold (mk_binder binder) *)
val list_mk_abstract = fold mk_abstract

fun strip_binder_vars binder (Const (binder', _) $ Abs (name, ty, body))
      = if binder' = binder then (name,ty) :: strip_binder_vars binder body else []
  | strip_binder_vars _ _ = []
fun strip_binder_raw_body binder (tm as (Const (binder', _) $ Abs (name, ty, body)))
      = if binder' = binder then strip_binder_raw_body binder body else tm
  | strip_binder_raw_body _ tm = tm
fun strip_binder_raw binder tm =
  (strip_binder_vars binder tm, strip_binder_raw_body binder tm)


(** helpful rules **)

fun undisch th = cprem_of th 1 |> assume |> implies_elim th
fun undisch_all th = (cprems_of th, implies_elim_list th (map assume (cprems_of th)))

fun fix_frees_lst pos = map (Term.dest_Free #> (fn (name,ty) =>
        (Binding.make (name, pos), (if ty = Term.dummyT then NONE else SOME ty), Mixfix.NoSyn)
      ))
fun fix_frees pos frees =
  Proof_Context.add_fixes (fix_frees_lst pos frees)
    #> apfst (fn new_names => 
      subst_free (frees ~~ new_names |> map (fn (free,new) =>
          (free, Term.Free (new, Term.dest_Free free |> #2)))))


fun free_to_fix_1 ctxt (tm as Term.Free (name,ty)) =
      (case Variable.lookup_fixed ctxt name of SOME name' => Term.Free (name', ty) | _ => tm)
  | free_to_fix_1 _ tm = tm
val free_to_var_ty = map_type_tfree (fn (name,sort) => TVar ((name,0),sort))
fun free_to_fix ctxt = Term.map_aterms (free_to_fix_1 ctxt)
val free_to_var = map_aterms (fn tm =>
      case tm of Free (name,ty) => Var ((name,0), free_to_var_ty ty)
         | Const (name,ty) => Const (name, free_to_var_ty ty)
         | Var (name,ty) => Var (name, free_to_var_ty ty))

(* fun forall_intr_by_names names th =
  let
    val frees = Thm.add_frees th []
    val foralls = map (fn name =>
      find_first (fn x => (term_of x |> dest_Free |> #1) = name) frees |> the) names
  in
    fold Thm.forall_intr foralls th
  end *)

val dummy_c = cterm_of @{context} dummy_prop
fun open_schematic_term tm = 
  betapplys (tm, (strip_abs_vars tm |> map (fn (n,t) => Var ((n,0),t))))

fun implies_elim_with_prems thAB thA =
  fold (elim_implies o assume) (cprems_of thA) thA
    |> implies_elim thAB
    |> fold_rev implies_intr (cprems_of thA)
fun map_fixes f = map (fn (a,b,c) => (a,Option.map f b,c))

fun int_of_string str =
  case Int.fromString str
    of SOME x => x | NONE => error (str ^ " is not a integer")

fun strip_implies_c tm = strip_implies_c (#2 (dest_implies tm))
  handle TERM _ => tm

fun absfree'' (a',(a,T)) body = Abs (a', T, abstract_over (Free (a, T), body));
val prodconst = Const (@{const_name case_prod}, dummyT)
fun caseprod (tm as (Abs (_,_, Abs (_,_, _)))) = prodconst $ tm
  | caseprod (tm as (Abs (_,_, Const (@{const_name case_prod}, _) $ _))) = prodconst $ tm
  | caseprod tm = tm
val tuple_abs = fold_rev (caseprod oo absfree'')
    
end
