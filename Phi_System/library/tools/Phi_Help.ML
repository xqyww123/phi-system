(*  Title:      Phi_Help.ML

Application-irrelevant basic tools.

*)

structure Phi_Kind = struct
  datatype T = Procedure | View_Shift | Implication | Construction
end

signature PHI_HELP = sig

(**** Basic Operations ****)
  val last : 'a list -> 'a
  val front : 'a list -> 'a list
  val repeat : ('a -> 'a) -> 'a -> 'a
  val ntimes : int -> (int -> 'a -> 'a) -> 'a -> 'a

  val has_head : string (* const name *) -> term -> bool

  val strip_meta_hhf : term -> (string * typ) list (*quantified variables*)
                              * term list (*premises of the antecedent*)
                              * term (*conclusion containing loose bound*)
  val leading_antecedent' : thm -> term
  val leading_antecedent : term -> (string * typ) list (*quantified variables*)
                                 * term list (*premises of the antecedent*)
                                 * term (*conclusion containing loose bound*)
  val rewrite_leading_antecedent : Proof.context -> thm -> thm

  val string_of_term_generic : Context.generic -> term -> string

  val tyenv_to_tvars_table : Proof.context -> Type.tyenv -> ctyp TVars.table
  val tenv_to_vars_table : Proof.context -> Type.tyenv -> Envir.tenv -> cterm Vars.table
  val env_to_table : Proof.context -> (Type.tyenv * Envir.tenv)
                                   -> (ctyp TVars.table * cterm Vars.table)

  val beta_eta_contract : thm -> thm
  val beta_eta_contract_leading_antecedent : thm -> thm

  val safe_fastype_of : term -> typ (*improved Term.fastype_of which considers dummyT*)

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
  val strip_binop_r_last (* right associative *) : string (* const name *) -> term -> term
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

  val strip_binder_vars : string -> term -> (string * typ) list
  val strip_binder_raw_body : string -> term -> term (* term containing raw bounds! *)
  val strip_binder_raw : string -> term -> (string * typ) list * term
  val strip_implies_c : cterm -> cterm

  (* abstract `free variables` into a lambda abstraction of a tuple of variables named `names`,
     viz. abstracts `Term` to `\<lambda>(v1,v2,v3). Term`.*)
  val tuple_abs : (string (*name*) * (string * typ) (*free variable*)) list -> term -> term

  val mk_Trueprop : term -> term
  val dest_Trueprop_c : cterm -> cterm

  val comp_rule : Proof.context -> bool -> thm -> thm -> thm
  val comp_rule_incr_left  : Proof.context -> thm -> thm -> thm
  val comp_rule_incr_right : Proof.context -> thm -> thm -> thm

  val debug_RS : Proof.context -> thm -> thm -> thm
end

structure Phi_Help : PHI_HELP = struct

fun last [] = raise Fail "last"
  | last [x] = x
  | last (h::ls) = last ls
fun front [] = raise Fail "front"
  | front [x] = []
  | front (h::ls) = h :: front ls

fun repeat f x = repeat f (f x) handle TERM _ => x | THM _ => x
fun ntimes_i i n f x = if i < n then ntimes_i (i+1) n f (f i x) else x
fun ntimes n f x = ntimes_i 0 n f x

fun leading_antecedent' thm = fst (Logic.dest_implies (Thm.prop_of thm))

fun strip_meta_hhf term =
  let
    fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,H::P) B
      | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
      | strip (V,P) X = (rev V, rev P, X)
  in strip ([],[]) term end

fun leading_antecedent (Const("Pure.imp", _) $ H $ _) = strip_meta_hhf H
  | leading_antecedent X = raise TERM ("has no antecedent", [X])

fun rewrite_leading_antecedent ctxt =
  Conv.fconv_rule (Conv.implies_conv (Simplifier.rewrite ctxt) Conv.all_conv)

fun string_of_term_generic (Context.Theory thy) = Syntax.string_of_term_global thy
  | string_of_term_generic (Context.Proof ctxt) = Syntax.string_of_term ctxt


fun tyenv_to_tvars_table ctxt : Type.tyenv -> ctyp TVars.table
  = Vartab.dest
 #> map (fn (N,(S,T)) => ((N,S), Thm.ctyp_of ctxt T))
 #> TVars.make

fun tenv_to_vars_table ctxt tyenv : Envir.tenv -> cterm Vars.table
  = Vartab.dest
 #> map (fn (N,(TY,TM)) => ((N, Envir.subst_type tyenv TY),
                            Thm.cterm_of ctxt (Envir.subst_term_types tyenv TM
                                            |> Envir.eta_contract)))
 #> Vars.make

fun env_to_table ctxt (TY,TM)
  = (tyenv_to_tvars_table ctxt TY,
     tenv_to_vars_table ctxt TY TM)

fun beta_eta_contract th =
  if Term.could_beta_eta_contract (Thm.prop_of th)
  then Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th
  else th

fun beta_eta_contract_leading_antecedent th =
  if Term.could_beta_eta_contract (leading_antecedent' th)
  then Thm.equal_elim (Conv.implies_conv Drule.beta_eta_conversion
                                         Conv.all_conv (Thm.cprop_of th)) th
  else th



local

fun fastype_of_term Ts (Abs (_, T, t)) = T --> fastype_of_term (T :: Ts) t
  | fastype_of_term Ts (t $ _) = range_type_of Ts t
  | fastype_of_term Ts a = fastype_of_atom Ts a
and fastype_of_atom _ (Const (_, T)) = T
  | fastype_of_atom _ (Free (_, T)) = T
  | fastype_of_atom _ (Var (_, T)) = T
  | fastype_of_atom Ts (Bound i) = fastype_of_bound Ts i
and fastype_of_bound (T :: Ts) i = if i = 0 then T else fastype_of_bound Ts (i - 1)
  | fastype_of_bound [] i = raise TERM ("fastype_of: Bound", [Bound i])
and range_type_of Ts (Abs (_, T, u)) = fastype_of_term (T :: Ts) u
  | range_type_of Ts (t $ u) = range_type_ofT (t $ u) (range_type_of Ts t)
  | range_type_of Ts a = range_type_ofT a (fastype_of_atom Ts a)
and range_type_ofT _ (Type ("fun", [_, T])) = T
  | range_type_ofT _ (Type ("dummy", _)) = dummyT
  | range_type_ofT t _ = raise TERM ("fastype_of: expected function type", [t]);

in
val safe_fastype_of = fastype_of_term [];
end



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
      (dest_monop const (Thm.term_of tm); Thm.dest_arg tm)

fun dest_binop const (tm as h $ a $ b) =
      if has_head const h then (a,b) else raise TERM ("dest_binop "^const, [tm])
  | dest_binop const tm = raise TERM ("dest_binop "^const, [tm])
fun dest_binop_c const tm =
      (dest_binop const (Thm.term_of tm); Thm.dest_binop tm)
fun dest_binop_ty const (ty as Type (const', [a, b])) =
      if const' = const then (a,b) else raise TYPE ("dest_binop_ty "^const, [ty], [])
  | dest_binop_ty const ty = raise TYPE ("dest_binop_ty "^const, [ty], [])
fun dest_binop_ty_c const ty = (dest_binop_ty const (Thm.typ_of ty);
      (Thm.dest_ctyp0 ty, Thm.dest_ctyp1 ty))

fun strip_bin_r_assoc strip tm =
  case try strip tm of SOME (a,b) => a :: (strip_bin_r_assoc strip b) | _ => [tm]
fun strip_bin_r_assoc_last strip tm =
  case try strip tm of SOME (a,b) => strip_bin_r_assoc_last strip b | _ => tm

val strip_binop_r   = strip_bin_r_assoc o dest_binop
val strip_binop_r_last = strip_bin_r_assoc_last o dest_binop
val strip_binop_r_c = strip_bin_r_assoc o dest_binop_c
val strip_binop_ty   = strip_bin_r_assoc o dest_binop_ty
val strip_binop_ty_c = strip_bin_r_assoc o dest_binop_ty_c
fun strip_bin_l_assoc L strip tm =
  case try strip tm of SOME (a,b) => (strip_bin_l_assoc (b :: L) strip a) | _ => (tm :: L)
val strip_binop_l = strip_bin_l_assoc [] o dest_binop

fun dest_triop const (tm as h $ a $ b $ c) =
      if has_head const h then (a,b,c) else raise TERM ("dest_triop "^const, [tm] )
  | dest_triop const tm = raise TERM ("dest_triop "^const, [tm])
fun dest_triop_c const tm =
      let
        val _ = dest_triop const (Thm.term_of tm)
        val (f,a3) = Thm.dest_comb tm
        val (f,a2) = Thm.dest_comb f
        val (_,a1) = Thm.dest_comb f
      in (a1,a2,a3) end

fun dest_quadop const (tm as h $ a $ b $ c $ d) =
      if has_head const h then (a,b,c,d) else raise TERM ("dest_quadop "^const, [tm] )
  | dest_quadop const tm = raise TERM ("dest_quadop "^const, [tm])
fun dest_quadop_c const tm =
      let
        val _ = dest_quadop const (Thm.term_of tm)
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
        val _ = dest_quinop const (Thm.term_of tm)
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

(*fun gen_strip_binder num dest tm =
  if num = 0 then ([],tm)
  else case try dest tm
    of SOME (var,body) => gen_strip_binder (num - 1) dest body |> apfst (fn l => var :: l)
     | NONE =>
        if num > 0 then raise Fail "strip_binder: insufficient binders"
        else ([],tm)

fun strip_binder_n  n = gen_strip_binder n o dest_binder
fun strip_binder_nc n = gen_strip_binder n o dest_binder_c
val strip_binder   = strip_binder_n ~1
val strip_binder_c = strip_binder_nc ~1 *)


fun strip_binder_vars binder (Const (binder', _) $ Abs (name, ty, body))
      = if binder' = binder then (name,ty) :: strip_binder_vars binder body else []
  | strip_binder_vars _ _ = []
fun strip_binder_raw_body binder (tm as (Const (binder', _) $ Abs (name, ty, body)))
      = if binder' = binder then strip_binder_raw_body binder body else tm
  | strip_binder_raw_body _ tm = tm
fun strip_binder_raw binder tm =
  (strip_binder_vars binder tm, strip_binder_raw_body binder tm)


fun strip_implies_c tm = strip_implies_c (#2 (Thm.dest_implies tm))
  handle TERM _ => tm

fun absfree'' (a',(a,T)) body = Abs (a', T, abstract_over (Free (a, T), body));
val prodconst = Const (@{const_name case_prod}, dummyT)
fun caseprod (tm as (Abs (_,_, Abs (_,_, _)))) = prodconst $ tm
  | caseprod (tm as (Abs (_,_, Const (@{const_name case_prod}, _) $ _))) = prodconst $ tm
  | caseprod tm = tm
val tuple_abs = fold_rev (caseprod oo absfree'')


fun comp_rule ctxt incremented th1 th2 =
  Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = incremented}
    (false, th1, 0) 1 th2
  |> Seq.list_of |> distinct Thm.eq_thm
  |> (fn [th] => Thm.solve_constraints th | _ => raise THM ("COMP", 1, [th1, th2]));

fun comp_rule_incr_left  ctxt th1 th2 = comp_rule ctxt true (Drule.incr_indexes th2 th1) th2
fun comp_rule_incr_right ctxt th1 th2 = comp_rule ctxt true th1 (Drule.incr_indexes th1 th2)

fun debug_RS ctxt tha thb =
  (case Seq.chop 2 (Thm.biresolution (SOME (Config.put Pattern.unify_trace_failure true ctxt))
                                     false [(false, tha)] 1 thb) of
    ([th], _) => Thm.solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", 1, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", 1, [tha, thb]));


end
