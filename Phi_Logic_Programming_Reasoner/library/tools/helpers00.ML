signature PHI_HELP = sig

  val has_head : string (* const name *) -> term -> bool

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

  val mk_Trueprop : term -> term
  val dest_Trueprop_c : cterm -> cterm


(*TODO: consider meta_Ball*)
val strip_meta_hhf : term -> (string * typ) list (*quantified variables*)
                            * term list (*premises of the antecedent*)
                            * term (*conclusion containing loose bound*)
val strip_meta_hhf_bvtys : term -> bv_typs * term
val strip_meta_hhf_bvs : term -> bvs * term
val leading_antecedent : term -> (string * typ) list (*quantified variables*)
                               * term list (*premises of the antecedent*)
                               * term (*conclusion containing loose bound*)
val fix_leading_antecedent_meta_quantifiers : Proof.context -> term
                          -> term list (*quant vars*) * term list (*premises*) * term (*conclusion*) * Proof.context
                             (*where quantified variables are fixed*)
val strip_meta_hhf_c :
      cterm -> Proof.context -> cterm list (*quant vars*) * cterm list (*premises*) * cterm * Proof.context

val mk_meta_hhf :
      (string * typ) list (*quantified variables*)
    * term list (*premises of the antecedent*)
    * term (*conclusion containing loose bound*)
    -> term

val varified_leading_antecedent_meta_quantifiers : Proof.context -> term
                          -> term list (*premises*) * term (*conclusion*)
                             (*where quantified variables are varified (schematic variables)*)

val aconv_bound_diff : int -> term * term -> bool
val subst_with_loose_bounds : (term * term) list -> term -> term
          (*supports loose bounds either in the redex or the residue*)

val K_I : 'a -> 'b -> 'b

end

structure Phi_Help : PHI_HELP = struct

fun has_head c (Const (c', _)) = (c = c')
  | has_head c (h $ _) = has_head c h
  | has_head _ _ = false

fun K_I _ x = x


fun strip_meta_hhf term =
  let
    fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,H::P) B
      | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
      | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
          strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
      | strip (V,P) X = (rev V, rev P, X)
  in strip ([],[]) term end

fun strip_meta_hhf_bvtys term =
  let
    fun strip V (Const("Pure.imp", _) $ H $ B) = strip V B
      | strip V (Const("Pure.all", _) $ Abs (_, T, B)) = strip (T::V) B
      | strip V (Const("Pure.all", _) $ X) = strip V X
      | strip V X = (V, X)
  in strip [] term end

fun strip_meta_hhf_bvs term =
  let
    fun strip V (Const("Pure.imp", _) $ H $ B) = strip V B
      | strip V (Const("Pure.all", _) $ Abs (N, T, B)) = strip ((N,T)::V) B
      | strip V (Const("Pure.all", _) $ X) = strip V X
      | strip V X = (V, X)
  in strip [] term end

fun mk_meta_hhf (vars, prems, concl) =
  fold_rev (fn P => fn X => \<^Const>\<open>Pure.imp\<close> $ P $ X) prems concl
    |> fold_rev (fn (N,Ty) => fn X => \<^Const>\<open>Pure.all Ty\<close> $ Abs (N, Ty, X)) vars

fun leading_antecedent (Const("Pure.imp", _) $ H $ _) = strip_meta_hhf H
  | leading_antecedent X = raise TERM ("has no antecedent", [X])

fun fix_leading_antecedent_meta_quantifiers ctxt0 sequent =
  let
    val (qvs, prems, ant01) = leading_antecedent sequent

    (* fix universally quantified variables *)
    val (qv_names, ctxt'01) = Variable.add_fixes (map fst qvs) ctxt0
    val qvars = map2 (fn N => fn (_,T) => Free (N,T)) qv_names qvs
    val ctxt = fold Variable.declare_term qvars ctxt'01
    val leading_ant = subst_bounds (rev qvars, ant01)
  in (qvars,prems,leading_ant,ctxt)
  end

fun strip_meta_hhf_c cterm ctxt =
  let
    fun strip (V,P) (Const("Pure.imp", _) $ H $ B) ctm ctxt
          = strip (V, Thm.dest_arg1 ctm :: P) B (Thm.dest_arg ctm) ctxt
      | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) ctm ctxt
          = let val ([name'],ctxt') = Variable.variant_fixes [a] ctxt
                val (v', B') = Thm.dest_abs_fresh name' (Thm.dest_arg ctm)
             in strip (v'::V,P) B B' ctxt'
            end
      | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ B) ctm ctxt
          = let val ([name'],ctxt') = Variable.variant_fixes ["_"] ctxt
                val v' = Thm.cterm_of ctxt (Free (name', ty))
                val B' = Thm.apply (Thm.dest_arg ctm) v'
             in strip (v' :: V, P) B B' ctxt'
            end
      | strip (V,P) X ctm ctxt = (rev V, rev P, ctm, ctxt)
  in strip ([],[]) (Thm.term_of cterm) cterm ctxt end

fun varified_leading_antecedent_meta_quantifiers ctxt sequent =
  let val (_,prems,leading_ant,ctxt') = fix_leading_antecedent_meta_quantifiers ctxt sequent
      val (leading_ant'::prems') = Variable.export_terms ctxt' ctxt (leading_ant::prems)
   in (prems',leading_ant')
  end

fun aconv_bound_diff d (t1 $ u1, t2 $ u2) =
      aconv_bound_diff d (t1,t2) andalso aconv_bound_diff d (u1,u2)
  | aconv_bound_diff d (Abs (_, T1, t1), Abs (_, T2, t2)) =
      aconv_bound_diff d (t1,t2) andalso T1 = T2
  | aconv_bound_diff d (Bound i, Bound j) = i = j + d
  | aconv_bound_diff _ (a1,a2) = a1 = a2

fun subst_with_loose_bounds [] = I
  | subst_with_loose_bounds pairs =
      let fun substf i u =
            case AList.lookup (aconv_bound_diff i) pairs u
              of SOME u' => Term.incr_boundvars i u'
               | NONE => (case u of Abs(a,T,t) => Abs(a, T, substf (i+1) t)
                                  | t$u' => substf i t $ substf i u'
                                  | _ => u)
       in substf 0 end






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
  case try strip tm of SOME (_,b) => strip_bin_r_assoc_last strip b | _ => tm

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
        val (_,a1) = Thm.dest_comb f
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



fun strip_binder_vars binder (Const (binder', _) $ Abs (name, ty, body))
      = if binder' = binder then (name,ty) :: strip_binder_vars binder body else []
  | strip_binder_vars binder (Const (binder', \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ _)
      = if binder' = binder then [("_",ty)] else []
  | strip_binder_vars _ _ = []
fun strip_binder_raw_body binder (tm as (Const (binder', _) $ Abs (_, _, body)))
      = if binder' = binder then strip_binder_raw_body binder body else tm
  | strip_binder_raw_body binder (tm as (Const (binder', _) $ X))
      = if binder' = binder then Term.incr_boundvars 1 X $ Bound 0 else tm
  | strip_binder_raw_body _ tm = tm
fun strip_binder_raw binder tm =
  (strip_binder_vars binder tm, strip_binder_raw_body binder tm)


fun strip_implies_c tm = strip_implies_c (#2 (Thm.dest_implies tm))
  handle TERM _ => tm

end

fun map3 _ [] [] [] = []
  | map3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: map3 f xs ys zs
  | map3 _ _ _ _ = raise ListPair.UnequalLengths

fun map4 _ [] [] [] [] = []
  | map4 f (x :: xs) (y :: ys) (z :: zs) (w :: ws)
      = f x y z w :: map4 f xs ys zs ws
  | map4 _ _ _ _ _ = raise ListPair.UnequalLengths