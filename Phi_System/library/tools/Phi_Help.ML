(*  Title:      Phi_Help.ML

Application-irrelevant basic tools.

*)

structure Phi_Kind = struct
  datatype T = Procedure | View_Shift | Implication | Construction
end

signature PHI_HELP = sig
include PHI_HELP

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
  val fix_leading_antecedent_meta_quantifiers : Proof.context -> term
                            -> term list (*quant vars*) * term list (*premises*) * term (*conclusion*) * Proof.context
                               (*where quantified variables are fixed*)
  val strip_meta_hhf_c :
        cterm -> Proof.context -> cterm list (*quant vars*) * cterm list (*premises*) * cterm * Proof.context
  val varified_leading_antecedent_meta_quantifiers : Proof.context -> term
                            -> term list (*premises*) * term (*conclusion*)
                               (*where quantified variables are varified (schematic variables)*)

  val string_of_term_generic : Context.generic -> term -> string

  (*Find the most general instantiation of the given type to meet the given sort*)
  val lift_type_sort : theory -> typ * sort -> Type.tyenv -> Type.tyenv
  val lift_type_sort' : theory -> (typ * sort) list -> typ TVars.table

  (*For tyenv/tenv given from Pattern.match*)
  val subst_tyenv : Type.tyenv -> typ TVars.table
  val subst_tenv  : Type.tyenv -> Envir.tenv -> term Vars.table
  val subst_env : Type.tyenv * Envir.tenv -> typ TVars.table * term Vars.table

  (*For tyenv/tenv given from Pattern.unify*)
  val norm_tyenv : Type.tyenv -> typ TVars.table
  val norm_tenv  : Type.tyenv -> Envir.tenv -> term Vars.table
  val norm_env : Type.tyenv * Envir.tenv -> typ TVars.table * term Vars.table

  val certify_tyvars : Context.generic -> typ TVars.table -> ctyp TVars.table
  val certify_tmvars : Context.generic -> term Vars.table -> cterm Vars.table
  val certify_vars : Context.generic -> typ TVars.table * term Vars.table -> ctyp TVars.table * cterm Vars.table
  val uncertify_tyvars : ctyp TVars.table -> typ TVars.table
  val uncertify_tmvars : cterm Vars.table -> term Vars.table
  val uncertify_vars   : ctyp TVars.table * cterm Vars.table -> typ TVars.table * term Vars.table

  (*val tvars_table_to_tyenv : ctyp TVars.table -> Type.tyenv
    val vars_table_to_tenv : cterm Vars.table -> Envir.tenv*)

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

  val empty_ctxt : Proof.context

  val instantiate_higher_order_schematic_var : int (*N*) -> Proof.context -> thm -> thm
  (*For the leading N antecedents only, if it contains any higher-order schematic
  variable where one of its parameters is always applied to constant argument, then instantiate
  the schematic variable with \<open>\<lambda>_. ?var\<close>

  N = ~1 means all antecedents, N = ~2 means to consider the conclusion of the thm in addition.
*)

  val generic_theory_mapping : (morphism -> Context.generic -> Context.generic) -> generic_theory -> generic_theory

  val list_mk_conj : term list -> term
  val list_mk_disj : term list -> term
  val conj_elims : Proof.context -> thm -> thm list


  (*The system `Term.abstract_over` doesn't support abstraction over a body containing loose bounds.
  The stuffs here improve it, but they still require that loose bounds do not occur in the redex*)
  val abstract_over : term * term -> term
  val lambda_name : string * term -> term -> term
  val lambda : term -> term -> term

end

structure Phi_Help : PHI_HELP = struct
open Phi_Help

fun last [] = raise Fail "last"
  | last [x] = x
  | last (h::ls) = last ls
fun front [] = raise Fail "front"
  | front [x] = []
  | front (h::ls) = h :: front ls

fun repeat f x = repeat f (f x) handle TERM _ => x | CTERM _ => x | THM _ => x
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
          = let val ([name'],ctxt') = Variable.add_fixes [a] ctxt
                val (v', B') = Thm.dest_abs_fresh name' (Thm.dest_arg ctm)
             in strip (v'::V,P) B B' ctxt'
            end
      | strip (V,P) X ctm ctxt = (rev V, rev P, ctm, ctxt)
  in strip ([],[]) (Thm.term_of cterm) cterm ctxt end


fun varified_leading_antecedent_meta_quantifiers ctxt sequent =
  let val (_,prems,leading_ant,ctxt') = fix_leading_antecedent_meta_quantifiers ctxt sequent
      val (leading_ant'::prems') = Variable.export_terms ctxt' ctxt (leading_ant::prems)
   in (prems',leading_ant')
  end

fun string_of_term_generic (Context.Theory thy) = Syntax.string_of_term_global thy
  | string_of_term_generic (Context.Proof ctxt) = Syntax.string_of_term ctxt


fun subst_tyenv tyenv
  = TVars.build (Vartab.fold (fn (N,(S,T)) => TVars.add ((N,S), T)) tyenv)

fun norm_tyenv tyenv
  = TVars.build (Vartab.fold (fn (N,(S,T)) => TVars.add ((N,S), Envir.norm_type tyenv T)) tyenv)

fun subst_tenv tyenv tenv =
  Vars.build (Vartab.fold (fn (N,(TY,TM)) =>
      Vars.add ((N, Envir.subst_type tyenv TY), Envir.eta_contract TM)) tenv)

fun norm_tenv tyenv tenv =
  Vars.build (Vartab.fold (fn (N,(TY,TM)) =>
      Vars.add ((N, Envir.norm_type tyenv TY),
                    Envir.norm_term (Envir.Envir {maxidx = ~1, tenv=tenv,tyenv=tyenv}) TM
                                |> Envir.eta_contract)) tenv)

fun subst_env (TY,TM) = (subst_tyenv TY, subst_tenv TY TM)
fun norm_env (TY,TM) = (norm_tyenv TY, norm_tenv TY TM)

fun certify_tyvars ctxt = TVars.map (K (Context.cases Thm.global_ctyp_of Thm.ctyp_of ctxt))
fun certify_tmvars ctxt = Vars.map (K (Context.cases Thm.global_cterm_of Thm.cterm_of ctxt))
fun certify_vars ctxt (ty, tm) = (certify_tyvars ctxt ty, certify_tmvars ctxt tm)
val uncertify_tyvars = TVars.map (K Thm.typ_of)
val uncertify_tmvars = Vars.map (K Thm.term_of)
fun uncertify_vars (ty, tm) = (uncertify_tyvars ty, uncertify_tmvars tm)


fun lift_type_sort thy (ty,sort) env00 =
  let val idx = Term.maxidx_of_typ ty
   in if Sign.of_sort thy (ty, sort)
      then env00
      else let val (env0,_) =
                     Sign.typ_unify thy
                           (ty, TVar(("_", idx), sort))
                           (env00, idx)
               val env = Vartab.map (fn N => (fn (S, TVar(_,S')) => (S, TVar(N,S'))
                                               | X => if N = ("_", 1) then X
                                                      else error "Internal bug 8bb59e49-9b57-48bc-b310-9da3b8f5ff7f"))
                         (Vartab.delete_safe ("_", idx) env0)
                in env
               end
           handle Type.TUNIFY => raise TYPE ("fail to unify the type to separation magma", [ty], [])
  end

fun lift_type_sort' thy ty_sorts =
  fold (fn (T,S) => fn env =>
    lift_type_sort thy (Envir.subst_type env T, S) env
  ) ty_sorts Vartab.empty
    |> subst_tyenv

(*
fun tvars_table_to_tyenv tab =
  Vartab.build (TVars.fold (fn ((N,S),T) => Vartab.insert (op =) (N,(S, Thm.typ_of T))) tab)

fun vars_table_to_tenv tab =
  Vartab.build (Vars.fold (fn ((N,S),T) => Vartab.insert (op =) (N,(S, Thm.term_of T))) tab)*)

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
fun strip_binder_raw_body binder (tm as (Const (binder', _) $ Abs (_, _, body)))
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


val empty_ctxt = Proof_Context.init_global Pure_Syn.bootstrap_thy


fun instantiate_higher_order_schematic_var num ctxt thm =
  let fun get_concl (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs(_,_,X)) = get_concl X
        | get_concl (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = get_concl X
        | get_concl X = X
      fun mk_ins ant (escape,ins0) =
        let
          fun count ret (X $ _) = count (ret + 1) X
            | count ret (Var v) = if member (op =) escape (fst v)
                                  then (ret, NONE)
                                  else (ret, SOME v)
            | count ret _ = (ret, NONE)
          val eq = ((op =) o apply2 fst)
          fun eq' ((a1,b1),(a2,b2)) = (fst a1 = fst a2 andalso b1 = b2)
          fun eqle ((a1,b1),(a2,b2)) = (fst a1 = fst a2 andalso b1 <= b2)
          fun sift set (X as _ $ _) =
               (case count 0 X
                  of (N, SOME v) =>
                      let fun visit (set,i) (X $ A) =
                                if exists_subterm (fn Bound _ => true | _ => false) A
                                then visit (sift (insert eq' (v,N-i) set) A, i+1) X
                                else visit (sift set A, i+1) X
                            | visit (set,_) _ = set
                       in visit (insert eqle (v, ~1 - N) set,1) X end
                   | _ =>
                      let fun visit set (A $ B) = visit (sift set B) A
                            | visit set X = sift set X
                       in visit set X end)
            | sift set (Abs(_,_,X)) = sift set X
            | sift set (Var v) =
                  if member (op =) escape (fst v)
                  then set
                  else insert eqle (v, ~1) set
            | sift set _ = set
          val set = sift [] ant
          fun calc_arity ret ((v,n)::L) =
                if n >= 0 orelse AList.defined eq ret v
                then calc_arity ret L
                else calc_arity ((v, fold (fn (v',m) => fn n' =>
                        if fst v' = fst v andalso m < 0 andalso ~1-m < n' then ~1-m else n') L (~1-n)) :: ret) L
            | calc_arity ret [] = ret
         val arity = calc_arity [] set
         fun forall_num n P = n < 0 orelse (P n andalso forall_num (n-1) P)
         val ins = map_filter (fn (v,n) =>
                if forall_num (n-1) (fn i => member eq' set (v,i))
                then NONE
                else let fun mk_term targs bs 0 T =
                                fold (fn b => fn X => X $ b) bs
                                  (Var (fst v, fold (fn a => fn T => \<^Type>\<open>fun a T\<close>) targs T))
                           | mk_term targs bs i \<^Type>\<open>fun a T\<close> =
                                if member (op =) set (v,n-i)
                                then Abs ("", a, mk_term (a::targs) (Bound (i-1) :: bs) (i-1) T)
                                else Abs ("", a, mk_term targs bs (i-1) T)
                           | mk_term _ _ _ _ = error "Internal bug #bb923326-bb1c-4ba6-9039-84963749ee92"
                         val term' = mk_term [] [] n (snd v)
                      in SOME (v, Thm.cterm_of ctxt term')
                     end
             ) arity
          fun collect_var ret (Var (v,_)) = insert (op =) v ret
            | collect_var ret (A $ B) = collect_var (collect_var ret A) B
            | collect_var ret (Abs(_,_,X)) = collect_var ret X
            | collect_var ret _ = ret
         in (collect_var escape ant, ins@ins0)
        end
      val (_, ins) = fold (fn prem => mk_ins (get_concl prem))
                          (if num = ~1 then Thm.prems_of thm
                           else if num = ~2 then Thm.prems_of thm @ [Thm.concl_of thm]
                           else List.take (Thm.prems_of thm, num))
                          ([],[])
  in Thm.instantiate (TVars.empty, Vars.make ins) thm
 end

fun generic_theory_mapping f =
  Context.mapping (Context.theory_map (f Morphism.identity))
                  (Local_Theory.declaration {syntax=false,pervasive=false} f)

fun list_mk_conj [] = \<^const>\<open>True\<close>
  | list_mk_conj L = foldr1 HOLogic.mk_conj L

fun list_mk_disj [] = \<^const>\<open>True\<close>
  | list_mk_disj L = foldr1 HOLogic.mk_disj L

fun conj_elims ctxt th =
  case Thm.prop_of th
    of \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> => []
     | _ => HOLogic.conj_elims ctxt th

(*The system `Term.abstract_over` doesn't support abstraction over a body containing loose bounds.
  This version improves it, but it still requires that loose bounds do not occur in `v`*)
fun abstract_over (v, body) =
  let
    fun abs lev tm =
      if v aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (lev + 1) t)
        | t $ u =>
            (abs lev t $ (abs lev u handle Same.SAME => u)
              handle Same.SAME => t $ abs lev u)
        | Bound j => if j >= lev then Bound (j+1) else Bound j
        | _ => raise Same.SAME);
  in abs 0 body handle Same.SAME => body end;

fun lambda_name (x, v) t =
  Abs (if x = "" then Term.term_name v else x, fastype_of v, abstract_over (v, t));

fun lambda v t = lambda_name ("", v) t;


end

functor Single_Thread_Proof_Data(Arg: PROOF_DATA_ARGS): PROOF_DATA = struct

type T = Arg.T

structure Data = Proof_Data (
type T = Arg.T Unsynchronized.ref
val init = Unsynchronized.ref o Arg.init
)

val get = Unsynchronized.! o Data.get
fun put x ctxt = (Data.get ctxt := x; ctxt)
fun map f ctxt = let val r = Data.get ctxt in r := f (!r); ctxt end

end

signature PROOF_DATA_OPT_ARGS =
sig
  type T
end;

signature PROOF_DATA_OPT =
sig
  type T
  val get: Proof.context -> T option
  val put: T -> Proof.context -> Proof.context
  val del: Proof.context -> Proof.context
  val map: (T option -> T) -> Proof.context -> Proof.context
end;

functor Single_Thread_Proof_Data_Opt(Arg: PROOF_DATA_OPT_ARGS): PROOF_DATA_OPT = struct

type T = Arg.T

structure Data = Proof_Data (
type T = Arg.T Unsynchronized.ref option
val init = K NONE
)

val get = Option.map Unsynchronized.! o Data.get

fun put x ctxt =
  case Data.get ctxt
    of SOME r => (r := x; ctxt)
     | NONE => Data.put (SOME (Unsynchronized.ref x)) ctxt

val del = Data.put NONE

fun map f ctxt =
  case Data.get ctxt
    of SOME r => (r := f (SOME (!r)); ctxt)
     | NONE => Data.put (SOME (Unsynchronized.ref (f NONE))) ctxt

end


