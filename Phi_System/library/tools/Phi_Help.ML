(*  Title:      Phi_Help.ML

Application-irrelevant basic tools.

*)

structure Phi_Kind = struct
  datatype T = Procedure | View_Shift | Implication | Construction
end

signature PHI_HELP = sig
include PHI_HELP

(**** Basic Operations ****)

  val string_of_term_generic : Context.generic -> term -> string

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

  val generic_theory_mapping : Position.T -> (morphism -> Context.generic -> Context.generic) -> generic_theory -> generic_theory

  (*The system `Term.abstract_over` doesn't support abstraction over a body containing loose bounds.
  The stuffs here improve it, but they still require that loose bounds do not occur in the redex*)
  val abstract_over : term * term -> term
  val lambda_name : string * term -> term -> term
  val lambda : term -> term -> term
  val subst_free_with_loose_bounds : (term * term) list -> term -> term
          (*supports loose bounds either in the redex or the residue*)

  val reason_tracing_inst : Proof.context -> (thm -> thm option)
                         -> term -> ((ctyp TVars.table * cterm Vars.table) * thm) option

  val reason_tracing_tyinst : Proof.context -> (thm -> thm option)
                           -> term -> (ctyp TVars.table * thm) option

end

structure Phi_Help : PHI_HELP = struct
open Phi_Help


fun string_of_term_generic (Context.Theory thy) = Syntax.string_of_term_global thy
  | string_of_term_generic (Context.Proof ctxt) = Syntax.string_of_term ctxt




(*
fun tvars_table_to_tyenv tab =
  Vartab.build (TVars.fold (fn ((N,S),T) => Vartab.insert (op =) (N,(S, Thm.typ_of T))) tab)

fun vars_table_to_tenv tab =
  Vartab.build (Vars.fold (fn ((N,S),T) => Vartab.insert (op =) (N,(S, Thm.term_of T))) tab)*)




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

fun generic_theory_mapping pos f =
  Context.mapping (Context.theory_map (f Morphism.identity))
                  (Local_Theory.declaration {syntax=false,pervasive=false, pos=pos} f)

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

fun subst_free_with_loose_bounds [] = I
  | subst_free_with_loose_bounds pairs =
      let fun aconv_bound_diff d (t1 $ u1, t2 $ u2) =
                aconv_bound_diff d (t1,t2) andalso aconv_bound_diff d (u1,u2)
            | aconv_bound_diff d (Abs (_, T1, t1), Abs (_, T2, t2)) =
                aconv_bound_diff d (t1,t2) andalso T1 = T2
            | aconv_bound_diff d (Bound i, Bound j) = i = j + d
            | aconv_bound_diff _ (a1,a2) = a1 = a2

          fun substf i u =
            case AList.lookup (aconv_bound_diff i) pairs u
              of SOME u' => Term.incr_boundvars i u'
               | NONE => (case u of Abs(a,T,t) => Abs(a, T, substf (i+1) t)
                                  | t$u' => substf i t $ substf i u'
                                  | _ => u)
       in substf 0 end


fun reason_tracing_inst ctxt reason goal_term =
  let val tvars = Term.add_tvars goal_term []
      val vars  = Term.add_vars goal_term []
      val goal_term = goal_term
              |> fold_rev (fn NS => fn X => Logic.mk_conjunction (Logic.mk_term (Logic.mk_type (TVar NS)), X)) tvars
              |> fold_rev (fn NT => fn X => Logic.mk_conjunction (Logic.mk_term (Var NT), X)) vars
      val goal = Thm.cterm_of ctxt goal_term
              |> Goal.init
              |> funpow (length tvars) (fn th => Drule.termI RS (Conjunction.conjunctionI RS th))
              |> funpow (length vars) (fn th => Drule.termI RS (Conjunction.conjunctionI RS th))
   in reason goal
   |> Option.map (fn th =>
        let val th = Goal.conclude th
            val (tm_insts, th) = funpow_yield (length  vars) Conjunction.elim th
            val (ty_insts, th) = funpow_yield (length tvars) Conjunction.elim th
            val tm_insts = map Drule.dest_term tm_insts
            val ty_insts = map (Thm.dest_ctyp0 o Thm.ctyp_of_cterm o Drule.dest_term) ty_insts
         in ((TVars.make (tvars ~~ ty_insts), Vars.make (vars ~~ tm_insts)), th)
        end)
  end

fun reason_tracing_tyinst ctxt reason goal_term =
  let val tvars = Term.add_tvars goal_term []
      val goal_term = goal_term
              |> fold_rev (fn NS => fn X => Logic.mk_conjunction (Logic.mk_term (Logic.mk_type (TVar NS)), X)) tvars
      val goal = Thm.cterm_of ctxt goal_term
              |> Goal.init
              |> funpow (length tvars) (fn th => Drule.termI RS (Conjunction.conjunctionI RS th))
   in reason goal
   |> Option.map (fn th =>
        let val th = Goal.conclude th
            val (ty_insts, th) = funpow_yield (length tvars) Conjunction.elim th
            val ty_insts = map (Thm.dest_ctyp0 o Thm.ctyp_of_cterm o Drule.dest_term) ty_insts
         in (TVars.make (tvars ~~ ty_insts), th)
        end)
  end



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


