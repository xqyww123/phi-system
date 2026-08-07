(* FILE: Phi_Logic_Programming_Reasoner/library/pattern.ML
   AUTHOR: Tobias Nipkow, Christine Heinzelmann, and Stefan Berghofer, TU Muenchen
   Modified by: Qiyuan Xu

   To support matching loose bounds in the target object.
   Regard them as fixed variables.
*)

type bv_typs = typ list (*types of contextual bound variables*)
type bvs = (string * typ) list

type spattern = term (*improved pattern where variables of a name \<open>var\<close> or a name leaded by \<open>var_\<close>,
                       match only schematic variables.*)

signature PLPR_PATTERN = sig

type fixed_bounds = int -> bool
      (*whether the bound variable is fixed, so regarded as a normal free variable*)

(*This is the upstream `Pure/pattern.ML' algorithm with `binders' initialised to
  `bvs' -- the caller's contextual binders count as already entered -- plus one
  relaxation: a contextual bound variable the caller declares fixed through
  `fixed_bounds' may stay inside a binding stored into `tenv', which plain
  upstream forbids.

  The loose `Bound's in a term stored into `tenv' are numbered from the position
  where `match' was called: entry k of `bvs' is always `Bound k', no matter how
  deep inside the match the binding was found.  A consumer substituting such a
  binding into a position under n binders must `Term.incr_boundvars n' it, and
  must beta-normalise before asking what that depth is.

  The `tenv' handed in must come from calls with the SAME `bvs' and
  `fixed_bounds': the repeated-schematic checks -- in `cases' on the higher-order
  path and in `first_order_match' on the fallback -- both rely on it.  That holds
  for `first_order_match' as a separate entry point too.*)
val match: theory -> fixed_bounds -> bvs -> term * term
        -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

val first_order_match: theory -> fixed_bounds -> bv_typs -> term * term
                              -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

val matches: theory -> fixed_bounds -> bvs -> term * term -> bool

val mk_spattern : term -> spattern
val smatch : theory -> fixed_bounds -> bvs -> spattern * term
          -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
val does_smatch : theory -> fixed_bounds -> bvs -> spattern * term -> bool

(*`Envir.subst_term' for a `tenv' that came out of `match' above.  The loose
  `Bound's in a stored binding are numbered from the position `match' was called
  at, so an occurrence landing under n binders has to be lifted by n; n differs
  per occurrence, which is why the caller cannot supply it and why plain
  `Envir.subst_term' silently captures.*)
val subst_term : Type.tyenv * Envir.tenv -> term -> term

val strip_typs : term -> term

end

structure PLPR_Pattern : PLPR_PATTERN = struct
open Pattern

type bv_typs = typ list (*types of bound variables of the object.*)
type bvs = (string * typ) list
type fixed_bounds = int -> bool

fun idx [] j     = raise Unif
  | idx(i::is) j = if (i:int) =j then length is else idx is j;

fun mkabs (binders,is,t)  =
    let fun mk(i::is) = let val (x,T) = nth binders i
                        in Abs(x,T,mk is) end
          | mk []     = t
    in mk is end;

fun ints_of []             = []
  | ints_of (Bound i ::bs) =
      let val is = ints_of bs
      in if member (op =) is i then raise Pattern else i::is end
  | ints_of _              = raise Pattern;

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;

fun mapbnd f =
    let fun mpb d (Bound(i))     = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs(s,T,t))   = Abs(s,T,mpb(d+1) t)
          | mpb d ((u1 $ u2))    = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end;

fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

(*Un-abstract a binding stored by `match_bind' so it can be compared against an
  object sitting `diff' binders deep.  Two deviations from upstream, both because
  a stored binding is no longer necessarily closed:
    - upstream's `handle Subscript => k' is dead code there (a closed binding has
      no index past `jn'); here such an index is a contextual bound variable
      numbered from the position `match' was called at, so it must be lifted by
      `diff';
    - upstream's `red t [] [] = t' clause is gone.  It short-circuits `is = []',
      which is the commonest shape (a schematic taking no arguments), and returns
      the binding without that lift.*)
fun red diff (Abs(_,_,s)) (i::is) js = red diff s is (i::js)
  | red diff t            is      jn =
      app (mapbnd (fn k => nth jn k handle Subscript => k - length jn + diff) t, is);


val incr = mapbnd (fn i => i+1);

fun typ_match thy TU tyenv = Sign.typ_match thy TU tyenv
  handle Type.TYPE_MATCH => raise MATCH;

(*The indices in `t' that this binding may NOT keep:
    i < d   -- a bound variable entered during this match; the binder that binds it
               is not coming along, so there is no valid way to relocate it
    i >= d  -- a contextual bound variable, `bvs' entry (i - d); it may be kept only
               if the caller declared it fixed, and then instantiation must shift it
               by the depth of the position it lands in *)
fun escaping fixed_bounds d t =
  filter (fn i => i < d orelse not (fixed_bounds (i - d))) (loose_bnos t);

(*This gate is also the SOLE precondition that makes the negative shifts below
  safe: an empty result says every loose index in `t' is >= d, so shifting down
  by d cannot go past zero.  `Term.incr_boundvars' does not check (term.ML:690) --
  defeat the gate and the store yields terms like `Bound (~1)'.*)

(* First Order Match *)
(*Improved from the system first_order_match, by allowing loose bounds in the object term,
    and regarding them as fixed free variables.*)
fun first_order_match thy fixed_bounds bv_tys (t,u) env =
  let
    fun mtch bv_tys lev (instsp as (tyinsts,insts)) = fn
        (Var(ixn,T), t)  =>
          if null (escaping fixed_bounds lev t)
          then (case Envir.lookup1 insts (ixn, T) of
                  (*`fastype_of1' must see the UNSHIFTED `t': `bv_tys' is indexed
                    from the current depth, the stored term from the call site.*)
                  NONE => (typ_match thy (T, fastype_of1 (bv_tys, t)) tyinsts,
                           Vartab.update_new (ixn, (T, Term.incr_boundvars (~lev) t)) insts)
                  (*`u' is stored numbered from the call site (just above), so
                    bring `t' down from the current depth before comparing.*)
                | SOME u => if Envir.aeconv (Term.incr_boundvars (~lev) t, u) then instsp
                            else raise MATCH)
          else raise MATCH
      | (Free (a,T), Free (b,U)) =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else raise MATCH
      | (Const (a,T), Const (b,U))  =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else raise MATCH
      | (Bound i, Bound j)  =>  if  i=j  then  instsp  else raise MATCH
      | (Abs(_,T,t), Abs(_,U,u))  =>
          (*`U', the OBJECT's binder type, not `T': the only consumer of `bv_tys' is
            `fastype_of1 (bv_tys, t)' where `t' is an object subterm, and the eta
            expansion clause below pushes the object's type too.*)
          mtch (U::bv_tys) (lev+1) (typ_match thy (T,U) tyinsts, insts) (t,u)
      | (f$t, g$u) => mtch bv_tys lev (mtch bv_tys lev instsp (f,g)) (t, u)
      | (t, Abs(_,T,u))  => mtch (T::bv_tys) (lev+1) instsp ((incr t)$(Bound 0), u)
      | _ => raise MATCH
  in mtch bv_tys 0 env (t,u) end;

(* Matching of higher-order patterns *)

(*fixed_bounds: bound variables regarded as normal free variables*)
fun match thy fixed_bounds bvs (po as (pat,obj)) envir =
let
  val len_initial = length bvs
  fun match_bind(itms,binders,ixn,T,is,t) =
    let val len = length binders
        val diff = len - len_initial
        val js = escaping fixed_bounds diff t
    in if null is
       then if null js then Vartab.update_new (ixn, (T, Term.incr_boundvars (~diff) t)) itms
            else raise MATCH
       else if subset (op =) (js, is)
            then let val n = length is
                     (*`downto0' holds only when `is' is exactly the `diff' entered
                       binders, and then `n = diff' makes both branches below the
                       identity, so `t' may be kept as it stands.*)
                     val t' = if downto0(is, diff - 1) then t
                              else mapbnd (fn j =>
                                     (*membership, not `j < diff': `is' may hold an
                                       index of a contextual bound variable, and
                                       `mkabs' does bind that one too*)
                                     if member (op =) is j then idx is j
                                     else j - diff + n) t
                 in Vartab.update_new (ixn, (T, mkabs (binders, is, t'))) itms end
            else raise MATCH
    end
  (* Pre: pat and obj have same type *)
  fun mtch binders (pat,obj) (env as (iTs,itms)) =
    case pat of
      Abs(ns,Ts,ts) =>
        (case obj of
           Abs(nt,Tt,tt) => mtch ((nt,Tt)::binders) (ts,tt) env
         | _ => let val Tt = Envir.subst_type iTs Ts
                in mtch((ns,Tt)::binders) (ts,(incr obj)$Bound(0)) env end)
    | _ => (case obj of
              Abs(nt,Tt,tt) =>
                mtch((nt,Tt)::binders) ((incr pat)$Bound(0),tt) env
            | _ => cases(binders,env,pat,obj))

  and cases(binders,env as (iTs,itms),pat,obj) =
    let val (ph,pargs) = strip_comb pat
        fun rigrig1(iTs,oargs) = fold (mtch binders) (pargs~~oargs) (iTs,itms)
          handle ListPair.UnequalLengths => raise MATCH
        fun rigrig2((a:string,Ta),(b,Tb),oargs) =
              if a <> b then raise MATCH
              else rigrig1(typ_match thy (Ta,Tb) iTs, oargs)
    in case ph of
         Var(ixn,T) =>
           let val is = ints_of pargs
           in case Envir.lookup1 itms (ixn, T) of
                NONE => (iTs,match_bind(itms,binders,ixn,T,is,obj))
              | SOME u => if Envir.aeconv (obj, red (length binders - len_initial) u is []) then env
                          else raise MATCH
           end
       | _ =>
           let val (oh,oargs) = strip_comb obj
           in case (ph,oh) of
                (Const c,Const d) => rigrig2(c,d,oargs)
              | (Free f,Free g)   => rigrig2(f,g,oargs)
              | (Bound i,Bound j) => if i<>j then raise MATCH
                                     else rigrig1(iTs,oargs)
              | (Abs _, _)        => raise Pattern
              | (_, Abs _)        => raise Pattern
              | _                 => raise MATCH
           end
    end;

  val bvtys = map snd bvs
  val pT = fastype_of pat
  and oT = fastype_of1 (bvtys, obj)
  val envir' = apfst (typ_match thy (pT, oT)) envir;
in mtch bvs po envir' handle Pattern => first_order_match thy fixed_bounds bvtys po envir' end;

fun matches thy fixed_bounds bv_typs po =
  (match thy fixed_bounds bv_typs po (Vartab.empty, Vartab.empty); true) handle MATCH => false;


fun mk_spattern raw =
  map_aterms (fn Var ((s,i),T) =>
                    if i < 0
                    then raise TERM ("Pattern_Translation: the pattern contains negative schematic index", [raw])
                    else Var ((s, if String.isPrefix "var_" s orelse s = "var" then ~i - 1 else i),T)
               | X => X) raw

val chk_trick = Vartab.forall (fn ((_,i),(_,tm)) => i >= 0 orelse is_Var (Term.head_of (Envir.beta_eta_contract tm)))

fun smatch thy fixed_bounds bvs pat_obj env =
  let val (tys,tms) = match thy fixed_bounds bvs pat_obj env
   in if chk_trick tms then (tys,tms)
      else raise MATCH
  end

fun does_smatch thy fixed_bounds bv_typs pat_obj =
      (smatch thy fixed_bounds bv_typs pat_obj (Vartab.empty, Vartab.empty) ; true)
      handle MATCH => false


fun strip_typs tm =
  let val i = Unsynchronized.ref (maxidx_of_term tm)
      fun var () = (i := !i + 1; TVar (("_",!i),[]))
      fun strip (Const(N,_)) = Const (N, var())
        | strip (Free(N,_)) = Free (N, var())
        | strip (Var(N,_)) = Var (N, var())
        | strip (A $ B) = strip A $ strip B
        | strip (Abs (N,T,X)) = Abs (N,T, strip X)
        | strip X = X
   in strip tm
  end



(* substitution that respects the numbering above *)

(*`Envir.subst_term2' (envir.ML:358-373) with a depth counter threaded through the
  `Abs' arc; the counter and the `incr_boundvars lev' are `prf_subst' in
  Pure/proofterm.ML:1429-1442, which does the same for proof terms.  Upstream needs
  neither because a binding it stores is always closed.*)
fun subst_term_same (tyenv, tenv) =
  let
    val substT = Envir.subst_type_same tyenv;
    fun subst _ (Const (a, T)) = Const (a, substT T)
      | subst _ (Free (a, T)) = Free (a, substT T)
      | subst lev (Var (xi, T)) =
          (case Envir.lookup1 tenv (xi, T) of
            SOME u => Term.incr_boundvars lev u
          | NONE => Var (xi, substT T))
      | subst _ (Bound _) = raise Same.SAME
      | subst lev (Abs (a, T, t)) =
          (Abs (a, substT T, Same.commit (subst (lev + 1)) t)
            handle Same.SAME => Abs (a, T, subst (lev + 1) t))
      | subst lev (t $ u) =
          (subst lev t $ Same.commit (subst lev) u
            handle Same.SAME => t $ subst lev u);
  in subst 0 end;

fun subst_term envs = Same.commit (subst_term_same envs);

end