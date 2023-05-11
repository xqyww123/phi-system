(* FILE: Phi_Logic_Programming_Reasoner/library/pattern.ML
   AUTHOR: Tobias Nipkow, Christine Heinzelmann, and Stefan Berghofer, TU Muenchen
   Modified by: Qiyuan Xu

   To support matching loose bounds in the target object.
   Regard them as fixed variables.
*)

signature PLPR_PATTERN = sig

val match: theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
val first_order_match: theory -> term * term
    -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

val matches: theory -> term * term -> bool

end

structure PLPR_Pattern = struct
open Pattern

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

fun red (Abs(_,_,s)) (i::is) js = red s is (i::js)
  | red t            []      [] = t
  | red t            is      jn = app (mapbnd (fn k => nth jn k handle Subscript => k) t,is);


val incr = mapbnd (fn i => i+1);

fun typ_match thy TU tyenv = Sign.typ_match thy TU tyenv
  handle Type.TYPE_MATCH => raise MATCH;

(* First Order Match *)
(*Improved from the system first_order_match, by allowing loose bounds in the object term,
    and regarding them as fixed free variables.*)
fun first_order_match thy (t,u) env =
  let
    val bs = Inttab.make_set (loose_bnos u)
    fun mtch lev (instsp as (tyinsts,insts)) = fn
        (Var(ixn,T), t)  =>
          if forall (Inttab.defined bs) (loose_bnos t)
          then (case Envir.lookup1 insts (ixn, T) of
                  NONE => (typ_match thy (T, fastype_of t) tyinsts,
                           Vartab.update_new (ixn, (T, t)) insts)
                | SOME u => if Envir.aeconv (t, u) then instsp else raise MATCH)
          else raise MATCH
      | (Free (a,T), Free (b,U)) =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else raise MATCH
      | (Const (a,T), Const (b,U))  =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else raise MATCH
      | (Bound i, Bound j)  =>  if  i=j  then  instsp  else raise MATCH
      | (Abs(_,T,t), Abs(_,U,u))  =>
          mtch lev (typ_match thy (T,U) tyinsts, insts) (t,u)
      | (f$t, g$u) => mtch lev (mtch lev instsp (f,g)) (t, u)
      | (t, Abs(_,_,u))  => mtch (lev+1) instsp ((incr t)$(Bound 0), u)
      | _ => raise MATCH
  in mtch 0 env (t,u) end;

(* Matching of higher-order patterns *)

fun match thy (po as (pat,obj)) envir =
let
  val bs = Inttab.make_set (loose_bnos obj)
  fun match_bind(itms,binders,ixn,T,is,t) =
    let val len = length binders
        val js = loose_bnos t
              |> filter (fn i => not (Inttab.defined bs (i - len)))
    in if null is
       then if null js then Vartab.update_new (ixn, (T, t)) itms else raise MATCH
       else if subset (op =) (js, is)
            then let val t' = if downto0(is, len - 1) then t
                              else mapbnd (idx is) t
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
              | SOME u => if Envir.aeconv (obj, red u is []) then env
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

  val pT = fastype_of pat
  and oT = fastype_of obj
  val envir' = apfst (typ_match thy (pT, oT)) envir;
in mtch [] po envir' handle Pattern => first_order_match thy po envir' end;

fun matches thy po =
  (match thy po (Vartab.empty, Vartab.empty); true) handle MATCH => false;


end