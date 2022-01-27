structure MY_Pattern =
struct

exception Unif;
exception Pattern;

val unify_trace_failure = Config.declare_bool ("unify_trace_failure", \<^here>) (K false);

fun string_of_term ctxt env binders t =
  Syntax.string_of_term ctxt (Envir.norm_term env (subst_bounds (map Free binders, t)));

fun bname binders i = fst (nth binders i);
fun bnames binders is = space_implode " " (map (bname binders) is);

fun typ_clash context (tye,T,U) =
  if Config.get_generic context unify_trace_failure then
    let
      val ctxt = Context.proof_of context;
      val t = Syntax.string_of_typ ctxt (Envir.norm_type tye T);
      val u = Syntax.string_of_typ ctxt (Envir.norm_type tye U);
    in tracing ("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ();

fun clash context a b =
  if Config.get_generic context unify_trace_failure
  then tracing ("Clash: " ^ a ^ " =/= " ^ b) else ();

fun boundVar binders i =
  "bound variable " ^ bname binders i ^ " (depth " ^ string_of_int i ^ ")";

fun clashBB context binders i j =
  if Config.get_generic context unify_trace_failure
  then clash context (boundVar binders i) (boundVar binders j) else ();

fun clashB context binders i s =
  if Config.get_generic context unify_trace_failure
  then clash context (boundVar binders i) s else ();

fun proj_fail context (env,binders,F,_,is,t) =
  if Config.get_generic context unify_trace_failure then
    let
      val ctxt = Context.proof_of context
      val f = Term.string_of_vname F
      val xs = bnames binders is
      val u = string_of_term ctxt env binders t
      val ys = bnames binders (subtract (op =) is (loose_bnos t))
    in
      tracing ("Cannot unify variable " ^ f ^
        " (depending on bound variables " ^ xs ^ ")\nwith term " ^ u ^
        "\nTerm contains additional bound variable(s) " ^ ys)
    end
  else ();

fun ocheck_fail context (F,t,binders,env) =
  if Config.get_generic context unify_trace_failure then
    let
      val ctxt = Context.proof_of context
      val f = Term.string_of_vname F
      val u = string_of_term ctxt env binders t
    in tracing ("Variable " ^ f ^ " occurs in term\n" ^ u ^ "\nCannot unify!\n") end
  else ();

fun occurs(F,t,env) =
    let fun occ(Var (G, T))   = (case Envir.lookup env (G, T) of
                                 SOME(t) => occ t
                               | NONE    => F=G)
          | occ(t1$t2)      = occ t1 orelse occ t2
          | occ(Abs(_,_,t)) = occ t
          | occ _           = false
    in occ t end;


fun mapbnd f =
    let fun mpb d (Bound(i))     = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs(s,T,t))   = Abs(s,T,mpb(d+1) t)
          | mpb d ((u1 $ u2))    = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end;

fun idx [] j     = raise Unif
  | idx(i::is) j = if (i:int) =j then length is else idx is j;

fun mkabs (binders,is,t)  =
    let fun mk(i::is) = let val (x,T) = nth binders i
                        in Abs(x,T,mk is) end
          | mk []     = t
    in mk is end;

val incr = mapbnd (fn i => i+1);

fun ints_of []             = []
  | ints_of (Bound i ::bs) =
      let val is = ints_of bs
      in if member (op =) is i then raise Pattern else i::is end
  | ints_of _              = raise Pattern;

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts);


fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

fun red (Abs(_,_,s)) (i::is) js = red s is (i::js)
  | red t            []      [] = t
  | red t            is      jn = app (mapbnd (nth jn) t,is);


(* split_type ([T1,....,Tn]---> T,n,[]) = ([Tn,...,T1],T) *)
fun split_type (T,0,Ts)                    = (Ts,T)
  | split_type (Type ("fun",[T1,T2]),n,Ts) = split_type (T2,n-1,T1::Ts)
  | split_type _                           = raise Fail "split_type";

fun type_of_G env (T, n, is) =
  let
    val tyenv = Envir.type_env env;
    val (Ts, U) = split_type (Envir.norm_type tyenv T, n, []);
  in map (nth Ts) is ---> U end;

fun mk_hnf (binders,is,G,js) = mkabs (binders, is, app(G,js));

fun mk_new_hnf(env,binders,is,F as (a,_),T,js) =
  let val (env',G) = Envir.genvar a (env,type_of_G env (T,length is,js))
  in Envir.update ((F, T), mk_hnf (binders, is, G, js)) env' end;


(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;

(*mk_proj_list(is) = [ |is| - k | 1 <= k <= |is| and is[k] >= 0 ]*)
fun mk_proj_list is =
    let fun mk(i::is,j) = if is_some i then j :: mk(is,j-1) else mk(is,j-1)
          | mk([],_)    = []
    in mk(is,length is - 1) end;

fun proj(s,env,binders,is) =
    let fun trans d i = if i<d then i else (idx is (i-d))+d;
        fun pr(s,env,d,binders) = (case Envir.head_norm env s of
              Abs(a,T,t) => let val (t',env') = pr(t,env,d+1,((a,T)::binders))
                            in (Abs(a,T,t'),env') end
            | t => (case strip_comb t of
                (c as Const _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(c,ts'),env') end
                 | (f as Free _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(f,ts'),env') end
                 | (Bound(i),ts) =>
                         let val j = trans d i
                             val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(Bound j,ts'),env') end
                 | (Var(F as (a,_),Fty),ts) =>
                      let val js = ints_of' env ts;
                          val js' = map (try (trans d)) js;
                          val ks = mk_proj_list js';
                          val ls = map_filter I js'
                          val Hty = type_of_G env (Fty,length js,ks)
                          val (env',H) = Envir.genvar a (env,Hty)
                          val env'' =
                            Envir.update ((F, Fty), mk_hnf (binders, js, H, ks)) env'
                      in (app(H,ls),env'') end
                 | _  => raise Pattern))
        and prs(s::ss,env,d,binders) =
              let val (s',env1) = pr(s,env,d,binders)
                  val (ss',env2) = prs(ss,env1,d,binders)
              in (s'::ss',env2) end
          | prs([],env,_,_) = ([],env)
   in if downto0(is,length binders - 1) then (s,env)
      else pr(s,env,0,binders)
   end;


(* mk_ff_list(is,js) = [ length(is) - k | 1 <= k <= |is| and is[k] = js[k] ] *)
fun mk_ff_list(is,js) =
    let fun mk([],[],_)        = []
          | mk(i::is,j::js, k) = if (i:int) = j then k :: mk(is,js,k-1)
                                        else mk(is,js,k-1)
          | mk _               = raise Fail "mk_ff_list"
    in mk(is,js,length is-1) end;

fun flexflex1(env,binders,F,Fty,is,js) =
  if is=js then env
  else let val ks = mk_ff_list(is,js)
       in mk_new_hnf(env,binders,is,F,Fty,ks) end;

fun flexflex2(env,binders,F,Fty,is,G,Gty,js) =
  let fun ff(F,Fty,is,G as (a,_),Gty,js) =
            if subset (op =) (js, is)
            then let val t= mkabs(binders,is,app(Var(G,Gty),map (idx is) js))
                 in Envir.update ((F, Fty), t) env end
            else let val ks = inter (op =) js is
                     val Hty = type_of_G env (Fty,length is,map (idx is) ks)
                     val (env',H) = Envir.genvar a (env,Hty)
                     fun lam(is) = mkabs(binders,is,app(H,map (idx is) ks));
                 in Envir.update ((G, Gty), lam js) (Envir.update ((F, Fty), lam is) env')
                 end;
  in if Term_Ord.indexname_ord (G,F) = LESS then ff(F,Fty,is,G,Gty,js) else ff(G,Gty,js,F,Fty,is) end

fun unify_types context (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  if T = U then env
  else
    let
      val thy = Context.theory_of context
      val (tyenv', maxidx') = Sign.typ_unify thy (U, T) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end
    handle Type.TUNIFY => (typ_clash context (tyenv, T, U); raise Unif);

fun unif context binders (s,t) env = case (Envir.head_norm env s, Envir.head_norm env t) of
      (Abs(ns,Ts,ts),Abs(nt,Tt,tt)) =>
         let val name = if ns = "" then nt else ns
         in unif context ((name,Ts)::binders) (ts,tt) (unify_types context (Ts, Tt) env) end
    | (Abs(ns,Ts,ts),t) => unif context ((ns,Ts)::binders) (ts,(incr t)$Bound(0)) env
    | (t,Abs(nt,Tt,tt)) => unif context ((nt,Tt)::binders) ((incr t)$Bound(0),tt) env
    | p => cases context (binders,env,p)

and cases context (binders,env,(s,t)) = case (strip_comb s,strip_comb t) of
       ((Var(F,Fty),ss),(Var(G,Gty),ts)) =>
         if F = G then flexflex1(env,binders,F,Fty,ints_of' env ss,ints_of' env ts)
                  else flexflex2(env,binders,F,Fty,ints_of' env ss,G,Gty,ints_of' env ts)
      | ((Var(F,Fty),ss),_)           => flexrigid context (env,binders,F,Fty,ints_of' env ss,t)
      | (_,(Var(F,Fty),ts))           => flexrigid context (env,binders,F,Fty,ints_of' env ts,s)
      | ((Const c,ss),(Const d,ts))   => rigidrigid context (env,binders,c,d,ss,ts)
      | ((Free(f),ss),(Free(g),ts))   => rigidrigid context (env,binders,f,g,ss,ts)
      | ((Bound(i),ss),(Bound(j),ts)) => rigidrigidB context (env,binders,i,j,ss,ts)
      | ((Abs(_),_),_)                => raise Pattern
      | (_,(Abs(_),_))                => raise Pattern
      | ((Const(c,_),_),(Free(f,_),_)) => (clash context c f; raise Unif)
      | ((Const(c,_),_),(Bound i,_))   => (clashB context binders i c; raise Unif)
      | ((Free(f,_),_),(Const(c,_),_)) => (clash context f c; raise Unif)
      | ((Free(f,_),_),(Bound i,_))    => (clashB context binders i f; raise Unif)
      | ((Bound i,_),(Const(c,_),_))   => (clashB context binders i c; raise Unif)
      | ((Bound i,_),(Free(f,_),_))    => (clashB context binders i f; raise Unif)


and rigidrigid context (env,binders,(a,Ta),(b,Tb),ss,ts) =
      if a<>b then (clash context a b; raise Unif)
      else env |> unify_types context (Ta,Tb) |> fold (unif context binders) (ss~~ts)

and rigidrigidB context (env,binders,i,j,ss,ts) =
     if i <> j then (clashBB context binders i j; raise Unif)
     else fold (unif context binders) (ss~~ts) env

and flexrigid context (params as (env,binders,F,Fty,is,t)) =
      if occurs(F,t,env) then (ocheck_fail context (F,t,binders,env); raise Unif)
      else (let val (u,env') = proj(t,env,binders,is)
            in Envir.update ((F, Fty), mkabs (binders, is, u)) env' end
            handle Unif => (proj_fail context params; raise Unif));

fun unify context = unif context [];



(*** Matching ***)

exception MATCH;

fun typ_match thy TU tyenv = Sign.typ_match thy TU tyenv
  handle Type.TYPE_MATCH => (@{print} "TTTXXXX"; @{print} TU; raise MATCH)

(*First-order matching;
  The pattern and object may have variables in common.
  Instantiation does not affect the object, so matching ?a with ?a+1 works.
  Object is eta-contracted on the fly (by eta-expanding the pattern).
  Precondition: the pattern is already eta-contracted!
  Types are matched on the fly.
  The parameter inAbs is an optimization to avoid calling is_open;
  it has the funny consequence that outside abstractions
  ?x matches terms containing loose Bounds.
*)
fun first_order_match thy =
  let
    fun mtch inAbs (instsp as (tyinsts,insts)) = fn
        (Var(ixn,T), t)  =>
          if inAbs andalso Term.is_open t then (@{print} "TTT6666"; raise MATCH)
          else (case Envir.lookup1 insts (ixn, T) of
                  NONE => (typ_match thy (T, fastype_of t) tyinsts,
                           Vartab.update_new (ixn, (T, t)) insts)
                | SOME u => if Envir.aeconv (t, u) then instsp else (@{print} "TTT5555"; raise MATCH))
      | (Free (a,T), Free (b,U)) =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else (@{print} "TTT4444"; raise MATCH)
      | (Const (a,T), Const (b,U))  =>
          if a=b then (typ_match thy (T,U) tyinsts, insts) else (@{print} "TTT3333"; raise MATCH)
      | (Bound i, Bound j)  =>  if  i=j  then  instsp  else (@{print} "TTT2222"; raise MATCH)
      | (Abs(_,T,t), Abs(_,U,u))  =>
          mtch true (typ_match thy (T,U) tyinsts, insts) (t,u)
      | (f$t, g$u) => mtch inAbs (mtch inAbs instsp (f,g)) (t, u)
      | (t, Abs(_,U,u))  =>  mtch true instsp ((incr t)$(Bound 0), u)
      | _ => (@{print} "TTT111"; raise MATCH)

  in fn tu => fn env => mtch false env tu end;


(* Matching of higher-order patterns *)

fun match_bind(itms,binders,ixn,T,is,t) =
  let val js = loose_bnos t
  in if null is
     then if null js then Vartab.update_new (ixn, (T, t)) itms else (@{print} "GGG2222"; raise MATCH)

     else if subset (op =) (js, is)
          then let val t' = if downto0(is,length binders - 1) then t
                            else mapbnd (idx is) t
               in Vartab.update_new (ixn, (T, mkabs (binders, is, t'))) itms end
          else (@{print} "GGG1111"; raise MATCH)

  end;

fun match thy (po as (pat,obj)) envir =
let
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
          handle ListPair.UnequalLengths => (@{print} "FFF1111"; raise MATCH)
        fun rigrig2((a:string,Ta),(b,Tb),oargs) =
              if a <> b then (@{print} "FFF2222"; raise MATCH)
              else rigrig1(typ_match thy (Ta,Tb) iTs, oargs)
    in case ph of
         Var(ixn,T) =>
           let val is = ints_of pargs
           in case Envir.lookup1 itms (ixn, T) of
                NONE => (iTs,match_bind(itms,binders,ixn,T,is,obj))
              | SOME u => if Envir.aeconv (obj, red u is []) then env
                          else (@{print} "FFF3333"; @{print} (obj, red u is []); raise MATCH)
           end
       | _ =>
           let val (oh,oargs) = strip_comb obj
           in case (ph,oh) of
                (Const c,Const d) => rigrig2(c,d,oargs)
              | (Free f,Free g)   => rigrig2(f,g,oargs)
              | (Bound i,Bound j) => if i<>j then (@{print} "FFF4444"; raise MATCH)
                                     else rigrig1(iTs,oargs)
              | (Abs _, _)        => (@{print} "FFF555"; raise MATCH)
              | (_, Abs _)        => (@{print} "FFF666"; raise MATCH)
              | _                 => (@{print} "FFF777"; raise MATCH)
           end
    end;

  val pT = fastype_of pat
  and oT = fastype_of obj
  val envir' = apfst (typ_match thy (pT, oT)) envir;
in mtch [] po envir' handle Pattern => first_order_match thy po envir' end;


fun matches thy po =
  (match thy po (Vartab.empty, Vartab.empty); true) handle MATCH => false;

fun pattern (Abs (_, _, t)) = pattern t
  | pattern t =
      let val (head, args) = strip_comb t in
        if is_Var head then
          forall is_Bound args andalso not (has_duplicates (op aconv) args)
        else forall pattern args
      end;
end;


signature NU_REASONER = sig
  type cost = int
  type 'a generic_reasoner = {name: term, pattern: term list, tactic: 'a}
  type reasoner = (Proof.context -> tactic) generic_reasoner
  val reasoner_eq : ('a generic_reasoner * 'a generic_reasoner) -> bool

  (* auto level: 2 - fully auto, 1 - paritally auto, 0 - fully manual *)
  val auto_level : int Config.T
  val reduce_auto_level : int -> Proof.context -> Proof.context

  exception Success of thm
  val add : cost * reasoner -> Context.generic -> Context.generic
  val del : reasoner -> Context.generic -> Context.generic
  val reasoners : Proof.context -> (cost * reasoner) list
  val reasoner_net : Proof.context -> reasoner Cost_Net.T

  val add_intro_rule : term option -> cost * thm -> Context.generic -> Context.generic
  val add_intro_rules : (thm list * cost * term option) list -> Proof.context -> Proof.context
  val del_intro_rule : thm -> Context.generic -> Context.generic
  val attr_add_intro : int * term option -> attribute
  val attr_del_intro : attribute

  val add_elim_rule : cost * thm -> Context.generic -> Context.generic
  val add_elim_rules : (thm list * cost) list -> Proof.context -> Proof.context
  val del_elim_rule : thm -> Context.generic -> Context.generic
  val attr_add_elim : int -> attribute
  val attr_del_elim : attribute

  val reason' : Proof.context -> reasoner Cost_Net.T -> thm -> thm option
  val reason : Proof.context -> thm -> thm option
  val reason_s : Proof.context -> (cost * thm Seq.seq) list -> thm Seq.seq (* Note it only returns one
    theorem in the returned sequence, that the one succeeded first or of least cost. *)
  val reason_tac : Proof.context -> tactic

  val setup_cmd : ((string (*name term*) * cost) * string list (*pattern terms*)) * Input.source (* tactic source*)
        -> local_theory -> local_theory
end

structure Nu_Reasoner : NU_REASONER = struct
open NuHelp

type cost = int
type 'a generic_reasoner = {name: term, pattern: term list, tactic: 'a}
type reasoner = (Proof.context -> tactic) generic_reasoner

val auto_level = Config.declare_int ("\<nu>auto_level", @{here}) (K 2)
fun reduce_auto_level i = Config.map auto_level (fn j => Int.min (i,j))


exception Success  of thm
exception Success' of cost * thm

structure States = Heap (
  type elem = (cost * thm Seq.seq);
  fun ord ((cost,_),(cost',_)) = int_ord (cost,cost')
)


fun debug prompt ctx (c,(r : reasoner as {name,...})) =
  (tracing (prompt ^ "  :  " ^ Syntax.string_of_term ctx name ^ "     " ^ string_of_int c); (c,r))
fun dbg2 ctx term = (tracing (Syntax.string_of_term ctx term); term)

fun call_tactics ctx tactics th =
  case Thm.prems_of th
    of prem :: _ =>
        (* (Logic.strip_assums_concl prem :: Logic.strip_assums_hyp prem)
           |> maps (fn term =>
               Cost_Net.retrieve tactics term
                 |> map (debug "x22" ctx)
                 |> map (apsnd (fn (r : reasoner) => #tactic r ctx th))) *)

        let
          val tacs = (Logic.strip_assums_concl prem :: Logic.strip_assums_hyp prem)
                          |> maps (fn term =>
                              Cost_Net.retrieve tactics term
                                |> map (debug "x22" ctx)
                                |> map (apsnd (fn (r : reasoner) =>
                                    Seq.make (fn () => Seq.pull (#tactic r ctx th)))))
                          |> sort (int_ord o apply2 fst)
                          (* |> map_filter (fn (c,seq) =>
                              Option.map (fn (t,s) => (c,Seq.cons t s))
                              (Seq.pull seq) *)
        in
          case get_first (fn (c,seq) =>
              if c <= ~1000 then
                Option.map (fn (t,_) => (c, Seq.single t)) (Seq.pull seq)
              else NONE
            ) tacs
            of SOME seq => [seq]
             | NONE => tacs
        end
     | [] => raise Success th

fun gen_reason ctx iter tactics (best_cost,best_stat) states =
  if States.is_empty states then (best_cost,best_stat) else
  let
    val _ = if iter > 100 then raise Fail "Nu_Reasoner: Too Much Tries" else ()
    val ((cost,seq),states) = States.min_elem states
  in
    case Seq.pull seq
      of SOME (th,seq') =>
          (let
            val _ = @{print} (cost, th)
            val (best_cost,best_stat) =
              if cost < best_cost then (cost,th)
              else (best_cost,best_stat)
            val states = states
                  |> fold (fn (c,seq'') => States.insert (cost+c, seq''))
                        (call_tactics ctx tactics th)
                  |> States.insert (cost, seq')
                handle Success ret => raise Success' (cost, ret)
          in
            gen_reason ctx (iter+1) tactics (best_cost,best_stat) states
          end)
       | NONE => gen_reason ctx iter tactics (best_cost,best_stat) states
  end

fun gen_reason' ctx iter tactics best states =
  (case gen_reason ctx iter tactics best states of (cost,ret) =>
    if cost <= 0 then SOME ret else NONE)
  handle Success' (cost,ret) => SOME ret

fun reason' ctx tactics thm =
  gen_reason' ctx 0 tactics (0,thm) (States.insert (0, Seq.single thm) States.empty)
fun reason'_s ctx tactics seqs = Seq.make (fn () =>
      gen_reason' ctx 0 tactics (100000000,Drule.dummy_thm)
        (fold States.insert seqs States.empty)
      |> Option.map (rpair Seq.empty)
    )

fun reasoner_eq ({name,pattern,...}, {name=name',pattern=pattern',...}) =
  (name = name' andalso pattern = pattern')

(* Contextual Data *)
structure Tactics = Generic_Data (
  type T = reasoner Cost_Net.T;
  val empty : T = Cost_Net.init reasoner_eq #pattern;
  val extend = I;
  val merge : T * T -> T = Cost_Net.merge
)

fun reasoners ctx = Cost_Net.content (Tactics.get (Context.Proof ctx))
fun reasoner_net ctx = Tactics.get (Context.Proof ctx)
fun add cost_reasoner = Tactics.map (Cost_Net.update cost_reasoner);
fun del reasoner = Tactics.map (Cost_Net.remove reasoner);
fun reason ctx = reason' ctx (Tactics.get (Context.Proof ctx))
fun reason_s ctx = reason'_s ctx (Tactics.get (Context.Proof ctx))
fun reason_tac ctx th = Seq.make (fn () =>
    reason ctx th |> Option.map (rpair Seq.empty)
  )

fun setup_cmd (((name,cost),patterns),tactic_src) lthy =
  let
    val patterns = if null patterns then [name] else patterns
    val name = Syntax.read_term lthy name
    val patterns = Syntax.read_props lthy patterns |> map free_to_var
  in
    lthy |> Context.proof_map (
      ML_Context.expression (Input.pos_of tactic_src)
        (ML_Lex.read
          ("Theory.local_setup (Local_Theory.background_theory (Context.theory_map (Nu_Reasoner.add (" ^
          ML_Syntax.print_int cost ^ ", {name=(" ^
          ML_Syntax.print_term name ^ "), pattern=(" ^
          ML_Syntax.print_list ML_Syntax.print_term patterns
          ^ "), tactic=(let in ") @
          ML_Lex.read_source tactic_src @
          ML_Lex.read (" end):(Proof.context -> tactic)}) )))"))
    )
  end

val _ =
  Outer_Syntax.local_theory @{command_keyword \<nu>reasoner} "define \<nu>reasoner"
    (Parse.term -- (Parse.int >> ~) --| Parse.$$$ "(" -- Parse.enum "|" Parse.term --| Parse.$$$ ")"
        --| @{keyword =} -- Parse.ML_source
      >> setup_cmd)

fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty)))


fun chk_pattern thy pat tac s =
  let
    val conc = Logic.concl_of_goal (Thm.prop_of s) 1
    (* val _ = debug_term_global thy "UUU " pat
    val _ = debug_term_global thy "TTT " conc *)
  in
    if Pattern.matches thy (pat, conc) (* |> @{print} *)
    then tac s else Seq.empty
  end

fun mk_pattern rule NONE = Thm.concl_of rule
  | mk_pattern rule (SOME pat) = NuHelp.mk_Trueprop pat

fun intro_reasoner guard_pattern rule =
  {name = @{term \<nu>Intro_Rule} $ Thm.prop_of rule,
   pattern = [Thm.concl_of rule],
   tactic = (fn ctxt =>
      chk_pattern (Proof_Context.theory_of ctxt)
        (mk_pattern rule guard_pattern)
        (HEADGOAL (Tactic.resolve_tac ctxt [rule]))
    )
  }
fun elim_reasoner rule =
  {name = @{term \<nu>Elim_Rule} $ Thm.prop_of rule,
   pattern = [Thm.major_prem_of rule],
   tactic = (fn ctxt => HEADGOAL (Tactic.eresolve_tac ctxt [rule]))}

fun add_intro_rule guard_pattern (cost, rule) =
  add (cost, intro_reasoner guard_pattern rule)
fun add_intro_rules rules =
  fold (fn (rules,cost,guard) =>
    fold (Context.proof_map o add_intro_rule guard o pair cost) rules) rules

fun del_intro_rule rule = del (intro_reasoner NONE rule)
fun attr_add_intro (cost, guard) =
  Thm.declaration_attribute (add_intro_rule guard o pair cost)
val attr_del_intro = Thm.declaration_attribute del_intro_rule

fun add_elim_rule (cost, rule) = add (cost, elim_reasoner rule)
fun add_elim_rules rules =
  fold (fn (rules,cost) => fold (Context.proof_map o add_elim_rule o pair cost) rules) rules
fun del_elim_rule rule = del (elim_reasoner rule)
fun attr_add_elim cost = Thm.declaration_attribute (add_elim_rule o pair cost)
val attr_del_elim = Thm.declaration_attribute del_elim_rule

end
