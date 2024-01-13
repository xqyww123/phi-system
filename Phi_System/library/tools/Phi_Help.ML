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


  (* abstract `free variables` into a lambda abstraction of a tuple of variables named `names`,
     viz. abstracts `Term` to `\<lambda>(v1,v2,v3). Term`.*)
  val tuple_abs : (string (*name*) * (string * typ) (*free variable*)) list -> term -> term

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

  val reason_tracing_inst : Proof.context -> (thm -> thm option)
                         -> term -> ((ctyp TVars.table * cterm Vars.table) * thm) option

  val reason_tracing_tyinst : Proof.context -> (thm -> thm option)
                           -> term -> (ctyp TVars.table * thm) option

  val fold_aterms : (PLPR_Pattern.bvs -> term -> 'a -> 'a) -> PLPR_Pattern.bvs -> term -> 'a -> 'a

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
  This version improves it, by supporting loose bound variables occurring in both redex and residue*)
fun abstract_over (v, body) =
  let
    fun abs lev tm =
      if aconv_bound_diff lev (tm, v) then Bound lev
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


fun fold_aterms F bvs (f $ x) = fold_aterms F bvs f #> fold_aterms F bvs x
  | fold_aterms F bvs (Abs (N, Ty, X)) = fold_aterms F ((N,Ty)::bvs) X
  | fold_aterms F bvs x = F bvs x



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

signature CONTEXT = sig
include CONTEXT

val full_name : generic -> binding -> string

end

signature GENERIC_THEORY = sig

val full_name : generic_theory -> binding -> string

end

structure Context : CONTEXT = struct

val full_name = Context.cases Sign.full_name Proof_Context.full_name

open Context

end

structure Generic_Theory : GENERIC_THEORY = struct

val full_name = Context.cases Sign.full_name Local_Theory.full_name

end

