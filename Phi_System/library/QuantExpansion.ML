signature QUANT_EXPANSION = sig
  val forall_expansion : string list -> Proof.context -> thm
  val pure_All_expansion : string list -> Proof.context -> thm
  val exists_expansion : string list -> Proof.context -> thm
  val ExNu_expansion : string list -> Proof.context -> thm
  val aux_expansions : Proof.context -> thm list
  (* expand all schematic variabls of type `?'x named 'names` *)
  val schematic_var_expansion : Proof.context -> thm -> thm
  val mk_cases_named :  string list -> term -> term

  val simproc_of : (string list -> Proof.context -> thm) -> Proof.context -> cterm -> thm option
  (* convert a multi-variable lambda expression (\<lambda>x y z. F x y z) to a single-variable lambda
  expression of a tuple, (\<lambda>t. F (fst t) (fst (snd t)) (snd (snd t))).
  In addition, the names of x y z are recorded in the type of t
    by using \<^typ>\<open>T <named> 'x \<times> 'y \<times> 'z\<close>*)
  val aggregate_variables_lambda : term -> string list (*names*) * term
  val aggregate_variables_quantification : term -> string list (*names*) * term
end

structure QuantExpansion : QUANT_EXPANSION = struct
open NuHelp PhiSyntax

fun mk_cases_named names tm = Const (@{const_name case_named},
      (dummyT --> dummyT) --> Type (@{type_name named}, [dummyT, mk_name_tylabels names]) --> dummyT) $ tm

fun const_dest_named T names =
  Const (@{const_name case_named}, (T --> T) --> PhiSyntax.mk_namedT T names --> T)
    $ Const (@{const_name id}, T --> T)

fun mk_cases_named_fullty names tm =
  case fastype_of tm of Type ("fun", [dom,rng]) =>
      Const (@{const_name case_named},
        (dom --> rng) --> Type (@{type_name named}, [dom, mk_name_tylabels names]) --> rng) $ tm
    | _ => raise TERM ("mk_cases_named_fullty: not a function type", [tm])


fun abs_arg_ty names =
  mk_binop_ty @{type_name named} 
    (HOLogic.mk_tupleT (List.tabulate (length names, (fn i => TVar (("'x",i),["HOL.type"])))),
    mk_name_tylabels names)

fun mk_the_binder binder P_term names =
  let
    val mk_binder = if binder = "" then I else (fn x => (Const (binder, dummyT) $ x))
    val arity = length names
  in
    (fold_rev (fn (name,ty) => fn tm => mk_binder (Abs (name, ty, tm)))
      names
      (P_term $ (Const (@{const_name tag}, dummyT) $
                  list_mk_binop_r @{const_name Pair}
                    (List.tabulate (arity, (fn i => Bound (arity - i - 1)))))))
  end

fun mk_the_cases P_term names =
  let
    fun mk_case (tm as (Abs (_,tya,Abs (_,tyb,body))))
          = Const (@{const_name case_prod},
                    (tya --> tyb --> fastype_of body) -->
                        HOLogic.mk_prodT (tya,tyb) --> fastype_of body) $ tm
      | mk_case (tm as (Abs (_, tya,
              Const (@{const_name case_prod},
                Type ("fun", [_, Type("fun", [tyb,ty_body])])) $ _)))
          = Const (@{const_name case_prod},
                    (tya --> tyb --> ty_body) -->
                        HOLogic.mk_prodT (tya,tyb) --> ty_body) $ tm
      | mk_case tm = tm
    val arity = length names
  in
    mk_cases_named_fullty (map fst names)
      (fold_rev (fn (name,ty) => fn tm => mk_case (Abs (name, ty, tm)))
        names
        (ntimes arity (fn i => fn x => x $ Bound (arity - 1 - i)) P_term))
  end

fun gen_general_expansion const thms ty names ctxt =
  let
    val ([P],ctxt) = Variable.add_fixes ["\<P>"] ctxt
    val P_term = Var((P,0), abs_arg_ty names --> the_default dummyT ty)
    val quant = Const (@{const_name Pure.eq}, dummyT)
      $ (Const (const, dummyT) $ P_term)
      $ mk_the_binder const P_term (map (rpair dummyT) names)
    val ctxt = (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) addsimps thms
    val quant = Syntax.check_prop ctxt quant |> Thm.cterm_of ctxt
    val quant = case Goal.init quant |> SINGLE (HEADGOAL (Simplifier.simp_tac ctxt))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve quantification-expansion", [quant])
  in quant end

val forall_expansion =
  gen_general_expansion @{const_name All} @{thms split_paired_All named_forall} (SOME \<^typ>\<open>bool\<close>)
val exists_expansion =
  gen_general_expansion @{const_name Ex} @{thms split_paired_Ex named_exists} (SOME \<^typ>\<open>bool\<close>)
val pure_All_expansion =
  gen_general_expansion @{const_name Pure.all} @{thms split_paired_all named_All} (SOME \<^typ>\<open>prop\<close>)
fun ExNu_expansion names ctxt =
  gen_general_expansion @{const_name ExSet} @{thms ExSet_pair named_ExSet}
    (SOME \<^typ>\<open>assn\<close>) names ctxt

fun aux_expansions ctxt = Named_Theorems.get ctxt @{named_theorems named_expansion}

fun schematic_var_expansion ctxt th =
  let
    fun uncurry_ty (Type ("fun", [Type (@{type_name named}, [domains, _]), rng])) =
          fold_rev (fn a => fn ty => a --> ty) (HOLogic.strip_tupleT domains) rng
    val insts = Term.add_vars (Thm.prop_of th) []
                  |> map_filter (try (` (dest_named o domain_type o snd))
                        #> Option.map (fn (names, tm) =>
                            (tm,
                             mk_the_cases (Var (tm |> apsnd uncurry_ty)) names
                                |> Thm.cterm_of ctxt)
                    ))
  in
    Thm.instantiate (TVars.empty, Vars.make insts) th
  end

fun simproc_of expn ctxt cterm =
  let
    val Const _ $ abst = Thm.term_of cterm
    val Type ("fun", [Type (@{type_name named}, [_, names]), _])  = fastype_of abst
    val names = dest_name_tylabels names
  in
    SOME (expn names ctxt)
  end

(*
val cty_a = TVar (("'a",1),["HOL.type"]) |> Thm.ctyp_of @{context}
fun spec_retaining_name th =
  let
    val Abs (name,_,_)
      = Thm.concl_of th |> HOLogic.dest_Trueprop |> dest_monop @{const_name All}
    val spec =
      Thm.instantiate
        (TVars.empty, Vars.make [((("x",1), TVar (("'a",1),["HOL.type"])), Thm.var((name,0), cty_a))])
        (Thm.incr_indexes 1 @{thm spec})
  in
    th RS spec
  end *)


val gname = fst o dest_Const

fun strip_abs_names (Abs (name,_,body)) = name :: strip_abs_names body
  | strip_abs_names _ = []
fun strip_quant_names H (H' $ Abs (name,_,X)) =
      if H = gname H' then name :: strip_quant_names H X else []
  | strip_quant_names _ _ = []

fun strip_abs_tys (Abs (_,ty,body)) = ty :: strip_abs_tys body
  | strip_abs_tys _ = []
fun strip_quant_tys H (H' $ Abs (_,ty,body)) =
      if H = gname H' then ty :: strip_quant_tys H body else []
  | strip_quant_tys _ _ = []

fun lambda_body (Abs (_,_,X)) = lambda_body X
  | lambda_body X = X
fun quant_body H (H' $ (X' as Abs (_,_,X))) =
      if H = gname H' then quant_body H X else X'
  | quant_body _ X = X

fun mk_tupleT [] = []
  | mk_tupleT (T::Ts) =
      case mk_tupleT Ts of [] => [T]
                         | (Ts1'::Tsr') => HOLogic.mk_prodT (T,Ts1') :: Ts1' :: Tsr'

fun nth_project [_] 0 term = term
  | nth_project (ty::_::_) 0 term
      = Const (\<^const_name>\<open>eoq__fst\<close>, ty --> fst (HOLogic.dest_prodT ty)) $ term
  | nth_project (ty::tys::tyss) i term =
      nth_project (tys::tyss) (i-1) (Const (\<^const_name>\<open>eoq__snd\<close>, ty --> tys) $ term) 
  | nth_project [] _ _ = error "BUG:gp8743bpfs"

fun aggregate_variables_raw names tys body =
  let
    val Ts = mk_tupleT tys
    val T = hd Ts
    val N = length names
    val C = const_dest_named T names
    fun tr M (Bound i) = if i < M then Bound i
                         else (nth_project Ts (N - 1 - i + M) (C $ Bound M))
      | tr M (X $ Y) = (tr M X $ tr M Y)
      | tr M (Abs (n,t,X)) = Abs (n,t, tr (M+1) X)
      | tr _ X = X
  in (names, Abs ("", PhiSyntax.mk_namedT T names, tr 0 body))
  end

fun aggregate_variables_lambda term =
      aggregate_variables_raw (strip_abs_names term) (strip_abs_tys term) (lambda_body term)

fun aggregate_variables_quantification term =
  let
    val Const (H, Type("fun", [Type("fun", [_,T1]),T2])) $ _ = term
    val (N,X) = aggregate_variables_raw (strip_quant_names H term)
                                    (strip_quant_tys H term)
                                    (quant_body H term)
    val (Abs (_,T0,_)) = X
  in
    (N, Const (H, (T0 --> T1) --> T2) $ X)
  end


end
