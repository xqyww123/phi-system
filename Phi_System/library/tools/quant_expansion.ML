(* FILE: library/tools/quant_expansion.ML
   AUTHOR: Qiyuan Xu

   Expand compact quantification whose quantifier is a tuple tagged names of each projection
   using named tag type.
*)

signature QUANT_EXPANSION = sig
  val mk_cases_named : string list -> term -> term
  val simproc_of : (typ -> string list -> Proof.context -> conv)
                -> Proof.context -> cterm -> thm option

  (*Expand name-tagged quantification like
      `\<forall>(x::'t1 \<times> 't2 \<times> 't3 <named> 'name1 \<times> 'name2 \<times> 'name3). P x`
    into `\<forall>name1::'t1  name2::'t2  name3::'t3.  P (name1,name2,name3)`*)
  val forall_expansion : string list -> Proof.context -> conv
  val meta_All_expansion : string list -> Proof.context -> conv
  val exists_expansion : string list -> Proof.context -> conv
  val ExNu_expansion : string list -> Proof.context -> conv
  val aux_expansions : Proof.context -> thm list

  val forall_expansion_arg_encoding : string list -> Proof.context -> conv
  val meta_All_expansion_arg_encoding : string list -> Proof.context -> conv
  val exists_expansion_arg_encoding : string list -> Proof.context -> conv

  val named_forall : simproc
  val named_ex     : simproc
  val named_metaAll: simproc
  val named_ExSet  : simproc

  (* convert a multi-variable lambda expression (\<lambda>x y z. F x y z) to a single-variable lambda
  expression of a tuple, (\<lambda>pack. F (fst pack) (fst (snd pack)) (snd (snd pack))).
  In addition, the names of x y z are recorded in the type of t
    by using \<^typ>\<open>T <named> 'x \<times> 'y \<times> 'z\<close>*)
  val aggregate_vars_lambda : int -> term -> string list (*names*) * term
  val aggregate_vars_quantification : int -> term -> string list (*names*) * term
  val aggregate_vars_lambda_arg_encoding : int -> term -> string list (*names*) * term
  val aggregate_vars_quantification_arg_encoding : int -> term -> string list (*names*) * term

  (* For any schematic variable \<open>?P :: ?'t1 \<times> ?'t2 \<times> \<dots> <named> ?'name1 \<times> ?'name2 \<times> ...\<close>
     instantiate ?P to \<open>\<lambda>x. case x of tag (t1, t2, ...) \<Rightarrow> ?P t1 t2 \<dots>\<close>*)
  val named_predicate_expansion : Proof.context -> thm -> thm
end

structure QuantExpansion : QUANT_EXPANSION = struct
open Phi_Help Phi_Syntax

fun mk_cases_named names tm = Const (@{const_name case_named},
      (dummyT --> dummyT) --> Type (@{type_name named}, [dummyT, mk_name_tylabels names]) --> dummyT) $ tm

fun const_dest_named T names =
  Const (@{const_name case_named}, (T --> T) --> Phi_Syntax.mk_namedT T names --> T)
    $ Const (@{const_name id}, T --> T)

fun mk_cases_named_fullty names tm =
  case fastype_of tm of Type ("fun", [dom,rng]) =>
      Const (@{const_name case_named},
        (dom --> rng) --> Type (@{type_name named}, [dom, mk_name_tylabels names]) --> rng) $ tm
    | _ => raise TERM ("mk_cases_named_fullty: not a function type", [tm])



fun set_name (N1,N2) rule =
  let fun rename (Abs (N, TY, B)) = Abs (if N = N1 then N2 else "", TY, rename B)
        | rename (A $ B) = rename A $ rename B
        | rename X = X
   in Thm.renamed_prop (rename (Thm.prop_of rule)) rule
  end

infix 1 my_then_conv

fun is_strict_reflexive th = (op =) (Logic.dest_equals (Thm.prop_of th))
  handle TERM _ => false;

fun (cv1 my_then_conv cv2) ct =
  let
    val eq1 = cv1 ct;
    val eq2 = cv2 (Thm.rhs_of eq1);
  in
    if is_strict_reflexive eq1 then eq2
    else if is_strict_reflexive eq2 then eq1
    else Thm.transitive eq1 eq2
  end

fun general_expansion binder tag_rule N0 quant_rule names ctxt =
  let open Conv
      fun expn [] _ ct = all_conv ct
        | expn [N] _ ct =
            let val ret = all_conv ct
             in case Thm.prop_of ret
                  of eq $ LHS $ (Const (B,T) $ Abs (_, T2, X)) =>
                      if B = binder
                      then Thm.renamed_prop (eq $ LHS $ (Const (B,T) $ Abs (N,T2,X))) ret
                      else raise CTERM ("QuantExpansion.general_expansion",[ct])
            end
        | expn (N::L) ctxt' ct =
           (rewr_conv (set_name (N0,N) quant_rule)
            my_then_conv Phi_Conv.quant_conv binder (expn L o snd) ctxt') ct
   in rewr_conv tag_rule
      my_then_conv expn names ctxt
  end


val forall_expansion =
  general_expansion @{const_name All} @{thm named_forall[folded atomize_eq]}
                    "a" @{thm split_paired_All[folded atomize_eq]}
val exists_expansion =
  general_expansion @{const_name Ex} @{thm named_exists[folded atomize_eq]}
                    "a" @{thm split_paired_Ex[folded atomize_eq]}
val meta_All_expansion =
  general_expansion @{const_name Pure.all} @{thm named_All[folded atomize_eq]}
                    "a" @{thm split_paired_all[folded atomize_eq]}
val ExNu_expansion =
  general_expansion @{const_name ExSet} @{thm named_ExSet[folded atomize_eq]}
                    "a" @{thm ExSet_pair[folded atomize_eq]}

(*
val forall_expansion_arg_encoding =
  general_expansion @{const_name All} @{thm named_forall[folded atomize_eq]}
                    "a" @{thm split_paired_All_\<phi>arg[folded atomize_eq]}
val exists_expansion_arg_encoding =
  general_expansion @{const_name Ex} @{thm named_exists[folded atomize_eq]}
                    "a" @{thm split_paired_Ex_\<phi>arg[folded atomize_eq]}
val meta_All_expansion_arg_encoding =
  general_expansion @{const_name Pure.all} @{thm named_All[folded atomize_eq]}
                    "a" @{thm split_paired_all_\<phi>arg[folded atomize_eq]}
*)

fun aux_expansions ctxt = Named_Theorems.get ctxt @{named_theorems named_expansion}



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

fun named_predicate_expansion ctxt th =
  let
    fun uncurry_ty (Type ("fun", [Type (@{type_name named}, [domains, _]), rng])) =
          (*fold_rev (fn a => fn ty => a --> ty) (HOLogic.strip_tupleT domains) rng*)
          HOLogic.strip_tupleT domains ---> rng
    val insts = Term.add_vars (Thm.prop_of th) []
                  |> map_filter (try (` (dest_namedT o domain_type o snd))
                        #> Option.map (fn (names, tm) =>
                            (tm,
                             mk_the_cases (Var (tm |> apsnd uncurry_ty)) names
                                |> Thm.cterm_of ctxt)
                    ))
  in
    Thm.instantiate (TVars.empty, Vars.make insts) th (*index is considered*)
  end

fun simproc_of expn ctxt cterm =
  let
    val Const _ $ abst = Thm.term_of cterm
    val Type ("fun", [Type (@{type_name named}, [T, names_ty]), _])  = fastype_of abst
    val names = dest_name_tylabels names_ty
  in
    SOME (expn T names ctxt cterm)
  end

val named_forall =
  Simplifier.make_simproc \<^context> (Sign.full_name \<^theory> \<^binding>\<open>named_forall\<close>)
    {lhss = [\<^term>\<open>All (P :: 'a <named> 'names \<Rightarrow> bool)\<close>],
     proc = K (simproc_of (fn Type(\<^type_name>\<open>\<phi>arg\<close>, _) => forall_expansion_arg_encoding
                                                    | _ => forall_expansion))}
val named_ex =
  Simplifier.make_simproc \<^context> (Sign.full_name \<^theory> \<^binding>\<open>named_ExSet\<close>)
    {lhss = [\<^term>\<open>Ex (P :: 'a <named> 'names \<Rightarrow> bool)\<close>],
     proc = K (simproc_of (fn Type(\<^type_name>\<open>\<phi>arg\<close>, _) => exists_expansion_arg_encoding
                                                    | _ => exists_expansion))}

val named_ExSet =
  Simplifier.make_simproc \<^context> (Sign.full_name \<^theory> \<^binding>\<open>named_ExSet\<close>)
    {lhss = [\<^term>\<open>ExSet (P :: 'a <named> 'names \<Rightarrow> 'b set)\<close>],
     proc = K (simproc_of (K ExNu_expansion))}

val named_metaAll =
  Simplifier.make_simproc \<^context> (Sign.full_name \<^theory> \<^binding>\<open>named_metaAll\<close>)
    {lhss = [\<^term>\<open>Pure.all (P :: 'a <named> 'names \<Rightarrow> prop)\<close>],
     proc = K (simproc_of (fn Type(\<^type_name>\<open>\<phi>arg\<close>, _) => meta_All_expansion_arg_encoding
                            | _ => meta_All_expansion))}


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

fun strip_abs_names 0 _ = []
  | strip_abs_names N (Abs (name,_,body)) = name :: strip_abs_names (N-1) body
  | strip_abs_names N _ = if N <= 0 then [] else raise Subscript
fun strip_quant_names _ 0 _ = []
  | strip_quant_names H N (H' $ Abs (name,_,X)) =
      if H = gname H' then name :: strip_quant_names H (N-1) X
      else if N <= 0 then [] else raise Subscript
  | strip_quant_names _ N _ = if N <= 0 then [] else raise Subscript

fun strip_abs_tys 0 _ = []
  | strip_abs_tys N (Abs (_,ty,body)) = ty :: strip_abs_tys (N-1) body
  | strip_abs_tys N _ = if N <= 0 then [] else raise Subscript
fun strip_quant_tys _ 0 _ = []
  | strip_quant_tys H N (H' $ Abs (_,ty,body)) =
      if H = gname H' then ty :: strip_quant_tys H (N-1) body
      else if N <= 0 then [] else raise Subscript
  | strip_quant_tys _ N _ = if N <= 0 then [] else raise Subscript

fun lambda_body 0 X = X
  | lambda_body N (Abs (_,_,X)) = lambda_body (N-1) X
  | lambda_body N X = if N <= 0 then X else raise Subscript
fun quant_body _ 0 X = X
  | quant_body H N (H' $ (X' as Abs (_,_,X))) =
      if H = gname H' then quant_body H (N-1) X
      else if N <= 0 then X' else raise Subscript
  | quant_body _ N X = if N <= 0 then X else raise Subscript

fun GEN (mk_prodT,dest_prodT,FST,SND) = let

fun mk_tupleT [] = []
  | mk_tupleT (T::Ts) =
      case mk_tupleT Ts of [] => [T]
                         | (Ts1'::Tsr') => mk_prodT (T,Ts1') :: Ts1' :: Tsr'

fun nth_project [_] 0 term = term
  | nth_project (ty::_::_) 0 term
      = Const (FST, ty --> (fst (dest_prodT ty))) $ term
  | nth_project (ty::tys::tyss) i term =
      nth_project (tys::tyss) (i-1) (Const (SND, ty --> tys) $ term)
  | nth_project _ _ _ = error "BUG:gp8743bpfs"

fun aggregate_vars_raw names tys body =
      let
        val Ts = mk_tupleT tys
        val T = if null Ts then \<^typ>\<open>unit\<close> else hd Ts
        val N = length names
        val C = const_dest_named T names
        fun tr M (Bound i) = if i = ~1 then Bound M (*a trick: ~1 denotes the whole packed lambda variable*)
                             else if i < M then Bound i
                             else (nth_project Ts (N - 1 - i + M) (C $ Bound M))
          | tr M (X $ Y) = (tr M X $ tr M Y)
          | tr M (Abs (n,t,X)) = Abs (n,t, tr (M+1) X)
          | tr _ X = X
      in (names, Abs ("", Phi_Syntax.mk_namedT T names, tr 0 body))
      end

fun aggregate_vars_lambda N term =
      aggregate_vars_raw (strip_abs_names N term) (strip_abs_tys N term) (lambda_body N term)

fun aggregate_vars_quantification N term =
  let
    val Const (H, Type("fun", [Type("fun", [_,T1]),T2])) $ _ = term
    val (N,X) = aggregate_vars_raw  (strip_quant_names H N term)
                                    (strip_quant_tys H N term)
                                    (quant_body H N term)
    val (Abs (_,T0,_)) = X
  in
    (N, Const (H, (T0 --> T1) --> T2) $ X)
  end

in (aggregate_vars_lambda, aggregate_vars_quantification)
end

val (aggregate_vars_lambda, aggregate_vars_quantification) =
  GEN (HOLogic.mk_prodT, HOLogic.dest_prodT, \<^const_name>\<open>eoq__fst\<close>, \<^const_name>\<open>eoq__snd\<close>)

val (aggregate_vars_lambda_arg_encoding,
     aggregate_vars_quantification_arg_encoding) =
  GEN (Procedure_Syntax.mk_arg_prodT, Procedure_Syntax.dest_arg_prodT,
       \<^const_name>\<open>\<phi>V_fst\<close>, \<^const_name>\<open>\<phi>V_snd\<close>)

end