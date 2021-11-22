signature QUANT_EXPANSION = sig
  val forall_expansion : string list -> Proof.context -> thm
  val pure_All_expansion : string list -> Proof.context -> thm
  val exists_expansion : string list -> Proof.context -> thm
  val ExNu_expansion : string list -> Proof.context -> thm
  val simproc_of : (string list -> string list -> thm) -> string list -> cterm -> thm option
  (* expand all schematic variabls of type `?'x named 'names` *)
  val schematic_var_expansion : string list -> Proof.context -> thm
end
structure QuantExpansion (* : QUANT_EXPANSION *) = struct
open NuHelp NuBasics

fun mk_cases_named names tm = Const (@{const_name case_named},
      (dummyT --> dummyT) --> Type (@{type_name named}, [dummyT, mk_name_tylabels names]) --> dummyT) $ tm

fun mk_cases_named_fullty names tm =
  case fastype_of tm of Type ("fun", [dom,rng]) =>
      Const (@{const_name case_named},
        (dom --> rng) --> Type (@{type_name named}, [dom, mk_name_tylabels names]) --> rng) $ tm
    | _ => raise TERM ("mk_cases_named_fullty: not a function type", [tm])

local

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
      | mk_case tm = tm
    val arity = length names
  in
    mk_cases_named_fullty (map fst names)
      (fold_rev (fn (name,ty) => fn tm => mk_case (Abs (name, ty, tm)))
        names
        (ntimes arity (fn i => fn x => x $ Bound (arity - 1 - i)) P_term))
  end

in

fun gen_general_expansion const thms names ctx =
  let
    val arity = length names
    val ([P],ctx) = Variable.add_fixes ["\<P>"] ctx
    val P_term = Var((P,0), abs_arg_ty names --> dummyT)
    val forall = Const (@{const_name Pure.eq}, dummyT)
      $ (Const (const, dummyT) $ P_term)
      $ mk_the_binder const P_term (map (rpair dummyT) names)
    val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx addsimps thms
    val forall = Syntax.check_prop ctx forall |> cterm_of ctx
    val forall = case Goal.init forall |> SINGLE (HEADGOAL (Simplifier.simp_tac ctx))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve \<forall>-expansion", [forall])
  in forall end

val forall_expansion =
  gen_general_expansion @{const_name All} @{thms pair_forall named_forall}
val exists_expansion =
  gen_general_expansion @{const_name Ex} @{thms pair_exists named_exists}
val pure_All_expansion =
  gen_general_expansion @{const_name Pure.all} @{thms pair_All named_All}


fun ExNu_expansion names ctx =
  let
    val arity = length names
    val ([T,X],ctx) = Variable.add_fixes ["\<TT>","\<xx>"] ctx
    val tya = TVar(("'a",0), @{sort "type"})
    val tyb = TVar(("'b",0), @{sort "type"})
    val T_term = Var((T,0), abs_arg_ty names --> mk_Nu_ty (tya,tyb))
    val X_term = Var((X,0), abs_arg_ty names --> tyb)
    val expansion = Const (@{const_name Pure.eq}, dummyT)
      $ mk_repset (mk_nuTy (X_term, mk_monop @{const_name ExNu} T_term))
      $ mk_repset (mk_nuTy (
          mk_the_binder "" X_term (map (rpair dummyT) names),
          mk_the_binder @{const_name ExNu} T_term (map (rpair dummyT) names)
      ))
      
    val ctx = (Proof_Context.set_mode Proof_Context.mode_schematic ctx)
          addsimps @{thms ExNu_pair named_ExNu}
    val expansion = Syntax.check_prop ctx expansion |> cterm_of ctx |> @{print}
    val expansion = case Goal.init expansion |> SINGLE (HEADGOAL (Simplifier.simp_tac ctx))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve \<exists>\<sup>\<nu>-expansion", [expansion])
  in expansion end

fun schematic_var_expansion ctx th =
  let
    fun uncurry_ty (Type ("fun", [Type (@{type_name named}, [domains, _]), rng])) =
          fold_rev (fn a => fn ty => a --> ty) (HOLogic.strip_tupleT domains) rng
    val insts = add_vars (Thm.prop_of th) []
                  |> map_filter (try (` (dest_named o domain_type o snd)) #> Option.map (fn (names, tm) =>
                      (tm, mk_the_cases (Var (tm |> apsnd uncurry_ty)) names
                              |> cterm_of ctx |> @{print})
                    ))
  in
    Thm.instantiate ([], insts) th
  end

end

fun simproc_of expn ctx cterm =
  let
    val Const _ $ abst = term_of cterm
    val Type ("fun", [Type (@{type_name named}, [_, names]), _])  = fastype_of abst
    val names = dest_name_tylabels names
  in
    SOME (expn names ctx)
  end

val cty_a = TVar (("'a",1),["HOL.type"]) |> Thm.ctyp_of @{context}
fun spec_retaining_name th =
  let
    val Abs (name,_,_)
      = Thm.concl_of th |> dest_Trueprop |> dest_monop @{const_name All}
    val spec =
      Thm.instantiate ([],[((("x",1), TVar (("'a",1),["HOL.type"])), Thm.var((name,0), cty_a))])
        (Thm.incr_indexes 1 @{thm spec})
  in
    th RS spec
  end

end
