structure NuVariablesTag = struct
open NuHelp NuBasics

(* TODO: replace all dummyT and Syntax.check_term by decided types.*)

fun strip_abs_names (Abs (name,_,body)) = name :: strip_abs_names body
  | strip_abs_names (Const (@{const_name case_prod}, _) $ body) = strip_abs_names body
  | strip_abs_names _ = []
fun strip_abs_tys (Abs (_,ty,body)) = ty :: strip_abs_tys body
  | strip_abs_tys (Const (@{const_name case_prod}, _) $ body) = strip_abs_tys body
  | strip_abs_tys _ = []
fun strip_abs_fixes (Abs (name,ty,body)) =
      (Binding.name name, (if ty = dummyT then NONE else SOME ty), NoSyn) :: strip_abs_fixes body
  | strip_abs_fixes (Const (@{const_name case_prod}, _) $ body) = strip_abs_fixes body
  | strip_abs_fixes _ = []

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

fun forall_expansion names ctx =
  let
    val arity = length names
    val ([P],ctx) = Variable.add_fixes ["\<P>"] ctx
    val P_term = Var((P,0), abs_arg_ty names --> boolT)
    val forall = Const (@{const_name Pure.eq}, dummyT)
      $ (Const (@{const_name All}, dummyT) $ P_term)
      $ mk_the_binder @{const_name All} P_term (map (rpair dummyT) names)
    val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
                addsimps @{thms pair_forall named_forall}
    val forall = Syntax.check_prop ctx forall |> cterm_of ctx
    val forall = case Goal.init forall |> SINGLE (HEADGOAL (Simplifier.simp_tac ctx))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve \<forall>-expansion", [forall])
  in forall end

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

fun schematic_var_expansion names ctx th =
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


fun gen_set_variables_tag vars stack_schema heap_schema always ctx meta =
  let
    val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
                |> Proof_Context.set_mode Proof_Context.mode_pattern
    val (major,aux) = elim_SPEC meta
    val Const (@{const_name Variant_Cast}, _)
          $ (stack_typing as (Const (@{const_name typing}, _) $ stack_term $ stack_Nu))
          $ (heap_typing as (Const (@{const_name typing}, _) $ heap_term $ heap_Nu))
          $ _ $ _ $ _
      = Thm.major_prem_of major |> dest_Trueprop
    val heap_ty = fastype_of heap_term
    val stack_ty = fastype_of stack_term
    val stack = HOLogic.strip_tuple stack_term
    val heap = HOLogic.strip_tuple heap_term

    val arity = length vars
    val names = map fst vars
    val ctx = Variable.declare_typ (mk_name_tylabels names) ctx

    val always = Option.map (Syntax.parse_term ctx #> tuple_abs vars #> mk_cases_named names) always

    val stack_schema = rev (
      case stack_schema of SOME sch => map (Syntax.parse_term ctx) sch
        | _ => [])
    val _ = if length stack_schema >= length stack then error "Insufficient stack elements" else ()
    val stack_schema = stack_schema @ (drop (length stack_schema) stack |> map (map_types (K dummyT)))
                          |> list_mk_binop_r @{const_name Pair} |> Type.constraint stack_ty
                          |> tuple_abs vars |> mk_cases_named names
    val stack_Nu = mk_auto_tag (Const (@{const_name DownLift}, dummyT) $ stack_Nu $ stack_schema)
    val stack_Nu = case always of SOME tm =>
              mk_auto_tag (Const (@{const_name NuRefine}, dummyT)
                $ stack_Nu $ mk_monop @{const_name Collect} tm)
          | NONE => stack_Nu

    val heap_schema = rev(
      case heap_schema of SOME sch => map (Syntax.parse_term ctx) sch
        | _ => [])
    val _ = if length heap_schema >= length heap then error "Insufficient heap elements" else ()
    val heap_schema = heap_schema @ (drop (length heap_schema) heap |> map (map_types (K dummyT)))
                          |> list_mk_binop_r @{const_name Pair} |> Type.constraint heap_ty
                          |> tuple_abs vars |> mk_cases_named names 
    val heap_Nu = mk_auto_tag (Const (@{const_name DownLift}, dummyT) $ heap_Nu $ heap_schema)

    val var_tag = Const (@{const_name Variant_Cast}, dummyT)
          $ stack_typing $ heap_typing $ dummy $ stack_Nu $ heap_Nu
              |> mk_Trueprop |> Syntax.check_prop ctx
    val var_tag = cterm_of ctx var_tag
    val goal = Goal.init var_tag |> @{print}
                  |> SINGLE (REPEAT (HEADGOAL (resolve_tac ctx
                        @{thms HOL.refl case_prod_expn_I case_named_expn_I
                               Variant_Cast_I Variant_Cast_I_always}))) |> @{print}
    val var_tag_th = (case goal of SOME concl => Goal.conclude concl
                        | NONE => raise CTERM ("fail to solve", [var_tag])) |> @{print}

    val forall = forall_expansion names ctx |> @{print}
    val exNu = ExNu_expansion names ctx |> @{print}
    val major = (var_tag_th RS major)
                  |> schematic_var_expansion names ctx
                  |> Raw_Simplifier.rewrite_rule ctx (forall::exNu::
                    @{thms HOL.simp_thms[unfolded atomize_eq[symmetric]]
                           Product_Type.prod.case[unfolded atomize_eq[symmetric]]})
                  |> Simplifier.full_simplify ctx
  in
    intro_SPEC (major, aux)
  end

fun variables_tag_pattern_match raw_vars stack_schema heap_schema always ctx meta =
  let
    val origin_var_names = map (fn (x,_,_) => Binding.name_of x) raw_vars
    val (new_var_names,ctx) =
      Proof_Context.add_fixes (map (fn (a,b,c) => (a, Option.map (Syntax.read_typ ctx) b, c)) raw_vars) ctx
    val vars = origin_var_names ~~ map (rpair dummyT) new_var_names
  in
    gen_set_variables_tag vars stack_schema heap_schema always ctx meta
  end

fun variables_tag_terms raw_vars stack_schema heap_schema always ctx meta =
  let
    val vars = map (Syntax.parse_term ctx #> Syntax.check_term ctx
                      #> term_name #> (fn name => (normlize_name name,(name,dummyT)) )) raw_vars
  in
    gen_set_variables_tag vars stack_schema heap_schema always ctx meta
  end

fun vars_subj subj ctx meta =
  let
    val (major,aux) = elim_SPEC meta
    val Const (@{const_name Variants_Subj}, _) $ vars $ _ = Thm.major_prem_of major |> dest_Trueprop
    val (new_var_names,ctx) = Proof_Context.add_fixes (strip_abs_fixes vars) ctx
    val origin_var_names = strip_abs_names vars
    val subj = Syntax.parse_term ctx subj
                |> tuple_abs (origin_var_names ~~ map (rpair dummyT) new_var_names)
    val var_subj = Const (@{const_name Variants_Subj}, dummyT) $ vars $ subj
                    |> mk_Trueprop |> Syntax.check_prop ctx |> cterm_of ctx
                    |> trivial |> (fn th => @{thm Variants_Subj_I} RS th) |> @{print}
    val major = var_subj RS major
  in
    intro_SPEC (major, aux)
  end

end
