structure NuVariablesTag = struct
open NuHelp NuBasics


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

fun forall_expansion vars ctx =
  let
    val var_names = strip_abs_names vars
    val arity = length var_names
    val ([P],ctx) = Variable.add_fixes ["\<P>"] ctx
    val P_term = Var((P,0), list_mk_binop_r_ty @{type_name prod} (strip_abs_tys vars) --> boolT)
    val forall = Const (@{const_name Pure.eq}, dummyT)
      $ (Const (@{const_name Variants_Quant_Tag}, dummyT) $ vars $ (Const (@{const_name All}, dummyT) $ P_term))
      $ (fold_rev (fn v => fn tm =>
                Const (@{const_name All}, dummyT) $ Abs (v, dummyT, tm)) var_names
          (P_term $
            list_mk_binop_r @{const_name Pair} (List.tabulate (arity,
              (fn i => Bound (arity - i - 1))))))
    val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
                addsimps @{thms pair_forall Variants_Quant_Tag_def}
    val forall = Syntax.check_prop ctx forall |> cterm_of ctx
    val forall = case Goal.init forall |> SINGLE (HEADGOAL (Simplifier.simp_tac ctx))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve \<forall>-expansion", [forall])
  in forall end

fun ExNu_expansion vars ctx =
  let
    val var_names = strip_abs_names vars
    val arity = length var_names
    val ([T,X],ctx) = Variable.add_fixes ["\<TT>","\<xx>"] ctx
    val T_term = Var((T,0), dummyT)
    val X_term = Var((X,0), dummyT)
    val expansion = Const (@{const_name Pure.eq}, dummyT)
      $ mk_repset (mk_nuTy (X_term,
          Const (@{const_name Variants_Quant_Tag}, dummyT) $ vars $ mk_monop @{const_name ExNu} T_term))
      $ mk_repset (mk_nuTy (
          (fold_rev (fn v => fn tm =>
                Abs (v, dummyT, tm)) var_names
            (X_term $
              list_mk_binop_r @{const_name Pair} (List.tabulate (arity,
                (fn i => Bound (arity - i - 1)))))),
          (fold_rev (fn v => fn tm =>
                Const (@{const_name ExNu}, dummyT) $ Abs (v, dummyT, tm)) var_names
            (T_term $
              list_mk_binop_r @{const_name Pair} (List.tabulate (arity,
                (fn i => Bound (arity - i - 1))))))
      ))
      
    val ctx = (Proof_Context.set_mode Proof_Context.mode_schematic ctx)
          addsimps @{thms ExNu_pair Variants_Quant_Tag_def}
    val expansion = Syntax.check_prop ctx expansion |> cterm_of ctx |> @{print}
    val expansion = case Goal.init expansion |> SINGLE (HEADGOAL (Simplifier.simp_tac ctx))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve \<exists>\<sup>\<nu>-expansion", [expansion])

    val tfrees = Term.add_tfree_names (Thm.prop_of expansion) []
    val expansion = Drule.generalize (tfrees, []) expansion
  in expansion end


fun gen_set_variables_tag vars stack_schema heap_schema always ctx meta =
  let
    val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
                |> Proof_Context.set_mode Proof_Context.mode_pattern
    val (major,aux) = elim_SPEC meta
    val Const (@{const_name Variants_Tag}, _) $ _ $ _ $ stack_term $ _ $ heap_term $ _ $ _
          = Thm.major_prem_of major |> dest_Trueprop
    val heap_ty = fastype_of heap_term
    val stack_ty = fastype_of stack_term
    val stack = HOLogic.strip_tuple stack_term |> @{print}
    val heap = HOLogic.strip_tuple heap_term

    val arity = length vars
    val lambda_vars = @{term "()"} |> tuple_abs vars

    val stack_schema = rev (
      case stack_schema of SOME sch => map (Syntax.parse_term ctx) sch
        | _ => [])
    val _ = if length stack_schema >= length stack then error "Insufficient stack elements" else ()
    val stack_schema = stack_schema @ (drop (length stack_schema) stack |> map (map_types (K dummyT)))
                          |> list_mk_binop_r @{const_name Pair} |> Type.constraint stack_ty |> @{print}
                          |> tuple_abs vars |> @{print}

    val heap_schema = rev(
      case heap_schema of SOME sch => map (Syntax.parse_term ctx) sch
        | _ => [])
    val _ = if length heap_schema >= length heap then error "Insufficient heap elements" else ()
    val heap_schema = heap_schema @ (drop (length heap_schema) heap |> map (map_types (K dummyT)))
                          |> list_mk_binop_r @{const_name Pair} |> Type.constraint heap_ty
                          |> tuple_abs vars

    val always = (case always of SOME tm => Syntax.parse_term ctx tm
                               | NONE => Const (@{const_name True}, boolT))
                    |> tuple_abs vars

    val var_tag = Const (@{const_name Variants_Tag}, dummyT) $ lambda_vars $ dummy
                    $ stack_term $ stack_schema $ heap_term $ heap_schema $ always
                     |> mk_Trueprop |> Syntax.check_prop ctx 
    val Const (@{const_name Variants_Tag}, _) $ lambda_vars $ _ $ _ $ _ $ _ $ _ $ _
      = dest_Trueprop var_tag
    val var_tag = cterm_of ctx var_tag
    val goal = Goal.init var_tag
                  |> SINGLE (REPEAT (HEADGOAL (resolve_tac ctx
                        @{thms Variants_Tag_I case_prod_expn_I HOL.refl})))
                  |> @{print}
    val var_tag_th = (case goal of SOME concl => Goal.conclude concl
                        | NONE => raise CTERM ("fail to solve", [var_tag])) |> @{print}

    val forall = forall_expansion lambda_vars ctx |> @{print}
    val exNu = ExNu_expansion lambda_vars ctx |> @{print}
    val major = (var_tag_th RS major)
                  |> Raw_Simplifier.rewrite_rule ctx (forall::exNu::
                    @{thms HOL.simp_thms[unfolded atomize_eq[symmetric]]
                           Product_Type.prod.case[unfolded atomize_eq[symmetric]]})
  in
    intro_SPEC (major, aux)
  end

fun variables_tag_pattern_match raw_vars stack_schema heap_schema always ctx meta =
  let
    val origin_var_names = map (fn (x,_,_) => Binding.name_of x) raw_vars
    val (new_var_names,ctx) =
      Proof_Context.add_fixes (map (fn (a,b,c) => (a, Option.map (Syntax.read_typ ctx) b, c)) raw_vars) ctx
    val var_pairs = origin_var_names ~~ new_var_names
    val vars = map (rpair dummyT) var_pairs
  in
    gen_set_variables_tag vars stack_schema heap_schema always ctx meta
  end

fun variables_tag_terms raw_vars stack_schema heap_schema always ctx meta =
  let
    val vars = map (Syntax.parse_term ctx #> Syntax.check_term ctx #> term_name
            #> (fn name => ((name,name), dummyT) )) raw_vars
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
                |> tuple_abs (origin_var_names ~~ new_var_names |> map (rpair dummyT))
    val var_subj = Const (@{const_name Variants_Subj}, dummyT) $ vars $ subj
                    |> mk_Trueprop |> Syntax.check_prop ctx |> cterm_of ctx
                    |> trivial |> (fn th => @{thm Variants_Subj_I} RS th) |> @{print}
    val major = var_subj RS major
  in
    intro_SPEC (major, aux)
  end

end
