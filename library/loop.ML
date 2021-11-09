structure NuLoop = struct
open NuHelp NuBasics

fun forall_expansion var_names P_ty ctx =
  let
    val arity = length var_names
    val ([P],ctx) = Variable.add_fixes ["\<P>"] ctx
    val P_term = Var((P,0), P_ty --> boolT)
    val forall = Const (@{const_name Pure.eq}, dummyT)
      $ (Const (@{const_name All}, dummyT) $ P_term)
      $ (fold_rev (fn v => fn tm =>
                Const (@{const_name All}, dummyT) $ Abs (v, dummyT, tm)) var_names
          (P_term $
            list_mk_binop_r @{const_name Pair} (List.tabulate (arity,
              (fn i => Bound (arity - i - 1))))))
    val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
                |> Simplifier.add_simp @{thm pair_forall}
    val forall = Syntax.check_prop ctx forall |> cterm_of ctx
    val forall = case Goal.init forall |> SINGLE (HEADGOAL (Simplifier.simp_tac ctx))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve \<forall>-expansion", [forall])
  in forall end

fun ExNu_expansion var_names ctx =
  let
    val arity = length var_names
    val ([T,X],ctx) = Variable.add_fixes ["\<TT>","\<xx>"] ctx
    val T_term = Var((T,0), dummyT)
    val X_term = Var((X,0), dummyT)
    val expansion = Const (@{const_name Pure.eq}, dummyT)
      $ mk_repset (mk_nuTy (X_term, mk_monop @{const_name ExNu} T_term))
      $ mk_repset (mk_nuTy (
          (fold_rev (fn v => fn tm =>
                Abs (v, dummyT, tm)) var_names
            (X_term $
              list_mk_binop_r @{const_name Pair} (List.tabulate (arity,
                (fn i => Bound (arity - i - 1)))))),
          (fold_rev (fn v => fn tm =>
                Const (@{const_name ExNu}, dummyT) $ Abs (v, dummyT,  tm)) var_names
            (T_term $
              list_mk_binop_r @{const_name Pair} (List.tabulate (arity,
                (fn i => Bound (arity - i - 1))))))
      ))
      
    val ctx = (Proof_Context.set_mode Proof_Context.mode_schematic ctx)
          addsimps @{thms ExNu_pair NameHint_def}
    val expansion = Syntax.check_prop ctx expansion |> cterm_of ctx |> @{print}
    val expansion = case Goal.init expansion |> SINGLE (HEADGOAL (Simplifier.simp_tac ctx))
                   of SOME th => Goal.conclude th
                    | _ => raise CTERM ("fail to solve \<exists>\<sup>\<nu>-expansion", [expansion])
  in expansion end

fun mk_loop_proc proc raw_vars stack_schema heap_schema subj always ctx meta =
  let
    val (Const (@{const_name Pair}, _) $ heap $ stack, NU) = dest_current_nu meta
    val stack = HOLogic.strip_tuple stack
    val heap = HOLogic.strip_tuple heap

    val arity = length raw_vars
    val origin_var_names = map (fn (x,_,_) => Binding.name_of x) raw_vars
    val (new_var_names,ctx) = Proof_Context.add_fixes
      (map (fn (a,b,c) => (a, Option.map (Syntax.read_typ ctx) b, c)) raw_vars) ctx
    val var_pairs = origin_var_names ~~ new_var_names
    val vars = map (rpair dummyT) var_pairs

    val stack_schema = rev (
      case stack_schema of SOME sch => map (Syntax.parse_term ctx) sch
        | _ => map (Free o rpair dummyT) new_var_names)
    val _ = if length stack_schema >= length stack then error "Insufficient stack elements" else ()
    val stack' = stack_schema @ (drop (length stack_schema) stack)
    val heap_schema = rev(
      case heap_schema of SOME sch => map (Syntax.parse_term ctx) sch
        | _ => [])
    val _ = if length heap_schema >= length heap then error "Insufficient heap elements" else ()
    val heap' = heap_schema @ (drop (length heap_schema) heap)
    val schema =
      mk_binop @{const_name Pair} (list_mk_binop_r @{const_name Pair} heap',
                                   list_mk_binop_r @{const_name Pair} stack')
                  |> tuple_abs vars
    val NU = Const (@{const_name DownLift}, dummyT) $ NU $ schema

    val always = Option.map (
          Syntax.parse_term ctx #> tuple_abs vars #> mk_monop @{const_name Collect}) always
    val NU = case always of SOME alw => mk_auto_tag (Const (@{const_name NuRefine}, dummyT)) $ NU $ alw
                          | _ => NU

    val NU = Syntax.check_term ctx NU |> cterm_of ctx
    val Type ("fun", [Type (@{type_name prod}, [@{typ "heap"}, ty_a]),
                      Type ("fun", [ty_b, @{typ bool}])]) = fastype_of (term_of NU)
    val cty_a = ctyp_of_cterm NU |> dest_ctyp0 |> dest_ctyp1
    val cty_b = ctyp_of_cterm NU |> dest_ctyp1 |> dest_ctyp0
    val proc = Thm.instantiate ([((("'a",0),[@{class lrep}]),cty_a),
                                 ((("'b",0),[@{class "type"}]),cty_b)],[]) proc

    val forall = forall_expansion origin_var_names (typ_of cty_b) ctx
    val exNu = ExNu_expansion origin_var_names ctx
    val tfrees = Term.add_tfree_names (Thm.prop_of exNu) []
    val exNu = Drule.generalize (tfrees, []) exNu
    val ctx_simp = (clear_simpset ctx) addsimps 
      (Named_Theorems.get ctx @{named_theorems "\<nu>auto_expansion"})
    val proc = Raw_Simplifier.rewrite_rule ctx_simp [forall, exNu] proc
                  |> Thm.instantiate ([],[((("X",0), typ_of_cterm NU), NU)])
                  |> Simplifier.simplify ctx_simp
                  |> @{print}
    val _ = @{print} (Thm.prop_of proc |> dest_Trueprop |> dest_binop @{const_name "HOL.implies"} |>
    #2 |> dest_procedure |> #2)


    val subj = tuple_abs vars (Syntax.parse_term ctx subj) |> mk_monop @{const_name Collect}
  in meta
  end
end
