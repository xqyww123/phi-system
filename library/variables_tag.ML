signature NU_VARIABLES_TAG = sig
  val variables_tag_terms : string list -> string option -> Proof.context -> thm -> thm
  val variables_tag_pattern_match : (binding * string option * mixfix) list
    -> string list option -> string list option -> string option -> Proof.context -> thm -> thm
end
structure NuVariablesTag : NU_VARIABLES_TAG = struct
open NuHelp NuBasics QuantExpansion

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


fun gen_set_variables_tag prep_S vars always ctx sequent =
  let
    val ctx = Proof_Context.set_mode Proof_Context.mode_schematic ctx
                |> Proof_Context.set_mode Proof_Context.mode_pattern
    val Const (@{const_name Variant_Cast}, _) $ _ $ S $ H $ _ $ _
          = Thm.major_prem_of sequent |> dest_Trueprop
    val (S',H') = prep_S ctx (S,H)
    val _ = debug_term ctx "aaaaaa " S'

    val names = map fst vars
    val ctx = Variable.declare_typ (mk_name_tylabels names) ctx

    val always = Option.map (Syntax.parse_term ctx #> tuple_abs vars #> mk_cases_named names) always

    val S' = tuple_abs vars S' |> mk_cases_named names
    val H' = tuple_abs vars H' |> mk_cases_named names
    val S' = case always of SOME alw =>
              Abs ("\<xx>", dummyT,
                Const(@{const_name AdditionSet}, dummyT) $ (S' $ Bound 0)
                  $ (Const (@{const_name Premise}, dummyT) $ (alw $ Bound 0)))
          | NONE => S'

    val var_tag = Const (@{const_name Variant_Cast}, dummyT) $ dummy $ S $ H $ S' $ H'
                    |> mk_Trueprop
                    |> Syntax.check_prop ctx |> cterm_of ctx
    val goal = Goal.init var_tag |> @{print}
                  |> SINGLE (REPEAT (HEADGOAL (resolve_tac ctx
                        @{thms HOL.refl case_prod_expn_I case_named_expn_I
                               Variant_Cast_I_always Variant_Cast_I})))
    val var_tag_th = (case goal of SOME concl => Goal.conclude concl
                        | NONE => raise CTERM ("fail to solve", [var_tag]))
                        |> @{print}

    val forall = forall_expansion names ctx
    val exNu = ExNu_expansion names ctx
    val simctx = Raw_Simplifier.clear_simpset ctx addsimprocs
          [@{simproc named_forall_expansion}, @{simproc named_exSet_expansion},
           @{simproc named_pureAll_expansion}]
          addsimps @{thms NuPrime.named.case Product_Type.prod.case}
    val sequent = (var_tag_th RS sequent)
                  |> @{print}
                  |> schematic_var_expansion ctx
                  |> @{print}
                  |> Raw_Simplifier.rewrite_rule ctx (forall::exNu::
                    @{thms HOL.simp_thms[unfolded atomize_eq[symmetric]]
                           Product_Type.prod.case[unfolded atomize_eq[symmetric]]
                           NuPrime.named.case[unfolded atomize_eq[symmetric]]
                           AdditionSet_simp_proc_arg
                     })
                  |> @{print}
  in
    sequent
  end

fun variables_tag_pattern_match raw_vars stack_schema heap_schema always ctx sequent =
  let
    val origin_var_names = map (fn (x,_,_) => Binding.name_of x) raw_vars
    val (new_var_names,ctx) =
      Proof_Context.add_fixes (map (fn (a,b,c) => (a, Option.map (Syntax.read_typ ctx) b, c)) raw_vars) ctx
    val vars = origin_var_names ~~ map (rpair dummyT) new_var_names

    fun prep_S ctx (S,H) =
      let
        val stack_schema = rev (
          case stack_schema of SOME sch => map (Syntax.parse_term ctx) sch
            | _ => [])
        val heap_schema = rev(
          case heap_schema of SOME sch => map (Syntax.parse_term ctx) sch
            | _ => [])

        val (stack,heap) =
            (strip_binop_l @{const_name Stack_Delimiter} S,
             strip_binop_l @{const_name Heap_Divider} H)

        val stack' = stack_schema ~~ take (length stack_schema) stack
              |> map (fn (sch, org) =>
                  case try dest_RepSet org
                    of SOME (x,T) => mk_RepSet (Type.constraint (fastype_of x) sch, T)
                     | NONE => sch)
              |> (fn l => l @ drop (length stack_schema) stack)
        val heap' = heap_schema ~~ take (length heap_schema) heap
              |> map (fn (sch, org) =>
                  case try dest_RepSet org
                    of SOME (x,T) => mk_RepSet (Type.constraint (fastype_of x) sch, T)
                     | NONE => sch)
              |> (fn l => l @ drop (length heap_schema) heap)
      in
        (list_mk_binop_l @{const_name Stack_Delimiter} stack',
         list_mk_binop_l @{const_name Heap_Divider}    heap' )
      end
  in
    gen_set_variables_tag prep_S vars always ctx sequent
  end

fun variables_tag_terms raw_vars always ctx sequent =
  let
    val vars = map (Syntax.parse_term ctx #> Syntax.check_term ctx #> debug_term ctx "qqqq "
                      #> (fn tm => (normlize_name (term_name tm), (term_name tm, fastype_of tm)))
                   ) raw_vars
  in
    gen_set_variables_tag (K I) vars always ctx sequent end

end
