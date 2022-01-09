signature NU_VARIABLES_TAG = sig
  val variables_tag_terms : string list -> string option -> Proof.context -> thm -> thm
  val variables_tag_pattern_match : (binding * string option * mixfix) list
    -> string list -> string option -> Proof.context -> thm -> thm
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


fun gen_set_variables_tag prep_seps vars always ctxt sequent =
  let
    val Const (@{const_name Variant_Cast}, _) $ _ $ X $ _
          = Thm.major_prem_of sequent |> dest_Trueprop
    val X' = prep_seps ctxt X

    val names = map fst vars
    val ctxt = Variable.declare_typ (mk_name_tylabels names) ctxt

    val always = always
          |> Option.map (Syntax.parse_term ctxt #> tuple_abs vars #> mk_cases_named names)

    val X' = tuple_abs vars X' |> mk_cases_named names
    val X' = case always of SOME alw =>
              Abs ("\<xx>", dummyT,
                Const(@{const_name Subjection}, dummyT) $ (X' $ Bound 0)
                  $ (Const (@{const_abbrev Normal_Premise}, dummyT) $ (alw $ Bound 0)))
             | NONE => X'

    val [var] = Variable.variant_frees ctxt [] [("Variant_Cast_vars", dummyT)]
    val var_tag = Const (@{const_name Variant_Cast}, dummyT) $ Free var $ X $ X'
                    |> Syntax.check_term ctxt 
    val var_tag = (case var_tag of (T0 $ Free(name,T1) $ T2 $ T3) =>
                      (T0 $ Var((name,0),T1) $ T2 $ T3))
                  |> mk_Trueprop |> cterm_of ctxt

    val goal = Goal.init var_tag |> @{print}
                  |> SINGLE (REPEAT (HEADGOAL (resolve_tac ctxt
                        @{thms HOL.refl case_prod_expn_I case_named_expn_I
                               Variant_Cast_I_always Variant_Cast_I})))
    val var_tag_th = (case goal of SOME concl => Goal.conclude concl
                        | NONE => raise CTERM ("fail to solve", [var_tag]))
                        |> @{print}

    val forall = forall_expansion names ctxt
    val exNu = ExNu_expansion names ctxt
    val simctx = Raw_Simplifier.clear_simpset ctxt addsimprocs
          [@{simproc named_forall_expansion}, @{simproc named_exSet_expansion},
           @{simproc named_pureAll_expansion}]
          addsimps @{thms NuSys.named.case Product_Type.prod.case}
    val sequent = (var_tag_th RS sequent)
                  |> @{print}
                  |> schematic_var_expansion ctxt
                  |> @{print}
                  |> Raw_Simplifier.rewrite_rule ctxt (forall::exNu::
                    @{thms HOL.simp_thms[unfolded atomize_eq[symmetric]]
                           Product_Type.prod.case[unfolded atomize_eq[symmetric]]
                           NuSys.named.case[unfolded atomize_eq[symmetric]]
                           Subjection_simp_proc_arg
                     })
                  |> @{print}
  in
    sequent
  end

fun variables_tag_pattern_match raw_vars pattern always ctxt sequent =
  let
    val origin_var_names = map (fn (x,_,_) => Binding.name_of x) raw_vars
    val (new_var_names,ctxt) =
      Proof_Context.add_fixes (map (fn (a,b,c) => (a, Option.map (Syntax.read_typ ctxt) b, c)) raw_vars) ctxt
    val vars = origin_var_names ~~ map (rpair dummyT) new_var_names

    fun prep_seps ctxt X =
      let
        val pattern = rev (map (Syntax.parse_term ctxt) pattern)
        val sep = strip_binop_l @{const_name Separation} X

        val sep' = pattern ~~ take (length pattern) sep
              |> map (fn (pat, org) => (*TODO: patter match here*)
                  case try dest_RepSet org
                    of SOME (x,T) => mk_RepSet (Type.constraint (fastype_of x) pat, T)
                     | NONE => pat)
              |> (fn l => l @ drop (length pattern) sep)
      in
        list_mk_binop_l @{const_name Separation} sep'
      end
  in
    gen_set_variables_tag prep_seps vars always ctxt sequent
  end

fun variables_tag_terms raw_vars always ctxt sequent =
  let
    val vars = map (Syntax.parse_term ctxt #> Syntax.check_term ctxt #> debug_term ctxt "qqqq "
                      #> (fn tm => (normlize_name (term_name tm), (term_name tm, fastype_of tm)))
                   ) raw_vars
  in
    gen_set_variables_tag (K I) vars always ctxt sequent end

end
