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
    val stack = strip_binop_r "Product_Type.Pair" (stack_term |> @{print})
    val heap  = strip_binop_r "Product_Type.Pair" heap_term

    val arity = length vars
    val names = map fst vars
    val ctx = Variable.declare_typ (mk_name_tylabels names) ctx

    val always = Option.map (Syntax.parse_term ctx #> tuple_abs vars #> mk_cases_named names) always

    val stack_schema = rev (
      case stack_schema of SOME sch => map (Syntax.parse_term ctx) sch
        | _ => []) |> @{print}
    val _ = if length stack_schema >= length stack then error "Insufficient stack elements" else ()
    val stack_schema = (@{print} stack_schema) @ (drop (length stack_schema) stack |> @{print}
                                      |> map (map_types (K dummyT))
                                    (* We strip type denotations here in order to catch them when
                                    * lambda-abstraction (since the type of lambda variable is also
                                    * dummyT), and they can be infered latter by explicit
                                    * type constraints. *))
                          |> @{print}
                          |> list_mk_binop_r @{const_name Pair} |> Type.constraint stack_ty
                          |> tuple_abs vars |> mk_cases_named names
    val stack_Nu = mk_auto_tag (Const (@{const_name DownLift}, dummyT) $ stack_Nu $ stack_schema)
    val stack_Nu = case always of SOME tm =>
              mk_auto_tag (Const (@{const_name NuRefine}, dummyT)
                $ stack_Nu $ mk_monop @{const_name Collect} tm)
          | NONE => stack_Nu
    val _ = debug_term ctx "aaa " stack_Nu

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
              |> mk_Trueprop 
              |> Syntax.check_prop ctx
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
                  |> @{print}
                  |> schematic_var_expansion ctx
                  |> @{print}
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

fun variables_tag_terms raw_vars always ctx meta =
  let
    val vars = map (Syntax.parse_term ctx #> Syntax.check_term ctx
                      #> term_name #> (fn name => (normlize_name name,(name,dummyT)) )) raw_vars
  in
    gen_set_variables_tag vars NONE NONE always ctx meta
  end

(* fun vars_subj subj ctx meta =
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
  end *)

end
