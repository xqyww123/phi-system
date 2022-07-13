signature NU_VARIABLE_FACTOR = sig
  val vary_by_parts : string list -> string option -> Proof.context -> thm -> thm
  val vary_by_pattern : (binding * string option * mixfix) list
    -> string -> string option -> Proof.context -> thm -> thm
end

structure Nu_Variable_Factor : NU_VARIABLE_FACTOR = struct
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

val prodconst = Const (@{const_name case_prod}, dummyT)
fun caseprod (tm as (Abs (_,_, Abs (_,_, _)))) = prodconst $ tm
  | caseprod (tm as (Abs (_,_, Const (@{const_name case_prod}, _) $ _))) = prodconst $ tm
  | caseprod tm = tm

fun gen_vary prep_vars prep_pattern prep_subj
        raw_vars raw_pattern subj ctxt' sequent =
  let
    val Const (@{const_name Variant_Cast}, _) $ _ $ X' $ _
          = Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val (origin_names, vnames, vars, X'', ctxt) =
          Phi_Generalization.gen_pattern_match prep_vars prep_pattern raw_vars raw_pattern ctxt' X'
    fun subst_var n x = case Symtab.lookup vars n
                          of SOME (i,_) => Bound i
                           | NONE => x
    val wrap =
           Term.map_aterms (fn (x as Var ((n,0),_)) => subst_var n x
                             | (x as Free (n,_)) => subst_var n x
                             | x => x)
        #> fold (fn (n,v) => fn b =>
              caseprod (Abs (n, the_default dummyT (Option.map snd (Symtab.lookup vars v)), b))
            ) (origin_names ~~ vnames)
        #> mk_cases_named origin_names
        #> (fn x => x $ Bound 0)
    val X = wrap X''
         |> (fn x => case subj
                       of SOME s => Const (\<^const_name>\<open>Subjection\<close>, dummyT)
                                        $ x $ wrap (prep_subj (ctxt,vnames) s)
                        | NONE => x)
         |> (fn x => Abs ("",dummyT,x))

    val [var] = Variable.variant_frees ctxt [] [("Variant_Cast_vars", dummyT)]
    val var_tag' = Const (@{const_name Variant_Cast}, dummyT) $ Free var $ X' $ X
                    |> Syntax.check_term ctxt 
    val var_tag = (case var_tag' of (T0 $ Free(name,T1) $ T2 $ T3) =>
                      (T0 $ Var((name,0),T1) $ T2 $ T3))
                  |> mk_Trueprop |> Thm.cterm_of ctxt

    val goal = Goal.init var_tag
                  |> SINGLE (REPEAT (HEADGOAL (resolve_tac ctxt
                        @{thms HOL.refl case_prod_expn_I case_named_expn_I
                               Variant_Cast_I_always Variant_Cast_I})))
    val var_tag_th = (case goal of SOME concl => Goal.conclude concl
                        | NONE => raise CTERM ("fail to solve", [var_tag]))

    val forall = forall_expansion origin_names ctxt
    val exNu = ExNu_expansion origin_names ctxt
    val Subjection_simp_proc_arg = Proof_Context.get_thm ctxt "local.Subjection_simp_proc_arg"
  in
    (var_tag_th RS sequent)
      |> schematic_var_expansion ctxt
      |> Raw_Simplifier.rewrite_rule ctxt
          (forall::exNu::Subjection_simp_proc_arg::
              Named_Theorems.get ctxt \<^named_theorems>\<open>named_expansion\<close>)
      |> Thm.solve_constraints
  end


val vary_by_pattern =
      gen_vary (fn ctxt => fn vs =>
                    (map (Binding.name_of o #1) vs, Proof_Context.add_fixes_cmd vs ctxt))
               (fn (ctxt,vnames) => Proof_Context.read_term_pattern ctxt
                                 #> map_aterms (
                                      fn (Free (n,t)) => if exists (fn n' => n' = n) vnames
                                                         then Var ((n,0), t)
                                                         else Free (n,t)
                                                (*0 is ok because the name is fixed*)
                                       | x => x))
               (fn (ctxt,vnames) => Syntax.parse_term ctxt
                                 #> map_aterms (
                                      fn (Free (n,t)) => if exists (fn n' => n' = n) vnames
                                                         then Var ((n,0), t)
                                                         else Free (n,t)
                                                (*0 is ok because the name is fixed*)
                                       | x => x))

fun vary_by_parts raw_vars subj ctxt sequent =
  let
    val Const (@{const_name Variant_Cast}, _) $ _ $ X' $ _
          = Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
  in gen_vary (fn ctxt => Syntax.read_terms ctxt
                       #> map (fn (Free (x,_)) => x
                                | t => raise TERM("pattern must be a free variable", [t]))
                       #> (fn v => (v, (v, ctxt))))
              (K (K X')) (Syntax.read_term o #1)
              raw_vars (Bound ~1) subj ctxt sequent
  end

end
