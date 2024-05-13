local


fun sem_rule_expr' bvtys0 T_term0 ctxt =
  let val (rev_args, x_ty, _) = dest_parameterized_phi_ty (Term.fastype_of1 (bvtys0,T_term0))
      val M = length rev_args
      val T_term = fold_index (fn (i,_) => fn X => X $ Bound (M-1-i)) rev_args
                      (Term.incr_boundvars M T_term0)
      val bvtys = rev_args @ bvtys0

      val T_params = Phi_Syntax.typ_parameter_of_phi_ty bvtys T_term
      val N = length T_params
      val ([TY_name], ctxt) = Variable.variant_fixes ["TY"] ctxt
      val TY_ty = fold (fn _ => fn X => \<^Type>\<open>TY\<close> --> X) T_params \<^Type>\<open>TY\<close>
      val TY = Free(TY_name, TY_ty)
            |> fold_index (fn (i,_) => fn X => X $ Bound (N - 1 - i)) T_params

      val T_term = Term.incr_boundvars N T_term
      val bvtys = List.tabulate (N, K \<^Type>\<open>TY\<close>) @ bvtys
      val T_params = Phi_Syntax.typ_parameter_of_phi_ty bvtys T_term

      val rule = HOLogic.Trueprop $ (\<^Const>\<open>Semantic_Type x_ty\<close> $ T_term $ TY)
              |> fold_rev (fn (j,((rev_args, x, _), T'h)) => fn XX =>
                  let val arity = length rev_args
                      val T' = fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) rev_args T'h
                   in HOLogic.Trueprop $ (\<^Const>\<open>Semantic_Type x\<close> $ T' $ Bound j)
                   |> fold (fn ty => fn X => \<^Const>\<open>Pure.all ty\<close> $ Abs("A", ty, X)) rev_args
                   |> (fn X => \<^Const>\<open>Pure.imp\<close> $ X $ XX)
                  end
                ) (map_index I T_params)
              |> fold_index (fn (i,_) => fn X =>
                    \<^Const>\<open>Pure.all \<^Type>\<open>TY\<close>\<close> $ Abs ("TY\<^sub>" ^ string_of_int i, \<^Type>\<open>TY\<close>, X) ) T_params
              |> fold_index (fn (i,ty) => fn X =>
                    \<^Const>\<open>Pure.all ty\<close> $ Abs ("T\<^sub>" ^ string_of_int (M-1-i), ty, X) ) rev_args
   in (rule, ctxt)
  end

fun get_name (Free (N,_)) = SOME N
  | get_name (X $ _) = get_name X
  | get_name _ = NONE

fun existing_sematic_types (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = existing_sematic_types X
  | existing_sematic_types (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = existing_sematic_types X
  | existing_sematic_types (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = existing_sematic_types X
  | existing_sematic_types (Abs (_, _, X)) = existing_sematic_types X
  | existing_sematic_types (Const(\<^const_name>\<open>Semantic_Type\<close>, _) $ X $ _) = get_name X
  | existing_sematic_types (Const(\<^const_name>\<open>Inhabited\<close>, _) $ X) = get_name X
  | existing_sematic_types _ = NONE

fun is_val_T ty =
  case try dest_parameterized_phi_ty ty
    of SOME (_, _, \<^Type>\<open>VAL\<close>) => true
     | _ => false

fun is_val_Tm ex (Free (N, ty)) = not (member (op = ) ex N) andalso is_val_T ty
  | is_val_Tm _  _ = false

in

val _ = Theory.setup (Context.theory_map (
  Phi_Toplevel.Infer_Requirements.add 100 (fn spec => fn {parse_ctxt, new_requirements} =>
    let val annotated_typs = map_filter (existing_sematic_types o #1 o #2)
                                        (#existing_requirements spec)
        val (prems,_,ctxt) = 
            Phi_Help.fold_aterms' (fn bvs => fn T => fn (prems,visited,ctxt) =>
                    if is_val_Tm visited T
                    then let
                         val (sprem,ctxt) = sem_rule_expr' bvs T ctxt
                         val iprem = Phi_Type_Derivers.inh_rule_expr bvs T
                       in (((Binding.empty, []), (sprem, [])) ::
                           ((Binding.empty, []), (iprem, [])) ::
                            prems,
                          Term.term_name T :: visited,
                          ctxt)
                      end
                    else (prems,visited,ctxt)
                ) [] (#arg spec) ([],annotated_typs,parse_ctxt)
     in {parse_ctxt = ctxt,
         new_requirements = prems @ new_requirements}
    end
    )
))

end