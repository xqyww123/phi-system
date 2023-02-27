signature PHISEM_CONTROL_FLOW = sig

val basic_recursive_mod : (Proof.context -> 'a list -> term list)
                       -> binding (*to bind the recursive func*)
                       -> 'a list -> context_state -> context_state

end

structure PhiSem_Control_Flow : PHISEM_CONTROL_FLOW = struct

fun basic_recursive_mod prep_vars binding raw_vars (ctxt0,sequent0) =
  let
    val sequent = sequent0
              |> Conv.fconv_rule (let open Phi_Helper_Conv Conv in
                    leading_antecedent_conv (meta_all_body_conv (fn ctxt =>
                                  aggregate_imps_obj (K all_conv) ctxt
                        then_conv protect_conv
                      ) ctxt0)
                 end)
    val (qvs,_, proc01) = Phi_Help.leading_antecedent (Thm.prop_of sequent)

    val (qv_names, ctxt'01) = Variable.add_fixes (map fst qvs) ctxt0
    val qvars = map2 (fn N => fn (_,T) => Free (N,T)) qv_names qvs
    val ctxt = fold Variable.declare_term qvars ctxt'01
    val vars = prep_vars ctxt raw_vars
    val proc01' = subst_bounds (rev qvars, proc01)

    val (_(*Pure.prop*) $ (_ (*imp*) $ (\<^const>\<open>Trueprop\<close> $ PP) $ proc02)) = proc01'
    val proc0 = case proc02
                  of \<^const>\<open>Trueprop\<close> $ (X as Const(\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _)
                       => X
                   | X => raise TERM ("The leading subgoal is not a procedure", [X])

    val (_,X,Y,E) = Phi_Syntax.dest_procedure proc0
    val (v,X'0) = Procedure_Syntax.package_values "" \<^typ>\<open>unit\<close> true NONE X
    val sem_args  = Procedure_Syntax.dest_arg_tuple v
    val arg_tys = map Term.fastype_of sem_args
    val names = map (Variable.revert_fixed ctxt o Term.term_name) sem_args
    val names_ty  = Thm.ctyp_of ctxt (Phi_Syntax.mk_name_tylabels names)
    fun pack_x term = term
            |> fold_rev (fn x => fn B => Abs (Variable.revert_fixed ctxt (Term.term_name x),
                                              Term.fastype_of x,
                                              abstract_over (x, B))
                        ) vars
            |> QuantExpansion.aggregate_vars_lambda (length vars) |> snd
            |> Thm.cterm_of ctxt
    val (X',Y',E',PP') = (pack_x X'0, pack_x Y, pack_x E, pack_x PP)
    val v' = Thm.cterm_of ctxt v

    val var_names_ty = Phi_Syntax.mk_name_tylabels
                          (map (Variable.revert_fixed ctxt o Term.term_name) vars)
    val var_tup = Phi_Syntax.mk_named_tag (HOLogic.mk_tuple vars) var_names_ty
                |> Thm.cterm_of ctxt

    val arg_ty = Thm.typ_of_cterm v'             |> Procedure_Syntax.dest_argT
    val ret_ty = domain_type (Term.fastype_of Y) |> Procedure_Syntax.dest_argT
    val _ = if arg_ty <> ret_ty
            then error (Pretty.string_of (Pretty.chunks [
                  Pretty.para "The argument arity and the return arity has to be identical\
                             \ in a recursive procedure!",
                  Pretty.item [Pretty.str "Argument: ", Syntax.pretty_typ ctxt arg_ty],
                  Pretty.item [Pretty.str "Return  : ", Syntax.pretty_typ ctxt ret_ty]
                ]))
            else ()

    val N = length sem_args
    val f_T = Phi_Syntax.mk_proc'T arg_ty ret_ty
          --> fold_rev (curry (op -->)) arg_tys (Phi_Syntax.mk_procT ret_ty)
    fun add_bounds N X = if N <= 0 then X else add_bounds (N-1) (X $ Bound (N-1))
    fun add_cases  N X =
            if N <= 0 then X else Const (\<^const_name>\<open>\<phi>V_case_prod\<close>, dummyT) $ Abs ("", dummyT, X)
    val [(F_name,())] = Variable.variant_frees ctxt [] [("F",())]
    val f' = Abs ("\<f>", Phi_Syntax.mk_proc'T arg_ty ret_ty,
              add_cases (N-1) (add_bounds (N-1) (Var ((F_name,0), f_T) $ Bound (N-1))))
          |> Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)
          |> Thm.cterm_of ctxt

    val label = Phi_Syntax.mk_label_c (Binding.name_of binding)

    val simp_ctxt = clear_simpset ctxt
              addsimps (@{thms \<phi>V_simps named.case prod.sel id_apply} @
                        QuantExpansion.aux_expansions ctxt)
              addsimprocs [QuantExpansion.named_metaAll,
                           QuantExpansion.named_forall]
    fun spec thm = spec (thm RS @{thm spec})
                   handle THM _ => thm
    val rule = @{thm "__op_recursion__"}
            |> Thm.instantiate (TVars.make [((("'names",0), \<^sort>\<open>type\<close>), names_ty)], Vars.empty)
            |> Drule.infer_instantiate ctxt [(("X",0),X'), (("Y",0),Y'), (("E",0),E'),
                                             (("v",0),v'), (("F",0),f'), (("label",0),label),
                                             (("x",0),var_tup), (("P",0),PP')]
            |> Simplifier.full_simplify simp_ctxt
            |> spec
            |> singleton (Proof_Context.export ctxt ctxt0)

    val norm_sequent = Phi_Help.rewrite_leading_antecedent simp_ctxt sequent
    val sequent1 = (rule RS norm_sequent)
                |> Conv.gconv_rule (let open Phi_Helper_Conv Conv in
                    meta_all_body_conv (fn ctxt =>
                        implies_conv all_conv (implies_conv (
                            Phi_Syntax.labelled_conv (arg_conv (meta_all_body_conv (
                                expand_aggregated_imps_obj (K (try_conv Phi_Syntax.elim_labelled
                                                              then_conv try_conv (rewr_conv @{thm HIDDEN_PREM_def})))
                            ) ctxt))
                          ) all_conv)
                        then_conv expand_aggregated_imps_obj (K all_conv) ctxt
                      ) ctxt
                 end) 1
  in (ctxt, sequent1)
  end

end