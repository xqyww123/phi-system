signature PHISEM_CONTROL_FLOW = sig

val mk_parameterized_schematic_proc : (typ -> typ)
                                   -> (int -> (term -> term) -> term -> term)
                                   -> Proof.context -> typ -> typ -> string -> term

val basic_recursive_mod : (Proof.context -> 'a list -> term list)
                       -> binding (*to bind the recursive func*)
                       -> 'a list -> context_state -> context_state

val is_constructing_recursive_procedure : Proof.context -> bool

structure Applying_Recursive_Modifier : HOOKS

end

structure PhiSem_Control_Flow : PHISEM_CONTROL_FLOW = struct

(*arg_ty, ret_ty: not wrapped by \<phi>arg*)
fun mk_parameterized_schematic_proc mk_T mk_F ctxt arg_ty ret_ty var_name =
  let
    val arg_tys = HOLogic.strip_tupleT arg_ty
    val N = length arg_tys
    val f_T0 = (if null arg_tys
               then (fn T => \<^typ>\<open>unit \<phi>arg\<close> --> T)
               else fold_rev (curry (op -->) o Procedure_Syntax.mk_argT) arg_tys)
              (Phi_Syntax.mk_procT ret_ty)
    val f_T = mk_T f_T0
    fun add_bounds N X = if N <= 0 then X else add_bounds (N-1) (X $ Bound (N-1))
    fun add_cases  N X =
          if N <= 0 then X
          else Const (\<^const_name>\<open>\<phi>V_case_prod\<close>, dummyT) $ Abs ("", dummyT, add_cases (N-1) X)
    val [(F_name,())] = Variable.variant_frees ctxt [] [(var_name,())]
    val var_F = Var ((F_name,0), f_T)
    val f' = mk_F (N-1) (add_cases (N-1) o add_bounds (N-1)) var_F
          |> Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)
   in f' end


structure Is_Recursive = Proof_Data (
  type T = bool
  val init = K false
)

val is_constructing_recursive_procedure = Is_Recursive.get

val _ = Phi_Toplevel.Finishing_Construction_Hooks.add 100 (fn () =>
          apfst (Is_Recursive.put false))

structure Applying_Recursive_Modifier = Hooks (type arg = unit
                                               type state = context_state)

fun basic_recursive_mod prep_vars binding raw_vars (ctxt01,sequent01) =
  let
    val _ = if is_constructing_recursive_procedure ctxt01
            then error "the procedure has already been declared recursive"
            else ()
    val (ctxt0,sequent0) = (ctxt01,sequent01)
          |> Applying_Recursive_Modifier.invoke (Context.Proof ctxt01) ()
          |> apfst (Is_Recursive.put true)
    val sequent = sequent0
                  (*first pack all premises*)
              |> Conv.gconv_rule (let open Phi_Helper_Conv Conv in
                   meta_all_body_conv (fn ctxt =>
                                aggregate_imps_obj (K all_conv) ctxt
                      then_conv protect_conv
                    ) ctxt0
                 end) 1
    val (_,_,proc01',ctxt) = Phi_Help.fix_leading_antecedent_meta_quantifiers ctxt0 (Thm.prop_of sequent)

    val (_(*Pure.prop*) $ (_ (*imp*) $ (\<^const>\<open>Trueprop\<close> $ PP) $ proc02)) = proc01'
    val proc0 = case proc02
                  of \<^const>\<open>Trueprop\<close> $ (X as Const(\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _)
                       => X
                   | X => raise TERM ("The leading subgoal is not a procedure", [X])

    val (_,X,Y,E) = Phi_Syntax.dest_procedure proc0
    (* pack concrete arguments *)
    val (v,X'0) = Procedure_Syntax.package_values "" \<^typ>\<open>unit\<close> true NONE X
    val v' = Thm.cterm_of ctxt v
    val sem_args  = Procedure_Syntax.dest_arg_tuple v
    val names = map (Variable.revert_fixed ctxt o Term.term_name) sem_args
    val names_ty  = Thm.ctyp_of ctxt (Phi_Syntax.mk_name_tylabels names)

    (* by the way, check the arity *)
    val arg_ty = Thm.typ_of_cterm v'             |> Procedure_Syntax.dest_argT
    val ret_ty = domain_type (Term.fastype_of Y) |> Procedure_Syntax.dest_argT
   (* val _ = if arg_ty <> ret_ty
            then error (Pretty.string_of (Pretty.chunks [
                  Pretty.para "The argument arity and the return arity has to be identical\
                             \ in a recursive procedure!",
                  Pretty.item [Pretty.str "Argument: ", Syntax.pretty_typ ctxt arg_ty],
                  Pretty.item [Pretty.str "Return  : ", Syntax.pretty_typ ctxt ret_ty]
                ]))
            else () *)


    (* pack abstract recursive variables *)
    val vars = prep_vars ctxt raw_vars
    val var_names_ty = Phi_Syntax.mk_name_tylabels
                          (map (Variable.revert_fixed ctxt o Term.term_name) vars)
    val var_tup = Phi_Syntax.mk_named_tag (HOLogic.mk_tuple vars) var_names_ty
                |> Thm.cterm_of ctxt
    fun pack_x term = term
            |> fold_rev (fn x => fn B => Abs (Variable.revert_fixed ctxt (Term.term_name x),
                                              Term.fastype_of x,
                                              abstract_over (x, B))
                        ) vars
            |> QuantExpansion.aggregate_vars_lambda (length vars) |> snd
            |> Thm.cterm_of ctxt
    (*by the way we get the instantiations of X Y E and P*)
    val (X',Y',E',PP') = (pack_x X'0, pack_x Y, pack_x E, pack_x PP)

    (* Make other instantiations of the rule *)
    val f' = mk_parameterized_schematic_proc
                  (fn T => Phi_Syntax.mk_proc'T arg_ty ret_ty --> T)
                  (fn N => fn mk => fn tm =>
                        Abs ("\<f>", Phi_Syntax.mk_proc'T arg_ty ret_ty,
                             mk (tm $ Bound (Int.max (N,0)))))
                  ctxt arg_ty ret_ty "F"
          |> Thm.cterm_of ctxt

    val label = Phi_Syntax.mk_label_c (Binding.name_of binding)

    (* With all instantiations, we can prepare the rule *)
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

    val norm_sequent = Phi_Helper_Conv.simplify_leading_antecedent simp_ctxt sequent
    val sequent1 = (rule RS norm_sequent)
                   (*unpack compressed premises*)
                |> Conv.gconv_rule (let open Phi_Helper_Conv Conv in
                    meta_all_body_conv (fn ctxt =>
                        implies_conv all_conv (implies_conv (
                            Phi_Syntax.labelled_conv (arg_conv (meta_all_body_conv (
                                expand_aggregated_imps_obj (K (try_conv Phi_Syntax.elim_labelled (*Labelled_def*)
                                                              then_conv try_conv (rewr_conv @{thm Technical_def})))
                            ) ctxt))
                          ) all_conv)
                        then_conv expand_aggregated_imps_obj (K all_conv) ctxt
                      ) ctxt
                 end) 1
  in (ctxt0, sequent1)
  end

end