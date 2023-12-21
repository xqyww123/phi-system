local open Phi_Type Phi_Type_Derivers
in
val _ = Theory.setup (Context.theory_map (
  PLPR_Template_Properties.add_template false (
      [SOME \<^pattern_prop>\<open>Transformation_Functor _ _ _ _ _ _ _\<close>], \<^here>,
       PLPR_Template_Properties.Free_Action (
  fn (pos, (_, [SOME (_, prop0)])) => fn ctxt00 =>
    let val ctxt0' = Context.proof_of ctxt00

        val prop = prop0 RS' (ctxt0',
              @{lemma' \<open>Transformation_Functor (F::('a,'b) \<phi> \<Rightarrow> ('c,'d) \<phi>) (F'::('a,'b) \<phi> \<Rightarrow> ('c,'d) \<phi>)
                                               T U D R m
                    \<Longrightarrow> Transformation_Functor F F' T U D R m\<close>
                   by this})
        val (F, F', oprs) =
           case Thm.concl_of prop
             of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Transformation_Functor\<close>, _) $ _ $ _ $ _ $ _ $ D $ R $ M )
                  => (Thm.cconcl_of prop |> Thm.dest_arg |> funpow 5 Thm.dest_fun |> Thm.dest_arg1,
                      Thm.cconcl_of prop |> Thm.dest_arg |> funpow 4 Thm.dest_fun |> Thm.dest_arg1,
                      [D,R,M])
              | _ => error "BUG DVk0ZhcwRxmx3ksmx7Ri2w"
        val base_name = Term.term_name (Term.head_of (Thm.term_of F))


        val ctxt0 = ctxt0'
                 |> Context_Position.set_visible false
                 |> load_simpset oprs
                 |> (fn ctxt => ctxt addsimps Expansion.simp_rules ctxt)
                 |> Context_Position.restore_visible ctxt0'  

        fun incr_term_idx_only d (Var ((N,i),T)) = Var ((N,i+d),T)
          | incr_term_idx_only d (A $ B) = incr_term_idx_only d A $ incr_term_idx_only d B
          | incr_term_idx_only d (Abs (N, Ty, X)) = Abs (N, Ty, incr_term_idx_only d X)
          | incr_term_idx_only _ X = X
        val idx = Thm.maxidx_of_cterm F + 1

        val T_ty = Thm.dest_ctyp0 (Thm.ctyp_of_cterm F)
        val x_ty = Thm.dest_ctyp0 (Thm.dest_ctyp1 (Thm.ctyp_of_cterm F))
        val T  = Thm.var (("T" , idx+idx), T_ty)
        val T' = Thm.var (("U", idx+idx), T_ty)
        val x  = Thm.var (("x" , idx+idx), x_ty)
        val x' = Thm.var (("y", idx+idx), x_ty)

        val ((_,F_thms),ctxt) = Variable.import true (map Drule.mk_term [F, F', T, T', x, x']) ctxt0
        val [Fi, Fi', Ti, Ti', xi, xi'] = map Drule.dest_term F_thms

        fun gen_eqs rets (Abs (_, _, X), Abs (_, _, X')) = gen_eqs rets (X, X')
          | gen_eqs rets (X $ Bound _, X' $ Bound _) = gen_eqs rets (X, X')
          | gen_eqs rets (X $ A, X' $ A') =
              gen_eqs (\<^Const>\<open>HOL.eq \<open>Term.fastype_of A\<close>\<close> $ A $ A' :: rets) (X, X')
          | gen_eqs rets _ = Phi_Help.list_mk_conj rets

        val eqs = Thm.cterm_of ctxt (gen_eqs [] (Thm.term_of Fi, Thm.term_of Fi'))

        val rulexx = Thm.transfer' ctxt @{thm' function_congruence_template}
                |> Drule.infer_instantiate ctxt
                      [(("eqs",0),eqs), (("F",0), Fi), (("F'",0), Fi'), (("T",0), Ti),
                       (("U",0), Ti') , (("x",0), xi), (("y" ,0), xi')]
        val rule = rulexx OF [prop, prop]
        val rule = rule
                |> Phi_Reasoner.reason NONE NONE ctxt
                |> (fn SOME ret => ret
                          |> oblg_solver (base_name ^ "/function-congruence") NONE ctxt 
                     | NONE => raise Automation_Fail (fn () => let open Pretty in
                                 [para "Fail to derive the congruence rule for Isabelle function package.",
                                  Thm.pretty_thm ctxt rule]
                               end))
                |> Conv.gconv_rule (Simplifier.rewrite (ctxt addsimps @{thms' sing_times_sing sing_if})) 3
                |> snd o PLPR_Syntax.rulify_antecedents false ~1 ctxt
                |> singleton (Variable.export ctxt ctxt0)
                |> Drule.zero_var_indexes
        val _ = Phi_Reasoner.info_pretty_generic ctxt00 0 (fn () => let open Pretty in
                  chunks [str "Setup congruence rule for Isabelle function package",
                          Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt00 rule]
                end)
     in ctxt00
     |> Function_Context_Tree.add_function_cong rule
     |> local_note_properties' base_name [(Binding.make ("fundef_cong", pos), [rule])]
    end))))
end