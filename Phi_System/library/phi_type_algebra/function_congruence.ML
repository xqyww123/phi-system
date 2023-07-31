local open Phi_Type_Algebra Phi_Type_Algebra_Derivers
in
val _ = Theory.setup (Context.theory_map (
  add_automation_on_property (99, [\<^const_name>\<open>Transformation_Functor\<close>]) (fn (phiopr, _, props) => fn ctxt =>
    let val oprs = case Thm.concl_of (hd props)
                     of _ (*Trueprop*) $ (_ (*Transformation_Functor*) $ _ $ _ $ D $ R $ M ) => [D,R,M]
                      | _ => error "BUG DVk0ZhcwRxmx3ksmx7Ri2w"
        val ctxt' = Context.proof_of ctxt
                 |> load_simpset oprs
                 |> (fn ctxt => ctxt addsimps Simps.simp_rules ctxt)
        val rule = (Thm.transfer'' ctxt @{thm' function_congruence_template} OF props)
                |> Phi_Reasoner.reason NONE true ctxt'
                |> (fn SOME ret => ret
                     | NONE => raise Automation_Fail "Fail to derive the congruence rule for Isabelle function package\n\
                                  \A proof obligation fails to be solved.\n\
                                  \The domain of the Transformation Functor seems not to be the subset of its domain\n\
                                  \nor the relation mapper is not equality preserved (\<open>mapper (=) = (=)\<close>).")
                |> Conv.gconv_rule (Phi_Conv.unfold_meta_ball_default ctxt') 2
        val _ = Phi_Reasoner.info_pretty_generic ctxt 1 (fn () => let open Pretty in
                  chunks [str "Setup the congruence rule for Isabelle function package",
                          Context.cases Thm.pretty_thm_global Thm.pretty_thm ctxt rule]
                end)
     in ctxt
     |> Function_Context_Tree.add_function_cong rule
    end)))
end