local open Phi_Type

val rule1 = @{lemma \<open>Parameter_Variant_of_the_Same_TypOpr Fa Fb\<close>
                 by (simp add: Parameter_Variant_of_the_Same_TypOpr_def)}

in
val _ = Theory.setup (Context.theory_map (
  Phi_Type.Defining_Phi_Type.add 100 (fn phi => fn thy =>
    let val ctm0 = Drule.dest_term (#cterm phi)

        (*pad arguments*)
        val ctm = let val (tys', _) = Thm.strip_type (Thm.ctyp_of_cterm ctm0)
                      val tys = Phi_Help.front tys'
                      val idx = Thm.maxidx_of_cterm ctm0 + 1
                      val args = map_index (fn (i, ty) => Thm.var (("a", idx+i), ty)) tys
                   in fold (fn a => fn f => Thm.apply f a) args ctm0
                  end

        fun mk_rule rule F_tm =
          let val protect_tvars = fold (fn (_,T) => fn L =>
                                      fold (fn (N,_) => fn L' => insert (op =) N L')
                                           (Term.add_tvarsT T []) L)
                                   (Term.add_vars F_tm []) []
              val F_ctm = Thm.cterm_of thy F_tm
              val d = Thm.maxidx_of_cterm F_ctm + 1
              val F_ctm' =
                    Term.map_types (Term.map_atyps (
                            fn T as TVar ((N,i),S) =>
                                  if member (op =) protect_tvars (N,i) then T else TVar ((N,i+d),S)
                             | T => T)) F_tm
                      |> Thm.cterm_of thy

           in try (Drule.infer_instantiate thy [(("Fa",d+d), F_ctm ), (("Fb",d+d), F_ctm')])
                  (Thm.incr_indexes (d+d) rule)
          end

        fun mk_variant_of_type_operator ctm =
          map_filter (mk_rule @{thm' Type_Variant_of_the_Same_Type_Operator_I} o #2)
            (Seq.list_of (separate_tyopr_and_its_typ_param_safe [] (Thm.term_of ctm)))

        fun mk_variant_of_type_operator2 ctm =
          case Thm.term_of ctm
            of F $ _ $ _ =>
              the_list (mk_rule @{thm' Type_Variant_of_the_Same_Type_Operator2_I} F)
             | _ => []

        fun mk_variant_of_scalar_mul F_s_T =
           case separate_module_tyopr [] F_s_T
             of SOME (Var _, Var _, F) =>
                     (*\<open>Var\<close> excludes recognizing fixed parameters of a locale to be a scalar*)
                     the_list (mk_rule @{thm' Type_Variant_of_the_Same_Scalar_Mul_I} F) @
                     the_list (mk_rule @{thm' Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_I'} F)
              | _ => (
           case separate_scalar_tyopr [] F_s_T
             of SOME (_, Var _, F) => the_list (mk_rule @{thm' Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_I}
                                                        (Envir.beta_eta_contract F))
              | _ => [])


      fun mk_parameter_variant Fa =
          let val Fb = Thm.incr_indexes_cterm (Thm.maxidx_of_cterm Fa + 1) Fa
           in \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm Fa\<close> and 'b=\<open>Thm.ctyp_of_cterm Fb\<close> and Fa and Fb
                           in lemma \<open>Parameter_Variant_of_the_Same_Type Fa Fb\<close>
                                 by (simp add: Parameter_Variant_of_the_Same_Type_def)\<close>
          end

      fun mk_parameter_variant_typopr Fa =
        separate_tyopr_and_its_typ_param_safe [] (Thm.term_of (Thm.incr_indexes_cterm 1 Fa))
          |> Seq.map (fn (_,F) =>
          let val Fa = Thm.cterm_of thy F
              val Fb = Thm.incr_indexes_cterm (Thm.maxidx_of_cterm Fa + 1) Fa
           in Drule.infer_instantiate thy [(("Fa",0),Fa), (("Fb",0),Fb)] rule1
          end
          ) |> Seq.list_of
(*
        fun mk_parameter_variant1 ctm =
          map (fn (_,F) =>
                let val Fa = Thm.incr_indexes_cterm 1 (Thm.cterm_of ctxt' F)
                    val Fb = Thm.incr_indexes_cterm (Thm.maxidx_of_cterm Fa + 1) Fa
                 in Drule.infer_instantiate ctxt' [(("Fa",0),Fa), (("Fb",0),Fb)]
                      @{lemma' \<open>Parameter_Variant_of_the_Same_Type1 Fa Fb\<close>
                           by (simp add: Parameter_Variant_of_the_Same_Type1_def)}
                end)
              (separate_tyopr_and_its_non_parameterized_typ_param_safe (Thm.term_of ctm))
*)
      (*fun mk_parameter_variants tm =
          let val d = Thm.maxidx_of_cterm tm + 1
              val tm' = Thm.incr_indexes_cterm d tm
              val rule = Drule.infer_instantiate ctxt' [(("Fa",d+d), tm ), (("Fb",d+d), tm')]
                             (Thm.incr_indexes (d+d) @{thm Parameter_Variant_of_the_Same_Type_I})
           in [rule]
          end*)

        val rules = mk_variant_of_type_operator  ctm (*@ mk_parameter_variants ctm*)
                  @ mk_variant_of_type_operator2 ctm
                  @ mk_variant_of_scalar_mul (Thm.term_of ctm)
                  @ [mk_parameter_variant ctm]
                  @ mk_parameter_variant_typopr ctm
                (*@ mk_parameter_variant1 ctm
                  @ [mk_parameter_variant ctm]*)
     in thy
     |> Local_Theory.declaration {syntax=false,pervasive=false, pos = #pos phi} (fn m => fn lthy => lthy
          |> Config.map_generic Phi_Reasoner.trace (fn i => i-1)
          |> Phi_Reasoner.add_rules (
                map (fn rule => ([rule], \<^here>, Phi_Reasoner.NORMAL_LOCAL_CUT',
                                 SOME @{reasoner_group %variants_of_type_opr}, [], [], NONE))
                    (Morphism.fact m rules))
          |> Config.map_generic Phi_Reasoner.trace (fn i => i+1)
     )
    end)
))
end