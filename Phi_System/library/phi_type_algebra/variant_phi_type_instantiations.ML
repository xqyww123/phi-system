local open Phi_Type_Algebra in
val _ = Theory.setup (Context.theory_map (
  Phi_Type_Algebra.Defining_Phi_Type.add 100 (fn phi => fn thy =>
    let val ctxt' = Context.proof_of thy
        val ctm0 = Drule.dest_term (#cterm phi)

        (*pad arguments*)
        val ctm = let val (tys', _) = Thm.strip_type (Thm.ctyp_of_cterm ctm0)
                      val tys = Phi_Help.front tys'
                      val idx = Thm.maxidx_of_cterm ctm0 + 1
                      val args = map_index (fn (i, ty) => Thm.var (("a", idx+i), ty)) tys
                   in fold (fn a => fn f => Thm.apply f a) args ctm0
                  end

        fun mk_variant_of_type_operator ctm =
          map_filter (fn (_, F_tm) =>
              let val protect_tvars = fold (fn (_,T) => fn L =>
                                          fold (fn (N,_) => fn L' => insert (op =) N L')
                                               (Term.add_tvarsT T []) L)
                                       (Term.add_vars F_tm []) []
                  val F_ctm = Thm.cterm_of ctxt' F_tm
                  val d = Thm.maxidx_of_cterm F_ctm + 1
                  val F_ctm' =
                        Term.map_types (Term.map_atyps (
                                fn T as TVar ((N,i),S) =>
                                      if member (op =) protect_tvars (N,i) then T else TVar ((N,i+d),S)
                                 | T => T)) F_tm
                          |> Thm.cterm_of ctxt'

               in try (Drule.infer_instantiate ctxt' [(("Fa",d+d), F_ctm ), (("Fb",d+d), F_ctm')])
                      (Thm.incr_indexes (d+d) @{thm Type_Variant_of_the_Same_Type_Operator_I})
              end)
            (separate_type_operator_and_its_parameter_safe (Thm.term_of ctm))

      (*fun mk_parameter_variants tm =
          let val d = Thm.maxidx_of_cterm tm + 1
              val tm' = Thm.incr_indexes_cterm d tm
              val rule = Drule.infer_instantiate ctxt' [(("Fa",d+d), tm ), (("Fb",d+d), tm')]
                             (Thm.incr_indexes (d+d) @{thm Parameter_Variant_of_the_Same_Type_I})
           in [rule]
          end*)

        val rules = mk_variant_of_type_operator ctm (*@ mk_parameter_variants ctm*)
     in thy
     |> Phi_Reasoner.add_rules (
          map (fn rule => ([rule], \<^here>, Phi_Reasoner.NORMAL_LOCAL_CUT, 1000, [], [], NONE)) rules)
    end)
))
end