structure Semantic_Type_Tools = struct

fun conv_sem_rule_expr is_weak =
  let fun norm_hint ((A as Const(\<^const_name>\<open>Trueprop\<close>, _)) $ X) = A $ norm_hint X
        | norm_hint (origin as \<^Const>\<open>Semantic_Type ty\<close> $ T $ TY) =
            if is_weak then \<^Const>\<open>Semantic_Type ty\<close> $ T $ TY
                       else origin
        | norm_hint (origin as \<^Const>\<open>Semantic_Type ty\<close> $ T $ TY) =
            if is_weak then origin
                       else \<^Const>\<open>Semantic_Type ty\<close> $ T $ TY
        | norm_hint X = X
   in Phi_Conv.map_hhf norm_hint
  end

val strong_to_weak = @{lemma
  \<open> Semantic_Type T TY
\<Longrightarrow> Semantic_Type T TY \<close>
  by (unfold Semantic_Type_def, blast)}

fun conv_sem_rule is_weak ctxt rule =
  let fun tac s = REPEAT_DETERM (Method.insert_tac ctxt [rule] 1 THEN
                ares_tac ctxt [strong_to_weak] 1) s
      val expr = conv_sem_rule_expr is_weak (Thm.prop_of rule)
      val [rule'] = Goal.prove_common ctxt NONE [] [] [expr] (K tac)
   in rule'
  end

end