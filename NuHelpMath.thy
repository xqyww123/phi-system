theory NuHelpMath
  imports Main
begin
text \<open>Supplementary mathematical notions for the \<nu>-system\<close>

notation rel_prod (infixr "\<times>\<^sub>r" 80)
notation pred_prod (infixr "\<times>\<^sub>p" 80)

lemma pair_exists: "Ex P \<longleftrightarrow> (\<exists>a b. P (a,b))" using split_paired_Ex .
lemma pair_forall: "All P \<longleftrightarrow> (\<forall>a b. P (a,b))" using split_paired_All .
lemmas pair_All = split_paired_all

lemma conj_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)" by rule simp+
end