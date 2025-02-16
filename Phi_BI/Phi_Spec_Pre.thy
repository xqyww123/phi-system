theory Phi_Spec_Pre
  imports Main
begin



(* definition Pure_When :: \<open>'a set \<Rightarrow> bool \<Rightarrow> 'a set\<close> (infixl "\<w>\<h>\<e>\<n>" 15)
  where \<open> (T \<w>\<h>\<e>\<n> P) = {p. P \<longrightarrow> p \<in> T}\<close>

lemma Pure_When_expn[simp]:
  \<open> p \<in> (T \<w>\<h>\<e>\<n> P) \<longleftrightarrow> (P \<longrightarrow> p \<in> T) \<close>
  unfolding Pure_When_def by simp

lemma [simp]:
  \<open> (T \<w>\<h>\<e>\<n> True) = T \<close>
  \<open> (T \<w>\<h>\<e>\<n> False) = UNIV \<close>
  unfolding Pure_When_def set_eq_iff
  by simp+ *)


end