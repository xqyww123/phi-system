theory Phi_Spec_Pre
  imports Main
begin



(* definition Pure_When :: \<open>'a set \<Rightarrow> bool \<Rightarrow> 'a set\<close> (infixl "\<when>" 15)
  where \<open> (T \<when> P) = {p. P \<longrightarrow> p \<in> T}\<close>

lemma Pure_When_expn[simp]:
  \<open> p \<in> (T \<when> P) \<longleftrightarrow> (P \<longrightarrow> p \<in> T) \<close>
  unfolding Pure_When_def by simp

lemma [simp]:
  \<open> (T \<when> True) = T \<close>
  \<open> (T \<when> False) = UNIV \<close>
  unfolding Pure_When_def set_eq_iff
  by simp+ *)


end