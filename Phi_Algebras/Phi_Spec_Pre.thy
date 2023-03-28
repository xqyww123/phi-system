theory Phi_Spec_Pre
  imports Main
begin

definition Subjection :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<s>\<u>\<b>\<j>" 15)
  where " (T \<s>\<u>\<b>\<j> P) = {p. p \<in> T \<and> P}"

lemma Subjection_expn:
  "p \<in> (T \<s>\<u>\<b>\<j> P) \<longleftrightarrow> p \<in> T \<and> P"
  unfolding Subjection_def by simp


end