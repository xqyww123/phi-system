theory Phi_Spec_Pre
  imports Main
begin

definition Subjection :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<s>\<u>\<b>\<j>" 15)
  where " (T \<s>\<u>\<b>\<j> P) = {p. p \<in> T \<and> P}"

lemma Subjection_expn:
  "p \<in> (T \<s>\<u>\<b>\<j> P) \<longleftrightarrow> p \<in> T \<and> P"
  unfolding Subjection_def by simp

lemma Subjection_Id_on:
  \<open>Id_on (S \<s>\<u>\<b>\<j> P) = (Id_on S \<s>\<u>\<b>\<j> P)\<close>
  by (auto simp add: Subjection_expn)

definition ExSet :: " ('c \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "\<exists>*" 14)
  where "ExSet S = {p. (\<exists>c. p \<in> S c)}"
notation ExSet (binder "\<exists>\<^sup>s" 14)

lemma ExSet_expn: "p \<in> ExSet S \<longleftrightarrow> (\<exists>c. p \<in> S c)" unfolding ExSet_def by simp


end