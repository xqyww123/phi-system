theory Phi_Spec_Pre
  imports Main
begin

definition Subjection :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<s>\<u>\<b>\<j>" 15)
  where " (T \<s>\<u>\<b>\<j> P) = {p. p \<in> T \<and> P}"

lemma Subjection_expn_set:
  "p \<in> (T \<s>\<u>\<b>\<j> P) \<longleftrightarrow> p \<in> T \<and> P"
  unfolding Subjection_def by simp

lemma Subjection_Id_on:
  \<open>Id_on (S \<s>\<u>\<b>\<j> P) = (Id_on S \<s>\<u>\<b>\<j> P)\<close>
  by (auto simp add: Subjection_expn_set)

lemma Subjection_image:
  \<open>f ` (S \<s>\<u>\<b>\<j> P) = (f ` S \<s>\<u>\<b>\<j> P)\<close>
  by (auto simp add: Subjection_expn_set)

definition ExSet :: " ('x \<Rightarrow> 'c set) \<Rightarrow> 'c set" (binder "\<exists>*" 14)
  where "ExSet S = {p. (\<exists>c. p \<in> S c)}"
notation ExSet (binder "\<exists>\<^sup>s" 14)

lemma ExSet_expn_set: "p \<in> (\<exists>*c. S c) \<longleftrightarrow> (\<exists>c. p \<in> S c)" unfolding ExSet_def by simp

lemma ExSet_Id_on:
  \<open>Id_on (\<exists>*x. S x) = (\<exists>*x. Id_on (S x))\<close>
  by (auto simp add: ExSet_expn_set; blast)

lemma ExSet_image:
  \<open>f ` (\<exists>*c. S c) = (\<exists>*c. f ` S c)\<close>
  by (auto simp add: ExSet_expn_set image_iff Bex_def; blast)

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