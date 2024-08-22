theory PhiSem_Void
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantics\<close>

debt_axiomatization \<v>\<o>\<i>\<d> :: TY
               and \<v>\<o>\<i>\<d>V :: VAL
  where WT_void  [simp]: \<open>Well_Type \<v>\<o>\<i>\<d> = {\<v>\<o>\<i>\<d>V} \<close>

lemma \<v>\<o>\<i>\<d>_neq_\<p>\<o>\<i>\<s>\<o>\<n>[simp]: \<open>\<v>\<o>\<i>\<d> \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  using WT_void by force

lemma \<p>\<o>\<i>\<s>\<o>\<n>_neq_\<v>\<o>\<i>\<d>[simp]: \<open>\<p>\<o>\<i>\<s>\<o>\<n> \<noteq> \<v>\<o>\<i>\<d>\<close>
  using \<v>\<o>\<i>\<d>_neq_\<p>\<o>\<i>\<s>\<o>\<n> by force 

end