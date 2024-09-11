theory PhiSem_Agg_Void
  imports PhSm_Ag_Base PhiSem_Void
begin

debt_axiomatization
    valid_idx_step_void[eval_aggregate_path] : \<open>valid_idx_step \<v>\<o>\<i>\<d> i \<longleftrightarrow> False\<close>

lemma valid_index_void[iff]:
  \<open>valid_index \<v>\<o>\<i>\<d> path \<longleftrightarrow> path = []\<close>
  by (induct path; simp add: valid_idx_step_void)

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> path = []
\<Longrightarrow> valid_index \<v>\<o>\<i>\<d> path\<close>
  unfolding Premise_def
  by simp


end