theory PhiSem_Agg_Void
  imports PhiSem_Aggregate_Base PhiSem_Void
begin

debt_axiomatization
    valid_idx_step_void[eval_aggregate_path] : \<open>valid_idx_step void i \<longleftrightarrow> False\<close>

lemma valid_index_void[iff]:
  \<open>valid_index void path \<longleftrightarrow> path = []\<close>
  by (induct path; simp add: valid_idx_step_void)

lemma [\<phi>reason 1000]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> path = []
\<Longrightarrow> valid_index void path\<close>
  unfolding Premise_def
  by simp

end