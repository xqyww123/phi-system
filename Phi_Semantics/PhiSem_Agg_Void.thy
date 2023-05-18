theory PhiSem_Agg_Void
  imports PhiSem_Aggregate_Base PhiSem_Void
begin

debt_axiomatization
    valid_idx_step_void[eval_aggregate_path] : \<open>valid_idx_step void i \<longleftrightarrow> False\<close>


end