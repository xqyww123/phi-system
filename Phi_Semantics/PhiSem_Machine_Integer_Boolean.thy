theory PhiSem_Machine_Integer_Boolean
  imports PhiSem_Machine_Integer
begin

specification (\<b>\<o>\<o>\<l>)
  bool_def'[discharging_semantic_debt]: \<open>\<b>\<o>\<o>\<l> = int(1)\<close> by blast

specification (sem_mk_bool)
  sem_mk_bool_def'[discharging_semantic_debt]: \<open>sem_mk_bool b = sem_mk_int (1, if b then 1 else 0)\<close>
  by fastforce

specification (sem_dest_bool)
  sem_dest_bool'[discharging_semantic_debt]:
    \<open>sem_dest_bool v = (snd (sem_dest_int v) = 1)\<close>
  by fastforce


end