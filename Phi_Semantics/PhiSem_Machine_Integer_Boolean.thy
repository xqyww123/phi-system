theory PhiSem_Machine_Integer_Boolean
  imports PhiSem_Machine_Integer
begin

specification (bool) bool_def'[discharging_semantic_debt]:
  \<open>bool = int(1)\<close> by blast

specification (V_bool) V_bool_def'[discharging_semantic_debt]:
    \<open>V_bool = Virtual_Datatype.lift_Field (\<lambda>(_,x). x = 1) (\<lambda>b. (1, if b then 1 else 0)) V_int\<close>
  by blast

hide_fact bool_def V_bool_def

end