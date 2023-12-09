theory PhiSem_Mem_C_Tuple
  imports PhiSem_Mem_C_Base PhiSem_Aggregate_Tuple
begin

debt_axiomatization
    Map_of_Val_tup: \<open>Map_of_Val (V_tup.mk vs) =
      (\<lambda>path. case path of AgIdx_N i # path' \<Rightarrow> if i < length vs then Map_of_Val (vs!i) path'
                                                else 1
                         | _ \<Rightarrow> 1)\<close>


end