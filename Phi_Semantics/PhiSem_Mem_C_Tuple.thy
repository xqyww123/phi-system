theory PhiSem_Mem_C_Tuple
  imports PhiSem_Mem_C_Base PhiSem_Aggregate_Tuple
begin

debt_axiomatization
    Map_of_Val_tup: \<open>Map_of_Val (V_tup.mk vs) = nnode (map Map_of_Val vs)\<close>


end