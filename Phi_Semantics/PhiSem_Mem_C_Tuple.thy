theory PhiSem_Mem_C_Tuple
  imports PhiSem_Mem_C_Base PhiSem_Aggregate_Tuple
begin

debt_axiomatization
    Mapof_Val_tup: \<open>Mapof_Val (V_tup.mk vs) = nnode (map Mapof_Val vs)\<close>


end