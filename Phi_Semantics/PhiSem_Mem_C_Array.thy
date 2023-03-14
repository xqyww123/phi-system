theory PhiSem_Mem_C_Array
  imports PhiSem_Mem_C_Base PhiSem_Aggregate_Array
begin

debt_axiomatization
    memobj_size_arr: \<open>MemObj_Size (array N T) = N * MemObj_Size T\<close>
and Mapof_Val_arr: \<open>Mapof_Val (V_array.mk vs) = nnode (map Mapof_Val vs)\<close>


end