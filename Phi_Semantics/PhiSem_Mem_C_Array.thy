theory PhiSem_Mem_C_Array
  imports PhiSem_Mem_C_Base PhiSem_Aggregate_Array
begin

debt_axiomatization
    memobj_size_arr: \<open>MemObj_Size (\<a>\<r>\<r>\<a>\<y>[N] T) = N * MemObj_Size T\<close>
and Map_of_Val_arr: \<open>Map_of_Val (V_array.mk vs) = nnode (map Map_of_Val vs)\<close>


end