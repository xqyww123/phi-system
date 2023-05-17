theory PhiSem_Mem_Ptr_Machine_Int
  imports PhiSem_Mem_Pointer PhiSem_Machine_Integer
begin

subsection \<open>Instruction\<close>

proc op_get_element_pointer_numidx:
  requires \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[eval_aggregate_path] valid_idx_step TY AG_IDX(#i)\<close>
       and \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[eval_aggregate_path] TY' : idx_step_type AG_IDX(#i) TY\<close>
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close>
  output \<open>addr \<^enum>\<^sub>a LOGIC_IDX(AgIdx_N i) \<Ztypecolon> \<v>\<a>\<l> Ptr TY'\<close>
\<medium_left_bracket>
  $addr semantic_local_value pointer
  $i semantic_local_value \<open>int('b)\<close>
  semantic_return \<open>
     V_pointer.mk (logaddr_to_raw (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)) \<^enum>\<^sub>a LOGIC_IDX(AgIdx_N (snd (V_int.dest (\<phi>arg.dest \<a>\<r>\<g>2))))))
         \<in> (addr \<^enum>\<^sub>a LOGIC_IDX(AgIdx_N i) \<Ztypecolon> Ptr TY')\<close>
  certified by ((insert useful, simp add: \<phi>expns;
        cases \<open>phantom_mem_semantic_type (logaddr_type addr)\<close>;
        simp add: logaddr_to_raw_phantom_mem_type),
        smt logaddr_to_raw_phantom_mem_type rawaddr_to_log_def someI_ex,
        force)
\<medium_right_bracket> .


end