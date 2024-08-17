theory PhiSem_Mem_C_MI \<comment> \<open>MI: Machine Integer\<close>
  imports PhiSem_Mem_C PhiSem_Machine_Integer PhiSem_Aggregate_Array
begin


debt_axiomatization
      MemObj_Size_int: \<open>MemObj_Size (sem_int_T n) = 0 \<longleftrightarrow> n = 0\<close>

lemma phantom_mem_semantic_type_\<a>\<i>\<n>\<t>[simp]:
  \<open> phantom_mem_semantic_type (sem_int_T n) \<longleftrightarrow> n = 0 \<close>
  unfolding phantom_mem_semantic_type_def
  using MemObj_Size_int by clarsimp

abbreviation \<open>\<s>\<i>\<z>\<e>_\<t> \<equiv> \<i>\<n>\<t>(\<s>\<i>\<z>\<e>_\<t>)\<close>
 

proc calloc:
  requires \<open>\<p>\<a>\<r>\<a>\<m> T\<close>
  input \<open>n \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>replicate n z \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (Array n T))\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<a>\<r>\<r>\<a>\<y>[n] TY)
          \<s>\<u>\<b>\<j> addr. memaddr.index addr = 0\<close>
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  note list_all2_conv_all_nth[simp] ;;

  semantic_local_value($n) \<open>\<i>\<n>\<t>(\<s>\<i>\<z>\<e>_\<t>)\<close>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=\<open>\<a>\<r>\<r>\<a>\<y>[snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>1))] TY\<close>
                                               and v=\<open>sem_mk_array (replicate (snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>1))) (the (Zero TY)))\<close>]

  semantic_assumption \<open>type_storable_in_mem (\<a>\<r>\<r>\<a>\<y>[snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>1))] TY)\<close>

  \<open>replicate n z \<Ztypecolon> MAKE _ (\<m>\<e>\<m>-\<b>\<l>\<k>[blk] (MAKE _ (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (Array n T))))\<close>
  \<open>replicate n z \<Ztypecolon> MAKE _ (\<m>\<e>\<m>[memaddr blk 0] Array n T)\<close>

  have t1: \<open>valid_address (memaddr blk [])\<close>
    unfolding valid_address_def Valid_MemBlk_def
    using \<open>memblk.layout blk = \<a>\<r>\<r>\<a>\<y>[n] TY\<close>
    by (cases blk; clarsimp simp: \<open>type_storable_in_mem (\<a>\<r>\<r>\<a>\<y>[n] TY)\<close>) ;;
  
  semantic_return \<open>sem_mk_pointer (memaddr (\<phi>arg.dest \<v>2) 0) \<Turnstile> (memaddr blk 0 \<Ztypecolon> TypedPtr (\<a>\<r>\<r>\<a>\<y>[n] TY))\<close>

\<medium_right_bracket> .


proc op_shift_pointer [\<phi>overload +]:
  requires \<open>\<p>\<a>\<r>\<a>\<m> TY\<close>
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> RawPointer\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>('b::len)\<close>
  output \<open>addr ||+ of_nat (MemObj_Size TY * n) \<Ztypecolon> \<v>\<a>\<l> RawPointer\<close>
\<medium_left_bracket>
  $addr semantic_local_value \<p>\<t>\<r>
  semantic_return \<open>
    sem_mk_pointer (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1) ||+ of_nat (MemObj_Size TY * n))
        \<Turnstile> (addr ||+ of_nat (MemObj_Size TY * n) \<Ztypecolon> RawPointer)\<close>
\<medium_right_bracket> .

proc abst_shift_pointer [\<phi>overload +]:
  requires [unfolded abstract_address_offset_def, useful]: \<open>abstract_address_offset addr TY TY' n addr'\<close>
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr TY\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>('b::len)\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>addr' \<Ztypecolon> \<v>\<a>\<l> TypedPtr TY'\<close>
\<medium_left_bracket>
  op_shift_pointer ($addr to RawPointer, $n) \<open>TY\<close> to \<open>TypedPtr TY'\<close>
\<medium_right_bracket> .
  


end