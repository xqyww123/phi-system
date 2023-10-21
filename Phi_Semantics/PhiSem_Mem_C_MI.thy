theory PhiSem_Mem_C_MI \<comment> \<open>MI: Machine Integer\<close>
  imports PhiSem_Mem_C PhiSem_Machine_Integer PhiSem_Aggregate_Array
begin

proc op_allocate_mem_N:
  input \<open>n \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>replicate n z \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[array n TY] (Array n T))\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr (array n TY) \<s>\<u>\<b>\<j> addr. memaddr.index addr = 0\<close>
  unfolding Guided_Mem_Coercion_def
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  note list_all2_conv_all_nth[simp] ;;

  semantic_local_value( $n ) \<open>\<i>\<n>\<t>(size_t)\<close>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=\<open>array n TY\<close>
                                               and v=\<open>V_array.mk (replicate (snd (V_int.dest (\<phi>arg.dest \<a>\<r>\<g>1))) (the (Zero TY)))\<close>]

  \<open>replicate n z \<Ztypecolon> MAKE (\<m>\<e>\<m>[memaddr blk 0] (MAKE (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (Array n T))))\<close>
  certified by (of_tac \<open>V_array.mk (replicate (snd (V_int.dest (\<phi>arg.dest \<a>\<r>\<g>1))) (the (Zero TY)))\<close>,
              auto_sledgehammer) ;;
  
  semantic_return \<open>V_pointer.mk (memaddr (\<phi>arg.dest \<v>2) 0) \<Turnstile> (memaddr blk 0 \<Ztypecolon> Ptr (array n TY))\<close>

\<medium_right_bracket> .



end