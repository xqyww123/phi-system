theory PhiSem_Mem_C_AI \<comment> \<open>AI: Integer of Arbitrary precision\<close>
  imports PhiSem_Mem_C PhiSem_Int_ArbiPrec PhiSem_Aggregate_Array
begin

proc calloc_aN:
  input \<open>n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>replicate n z \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (Array n T))\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr (\<a>\<r>\<r>\<a>\<y>[n] TY) \<s>\<u>\<b>\<j> addr. address_to_base addr \<close>
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  note list_all2_conv_all_nth[simp] ;;

  semantic_local_value($n) \<open>\<a>\<i>\<n>\<t>\<close>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=\<open>\<a>\<r>\<r>\<a>\<y>[n] TY\<close>
                                               and v=\<open>V_array.mk (replicate (nat (V_aint.dest (\<phi>arg.dest \<a>\<r>\<g>1))) (the (Zero TY)))\<close>]

  semantic_assumption \<open>type_storable_in_mem (\<a>\<r>\<r>\<a>\<y>[nat (V_aint.dest (\<phi>arg.dest \<a>\<r>\<g>1))] TY)\<close>

  \<open>replicate n z \<Ztypecolon> MAKE _ (\<m>\<e>\<m>[memaddr blk 0] (MAKE _ (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (Array n T))))\<close>

  have t1: \<open>valid_logaddr (memaddr blk [])\<close>
    unfolding valid_logaddr_def Valid_MemBlk_def
    using \<open>memblk.layout blk = \<a>\<r>\<r>\<a>\<y>[n] TY\<close>
    by (cases blk; clarsimp simp: \<open>type_storable_in_mem (\<a>\<r>\<r>\<a>\<y>[n] TY)\<close>) ;;
  
  semantic_return \<open>V_pointer.mk (memaddr (\<phi>arg.dest \<v>2) 0) \<Turnstile> (memaddr blk 0 \<Ztypecolon> Ptr (\<a>\<r>\<r>\<a>\<y>[n] TY))\<close>

\<medium_right_bracket> .


proc calloc_aN2:
  requires \<open>\<p>\<a>\<r>\<a>\<m> T\<close>
  input \<open>n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>replicate n (replicate m z) \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> \<Aa>\<r>\<r>\<a>\<y>[n] \<Aa>\<r>\<r>\<a>\<y>[m] T)\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> Ptr (\<a>\<r>\<r>\<a>\<y>[n] \<a>\<r>\<r>\<a>\<y>[m] TY)
          \<s>\<u>\<b>\<j> addr. address_to_base addr \<close>
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  note list_all2_conv_all_nth[simp] ;;

  semantic_local_value($n) \<open>\<a>\<i>\<n>\<t>\<close>
  semantic_local_value($m) \<open>\<a>\<i>\<n>\<t>\<close>
  semantic_assert \<open>Zero TY \<noteq> None\<close>

  apply_rule FIC.aggregate_mem.allocate_rule
            [where TY=\<open>\<a>\<r>\<r>\<a>\<y>[n] \<a>\<r>\<r>\<a>\<y>[m] TY\<close>
               and v=\<open>V_array.mk (replicate (nat (V_aint.dest (\<phi>arg.dest \<a>\<r>\<g>1)))
                                 (V_array.mk (replicate (nat (V_aint.dest (\<phi>arg.dest \<a>\<r>\<g>2))) (the (Zero TY)))))\<close>]

  semantic_assumption \<open>type_storable_in_mem (\<a>\<r>\<r>\<a>\<y>[nat (V_aint.dest (\<phi>arg.dest \<a>\<r>\<g>1))] \<a>\<r>\<r>\<a>\<y>[nat (V_aint.dest (\<phi>arg.dest \<a>\<r>\<g>2))] TY)\<close>
  \<open>replicate n (replicate m z) \<Ztypecolon> MAKE _ (\<m>\<e>\<m>[memaddr blk 0] (MAKE _ (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (Array n (Array m T)))))\<close>

  have t1: \<open>valid_logaddr (memaddr blk [])\<close>
    unfolding valid_logaddr_def Valid_MemBlk_def
    using \<open>memblk.layout blk = \<a>\<r>\<r>\<a>\<y>[n] \<a>\<r>\<r>\<a>\<y>[m] TY\<close>
    by (cases blk; clarsimp simp: \<open>type_storable_in_mem (\<a>\<r>\<r>\<a>\<y>[n] \<a>\<r>\<r>\<a>\<y>[m] TY)\<close>) ;;
  
  semantic_return \<open>V_pointer.mk (memaddr (\<phi>arg.dest \<v>3) 0) \<Turnstile> (memaddr blk 0 \<Ztypecolon> Ptr (\<a>\<r>\<r>\<a>\<y>[n] \<a>\<r>\<r>\<a>\<y>[m] TY))\<close>

\<medium_right_bracket> .


end