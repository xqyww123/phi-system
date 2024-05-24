theory PhiSem_Mem_C_Ar_MI \<comment> \<open>AI stands for \<open>machine integer\<close>\<close>
  imports PhiSem_Mem_C_Ag_Ar PhiSem_Machine_Integer
begin

section \<open>Pointer Arithmetic\<close>

proc op_add_ptr[\<phi>overload +]:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close>
  premises \<open>0 \<le> int i + j \<and> nat (int i + j) \<le> len\<close>
  output \<open>nat (int i + j) \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<close>
\<medium_left_bracket>
  $i semantic_local_value \<p>\<t>\<r>
  $j semantic_local_value \<open>\<i>\<n>\<t>('b)\<close> 

  have [simp]: \<open>word_of_nat (nat (2 ^ LENGTH('b) + j)) = (word_of_int j :: 'b word)\<close>
    by (smt (verit, ccfv_threshold) One_nat_def nat_0_le of_int_of_nat_eq sint_of_int_eq the_\<phi>lemmata(1) two_less_eq_exp_length wi_hom_add word_of_int_0 word_of_int_2p_len) \<semicolon>

  semantic_return \<open>
      sem_mk_pointer (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1)
              ||+ Word.scast (of_nat (snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>2))) :: 'b word) * of_nat (MemObj_Size TY))
          \<Turnstile> (nat (int i + j) \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY)\<close>
  certified by (insert useful, auto simp: address_to_raw_array_GEP[OF \<open>address_type addr = \<a>\<r>\<r>\<a>\<y>[len] TY\<close>] distrib_right,
                simp add: add.commute signed_of_int signed_take_bit_int_eq_self)
\<medium_right_bracket> .


proc op_add_ptr_unsigned[\<phi>overload +]:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close>
  premises \<open>i + j \<le> len\<close>
  output \<open>i + j \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<close>
\<medium_left_bracket>
  $i semantic_local_value \<p>\<t>\<r>
  $j semantic_local_value \<open>\<i>\<n>\<t>('b)\<close>

  semantic_return \<open>
      sem_mk_pointer (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1)
              ||+ Word.ucast (of_nat (snd (sem_dest_int (\<phi>arg.dest \<a>\<r>\<g>2))) :: 'b word) * of_nat (MemObj_Size TY))
          \<Turnstile> (i + j \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY)\<close>
  certified by (insert useful,
                auto simp: address_to_raw_array_GEP[OF \<open>address_type addr = \<a>\<r>\<r>\<a>\<y>[len] TY\<close>]
                           distrib_right ucast_of_nat_small, simp add: add.commute)
\<medium_right_bracket> .



declare nat_int_add[iff]

lemma nat_int_mul[iff]: "nat (int a * int b) = a * b"
  using nat_times_as_int by presburger
  

end