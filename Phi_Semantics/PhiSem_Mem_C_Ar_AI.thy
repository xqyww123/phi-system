theory PhiSem_Mem_C_Ar_AI \<comment> \<open>AI stands for \<open>arbitrary-precision integer\<close>\<close>
  imports PhiSem_Mem_C_Ag_Ar PhiSem_Int_ArbiPrec
begin

section \<open>Pointer Arithmetic\<close>

proc op_add_ptr_a[\<phi>overload +]:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  premises \<open>0 \<le> int i + j \<and> nat (int i + j) \<le> len\<close>
  output \<open>nat (int i + j) \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<close>
\<medium_left_bracket>
  $i semantic_local_value \<p>\<t>\<r>
  $j semantic_local_value \<a>\<i>\<n>\<t>

  semantic_return \<open>
      sem_mk_pointer (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1) ||+ of_int (sem_dest_aint (\<phi>arg.dest \<a>\<r>\<g>2)) * of_nat (MemObj_Size TY))
          \<Turnstile> (nat (int i + j) \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY)\<close>
certified proof -
  have t1: \<open>address_type addr = \<a>\<r>\<r>\<a>\<y>[len] TY \<and> TY \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> (len = 0 \<longrightarrow> nat (int i + j) = 0)\<close>
    by (metis \<a>\<r>\<r>\<a>\<y>_0_eq_any the_\<phi>lemmata(2) the_\<phi>lemmata(3) valid_array_pointer_not_poison)
  show ?thesis
    by (clarsimp simp: memaddr_to_raw_array_GEP[OF t1] useful distrib_right,
                 simp add: add.commute,
        metis memaddr_to_raw_array_GEP le_zero_eq local.t1 mem_shift_shift of_nat_mult the_\<phi>lemmata(1))
  qed
\<medium_right_bracket> .

proc (nodef) op_add_ptr_aN[\<phi>overload +]:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i + j \<le> len\<close>
  output \<open>i + j \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:len] TY\<close>
\<medium_left_bracket>
  $i + $j
\<medium_right_bracket> .


lemma nat_int_mul[iff]: "nat (int a * int b) = a * b"
  using nat_times_as_int by presburger
  

end