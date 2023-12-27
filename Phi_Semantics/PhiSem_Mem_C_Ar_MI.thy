theory PhiSem_Mem_C_Ar_MI \<comment> \<open>AI stands for \<open>machine integer\<close>\<close>
  imports PhiSem_Mem_C_Ag_Ar PhiSem_Machine_Integer
begin

section \<open>Pointer Arithmetic\<close>

proc op_add_ptr[\<phi>overload +]:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<int>('b)\<close>
  premises \<open>0 \<le> int i + j \<and> nat (int i + j) \<le> len\<close>
  output \<open>nat (int i + j) \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY\<close>
\<medium_left_bracket>
  $i semantic_local_value \<open>pointer\<close>
  $j semantic_local_value \<open>\<i>\<n>\<t>('b)\<close> 

  thm useful
  from \<open>valid_logaddr_range TY addr base len\<close>[unfolded valid_logaddr_range_def]
  have t1[useful]: \<open>valid_logaddr addr \<and> (\<forall>i<len. valid_logaddr (addr \<tribullet>\<^sub>a (base + i)\<^sup>\<t>\<^sup>\<h>) \<and> logaddr_type (addr \<tribullet>\<^sub>a (base + i)\<^sup>\<t>\<^sup>\<h>) = TY)\<close> by simp

  from \<open>valid_logaddr_range TY addr base len\<close>[unfolded valid_logaddr_range_def]
  obtain N where t2[useful]: \<open>logaddr_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY\<close> and t3[useful]: \<open>base + len \<le> N\<close> by blast

  have [simp]: \<open>word_of_nat (nat (2 ^ LENGTH('b) + j)) = (word_of_int j :: 'b word)\<close>
    by (smt (verit, del_insts) More_Word.power_not_zero diff_less exp_eq_zero_iff len_gt_0 less_Suc0 nat_0_le of_int_of_nat_eq power_increasing_iff the_\<phi>lemmata(4) wi_hom_add word_arith_wis(7) word_of_int_2p_len) ;;

  semantic_return \<open>
      V_pointer.mk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)
              ||+ Word.scast (of_nat (snd (V_int.dest (\<phi>arg.dest \<a>\<r>\<g>2))) :: 'b word) * of_nat (MemObj_Size TY))
          \<Turnstile> (nat (int i + j) \<Ztypecolon> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY)\<close>
  certified by (insert useful, auto simp: logaddr_to_raw_array_GEP[OF t2] distrib_right,
                metis signed_of_int signed_take_bit_int_eq_self_iff the_\<phi>lemmata(4))
\<medium_right_bracket> .


proc (nodef) op_add_ptr_N[\<phi>overload +]:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close>
  premises \<open>i + j \<le> len\<close>
  output \<open>i + j \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY\<close>
\<medium_left_bracket>
  $i semantic_local_value \<open>pointer\<close>
  $j semantic_local_value \<open>\<i>\<n>\<t>('b)\<close> 

  thm useful
  from \<open>valid_logaddr_range TY addr base len\<close>[unfolded valid_logaddr_range_def]
  have t1[useful]: \<open>valid_logaddr addr \<and> (\<forall>i<len. valid_logaddr (addr \<tribullet>\<^sub>a (base + i)\<^sup>\<t>\<^sup>\<h>) \<and> logaddr_type (addr \<tribullet>\<^sub>a (base + i)\<^sup>\<t>\<^sup>\<h>) = TY)\<close> by simp

  from \<open>valid_logaddr_range TY addr base len\<close>[unfolded valid_logaddr_range_def]
  obtain N where t2[useful]: \<open>logaddr_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY\<close> and t3[useful]: \<open>base + len \<le> N\<close> by blast ;;

  semantic_return \<open>
      V_pointer.mk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)
              ||+ Word.ucast (of_nat (snd (V_int.dest (\<phi>arg.dest \<a>\<r>\<g>2))) :: 'b word) * of_nat (MemObj_Size TY))
          \<Turnstile> (i + j \<Ztypecolon> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY)\<close>
  certified by (insert useful, auto simp: logaddr_to_raw_array_GEP[OF t2] distrib_right ucast_of_nat_small)

\<medium_right_bracket> .



declare nat_int_add[iff]

lemma nat_int_mul[iff]: "nat (int a * int b) = a * b"
  using nat_times_as_int by presburger
  

end