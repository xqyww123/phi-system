theory PhiSem_Mem_C_Ar_AI
  imports PhiSem_Mem_C_Ag_Ar PhiSem_Int_ArbiPrec
begin

section \<open>Pointer Arithmetic\<close>

proc op_add_ptr_a[\<phi>overload +]:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  premises \<open>0 \<le> int i + j \<and> nat (int i + j) \<le> len\<close>
  output \<open>nat (int i + j) \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY\<close>
\<medium_left_bracket>
  $i semantic_local_value \<open>pointer\<close>
  $j semantic_local_value \<open>\<a>\<i>\<n>\<t>\<close> 

  thm useful
  from \<open>valid_logaddr_range TY addr base len\<close>[unfolded valid_logaddr_range_def]
  have t1[useful]: \<open>valid_logaddr addr \<and> (\<forall>i<len. valid_logaddr (addr \<tribullet>\<^sub>a (base + i)\<^sup>\<t>\<^sup>\<h>) \<and> logaddr_type (addr \<tribullet>\<^sub>a (base + i)\<^sup>\<t>\<^sup>\<h>) = TY)\<close> by simp

  from \<open>valid_logaddr_range TY addr base len\<close>[unfolded valid_logaddr_range_def]
  obtain N where t2[useful]: \<open>logaddr_type addr = \<a>\<r>\<r>\<a>\<y>[N] TY\<close> and t3[useful]: \<open>base + len \<le> N\<close> by blast ;;

  semantic_return \<open>
      V_pointer.mk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1) ||+ of_int (V_aint.dest (\<phi>arg.dest \<a>\<r>\<g>2)) * of_nat (MemObj_Size TY))
          \<Turnstile> (nat (int i + j) \<Ztypecolon> \<Ss>\<Pp>\<t>\<r>[addr:base:len] TY)\<close>
  certified by (clarsimp simp: logaddr_to_raw_array_GEP[OF t2] useful distrib_right)

\<medium_right_bracket> .

declare nat_int_add[iff]

lemma nat_int_mul[iff]: "nat (int a * int b) = a * b"
  using nat_times_as_int by presburger
  

end