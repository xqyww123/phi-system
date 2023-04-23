theory PhiTest_Arithmetic
  imports
    Phi_Semantics.PhiSem_CF_Routine
    Phi_Semantics.PhiSem_CF_Breakable
    Phi_Semantics.PhiSem_Variable
    Phi_Semantics.PhiSem_Int_ArbiPrec
    "HOL-Computational_Algebra.Primes"
begin

ML \<open>Phi_Cache_DB.invalidate_cache \<^theory>\<close>

proc test_prime:
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> prime x \<Ztypecolon> \<bool>\<close> \<comment> \<open>\<^term>\<open>prime :: nat => bool\<close> is a predicate checking primes\<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$x \<le> 1\<close>  \<medium_left_bracket>
      return (False)
    \<medium_right_bracket>.
    \<medium_left_bracket>
      \<open>2 \<Ztypecolon> \<nat>\<close> \<rightarrow> var v ;;

      while \<open>i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i.
              Inv: (1 < i \<and> i \<le> x \<and> (\<forall>j. 1 < j \<and> j < i \<longrightarrow> \<not> j dvd x)) \<and>
              Guard: (i \<noteq> x) \<and>
              End: (i = x)\<close> \<comment> \<open>Specification of the loop\<close>
      \<medium_left_bracket> \<open>$v \<noteq> $x\<close> \<medium_right_bracket>. \<comment> \<open>Code for loop guard\<close>
      \<medium_left_bracket>               \<comment> \<open>Code for loop body\<close>
        if \<open>$x mod $v = 0\<close> \<medium_left_bracket>
          return (False)
        \<medium_right_bracket>.
        \<medium_left_bracket>
          \<open>$v + 1\<close> \<rightarrow> $v
        \<medium_right_bracket>.
      \<medium_right_bracket>.
      return (True)
    \<medium_right_bracket>.
  \<medium_right_bracket>. .

thm test_prime_def \<comment> \<open>Semantic definition\<close>
thm test_prime_\<phi>app \<comment> \<open>Specification theorem\<close>












proc test_prime':
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> prime x \<Ztypecolon> \<bool>\<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$x \<le> 1\<close> \<medium_left_bracket>
      return (False)
    \<medium_right_bracket>.
    \<medium_left_bracket>
      \<open>2 \<Ztypecolon> \<nat>\<close> \<rightarrow> var v ;;
      (* In the previous example, the loop iterates from 2 to x, here we apply an optimization
         where the loop only needs to iterate to sqrt(x). *)
      while \<open>i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i.
          Inv: (1 < i \<and> i \<le> x \<and> (\<forall>j \<in> {1<..<i}. \<not> j dvd x)) \<and>
          Guard: (i * i \<le> x) \<and>
          End: (x < i * i)\<close>
      \<medium_left_bracket> \<open>$v * $v \<le> $x\<close> \<medium_right_bracket>.
      \<medium_left_bracket>
        if \<open>$x mod $v = 0\<close> \<medium_left_bracket>
          return (False)  
        \<medium_right_bracket>.
        \<medium_left_bracket>
          \<open>$v + 1\<close> \<rightarrow> $v 
        \<medium_right_bracket>.
      \<medium_right_bracket>. ;;

      return (True) affirm (*with this optimization, the final obligation fails to be solved
                             automatically, but the manual proof is intuitive and semi-automated.*)
        proof simp
          have \<open>False\<close> if assm: \<open>\<not> prime x\<close>
            proof -
              obtain k where \<open>k dvd x \<and> 1 < k \<and> k < x\<close>  (* v generated automatically by sledgehammer *)
                by (metis One_nat_def Suc_lessI assm dvd_pos_nat linorder_le_less_linear nat_dvd_not_less not_less_iff_gr_or_eq prime_nat_iff the_\<phi>(5) zero_less_iff_neq_zero)
              then have \<open>k < ib \<or> x div k < ib\<close>   (* v generated automatically by sledgehammer *)
                by (metis dvd_mult_div_cancel leD leI mult_le_mono the_\<phi>lemmata(4))
              then show False                     (* v generated automatically by sledgehammer *)
                by (metis One_nat_def \<open>k dvd x \<and> 1 < k \<and> k < x\<close> div_mod_decomp dvd_imp_mod_0 dvd_triv_right greaterThanLessThan_iff mult.commute nat_arith.rule0 nat_mult_1_right nat_mult_less_cancel_disj the_\<phi>lemmata(3))
            qed
          then show \<open>prime x\<close>
            by fastforce
        qed
    \<medium_right_bracket>. \<comment> \<open>Close the top branch\<close>
  \<medium_right_bracket>. \<comment> \<open>Close the function body\<close> .


end
