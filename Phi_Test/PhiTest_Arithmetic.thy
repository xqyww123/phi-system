theory PhiTest_Arithmetic
  imports
    Phi_Semantics.PhiSem_CF_Routine
    Phi_Semantics.PhiSem_CF_Breakable
    Phi_Semantics.PhiSem_Variable
    Phi_Semantics.PhiSem_Int_ArbiPrec
    "HOL-Computational_Algebra.Primes"
begin

term prime

term \<open>3 dvd 4\<close>
term \<open>3 mod 4\<close>

proc
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> prime x \<Ztypecolon> \<bool>\<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$x \<le> 1\<close> \<medium_left_bracket>
      return (\<open>False\<close>) affirm using leD prime_gt_1_nat the_\<phi> by auto
    \<medium_right_bracket>.
    \<medium_left_bracket>  note [[\<phi>trace_reasoning = 2]] ;;
      \<open>2 \<Ztypecolon> \<nat>\<close> \<rightarrow> var v ;;
      while \<open>i \<Ztypecolon> \<v>\<a>\<r>[\<v>\<a>\<r>_v] \<nat> \<s>\<u>\<b>\<j> i.
            Inv: (1 < i \<and> i \<le> x \<and> (\<forall>j \<in> {1<..<i}. \<not> j dvd x)) \<and>
            Guard: (i \<noteq> x) \<and>
            End: (i dvd x)\<close>
        \<medium_left_bracket> \<open>$v \<noteq> $x\<close> \<medium_right_bracket>.
        \<medium_left_bracket>
          if \<open>$x mod $v = 0\<close> \<medium_left_bracket>
            return (\<open>False\<close>) affirm by (metis le_neq_implies_less mod_0_imp_dvd nat_neq_iff prime_nat_not_dvd the_\<phi>(1) the_\<phi>(2) the_\<phi>(4) the_\<phi>(5))
          \<medium_right_bracket>.
          \<medium_left_bracket>
            continue
          \<medium_right_bracket>. ;;
            \<medium_right_bracket>   ..

end