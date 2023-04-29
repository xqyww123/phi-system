theory PhiTest_Arithmetic
  imports
    Phi_Semantics.PhiSem_CF_Routine
    Phi_Semantics.PhiSem_CF_Breakable
    Phi_Semantics.PhiSem_Variable
    Phi_Semantics.PhiSem_Int_ArbiPrec
    "HOL-Computational_Algebra.Primes"
begin
 
proc GCD:
  input \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>gcd x y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> 
  is [recursive x y] \<comment> \<open>x, y are variable through recursive callings\<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$x > $y\<close> \<medium_left_bracket> GCD ($y, $x) \<medium_right_bracket>.
    \<medium_left_bracket>
      \<open>$y mod $x\<close> \<rightarrow> val t
      if \<open>$t = 0\<close> \<medium_left_bracket> $x \<medium_right_bracket>. \<medium_left_bracket> GCD ($t, $x) \<medium_right_bracket>.
    \<medium_right_bracket>.
  \<medium_right_bracket>. .

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

proc bin_search:
  assumes F: \<open>\<forall>i v1. \<p>\<r>\<o>\<c> F v1 \<lbrace> i \<Ztypecolon> \<v>\<a>\<l>[v1] \<int> \<longmapsto> f i \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close>
  premises \<open>mono f\<close>
  input \<open>lower \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  premises \<open>f upper\<close> and \<open>lower < upper\<close>
  output \<open>(LEAST i. lower \<le> i \<and> i \<le> upper \<and> f i) \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  is [routine]
  \<medium_left_bracket>
    pure-fact \<open>i \<le> j \<Longrightarrow> f i \<Longrightarrow> f j\<close> for i j ;;

    if \<medium_left_bracket> F($lower) \<medium_right_bracket>. \<medium_left_bracket> return ($lower) \<medium_right_bracket>.
    \<medium_left_bracket>  
      $lower, $upper \<rightarrow> var $l, $u ;;
      while \<open>l \<Ztypecolon> \<v>\<a>\<r>[l] \<int>\<heavy_comma> u \<Ztypecolon> \<v>\<a>\<r>[u] \<int> \<s>\<u>\<b>\<j> l u.
              Inv: (lower \<le> l \<and> l < u \<and> u \<le> upper \<and> \<not> f l \<and> f u) \<and>
              Guard: (l + 1 < u) \<and>
              End: (l + 1 = u)\<close>
      \<medium_left_bracket> \<open>$l + 1 < $u\<close> \<medium_right_bracket>.
      \<medium_left_bracket>
        \<open>($l + $u) div 2\<close> \<rightarrow> val m ;;
        if \<medium_left_bracket> F($m) \<medium_right_bracket>. \<medium_left_bracket> $m \<rightarrow> $u \<medium_right_bracket>. \<medium_left_bracket> $m \<rightarrow> $l \<medium_right_bracket>.
      \<medium_right_bracket>. 
      return ($u)
    \<medium_right_bracket>.
  \<medium_right_bracket>. .

end
