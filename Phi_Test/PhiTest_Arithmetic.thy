theory PhiTest_Arithmetic
  imports
    Phi_Semantics.PhiSem_CF_Routine
    Phi_Semantics.PhiSem_CF_Breakable
    Phi_Semantics.PhiSem_Variable
    Phi_Semantics.PhiSem_Int_ArbiPrec
    "HOL-Computational_Algebra.Primes"
begin

proc test_prime:
  input  \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> prime x \<Ztypecolon> \<bool>\<close> \<comment> \<open>\<^term>\<open>prime :: nat => bool\<close> is a predicate checking primes\<close>
  is [routine]
\<medium_left_bracket>
  if ( $x \<le> 1 )  \<medium_left_bracket>
    return (False)
  \<medium_right_bracket>
  \<medium_left_bracket>
    2 \<rightarrow> var v ;;

    while \<open>i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i.
            Inv: (1 < i \<and> i \<le> x \<and> (\<forall>j. 1 < j \<and> j < i \<longrightarrow> \<not> j dvd x)) \<and>
            Guard: (i \<noteq> x) \<and>
            End: (i = x)\<close> \<comment> \<open>Specification of the loop\<close>
          ( \<open>$v \<noteq> $x\<close> ) \<comment> \<open>Code for loop guard\<close>
    \<medium_left_bracket>                   \<comment> \<open>Code for loop body\<close>
      if \<open>$x mod $v = 0\<close> \<medium_left_bracket>
        return (False)
      \<medium_right_bracket>
      \<medium_left_bracket>
        $v + 1 \<rightarrow> $v
      \<medium_right_bracket> 
    \<medium_right_bracket> 
    return (True)
  \<medium_right_bracket>
\<medium_right_bracket> .

term \<open>(\<lambda>e. \<b>\<r>\<e>\<a>\<k> lb \<w>\<i>\<t>\<h> (\<lambda>_. i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i. (1 < i \<and> i \<le> x \<and> (\<forall>j. 1 < j \<and> j < i \<longrightarrow> \<not> j dvd x)) \<and> i = x) \<o>\<r> \<b>\<r>\<e>\<a>\<k> lc
                 \<w>\<i>\<t>\<h> (\<lambda>_. i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i. 1 < i \<and> i \<le> x \<and> (\<forall>j. 1 < j \<and> j < i \<longrightarrow> \<not> j dvd x)) \<o>\<r> i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat>\<heavy_comma>
                 (\<^bold>b\<^bold>r\<^bold>o\<^bold>k\<^bold>e\<^bold>n label_ret \<w>\<i>\<t>\<h> (\<lambda>\<r>\<e>\<t>. prime x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<bool>)))\<close>

thm test_prime_def \<comment> \<open>Semantic definition\<close>
thm test_prime_\<phi>app \<comment> \<open>Specification theorem\<close>


proc test_prime':
  input  \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> prime x \<Ztypecolon> \<bool>\<close>
  is [routine] (*If you don't add this attribute telling the program you are building is a routine,
                 then the program is just a program fragment and you cannot use \<open>return\<close> *)
\<medium_left_bracket>
  if \<open>$x \<le> 1\<close> \<medium_left_bracket>
    return (False)
  \<medium_right_bracket>
  \<medium_left_bracket>
    \<open>2 \<Ztypecolon> \<nat>\<close> \<rightarrow> var v ;;
    (* In the previous example, the loop iterates from 2 to x, here we apply an optimization
       where the loop only needs to iterate to sqrt(x). *)
    while \<open>i \<Ztypecolon> \<v>\<a>\<r>[v] \<nat> \<s>\<u>\<b>\<j> i.
          Inv: (1 < i \<and> i \<le> x \<and> (\<forall>j \<in> {1<..<i}. \<not> j dvd x)) \<and>
          Guard: (i * i \<le> x) \<and>
          End: (x < i * i)\<close>
        ( $v * $v \<le> $x )
    \<medium_left_bracket>
      if \<open>$x mod $v = 0\<close> \<medium_left_bracket>
        return (False)
      \<medium_right_bracket> \<medium_left_bracket>
        \<open>$v + 1\<close> \<rightarrow> $v 
      \<medium_right_bracket>
    \<medium_right_bracket>

    return (True) (*with this optimization, the final obligation fails to be solved
                    automatically, but the manual proof is intuitive and semi-automated.*)
    certified proof simp
        have \<open>False\<close> if assm: \<open>\<not> prime x\<close>
          proof -
            obtain k where \<open>k dvd x \<and> 1 < k \<and> k < x\<close> by auto_sledgehammer
            then have \<open>k < i \<or> x div k < i\<close> by auto_sledgehammer
            then show False by auto_sledgehammer
          qed
        then show \<open>prime x\<close>
          by auto_sledgehammer
      qed
  \<medium_right_bracket> \<comment> \<open>Close the top branch\<close>
\<medium_right_bracket> \<comment> \<open>Close the function body\<close> .


proc GCD:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>gcd x y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close> 
  is [recursive x y] \<comment> \<open>x, y are variable through recursive callings\<close>
\<medium_left_bracket>
  if ($y < $x) \<medium_left_bracket> GCD ($y, $x) \<medium_right_bracket>
  \<medium_left_bracket>
    \<open>$y mod $x\<close> \<rightarrow> val t
    if \<open>$t = 0\<close> \<medium_left_bracket> $x \<medium_right_bracket> \<medium_left_bracket> GCD ($t, $x) \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket>.

declare GCD_\<phi>app[\<phi>synthesis add] \<comment> \<open>So that we can use abstract spec \<open>gcd\<close> in synthesis\<close>

proc Coprime:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>coprime x y \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  \<open>gcd $x $y = 1\<close>
\<medium_right_bracket>.

proc binary_search:
  requires F: \<open>\<forall>i v. \<p>\<r>\<o>\<c> F v \<lbrace> i \<Ztypecolon> \<v>\<a>\<l>[v] \<int> \<longmapsto> f i \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close> \<comment> \<open>v: raw value\<close>
  premises \<open>mono f\<close>
  input  \<open>lower \<Ztypecolon> \<v>\<a>\<l> \<int>\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  premises \<open>f upper\<close> and \<open>lower < upper\<close>
  output \<open>(LEAST i. lower \<le> i \<and> i \<le> upper \<and> f i) \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  is [routine]
\<medium_left_bracket> 
  pure_fact \<open>i \<le> j \<Longrightarrow> f i \<Longrightarrow> f j\<close> for i j ;;

  if ( F($lower) ) \<medium_left_bracket>
     return ($lower)
  \<medium_right_bracket> \<medium_left_bracket>
    ($lower, $upper) \<rightarrow> var $l, $u ;;
    while \<open>l \<Ztypecolon> \<v>\<a>\<r>[l] \<int>\<heavy_comma> u \<Ztypecolon> \<v>\<a>\<r>[u] \<int> \<s>\<u>\<b>\<j> l u.
            Inv: (lower \<le> l \<and> l < u \<and> u \<le> upper \<and> \<not> f l \<and> f u) \<and>
            Guard: (l + 1 < u) \<and>
            End: (l + 1 = u)\<close>
          ( \<open>$l + 1 < $u\<close> )
    \<medium_left_bracket>
      \<open>($l + $u) div 2\<close> \<rightarrow> val m
      if ( F($m) ) \<medium_left_bracket> $m \<rightarrow> $u \<medium_right_bracket> \<medium_left_bracket> $m \<rightarrow> $l \<medium_right_bracket>
    \<medium_right_bracket>
    return ($u)
  \<medium_right_bracket>
\<medium_right_bracket>.


end
