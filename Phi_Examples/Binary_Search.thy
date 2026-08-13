theory Binary_Search
  imports Phi_Semantics.PhiSem_C
begin


proc binary_search_array:
  input  \<open>arr \<Ztypecolon> \<mem>[ptr] \<Array>[cap] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
          ptr \<Ztypecolon> \<val> Ptr[\<array>[cap] \<i>\<n>\<t>]\<heavy_comma> lower \<Ztypecolon> \<val> \<nat>(\<i>\<n>\<t>)\<heavy_comma> upper \<Ztypecolon> \<val> \<nat>(\<i>\<n>\<t>)\<heavy_comma> k \<Ztypecolon> \<val> \<nat>(\<i>\<n>\<t>)\<close>
  premises \<open>arr ! upper \<le> k\<close>
       and \<open>lower < upper\<close>
       and \<open>upper < cap\<close>
       and \<open>sorted arr\<close>
  output \<open>arr \<Ztypecolon> \<mem>[ptr] \<Array>[cap] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
          (LEAST i. lower \<le> i \<and> i \<le> upper \<and> arr!i \<le> k) \<Ztypecolon> \<val> \<nat>(\<i>\<n>\<t>)\<close>
  is [routine]
\<medium_left_bracket>
  if (ptr[lower] \<le> k) \<medium_left_bracket>
    return (lower)
  \<medium_right_bracket> \<medium_left_bracket>
    (lower, upper) \<rightarrow> var l, u
    while \<open>l \<Ztypecolon> \<var>[l] \<nat>(\<i>\<n>\<t>)\<heavy_comma> u \<Ztypecolon> \<var>[u] \<nat>(\<i>\<n>\<t>) \<subj> l u.
            Inv: (lower \<le> l \<and> l < u \<and> u \<le> upper \<and> k < arr!l \<and> arr!u \<le> k) \<and>
            Guard: (l + 1 < u) \<and>
            End: (l + 1 = u)\<close>
         ( l + 1 < u )
    \<medium_left_bracket>
      val m \<leftarrow> l + (u - l) / 2 \<semicolon>
      if ( ptr[m] \<le> k ) \<medium_left_bracket> m \<rightarrow> u \<medium_right_bracket> \<medium_left_bracket> m \<rightarrow> l \<medium_right_bracket>
    \<medium_right_bracket>
    return (u)
  \<medium_right_bracket>
\<medium_right_bracket> .


proc generalized_binary_search:
  requires F: \<open>\<forall>i v. \<proc> F v \<lbrace> i \<Ztypecolon> \<val>[v] \<nat>(\<i>\<n>\<t>) \<longmapsto> f i \<Ztypecolon> \<val> \<bool> \<rbrace>\<close> \<comment> \<open>v: raw value\<close>
  premises \<open>\<forall>i j. i \<le> j \<longrightarrow> f i \<longrightarrow> f j\<close>
  input  \<open>lower \<Ztypecolon> \<val> \<nat>(\<i>\<n>\<t>)\<heavy_comma> upper \<Ztypecolon> \<val> \<nat>(\<i>\<n>\<t>)\<close>
  premises \<open>f upper\<close> and \<open>lower < upper\<close>
  output \<open>(LEAST i. lower \<le> i \<and> i \<le> upper \<and> f i) \<Ztypecolon> \<val> \<nat>(\<i>\<n>\<t>)\<close>
  is [routine]
\<medium_left_bracket>

  if ( F(lower) ) \<medium_left_bracket>
     return (lower)
  \<medium_right_bracket> \<medium_left_bracket>
    (lower, upper) \<rightarrow> var l, u ;;
    while \<open>l \<Ztypecolon> \<var>[l] \<nat>(\<i>\<n>\<t>)\<heavy_comma> u \<Ztypecolon> \<var>[u] \<nat>(\<i>\<n>\<t>) \<subj> l u.
            Inv: (lower \<le> l \<and> l < u \<and> u \<le> upper \<and> \<not> f l \<and> f u) \<and>
            Guard: (l + 1 < u) \<and>
            End: (l + 1 = u)\<close>
          ( \<open>$l + 1 < $u\<close> )
    \<medium_left_bracket>
      val m \<leftarrow> l + (u - l) / 2 ;;
      if ( F(m) ) \<medium_left_bracket> m \<rightarrow> u \<medium_right_bracket> \<medium_left_bracket> m \<rightarrow> l \<medium_right_bracket>
    \<medium_right_bracket>
    return (u)
  \<medium_right_bracket>
\<medium_right_bracket>.

text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm binary_search_array_\<phi>app
thm generalized_binary_search_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm binary_search_array_def
thm generalized_binary_search_def

end