theory Binary_Search
  imports Phi_Semantics.PhiSem_C
begin


proc binary_search_array:
  input  \<open>arr \<Ztypecolon> \<m>\<e>\<m>[ptr] \<bbbA>\<r>\<r>\<a>\<y>[cap] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
          ptr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[cap] \<i>\<n>\<t>\<heavy_comma> lower \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
  premises \<open>arr ! upper \<le> k\<close> and \<open>lower < upper\<close> and \<open>upper < cap\<close> and \<open>sorted arr\<close>
  output \<open>arr \<Ztypecolon> \<m>\<e>\<m>[ptr] \<bbbA>\<r>\<r>\<a>\<y>[cap] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
          (LEAST i. lower \<le> i \<and> i \<le> upper \<and> arr!i \<le> k) \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
  is [routine]
\<medium_left_bracket>
  if (ptr[lower] \<le> k) \<medium_left_bracket>
    return (lower)
  \<medium_right_bracket> \<medium_left_bracket>
    (lower, upper) \<rightarrow> var l, u
    while \<open>l \<Ztypecolon> \<v>\<a>\<r>[l] \<nat>(\<i>\<n>\<t>)\<heavy_comma> u \<Ztypecolon> \<v>\<a>\<r>[u] \<nat>(\<i>\<n>\<t>) \<s>\<u>\<b>\<j> l u.
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


  proc generic_binary_search:
    requires Test: \<open>\<forall>i. \<p>\<r>\<o>\<c> Test \<lbrace> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>) \<longmapsto> f i \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close>
    premises \<open>\<forall>i j. i \<le> j \<longrightarrow> f i \<longrightarrow> f j\<close>
    input  \<open>lower \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
    premises \<open>f upper\<close> and \<open>lower < upper\<close>
    output \<open>(LEAST i. lower \<le> i \<and> i \<le> upper \<and> f i) \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
    is [routine]
  \<medium_left_bracket>
  
    if ( Test(lower) ) \<medium_left_bracket>
       return (lower)
    \<medium_right_bracket> \<medium_left_bracket>
      (lower, upper) \<rightarrow> var l, u \<semicolon>
      while \<open>l \<Ztypecolon> \<v>\<a>\<r>[l] \<nat>(\<i>\<n>\<t>)\<heavy_comma> u \<Ztypecolon> \<v>\<a>\<r>[u] \<nat>(\<i>\<n>\<t>) \<s>\<u>\<b>\<j> l u.
              Inv: (lower \<le> l \<and> l < u \<and> u \<le> upper \<and> \<not> f l \<and> f u) \<and>
              Guard: (l + 1 < u) \<and>
              End: (l + 1 = u)\<close>
            ( l + 1 < u )
      \<medium_left_bracket>
        val m \<leftarrow> l + (u - l) / 2 \<semicolon>
        if ( Test(m) ) \<medium_left_bracket> m \<rightarrow> u \<medium_right_bracket> \<medium_left_bracket> m \<rightarrow> l \<medium_right_bracket>
      \<medium_right_bracket>
      return (u)
    \<medium_right_bracket>
  \<medium_right_bracket>.


text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm binary_search_array_\<phi>app
thm generic_binary_search_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm binary_search_array_def
thm generic_binary_search_def

end