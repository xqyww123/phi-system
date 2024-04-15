theory Binary_Search
  imports
    Phi_Semantics.PhiSem_C
begin

proc binary_search:
  requires F: \<open>\<forall>i v. \<p>\<r>\<o>\<c> F v \<lbrace> i \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>(32) \<longmapsto> f i \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close> \<comment> \<open>v: raw value\<close>
  premises \<open>\<forall>i j. i \<le> j \<longrightarrow> f i \<longrightarrow> f j\<close>
  input  \<open>lower \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<heavy_comma> upper \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  premises \<open>f upper\<close> and \<open>lower < upper\<close>
  output \<open>(LEAST i. lower \<le> i \<and> i \<le> upper \<and> f i) \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  is [routine]
\<medium_left_bracket>

  if ( F($lower) ) \<medium_left_bracket>
     return ($lower)
  \<medium_right_bracket> \<medium_left_bracket>
    ($lower, $upper) \<rightarrow> var $l, $u ;;
    while \<open>l \<Ztypecolon> \<v>\<a>\<r>[l] \<nat>(32)\<heavy_comma> u \<Ztypecolon> \<v>\<a>\<r>[u] \<nat>(32) \<s>\<u>\<b>\<j> l u.
            Inv: (lower \<le> l \<and> l < u \<and> u \<le> upper \<and> \<not> f l \<and> f u) \<and>
            Guard: (l + 1 < u) \<and>
            End: (l + 1 = u)\<close>
          ( \<open>$l + 1 < $u\<close> )
    \<medium_left_bracket>
      val m \<leftarrow> $l + ($u - $l) / 2 ;;
      if ( F($m) ) \<medium_left_bracket> $m \<rightarrow> $u \<medium_right_bracket> \<medium_left_bracket> $m \<rightarrow> $l \<medium_right_bracket>
    \<medium_right_bracket>
    return ($u)
  \<medium_right_bracket>
\<medium_right_bracket>.


end