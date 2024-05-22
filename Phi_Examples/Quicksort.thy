theory Quicksort
  imports Phi_Semantics.PhiSem_C
          "HOL-Combinatorics.List_Permutation"
          PhiStd.PhiStd_Loop
begin

declare [[auto_sledgehammer_params = "try0 = false"]]
proc qsort:
  input  \<open>i \<Ztypecolon> \<v>\<a>\<l> \<bbbS>\<p>\<t>\<r>[addr:LEN] \<i>\<n>\<t>\<heavy_comma> \<comment> \<open>\<open>LEN\<close> is the length of the entire array, which decides
                                            the scope that a slice pointer can range over.\<close>
          len \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma>
          l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(\<i>\<n>\<t>)\<close>
  premises \<open>i + len \<le> LEN\<close>
  output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(\<i>\<n>\<t>) \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if (len \<le> 1)
  \<medium_left_bracket> return \<medium_right_bracket>
  \<medium_left_bracket>
    val pivot \<leftarrow> *(i + (len - 1)) \<semicolon>
    var d \<leftarrow> 0 \<semicolon>
    iterate (0,len) \<open>\<lambda>n. d \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
                          l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(\<i>\<n>\<t>)
                         \<s>\<u>\<b>\<j> l' d.
                           d \<le> n \<and> l <~~> l' \<and>
                           (\<forall>k<d. l' ! k \<le> ?pivot) \<and>
                           (\<forall>k<n-d. ?pivot < l' ! (d + k)) \<close> 
    \<medium_left_bracket> 
      for n \<rightarrow> val n \<semicolon>
      *(i + n) \<rightarrow> val x \<semicolon>
      if (x \<le> pivot)
      \<medium_left_bracket>
        (i + n) := *(i + d) \<semicolon>
        (i + d) := x \<semicolon>
        d \<leftarrow> d + 1
      \<medium_right_bracket>
      \<medium_left_bracket> \<medium_right_bracket> \<semicolon>
    \<medium_right_bracket>
    qsort (i, d) \<semicolon>
    qsort (i + d, len - d) \<semicolon>
        
    holds_fact t1: \<open>(\<forall>x\<in>set (drop d l'). l ! (len - 1) < x)\<close>
           and t2: \<open>(\<forall>x\<in>set (take d l'). x \<le> l ! (len - 1))\<close>
           and t4[\<phi>sledgehammer_simps]: \<open>set l'b = set (drop d l')\<close>
    from \<open>mset (take d l') = mset l'a\<close> have t3[\<phi>sledgehammer_simps]: \<open>set l'a = set (take d l')\<close> by auto_sledgehammer
    note [\<phi>sledgehammer_simps] = sorted_append  \<semicolon>

    return
  \<medium_right_bracket>
\<medium_right_bracket> .


text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm qsort_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>
 
thm qsort_def

end