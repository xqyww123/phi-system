theory Quicksort
  imports Phi_Semantics.PhiSem_C
          "HOL-Combinatorics.List_Permutation"
          PhiStd.PhiStd_Loop
          Rational_Arith
begin

declare [[auto_sledgehammer_params = "try0 = false",
          linarith_split_limit = 20]]
declare [[\<phi>variable_is_typed]]

  proc qsort:
    input  \<open>\<v>\<a>\<l> i \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:LEN] \<i>\<n>\<t>\<heavy_comma>
            \<v>\<a>\<l> len \<Ztypecolon> \<nat>(\<i>\<n>\<t>)\<heavy_comma>
            l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(\<i>\<n>\<t>)  \<close>
    premises \<open>i + len \<le> LEN\<close>
    output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(\<i>\<n>\<t>)
            \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
    is [recursive]
    is [routine]
  \<medium_left_bracket>
    if (len \<le> 1) \<medium_left_bracket>
      return
    \<medium_right_bracket> \<medium_left_bracket>
      val pivot \<leftarrow> *(i + (len - 1)) \<semicolon>
      var d \<leftarrow> 0 \<semicolon>
      iterate (0,len) \<open>\<lambda>n. d  \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
                           l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(\<i>\<n>\<t>)
                   \<s>\<u>\<b>\<j> l' d.
                     d \<le> n \<and> l <~~> l' \<and>
                     (if n = length l' then 0<d \<and> l'!(d-1) = ?pivot
                                       else last l' = ?pivot) \<and>
                     (\<forall>k<d. l' ! k \<le> ?pivot) \<and>
                     (\<forall>k<n-d. ?pivot < l' ! (d + k) ) \<close> 
      \<medium_left_bracket>
        for n \<rightarrow> val n \<semicolon>
        *(i + n) \<rightarrow> val x \<semicolon>
        if (x \<le> pivot) \<medium_left_bracket>
          (i + n) := *(i + d) \<semicolon>
          (i + d) := x \<semicolon>
          d \<leftarrow> d + 1
        \<medium_right_bracket> \<medium_left_bracket>
          (*comment: else, do nothing*)
        \<medium_right_bracket> \<semicolon>
      \<medium_right_bracket> \<semicolon> thm \<phi>  \<semicolon>

      holds_fact t5[simp]: \<open>d - (d - Suc 0) = 1\<close> \<semicolon>

      qsort (i, d-1) \<semicolon>
      qsort (i + d, len - d)   \<semicolon>
          


      holds_fact t1: \<open>(\<forall>x\<in>set (drop d l'). ?pivot < x)\<close>
             and t2: \<open>(\<forall>x\<in>set (take (d-1) l'). x \<le> ?pivot)\<close>
             and t3[simp]: \<open>set l'b = set (drop d l')\<close>
             and t4[simp]: \<open>set l'a = set (take (d-1) l')\<close>  
             
      note [simp] = sorted_simps sorted_wrt_append \<semicolon>
  
      return
    \<medium_right_bracket>
  \<medium_right_bracket> .


text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm qsort_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>
  
thm qsort_def
(*


  proc qsort_rat:
    input  \<open>\<v>\<a>\<l> i \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:LEN] \<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l>\<heavy_comma>
            \<v>\<a>\<l> len \<Ztypecolon> \<nat>(\<i>\<n>\<t>)\<heavy_comma>
            l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<rat>\<close>
    premises \<open>i + len \<le> LEN\<close>
    output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<rat>
            \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
    is [recursive]
    is [routine]
  \<medium_left_bracket>
    if (len \<le> 1) \<medium_left_bracket>
      return
    \<medium_right_bracket> \<medium_left_bracket>
      val pivot \<leftarrow> *(i + (len - 1)) \<semicolon>
      var d \<leftarrow> \<open>0 \<Ztypecolon> \<nat>(\<i>\<n>\<t>)\<close> \<semicolon>
      iterate (0,len) \<open>\<lambda>n. d  \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
                           l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<rat>
                     \<s>\<u>\<b>\<j> l' d.
                       d \<le> n \<and> l <~~> l' \<and>
                       (if n = length l' then 0<d \<and> l'!(d-1) = ?pivot
                                         else last l' = ?pivot) \<and>
                       (\<forall>k<d. l' ! k \<le> ?pivot) \<and>
                       (\<forall>k<n-d. ?pivot < l' ! (d + k)) \<close> 
      \<medium_left_bracket>
        for n \<rightarrow> val n \<semicolon>
        *(i + n) \<rightarrow> val x \<semicolon>
        if (x \<le> pivot) \<medium_left_bracket>
          (i + n) := *(i + d) \<semicolon>
          (i + d) := x \<semicolon>
          d \<leftarrow> d + 1
        \<medium_right_bracket> \<medium_left_bracket>
          (*comment: else, do nothing*)
        \<medium_right_bracket> \<semicolon>
      \<medium_right_bracket>
      qsort_rat (i, d-1) \<semicolon>
      qsort_rat (i + d, len - d) \<semicolon>
          
      holds_fact t1: \<open>(\<forall>x\<in>set (drop d l'). l ! (len - 1) < x)\<close>
             and t2: \<open>(\<forall>x\<in>set (take (d-1) l'). x \<le> l ! (len - 1))\<close>
             and t3[simp]: \<open>set l'b = set (drop d l')\<close>
             and t4[simp]: \<open>set l'a = set (take (d-1) l')\<close>
             and t5[simp]: \<open>d - (d - Suc 0) = 1\<close>
      note [simp] = sorted_simps sorted_wrt_append \<semicolon>  

      return
    \<medium_right_bracket>
  \<medium_right_bracket> .

declare [[\<phi>infer_requirements]]
 
 
  proc qsort_generic:
    input  \<open>\<v>\<a>\<l> i \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:LEN] (\<t>\<y>\<p>\<e>\<o>\<f> T)\<heavy_comma>
            \<v>\<a>\<l> len \<Ztypecolon> \<nat>(\<i>\<n>\<t>)\<heavy_comma>
            l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T  \<close>
    requires \<open>Order T\<close>
    premises \<open>i + len \<le> LEN\<close>
    output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T
            \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
    is [recursive]
    is [routine]
  \<medium_left_bracket>
    if (len \<le> 1) \<medium_left_bracket>
      return
    \<medium_right_bracket> \<medium_left_bracket>
      val pivot \<leftarrow> *(i + (len - 1)) \<semicolon>
      var d \<leftarrow> 0 \<semicolon>
      iterate (0,len) \<open>\<lambda>n. d  \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
                           l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T
                           \<s>\<u>\<b>\<j> l' d.
                             d \<le> n \<and> l <~~> l' \<and>
                             (\<forall>k<d. l' ! k \<le> ?pivot) \<and>
                             (\<forall>k<n-d. ?pivot < l' ! (d + k)) \<close> 
      \<medium_left_bracket>
        for n \<rightarrow> val n \<semicolon>
        *(i + n) \<rightarrow> val x \<semicolon>
        if (x \<le> pivot) \<medium_left_bracket>
          (i + n) := *(i + d) \<semicolon>
          (i + d) := x \<semicolon>
          d \<leftarrow> d + 1
        \<medium_right_bracket> \<medium_left_bracket>
          (*comment: else, do nothing*)
        \<medium_right_bracket> \<semicolon>
      \<medium_right_bracket>
      qsort_generic (i, d) \<semicolon>
      qsort_generic (i + d, len - d) \<semicolon>
          
      holds_fact t1: \<open>(\<forall>x\<in>set (drop d l'). l ! (len - 1) < x)\<close>
             and t2: \<open>(\<forall>x\<in>set (take d l'). x \<le> l ! (len - 1))\<close>
             and t3[simp]: \<open>set l'b = set (drop d l')\<close>
             and t4[simp]: \<open>set l'a = set (take d l')\<close> \<semicolon>
  
      return
    \<medium_right_bracket>
  \<medium_right_bracket> .
*)

 
  proc qsort_generic:
    input  \<open>\<v>\<a>\<l> i \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:LEN] (\<t>\<y>\<p>\<e>\<o>\<f> T)\<heavy_comma>
            \<v>\<a>\<l> len \<Ztypecolon> \<nat>(\<i>\<n>\<t>)\<heavy_comma>
            l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T  \<close>
    requires \<open>Order T\<close>
    premises \<open>i + len \<le> LEN\<close>
    output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T
            \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
    is [recursive]
    is [routine]
  \<medium_left_bracket>
    if (len \<le> 1) \<medium_left_bracket>
      return
    \<medium_right_bracket> \<medium_left_bracket>
      val pivot \<leftarrow> *(i + (len - 1)) \<semicolon>
      var d \<leftarrow> 0 \<semicolon>
      iterate (0,len) \<open>\<lambda>n. d  \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(\<i>\<n>\<t>)\<heavy_comma>
                           l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T
                           \<s>\<u>\<b>\<j> l' d.
                             d \<le> n \<and> l <~~> l' \<and>
                             (\<forall>k<d. l' ! k \<le> ?pivot) \<and>
                             (\<forall>k<n-d. ?pivot < l' ! (d + k)) \<close> 
      \<medium_left_bracket>
        for n \<rightarrow> val n \<semicolon>
        *(i + n) \<rightarrow> val x \<semicolon>
        if (x \<le> pivot) \<medium_left_bracket>
          (i + n) := *(i + d) \<semicolon>
          (i + d) := x \<semicolon>
          d \<leftarrow> d + 1
        \<medium_right_bracket> \<medium_left_bracket>
          (*comment: else, do nothing*)
        \<medium_right_bracket> \<semicolon>
      \<medium_right_bracket>
      qsort_generic (i, d) \<semicolon>
      qsort_generic (i + d, len - d) \<semicolon>
          
      holds_fact t1: \<open>(\<forall>x\<in>set (drop d l'). l ! (len - 1) < x)\<close>
             and t2: \<open>(\<forall>x\<in>set (take d l'). x \<le> l ! (len - 1))\<close>
             and t3[simp]: \<open>set l'b = set (drop d l')\<close>
             and t4[simp]: \<open>set l'a = set (take d l')\<close> \<semicolon>
  
      return
    \<medium_right_bracket>
  \<medium_right_bracket> .


end
