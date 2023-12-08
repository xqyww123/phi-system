theory PhiTest_Mem_C
  imports Phi_Semantics.PhiSem_Mem_C
begin

lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T\<heavy_comma>
             take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T\<close>
  \<medium_left_bracket>
  \<medium_right_bracket> certified by auto_sledgehammer .

lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T\<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .


lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T \<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T\<close>
             
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .

lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T \<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T \<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T \<close>
             
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .

lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T \<heavy_comma>
              y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T \<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T \<close>
             
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .



end