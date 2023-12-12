theory PhiTest_Mem_C
  imports Phi_Semantics.PhiSem_Mem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
          Phi_Semantics.PhiSem_Mem_C_Ag_NT
begin

declare [[\<phi>reasoning_step_limit = 50]]
 
proc test_mem1:
  input \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<a>\<i>\<n>\<t>\<close>
  output \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket>
    note [[\<phi>trace_reasoning = 2]] ;;
    $addr !
  \<medium_right_bracket> .

proc test_mem2:
  input \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<a>\<i>\<n>\<t>\<close>
  output \<open>2 \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<close>
  \<medium_left_bracket>
    $addr := \<open>2 \<Ztypecolon> \<nat>\<close>
  \<medium_right_bracket> .

proc test_ptr3:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  output \<open>addr \<tribullet>\<^sub>a c \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<a>\<i>\<n>\<t>\<close>
\<medium_left_bracket>
  $addr \<tribullet> c
\<medium_right_bracket> .


declare [[\<phi>reasoning_step_limit = 40]]

thm \<phi>MapAt_L.ToA_mapper


  
proc test_mem3:
  input \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  output \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket> 
    note [[\<phi>trace_reasoning = 2]]
    ;; $addr \<tribullet> c !























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