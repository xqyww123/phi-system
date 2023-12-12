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



declare [[\<phi>reasoning_step_limit = 140]]

thm \<phi>MapAt_L.ToA_mapper

thm ttt
  
proc test_mem3:
  input \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  output \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket>
    $addr \<tribullet> b !
  \<medium_right_bracket> .

proc test_mem4:
  input \<open>(x,(y,z)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> z \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket>
    $addr \<tribullet> d \<tribullet> e !
  \<medium_right_bracket> .

proc test_mem5:
  input \<open>(x,(y,z,f)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z,f)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<nat>\<rbrace> \<rbrace>\<heavy_comma> f \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket>
    $addr \<tribullet> d \<tribullet> f !
  \<medium_right_bracket> .

proc test_mem6:
  input \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<s>\<t>\<r>\<u>\<c>\<t> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}}\<close>
  output \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<rbrace> \<rbrace>\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket>
    $addr \<tribullet> d \<tribullet> f \<tribullet> j !
  \<medium_right_bracket> .



















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