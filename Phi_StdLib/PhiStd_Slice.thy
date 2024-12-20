theory PhiStd_Slice \<comment> \<open>'a' for arbitary precision interger\<close>
  imports PhiStd_Loop
          Phi_Semantics.PhiSem_Mem_C_Ar_MI
begin

text \<open>Predefined abstractions of Loop statemetns, counted as a part of loop invariants in our statistics\<close>

proc (nodef) map_slice:
  requires body: \<open>\<And>k v. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k < length l
                     \<Longrightarrow> \<p>\<r>\<o>\<c> Body v \<lbrace> k \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('b)\<heavy_comma> l ! k \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet> (i+k)\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma> X
                                  \<longmapsto> f k (l ! k) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet> (i+k)\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma> X \<rbrace>\<close>

  input  \<open>len \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T\<heavy_comma> X\<close>
  output \<open>map_index f l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T\<heavy_comma> X\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
\<medium_left_bracket> 
  note \<open>length l = len\<close> [simp] ;;
  map_list_loop ($len) \<open>\<lambda>j. \<m>\<e>\<m>[addr \<tribullet> (i+j)\<^sup>\<t>\<^sup>\<h>] T\<close> \<medium_left_bracket> for j
    body
  \<medium_right_bracket>
\<medium_right_bracket> .


proc (nodef) map_2slice:
  requires body: \<open>\<And>k v. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k < len
                     \<Longrightarrow> \<p>\<r>\<o>\<c> Body v \<lbrace>
                              k \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('b)\<heavy_comma> l\<^sub>a ! k \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a \<tribullet> (i\<^sub>a+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>a\<heavy_comma>
                              l\<^sub>b ! k \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b \<tribullet> (i\<^sub>b+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>b\<heavy_comma> X
                          \<longmapsto> f k (l\<^sub>b ! k) (l\<^sub>a ! k) \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a \<tribullet> (i\<^sub>a+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>a\<heavy_comma>
                              l\<^sub>b ! k \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b \<tribullet> (i\<^sub>b+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>b\<heavy_comma> X
                         \<rbrace>\<close>

  input  \<open>len \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> l\<^sub>a \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<^sub>a\<heavy_comma> l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<^sub>b\<heavy_comma> X\<close>
  output \<open>map_index (\<lambda>i (a,b). f i b a) (zip l\<^sub>a l\<^sub>b) \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<^sub>a\<heavy_comma>
          l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<^sub>b\<heavy_comma> X \<close>
  for T\<^sub>a :: \<open>(mem_fic, 'x) \<phi>\<close>
  and T\<^sub>b :: \<open>(mem_fic, 'y) \<phi>\<close>
\<medium_left_bracket>
  note \<open>length l\<^sub>a = len\<close> [simp] \<open>length l\<^sub>b = len\<close> [simp] ;;
  map_2list_loop ($len) \<open>(\<lambda>j. \<m>\<e>\<m>[addr\<^sub>a \<tribullet> (i\<^sub>a+j)\<^sup>\<t>\<^sup>\<h>] T\<^sub>a, \<lambda>j. \<m>\<e>\<m>[addr\<^sub>b \<tribullet> (i\<^sub>b+j)\<^sup>\<t>\<^sup>\<h>] T\<^sub>b)\<close> \<medium_left_bracket>
    body 
  \<medium_right_bracket>
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 1]]

proc memcpy:
  requires \<open>(\<And>x. Semantic_Type T TY)\<close>
  input  \<open>i\<^sub>a \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>-\<p>\<t>\<r>[addr\<^sub>a:LEN\<^sub>a] TY\<heavy_comma>
          i\<^sub>b \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>-\<p>\<t>\<r>[addr\<^sub>b:LEN\<^sub>b] TY\<heavy_comma>
          len \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma>
          l\<^sub>a \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<heavy_comma>
          l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<close>
  premises \<open>i\<^sub>a + len \<le> LEN\<^sub>a \<and> i\<^sub>b + len \<le> LEN\<^sub>b\<close>
  output \<open>l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<heavy_comma>
          l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<close>
  for T :: \<open>(VAL, 'x) \<phi>\<close>
\<medium_left_bracket>
  map_2slice ($len) \<medium_left_bracket> \<rightarrow> val k ;;
      $i\<^sub>a + $k := ($i\<^sub>b + $k) !
  \<medium_right_bracket>
\<medium_right_bracket> .


end