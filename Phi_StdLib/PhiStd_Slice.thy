theory PhiStd_Slice \<comment> \<open>'a' for arbitary precision interger\<close>
  imports PhiStd_Loop
          Phi_Semantics.PhiSem_Mem_C_Ar_MI
begin

proc (nodef) map_slice:
  requires body: \<open>\<And>k v. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k < length l
                     \<Longrightarrow> \<p>\<r>\<o>\<c> Body v \<lbrace> X\<heavy_comma> l ! k \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a (i+k)\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('b)
                                  \<longmapsto> X\<heavy_comma> f k (l ! k) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a (i+k)\<^sup>\<t>\<^sup>\<h>] T \<rbrace>\<close>

  input  \<open>X\<heavy_comma> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T\<heavy_comma> len \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close>
  output \<open>X\<heavy_comma> map_index f l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
\<medium_left_bracket>
  note \<open>length l = len\<close> [simp] ;;
  map_list_loop ($len) \<open>\<lambda>j. \<m>\<e>\<m>[addr \<tribullet>\<^sub>a (i+j)\<^sup>\<t>\<^sup>\<h>] T\<close> \<medium_left_bracket> for j
    body
  \<medium_right_bracket>
\<medium_right_bracket> .


proc (nodef) map_2slice:
  requires body: \<open>\<And>k v. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k < len
                     \<Longrightarrow> \<p>\<r>\<o>\<c> Body v \<lbrace> X\<heavy_comma> l\<^sub>a ! k \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a \<tribullet>\<^sub>a (i\<^sub>a+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>a\<heavy_comma>
                                         l\<^sub>b ! k \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b \<tribullet>\<^sub>a (i\<^sub>b+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>b\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('b)
                                  \<longmapsto> X\<heavy_comma> f k (l\<^sub>b ! k) (l\<^sub>a ! k) \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a \<tribullet>\<^sub>a (i\<^sub>a+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>a\<heavy_comma>
                                         l\<^sub>b ! k \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b \<tribullet>\<^sub>a (i\<^sub>b+k)\<^sup>\<t>\<^sup>\<h>] T\<^sub>b \<rbrace>\<close>

  input  \<open>X\<heavy_comma> l\<^sub>a \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<^sub>a\<heavy_comma> l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<^sub>b\<heavy_comma> len \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close>
  output \<open>X\<heavy_comma> map_index (\<lambda>i (a,b). f i b a) (zip l\<^sub>a l\<^sub>b) \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<^sub>a\<heavy_comma>
             l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<^sub>b \<close>
  for T\<^sub>a :: \<open>(mem_fic, 'x) \<phi>\<close>
  and T\<^sub>b :: \<open>(mem_fic, 'y) \<phi>\<close>
\<medium_left_bracket>
  note \<open>length l\<^sub>a = len\<close> [simp] \<open>length l\<^sub>b = len\<close> [simp] ;;
  map_2list_loop ($len) \<open>(\<lambda>j. \<m>\<e>\<m>[addr\<^sub>a \<tribullet>\<^sub>a (i\<^sub>a+j)\<^sup>\<t>\<^sup>\<h>] T\<^sub>a, \<lambda>j. \<m>\<e>\<m>[addr\<^sub>b \<tribullet>\<^sub>a (i\<^sub>b+j)\<^sup>\<t>\<^sup>\<h>] T\<^sub>b)\<close> \<medium_left_bracket>
    body 
  \<medium_right_bracket>
\<medium_right_bracket> .


proc memcpy:
  requires \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY)\<close>
  input  \<open>l\<^sub>a \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<heavy_comma> l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<heavy_comma>
          i\<^sub>a \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr\<^sub>a:LEN\<^sub>a] TY\<heavy_comma> i\<^sub>b \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr\<^sub>b:LEN\<^sub>b] TY\<heavy_comma> len \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close>
  premises \<open>i\<^sub>a + len \<le> LEN\<^sub>a \<and> i\<^sub>b + len \<le> LEN\<^sub>b\<close>
  output \<open>l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>a] \<s>\<l>\<i>\<c>\<e>[i\<^sub>a,len] T\<heavy_comma> l\<^sub>b \<Ztypecolon> \<m>\<e>\<m>[addr\<^sub>b] \<s>\<l>\<i>\<c>\<e>[i\<^sub>b,len] T\<close>
  for T :: \<open>(VAL, 'x) \<phi>\<close>
\<medium_left_bracket>
  map_2slice ($len) \<medium_left_bracket> \<rightarrow> val k ;;
      $i\<^sub>a + $k := ($i\<^sub>b + $k) !
  \<medium_right_bracket>
\<medium_right_bracket> .


end