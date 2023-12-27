theory PhiStd_Slice_a \<comment> \<open>'a' for arbitary precision interger\<close>
  imports PhiStd_Loop_a
          Phi_Semantics.PhiSem_Mem_C_Ag_Ar
begin

proc map_slice:
  requires body: \<open>\<And>k v. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k < length l
                     \<Longrightarrow> \<p>\<r>\<o>\<c> Body v \<lbrace> X\<heavy_comma> l ! k \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a (i+k)\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>
                                  \<longmapsto> X\<heavy_comma> f k (l ! k) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a (i+k)\<^sup>\<t>\<^sup>\<h>] T \<rbrace>\<close>
  premises \<open>length l = len\<close>

  input  \<open>X\<heavy_comma> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T\<heavy_comma> len \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>X\<heavy_comma> map_index f l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] T\<close> 
\<medium_left_bracket>
  map_list_loop ($len) \<open>\<lambda>j. \<m>\<e>\<m>[addr \<tribullet>\<^sub>a (i+j)\<^sup>\<t>\<^sup>\<h>] T\<close> \<medium_left_bracket> for j
    body
  \<medium_right_bracket> ;;
\<medium_right_bracket> .











end