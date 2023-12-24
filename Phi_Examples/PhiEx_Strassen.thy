theory PhiEx_Strassen
  imports Phi_Semantics.PhiSem_C Jordan_Normal_Form.Matrix
          Phi_Semantics.PhiSem_Int_ArbiPrec
          PhiStd.PhiStd_Loop
begin

declare [[\<phi>trace_reasoning = 0]]

abbreviation \<open>\<m>\<a>\<t> M N \<equiv> \<a>\<r>\<r>\<a>\<y>[M] \<a>\<r>\<r>\<a>\<y>[N] \<a>\<i>\<n>\<t>\<close>

\<phi>type_def MatSlice :: \<open>logaddr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (fiction, nat mat) \<phi>\<close>
  where \<open>x \<Ztypecolon> MatSlice addr i j m n \<equiv> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,m] (\<s>\<l>\<i>\<c>\<e>[j,n] \<nat>)
                                     \<s>\<u>\<b>\<j> l. l = mat_to_list x \<and> dim_row x = m \<and> dim_col x = n\<close>
  deriving \<open>Abstract_Domain (MatSlice addr i j m n) (\<lambda>_. addr \<noteq> 0)\<close>

thm mat_eq_iff

term \<open>map2 (map2 (+))\<close>
lemma mat_to_list_plus:
  \<open> dim_row A = dim_row B
\<Longrightarrow> dim_col A = dim_col B
\<Longrightarrow> map2 (map2 (+)) (mat_to_list A) (mat_to_list B) = mat_to_list (A + B) \<close>
  unfolding mat_to_list_def list_eq_iff_nth_eq
  by auto


proc add_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i\<^sub>x + m \<le> M \<and> i\<^sub>y + m \<le> M \<and> j\<^sub>x + n \<le> N \<and> j\<^sub>y + n \<le> N\<close>
  output \<open>x + y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
\<medium_left_bracket>
  \<open>MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close> to \<open>OPEN _ _\<close>
  \<open>MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<close> to \<open>OPEN _ _\<close> ;;

  map_2list_loop ($m) \<open>(\<lambda>k. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<nat>, \<lambda>k. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<nat>)\<close> \<medium_left_bracket> for k \<rightarrow> val k ;;
    map_2list_loop ($n) \<open>(\<lambda>h. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>y+h)\<^sup>\<t>\<^sup>\<h>] \<nat>, \<lambda>h. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>x+h)\<^sup>\<t>\<^sup>\<h>] \<nat>)\<close> \<medium_left_bracket> for h \<rightarrow> val h ;;
        $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) := $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) ! + $a\<^sub>y \<tribullet> ($i\<^sub>y + $k) \<tribullet> ($j\<^sub>y + $h ) !
    \<medium_right_bracket> ;;
  \<medium_right_bracket> ;;

  \<open>\<m>\<e>\<m>[a\<^sub>x] \<s>\<l>\<i>\<c>\<e>[i\<^sub>x, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<nat>\<close> \<open>x + y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n)\<close>
  \<open>\<m>\<e>\<m>[a\<^sub>y] \<s>\<l>\<i>\<c>\<e>[i\<^sub>y, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<nat>\<close> \<open>_ \<Ztypecolon> MAKE _ (MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n)\<close>
\<medium_right_bracket> .





    term \<open>(\<lambda>h. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>x+h)\<^sup>\<t>\<^sup>\<h>] \<nat>, \<lambda>h. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>x+h)\<^sup>\<t>\<^sup>\<h>] \<nat>)\<close>

    term \<open>(\<lambda>k. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<nat>, \<lambda>k. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<nat>)\<close>

    term \<open>AG_IDX(i\<^sub>y)\<close>

term \<open>Abstract_Domain (MatSlice addr i j n) (\<lambda>_. True)\<close>

term mat_to_list

end