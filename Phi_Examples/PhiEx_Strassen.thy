theory PhiEx_Strassen
  imports Phi_Semantics.PhiSem_C
          Jordan_Normal_Form.Strassen_Algorithm
          Phi_Semantics.PhiSem_Int_ArbiPrec
          PhiStd.PhiStd_Loop
begin

declare [[\<phi>trace_reasoning = 0]]

abbreviation \<open>\<m>\<a>\<t> M N \<equiv> \<a>\<r>\<r>\<a>\<y>[M] \<a>\<r>\<r>\<a>\<y>[N] \<a>\<i>\<n>\<t>\<close>




\<phi>type_def MatSlice :: \<open>logaddr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (fiction, int mat) \<phi>\<close>
  where \<open>x \<Ztypecolon> MatSlice addr i j m n \<equiv> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,m] (\<s>\<l>\<i>\<c>\<e>[j,n] \<int>)
                                     \<s>\<u>\<b>\<j> l. l = mat_to_list x \<and> x \<in> carrier_mat m n\<close>
  deriving \<open>Abstract_Domain (MatSlice addr i j m n) (\<lambda>_. addr \<noteq> 0)\<close>



proc zero_mat:
  input  \<open>x \<Ztypecolon> MatSlice a i j m n\<heavy_comma>
          a \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i + m \<le> M \<and> j + n \<le> N\<close>
  output \<open>0\<^sub>m m n \<Ztypecolon> MatSlice a i j m n\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close>

  map_list_loop ($m) \<open>\<lambda>k. \<m>\<e>\<m>[a \<tribullet>\<^sub>a (i+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j, n] \<int>\<close> \<medium_left_bracket> for k \<rightarrow> val k
    map_list_loop ($n) \<open>\<lambda>h. \<m>\<e>\<m>[a \<tribullet>\<^sub>a (i+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j+h)\<^sup>\<t>\<^sup>\<h>] \<int>\<close> \<medium_left_bracket> for h \<rightarrow> val h
      $a \<tribullet> ($i + $k) \<tribullet> ($j + $h) := \<open>0 \<Ztypecolon> \<int>\<close>
    \<medium_right_bracket>
  \<medium_right_bracket> ;;

  \<open>0\<^sub>m m n \<Ztypecolon> MAKE _ (MatSlice a i j m n)\<close>
    certified unfolding mat_to_list_def list_eq_iff_nth_eq by auto_sledgehammer
\<medium_right_bracket> .



proc add_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i\<^sub>x + m \<le> M \<and> i\<^sub>y + m \<le> M \<and> j\<^sub>x + n \<le> N \<and> j\<^sub>y + n \<le> N\<close>
  output \<open>x + y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
\<medium_left_bracket>
  \<open>MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<close> to \<open>OPEN _ _\<close>
  \<open>MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close> to \<open>OPEN _ _\<close> ;;

  map_2list_loop ($m) \<open>(\<lambda>k. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>, \<lambda>k. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>)\<close> \<medium_left_bracket> for k \<rightarrow> val k
    map_2list_loop ($n) \<open>(\<lambda>h. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>x+h)\<^sup>\<t>\<^sup>\<h>] \<int>, \<lambda>h. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>y+h)\<^sup>\<t>\<^sup>\<h>] \<int>)\<close> \<medium_left_bracket> for h \<rightarrow> val h
        $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) := $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) ! + $a\<^sub>y \<tribullet> ($i\<^sub>y + $k) \<tribullet> ($j\<^sub>y + $h ) !
    \<medium_right_bracket> ;;
  \<medium_right_bracket> ;;

  \<open>\<m>\<e>\<m>[a\<^sub>x] \<s>\<l>\<i>\<c>\<e>[i\<^sub>x, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>\<close> \<open>x + y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n)\<close>
    certified unfolding mat_to_list_def list_eq_iff_nth_eq by auto_sledgehammer ;;
  \<open>\<m>\<e>\<m>[a\<^sub>y] \<s>\<l>\<i>\<c>\<e>[i\<^sub>y, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>\<close> \<open>_ \<Ztypecolon> MAKE _ (MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n)\<close>
\<medium_right_bracket> .




proc sub_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i\<^sub>x + m \<le> M \<and> i\<^sub>y + m \<le> M \<and> j\<^sub>x + n \<le> N \<and> j\<^sub>y + n \<le> N\<close>
  output \<open>x - y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
\<medium_left_bracket>
  \<open>MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<close> to \<open>OPEN _ _\<close>
  \<open>MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close> to \<open>OPEN _ _\<close> ;;

  map_2list_loop ($m) \<open>(\<lambda>k. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>, \<lambda>k. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>)\<close> \<medium_left_bracket> for k \<rightarrow> val k
    map_2list_loop ($n) \<open>(\<lambda>h. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>x+h)\<^sup>\<t>\<^sup>\<h>] \<int>, \<lambda>h. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>y+h)\<^sup>\<t>\<^sup>\<h>] \<int>)\<close> \<medium_left_bracket> for h \<rightarrow> val h
        $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) := $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) ! - $a\<^sub>y \<tribullet> ($i\<^sub>y + $k) \<tribullet> ($j\<^sub>y + $h ) !
    \<medium_right_bracket> ;;
  \<medium_right_bracket> ;;

  \<open>\<m>\<e>\<m>[a\<^sub>x] \<s>\<l>\<i>\<c>\<e>[i\<^sub>x, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>\<close> \<open>x - y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n)\<close>
    certified unfolding mat_to_list_def list_eq_iff_nth_eq by auto_sledgehammer ;;
  \<open>\<m>\<e>\<m>[a\<^sub>y] \<s>\<l>\<i>\<c>\<e>[i\<^sub>y, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>\<close> \<open>_ \<Ztypecolon> MAKE _ (MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n)\<close>
\<medium_right_bracket> .

(*
proc strassen_mut:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
*)


lemma split_4mat:
  \<open> \<p>\<a>\<r>\<a>\<m> (s, t)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> m \<and> t \<le> n
\<Longrightarrow> x \<Ztypecolon> MatSlice a i j m n \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x\<^sub>1\<^sub>1 \<Ztypecolon> MatSlice a i j s t\<heavy_comma> x\<^sub>1\<^sub>2 \<Ztypecolon> MatSlice a i (j+t) s (n-t)\<heavy_comma>
                                    x\<^sub>2\<^sub>1 \<Ztypecolon> MatSlice a (i+s) j (m-s) t\<heavy_comma> x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a (i+s) (j+t) (m-s) (n-t)
                                    \<s>\<u>\<b>\<j> x\<^sub>1\<^sub>1 x\<^sub>1\<^sub>2 x\<^sub>2\<^sub>1 x\<^sub>2\<^sub>2. (x\<^sub>1\<^sub>1, x\<^sub>1\<^sub>2, x\<^sub>2\<^sub>1, x\<^sub>2\<^sub>2) = split_block x s t\<close>
  unfolding MatSlice.unfold \<comment> \<open>open abstraction in both sides\<close>
  \<medium_left_bracket>  \<medium_right_bracket> certified
       by (auto simp: Let_def image_iff split_block_def mat_to_list_def list_eq_iff_nth_eq; auto_sledgehammer) .

lemma merge_4mat:
  \<open> \<p>\<a>\<r>\<a>\<m> (s, t)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> m \<and> t \<le> n
\<Longrightarrow> x\<^sub>1\<^sub>1 \<Ztypecolon> MatSlice a i j s t\<heavy_comma> x\<^sub>1\<^sub>2 \<Ztypecolon> MatSlice a i (j+t) s (n-t)\<heavy_comma>
    x\<^sub>2\<^sub>1 \<Ztypecolon> MatSlice a (i+s) j (m-s) t\<heavy_comma> x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a (i+s) (j+t) (m-s) (n-t)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> four_block_mat x\<^sub>1\<^sub>1 x\<^sub>1\<^sub>2 x\<^sub>2\<^sub>1 x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a i j m n \<close>
  unfolding MatSlice.unfold \<comment> \<open>open abstraction in both sides\<close>
  \<medium_left_bracket> \<medium_right_bracket> certified 
      by (auto simp: four_block_mat_def Let_def mat_to_list_def list_eq_iff_nth_eq
                        \<phi>[unfolded carrier_mat_def, simplified] nth_append; auto_sledgehammer)


end