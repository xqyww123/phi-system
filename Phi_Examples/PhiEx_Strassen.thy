theory PhiEx_Strassen
  imports Phi_Semantics.PhiSem_C
          Jordan_Normal_Form.Strassen_Algorithm
          Phi_Semantics.PhiSem_Int_ArbiPrec
          PhiStd.PhiStd_Loop
          Phi_Semantics.PhiSem_Mem_C_AI
begin

declare One_nat_def[simp del]
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

proc new_mat:
  input  \<open>m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>0\<^sub>m m n \<Ztypecolon> MatSlice a 0 0 m n\<heavy_comma>
          a \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> m n
          \<s>\<u>\<b>\<j> a. address_to_base a\<close> \<comment> \<open>TODO: why is there a syntax warning?\<close>
\<medium_left_bracket>
  calloc_aN2 ($m, $n) \<open>\<int>\<close> \<exists>a
  \<open>0\<^sub>m m n \<Ztypecolon> MAKE _ (MatSlice a 0 0 m n)\<close>
    certified unfolding mat_to_list_def list_eq_iff_nth_eq by auto_sledgehammer
\<medium_right_bracket> .

proc del_mat:
  input  \<open>x \<Ztypecolon> MatSlice a i j m n\<heavy_comma> a \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<close>
  premises \<open>m = M \<and> n = N \<and> i = 0 \<and> j = 0 \<and> address_to_base a\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close>
  mfree ($a)
\<medium_right_bracket> .

proc copy_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>x N\<^sub>x\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>y N\<^sub>y\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y\<close>
  output \<open>y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
\<medium_left_bracket>
  \<open>MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<close> to \<open>OPEN _ _\<close>
  \<open>MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close> to \<open>OPEN _ _\<close> ;;

  map_2list_loop ($m) \<open>(\<lambda>k. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>, \<lambda>k. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h>] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>)\<close> \<medium_left_bracket> for k \<rightarrow> val k
    map_2list_loop ($n) \<open>(\<lambda>h. \<m>\<e>\<m>[a\<^sub>x \<tribullet>\<^sub>a (i\<^sub>x+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>x+h)\<^sup>\<t>\<^sup>\<h>] \<int>, \<lambda>h. \<m>\<e>\<m>[a\<^sub>y \<tribullet>\<^sub>a (i\<^sub>y+k)\<^sup>\<t>\<^sup>\<h> \<tribullet>\<^sub>a (j\<^sub>y+h)\<^sup>\<t>\<^sup>\<h>] \<int>)\<close> \<medium_left_bracket> for h \<rightarrow> val h
        $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) := $a\<^sub>y \<tribullet> ($i\<^sub>y + $k) \<tribullet> ($j\<^sub>y + $h ) !
    \<medium_right_bracket> ;;
  \<medium_right_bracket> ;;

  \<open>\<m>\<e>\<m>[a\<^sub>x] \<s>\<l>\<i>\<c>\<e>[i\<^sub>x, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>\<close> \<open>y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n)\<close>
    certified unfolding mat_to_list_def list_eq_iff_nth_eq by auto_sledgehammer ;;
  \<open>\<m>\<e>\<m>[a\<^sub>y] \<s>\<l>\<i>\<c>\<e>[i\<^sub>y, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>\<close> \<open>_ \<Ztypecolon> MAKE _ (MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n)\<close>
\<medium_right_bracket> .


proc add_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>x N\<^sub>x\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>y N\<^sub>y\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y\<close>
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
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>x N\<^sub>x\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>y N\<^sub>y\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y \<close>
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
  \<open> \<p>\<a>\<r>\<a>\<m> (i, s, j, t)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> m \<and> t \<le> n
\<Longrightarrow> x\<^sub>1\<^sub>1 \<Ztypecolon> MatSlice a i j s t\<heavy_comma> x\<^sub>1\<^sub>2 \<Ztypecolon> MatSlice a i (j+t) s (n-t)\<heavy_comma>
    x\<^sub>2\<^sub>1 \<Ztypecolon> MatSlice a (i+s) j (m-s) t\<heavy_comma> x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a (i+s) (j+t) (m-s) (n-t)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> four_block_mat x\<^sub>1\<^sub>1 x\<^sub>1\<^sub>2 x\<^sub>2\<^sub>1 x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a i j m n \<close>
  unfolding MatSlice.unfold \<comment> \<open>open abstraction in both sides\<close>
  \<medium_left_bracket> \<medium_right_bracket> certified
      by (clarsimp simp: four_block_mat_def Let_def mat_to_list_def list_eq_iff_nth_eq
                        \<phi>[unfolded carrier_mat_def, simplified] nth_append; auto_sledgehammer) .


proc strassen:
  input  \<open>A \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x (2^n) (2^n)\<heavy_comma>
          B \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y (2^n) (2^n)\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> N\<^sub>x N\<^sub>x\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> N\<^sub>y N\<^sub>y\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          n \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i\<^sub>x + 2^n \<le> N\<^sub>x \<and> j\<^sub>x + 2^n \<le> N\<^sub>x \<and> i\<^sub>y + 2^n \<le> N\<^sub>y \<and> j\<^sub>y + 2^n \<le> N\<^sub>y\<close>
  output \<open>A * B \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x (2^n) (2^n)\<heavy_comma>
          B \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y (2^n) (2^n)\<close>
  is [recursive A B n a\<^sub>x i\<^sub>x j\<^sub>x a\<^sub>y i\<^sub>y j\<^sub>y N\<^sub>x N\<^sub>y]
\<medium_left_bracket>
  if ($n = \<open>0 \<Ztypecolon> \<nat>\<close>)
  \<medium_left_bracket>
    \<open>MatSlice a\<^sub>x _ _ _ _\<close> to \<open>OPEN _ _\<close>
    \<open>MatSlice a\<^sub>y _ _ _ _\<close> to \<open>OPEN _ _\<close> ;;

    $a\<^sub>x \<tribullet> $i\<^sub>x \<tribullet> $j\<^sub>x := $a\<^sub>x \<tribullet> $i\<^sub>x \<tribullet> $j\<^sub>x ! * $a\<^sub>y \<tribullet> $i\<^sub>y \<tribullet> $j\<^sub>y ! ;;

    \<open>A * B \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x (2^n) (2^n))\<close> certified  unfolding mat_to_list_def list_eq_iff_nth_eq sorry
  \<medium_right_bracket>
  \<medium_left_bracket>
    \<open>MatSlice a\<^sub>x _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>A\<^sub>1\<^sub>1, A\<^sub>1\<^sub>2, A\<^sub>2\<^sub>1, A\<^sub>2\<^sub>2 ;;
    \<open>MatSlice a\<^sub>y _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>B\<^sub>1\<^sub>1, B\<^sub>1\<^sub>2, B\<^sub>2\<^sub>1, B\<^sub>2\<^sub>2 ;;

    have [simp]: \<open>(2::nat) ^ n - 2 ^ (n - 1) = 2 ^ (n - 1)\<close>
      by (simp add: \<open>n \<noteq> 0\<close> mult_2 power_eq_if);;

    1 << ($n-1) \<rightarrow> val N ;;
    $i\<^sub>x + $N \<rightarrow> val i\<^sub>x' ;;
    $j\<^sub>x + $N \<rightarrow> val j\<^sub>x' ;;
    $i\<^sub>y + $N \<rightarrow> val i\<^sub>y' ;;
    $j\<^sub>y + $N \<rightarrow> val j\<^sub>y' ;;


    new_mat ($N, $N) \<exists>M\<^sub>1 \<rightarrow> val M\<^sub>1 ;;
    new_mat ($N, $N) \<exists>M\<^sub>2 \<rightarrow> val M\<^sub>2 ;;
    new_mat ($N, $N) \<exists>M\<^sub>3 \<rightarrow> val M\<^sub>3 ;;
    new_mat ($N, $N) \<exists>M\<^sub>4 \<rightarrow> val M\<^sub>4 ;;
    new_mat ($N, $N) \<exists>M\<^sub>5 \<rightarrow> val M\<^sub>5 ;;
    new_mat ($N, $N) \<exists>M\<^sub>6 \<rightarrow> val M\<^sub>6 ;;
    new_mat ($N, $N) \<exists>M\<^sub>7 \<rightarrow> val M\<^sub>7 ;;
    new_mat ($N, $N) \<exists>t \<rightarrow> val t ;;

    copy_mat ($M\<^sub>1, 0, 0, $a\<^sub>x, $i\<^sub>x, $j\<^sub>x, $N, $N) ;;
    add_mat  ($M\<^sub>1, 0, 0, $a\<^sub>x, $i\<^sub>x', $j\<^sub>x', $N, $N) ;;
    copy_mat ($t, 0, 0, $a\<^sub>y, $i\<^sub>y, $j\<^sub>y, $N, $N) ;;
    add_mat  ($t, 0, 0, $a\<^sub>y, $i\<^sub>y', $j\<^sub>y', $N, $N) ;;
    strassen ($M\<^sub>1, 0, 0, $t, 0, 0, $n-1) ;;

    copy_mat ($M\<^sub>2, 0, 0, $a\<^sub>x, $i\<^sub>x', $j\<^sub>x, $N, $N) ;;
    add_mat  ($M\<^sub>2, 0, 0, $a\<^sub>x, $i\<^sub>x', $j\<^sub>x', $N, $N) ;;
    strassen ($M\<^sub>2, 0, 0, $a\<^sub>y, $i\<^sub>y, $j\<^sub>y, $n-1) ;;

    copy_mat ($M\<^sub>3, 0, 0, $a\<^sub>y, $i\<^sub>y, $j\<^sub>y', $N, $N) ;;
    sub_mat  ($M\<^sub>3, 0, 0, $a\<^sub>y, $i\<^sub>y', $j\<^sub>y', $N, $N) ;;
    strassen ($M\<^sub>3, 0, 0, $a\<^sub>x, $i\<^sub>x, $j\<^sub>x, $n-1) ;;

    copy_mat ($M\<^sub>4, 0, 0, $a\<^sub>y, $i\<^sub>y', $j\<^sub>y, $N, $N)
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      
                                                      ;;
    sub_mat  ($M\<^sub>4, 0, 0, $a\<^sub>y, $i\<^sub>y, $j\<^sub>y, $N, $N) ;;
    strassen ($M\<^sub>4, 0, 0, $a\<^sub>x, $i\<^sub>x', $j\<^sub>x', $n-1) ;;

    copy_mat ($M\<^sub>5, 0, 0, $a\<^sub>x, $i\<^sub>x, $j\<^sub>x, $N, $N) ;;
    add_mat  ($M\<^sub>5, 0, 0, $a\<^sub>x, $i\<^sub>x, $j\<^sub>x', $N, $N) ;;
    strassen ($M\<^sub>5, 0, 0, $a\<^sub>y, $i\<^sub>y', $j\<^sub>y', $n-1) ;;

    copy_mat ($M\<^sub>6, 0, 0, $a\<^sub>x, $i\<^sub>x', $j\<^sub>x, $N, $N) ;;
    sub_mat  ($M\<^sub>6, 0, 0, $a\<^sub>x, $i\<^sub>x, $j\<^sub>x, $N, $N) ;;
    copy_mat ($t, 0, 0, $a\<^sub>y, $i\<^sub>y, $j\<^sub>y, $N, $N) ;;
    add_mat  ($t, 0, 0, $a\<^sub>y, $i\<^sub>y, $j\<^sub>y', $N, $N) ;;
    strassen ($M\<^sub>6, 0, 0, $t, 0, 0, $n-1) ;;

    copy_mat ($M\<^sub>7, 0, 0, $a\<^sub>x, $i\<^sub>x, $j\<^sub>x', $N, $N) ;;
    sub_mat  ($M\<^sub>7, 0, 0, $a\<^sub>x, $i\<^sub>x', $j\<^sub>x', $N, $N) ;;
    copy_mat ($t, 0, 0, $a\<^sub>y, $i\<^sub>y', $j\<^sub>y, $N, $N) ;;
    add_mat  ($t, 0, 0, $a\<^sub>y, $i\<^sub>y', $j\<^sub>y', $N, $N) ;;
    strassen ($M\<^sub>7, 0, 0, $t, 0, 0, $n-1) ;;

    del_mat ($t)

    add_mat  ($M\<^sub>7, 0, 0, $M\<^sub>1, 0, 0, $N, $N) ;;
    add_mat  ($M\<^sub>7, 0, 0, $M\<^sub>4, 0, 0, $N, $N) ;;
    sub_mat  ($M\<^sub>7, 0, 0, $M\<^sub>5, 0, 0, $N, $N) ;;
    copy_mat ($a\<^sub>x, $i\<^sub>x, $j\<^sub>x, $M\<^sub>7, 0, 0, $N, $N) ;;

    add_mat  ($M\<^sub>5, 0, 0, $M\<^sub>3, 0, 0, $N, $N) ;;
    copy_mat ($a\<^sub>x, $i\<^sub>x, $j\<^sub>x', $M\<^sub>7, 0, 0, $N, $N) ;;

    add_mat  ($M\<^sub>4, 0, 0, $M\<^sub>2, 0, 0, $N, $N) ;;
    copy_mat ($a\<^sub>x, $i\<^sub>x', $j\<^sub>x, $M\<^sub>4, 0, 0, $N, $N) ;;

    add_mat  ($M\<^sub>6, 0, 0, $M\<^sub>1, 0, 0, $N, $N) ;;
    sub_mat  ($M\<^sub>6, 0, 0, $M\<^sub>2, 0, 0, $N, $N) ;;
    add_mat  ($M\<^sub>6, 0, 0, $M\<^sub>3, 0, 0, $N, $N) ;;
    copy_mat ($a\<^sub>x, $i\<^sub>x', $j\<^sub>x', $M\<^sub>6, 0, 0, $N, $N) ;;

    del_mat ($M\<^sub>1) ;;
    del_mat ($M\<^sub>2) ;;
    del_mat ($M\<^sub>3) ;;
    del_mat ($M\<^sub>4) ;;
    del_mat ($M\<^sub>5) ;;
    del_mat ($M\<^sub>6) ;;
    del_mat ($M\<^sub>7) ;;
thm useful ;;
    apply_rule merge_4mat[where a=a\<^sub>x and i=i\<^sub>x and s=\<open>2 ^ (n - 1)\<close> and j=j\<^sub>x and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified] \<open>(i\<^sub>x, 2 ^ (n - 1), j\<^sub>x, 2 ^ (n - 1))\<close>
      is \<open>A * B\<close> certified apply (simp add: add_mult_distrib_mat minus_mult_distrib_mat add_carrier_mat uminus_carrier_iff_mat
                                            mult_add_distrib_mat mult_minus_distrib_mat assoc_add_mat comm_add_mat)

thm useful
;;


apply_rule merge_4mat[where a=a\<^sub>y and i=i\<^sub>y and s=\<open>2 ^ (n - 1)\<close> and j=j\<^sub>y and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified]
                        \<open>(i\<^sub>y, 2 ^ (n - 1), j\<^sub>y, 2 ^ (n - 1))\<close> ;;

    











    text \<open>TODO: paper: we cannot determine the type of literals\<close>





end