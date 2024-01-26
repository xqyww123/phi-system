theory PhiEx_Strassen
  imports Phi_Semantics.PhiSem_C
          Jordan_Normal_Form.Matrix \<comment> \<open>We don't import the existing proofs for Strassen Multiplication,
                                        but only the common library for matrix.
                                        Instead we manually copy the proof code of the Strassen Multiplication
                                        here, to ensure our statistics precise.\<close>
          (*Phi_Semantics.PhiSem_Int_ArbiPrec*)
          PhiStd.PhiStd_Slice
          Phi_Semantics.PhiSem_Mem_C_MI
begin

abbreviation \<open>\<m>\<a>\<t> M N \<equiv> \<a>\<r>\<r>\<a>\<y>[M] \<a>\<r>\<r>\<a>\<y>[N] \<i>\<n>\<t>\<close>

\<phi>type_def MatSlice :: \<open>logaddr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (fiction, int mat) \<phi>\<close>
  where \<open>x \<Ztypecolon> MatSlice addr i j m n \<equiv> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,m] (\<s>\<l>\<i>\<c>\<e>[j,n] \<int>\<^sup>r(\<i>\<n>\<t>))
                                     \<s>\<u>\<b>\<j> l. l = mat_to_list x \<and> x \<in> carrier_mat m n\<close>
  deriving \<open>Abstract_Domain (MatSlice addr i j m n) (\<lambda>x. addr \<noteq> 0 \<and> x \<in> carrier_mat m n)\<close>
       and \<open>Object_Equiv (MatSlice addr i j m n) (=)\<close>
       and Basic


declare mat_to_list_def [\<phi>sledgehammer_simps] list_eq_iff_nth_eq [\<phi>sledgehammer_simps]   (*counted in Tac-4m,*)
        list_all2_conv_all_nth[\<phi>sledgehammer_simps] zero_mat_def[\<phi>sledgehammer_simps]    (*as 2 proof lines*)

proc zero_mat:
  input  \<open>x \<Ztypecolon> MatSlice a i j m n\<heavy_comma>
          a \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  premises \<open>i + m \<le> M \<and> j + n \<le> N \<and> M < 2 ^ addrspace_bits \<and> N < 2 ^ addrspace_bits\<close>
  output \<open>0\<^sub>m m n \<Ztypecolon> MatSlice a i j m n\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close>

  map_slice ($m) \<medium_left_bracket> for k \<rightarrow> val k ;;
    map_slice ($n) \<medium_left_bracket> for h \<rightarrow> val h ;;
      $a \<tribullet> ($i + $k) \<tribullet> ($j + $h) := \<open>0 \<Ztypecolon> \<int>\<^sup>r(\<i>\<n>\<t>)\<close>
    \<medium_right_bracket>
  \<medium_right_bracket> ;;

  \<open>0\<^sub>m m n \<Ztypecolon> MAKE _ (MatSlice a i j m n)\<close>
\<medium_right_bracket> .


proc new_mat:
  requires \<open>\<p>\<a>\<r>\<a>\<m> M\<close>
  requires \<open>\<p>\<a>\<r>\<a>\<m> N\<close>
  input  \<open>Void\<close>
  output \<open>0\<^sub>m M N \<Ztypecolon> MatSlice a 0 0 M N\<heavy_comma>
          a \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M N
          \<s>\<u>\<b>\<j> a. address_to_base a\<close> \<comment> \<open>TODO: why is there a syntax warning?\<close>
\<medium_left_bracket>
  calloc_1 \<open>\<Aa>\<r>\<r>\<a>\<y>[M] \<Aa>\<r>\<r>\<a>\<y>[N] \<int>\<^sup>r(\<i>\<n>\<t>)\<close> 
  \<open>0\<^sub>m M N \<Ztypecolon> MAKE _ (MatSlice addr 0 0 M N)\<close>
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
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>x N\<^sub>x\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>y N\<^sub>y\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y \<and>
            M\<^sub>x < 2 ^ addrspace_bits \<and> N\<^sub>x < 2 ^ addrspace_bits \<and>
            M\<^sub>y < 2 ^ addrspace_bits \<and> N\<^sub>y < 2 ^ addrspace_bits\<close>
  output \<open>y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
\<medium_left_bracket>
  \<open>MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<close> to \<open>OPEN _ _\<close>
  \<open>MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close> to \<open>OPEN _ _\<close> ;;

  map_2slice ($m) \<medium_left_bracket> for k \<rightarrow> val k ;;
    map_2slice ($n) \<medium_left_bracket> for h \<rightarrow> val h ;;
      $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) := $a\<^sub>y \<tribullet> ($i\<^sub>y + $k) \<tribullet> ($j\<^sub>y + $h ) !
    \<medium_right_bracket> ;;
  \<medium_right_bracket> ;;

  \<open>\<m>\<e>\<m>[a\<^sub>x] \<s>\<l>\<i>\<c>\<e>[i\<^sub>x, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>\<^sup>r(\<i>\<n>\<t>)\<close> \<open>y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n)\<close> ;;
  \<open>\<m>\<e>\<m>[a\<^sub>y] \<s>\<l>\<i>\<c>\<e>[i\<^sub>y, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>\<^sup>r(\<i>\<n>\<t>)\<close> \<open>y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n)\<close>
\<medium_right_bracket> .


proc add_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>x N\<^sub>x\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>y N\<^sub>y\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y \<and>
            M\<^sub>x < 2 ^ addrspace_bits \<and> N\<^sub>x < 2 ^ addrspace_bits \<and>
            M\<^sub>y < 2 ^ addrspace_bits \<and> N\<^sub>y < 2 ^ addrspace_bits\<close>
  output \<open>x + y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
\<medium_left_bracket>
  \<open>MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<close> to \<open>OPEN _ _\<close>
  \<open>MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close> to \<open>OPEN _ _\<close> ;;

  map_2slice ($m) \<medium_left_bracket> for k \<rightarrow> val k
    map_2slice ($n) \<medium_left_bracket> for h \<rightarrow> val h
        $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) := $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) ! + $a\<^sub>y \<tribullet> ($i\<^sub>y + $k) \<tribullet> ($j\<^sub>y + $h ) !
    \<medium_right_bracket> ;;
  \<medium_right_bracket> ;;

  \<open>\<m>\<e>\<m>[a\<^sub>x] \<s>\<l>\<i>\<c>\<e>[i\<^sub>x, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>\<^sup>r(\<i>\<n>\<t>)\<close> \<open>x + y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n)\<close> ;;
  \<open>\<m>\<e>\<m>[a\<^sub>y] \<s>\<l>\<i>\<c>\<e>[i\<^sub>y, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>\<^sup>r(\<i>\<n>\<t>)\<close> \<open>y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n)\<close>
\<medium_right_bracket> .


proc sub_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
          y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>x N\<^sub>x\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> M\<^sub>y N\<^sub>y\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          m \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y \<and>
            M\<^sub>x < 2 ^ addrspace_bits \<and> N\<^sub>x < 2 ^ addrspace_bits \<and>
            M\<^sub>y < 2 ^ addrspace_bits \<and> N\<^sub>y < 2 ^ addrspace_bits \<close>
  output \<open>x - y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
\<medium_left_bracket>
  \<open>MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<close> to \<open>OPEN _ _\<close>
  \<open>MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close> to \<open>OPEN _ _\<close> ;;

  map_2slice ($m) \<medium_left_bracket> for k \<rightarrow> val k ;;
    map_2slice ($n) \<medium_left_bracket> for h \<rightarrow> val h ;;
      $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) := $a\<^sub>x \<tribullet> ($i\<^sub>x + $k) \<tribullet> ($j\<^sub>x + $h) ! - $a\<^sub>y \<tribullet> ($i\<^sub>y + $k) \<tribullet> ($j\<^sub>y + $h ) ! 
    \<medium_right_bracket> ;;
  \<medium_right_bracket> ;;

  \<open>\<m>\<e>\<m>[a\<^sub>x] \<s>\<l>\<i>\<c>\<e>[i\<^sub>x, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>x, n] \<int>\<^sup>r(\<i>\<n>\<t>)\<close> \<open>x - y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n)\<close> ;;
  \<open>\<m>\<e>\<m>[a\<^sub>y] \<s>\<l>\<i>\<c>\<e>[i\<^sub>y, m] \<s>\<l>\<i>\<c>\<e>[j\<^sub>y, n] \<int>\<^sup>r(\<i>\<n>\<t>)\<close> \<open>y \<Ztypecolon> MAKE _ (MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n)\<close>
\<medium_right_bracket> .


context
  notes [\<phi>sledgehammer_simps] = Let_def image_iff split_block_def four_block_mat_def mat_to_list_def
                                list_eq_iff_nth_eq nth_append         (*counted as Tac-7m, 2 proof lines*)
begin

lemma split_4mat:
  \<open> \<p>\<a>\<r>\<a>\<m> (s, t)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> m \<and> t \<le> n
\<Longrightarrow> x \<Ztypecolon> MatSlice a i j m n \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x\<^sub>1\<^sub>1 \<Ztypecolon> MatSlice a i j s t\<heavy_comma> x\<^sub>1\<^sub>2 \<Ztypecolon> MatSlice a i (j+t) s (n-t)\<heavy_comma>
                                    x\<^sub>2\<^sub>1 \<Ztypecolon> MatSlice a (i+s) j (m-s) t\<heavy_comma> x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a (i+s) (j+t) (m-s) (n-t)
                                    \<s>\<u>\<b>\<j> x\<^sub>1\<^sub>1 x\<^sub>1\<^sub>2 x\<^sub>2\<^sub>1 x\<^sub>2\<^sub>2. (x\<^sub>1\<^sub>1, x\<^sub>1\<^sub>2, x\<^sub>2\<^sub>1, x\<^sub>2\<^sub>2) = split_block x s t\<close>
  unfolding MatSlice.unfold \<comment> \<open>open abstraction in both sides\<close>
  \<medium_left_bracket>  \<medium_right_bracket> certified by (auto_sledgehammer) .

lemma merge_4mat:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> m \<and> t \<le> n
\<Longrightarrow> x\<^sub>1\<^sub>1 \<Ztypecolon> MatSlice a i j s t\<heavy_comma> x\<^sub>1\<^sub>2 \<Ztypecolon> MatSlice a i (j+t) s (n-t)\<heavy_comma>
    x\<^sub>2\<^sub>1 \<Ztypecolon> MatSlice a (i+s) j (m-s) t\<heavy_comma> x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a (i+s) (j+t) (m-s) (n-t)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> four_block_mat x\<^sub>1\<^sub>1 x\<^sub>1\<^sub>2 x\<^sub>2\<^sub>1 x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a i j m n \<close>
  unfolding MatSlice.unfold \<comment> \<open>open abstraction in both sides\<close>
  \<medium_left_bracket> \<medium_right_bracket> certified by (clarsimp simp: \<phi>sledgehammer_simps \<phi>[unfolded carrier_mat_def, simplified]; auto_sledgehammer) .

end


context
  fixes N :: nat
begin
 
proc strassen:
  input  \<open>A \<Ztypecolon> MatSlice a\<^sub>A i\<^sub>A j\<^sub>A (2^n) (2^n)\<heavy_comma>
          B \<Ztypecolon> MatSlice a\<^sub>B i\<^sub>B j\<^sub>B (2^n) (2^n)\<heavy_comma>
          buf\<^sub>1 \<Ztypecolon> MatSlice a\<^sub>C i\<^sub>C j\<^sub>C (2^n) (2^n)\<heavy_comma> \<comment> \<open>buffers used to store intermediate values\<close>
          buf\<^sub>2 \<Ztypecolon> MatSlice a\<^sub>D i\<^sub>D j\<^sub>D (2^n) (2^n)\<heavy_comma>
          a\<^sub>A \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> N N\<heavy_comma> i\<^sub>A \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>A \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          a\<^sub>B \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> N N\<heavy_comma> i\<^sub>B \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>B \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          a\<^sub>C \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> N N\<heavy_comma> i\<^sub>C \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>C \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          a\<^sub>D \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> N N\<heavy_comma> i\<^sub>D \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> j\<^sub>D \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma>
          n \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  premises \<open>i\<^sub>A + 2^n \<le> N \<and> j\<^sub>A + 2^n \<le> N \<and>
            i\<^sub>B + 2^n \<le> N \<and> j\<^sub>B + 2^n \<le> N \<and>
            i\<^sub>C + 2^n \<le> N \<and> j\<^sub>C + 2^n \<le> N \<and>
            i\<^sub>D + 2^n \<le> N \<and> j\<^sub>D + 2^n \<le> N \<and>
            M < 2 ^ addrspace_bits \<and> N < 2 ^ addrspace_bits\<close>
  output \<open>A * B \<Ztypecolon> MatSlice a\<^sub>A i\<^sub>A j\<^sub>A (2^n) (2^n)\<heavy_comma>
          B \<Ztypecolon> MatSlice a\<^sub>B i\<^sub>B j\<^sub>B (2^n) (2^n)\<heavy_comma>
          buf\<^sub>1 \<Ztypecolon> MatSlice a\<^sub>C i\<^sub>C j\<^sub>C (2^n) (2^n)\<heavy_comma> \<comment> \<open>buffers used to store intermediate values\<close>
          buf\<^sub>2 \<Ztypecolon> MatSlice a\<^sub>D i\<^sub>D j\<^sub>D (2^n) (2^n)
          \<s>\<u>\<b>\<j> buf\<^sub>1 buf\<^sub>2. \<top>\<close>
  is [recursive]
\<medium_left_bracket>
  if ($n = 0)
  \<medium_left_bracket>
    \<open>MatSlice a\<^sub>A _ _ _ _\<close> to \<open>OPEN _ _\<close>
    \<open>MatSlice a\<^sub>B _ _ _ _\<close> to \<open>OPEN _ _\<close> ;;

    $a\<^sub>A \<tribullet> $i\<^sub>A \<tribullet> $j\<^sub>A := $a\<^sub>A \<tribullet> $i\<^sub>A \<tribullet> $j\<^sub>A ! * $a\<^sub>B \<tribullet> $i\<^sub>B \<tribullet> $j\<^sub>B ! ;;
      
    holds_fact [\<phi>sledgehammer_simps]: \<open>dim_col B = 1 \<and> dim_row B = 1 \<and> dim_col A = 1 \<and> dim_row A = 1\<close> (*for proof, Tac-s*)
    note scalar_prod_def [\<phi>sledgehammer_simps] ;;                                       (*for proof, Tac-m*)

    \<open>A * B \<Ztypecolon> MAKE _ (MatSlice a\<^sub>A i\<^sub>A j\<^sub>A (2^n) (2^n))\<close> ;;
    \<open>B \<Ztypecolon> MAKE _ (MatSlice a\<^sub>B i\<^sub>B j\<^sub>B (2^n) (2^n))\<close>
  \<medium_right_bracket>
  \<medium_left_bracket>
    holds_fact t0: \<open>(2::nat) ^ n = 2 ^ (n - 1) + 2 ^ (n - 1)\<close>                          (*for proof, Tac-s*)
    holds_fact t1[simp]: \<open>(2::nat) ^ n - 2 ^ (n - 1) = 2 ^ (n - 1)\<close> ;;                 (*for reasoning, A*)
        \<comment> \<open>Even when ML-aided ATP \<open>Sledgehammer\<close> is so powerful now, it cannot solve some simple
            high-school problems without the \<open>t0\<close> hint ...\<close>

    \<open>MatSlice a\<^sub>A _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>A\<^sub>1\<^sub>1, A\<^sub>1\<^sub>2, A\<^sub>2\<^sub>1, A\<^sub>2\<^sub>2 ;;
    \<open>MatSlice a\<^sub>B _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>B\<^sub>1\<^sub>1, B\<^sub>1\<^sub>2, B\<^sub>2\<^sub>1, B\<^sub>2\<^sub>2 ;;
    \<open>MatSlice a\<^sub>C _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>M\<^sub>1, M\<^sub>2, M\<^sub>3, M\<^sub>4 ;;
    \<open>MatSlice a\<^sub>D _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>M\<^sub>5, M\<^sub>6, M\<^sub>7, M\<^sub>t ;;

    holds_fact t2: \<open>n < addrspace_bits\<close> ;;                                              (*for proof, Tac-s*)

    1 << ($n-1) \<rightarrow> val N ;;
    $i\<^sub>A + $N \<rightarrow> val i\<^sub>A' ;;
    $j\<^sub>A + $N \<rightarrow> val j\<^sub>A' ;;
    $i\<^sub>B + $N \<rightarrow> val i\<^sub>B' ;;
    $j\<^sub>B + $N \<rightarrow> val j\<^sub>B' ;;
    $i\<^sub>C + $N \<rightarrow> val i\<^sub>C' ;;
    $j\<^sub>C + $N \<rightarrow> val j\<^sub>C' ;;
    $i\<^sub>D + $N \<rightarrow> val i\<^sub>D' ;;
    $j\<^sub>D + $N \<rightarrow> val j\<^sub>D' ;;

    copy_mat ($a\<^sub>C, $i\<^sub>C , $j\<^sub>C,  (*M\<^sub>1*) $a\<^sub>A, $i\<^sub>A , $j\<^sub>A , (*A\<^sub>1\<^sub>1*) $N, $N) ;;
    add_mat  ($a\<^sub>C, $i\<^sub>C , $j\<^sub>C,  (*M\<^sub>1*) $a\<^sub>A, $i\<^sub>A', $j\<^sub>A', (*A\<^sub>2\<^sub>2*) $N, $N) ;;
    copy_mat ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B , $j\<^sub>B , (*B\<^sub>1\<^sub>1*) $N, $N) ;;
    add_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B', $j\<^sub>B', (*B\<^sub>2\<^sub>2*) $N, $N) ;;
    strassen ($a\<^sub>C, $i\<^sub>C , $j\<^sub>C , (*M\<^sub>1*) $a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t *)
              $a\<^sub>C, $i\<^sub>C , $j\<^sub>C', (*M\<^sub>2*) $a\<^sub>C, $i\<^sub>C', $j\<^sub>C , (*M\<^sub>3 *) $n-1) ;;

    copy_mat ($a\<^sub>C, $i\<^sub>C, $j\<^sub>C', (*M\<^sub>2*) $a\<^sub>A, $i\<^sub>A', $j\<^sub>A , (*A\<^sub>2\<^sub>1*) $N, $N) ;;
    add_mat  ($a\<^sub>C, $i\<^sub>C, $j\<^sub>C', (*M\<^sub>2*) $a\<^sub>A, $i\<^sub>A', $j\<^sub>A', (*A\<^sub>2\<^sub>2*) $N, $N) ;;
    strassen ($a\<^sub>C, $i\<^sub>C, $j\<^sub>C', (*M\<^sub>2*) $a\<^sub>B, $i\<^sub>B , $j\<^sub>B , (*B\<^sub>1\<^sub>1*)
              $a\<^sub>C, $i\<^sub>C', $j\<^sub>C, (*M\<^sub>3*) $a\<^sub>C, $i\<^sub>C', $j\<^sub>C', (*M\<^sub>4*) $n-1) ;;

    copy_mat ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B , $j\<^sub>B', (*B\<^sub>1\<^sub>2*) $N, $N) ;;
    sub_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B', $j\<^sub>B', (*B\<^sub>2\<^sub>2*) $N, $N) ;;
    copy_mat ($a\<^sub>C, $i\<^sub>C', $j\<^sub>C , (*M\<^sub>3*) $a\<^sub>A, $i\<^sub>A , $j\<^sub>A , (*A\<^sub>1\<^sub>1*) $N, $N) ;;
    strassen ($a\<^sub>C, $i\<^sub>C', $j\<^sub>C , (*M\<^sub>3*) $a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*)
              $a\<^sub>C, $i\<^sub>C', $j\<^sub>C', (*M\<^sub>4*) $a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $n-1) ;;


    copy_mat ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B', $j\<^sub>B , (*B\<^sub>2\<^sub>1*) $N, $N) ;;
    sub_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B , $j\<^sub>B , (*B\<^sub>1\<^sub>1*) $N, $N) ;;
    copy_mat ($a\<^sub>C, $i\<^sub>C', $j\<^sub>C', (*M\<^sub>4*) $a\<^sub>A, $i\<^sub>A', $j\<^sub>A', (*A\<^sub>2\<^sub>2*) $N, $N) ;;
    strassen ($a\<^sub>C, $i\<^sub>C', $j\<^sub>C', (*M\<^sub>4*) $a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*)
              $a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $n-1) ;;

    copy_mat ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $a\<^sub>A, $i\<^sub>A , $j\<^sub>A , (*A\<^sub>1\<^sub>1*) $N, $N) ;;
    add_mat  ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $a\<^sub>A, $i\<^sub>A , $j\<^sub>A', (*A\<^sub>1\<^sub>2*) $N, $N) ;;
    strassen ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $a\<^sub>B, $i\<^sub>B', $j\<^sub>B', (*B\<^sub>2\<^sub>2*)
              $a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $n-1) ;;

    copy_mat ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $a\<^sub>A, $i\<^sub>A', $j\<^sub>A , (*A\<^sub>2\<^sub>1*) $N, $N) ;;
    sub_mat  ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $a\<^sub>A, $i\<^sub>A , $j\<^sub>A , (*A\<^sub>1\<^sub>1*) $N, $N) ;;
    copy_mat ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B , $j\<^sub>B , (*B\<^sub>1\<^sub>1*) $N, $N) ;;
    add_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B , $j\<^sub>B', (*B\<^sub>1\<^sub>2*) $N, $N) ;;
    strassen ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*)
              $a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $a\<^sub>A, $i\<^sub>A , $j\<^sub>A , (*A\<^sub>1\<^sub>1*) $n-1) ;;


    copy_mat ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $a\<^sub>A, $i\<^sub>A , $j\<^sub>A', (*A\<^sub>1\<^sub>2*) $N, $N) ;;
    sub_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $a\<^sub>A, $i\<^sub>A', $j\<^sub>A', (*A\<^sub>2\<^sub>2*) $N, $N) ;;
    copy_mat ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B', $j\<^sub>B , (*B\<^sub>2\<^sub>1*) $N, $N) ;;
    add_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*) $a\<^sub>B, $i\<^sub>B', $j\<^sub>B', (*B\<^sub>2\<^sub>2*) $N, $N) ;;
    strassen ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $a\<^sub>D, $i\<^sub>D', $j\<^sub>D', (*M\<^sub>t*)
              $a\<^sub>A, $i\<^sub>A , $j\<^sub>A , (*A\<^sub>1\<^sub>1*)$a\<^sub>A, $i\<^sub>A , $j\<^sub>A', (*A\<^sub>1\<^sub>2*) $n-1) ;;

    add_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $a\<^sub>C, $i\<^sub>C , $j\<^sub>C , (*M\<^sub>1*) $N, $N) ;;
    add_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $a\<^sub>C, $i\<^sub>C', $j\<^sub>C', (*M\<^sub>4*) $N, $N) ;;
    sub_mat  ($a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $N, $N) ;;
    copy_mat ($a\<^sub>A, $i\<^sub>A , $j\<^sub>A , (*A\<^sub>1\<^sub>1*)$a\<^sub>D, $i\<^sub>D', $j\<^sub>D , (*M\<^sub>7*) $N, $N) ;;

    add_mat  ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $a\<^sub>C, $i\<^sub>C', $j\<^sub>C , (*M\<^sub>3*) $N, $N) ;;
    copy_mat ($a\<^sub>A, $i\<^sub>A , $j\<^sub>A', (*A\<^sub>1\<^sub>2*)$a\<^sub>D, $i\<^sub>D , $j\<^sub>D , (*M\<^sub>5*) $N, $N) ;;

    add_mat  ($a\<^sub>C, $i\<^sub>C', $j\<^sub>C', (*M\<^sub>4*) $a\<^sub>C, $i\<^sub>C, $j\<^sub>C', (*M\<^sub>2*) $N, $N) ;;
    copy_mat ($a\<^sub>A, $i\<^sub>A', $j\<^sub>A , (*A\<^sub>2\<^sub>1*)$a\<^sub>C, $i\<^sub>C', $j\<^sub>C', (*M\<^sub>4*) $N, $N) ;;

    add_mat  ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $a\<^sub>C, $i\<^sub>C , $j\<^sub>C, (*M\<^sub>1*) $N, $N) ;;
    sub_mat  ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $a\<^sub>C, $i\<^sub>C , $j\<^sub>C',(*M\<^sub>2*) $N, $N) ;;
    add_mat  ($a\<^sub>D, $i\<^sub>D , $j\<^sub>D', (*M\<^sub>6*) $a\<^sub>C, $i\<^sub>C', $j\<^sub>C, (*M\<^sub>3*) $N, $N) ;;
    copy_mat ($a\<^sub>A, $i\<^sub>A', $j\<^sub>A', (*A\<^sub>2\<^sub>2*)$a\<^sub>D, $i\<^sub>D , $j\<^sub>D',(*M\<^sub>6*) $N, $N)

    (*Below, the proof is stolen from $AFP23-10-16/Jordan_Normal_Form/Strassen_Algorithm.thy: 175-182, 227-239, lemma strassen_mat_mult*)

    holds_fact split_A_B: \<open>B = four_block_mat B\<^sub>1\<^sub>1 B\<^sub>1\<^sub>2 B\<^sub>2\<^sub>1 B\<^sub>2\<^sub>2\<close>                      (*for proof, Tac-s*)
                          \<open>A = four_block_mat A\<^sub>1\<^sub>1 A\<^sub>1\<^sub>2 A\<^sub>2\<^sub>1 A\<^sub>2\<^sub>2\<close> ;;                   (*for proof, Tac-s*)

    note carriers = \<open>A\<^sub>1\<^sub>1 \<in> carrier_mat _ _\<close> \<open>A\<^sub>1\<^sub>2 \<in> carrier_mat _ _\<close>                (*for proof, each line is counted as one Tac-m*)
                    \<open>A\<^sub>2\<^sub>1 \<in> carrier_mat _ _\<close> \<open>A\<^sub>2\<^sub>2 \<in> carrier_mat _ _\<close>
                    \<open>B\<^sub>1\<^sub>1 \<in> carrier_mat _ _\<close> \<open>B\<^sub>1\<^sub>2 \<in> carrier_mat _ _\<close>
                    \<open>B\<^sub>2\<^sub>1 \<in> carrier_mat _ _\<close> \<open>B\<^sub>2\<^sub>2 \<in> carrier_mat _ _\<close> ;;

    apply_rule merge_4mat[where a=a\<^sub>A and i=i\<^sub>A and s=\<open>?N\<close> and j=j\<^sub>A and t=\<open>?N\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
      is \<open>A * B\<close> certified by (                                                    (*is \<open>A * B\<close> is an annotation, A*)
         simp add: carriers split_A_B mult_four_block_mat[OF carriers],
         rule cong_four_block_mat,
         insert carriers,
         auto simp add:  mult_carrier_mat[where n=\<open>?N\<close>]
                         add_mult_distrib_mat[where nr=\<open>?N\<close> and n=\<open>?N\<close> and nc=\<open>?N\<close>]
                         minus_mult_distrib_mat[where nr=\<open>?N\<close> and n=\<open>?N\<close> and nc=\<open>?N\<close>]
                         mult_add_distrib_mat[where nr=\<open>?N\<close> and n=\<open>?N\<close> and nc=\<open>?N\<close>]
                         mult_minus_distrib_mat[where nr=\<open>?N\<close> and n=\<open>?N\<close> and nc=\<open>?N\<close>]
                         add_carrier_mat[where nr=\<open>?N\<close> and nc=\<open>?N\<close>]
                         uminus_carrier_iff_mat[where nr=\<open>?N\<close> and nc=\<open>?N\<close>]
                         assoc_add_mat[where nr=\<open>?N\<close> and nc=\<open>?N\<close>]
                         comm_add_mat[where nr=\<open>?N\<close> and nc=\<open>?N\<close>]
                         minus_add_minus_mat[where nr=\<open>?N\<close> and nc=\<open>?N\<close>])
    (*end of stolen proof*) ;;


    apply_rule merge_4mat[where a=a\<^sub>B and i=i\<^sub>B and s=\<open>?N\<close> and j=j\<^sub>B and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
            is B ;;                                                                (*is \<open>B\<close> is an annotation, A*)

    apply_rule merge_4mat[where a=a\<^sub>C and i=i\<^sub>C and s=\<open>?N\<close> and j=j\<^sub>C and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
    apply_rule merge_4mat[where a=a\<^sub>D and i=i\<^sub>D and s=\<open>?N\<close> and j=j\<^sub>D and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
    
  \<medium_right_bracket> ;;
\<medium_right_bracket> .

end

proc strassen_mul:
  input  \<open>A \<Ztypecolon> MatSlice a\<^sub>x 0 0 (2^n) (2^n)\<heavy_comma>
          B \<Ztypecolon> MatSlice a\<^sub>y 0 0 (2^n) (2^n)\<heavy_comma>
          a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> (2^n) (2^n)\<heavy_comma>
          a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<m>\<a>\<t> (2^n) (2^n)\<close>
  premises \<open>n < addrspace_bits\<close>
  output \<open>A * B \<Ztypecolon> MatSlice a\<^sub>x 0 0 (2^n) (2^n)\<heavy_comma>
          B \<Ztypecolon> MatSlice a\<^sub>y 0 0 (2^n) (2^n) \<close>
\<medium_left_bracket>
  \<open>literal n \<Ztypecolon> \<nat>(size_t)\<close> \<rightarrow> val n ;;
  1 << $n \<rightarrow> val N ;;
  new_mat \<open>2^n\<close> \<open>2^n\<close> \<rightarrow> val C ;;
  new_mat \<open>2^n\<close> \<open>2^n\<close> \<rightarrow> val D ;;
  strassen ($a\<^sub>x, 0, 0, $a\<^sub>y, 0, 0, $C, 0, 0, $D, 0, 0, $n) ;;
  del_mat ($C) ;;
  del_mat ($D)
\<medium_right_bracket> .


end