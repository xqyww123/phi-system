theory Matrix_Oprs
  imports Phi_Semantics.PhiSem_C
          Jordan_Normal_Form.Matrix
          PhiStd.PhiStd_Slice
          Phi_Semantics.PhiSem_Mem_C_MI
begin

abbreviation \<open>\<m>\<a>\<t> M N \<equiv> \<a>\<r>\<r>\<a>\<y>[M] \<a>\<r>\<r>\<a>\<y>[N] \<i>\<n>\<t>\<close>
 
\<phi>type_def MatSlice
  where \<open>x \<Ztypecolon> MatSlice addr i j m n \<equiv> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,m] (\<s>\<l>\<i>\<c>\<e>[j,n] \<int>\<^sup>r(\<i>\<n>\<t>))
                                     \<s>\<u>\<b>\<j> l. l = mat_to_list x \<and> x \<in> carrier_mat m n\<close>
  parameter_equality (id,id,id,id,id)
  deriving \<open>Abstract_Domain (MatSlice addr i j m n) (\<lambda>x. addr \<noteq> 0 \<and> x \<in> carrier_mat m n)\<close>
       and \<open>Object_Equiv (MatSlice addr i j m n) (=)\<close>
       and Basic



lemmas [\<phi>sledgehammer_simps] = mat_to_list_def list_eq_iff_nth_eq list_all2_conv_all_nth zero_mat_def

proc zero_mat:
  input    \<open>a \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M N]\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            m \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            x \<Ztypecolon> MatSlice a i j m n\<close>
  premises \<open>i + m \<le> M \<and> j + n \<le> N \<and> M < 2 ^ addrspace_bits \<and> N < 2 ^ addrspace_bits\<close>
  output   \<open>0\<^sub>m m n \<Ztypecolon> MatSlice a i j m n\<close>
  unfolding MatSlice.unfold
\<medium_left_bracket>
  map_slice(m) \<medium_left_bracket> for k \<rightarrow> val k \<semicolon>
    map_slice(n) \<medium_left_bracket> for h \<rightarrow> val h  \<semicolon>
      a[i+k, j+h] := \<open>0 \<Ztypecolon> \<int>\<^sup>r(\<i>\<n>\<t>)\<close>
    \<medium_right_bracket>
  \<medium_right_bracket> \<semicolon>

\<medium_right_bracket> .


proc new_mat:
  requires \<open>\<p>\<a>\<r>\<a>\<m> M\<close>
  requires \<open>\<p>\<a>\<r>\<a>\<m> N\<close>
  input    \<open>Void\<close>
  output   \<open>a \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M N]\<heavy_comma>
            0\<^sub>m M N \<Ztypecolon> MatSlice a 0 0 M N
            \<s>\<u>\<b>\<j> a. address_to_base a\<close>
  unfolding MatSlice.unfold
\<medium_left_bracket>
  calloc1 \<open>\<bbbA>\<r>\<r>\<a>\<y>[M] \<bbbA>\<r>\<r>\<a>\<y>[N] \<int>\<^sup>r(\<i>\<n>\<t>)\<close>
\<medium_right_bracket> .

proc del_mat:
  input    \<open>a \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M N]\<heavy_comma> x \<Ztypecolon> MatSlice a i j m n\<close>
  premises \<open>m = M \<and> n = N \<and> i = 0 \<and> j = 0 \<and> address_to_base a\<close>
  output   \<open>Void\<close>
  unfolding MatSlice.unfold
\<medium_left_bracket>
  mfree (a)
\<medium_right_bracket> .


proc copy_mat:
  input    \<open>a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M\<^sub>x N\<^sub>x]\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M\<^sub>y N\<^sub>y]\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            m \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
            y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>

  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y \<and>
            M\<^sub>x < 2 ^ addrspace_bits \<and> N\<^sub>x < 2 ^ addrspace_bits \<and>
            M\<^sub>y < 2 ^ addrspace_bits \<and> N\<^sub>y < 2 ^ addrspace_bits\<close>

  output   \<open>y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
  unfolding MatSlice.unfold
\<medium_left_bracket>
  map_2slice (m) \<medium_left_bracket> for k \<rightarrow> val k \<semicolon>
    map_2slice (n) \<medium_left_bracket> for h \<rightarrow> val h \<semicolon>
      a\<^sub>x[i\<^sub>x+k, j\<^sub>x+h] := a\<^sub>y[i\<^sub>y+k, j\<^sub>y+h]
    \<medium_right_bracket> \<semicolon>
  \<medium_right_bracket>
\<medium_right_bracket> .


proc add_mat:
  input    \<open>a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M\<^sub>x N\<^sub>x]\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M\<^sub>y N\<^sub>y]\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            m \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
            y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>

  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y \<and>
            M\<^sub>x < 2 ^ addrspace_bits \<and> N\<^sub>x < 2 ^ addrspace_bits \<and>
            M\<^sub>y < 2 ^ addrspace_bits \<and> N\<^sub>y < 2 ^ addrspace_bits\<close>

  output   \<open>x + y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
  unfolding MatSlice.unfold
\<medium_left_bracket>
  map_2slice (m) \<medium_left_bracket> for k \<rightarrow> val k
    map_2slice (n) \<medium_left_bracket> for h \<rightarrow> val h
        a\<^sub>x[i\<^sub>x+k, j\<^sub>x+h] := a\<^sub>x[i\<^sub>x+k, j\<^sub>x+h] + a\<^sub>y[i\<^sub>y+k, j\<^sub>y+h]
    \<medium_right_bracket> \<semicolon>
  \<medium_right_bracket>
\<medium_right_bracket> .


proc sub_mat:
  input    \<open>a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M\<^sub>x N\<^sub>x]\<heavy_comma> i\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> M\<^sub>y N\<^sub>y]\<heavy_comma> i\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            m \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> n \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma>
            y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>

  premises \<open>i\<^sub>x + m \<le> M\<^sub>x \<and> i\<^sub>y + m \<le> M\<^sub>y \<and> j\<^sub>x + n \<le> N\<^sub>x \<and> j\<^sub>y + n \<le> N\<^sub>y \<and>
            M\<^sub>x < 2 ^ addrspace_bits \<and> N\<^sub>x < 2 ^ addrspace_bits \<and>
            M\<^sub>y < 2 ^ addrspace_bits \<and> N\<^sub>y < 2 ^ addrspace_bits \<close>

  output   \<open>x - y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x m n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>y i\<^sub>y j\<^sub>y m n\<close>
  unfolding MatSlice.unfold
\<medium_left_bracket>
  map_2slice (m) \<medium_left_bracket> for k \<rightarrow> val k \<semicolon>
    map_2slice (n) \<medium_left_bracket> for h \<rightarrow> val h \<semicolon>
      a\<^sub>x[i\<^sub>x+k, j\<^sub>x+h] := a\<^sub>x[i\<^sub>x+k, j\<^sub>x+h] - a\<^sub>y[i\<^sub>y+k, j\<^sub>y+h]
    \<medium_right_bracket> \<semicolon>
  \<medium_right_bracket> \<semicolon>
\<medium_right_bracket> .


context
  notes [\<phi>sledgehammer_simps] = Let_def image_iff split_block_def four_block_mat_def mat_to_list_def
                                list_eq_iff_nth_eq nth_append Bex_def in_set_conv_nth image_iff
begin

lemma split_4mat:
  \<open> \<p>\<a>\<r>\<a>\<m> (s, t)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> m \<and> t \<le> n
\<Longrightarrow> x \<Ztypecolon> MatSlice a i j m n \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x\<^sub>1\<^sub>1 \<Ztypecolon> MatSlice a i j s t\<heavy_comma> x\<^sub>1\<^sub>2 \<Ztypecolon> MatSlice a i (j+t) s (n-t)\<heavy_comma>
                                    x\<^sub>2\<^sub>1 \<Ztypecolon> MatSlice a (i+s) j (m-s) t\<heavy_comma> x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a (i+s) (j+t) (m-s) (n-t)
                                    \<s>\<u>\<b>\<j> x\<^sub>1\<^sub>1 x\<^sub>1\<^sub>2 x\<^sub>2\<^sub>1 x\<^sub>2\<^sub>2. (x\<^sub>1\<^sub>1, x\<^sub>1\<^sub>2, x\<^sub>2\<^sub>1, x\<^sub>2\<^sub>2) = split_block x s t\<close>
  unfolding MatSlice.unfold \<comment> \<open>open abstraction in both sides\<close>
  \<medium_left_bracket> \<medium_right_bracket> certified by (auto simp: Bex_def in_set_conv_nth image_iff; auto_sledgehammer) .

lemma merge_4mat:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> m \<and> t \<le> n
\<Longrightarrow> x\<^sub>1\<^sub>1 \<Ztypecolon> MatSlice a i j s t\<heavy_comma> x\<^sub>1\<^sub>2 \<Ztypecolon> MatSlice a i (j+t) s (n-t)\<heavy_comma>
    x\<^sub>2\<^sub>1 \<Ztypecolon> MatSlice a (i+s) j (m-s) t\<heavy_comma> x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a (i+s) (j+t) (m-s) (n-t)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> four_block_mat x\<^sub>1\<^sub>1 x\<^sub>1\<^sub>2 x\<^sub>2\<^sub>1 x\<^sub>2\<^sub>2 \<Ztypecolon> MatSlice a i j m n \<close>
  unfolding MatSlice.unfold \<comment> \<open>open abstraction in both sides\<close>
  \<medium_left_bracket> \<medium_right_bracket> certified by (auto simp: \<phi>sledgehammer_simps \<phi>[unfolded carrier_mat_def, simplified]) .

end


declare [[linarith_split_limit = 20]]

context
  fixes N :: nat
begin
 
proc strassen:
  input    \<open>a\<^sub>A \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> N N]\<heavy_comma> i\<^sub>A \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>A \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            a\<^sub>B \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> N N]\<heavy_comma> i\<^sub>B \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>B \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            a\<^sub>C \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> N N]\<heavy_comma> i\<^sub>C \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>C \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            a\<^sub>D \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> N N]\<heavy_comma> i\<^sub>D \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> j\<^sub>D \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            n \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma>
            A \<Ztypecolon> MatSlice a\<^sub>A i\<^sub>A j\<^sub>A (2^n) (2^n)\<heavy_comma>
            B \<Ztypecolon> MatSlice a\<^sub>B i\<^sub>B j\<^sub>B (2^n) (2^n)\<heavy_comma>
            buf\<^sub>1 \<Ztypecolon> MatSlice a\<^sub>C i\<^sub>C j\<^sub>C (2^n) (2^n)\<heavy_comma> \<comment> \<open>buffers used to store intermediate values\<close>
            buf\<^sub>2 \<Ztypecolon> MatSlice a\<^sub>D i\<^sub>D j\<^sub>D (2^n) (2^n)\<close>

  premises \<open>i\<^sub>A + 2^n \<le> N \<and> j\<^sub>A + 2^n \<le> N \<and>
            i\<^sub>B + 2^n \<le> N \<and> j\<^sub>B + 2^n \<le> N \<and>
            i\<^sub>C + 2^n \<le> N \<and> j\<^sub>C + 2^n \<le> N \<and>
            i\<^sub>D + 2^n \<le> N \<and> j\<^sub>D + 2^n \<le> N \<and>
            M < 2 ^ addrspace_bits \<and> N < 2 ^ addrspace_bits\<close>

  output   \<open>A * B \<Ztypecolon> MatSlice a\<^sub>A i\<^sub>A j\<^sub>A (2^n) (2^n)\<heavy_comma>
            B \<Ztypecolon> MatSlice a\<^sub>B i\<^sub>B j\<^sub>B (2^n) (2^n)\<heavy_comma>
            buf\<^sub>1 \<Ztypecolon> MatSlice a\<^sub>C i\<^sub>C j\<^sub>C (2^n) (2^n)\<heavy_comma> \<comment> \<open>buffers used to store intermediate values\<close>
            buf\<^sub>2 \<Ztypecolon> MatSlice a\<^sub>D i\<^sub>D j\<^sub>D (2^n) (2^n)
            \<s>\<u>\<b>\<j> buf\<^sub>1 buf\<^sub>2. \<top>\<close>
  is [recursive]
\<medium_left_bracket>
  if (n = 0)
  \<medium_left_bracket>
    \<open>MatSlice a\<^sub>A _ _ _ _\<close> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>
    \<open>MatSlice a\<^sub>B _ _ _ _\<close> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>  \<semicolon>

    a\<^sub>A[i\<^sub>A, j\<^sub>A] := a\<^sub>A[i\<^sub>A, j\<^sub>A] * a\<^sub>B[i\<^sub>B, j\<^sub>B] \<semicolon>
      
    holds_fact [\<phi>sledgehammer_simps]: \<open>dim_col B = 1 \<and> dim_row B = 1 \<and> dim_col A = 1 \<and> dim_row A = 1\<close> (*for proof obligation*)
    note scalar_prod_def [\<phi>sledgehammer_simps] \<semicolon>                                       (*for proof obligation*)

    \<m>\<a>\<k>\<e>\<s> \<open>A * B \<Ztypecolon> MatSlice a\<^sub>A i\<^sub>A j\<^sub>A (2^n) (2^n)\<close> \<semicolon>
    \<m>\<a>\<k>\<e>\<s> \<open>B \<Ztypecolon> MatSlice a\<^sub>B i\<^sub>B j\<^sub>B (2^n) (2^n)\<close>
  \<medium_right_bracket>
  \<medium_left_bracket>
    holds_fact t0: \<open>(2::nat) ^ n = 2 ^ (n - 1) + 2 ^ (n - 1)\<close>                          (*for proof obligation*)
    holds_fact t1[simp]: \<open>(2::nat) ^ n - 2 ^ (n - 1) = 2 ^ (n - 1)\<close> \<semicolon>                  (*an annotation for reasoning*)
        \<comment> \<open>Even when ML-aided ATP \<open>Sledgehammer\<close> is so powerful now, it cannot solve some simple
            high-school problems without the \<open>t0\<close> hint ...\<close>

    \<open>MatSlice a\<^sub>A _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>A\<^sub>1\<^sub>1, A\<^sub>1\<^sub>2, A\<^sub>2\<^sub>1, A\<^sub>2\<^sub>2 \<semicolon>
    \<open>MatSlice a\<^sub>B _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>B\<^sub>1\<^sub>1, B\<^sub>1\<^sub>2, B\<^sub>2\<^sub>1, B\<^sub>2\<^sub>2 \<semicolon>
    \<open>MatSlice a\<^sub>C _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>M\<^sub>1, M\<^sub>2, M\<^sub>3, M\<^sub>4 \<semicolon>
    \<open>MatSlice a\<^sub>D _ _ _ _\<close> split_4mat \<open>(2^(n-1), 2^(n-1))\<close> \<exists>M\<^sub>5, M\<^sub>6, M\<^sub>7, M\<^sub>t \<semicolon>

    holds_fact t2: \<open>n < addrspace_bits\<close> \<semicolon>                                              (*for proof obligation*)

    1 << (n-1) \<rightarrow> val N \<semicolon>
    i\<^sub>A + N \<rightarrow> val i\<^sub>A' \<semicolon>
    j\<^sub>A + N \<rightarrow> val j\<^sub>A' \<semicolon>
    i\<^sub>B + N \<rightarrow> val i\<^sub>B' \<semicolon>
    j\<^sub>B + N \<rightarrow> val j\<^sub>B' \<semicolon>
    i\<^sub>C + N \<rightarrow> val i\<^sub>C' \<semicolon>
    j\<^sub>C + N \<rightarrow> val j\<^sub>C' \<semicolon>
    i\<^sub>D + N \<rightarrow> val i\<^sub>D' \<semicolon>
    j\<^sub>D + N \<rightarrow> val j\<^sub>D' \<semicolon>

    copy_mat (a\<^sub>C, i\<^sub>C , j\<^sub>C,  (*M\<^sub>1*) a\<^sub>A, i\<^sub>A , j\<^sub>A , (*A\<^sub>1\<^sub>1*) N, N) \<semicolon>
    add_mat  (a\<^sub>C, i\<^sub>C , j\<^sub>C,  (*M\<^sub>1*) a\<^sub>A, i\<^sub>A', j\<^sub>A', (*A\<^sub>2\<^sub>2*) N, N) \<semicolon>
    copy_mat (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B , j\<^sub>B , (*B\<^sub>1\<^sub>1*) N, N) \<semicolon>
    add_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B', j\<^sub>B', (*B\<^sub>2\<^sub>2*) N, N) \<semicolon>
    strassen (a\<^sub>C, i\<^sub>C , j\<^sub>C , (*M\<^sub>1*) a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t *)
              a\<^sub>C, i\<^sub>C , j\<^sub>C', (*M\<^sub>2*) a\<^sub>C, i\<^sub>C', j\<^sub>C , (*M\<^sub>3 *) n-1) \<semicolon>

    copy_mat (a\<^sub>C, i\<^sub>C, j\<^sub>C', (*M\<^sub>2*) a\<^sub>A, i\<^sub>A', j\<^sub>A , (*A\<^sub>2\<^sub>1*) N, N) \<semicolon>
    add_mat  (a\<^sub>C, i\<^sub>C, j\<^sub>C', (*M\<^sub>2*) a\<^sub>A, i\<^sub>A', j\<^sub>A', (*A\<^sub>2\<^sub>2*) N, N) \<semicolon>
    strassen (a\<^sub>C, i\<^sub>C, j\<^sub>C', (*M\<^sub>2*) a\<^sub>B, i\<^sub>B , j\<^sub>B , (*B\<^sub>1\<^sub>1*)
              a\<^sub>C, i\<^sub>C', j\<^sub>C, (*M\<^sub>3*) a\<^sub>C, i\<^sub>C', j\<^sub>C', (*M\<^sub>4*) n-1) \<semicolon>

    copy_mat (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B , j\<^sub>B', (*B\<^sub>1\<^sub>2*) N, N) \<semicolon>
    sub_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B', j\<^sub>B', (*B\<^sub>2\<^sub>2*) N, N) \<semicolon>
    copy_mat (a\<^sub>C, i\<^sub>C', j\<^sub>C , (*M\<^sub>3*) a\<^sub>A, i\<^sub>A , j\<^sub>A , (*A\<^sub>1\<^sub>1*) N, N) \<semicolon>
    strassen (a\<^sub>C, i\<^sub>C', j\<^sub>C , (*M\<^sub>3*) a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*)
              a\<^sub>C, i\<^sub>C', j\<^sub>C', (*M\<^sub>4*) a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) n-1) \<semicolon>


    copy_mat (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B', j\<^sub>B , (*B\<^sub>2\<^sub>1*) N, N) \<semicolon>
    sub_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B , j\<^sub>B , (*B\<^sub>1\<^sub>1*) N, N) \<semicolon>
    copy_mat (a\<^sub>C, i\<^sub>C', j\<^sub>C', (*M\<^sub>4*) a\<^sub>A, i\<^sub>A', j\<^sub>A', (*A\<^sub>2\<^sub>2*) N, N) \<semicolon>
    strassen (a\<^sub>C, i\<^sub>C', j\<^sub>C', (*M\<^sub>4*) a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*)
              a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) n-1) \<semicolon>

    copy_mat (a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) a\<^sub>A, i\<^sub>A , j\<^sub>A , (*A\<^sub>1\<^sub>1*) N, N) \<semicolon>
    add_mat  (a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) a\<^sub>A, i\<^sub>A , j\<^sub>A', (*A\<^sub>1\<^sub>2*) N, N) \<semicolon>
    strassen (a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) a\<^sub>B, i\<^sub>B', j\<^sub>B', (*B\<^sub>2\<^sub>2*)
              a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) n-1) \<semicolon>

    copy_mat (a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) a\<^sub>A, i\<^sub>A', j\<^sub>A , (*A\<^sub>2\<^sub>1*) N, N) \<semicolon>
    sub_mat  (a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) a\<^sub>A, i\<^sub>A , j\<^sub>A , (*A\<^sub>1\<^sub>1*) N, N) \<semicolon>
    copy_mat (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B , j\<^sub>B , (*B\<^sub>1\<^sub>1*) N, N) \<semicolon>
    add_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B , j\<^sub>B', (*B\<^sub>1\<^sub>2*) N, N) \<semicolon>
    strassen (a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*)
              a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) a\<^sub>A, i\<^sub>A , j\<^sub>A , (*A\<^sub>1\<^sub>1*) n-1) \<semicolon>


    copy_mat (a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) a\<^sub>A, i\<^sub>A , j\<^sub>A', (*A\<^sub>1\<^sub>2*) N, N) \<semicolon>
    sub_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) a\<^sub>A, i\<^sub>A', j\<^sub>A', (*A\<^sub>2\<^sub>2*) N, N) \<semicolon>
    copy_mat (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B', j\<^sub>B , (*B\<^sub>2\<^sub>1*) N, N) \<semicolon>
    add_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*) a\<^sub>B, i\<^sub>B', j\<^sub>B', (*B\<^sub>2\<^sub>2*) N, N) \<semicolon>
    strassen (a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) a\<^sub>D, i\<^sub>D', j\<^sub>D', (*M\<^sub>t*)
              a\<^sub>A, i\<^sub>A , j\<^sub>A , (*A\<^sub>1\<^sub>1*)a\<^sub>A, i\<^sub>A , j\<^sub>A', (*A\<^sub>1\<^sub>2*) n-1) \<semicolon>

    add_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) a\<^sub>C, i\<^sub>C , j\<^sub>C , (*M\<^sub>1*) N, N) \<semicolon>
    add_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) a\<^sub>C, i\<^sub>C', j\<^sub>C', (*M\<^sub>4*) N, N) \<semicolon>
    sub_mat  (a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) N, N) \<semicolon>
    copy_mat (a\<^sub>A, i\<^sub>A , j\<^sub>A , (*A\<^sub>1\<^sub>1*)a\<^sub>D, i\<^sub>D', j\<^sub>D , (*M\<^sub>7*) N, N) \<semicolon>

    add_mat  (a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) a\<^sub>C, i\<^sub>C', j\<^sub>C , (*M\<^sub>3*) N, N) \<semicolon>
    copy_mat (a\<^sub>A, i\<^sub>A , j\<^sub>A', (*A\<^sub>1\<^sub>2*)a\<^sub>D, i\<^sub>D , j\<^sub>D , (*M\<^sub>5*) N, N) \<semicolon>

    add_mat  (a\<^sub>C, i\<^sub>C', j\<^sub>C', (*M\<^sub>4*) a\<^sub>C, i\<^sub>C, j\<^sub>C', (*M\<^sub>2*) N, N) \<semicolon>
    copy_mat (a\<^sub>A, i\<^sub>A', j\<^sub>A , (*A\<^sub>2\<^sub>1*)a\<^sub>C, i\<^sub>C', j\<^sub>C', (*M\<^sub>4*) N, N) \<semicolon>

    add_mat  (a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) a\<^sub>C, i\<^sub>C , j\<^sub>C, (*M\<^sub>1*) N, N) \<semicolon>
    sub_mat  (a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) a\<^sub>C, i\<^sub>C , j\<^sub>C',(*M\<^sub>2*) N, N) \<semicolon>
    add_mat  (a\<^sub>D, i\<^sub>D , j\<^sub>D', (*M\<^sub>6*) a\<^sub>C, i\<^sub>C', j\<^sub>C, (*M\<^sub>3*) N, N) \<semicolon>
    copy_mat (a\<^sub>A, i\<^sub>A', j\<^sub>A', (*A\<^sub>2\<^sub>2*)a\<^sub>D, i\<^sub>D , j\<^sub>D',(*M\<^sub>6*) N, N)

    (*Below, the proof is stolen from AFP23-10-16/Jordan_Normal_Form/Strassen_Algorithm.thy: 175-182, 227-239, lemma strassen_mat_mult*)

    holds_fact split_A_B: \<open>B = four_block_mat B\<^sub>1\<^sub>1 B\<^sub>1\<^sub>2 B\<^sub>2\<^sub>1 B\<^sub>2\<^sub>2\<close>                      (*for proof obligation*)
                          \<open>A = four_block_mat A\<^sub>1\<^sub>1 A\<^sub>1\<^sub>2 A\<^sub>2\<^sub>1 A\<^sub>2\<^sub>2\<close> \<semicolon>                    (*for proof obligation*)

    note carriers = \<open>A\<^sub>1\<^sub>1 \<in> carrier_mat _ _\<close> \<open>A\<^sub>1\<^sub>2 \<in> carrier_mat _ _\<close>                (*for proof obligation*)
                    \<open>A\<^sub>2\<^sub>1 \<in> carrier_mat _ _\<close> \<open>A\<^sub>2\<^sub>2 \<in> carrier_mat _ _\<close>
                    \<open>B\<^sub>1\<^sub>1 \<in> carrier_mat _ _\<close> \<open>B\<^sub>1\<^sub>2 \<in> carrier_mat _ _\<close>
                    \<open>B\<^sub>2\<^sub>1 \<in> carrier_mat _ _\<close> \<open>B\<^sub>2\<^sub>2 \<in> carrier_mat _ _\<close> \<semicolon>

    apply_rule merge_4mat[where a=a\<^sub>A and i=i\<^sub>A and s=\<open>?N\<close> and j=j\<^sub>A and t=\<open>?N\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
      is \<open>A * B\<close> certified by (                                                    (*\<open>A * B\<close> is an annotation*)
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
    (*end of stolen proof*) \<semicolon>


    apply_rule merge_4mat[where a=a\<^sub>B and i=i\<^sub>B and s=\<open>?N\<close> and j=j\<^sub>B and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
            is B \<semicolon>                                                                (*\<open>B\<close> is an annotation*)

    apply_rule merge_4mat[where a=a\<^sub>C and i=i\<^sub>C and s=\<open>?N\<close> and j=j\<^sub>C and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
    apply_rule merge_4mat[where a=a\<^sub>D and i=i\<^sub>D and s=\<open>?N\<close> and j=j\<^sub>D and t=\<open>2^(n-1)\<close> and m=\<open>2^n\<close> and n=\<open>2^n\<close>, simplified t1]
    
  \<medium_right_bracket> \<semicolon>
\<medium_right_bracket> .

end

proc strassen_mul:
  input    \<open>a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> (2^n) (2^n)]\<heavy_comma>
            a\<^sub>y \<Ztypecolon> \<v>\<a>\<l> Ptr[\<m>\<a>\<t> (2^n) (2^n)]\<heavy_comma>
            A \<Ztypecolon> MatSlice a\<^sub>x 0 0 (2^n) (2^n)\<heavy_comma>
            B \<Ztypecolon> MatSlice a\<^sub>y 0 0 (2^n) (2^n)\<close>
  premises \<open>n < addrspace_bits\<close>
  output   \<open>A * B \<Ztypecolon> MatSlice a\<^sub>x 0 0 (2^n) (2^n)\<heavy_comma>
            B \<Ztypecolon> MatSlice a\<^sub>y 0 0 (2^n) (2^n) \<close>
\<medium_left_bracket>
  \<open>literal n \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close> \<rightarrow> val n \<semicolon>
  1 << n \<rightarrow> val N \<semicolon>
  new_mat \<open>2^n\<close> \<open>2^n\<close> \<rightarrow> val C \<semicolon>
  new_mat \<open>2^n\<close> \<open>2^n\<close> \<rightarrow> val D \<semicolon>
  strassen (a\<^sub>x, 0, 0, a\<^sub>y, 0, 0, C, 0, 0, D, 0, 0, n) \<semicolon>
  del_mat (C) \<semicolon>
  del_mat (D)
\<medium_right_bracket> .


text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm zero_mat_\<phi>app
thm new_mat_\<phi>app
thm del_mat_\<phi>app
thm copy_mat_\<phi>app
thm add_mat_\<phi>app
thm sub_mat_\<phi>app
thm strassen_\<phi>app
thm strassen_mul_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm zero_mat_def
thm new_mat_def
thm del_mat_def
thm copy_mat_def
thm add_mat_def
thm sub_mat_def
thm strassen_def
thm strassen_mul_def

end