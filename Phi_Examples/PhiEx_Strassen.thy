theory PhiEx_Strassen
  imports Phi_Semantics.PhiSem_C Jordan_Normal_Form.Matrix
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def MatSlice :: \<open>logaddr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (fiction, nat mat) \<phi>\<close>
    where \<open>m \<Ztypecolon> MatSlice addr i j n \<equiv> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,2^n] (\<s>\<l>\<i>\<c>\<e>[j,2^n] \<nat>) \<s>\<u>\<b>\<j> l. l = mat_to_list m\<close>
    deriving \<open>Abstract_Domain (MatSlice addr i j n) (\<lambda>_. addr \<noteq> 0)\<close>

proc add_mat:
  input  \<open>x \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x n\<heavy_comma> y \<Ztypecolon> MatSlice a\<^sub>x i\<^sub>x j\<^sub>x n\<heavy_comma> a\<^sub>x \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<i>\<n>\<t> \<close>

term \<open>Abstract_Domain (MatSlice addr i j n) (\<lambda>_. True)\<close>

term mat_to_list

end