theory PhiSem_CF_Solidity
  imports PhiSem_CF_Basic
begin

(*we first declare a quick-and-dirty formalization of the semantics.*)

definition op_require :: \<open>(VAL, unit) proc'\<close>
  where \<open>op_require rP =
    \<phi>M_getV bool V_bool.dest rP \<phi>M_assert\<close>
 
lemma require_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P
\<Longrightarrow> \<p>\<r>\<o>\<c> op_require rP \<lbrace> P \<Ztypecolon> \<v>\<a>\<l>[rP] \<bool> \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding op_require_def
  by (cases rP; simp, rule, simp add: \<phi>expns WT_bool, blast, rule, simp add: \<phi>expns WT_bool)


end