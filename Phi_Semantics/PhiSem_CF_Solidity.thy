theory PhiSem_CF_Solidity
  imports PhiSem_CF_Basic
begin

(*for now we use a quick-and-dirty formalization of the semantics that doesn't use exception mechanism*)

definition op_require :: \<open>(VAL, unit) proc'\<close>
  where \<open>op_require rP =
    \<phi>M_getV bool V_bool.dest rP \<phi>M_assert\<close>
 
lemma require_\<phi>app:
  \<open> \<premise> P
\<Longrightarrow> \<proc> op_require rP \<lbrace> P \<Ztypecolon> \<val>[rP] \<bool> \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding op_require_def
  by (cases rP; simp, rule, simp add: \<phi>expns WT_bool, blast, rule, simp add: \<phi>expns WT_bool)


definition op_require' :: \<open>(VAL, unit) proc'\<close>
  where \<open>op_require' rP =
    \<phi>M_getV bool V_bool.dest rP \<phi>M_assume\<close>

lemma op_require'_\<phi>app:
  \<open>\<proc> op_require' rP \<lbrace> P \<Ztypecolon> \<val>[rP] \<bool> \<longmapsto> \<lambda>_. Void \<subj> P \<rbrace>\<close>
  unfolding op_require'_def
  by (cases rP; simp, rule, simp add: \<phi>expns WT_bool, simp add: \<phi>expns WT_bool, rule)

end