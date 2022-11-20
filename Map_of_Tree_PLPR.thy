theory Map_of_Tree_PLPR
  imports Map_of_Tree
    "./Phi_Logic_Programming_Reasoner/Phi_Logic_Programming_Reasoner"
begin

subsection \<open>PLPR Procedures\<close>

subsubsection \<open>Subtract Prefix\<close>

lemma [\<phi>reason 1200]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m x = z
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m xs @ ys = zs
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m (x#xs) @ ys = (z#zs)\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 1200 for \<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m [] @ ?ys = ?zs\<close>]:
  \<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m [] @ ys = ys\<close>
  unfolding Premise_def by simp


end