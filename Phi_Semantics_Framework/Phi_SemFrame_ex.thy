theory Phi_SemFrame_ex
imports Phi_Semantics_Framework
begin

declare [[typedef_overloaded]]

datatype 'ret eval_stat = Normal \<open>'ret \<phi>arg\<close> | Abnm ABNM | Crash

declare [[typedef_overloaded = false]]

lemma eval_stat_forall:
  \<open>All P \<longleftrightarrow> (\<forall>ret. P (Normal ret)) \<and> (\<forall>e. P (Abnm e)) \<and> P Crash\<close>
  by (metis eval_stat.exhaust)

lemma eval_stat_ex:
  \<open>Ex P \<longleftrightarrow> (\<exists>ret. P (Normal ret)) \<or> (\<exists>e. P (Abnm e)) \<or> P Crash\<close>
  by (metis eval_stat.exhaust)

definition Transition_of' :: \<open>'ret proc \<Rightarrow> 'ret eval_stat \<Rightarrow> resource rel\<close>
  where \<open>Transition_of' f = (\<lambda>x. (case x of Normal v \<Rightarrow> { (s,s'). Success v s' \<in> f s \<and> s \<in> RES.SPACE }
                                          | Abnm e \<Rightarrow> { (s,s'). Abnormal e s' \<in> f s \<and> s \<in> RES.SPACE }
                                          | Crash \<Rightarrow> { (s,s'). Invalid \<in> f s \<and> s = s' \<and> s \<in> RES.SPACE }))\<close>

definition Valid_Transition :: \<open>('ret eval_stat \<Rightarrow> 'a rel) \<Rightarrow> bool\<close>
  where \<open>Valid_Transition tr \<longleftrightarrow> tr Crash = {}\<close>




end