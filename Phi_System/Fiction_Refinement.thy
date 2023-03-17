theory Fiction_Refinement
  imports Spec_Framework
  abbrevs "<refines>" = "\<r>\<e>\<f>\<i>\<n>\<e>\<s>"
      and "<w.r.t>" = "\<w>.\<r>.\<t>"
begin

term Id
term \<open>(O)\<close>
term \<open>(OO)\<close>
term Interp
term \<open>\<I> x\<close>
thm \<phi>Procedure_def


definition Raw_Procedure :: "'ret::VALs proc
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> resource rel)
                        \<Rightarrow> bool"
    ("\<r>\<a>\<w> \<p>\<r>\<o>\<c> (2_) \<r>\<e>\<f>\<i>\<n>\<e>\<s> _ " [11,11] 10)
  where "Raw_Procedure f S \<longleftrightarrow> (\<forall>x r. (\<exists>v y. (x,y) \<in> S v) \<longrightarrow> f (r * x) \<subseteq> \<S> (\<lambda>v. { r * y | y. (x,y) \<in> S v }) 0)"

term Domain

definition Sep_Forward_Simulation :: \<open>'c rel \<Rightarrow> 'a rel \<Rightarrow> ('a::sep_magma_1,'c::sep_magma_1) interp \<Rightarrow> bool\<close>
      ("_ \<r>\<e>\<f>\<i>\<n>\<e>\<s> _ \<w>.\<r>.\<t> _ " [11,11,11] 10)
  where \<open>(F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T) \<longleftrightarrow> (\<forall>x r. F `` \<I> T (r * x) \<subseteq> {y'. \<exists>y. y' \<in> \<I> T (r * y) \<and> (x,y) \<in> G})\<close>

lemma
  \<open>A1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> B1 \<w>.\<r>.\<t> T\<close>

lemma
  \<open> \<r>\<a>\<w> \<p>\<r>\<o>\<c> f \<r>\<e>\<f>\<i>\<n>\<e>\<s> S1
\<Longrightarrow> (\<And>v. S1 v \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> T)
\<close>


lemma
  \<open> 1 \<in> S
\<Longrightarrow> F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T
\<Longrightarrow> F \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on S * G \<w>.\<r>.\<t> T\<close>
  for G :: \<open>'b::sep_monoid rel\<close>
  unfolding Sep_Forward_Simulation_def subset_iff Image_iff Bex_def
  apply (clarsimp simp add: Id_on_iff set_mult_expn)
  by (metis mult_1_class.mult_1_left sep_magma_1_right)

lemma
  \<open> F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T
\<Longrightarrow> Id_on S * F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T\<close>
  unfolding Sep_Forward_Simulation_def subset_iff Image_iff Bex_def
  apply (clarsimp simp add: Id_on_iff set_mult_expn)
  subgoal premises prems for x r b aa ba
  proof -
    thm prems
    have \<open>\<exists>xa. xa \<in> \<I> T (r * x) \<and> (xa, t) \<in> F\<close>
    obtain y where t1: \<open>t \<in> \<I> T (r * y) \<and> (x, y) \<in> G\<close> 
    



end