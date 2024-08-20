theory Phi_Fiction
  imports Phi_System.Phi_BI Unital_Homo
begin

section \<open>Interpretation of Fictional Separation\<close>

subsection \<open>Algebraic Structure\<close>

subsubsection \<open>Auxiliary\<close>

definition \<open>pairself f = (\<lambda>(x,y). (f x, f y))\<close>

lemma pairself[simp]:
  \<open>pairself f (x,y) = (f x, f y)\<close>
  unfolding pairself_def by simp

lemma pairself_image_Id_on[simp]:
  \<open>pairself f ` Id_on S = Id_on (f ` S)\<close>
  by (clarsimp simp add: set_eq_iff Id_on_iff image_iff Bex_def; blast)
(*
definition BI_Image :: \<open>('a \<times> 'b) set \<Rightarrow> 'a BI \<Rightarrow> 'b BI\<close>  (infixr "``\<^sub>I" 90)
  where "r ``\<^sub>I s = BI (r `` BI.dest s)"

lemma BI_Image_expn[iff]:
  \<open> w \<Turnstile> r ``\<^sub>I s \<longleftrightarrow> (\<exists>w'. (w',w) \<in> r \<and> w' \<Turnstile> s) \<close>
  unfolding BI_Image_def
  by (meson ImageE Satisfaction_BI_red Satisfaction_def rev_ImageI)

definition BI_Id_on :: "'a BI \<Rightarrow> ('a \<times> 'a) BI"
  where "BI_Id_on A = BI (Id_on (BI.dest A))"

lemma BI_Id_on_expn[iff]:
  \<open> (a,b) \<Turnstile> BI_Id_on A \<longleftrightarrow> a = b \<and> a \<Turnstile> A \<close>
  unfolding BI_Id_on_def
  by (cases A; auto)

lemma BI_Id_on_0[iff]:
  \<open>BI_Id_on 0 = 0\<close>
  unfolding BI_eq_iff by simp

definition i_relcomp :: \<open>('a \<times> 'b) BI \<Rightarrow> ('b \<times> 'c) BI \<Rightarrow> ('a \<times> 'c) BI\<close> (infixr "O\<^sub>I" 75)
  where \<open> A O\<^sub>I B = BI (BI.dest A O BI.dest B) \<close>

lemma i_relcomp_expn[iff]:
  \<open> (a,c) \<Turnstile> R O\<^sub>I S \<longleftrightarrow> (\<exists>b. (a,b) \<Turnstile> R \<and> (b,c) \<Turnstile> S) \<close>
  unfolding i_relcomp_def
  by (cases R; cases S; simp; blast)
*)
definition BI_Monad_Comb :: \<open>'a BI BI \<Rightarrow> 'a BI\<close>
  where \<open>BI_Monad_Comb S = Sup (BI.dest S)\<close>

lemma BI_Monad_Comb_expn[iff]:
  \<open> w \<Turnstile> BI_Monad_Comb S \<longleftrightarrow> (\<exists>m. m \<Turnstile> S \<and> w \<Turnstile> m) \<close>
  unfolding BI_Monad_Comb_def
  by (cases S; auto)


subsection \<open>Subjection\<close>

definition SubjectionSet :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<s>\<u>\<b>\<j>\<s>" 15)
  where " (T \<s>\<u>\<b>\<j>\<s> P) = {p. p \<in> T \<and> P}"

lemma SubjectionSet_expn[iff]:
  \<open>p \<in> (S \<s>\<u>\<b>\<j>\<s> P) \<longleftrightarrow> p \<in> S \<and> P\<close>
  by (simp add: SubjectionSet_def)

lemma SubjectionSet_cong:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<s>\<u>\<b>\<j>\<s> P) \<equiv> (S' \<s>\<u>\<b>\<j>\<s> P')\<close>
  unfolding atomize_eq by (simp, blast)

lemma SubjectionSet_red[iff]:
  \<open> (S \<s>\<u>\<b>\<j>\<s> True) = S \<close>
  \<open> (S \<s>\<u>\<b>\<j>\<s> False) = {} \<close>
  unfolding SubjectionSet_def by simp_all

lemma SubjectionSet_times[simp]:
  \<open>(S \<s>\<u>\<b>\<j>\<s> P) * T = (S * T \<s>\<u>\<b>\<j>\<s> P)\<close>
  \<open>T * (S \<s>\<u>\<b>\<j>\<s> P) = (T * S \<s>\<u>\<b>\<j>\<s> P)\<close>
  unfolding set_eq_iff
  by (simp add: set_mult_expn, blast)+

lemma SubjectionSet_Id_on:
  \<open>Id_on (S \<s>\<u>\<b>\<j>\<s> P) = (Id_on S \<s>\<u>\<b>\<j>\<s> P)\<close>
  by auto

lemma SubjectionSet_image:
  \<open>f ` (S \<s>\<u>\<b>\<j>\<s> P) = (f ` S \<s>\<u>\<b>\<j>\<s> P)\<close>
  unfolding set_eq_iff
  by simp blast

lemma SubjectionSet_Subjection[simp]:
  \<open>(S \<s>\<u>\<b>\<j>\<s> P \<s>\<u>\<b>\<j>\<s> Q) = (S \<s>\<u>\<b>\<j>\<s> P \<and> Q)\<close>
  unfolding set_eq_iff
  by simp

lemma SubjectionSet_Zero[simp]:
  \<open>(0 \<s>\<u>\<b>\<j>\<s> P) = 0\<close>
  unfolding set_eq_iff
  by simp


paragraph \<open>Supplementary of Meta-Ball\<close>

lemma [\<phi>reason %meta_ball]:
  \<open> (Q \<Longrightarrow> (\<And>x \<in> S. PROP P x))
\<Longrightarrow> (\<And>x \<in> S \<s>\<u>\<b>\<j>\<s> Q. PROP P x)\<close>
  unfolding meta_Ball_def Premise_def
  by (clarsimp simp add: atomize_conj[symmetric] conjunction_imp norm_hhf_eq)

lemma [\<phi>reason %meta_ball]:
  \<open> (Q \<Longrightarrow> \<forall>x \<in> S. P x)
\<Longrightarrow> (\<forall>x \<in> S \<s>\<u>\<b>\<j>\<s> Q. P x)\<close>
  unfolding Ball_def
  by simp


subsubsection \<open>ExSet\<close>

definition ExSet :: " ('x \<Rightarrow> 'c set) \<Rightarrow> 'c set" (binder "\<exists>\<^sup>s" 14)
  where "ExSet S = {p. (\<exists>c. p \<in> S c)}"

lemma ExSet_expn[iff, \<phi>expns]:
  \<open>p \<in> (ExSet S) \<longleftrightarrow> (\<exists>x. p \<in> S x)\<close>
  by (simp add: ExSet_def)

lemma ExSet_const[iff]:
  \<open>ExSet (\<lambda>_. S) = S\<close>
  unfolding set_eq_iff
  by clarsimp

lemma ExSet_times_left [simp]:
  "((\<exists>\<^sup>s c. T c) * R) = (\<exists>\<^sup>s c. T c * R )"
  by (simp add: set_eq_iff set_mult_expn, blast)

lemma ExSet_times_right[simp]:
  "(L * (\<exists>\<^sup>sc. T c)) = (\<exists>\<^sup>s c. L * T c)"
  by (simp add: set_eq_iff set_mult_expn, blast)

lemma ExSet_Id_on:
  \<open>Id_on (\<exists>\<^sup>sx. S x) = (\<exists>\<^sup>sx. Id_on (S x))\<close>
  by (auto; blast)

lemma ExSet_image:
  \<open>f ` (\<exists>\<^sup>sc. S c) = (\<exists>\<^sup>sc. f ` S c)\<close>
  by (auto simp add: image_iff Bex_def; blast)

lemma ExSet_simps[simp]:
  \<open>ExSet 0 = 0\<close>
  \<open>ExSet (\<lambda>_. T) = T\<close>
  \<open>((\<exists>\<^sup>sc. X c) \<s>\<u>\<b>\<j>\<s> PP) = (\<exists>\<^sup>sc. X c \<s>\<u>\<b>\<j>\<s> PP)\<close>
  \<open>(\<exists>\<^sup>sy. F' y \<s>\<u>\<b>\<j>\<s> embedded_func f' P' x' y) = (F' (f' x') \<s>\<u>\<b>\<j>\<s> P' x')\<close>
  unfolding set_eq_iff embedded_func_def
  by simp_all

lemma ExSet_defined[simp]:
  \<open>(\<exists>\<^sup>s x. F x \<s>\<u>\<b>\<j>\<s> x = y) = (F y)\<close>
  \<open>(\<exists>\<^sup>s x. F x \<s>\<u>\<b>\<j>\<s> y = x) = (F y)\<close>
  \<open>(\<exists>\<^sup>s x. F x \<s>\<u>\<b>\<j>\<s> x = y \<and> P x) = (F y \<s>\<u>\<b>\<j>\<s> P y)\<close>
  \<open>(\<exists>\<^sup>s x. F x \<s>\<u>\<b>\<j>\<s> y = x \<and> P x) = (F y \<s>\<u>\<b>\<j>\<s> P y)\<close>
  unfolding set_eq_iff
  by simp_all

lemma split_discrete_ExSet: \<open>(\<exists>\<^sup>sx. P x) = (\<exists>\<^sup>sx. P (discrete x))\<close>
  unfolding set_eq_iff by (simp add: split_discrete_ex)


subsubsection \<open>Fictional Interpretation\<close>

text \<open>
  Referring to Fictional Separation Logic~\cite{FSL}, the interpretation of fictional separation
  maps a fictional resource to a set of concrete resource.
  The interpretation can be any map to set that preserves \<open>1\<close>, the unit of the separation algebra.\<close>

type_synonym 'a BI_rel = \<open>('a \<times> 'a) BI\<close>
type_synonym ('a,'b) unital_homo_interp = \<open>('a, 'b BI) unital_homo\<close>

(*
definition \<I>\<^sub>r\<^sub>e\<^sub>l :: \<open>('a::one,'b::one) interp \<Rightarrow> ('a \<times> 'b) set\<close> 
  where \<open>\<I>\<^sub>r\<^sub>e\<^sub>l I = {(x,y). y \<in> \<I> I x}\<close> *)


subsubsection \<open>Fictional Refinement\<close>

definition Fictional_Forward_Simulation :: \<open>'c rel \<Rightarrow> 'a rel \<Rightarrow> ('c::sep_magma, 'a::sep_magma) \<phi> \<Rightarrow> 'a set \<Rightarrow> bool\<close>
      ("_/ \<r>\<e>\<f>\<i>\<n>\<e>\<s> _/ \<w>.\<r>.\<t> _/ \<i>\<n> _" [11,11,11] 10)
  where \<open>(F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T \<i>\<n> D)
    \<longleftrightarrow> (\<forall>x r R. F `` BI.dest (T (x * r) * R \<s>\<u>\<b>\<j> x ## r \<and> x \<in> D) \<le> { y'. \<exists>y. y' \<Turnstile> T (y * r) * R \<and> y ## r \<and> (x,y) \<in> G})\<close>

text \<open>We use relation directly here but doesn't mean we cannot model return value or threw exceptions.
They can parameterize the relation, as we don't need to (it is not designed to) abstract the values.
We only relate resources in different abstractions.

\<^prop>\<open>\<And>ret. F ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> G ret \<w>.\<r>.\<t> T \<i>\<n> D\<close>
\<close>

lemma empty_refines_any[simp]:
  \<open>0 \<r>\<e>\<f>\<i>\<n>\<e>\<s> Any \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def subset_iff
  by (simp add: Image_iff)

lemma refinement_sub_domain:
  \<open> D' \<le> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D'\<close>
  unfolding Fictional_Forward_Simulation_def subset_iff
  by (clarsimp simp add: subset_iff Image_iff Image_def Bex_def Id_on_iff) blast

lemma refinement_sub_fun:
  \<open> A' \<le> A
\<Longrightarrow> A  \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A' \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def less_eq_BI_iff
  by (clarsimp simp add: subset_iff Image_def Bex_def Id_on_iff; blast)

lemma refinement_sub_fun_right:
  \<open> B \<le> B'
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B' \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def less_eq_BI_iff
  by (clarsimp simp add: subset_iff Image_def Bex_def Id_on_iff; blast)

lemma refinement_frame:
  \<open> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B * Id_on R \<w>.\<r>.\<t> I \<i>\<n> D * R\<close>
  for B :: \<open>'b::sep_semigroup rel\<close>
  unfolding Fictional_Forward_Simulation_def less_eq_BI_iff
  by (clarsimp simp add: subset_iff set_mult_expn Image_def Bex_def Id_on_iff,
      smt (z3) sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc')

lemma sep_refinement_horizontal_stepwise:
  \<open> A1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B2 \<w>.\<r>.\<t> I \<i>\<n> D'
\<Longrightarrow> (B1 `` D \<le> D')
\<Longrightarrow> A1 O A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 O B2 \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def subset_iff
  apply (clarsimp simp add: Image_iff Bex_def)
  subgoal premises prems for x r R u v y z
  proof -
    have \<open>\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<Turnstile> I (x * r) \<and> v \<Turnstile> R \<and> u ## v) \<and> x ## r \<and> x \<in> D \<and> (xa, y) \<in> A1\<close>
      using prems(10) prems(4) prems(5) prems(6) prems(8) prems(9) by blast
    note prems(1)[THEN spec[where x=x], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=y],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y' u' v'
      proof -
        have \<open>\<exists>x. (\<exists>u v. x = u * v \<and> u \<Turnstile> I (y' * r) \<and> v \<Turnstile> R \<and> u ## v) \<and> y' ## r \<and> y' \<in> D' \<and> (x, z) \<in> A2\<close>
          using prems(3) prems(5) prems(7) prems2(1) prems2(2) prems2(3) prems2(4) prems2(5) prems2(6) by blast
        note prems(2)[THEN spec[where x=y'], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=z],
          THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(2) by blast
      qed .
  qed .

lemma constant_refinement:
  \<open>Id_on A * Id_on top \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on B \<w>.\<r>.\<t> I \<i>\<n> B\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff Id_on_iff set_mult_expn times_fun; blast)

lemma refinement_subjection:
  \<open> (P \<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D)
\<Longrightarrow> P \<longrightarrow> Q
\<Longrightarrow> A \<s>\<u>\<b>\<j>\<s> P \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<s>\<u>\<b>\<j>\<s> Q \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def 
  by (clarsimp simp add: less_eq_BI_iff Image_def Bex_def) blast

lemma refinement_existential:
  \<open> (\<And>x. A x \<r>\<e>\<f>\<i>\<n>\<e>\<s> B x \<w>.\<r>.\<t> I \<i>\<n> D)
\<Longrightarrow> ExSet A \<r>\<e>\<f>\<i>\<n>\<e>\<s> ExSet B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff Image_def Bex_def Id_on_iff; blast)

lemma refinement_source_subjection:
  \<open>(A \<s>\<u>\<b>\<j>\<s> P \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D) \<longleftrightarrow> (P \<longrightarrow> (A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D))\<close>
  unfolding Fictional_Forward_Simulation_def
  by (auto simp add: less_eq_BI_iff Image_def Bex_def Id_on_iff set_mult_expn; blast)

lemma refinement_ExBI:
  \<open> (\<And>v. A v \<r>\<e>\<f>\<i>\<n>\<e>\<s> B v \<w>.\<r>.\<t> I \<i>\<n> D)
\<Longrightarrow> ExSet A \<r>\<e>\<f>\<i>\<n>\<e>\<s> ExSet B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff Image_def Bex_def Id_on_iff, blast)


subsection \<open>Separation Closed Set\<close>

definition One_in_Set :: \<open>'a::one set \<Rightarrow> bool\<close>
  where \<open>One_in_Set S \<longleftrightarrow> 1 \<in> S\<close>

definition Sep_Closed :: \<open>'a::sep_magma set \<Rightarrow> bool\<close>
  where \<open>Sep_Closed S \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> x \<in> S \<and> y \<in> S \<longrightarrow> (x * y) \<in> S)\<close>

lemma Sep_Closed_inter:
  \<open>Sep_Closed S1 \<Longrightarrow> Sep_Closed S2 \<Longrightarrow> Sep_Closed (S1 \<inter> S2)\<close>
  unfolding Sep_Closed_def by blast

lemma One_in_Set_inter:
  \<open>One_in_Set S1 \<Longrightarrow> One_in_Set S2 \<Longrightarrow> One_in_Set (S1 \<inter> S2)\<close>
  unfolding One_in_Set_def by blast

lemma Sep_Closed_UNIV[simp]:
  \<open>Sep_Closed UNIV\<close>
  unfolding Sep_Closed_def by simp

lemma One_in_Set_UNIV[simp]:
  \<open>One_in_Set UNIV\<close>
  unfolding One_in_Set_def by simp

typedef (overloaded) ('a::sep_magma_1) sep_closed_set
    = \<open>Collect (Sep_Closed::'a set \<Rightarrow> bool) \<inter> Collect One_in_Set\<close>
  morphisms dest_sep_closed_set sep_closed_set
  unfolding Sep_Closed_def One_in_Set_def by blast

setup_lifting type_definition_sep_closed_set

lift_definition sep_closed_member :: \<open>'a::sep_magma_1 \<Rightarrow> 'a sep_closed_set \<Rightarrow> bool\<close> (infix "\<in>\<^sub>S" 50)
  is \<open>\<lambda>x S. x \<in> S\<close> .

lemma in_sep_closed_set[simp]:
  \<open>Sep_Closed S \<Longrightarrow> One_in_Set S \<Longrightarrow> x \<in>\<^sub>S sep_closed_set S \<longleftrightarrow> x \<in> S\<close>
  unfolding sep_closed_member_def
  by (simp add: sep_closed_set_inverse)

lemma one_in_sep_closed_set[simp]:
  \<open>1 \<in>\<^sub>S S\<close> for S :: \<open>'a::sep_magma_1 sep_closed_set\<close>
  by (transfer; simp add: One_in_Set_def)

lemma mult_in_sep_closed_set[simp]:
  \<open>x ## y \<Longrightarrow> x \<in>\<^sub>S S \<and> y \<in>\<^sub>S S \<longrightarrow> x * y \<in>\<^sub>S S\<close> for S :: \<open>'a::sep_algebra sep_closed_set\<close>
  by (transfer; simp add: Sep_Closed_def)

lift_definition sep_closed_inter :: \<open>'a::sep_magma_1 sep_closed_set \<Rightarrow> 'a sep_closed_set \<Rightarrow> 'a sep_closed_set\<close> (infixl "\<inter>\<^sub>S" 65)
  is \<open>\<lambda>S1 S2. S1 \<inter> S2\<close>
  by (clarsimp simp add: Sep_Closed_def One_in_Set_def; blast)

definition sep_closed_image :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> 'a sep_closed_set \<Rightarrow> 'b sep_closed_set\<close> (infixr "`\<^sub>S" 90)
  where \<open>(f `\<^sub>S S) = sep_closed_set (f ` dest_sep_closed_set S) \<close>

(*
definition Homo_Sep_Closed :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> bool\<close>
  where \<open>Homo_Sep_Closed f \<longleftrightarrow> (\<forall>S. Sep_Closed S \<longrightarrow> Sep_Closed (f ` S))\<close>

lemma in_image_sep_closed[simp]:
  \<open>Homo_Sep_Closed f \<Longrightarrow> x \<in>\<^sub>S f `\<^sub>S S \<longleftrightarrow> (\<exists>x'. x = f x' \<and> x' \<in>\<^sub>S S)\<close>
  by (smt (verit, del_insts) Homo_Sep_Closed_def  dest_sep_closed_set dest_sep_closed_set_inverse image_iff in_sep_closed_set mem_Collect_eq sep_closed_image_def)
*)


subsubsection \<open>Aux\<close>

definition [simp]: "\<F>_FP_homo I f = prod (\<lambda>x. apply_unital_homo (I x) (f x)) (dom1 f)"

lemma \<F>_FP_homo_split:
  " finite (dom1 f)
\<Longrightarrow> \<F>_FP_homo I f = apply_unital_homo (I k) (f k) * \<F>_FP_homo I (f(k:=1))
   \<and> apply_unital_homo (I k) (f k) ## \<F>_FP_homo I (f(k:=1)) "
  for I :: \<open>'a \<Rightarrow> ('b::sep_algebra, 'c::sep_algebra set) unital_homo\<close>
  by (simp add: homo_one_def,
      smt (verit, ccfv_SIG) Diff_empty Diff_insert0 apply_unital_homo_1 dom1_def mem_Collect_eq mult.commute mult_1_class.mult_1_right prod.remove)


subsubsection \<open>Common Sep-Closed Sets\<close>

lemma sep_closed_partial_map[simp]:
  \<open>Sep_Closed {vars. finite (dom vars)}\<close>
  unfolding Sep_Closed_def
  by (clarsimp simp add: dom_mult)

lemma sep_closed_partial_map1[simp]:
  \<open>Sep_Closed {h::'a \<Rightarrow> 'b :: sep_no_inverse. finite (dom1 h)}\<close> 
  unfolding Sep_Closed_def
  by (clarsimp simp add: dom1_mult)

lemma Sep_Closed_pointwise:
  \<open> (\<forall>k. P k 1)
\<Longrightarrow> (\<forall>k x y. x ## y \<longrightarrow> P k x \<and> P k y \<longrightarrow> P k (x * y))
\<Longrightarrow>   Sep_Closed {f. \<forall>k. P k (f k) }\<close>
  unfolding Sep_Closed_def
  by (simp add: times_fun; blast)



subsection \<open>Separation Homo Set\<close>

definition Sep_Homo :: \<open>'a::sep_magma_1 set \<Rightarrow> bool\<close>
  where \<open>Sep_Homo S \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> (x * y) \<in> S \<longleftrightarrow> x \<in> S \<and> y \<in> S) \<and> 1 \<in> S\<close>

lemma Sep_Homo_inter:
  \<open>Sep_Homo S1 \<Longrightarrow> Sep_Homo S2 \<Longrightarrow> Sep_Homo (S1 \<inter> S2)\<close>
  unfolding Sep_Homo_def by blast

lemma Sep_Homo_UNIV[simp]:
  \<open>Sep_Homo UNIV\<close>
  unfolding Sep_Homo_def by simp

typedef (overloaded) ('a::sep_magma_1) sep_homo_set = \<open>Collect (Sep_Homo::'a set \<Rightarrow> bool)\<close>
  morphisms dest_sep_homo_set sep_homo_set
  unfolding Sep_Homo_def by blast

setup_lifting type_definition_sep_homo_set

lift_definition sep_homo_member :: \<open>'a::sep_magma_1 \<Rightarrow> 'a sep_homo_set \<Rightarrow> bool\<close> (infix "\<in>\<^sub>S\<^sub>H" 50)
  is \<open>\<lambda>x S. x \<in> S\<close> .

lemma in_sep_homo_set[simp]:
  \<open>Sep_Homo S \<Longrightarrow> x \<in>\<^sub>S\<^sub>H sep_homo_set S \<longleftrightarrow> x \<in> S\<close>
  unfolding sep_homo_member_def
  by (simp add: sep_homo_set_inverse)

lemma one_in_sep_homo_set[simp]:
  \<open>1 \<in>\<^sub>S\<^sub>H S\<close> for S :: \<open>'a::sep_magma_1 sep_homo_set\<close>
  by (transfer; simp add: Sep_Homo_def)

lemma mult_in_sep_homo_set[simp]:
  \<open>x ## y \<Longrightarrow> x * y \<in>\<^sub>S\<^sub>H S \<longleftrightarrow> x \<in>\<^sub>S\<^sub>H S \<and> y \<in>\<^sub>S\<^sub>H S\<close> for S :: \<open>'a::sep_algebra sep_homo_set\<close>
  by (transfer; simp add: Sep_Homo_def)

lift_definition sep_homo_inter :: \<open>'a::sep_magma_1 sep_homo_set \<Rightarrow> 'a sep_homo_set \<Rightarrow> 'a sep_homo_set\<close> (infixl "\<inter>\<^sub>S\<^sub>H" 65)
  is \<open>\<lambda>S1 S2. S1 \<inter> S2\<close>
  by (clarsimp simp add: Sep_Homo_def; blast)

definition sep_homo_image :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> 'a sep_homo_set \<Rightarrow> 'b sep_homo_set\<close> (infixr "`\<^sub>S\<^sub>H" 90)
  where \<open>(f `\<^sub>S\<^sub>H S) = sep_homo_set (f ` dest_sep_homo_set S) \<close>

definition Homo_Sep_Homo :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> bool\<close>
  where \<open>Homo_Sep_Homo f \<longleftrightarrow> (\<forall>S. Sep_Homo S \<longrightarrow> Sep_Homo (f ` S))\<close>

lemma in_image_sep_homo[simp]:
  \<open>Homo_Sep_Homo f \<Longrightarrow> x \<in>\<^sub>S\<^sub>H f `\<^sub>S\<^sub>H S \<longleftrightarrow> (\<exists>x'. x = f x' \<and> x' \<in>\<^sub>S\<^sub>H S)\<close>
  by (smt (verit, best) Homo_Sep_Homo_def dest_sep_homo_set dest_sep_homo_set_inverse image_iff in_sep_homo_set mem_Collect_eq sep_homo_image_def)
  
subsubsection \<open>Common Sep-Homo Sets\<close>

lemma sep_homo_partial_map[simp]:
  \<open>Sep_Homo {vars. finite (dom vars)}\<close>
  unfolding Sep_Homo_def
  by (clarsimp simp add: dom_mult)

lemma sep_homo_partial_map1[simp]:
  \<open>Sep_Homo {h::'a \<Rightarrow> 'b :: sep_no_inverse. finite (dom1 h)}\<close> 
  unfolding Sep_Homo_def
  by (clarsimp simp add: dom1_mult)

lemma Sep_Homo_pointwise:
  \<open> (\<forall>k. P k 1)
\<Longrightarrow> (\<forall>k x y. x ## y \<longrightarrow> P k (x * y) \<longleftrightarrow> P k x \<and> P k y)
\<Longrightarrow>   Sep_Homo {f. \<forall>k. P k (f k) }\<close>
  unfolding Sep_Homo_def
  by (simp add: times_fun; blast)




end