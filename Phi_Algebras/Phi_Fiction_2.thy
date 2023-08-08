theory Phi_Fiction_2
  imports Algebras
begin

section \<open>Interpretation of Fictional Separation\<close>

subsection \<open>Algebraic Structure\<close>

subsubsection \<open>Auxiliary Helper\<close>

definition \<open>pairself f = (\<lambda>(x,y). (f x, f y))\<close>

lemma pairself[simp]:
  \<open>pairself f (x,y) = (f x, f y)\<close>
  unfolding pairself_def by simp

lemma pairself_image_Id_on[simp]:
  \<open>pairself f ` Id_on S = Id_on (f ` S)\<close>
  by (clarsimp simp add: set_eq_iff Id_on_iff image_iff Bex_def; blast)


subsubsection \<open>Fictional Interpretation\<close>

text \<open>
  Referring to Fictional Separation Logic~\cite{FSL}, the interpretation of fictional separation
  maps a fictional resource to a set of concrete resource.
  The interpretation can be any map to set that preserves \<open>1\<close>, the unit of the separation algebra.\<close>

definition Interpretation :: "('a::one \<Rightarrow> 'b::one set) \<Rightarrow> bool"
  where "Interpretation \<I> \<longleftrightarrow> \<I> 1 = 1"

typedef (overloaded) ('a::one,'b::one) interp
    = \<open>Collect (Interpretation :: ('a \<Rightarrow> 'b set) \<Rightarrow> bool)\<close>
  morphisms \<I> Interp
  by (rule exI[where x = \<open>\<lambda>_. 1\<close>]) (simp add:sep_mult_commute Interpretation_def)

text \<open>Type \<open>('a,'b) interp\<close> encapsulating the 1-preserving condition, represents an interpretation.
\<^const>\<open>\<I>\<close> activates the interpretation; \<^const>\<open>Interp\<close> constructs an interpretation by checking
the 1-preserving condition.
\[@{thm Interp_inverse[simplified]}\]\<close>

lemmas Interp_inverse[simp] = Interp_inverse[simplified]

lemma Interp_one[simp]: "\<I> I 1 = 1"
  using Interpretation_def \<I> by blast

lemma interp_eq_I[intro!]:
  \<open>\<I> x = \<I> y \<Longrightarrow> x = y\<close>
  by (simp add: \<I>_inject)
  

(*
definition \<I>\<^sub>r\<^sub>e\<^sub>l :: \<open>('a::one,'b::one) interp \<Rightarrow> ('a \<times> 'b) set\<close> 
  where \<open>\<I>\<^sub>r\<^sub>e\<^sub>l I = {(x,y). y \<in> \<I> I x}\<close> *)


subsubsection \<open>Fictional Refinement\<close>

definition Fictional_Forward_Simulation :: \<open>'c rel \<Rightarrow> 'a rel \<Rightarrow> ('a::sep_magma_1,'c::sep_magma_1) interp \<Rightarrow> 'a set \<Rightarrow> bool\<close>
      ("_/ \<r>\<e>\<f>\<i>\<n>\<e>\<s> _/ \<w>.\<r>.\<t> _/ \<i>\<n> _" [11,11,11] 10)
  where \<open>(F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T \<i>\<n> D)
    \<longleftrightarrow> (\<forall>x r R. F `` (R * \<I> T (r * x) \<s>\<u>\<b>\<j> r ## x \<and> x \<in> D) \<subseteq> { y'. \<exists>y. y' \<in> R * \<I> T (r * y) \<and> r ## y \<and> (x,y) \<in> G})\<close>

text \<open>We use relation directly here but doesn't mean we cannot model return value or threw exceptions.
They can parameterize the relation, as we don't need to (it is not designed to) abstract the values.
We only relate resources in different abstractions.

\<^prop>\<open>\<And>ret. F ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> G ret \<w>.\<r>.\<t> T \<i>\<n> D\<close>
\<close>

definition \<open>refinement_projection I D = \<Union> (\<I> I ` (UNIV * D))\<close>

lemma empty_refines_any[simp]:
  \<open>{} \<r>\<e>\<f>\<i>\<n>\<e>\<s> Any \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by simp

lemma refinement_sub_domain:
  \<open> D' \<subseteq> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D'\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Subjection_expn subset_iff Image_def Bex_def Id_on_iff, blast)

lemma refinement_sub_fun:
  \<open> A' \<subseteq> A
\<Longrightarrow> A  \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A' \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Subjection_expn subset_iff Image_def Bex_def Id_on_iff; blast)

lemma refinement_sub_fun_right:
  \<open> B \<subseteq> B'
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B' \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Subjection_expn subset_iff Image_def Bex_def Id_on_iff; blast)

lemma refinement_frame:
  \<open> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on R * B \<w>.\<r>.\<t> I \<i>\<n> R * D\<close>
  for B :: \<open>'b::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff Subjection_expn set_mult_expn Image_def Bex_def Id_on_iff)
  by (smt (z3) sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc')

lemma sep_refinement_horizontal_stepwise:
  \<open> A1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B2 \<w>.\<r>.\<t> I \<i>\<n> D'
\<Longrightarrow> (B1 `` D \<subseteq> D')
\<Longrightarrow> A1 O A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 O B2 \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn Subjection_expn subset_iff Image_def Bex_def)
  subgoal premises prems for x r R u v y z
  proof -
    have \<open>(\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<in> R \<and> v \<in> \<I> I (r * x) \<and> u ## v) \<and> r ## x \<and> x \<in> D \<and> (xa, y) \<in> A1)\<close>
      using prems(10) prems(4) prems(5) prems(6) prems(8) prems(9) by blast
    note prems(1)[THEN spec[where x=x], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=y],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y' u' v'
      proof -
        have \<open>(\<exists>x. (\<exists>u v. x = u * v \<and> u \<in> R \<and> v \<in> \<I> I (r * y') \<and> u ## v) \<and> r ## y' \<and> y' \<in> D' \<and> (x, z) \<in> A2)\<close>
          using prems(3) prems(5) prems(7) prems2(1) prems2(2) prems2(3) prems2(4) prems2(5) prems2(6) by blast
        note prems(2)[THEN spec[where x=y'], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=z],
          THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(2) by blast
      qed .
  qed .

lemma constant_refinement:
  \<open>Id_on UNIV * Id_on A \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on B \<w>.\<r>.\<t> I \<i>\<n> B\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: subset_iff Id_on_iff set_mult_expn Subjection_expn times_fun; blast)

lemma refinement_subjection:
  \<open> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<s>\<u>\<b>\<j> P \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<s>\<u>\<b>\<j> P \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Subjection_expn subset_iff Image_def Bex_def Id_on_iff)

lemma refinement_ExSet:
  \<open> (\<And>v. A v \<r>\<e>\<f>\<i>\<n>\<e>\<s> B v \<w>.\<r>.\<t> I \<i>\<n> D)
\<Longrightarrow> ExSet A \<r>\<e>\<f>\<i>\<n>\<e>\<s> ExSet B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: ExSet_expn subset_iff Image_def Bex_def Id_on_iff, blast)


subsection \<open>Instances\<close>

subsubsection \<open>Itself\<close>

definition [simp]: "\<F>_it' x = {x}"

definition "\<F>_it = Interp \<F>_it'"

lemma \<F>_it_\<I>[simp]: "\<I> \<F>_it = \<F>_it'"
  unfolding \<F>_it_def
  by (rule Interp_inverse) (simp add: Interpretation_def one_set_def)

lemma \<F>_it_refinement_projection:
  \<open>refinement_projection \<F>_it S \<subseteq> UNIV * S\<close>
  unfolding refinement_projection_def
  by (clarsimp simp add: set_mult_expn)

lemma \<F>_it_refinement:
  \<open>Id_on UNIV * {(u,v)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(u,v)} \<w>.\<r>.\<t> \<F>_it \<i>\<n> {u}\<close>
  for u :: \<open>'a::{sep_cancel,sep_monoid}\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Subjection_expn set_mult_expn,
      metis sep_cancel sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc')


subsubsection \<open>Composition\<close>

definition interp_comp :: \<open>('b::one,'c::one) interp \<Rightarrow> ('a::one,'b) interp \<Rightarrow> ('a,'c) interp\<close> (infixr "\<Zcomp>\<^sub>\<I>" 55)
  where \<open>(I1 \<Zcomp>\<^sub>\<I> I2) = Interp (\<lambda>x. \<Union>(\<I> I1 ` \<I> I2 x))\<close>

notation (ASCII) interp_comp  (infixl ";\<^sub>\<I>" 55)

lemma interp_comp_\<I>[simp]:
  \<open>\<I> (I1 \<Zcomp>\<^sub>\<I> I2) = (\<lambda>x. \<Union>(\<I> I1 ` \<I> I2 x))\<close>
  unfolding interp_comp_def
  by (rule Interp_inverse)  (simp add: Interpretation_def one_set_def)

lemma interp_comp_assoc:
  \<open>(I1 \<Zcomp>\<^sub>\<I> I2) \<Zcomp>\<^sub>\<I> I3 = I1 \<Zcomp>\<^sub>\<I> (I2 \<Zcomp>\<^sub>\<I> I3)\<close>
  by (subst \<I>_inject[symmetric]; simp)

lemma \<F>_it_comp[simp]:
  \<open>\<F>_it ;\<^sub>\<I> I = I\<close> \<open>I ;\<^sub>\<I> \<F>_it = I\<close>
  by (subst \<I>_inject[symmetric], simp)+

lemma sep_refinement_stepwise:
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> I1 \<i>\<n> D
\<Longrightarrow> S2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> I2 \<i>\<n> D'
\<Longrightarrow> refinement_projection I2 D' \<subseteq> D
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (I1 \<Zcomp>\<^sub>\<I> I2) \<i>\<n> D'\<close>
  unfolding Fictional_Forward_Simulation_def interp_comp_\<I> refinement_projection_def
  apply (auto simp add: subset_iff Image_def Bex_def Subjection_expn set_mult_expn split_option_all)
  subgoal premises prems for x r R t u v xb
  proof -
    thm prems
    thm prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>]]
    have \<open>(\<exists>x. (\<exists>u v. x = u * v \<and> u \<in> R \<and> v \<in> \<I> I1 (1 * xb) \<and> u ## v) \<and> 1 ## xb \<and> xb \<in> D \<and> (x, t) \<in> S1)\<close>
      apply (simp add: prems)
      using prems(10) prems(3) prems(4) prems(5) prems(6) prems(7) prems(8) prems(9) by blast
    note prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y u'' v''
      proof -
        have \<open>(\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<in> {1} \<and> v \<in> \<I> I2 (r * x) \<and> u ## v) \<and> r ## x \<and> x \<in> D' \<and> (xa, y) \<in> S2)\<close>
          by (simp, rule exI[where x=xb], simp add: prems2 prems)
        note prems(2)[THEN spec[where x=x],THEN spec[where x=r],THEN spec[where x=\<open>{1}\<close>], THEN spec[where x=y],
                THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(3) prems2(4) prems2(5) by auto
      qed .
  qed .

lemma sep_refinement_stepwise':
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> I1 \<i>\<n> D
\<Longrightarrow> S2' \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> I2 \<i>\<n> D'
\<Longrightarrow> refinement_projection I2 D' \<subseteq> D
\<Longrightarrow> S2 \<subseteq> S2'
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (I1 \<Zcomp>\<^sub>\<I> I2) \<i>\<n> D'\<close>
  using refinement_sub_fun sep_refinement_stepwise
  by metis

lemma refinement_projections_stepwise:
  \<open>refinement_projection (I1 \<Zcomp>\<^sub>\<I> I2) D \<subseteq> refinement_projection I1 (refinement_projection I2 D)\<close>
  for I1 :: \<open>('c::sep_monoid, 'a::sep_magma_1) interp\<close>
  unfolding refinement_projection_def
  apply (clarsimp simp add: Bex_def set_eq_iff set_mult_expn)
  subgoal for x x' u v
    by (metis mult_1_class.mult_1_left sep_magma_1_right) .

subsubsection \<open>Function, pointwise\<close>

definition "\<F>_fun' I = Interp (\<lambda>f. prod (\<lambda>x. \<I> (I x) (f x)) (dom1 f))"

lemma \<F>_fun'_\<I>[simp]: "\<I> (\<F>_fun' I) = (\<lambda>f. prod (\<lambda>x. \<I> (I x) (f x)) (dom1 f))"
  unfolding \<F>_fun'_def by (rule Interp_inverse) (simp add: Interpretation_def)

lemma \<F>_fun'_split:
  " finite (dom1 f)
\<Longrightarrow> \<I> (\<F>_fun' I) f = \<I> (\<F>_fun' I) (f(k:=1)) * \<I> (I k) (f k)
   \<and> \<I> (\<F>_fun' I) (f(k:=1)) ## \<I> (I k) (f k)"
  for f :: "'a \<Rightarrow> 'b::sep_algebra"
  by simp (smt (verit, best) Interp_one dom1_upd fun_upd_triv mult.comm_neutral mult.commute prod.insert_remove)


definition "\<F>_fun I = \<F>_fun' (\<lambda>_. I)"

lemma \<F>_fun_\<I>[simp]: "\<I> (\<F>_fun I) = (\<lambda>f. prod (\<I> I o f) (dom1 f))"
  unfolding \<F>_fun_def by simp

lemma \<F>_fun_split:
  " finite (dom1 f)
\<Longrightarrow> \<I> (\<F>_fun I) f = \<I> (\<F>_fun I) (f(k:=1)) * \<I> I (f k)
  \<and> \<I> (\<F>_fun I) (f(k:=1)) ## \<I> I (f k)"
  for f :: "'a \<Rightarrow> 'b::sep_algebra"
  unfolding \<F>_fun_def using \<F>_fun'_split .

lemma \<F>_interp_fun_\<I>_1_fupdt[simp]: "\<I> (\<F>_fun I) (1(k:=v)) = \<I> I v" by simp


definition "\<F>_pointwise I = Interp (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"

lemma \<F>_pointwise_\<I>[simp]:
  "\<I> (\<F>_pointwise I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"
  unfolding \<F>_pointwise_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fun_def fun_eq_iff)

lemma \<F>_pointwise_\<F>_it:
  \<open>\<F>_pointwise \<F>_it = \<F>_it\<close>
  by (rule interp_eq_I; simp add: fun_eq_iff set_eq_iff)

definition "\<F>_pointwise' I = Interp (\<lambda>f. {g. \<forall>x. g x \<in> \<I> (I x) (f x) })"

lemma \<F>_pointwise'_\<I>[simp]:
  "\<I> (\<F>_pointwise' I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> (I x) (f x) })"
  unfolding \<F>_pointwise'_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fun_def fun_eq_iff)

lemma \<F>_pointwise_projection:
  \<open> refinement_projection I D' \<subseteq> UNIV * D
\<Longrightarrow> refinement_projection (\<F>_pointwise I) (fun_upd 1 k ` D') \<subseteq> UNIV * fun_upd 1 k ` D\<close>
  for D :: \<open>'b::sep_monoid set\<close>
  apply (clarsimp simp add: subset_iff Bex_def image_iff set_mult_expn times_fun
            refinement_projection_def)
  subgoal premises prems for t u xb
  proof -
    have t1: \<open>u k ## xb\<close>
      by (metis fun_upd_same prems(3) sep_disj_fun)
    have \<open>(\<exists>x. (\<exists>xa. (\<exists>u v. xa = u * v \<and> v \<in> D' \<and> u ## v) \<and> x = \<I> I xa) \<and> t k \<in> x)\<close>
      by (metis prems(2) prems(4) t1)
    note prems(1)[THEN spec[where x=\<open>t k\<close>], THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for u' v'
        apply (rule exI[where x=\<open>t(k := u')\<close>], rule exI[where x=\<open>1(k := v')\<close>])
        by (simp add: fun_eq_iff prems2 sep_disj_fun_def times_fun) .
  qed .

lemma \<F>_pointwise_refinement:
  \<open> Id_on UNIV * A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> Id_on UNIV * pairself (fun_upd 1 k) ` A \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` B
    \<w>.\<r>.\<t> \<F>_pointwise I \<i>\<n> fun_upd 1 k ` D\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn Subjection_expn image_iff Image_def subset_iff Bex_def times_fun Id_on_iff)
  subgoal premises prems for r R u v xb xc a b
  proof -
    have t1[simp]: \<open>xc k ## a\<close>
      by (metis fun_upd_same prems(8) sep_disj_fun)
    have t2[simp]: \<open>xc k ## b\<close>
      by (metis fun_upd_same prems(9) sep_disj_fun)
    have \<open>(\<exists>x. (\<exists>ua v. x = ua * v \<and> ua \<in> {u k} \<and> v \<in> \<I> I (r k * xb) \<and> ua ## v) \<and>
     r k ## xb \<and>
     xb \<in> D \<and> (\<exists>a ba aa. x = a * aa \<and> (\<exists>bb. xc k * b = ba * bb \<and> a = ba \<and> (aa, bb) \<in> A \<and> a ## aa \<and> ba ## bb)))\<close>
      by (simp add: prems,
          smt (verit, del_insts) fun_upd_same prems(10) prems(2) prems(5) prems(6) prems(7) sep_disj_fun_def t1 t2 times_fun)
    note prems(1)[THEN spec[where x=xb], THEN spec[where x=\<open>r k\<close>], THEN spec[where x=\<open>{u k}\<close>, THEN spec[where x=\<open>xc k * b\<close>]],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y v'
      proof -
        have t4: \<open>u ## v(k := v')\<close>
          by (clarsimp simp add: sep_disj_fun_def prems2 prems(7)) (simp add: prems(7))
        have t3: \<open>xc * 1(k := b) = u * v(k := v')\<close>
          by (clarsimp simp add: fun_eq_iff times_fun prems2,
              metis (no_types, opaque_lifting) fun_upd_other mult_1_class.mult_1_right prems(5) times_fun_def)
        show ?thesis
          by (rule exI[where x=\<open>1(k := y)\<close>]; simp add: prems prems2; rule,
               smt (verit, ccfv_threshold) fun_split_1 fun_upd_other fun_upd_same prems(3) prems(6) prems2(4) t3 t4 times_fun,
               metis fun_sep_disj_1_fupdt(1) fun_upd_triv prems2(1) prems2(2))
      qed .
  qed .

subsubsection \<open>Pairwise\<close>

definition "\<F>_pair I1 I2 = Interp (\<lambda>(x,y). \<I> I1 x * \<I> I2 y) "

lemma \<F>_pair_\<I>[simp]: "\<I> (\<F>_pair I1 I2) = (\<lambda>(x,y). \<I> I1 x * \<I> I2 y)"
  for I1 :: "('a::one,'b::sep_monoid) interp"
  unfolding \<F>_pair_def
  by (rule Interp_inverse) (simp add: Interpretation_def one_prod_def)

notation \<F>_pair (infixl "\<bullet>\<^sub>\<F>" 50)


subsubsection \<open>Option\<close>

definition "\<F>_option I = Interp (case_option 1 I)"

lemma \<F>_option_\<I>[simp]: "\<I> (\<F>_option I) = (case_option 1 I)"
  unfolding \<F>_option_def
  by (rule Interp_inverse) (simp add: Interpretation_def)


definition "\<F>_optionwise I = Interp (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"

lemma \<F>_optionwise_\<I>[simp]:
  "\<I> (\<F>_optionwise I) = (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"
  unfolding \<F>_optionwise_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def)


(* subsubsection \<open>Partiality\<close>

definition "fine I = Interp (case_fine (\<I> I) {})"
lemma fine_\<I>[simp]: "\<I> (fine I) = case_fine (\<I> I) {}"
  unfolding fine_def by (rule Interp_inverse) (simp add: Interpretation_def one_fine_def)

definition "defined I = Interp (\<lambda>x. Fine ` \<I> I x)"
lemma defined_\<I>[simp]: "\<I> (defined I) = (\<lambda>x. Fine ` \<I> I x)"
  unfolding defined_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fine_def)

definition "partialwise I = \<F>_fine (defined I)"
lemma partialwise_\<I>[simp]: "\<I> (partialwise I) (Fine x) = { Fine y |y. y \<in> \<I> I x }"
  unfolding partialwise_def by auto
*)

subsubsection \<open>Functional Fiction\<close>

definition \<open>\<F>_functional \<psi> D = Interp (\<lambda>x. {y. x = \<psi> y \<and> y \<in> D })\<close>

(* lemma (in kernel_is_1) \<F>_functional_\<I>[simp]:
  \<open>\<I> (\<F>_functional \<psi>) = (\<lambda>x. {y. x = \<psi> y})\<close>
  unfolding \<F>_functional_def
  by (rule Interp_inverse, simp add: Interpretation_def one_set_def set_eq_iff inj_at_1) *)

lemma \<F>_functional_\<I>[simp]:
  \<open> kernel_is_1 \<psi> D
\<Longrightarrow> \<I> (\<F>_functional \<psi> D) = (\<lambda>x. {y. x = \<psi> y \<and> y \<in> D })\<close>
  unfolding \<F>_functional_def kernel_is_1_def
  by (rule Interp_inverse, auto simp add: Interpretation_def one_set_def set_eq_iff Ball_def)

lemma map_option_inj_at_1[simp]:
  \<open>kernel_is_1 (map_option f) UNIV\<close>
  unfolding one_option_def kernel_is_1_def
  by (simp add: split_option_all)

lemma (in sep_orthogonal_monoid) \<F>_functional_projection [simp]:
  \<open> S \<subseteq> D
\<Longrightarrow> refinement_projection (\<F>_functional \<psi> D) (\<psi> ` S) \<subseteq> UNIV * S\<close>
  unfolding refinement_projection_def
  by (clarsimp simp add: subset_iff set_mult_expn eq_commute[where a=\<open>\<psi> _\<close>] sep_orthogonal; blast)

lemma kernel_is_1_pointwise[simp,intro!]:
  \<open>kernel_is_1 \<psi> D \<Longrightarrow> kernel_is_1 ((\<circ>) \<psi>) (pointwise_set D)\<close>
  unfolding kernel_is_1_def pointwise_set_def by (simp add: fun_eq_iff)

lemma \<F>_functional_pointwise:
  \<open> kernel_is_1 \<psi> D
\<Longrightarrow> \<F>_functional ((\<circ>) \<psi>) (pointwise_set D) = \<F>_pointwise (\<F>_functional \<psi> D)\<close>
  by (rule interp_eq_I; auto simp add: fun_eq_iff set_eq_iff; simp add: pointwise_set_def)

lemma \<F>_functional_comp:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> kernel_is_1 f Df
\<Longrightarrow> kernel_is_1 g Dg
\<Longrightarrow> \<F>_functional (f o g) Dg = \<F>_functional g Dg ;\<^sub>\<I> \<F>_functional f Df\<close>
  by (auto simp add: fun_eq_iff set_eq_iff; blast)
  

definition "\<F>_share s = (case s of Share w v \<Rightarrow> if w = 1 then {v} else {})"

lemma \<F>_share_\<I>[simp]: "\<F>_share (Share w v) = (if w = 1 then {v} else {})"
  unfolding \<F>_share_def by simp

(* lemma In_ficion_fine [simp]:
  \<open>x \<in> (case some_fine of Fine y \<Rightarrow> f y | Undef \<Rightarrow> {})
        \<longleftrightarrow> (\<exists>y. some_fine = Fine y \<and> x \<in> f y)\<close>
  by (cases some_fine; simp)
*)

subsubsection \<open>Agreement\<close>

definition \<open>\<F>_agree = (\<lambda>x. case x of agree x' \<Rightarrow> {x'})\<close>


subsection \<open>Refinement of Algebraic Structures\<close>

subsubsection \<open>Cancellative Separation Insertion Homomorphism\<close>

(*
lemma refinement_projection:
  \<open> kernel_is_1 \<psi>
\<Longrightarrow> Id_on UNIV * {(a, b)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` {(a,b)} \<w>.\<r>.\<t> \<F>_functional \<psi> \<i>\<n> \<psi> ` {a}\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn Subjection_expn)
subgoal for r R u v w *)

context cancl_sep_orthogonal_monoid begin

lemma \<F>_functional_refinement:
  \<open> a \<in> D \<and> b \<in> D
\<Longrightarrow> (\<forall>r x y. r ## x \<and> r \<in> D \<and> x \<in> D \<and> r * x \<in> D \<and> y \<in> D \<longrightarrow> r * y \<in> D)
\<Longrightarrow> kernel_is_1 \<psi> D
\<Longrightarrow> Id_on UNIV * {(a, b)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` {(a,b)} \<w>.\<r>.\<t> \<F>_functional \<psi> D \<i>\<n> \<psi> ` {a} \<close>
  unfolding Fictional_Forward_Simulation_def
  apply (auto simp add: set_mult_expn Subjection_expn sep_orthogonal)
  apply (metis (no_types, lifting) homo_mult sep_cancel sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)
  by (metis sep_cancel sep_disj_homo_semi sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_mult_assoc')

end

subsubsection \<open>Cancellative Permission Insertion Homomorphism\<close>


context cancl_share_orthogonal_homo begin

lemma refinement_projection_half_perm:
  \<open>S \<subseteq> D \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow> refinement_projection (\<F>_functional \<psi> D) ((share n o \<psi>) ` S) \<subseteq> UNIV * S\<close>
  unfolding refinement_projection_def
  by (auto simp add: set_mult_expn sep_orthogonal share_orthogonal',
      insert share_orthogonal_homo.share_orthogonal' share_orthogonal_homo_axioms, blast)


end



end