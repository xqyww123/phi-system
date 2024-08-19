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

definition BI_Image :: \<open>('a \<times> 'b) BI \<Rightarrow> 'a BI \<Rightarrow> 'b BI\<close>  (infixr "``\<^sub>I" 90)
  where "r ``\<^sub>I s = BI (BI.dest r `` BI.dest s)"

lemma BI_Image_expn[iff]:
  \<open> w \<Turnstile> r ``\<^sub>I s \<longleftrightarrow> (\<exists>w'. (w',w) \<Turnstile> r \<and> w' \<Turnstile> s) \<close>
  unfolding BI_Image_def
  by (meson ImageE Satisfaction_BI_red Satisfaction_def rev_ImageI)

definition BI_Id_on :: "'a BI \<Rightarrow> ('a \<times> 'a) BI"
  where "BI_Id_on A = BI (Id_on (BI.dest A))"

lemma BI_Id_on_expn[iff]:
  \<open> (a,b) \<Turnstile> BI_Id_on A \<longleftrightarrow> a = b \<and> a \<Turnstile> A \<close>
  unfolding BI_Id_on_def
  by (cases A; auto)

definition i_relcomp :: \<open>('a \<times> 'b) BI \<Rightarrow> ('b \<times> 'c) BI \<Rightarrow> ('a \<times> 'c) BI\<close> (infixr "O\<^sub>I" 75)
  where \<open> A O\<^sub>I B = BI (BI.dest A O BI.dest B) \<close>

lemma i_relcomp_expn[iff]:
  \<open> (a,c) \<Turnstile> R O\<^sub>I S \<longleftrightarrow> (\<exists>b. (a,b) \<Turnstile> R \<and> (b,c) \<Turnstile> S) \<close>
  unfolding i_relcomp_def
  by (cases R; cases S; simp; blast)

definition BI_Monad_Comb :: \<open>'a BI BI \<Rightarrow> 'a BI\<close>
  where \<open>BI_Monad_Comb S = Sup (BI.dest S)\<close>

lemma BI_Monad_Comb_expn[iff]:
  \<open> w \<Turnstile> BI_Monad_Comb S \<longleftrightarrow> (\<exists>m. m \<Turnstile> S \<and> w \<Turnstile> m) \<close>
  unfolding BI_Monad_Comb_def
  by (cases S; auto)


subsubsection \<open>Fictional Interpretation\<close>

text \<open>
  Referring to Fictional Separation Logic~\cite{FSL}, the interpretation of fictional separation
  maps a fictional resource to a set of concrete resource.
  The interpretation can be any map to set that preserves \<open>1\<close>, the unit of the separation algebra.\<close>

type_synonym 'a BI_rel = \<open>('a \<times> 'a) BI\<close>
type_synonym 'a spec = \<open>'a BI\<close>
type_synonym ('a,'b) unital_homo_interp = \<open>('a, 'b spec) unital_homo\<close>

(*
definition \<I>\<^sub>r\<^sub>e\<^sub>l :: \<open>('a::one,'b::one) interp \<Rightarrow> ('a \<times> 'b) set\<close> 
  where \<open>\<I>\<^sub>r\<^sub>e\<^sub>l I = {(x,y). y \<in> \<I> I x}\<close> *)


subsubsection \<open>Fictional Refinement\<close>

definition Fictional_Forward_Simulation :: \<open>'c BI_rel \<Rightarrow> 'a BI_rel \<Rightarrow> ('c::sep_magma, 'a::sep_magma) \<phi> \<Rightarrow> 'a BI \<Rightarrow> bool\<close>
      ("_/ \<r>\<e>\<f>\<i>\<n>\<e>\<s> _/ \<w>.\<r>.\<t> _/ \<i>\<n> _" [11,11,11] 10)
  where \<open>(F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T \<i>\<n> D)
    \<longleftrightarrow> (\<forall>x r R. F ``\<^sub>I (T (x * r) * R \<s>\<u>\<b>\<j> x ## r \<and> x \<Turnstile> D) \<le> BI { y'. \<exists>y. y' \<Turnstile> T (y * r) * R \<and> y ## r \<and> (x,y) \<Turnstile> G})\<close>

text \<open>We use relation directly here but doesn't mean we cannot model return value or threw exceptions.
They can parameterize the relation, as we don't need to (it is not designed to) abstract the values.
We only relate resources in different abstractions.

\<^prop>\<open>\<And>ret. F ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> G ret \<w>.\<r>.\<t> T \<i>\<n> D\<close>
\<close>

lemma empty_refines_any[simp]:
  \<open>0 \<r>\<e>\<f>\<i>\<n>\<e>\<s> Any \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def less_eq_BI_iff
  by simp

lemma refinement_sub_domain:
  \<open> D' \<le> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D'\<close>
  unfolding Fictional_Forward_Simulation_def less_eq_BI_iff
  by (clarsimp simp add: subset_iff Image_def Bex_def Id_on_iff, blast)

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
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B * BI_Id_on R \<w>.\<r>.\<t> I \<i>\<n> D * R\<close>
  for B :: \<open>'b::sep_semigroup BI_rel\<close>
  unfolding Fictional_Forward_Simulation_def less_eq_BI_iff
  by (clarsimp simp add: subset_iff set_mult_expn Image_def Bex_def Id_on_iff,
      smt (z3) sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc')

lemma sep_refinement_horizontal_stepwise:
  \<open> A1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B2 \<w>.\<r>.\<t> I \<i>\<n> D'
\<Longrightarrow> (B1 ``\<^sub>I D \<le> D')
\<Longrightarrow> A1 O\<^sub>I A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 O\<^sub>I B2 \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: less_eq_BI_iff Bex_def)
  subgoal premises prems for x r R z y u v
  proof -
    have \<open>\<exists>w'. (w', y) \<Turnstile> A1 \<and> (\<exists>u v. w' = u * v \<and> u \<Turnstile> I (x * r) \<and> v \<Turnstile> R \<and> u ## v) \<and> x ## r \<and> x \<Turnstile> D\<close>
      using prems(10) prems(4) prems(6) prems(7) prems(8) prems(9) by blast
    note prems(1)[THEN spec[where x=x], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=y],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y' u' v'
      proof -
        have \<open>\<exists>w'. (w', z) \<Turnstile> A2 \<and> (\<exists>u v. w' = u * v \<and> u \<Turnstile> I (y' * r) \<and> v \<Turnstile> R \<and> u ## v) \<and> y' ## r \<and> y' \<Turnstile> D'\<close>
          using prems(3) prems(5) prems(7) prems2(1) prems2(2) prems2(3) prems2(4) prems2(5) prems2(6) by blast
        note prems(2)[THEN spec[where x=y'], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=z],
          THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(2) by blast
      qed .
  qed .

lemma constant_refinement:
  \<open>BI_Id_on A * BI_Id_on top \<r>\<e>\<f>\<i>\<n>\<e>\<s> BI_Id_on B \<w>.\<r>.\<t> I \<i>\<n> B\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff Id_on_iff set_mult_expn times_fun; blast)

lemma refinement_subjection:
  \<open> (P \<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D)
\<Longrightarrow> P \<longrightarrow> Q
\<Longrightarrow> A \<s>\<u>\<b>\<j> P \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<s>\<u>\<b>\<j> Q \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def 
  by (clarsimp simp add: less_eq_BI_iff Image_def Bex_def) blast

lemma refinement_existential:
  \<open> (\<And>x. A x \<r>\<e>\<f>\<i>\<n>\<e>\<s> B x \<w>.\<r>.\<t> I \<i>\<n> D)
\<Longrightarrow> ExBI A \<r>\<e>\<f>\<i>\<n>\<e>\<s> ExBI B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff Image_def Bex_def Id_on_iff; blast)

lemma refinement_source_subjection:
  \<open>(A \<s>\<u>\<b>\<j> P \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D) \<longleftrightarrow> (P \<longrightarrow> (A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D))\<close>
  unfolding Fictional_Forward_Simulation_def
  by (auto simp add: less_eq_BI_iff Image_def Bex_def Id_on_iff set_mult_expn; blast)

lemma refinement_ExBI:
  \<open> (\<And>v. A v \<r>\<e>\<f>\<i>\<n>\<e>\<s> B v \<w>.\<r>.\<t> I \<i>\<n> D)
\<Longrightarrow> ExBI A \<r>\<e>\<f>\<i>\<n>\<e>\<s> ExBI B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff Image_def Bex_def Id_on_iff, blast)



definition refinement_projection :: \<open>('abstract::sep_magma \<Rightarrow> 'concrete BI) \<Rightarrow> 'abstract spec \<Rightarrow> 'concrete spec\<close>
  where \<open>refinement_projection I D = BI_Monad_Comb (I `\<^sub>I (D * top))\<close>

lemma refinement_projection_mono:
  \<open> D \<le> D'
\<Longrightarrow> refinement_projection I D \<le> refinement_projection I D'\<close>
  unfolding refinement_projection_def
  by (clarsimp simp add: less_eq_BI_iff set_mult_expn Bex_def; blast)

lemma BI_top_times_idem:
  \<open>top * top = (top :: 'a::sep_magma_1 BI)\<close>
  unfolding BI_eq_iff
  by (clarsimp, metis mult_1_class.mult_1_right sep_magma_1_left)

lemma refinement_projection_UNIV_times_D[simp]:
  \<open> refinement_projection I (D * top) \<le> refinement_projection I D \<close>
  for D :: \<open>'a::sep_monoid BI\<close>
  unfolding refinement_projection_def mult.assoc BI_top_times_idem ..

subsection \<open>Instances\<close>

subsubsection \<open>Itself\<close>

lemma Itself_refinement_projection:
  \<open> S \<le> S'
\<Longrightarrow> refinement_projection Itself S \<le> S' * top\<close>
  unfolding refinement_projection_def
  by (clarsimp simp add: less_eq_BI_iff) blast

lemma Itself_refinement:
  \<open>((u,v) \<Ztypecolon> Itself) * BI_Id_on top \<r>\<e>\<f>\<i>\<n>\<e>\<s> (u,v) \<Ztypecolon> Itself \<w>.\<r>.\<t> Itself \<i>\<n> (u \<Ztypecolon> Itself)\<close>
  for u :: \<open>'a::{sep_cancel,sep_semigroup}\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: less_eq_BI_iff,
      metis sep_cancel sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)


subsubsection \<open>Composition\<close>

definition interp_comp :: \<open>('c::one,'b::one) \<phi> \<Rightarrow> ('b,'a::one) \<phi> \<Rightarrow> ('c,'a) \<phi>\<close> (infixr "\<Zcomp>\<^sub>\<I>" 55)
  where [simp]: \<open>(I1 \<Zcomp>\<^sub>\<I> I2) x = \<Union>(I1 ` I2 x)\<close>

lemma interp_comp_assoc:
  \<open>(I1 \<Zcomp>\<^sub>\<I> I2) \<Zcomp>\<^sub>\<I> I3 = I1 \<Zcomp>\<^sub>\<I> (I2 \<Zcomp>\<^sub>\<I> I3)\<close>
  by (simp add: fun_eq_iff)

lemma interp_comp_homo_one[simp]:
  \<open>homo_one Ia \<Longrightarrow> homo_one Ib \<Longrightarrow> homo_one (Ia \<Zcomp>\<^sub>\<I> Ib)\<close>
  unfolding homo_one_def by (simp add: set_eq_iff)

lemma Itself_comp[simp]:
  \<open>Itself \<Zcomp>\<^sub>\<I> I = I\<close> \<open>I \<Zcomp>\<^sub>\<I> Itself = I\<close>
  by (simp add: fun_eq_iff)+

lemma sep_refinement_stepwise:
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> Ia \<i>\<n> D
\<Longrightarrow> S2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> Ib \<i>\<n> D'
\<Longrightarrow> refinement_projection Ib D' \<subseteq> D
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (Ia \<Zcomp>\<^sub>\<I> Ib) \<i>\<n> D'\<close>
  for Ia :: \<open>'b::sep_magma_1 \<Rightarrow> 'a::sep_magma_1 set\<close>
  unfolding Fictional_Forward_Simulation_def refinement_projection_def
  apply (auto simp add: subset_iff Image_def Bex_def Subjection_expn_set set_mult_expn split_option_all)
  subgoal premises prems for x r R t u v xb
  proof -
    thm prems
    thm prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>]]
    have \<open>\<exists>x. (\<exists>u v. x = u * v \<and> u \<in> Ia (xb * 1) \<and> v \<in> R \<and> u ## v) \<and> xb ## 1 \<and> xb \<in> D \<and> (x, t) \<in> S1\<close>
      using prems(10) prems(3) prems(4) prems(5) prems(6) prems(7) prems(8) prems(9) by fastforce
    note prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y u'' v''
      proof -
        have \<open>(\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<in> Ib (x * r) \<and> v \<in> {1} \<and> u ## v) \<and> x ## r \<and> x \<in> D' \<and> (xa, y) \<in> S2)\<close>
          by (simp, rule exI[where x=xb], simp add: prems2 prems)
        note prems(2)[THEN spec[where x=x],THEN spec[where x=r],THEN spec[where x=\<open>{1}\<close>], THEN spec[where x=y],
                THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(3) prems2(4) prems2(5) by auto
      qed .
  qed .

lemma sep_refinement_stepwise':
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> Ia \<i>\<n> D
\<Longrightarrow> S2' \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> Ib \<i>\<n> D'
\<Longrightarrow> refinement_projection Ib D' \<subseteq> D
\<Longrightarrow> S2 \<subseteq> S2'
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (Ia \<Zcomp>\<^sub>\<I> Ib) \<i>\<n> D'\<close>
  for Ia :: \<open>'b::sep_magma_1 \<Rightarrow> 'a::sep_magma_1 set\<close>
  using refinement_sub_fun sep_refinement_stepwise
  by metis

lemma refinement_projections_stepwise:
  \<open>refinement_projection (Ia \<Zcomp>\<^sub>\<I> Ib) D \<subseteq> refinement_projection Ia (refinement_projection Ib D)\<close>
  for Ia :: \<open>('c::sep_monoid, 'a::sep_magma_1) interp\<close>
  unfolding refinement_projection_def
  apply (clarsimp simp add: Bex_def set_eq_iff set_mult_expn)
  subgoal for x x' u v
    by (metis mult_1_class.mult_1_right sep_magma_1_left) .

lemma refinement_projections_stepwise_UNIV_paired:
  \<open> refinement_projection Ia Da \<subseteq> Dc * UNIV
\<Longrightarrow> refinement_projection Ib Db \<subseteq> Da * UNIV
\<Longrightarrow> refinement_projection (Ia \<Zcomp>\<^sub>\<I> Ib) Db \<subseteq> Dc * UNIV \<close>
  for Ia :: \<open>('c::sep_monoid, 'a::sep_magma_1) interp\<close>
  using refinement_projections_stepwise
  by (metis (mono_tags, lifting) refinement_projection_UNIV_times_D refinement_projection_mono subset_trans)


subsubsection \<open>Function, pointwise\<close>

definition [simp]: "\<F>_finite_product I f = prod (\<lambda>x. I x (f x)) (dom1 f)"

lemma \<F>_finite_product_split:
  " finite (dom1 f)
\<Longrightarrow> (\<And>k. homo_one (I k))
\<Longrightarrow> \<F>_finite_product I f = I k (f k) * \<F>_finite_product I (f(k:=1))
   \<and> \<F>_finite_product I (f(k:=1)) ## I k (f k)"
  for I :: \<open>'a \<Rightarrow> 'b::sep_algebra \<Rightarrow> 'c::sep_algebra set\<close>
  by (simp add: homo_one_def,
      smt (verit, best) dom1_upd fun_upd_triv mult.comm_neutral mult.commute prod.insert_remove)


definition [simp]: "\<F>_FP_homo I f = prod (\<lambda>x. apply_unital_homo (I x) (f x)) (dom1 f)"

lemma \<F>_FP_homo_split:
  " finite (dom1 f)
\<Longrightarrow> \<F>_FP_homo I f = apply_unital_homo (I k) (f k) * \<F>_FP_homo I (f(k:=1))
   \<and> apply_unital_homo (I k) (f k) ## \<F>_FP_homo I (f(k:=1)) "
  for I :: \<open>'a \<Rightarrow> ('b::sep_algebra, 'c::sep_algebra set) unital_homo\<close>
  by (simp add: homo_one_def,
      smt (verit, ccfv_SIG) Diff_empty Diff_insert0 apply_unital_homo_1 dom1_def mem_Collect_eq mult.commute mult_1_class.mult_1_right prod.remove)

(*
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
*)
(*
definition "\<F>_pointwise I = Interp (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"

lemma \<F>_pointwise_\<I>[simp]:
  "\<I> (\<F>_pointwise I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"
  unfolding \<F>_pointwise_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fun_def fun_eq_iff)

lemma \<F>_pointwise_Itself:
  \<open>\<F>_pointwise Itself = Itself\<close>
  by (rule interp_eq_I; simp add: fun_eq_iff set_eq_iff) *)

definition [simp]: "\<F>_pointwise I f = {g. \<forall>x. g x \<in> (I x) (f x)}"

lemma \<F>_pointwise_homo_one[simp, locale_intro]:
  \<open> (\<And>k. homo_one (I k))
\<Longrightarrow> homo_one (\<F>_pointwise I)\<close>
  unfolding homo_one_def by (simp add: set_eq_iff) fastforce

lemma \<F>_pointwise_Itself:
  \<open>\<F>_pointwise (\<lambda>_. Itself) = Itself\<close>
  by (simp add: fun_eq_iff set_eq_iff)

lemma \<F>_pointwise_projection:
  \<open> refinement_projection (I k) D' \<subseteq> D * UNIV
\<Longrightarrow> refinement_projection (\<F>_pointwise I) (fun_upd 1 k ` D') \<subseteq> fun_upd 1 k ` D * UNIV\<close>
  for D :: \<open>'b::sep_monoid set\<close>
  apply (clarsimp simp add: subset_iff Bex_def image_iff set_mult_expn times_fun
            refinement_projection_def)
  subgoal premises prems for t u xb
  proof -
    have t1: \<open>xb ## u k\<close>
      by (metis fun_upd_same prems(3) sep_disj_fun)
    have \<open>(\<exists>x. (\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<in> D' \<and> u ## v) \<and> x = I k xa) \<and> t k \<in> x)\<close>
      by (metis prems(2) prems(4) t1)
    note prems(1)[THEN spec[where x=\<open>t k\<close>], THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for u' v'
        by (rule exI[where x=\<open>1(k := u')\<close>], rule exI[where x=\<open>t(k := v')\<close>],
            simp add: fun_eq_iff prems2 sep_disj_fun_def times_fun) .
  qed .

lemma \<F>_pointwise_refinement:
  \<open> A * Id_on UNIV \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I k \<i>\<n> D
\<Longrightarrow> pairself (fun_upd 1 k) ` A * Id_on UNIV \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` B
    \<w>.\<r>.\<t> \<F>_pointwise I \<i>\<n> fun_upd 1 k ` D\<close>
  for I :: \<open>'c \<Rightarrow> 'b::sep_magma_1 \<Rightarrow> 'a::sep_magma_1 set\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn Subjection_expn_set image_iff Image_def subset_iff Bex_def times_fun Id_on_iff)
  subgoal premises prems for r R u v xb xc a b
  proof -
    have t1[simp]: \<open>a ## xc k\<close>
      by (metis fun_upd_same prems(8) sep_disj_fun)
    have t2[simp]: \<open>b ## xc k\<close>
      by (metis fun_upd_same prems(9) sep_disj_fun)
    have \<open>\<exists>x. (\<exists>u va. x = u * va \<and> u \<in> I k (xb * r k) \<and> va \<in> {v k} \<and> u ## va) \<and>
      xb ## r k \<and> xb \<in> D \<and> (\<exists>a ba aa. x = a * aa \<and> b * xc k = ba * aa \<and> (a, ba) \<in> A \<and> a ## aa \<and> ba ## aa)\<close>
      by (auto simp add: prems,
          smt (verit, ccfv_threshold) fun_upd_same prems(10) prems(2) prems(3) prems(5) prems(7) sep_disj_fun_def t1 t2 times_fun_def)
    note prems(1)[THEN spec[where x=xb], THEN spec[where x=\<open>r k\<close>], THEN spec[where x=\<open>{v k}\<close>, THEN spec[where x=\<open>b * xc k\<close>]],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y v'
      proof -
        have t4: \<open>u(k := v') ## v\<close>
          by (clarsimp simp add: sep_disj_fun_def prems2 prems(7)) (simp add: prems(7))
        have t3: \<open>1(k := b) * xc = u(k := v') * v\<close>
          by (clarsimp simp add: fun_eq_iff times_fun prems2,
              metis (mono_tags, lifting) fun_upd_apply mult_1_class.mult_1_left prems(5) times_fun_def)
        show ?thesis
          by (rule exI[where x=\<open>1(k := y)\<close>]; simp add: prems prems2; rule,
              smt (verit) fun_upd_apply mult_1_class.mult_1_left one_fun_def prems(3) prems(6) prems2(4) t3 t4,
              metis fun_sep_disj_1_fupdt(2) fun_upd_triv prems2(1) prems2(2))
      qed .
  qed .

(* subsubsection \<open>Pairwise\<close>

definition "\<F>_pair I1 I2 = (\<lambda>(x,y). I1 x * I2 y) "

lemma \<F>_pair[simp]: "\<F>_pair I1 I2 (x,y) = I1 x * I2 y"
  for I1 :: "('a::one,'b::sep_monoid) interp"
  unfolding \<F>_pair_def by (simp add: one_prod_def)

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
*)

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

definition [simp]: \<open>\<F>_functional \<psi> D x = {y. x = \<psi> y \<and> y \<in> D }\<close>

(* lemma (in kernel_is_1) \<F>_functional_\<I>[simp]:
  \<open>\<I> (\<F>_functional \<psi>) = (\<lambda>x. {y. x = \<psi> y})\<close>
  unfolding \<F>_functional_def
  by (rule Interp_inverse, simp add: Interpretation_def one_set_def set_eq_iff inj_at_1) *)

lemma \<F>_functional_homo_one[simp, locale_intro]:
  \<open> simple_homo_mul \<psi> D
\<Longrightarrow> homo_one (\<F>_functional \<psi> D)\<close>
  unfolding homo_one_def \<F>_functional_def simple_homo_mul_def
  by (clarsimp simp add: set_eq_iff Ball_def; blast)

(*TODO: move this or remove this*)
lemma map_option_inj_at_1[simp]:
  \<open>simple_homo_mul (map_option f) UNIV\<close>
  unfolding one_option_def simple_homo_mul_def
  by (simp add: split_option_all)

lemma (in sep_orthogonal_monoid) \<F>_functional_projection:
  \<open> S \<subseteq> D
\<Longrightarrow> refinement_projection (\<F>_functional \<psi> D) (\<psi> ` S) \<subseteq> S * UNIV\<close>
  unfolding refinement_projection_def
  by (clarsimp simp add: subset_iff set_mult_expn eq_commute[where a=\<open>\<psi> _\<close>] sep_orthogonal; blast)

lemma \<F>_functional_pointwise:
  \<open>\<F>_functional ((\<circ>) \<psi>) (pointwise_set D) = \<F>_pointwise (\<lambda>_. \<F>_functional \<psi> D)\<close>
  by (auto simp add: fun_eq_iff set_eq_iff; simp add: pointwise_set_def)

lemma \<F>_functional_comp:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> \<F>_functional (f o g) Dg = \<F>_functional g Dg \<Zcomp>\<^sub>\<I> \<F>_functional f Df\<close>
  by (auto simp add: fun_eq_iff set_eq_iff; blast)
  

(* definition "\<F>_share s = (case s of Share w v \<Rightarrow> if w = 1 then {v} else {})"

lemma \<F>_share_\<I>[simp]: "\<F>_share (Share w v) = (if w = 1 then {v} else {})"
  unfolding \<F>_share_def by simp *)

(* lemma In_ficion_fine [simp]:
  \<open>x \<in> (case some_fine of Fine y \<Rightarrow> f y | Undef \<Rightarrow> {})
        \<longleftrightarrow> (\<exists>y. some_fine = Fine y \<and> x \<in> f y)\<close>
  by (cases some_fine; simp)
*)

subsubsection \<open>Agreement\<close>

(* TODO: check this!!!!
definition \<open>\<F>_agree = (\<lambda>x. case x of agree x' \<Rightarrow> {x'})\<close> *)


subsection \<open>Refinement of Algebraic Structures\<close>

subsubsection \<open>Cancellative Separation Insertion Homomorphism\<close>

(*
lemma refinement_projection:
  \<open> kernel_is_1 \<psi>
\<Longrightarrow> Id_on UNIV * {(a, b)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` {(a,b)} \<w>.\<r>.\<t> \<F>_functional \<psi> \<i>\<n> \<psi> ` {a}\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn Subjection_expn_set)
subgoal for r R u v w *)

definition \<F>_functional_condition
  where \<open>\<F>_functional_condition D \<longleftrightarrow> (\<forall>r x y. x ## r \<and> y ## r \<and> r \<in> D \<and> x \<in> D \<and> x * r \<in> D \<and> y \<in> D \<longrightarrow> y * r \<in> D)\<close>

lemma \<F>_functional_condition_UNIV[simp]:
  \<open>\<F>_functional_condition UNIV\<close>
  unfolding \<F>_functional_condition_def by simp

definition frame_preserving_relation \<comment> \<open>TODO: REALLY UGLY!\<close>
  where \<open>frame_preserving_relation R
    \<longleftrightarrow> (\<forall>a b c d r w. (a,b) \<in> R \<and> (c,d) \<in> R \<and> a * r = c * w \<and> a ## r \<and> b ## r \<and> c ## w
            \<longrightarrow> b * r = d * w \<and> d ## w)\<close>

context cancl_sep_orthogonal_monoid begin

lemma \<F>_functional_refinement_complex:
  \<open> (\<forall>a b. (a,b) \<in> R \<longrightarrow> a \<in> D \<and> b \<in> D)
\<Longrightarrow> frame_preserving_relation R
\<Longrightarrow> Sep_Closed D
\<Longrightarrow> R * Id_on UNIV \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` R \<w>.\<r>.\<t> \<F>_functional \<psi> D \<i>\<n> \<psi> ` (Domain R) \<close>
  unfolding Fictional_Forward_Simulation_def
  apply (auto simp add: set_mult_expn Subjection_expn_set sep_orthogonal Sep_Closed_def image_iff Bex_def)
  by (smt (z3) frame_preserving_relation_def homo_mult sep_disj_homo_semi sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)

lemma \<F>_functional_refinement:
  \<open> a \<in> D \<and> b \<in> D
\<Longrightarrow> \<F>_functional_condition D
\<Longrightarrow> {(a, b)} * Id_on UNIV \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself \<psi> ` {(a,b)} \<w>.\<r>.\<t> \<F>_functional \<psi> D \<i>\<n> \<psi> ` {a} \<close>
  unfolding Fictional_Forward_Simulation_def \<F>_functional_condition_def
  apply (auto simp add: set_mult_expn Subjection_expn_set sep_orthogonal)
  apply (metis (no_types, lifting) homo_mult sep_cancel sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)
  by (metis sep_cancel sep_disj_homo_semi sep_disj_multD1 sep_disj_multD2 sep_disj_multI2 sep_mult_assoc)

end

subsubsection \<open>Cancellative Permission Insertion Homomorphism\<close>


context cancl_share_orthogonal_homo begin

lemma refinement_projection_half_perm:
  \<open>S \<subseteq> D \<Longrightarrow> 0 < n \<Longrightarrow> refinement_projection (\<F>_functional \<psi> D) ((share n o \<psi>) ` S) \<subseteq> S * UNIV\<close>
  unfolding refinement_projection_def
  by (auto simp add: set_mult_expn sep_orthogonal share_orthogonal';
      cases \<open>n \<le> 1\<close>,
      ((insert share_orthogonal_homo.share_orthogonal' share_orthogonal_homo_axioms, blast)[1],
       metis in_mono leI sep_orthogonal share_bounded share_right_one))


end



end