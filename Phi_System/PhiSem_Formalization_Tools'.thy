theory PhiSem_Formalization_Tools2
  imports IDE_CP
begin

section \<open>Tools for Formalizing Instructions\<close>

named_theorems discharging_semantic_debt
  \<open>Theorems that discharges or helps to discharge the debt axioms for semantic formalization.\<close>

subsection \<open>Elementary Constructions for Formalizing Instructions\<close>

definition \<phi>M_assert :: \<open>bool \<Rightarrow> unit proc\<close>
  where \<open>\<phi>M_assert P = (\<lambda>s. if P then Return \<phi>V_none s else {Invalid})\<close>

definition \<phi>M_assume :: \<open>bool \<Rightarrow> unit proc\<close>
  where \<open>\<phi>M_assume P = (\<lambda>s. if P then Return \<phi>V_none s else {AssumptionBroken})\<close>

definition \<phi>M_getV_raw :: \<open>(VAL \<Rightarrow> 'v) \<Rightarrow> VAL \<phi>arg \<Rightarrow> ('v \<Rightarrow> 'y proc) \<Rightarrow> 'y proc\<close>
  where \<open>\<phi>M_getV_raw VDT_dest v F = F (VDT_dest (\<phi>arg.dest v))\<close>

definition \<phi>M_getV :: \<open>TY \<Rightarrow> (VAL \<Rightarrow> 'v) \<Rightarrow> VAL \<phi>arg \<Rightarrow> ('v \<Rightarrow> 'y proc) \<Rightarrow> 'y proc\<close>
  where \<open>\<phi>M_getV TY VDT_dest v F =
    (\<phi>M_assert (\<phi>arg.dest v \<in> Well_Type TY) \<ggreater> F (VDT_dest (\<phi>arg.dest v)))\<close>

definition \<phi>M_caseV :: \<open>(VAL \<phi>arg \<Rightarrow> ('vr,'ret) proc') \<Rightarrow> (VAL \<times> 'vr::FIX_ARITY_VALs,'ret) proc'\<close>
  where \<open>\<phi>M_caseV F = (\<lambda>arg. case arg of \<phi>arg (a1,a2) \<Rightarrow> F (\<phi>arg a1) (\<phi>arg a2))\<close>


lemma Valid_Proc_\<phi>M_assert[intro!, \<phi>reason 1200]:
  \<open>Valid_Proc (\<phi>M_assert P)\<close>
  unfolding Valid_Proc_def \<phi>M_assert_def Return_def det_lift_def
  by clarsimp

lemma Valid_Proc_\<phi>M_assume[intro!, \<phi>reason 1200]:
  \<open>Valid_Proc (\<phi>M_assume P)\<close>
  unfolding Valid_Proc_def \<phi>M_assume_def Return_def det_lift_def
  by clarsimp

lemma Valid_Proc_\<phi>M_getV_raw[intro!, \<phi>reason 1200]:
  \<open> (\<And>v. Valid_Proc (F v))
\<Longrightarrow> Valid_Proc (\<phi>M_getV_raw VDF v F)\<close>
  unfolding Valid_Proc_def \<phi>M_getV_raw_def
  by blast


subsection \<open>Reasoning for Elementary Constructions\<close>

declare \<phi>SEQ[intro!]

lemma \<phi>M_assert[intro!]:
  \<open>(Inhabited X \<Longrightarrow> P) \<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_assert P \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>M_assert_def
  by (rule \<phi>Inhabited; simp; rule)

lemma \<phi>M_assert_True[simp]:
  \<open>\<phi>M_assert True = Return \<phi>V_none\<close>
  unfolding \<phi>M_assert_def by simp

lemma \<phi>M_assert':
  \<open>P \<Longrightarrow> Q (F args) \<Longrightarrow> Q ((\<phi>M_assert P \<ggreater> F) args)\<close>
  unfolding \<phi>M_assert_def bind_def Return_def det_lift_def by simp

lemma \<phi>M_assume[intro!]:
  \<open>(P \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E) \<Longrightarrow> \<p>\<r>\<o>\<c> (\<phi>M_assume P \<ggreater> F) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>Procedure_def \<phi>M_assume_def bind_def Return_def det_lift_def
  by clarsimp

lemma \<phi>M_assume1[intro!]:
  \<open>\<p>\<r>\<o>\<c> (\<phi>M_assume P) \<lbrace> Void \<longmapsto> Void \<s>\<u>\<b>\<j> P \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>M_assume_def \<phi>Procedure_def bind_def Return_def det_lift_def
  by clarsimp

lemma \<phi>M_tail_left:  \<open>\<p>\<r>\<o>\<c> F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_tail_right: \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> \<lambda>v. 1 \<heavy_comma> Y v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_tail_right_right: \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> \<lambda>v. Y v\<heavy_comma> 1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_shrink_left:  \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_shrink_right[intro!]: \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> \<lambda>v. 1\<heavy_comma> Y v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp

lemma \<phi>M_getV_raw[intro!]:
   \<open>(v \<in> (x \<Ztypecolon> A) \<Longrightarrow> \<p>\<r>\<o>\<c> F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  )
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_getV_raw VDT_dest (\<phi>arg v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (\<phi>arg v) A \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>M_getV_raw_def Premise_def
  by (clarsimp simp add: \<phi>expns norm_precond_conj)

declare \<phi>M_getV_raw[where X=1, simplified, intro!]

lemma \<phi>M_getV[intro!]:
   \<open>(v \<in> (x \<Ztypecolon> A) \<Longrightarrow> <\<phi>expn> v \<in> Well_Type TY)
\<Longrightarrow> (v \<in> (x \<Ztypecolon> A) \<Longrightarrow> \<p>\<r>\<o>\<c> F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  )
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_getV TY VDT_dest (\<phi>arg v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (\<phi>arg v) A \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>M_getV_def Premise_def
  by (clarsimp simp add: \<phi>expns norm_precond_conj)

declare \<phi>M_getV[where X=1, simplified, intro!]

lemma \<phi>M_caseV[intro!]:
  \<open> \<p>\<r>\<o>\<c> F va vb \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_caseV F (\<phi>V_pair va vb) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>M_caseV_def \<phi>V_pair_def by simp


subsection \<open>Elementary Constructions for Reasoning Fictions\<close>

text \<open>It is a Hybrid Dynamic Logic\<close>

definition \<phi>Res_Spec :: \<open>rassn \<Rightarrow> rassn\<close>
  where \<open>\<phi>Res_Spec S = RES.SPACE \<inter> S\<close>

definition \<phi>Res_Sat  :: \<open>resource \<Rightarrow> rassn \<Rightarrow> bool\<close>
  where \<open>\<phi>Res_Sat s P \<longleftrightarrow> s \<in> P\<close>

abbreviation \<phi>Res_Sat'  :: \<open>resource \<Rightarrow> rassn \<Rightarrow> bool\<close> ("\<s>\<t>\<a>\<t>\<e> _ \<i>\<s> _" [11,11] 10)
  where \<open>\<phi>Res_Sat' s P \<equiv> \<phi>Res_Sat s (\<phi>Res_Spec P)\<close>

definition \<phi>Comp_Sat :: \<open>'ret comp set \<Rightarrow> ('ret \<phi>arg \<Rightarrow> rassn) \<Rightarrow> (ABNM \<Rightarrow> rassn) \<Rightarrow> bool\<close>
  where \<open>\<phi>Comp_Sat c S E \<longleftrightarrow> c \<subseteq> \<S> S E\<close>

abbreviation \<phi>Comp_Sat' :: \<open>'ret comp set \<Rightarrow> ('ret \<phi>arg \<Rightarrow> rassn) \<Rightarrow> (ABNM \<Rightarrow> rassn) \<Rightarrow> bool\<close>
                          ("_ \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> _ \<t>\<h>\<r>\<o>\<w>\<s> _" [11,11,11] 10)
  where \<open>\<phi>Comp_Sat' c S E \<equiv> \<phi>Comp_Sat c (\<lambda>r. \<phi>Res_Spec (S r)) (\<lambda>e. \<phi>Res_Spec (E e))\<close>

lemma \<phi>Comp_Sat_success[simp]:
  \<open> ({Success ret res} \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E)
\<longleftrightarrow> (\<s>\<t>\<a>\<t>\<e> res \<i>\<s> Y ret)\<close>
  unfolding \<phi>Comp_Sat_def \<phi>Res_Sat_def by simp

lemma \<phi>Res_Sat_0[iff]:
  \<open>\<not> (\<s>\<t>\<a>\<t>\<e> x \<i>\<s> {})\<close> \<open>\<not> (\<s>\<t>\<a>\<t>\<e> x \<i>\<s> 0)\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def by (simp add: zero_set_def)+

(*lemma \<phi>Res_Sat_0[iff]:
  \<open>(\<s>\<t>\<a>\<t>\<e> x \<i>\<s> {})\<close> \<open>\<not> (\<s>\<t>\<a>\<t>\<e> x \<i>\<s> 0)\<close>
  unfolding \<phi>Res_Sat_def by (simp add: zero_set_def)+

lemma \<phi>Res_Spec_1[iff]:
  \<open>\<phi>Res_Spec 1 = 1\<close>
  unfolding \<phi>Res_Spec_def by (simp add: set_eq_iff; blast) *)

(*lemma \<phi>Res_Spec_mult_homo:
  \<open>\<phi>Res_Spec (A * B) = \<phi>Res_Spec A * \<phi>Res_Spec B\<close>
  unfolding \<phi>Res_Spec_def
  by (clarsimp simp add: set_eq_iff times_set_def; rule; clarsimp simp add: RES.SPACE_mult_homo; blast) *)

lemma \<phi>Res_Sat_subj[iff]:
  \<open>(\<s>\<t>\<a>\<t>\<e> s \<i>\<s> S \<s>\<u>\<b>\<j> P) \<longleftrightarrow> (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> S) \<and> P\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Comp_Sat_subj:
  \<open> P
\<Longrightarrow> c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>v. S v \<s>\<u>\<b>\<j> P) \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  by (clarsimp simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Sat_ex[iff]:
  \<open>(\<s>\<t>\<a>\<t>\<e> s \<i>\<s> ExSet S) \<longleftrightarrow> (\<exists>x. \<s>\<t>\<a>\<t>\<e> s \<i>\<s> S x)\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Sat_ex_ret:
  \<open> c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S x \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>v. \<exists>*x. S x v) \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>Comp_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<phi>expns set_eq_iff subset_iff)
  subgoal for x by (cases x; clarsimp simp add: \<phi>expns set_eq_iff subset_iff; blast) .

lemma \<phi>Res_Sat_ex_abn:
  \<open> c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S \<t>\<h>\<r>\<o>\<w>\<s> E x
\<Longrightarrow> c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. \<exists>*x. E x v)\<close>
  unfolding \<phi>Comp_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<phi>expns set_eq_iff subset_iff)
  subgoal for x by (cases x; clarsimp simp add: \<phi>expns set_eq_iff subset_iff; blast) .

(*lemma \<phi>INTERP_RES_\<phi>Res_Spec:
  \<open>res \<in> INTERP_RES fic \<longleftrightarrow> res \<in> \<phi>Res_Spec (\<I> FIC.INTERP fic) \<and> fic \<in> FIC.SPACE\<close>
  unfolding In_INTERP_RES \<phi>Res_Spec_def by simp blast *)

term \<open>\<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> FIC.INTERP (r * p) \<s>\<u>\<b>\<j> p. p \<in> P \<and> r \<in> FIC.SPACE \<and> p \<in> FIC.SPACE \<and> r ## p\<close>

lemma \<phi>Procedure_Hybrid_DL:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> P \<longmapsto> Q \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<longleftrightarrow> (\<forall>r s. (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> FIC.INTERP (r * p) \<s>\<u>\<b>\<j> p. p \<in> P \<and> r \<in> FIC.SPACE \<and> p \<in> FIC.SPACE \<and> r ## p)
       \<longrightarrow> (f s \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>v. \<I> FIC.INTERP (r * q) \<s>\<u>\<b>\<j> q. q \<in> Q v \<and> r \<in> FIC.SPACE \<and> q \<in> FIC.SPACE \<and> r ## q)
                \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. \<I> FIC.INTERP (r * e) \<s>\<u>\<b>\<j> e. e \<in> E v \<and> r \<in> FIC.SPACE \<and> e \<in> FIC.SPACE \<and> r ## e)))\<close>
  apply rule
   apply (unfold \<phi>Procedure_alt INTERP_SPEC \<phi>Res_Sat_def \<phi>Comp_Sat_def \<phi>Res_Spec_def subset_iff)
   apply (clarsimp simp add: times_set_def \<phi>expns In_INTERP_RES)
  thm In_INTERP_RES
  subgoal premises prems for r res s c proof-
    have t1: \<open>(\<exists>fic. (\<exists>y. fic = r * y \<and> y \<in> P \<and> r ## y) \<and> res \<in> RES.SPACE \<and> fic \<in> FIC.SPACE \<and> res \<in> \<I> FIC.INTERP fic)\<close>
      using FIC.SPACE_mult_homo prems by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=res], THEN spec[where x=r], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> f res\<close>])
      apply (cases s; clarsimp simp add: \<phi>expns In_INTERP_RES FIC.SPACE_mult_homo)
      apply force
      using FIC.SPACE_mult_homo by blast
  qed
  apply (clarsimp simp add: times_set_def \<phi>expns In_INTERP_RES)
  subgoal premises prems for res r s c proof-
    have t1: \<open>res \<in> RES.SPACE \<and> (\<exists>c. res \<in> \<I> FIC.INTERP (r * c) \<and> c \<in> P \<and> r \<in> FIC.SPACE \<and> c \<in> FIC.SPACE \<and> r ## c)\<close>
      using prems FIC.SPACE_mult_homo by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=r], THEN spec[where x=res], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> _\<close>])
      apply (cases s; simp add: \<phi>expns In_INTERP_RES)
      using FIC.SPACE_mult_homo apply blast
      using FIC.SPACE_mult_homo by blast
  qed .

lemma \<phi>Res_Spec_expn_R:
  \<open>\<phi>Res_Spec (\<I> FIC.INTERP (r * p) \<s>\<u>\<b>\<j> p. p \<in> (R \<heavy_comma> X) \<and> r \<in> FIC.SPACE \<and> p \<in> FIC.SPACE \<and> r ## p)
 = \<phi>Res_Spec (\<I> FIC.INTERP (r * u * x) \<s>\<u>\<b>\<j> u x. u \<in> R \<and> x \<in> X \<and> (r * u) \<in> FIC.SPACE \<and> x \<in> FIC.SPACE
                                           \<and> r ## u \<and> (r * u) ## x)\<close>
  unfolding set_eq_iff \<phi>Res_Spec_def
  apply (clarsimp simp add: \<phi>expns; rule; clarify)
  apply (metis FIC.SPACE_mult_homo sep_disj_multD1 sep_disj_multI1 sep_mult_assoc')
  by (metis FIC.SPACE_mult_homo sep_disj_multD2 sep_disj_multI2 sep_mult_assoc)

(*
lemma \<phi>Res_Sat_expn_R:
  \<open> (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> FIC.INTERP (r * p) \<s>\<u>\<b>\<j> p. p \<in> (R \<heavy_comma> X) \<and> r \<in> FIC.SPACE \<and> p \<in> FIC.SPACE \<and> r ## p)
\<longleftrightarrow> (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> FIC.INTERP (r * u * x) \<s>\<u>\<b>\<j> u x. u \<in> R \<and> x \<in> X \<and> (r * u) \<in> FIC.SPACE \<and> x \<in> FIC.SPACE
                                           \<and> r ## u \<and> (r * u) ## x)\<close>
  unfolding \<phi>Res_Sat_def using \<phi>Res_Spec_expn_R by simp *)

(*lemma \<phi>Res_Comp_expn_R:
  \<open> (c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> \<I> FIC.INTERP (r * p) \<s>\<u>\<b>\<j> p. p \<in> (R \<heavy_comma> X) \<and> r \<in> FIC.SPACE \<and> p \<in> FIC.SPACE \<and> r ## p)
\<longleftrightarrow> (c \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> \<I> FIC.INTERP (r * u * x) \<s>\<u>\<b>\<j> u x. u \<in> R \<and> x \<in> X \<and> (r * u) \<in> FIC.SPACE \<and> x \<in> FIC.SPACE
                                           \<and> r ## u \<and> (r * u) ## x)\<close>
  unfolding \<phi>Res_Sat_def using \<phi>Res_Spec_expn_R by simp *)


lemma \<phi>Res_Sat_expn_impEx:
  \<open>((\<s>\<t>\<a>\<t>\<e> s \<i>\<s> (ExSet A)) \<longrightarrow> P) \<longleftrightarrow> (\<forall>a. (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> A a) \<longrightarrow> P)\<close>
  by (simp add: ExSet_def \<phi>Res_Sat_def \<phi>Res_Spec_def)

lemma \<phi>Res_Sat_expn_impSubj:
  \<open>((\<s>\<t>\<a>\<t>\<e> s \<i>\<s> A \<s>\<u>\<b>\<j> B) \<longrightarrow> P) \<longleftrightarrow> (B \<longrightarrow> (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> A) \<longrightarrow> P)\<close>
  by (simp add: Subjection_expn \<phi>Res_Sat_def \<phi>Res_Spec_def; blast)


paragraph \<open>Weakest Precondition Transformer for \<phi>Res_Spec\<close>

lemma \<phi>M_RS_WP_SEQ[intro!]:
  \<open> F s \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> P \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> (\<And>v s. \<s>\<t>\<a>\<t>\<e> s \<i>\<s> P v \<Longrightarrow> G v s \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Q \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> (F \<bind> G) s \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Q \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding bind_def subset_iff \<phi>Res_Sat_def \<phi>Comp_Sat_def
  apply clarsimp subgoal for s s'
    by (cases s'; simp; cases s; clarsimp ; blast) .


section \<open>Predefined Resource Snippet\<close>

subsection \<open>Resource Base\<close>

locale resource =
  resource_kind RES.DOMAIN Res
  for Res :: "'T::sep_algebra resource_entry"
begin

lemma get_res_valid_raw:
  \<open> res \<in> RES.SPACE
\<Longrightarrow> get res \<in>\<^sub>S\<^sub>H domain\<close>
  unfolding RES.SPACE_def
  by (simp, metis in_DOMAIN proj_inj)

lemma get_res_Valid:
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> S
\<Longrightarrow> get res \<in>\<^sub>S\<^sub>H domain\<close>
  unfolding \<phi>Res_Spec_def \<phi>Res_Sat_def by (clarsimp simp add: \<r>_valid_split')

definition \<open>basic_fiction = Interp (\<lambda>x. { 1(Res #= x) })\<close>

lemma basic_fiction_\<I>:
  "\<I> basic_fiction = (\<lambda>x. { 1(Res #= x)})"
  unfolding basic_fiction_def
  by (rule Interp_inverse) (clarsimp simp add: Interpretation_def one_set_def)


lemma \<F>_itself_expn[\<phi>expns]:
  \<open>R2 ## x
\<Longrightarrow> \<phi>Res_Spec (\<I> (basic_fiction \<Zcomp>\<^sub>\<I> \<F>_it) (R2 * x))
  = \<phi>Res_Spec (\<I> (basic_fiction \<Zcomp>\<^sub>\<I> \<F>_it) R2 * {mk x})\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: \<phi>expns basic_fiction_\<I> prj.homo_mult interp_comp_\<I>)
  apply (rule; clarify)
   apply (simp add: mk_homo_mult sep_mult_assoc')
  using SPACE_mult_homo inj.homo_mult by force

lemma implies_part:
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk x}
\<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L get res\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def join_sub_def times_set_def apply clarsimp
  using get_homo_mult sep_disj_get_name by fastforce

end


subsection \<open>Fictions\<close>

subsubsection \<open>Fiction Base\<close>

locale basic_fiction =
   R: resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> I\<close>
for Res :: "'T::sep_algebra resource_entry"
and I :: "('U::sep_algebra, 'T) interp"
and Fic :: "'U fiction_entry"
begin

paragraph \<open>\<phi>-Type\<close>

definition \<phi> :: \<open>('U, 'x) \<phi> \<Rightarrow> (fiction, 'x) \<phi>\<close>
    \<comment> \<open>\<phi>Type for level-1 mapping\<close>
  where \<open>\<phi> T = (\<lambda>x. { mk v |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma \<phi>_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = mk v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>_def by simp

lemma \<phi>_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>_Prod:
  \<open> \<phi> T \<^emph> \<phi> U = \<phi> (T \<^emph> U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis mk_homo_mult)
  by (metis fun_1upd_homo inj.homo_mult sep_disj_mk)

lemma \<phi>_\<phi>None:
  \<open>\<phi> \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns)

lemma \<phi>_unit:
  \<open>(1 \<Ztypecolon> \<phi> Itself) = Void\<close>
  by (clarsimp simp add: set_eq_iff \<phi>_expn Itself_expn)


lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp

lemma [\<phi>reason 1300 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = 1 @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp


(*
lemma [\<phi>reason 1500 for \<open>(x \<Ztypecolon> \<phi> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action (?Act::?'act::simplification action)\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (() \<Ztypecolon> \<circle>) @action Act\<close>
  for Act :: \<open>'act::simplification action\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None
  by (simp add: transformation_refl) *)

paragraph \<open>Reasoning Rules\<close>

lemma \<phi>_cast:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp simp add: \<phi>expns)

lemma \<phi>_Structural_Extract:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W) P\<close>
  unfolding Structural_Extract_def
  by (simp add: \<phi>Prod_expn'[symmetric] \<phi>_Prod \<phi>_cast)

declare \<phi>_Structural_Extract[THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W)
      (Reverse_Transformation RP (Structural_Extract (y' \<Ztypecolon> \<phi> U') (w' \<Ztypecolon> \<phi> W') (x' \<Ztypecolon> \<phi> T') (r' \<Ztypecolon> \<phi> R') P') \<and> P)\<close>
  unfolding Generated_Rule_def Action_Tag_def
  by (blast intro: \<phi>_Structural_Extract[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)

lemma ToSA_by_structural_extraction:
  " Structure_Info U Q
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> Q' : Q
\<Longrightarrow> (<premise> Q' \<Longrightarrow> Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W P2))
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 \<heavy_comma> \<blangle> W \<brangle> \<w>\<i>\<t>\<h> P1
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> \<phi> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<w>\<i>\<t>\<h> P1 \<and> P2"
  unfolding Premise_def FOCUS_TAG_def Structural_Extract_def Simplify_def Try_def
  \<medium_left_bracket> premises SI and Q and SE and A
  have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
  ;;  A[THEN implies_right_prod]
     SE[OF \<open>Q'\<close>]
  \<medium_right_bracket> certified using \<phi> by simp .

lemma ToSA_by_structural_extraction__reverse_transformation:
  " Structure_Info U Q
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> Q' : Q
\<Longrightarrow> (Q' \<Longrightarrow> Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W
             (Reverse_Transformation RP2 (Structural_Extract (x' \<Ztypecolon> \<phi> T') W' (y' \<Ztypecolon> \<phi> U') R1' P2') \<and> P2)))
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 \<heavy_comma> \<blangle> W \<brangle> \<w>\<i>\<t>\<h> (Reverse_Transformation RP1 (R2'\<heavy_comma> \<blangle> W' \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<w>\<i>\<t>\<h> P1') \<and> P1)
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> \<phi> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<w>\<i>\<t>\<h>
      (Reverse_Transformation (RP2 \<and>\<^sub>\<r> RP1) (R2'\<heavy_comma> R1'\<heavy_comma> \<blangle> x' \<Ztypecolon> \<phi> T' \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A'\<heavy_comma> y' \<Ztypecolon> \<phi> U' \<w>\<i>\<t>\<h> P1' \<and> P2')
          \<and> P1 \<and> P2)"
  unfolding Premise_def FOCUS_TAG_def Structural_Extract_def Simplify_def
            Generated_Rule_def Compact_Antecedent_def Try_def
  \<medium_left_bracket> premises SI and Q and SE and A
  have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
  ;; A[THEN implies_right_prod]
     SE[OF \<open>Q'\<close>]
  \<medium_right_bracket> certified apply  (simp add: \<phi>)
  \<medium_left_bracket>
    have A : \<open>R2' \<heavy_comma> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<w>\<i>\<t>\<h> P1'\<close> using \<phi>_previous \<open>RP2 \<and> RP1\<close> by simp
    have SE: \<open>(R1' \<heavy_comma> x' \<Ztypecolon> \<phi> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> W' \<heavy_comma> y' \<Ztypecolon> \<phi> U' \<w>\<i>\<t>\<h> P2')\<close> using \<phi>_previous \<open>RP2 \<and> RP1\<close> by simp
    ;; SE A[THEN implies_right_prod]
  \<medium_right_bracket>. .


lemma ToSA_skip [\<phi>reason 1200 except \<open> _ \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<w>\<i>\<t>\<h> _\<close> ]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R'\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Action_Tag_def FOCUS_TAG_def split_paired_All Action_Tag_def
  by (metis ab_semigroup_mult_class.mult_ac(1) implies_left_prod mult.commute)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def using \<phi>_cast .

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action to Target
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi> U \<w>\<i>\<t>\<h> P @action to Target \<close>
  unfolding Action_Tag_def using \<phi>_cast .


lemma [\<phi>reason 1200]:
  \<open> Identity_Element\<^sub>I (x \<Ztypecolon> T)
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> \<phi> T) \<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def apply (simp add: \<phi>expns)
  using mk_homo_one by blast

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<phi> _) (_ \<Ztypecolon> \<phi> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> \<phi> T) (y \<Ztypecolon> \<phi> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (z \<Ztypecolon> \<phi> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>_cast)

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>(\<phi> (ExTyp T)) = (\<exists>\<phi> c. \<phi> (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi> (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<phi> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi> T) = (x' \<Ztypecolon> \<phi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>\<phi>_simp_cong ("x \<Ztypecolon> \<phi> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>_simp_cong} ctxt)
\<close>

paragraph \<open>Synthesis for moving\<close>

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse (\<phi> ?T) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (\<phi> T) (\<lambda>_. x \<Ztypecolon> \<phi> T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

(* lemma [\<phi>reason for \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?S1 \<longmapsto> \<lambda>ret. ?S2\<heavy_comma>  \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E\<close>]:
  \<open> SUBGOAL G G'
\<Longrightarrow> S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S2\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle>
\<Longrightarrow> SOLVE_SUBGOAL G'
\<Longrightarrow> \<p>\<r>\<o>\<c> Return \<phi>V_none \<lbrace> S1 \<longmapsto> \<lambda>_. S2\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<rbrace>\<close>
  unfolding FOCUS_TAG_def Synthesis_def Action_Tag_def
  using \<phi>__Return_rule__ view_shift_by_implication by blast *)

end


subsubsection \<open>Permission Fiction\<close>

locale permission_fiction =
   R: resource Res
+  share: perm_ins_homo \<psi>
+  fiction_kind FIC.DOMAIN INTERPRET Fic
      \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> (\<F>_functional \<psi>)\<close>
for Res :: "'T::sep_algebra resource_entry"
and \<psi> :: \<open>'T \<Rightarrow> 'U::{share_sep_disj,share_module_sep,sep_algebra}\<close>
and Fic :: "'U fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_functional \<psi>\<close> ..

lemma sep_disj_fiction:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> INTERP r * { R.mk x }
\<Longrightarrow> r ## mk (\<psi> x)\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: R.basic_fiction_\<I> interp_comp_\<I> \<phi>expns
            \<phi>Res_Spec_def R.\<r>_valid_split'
            R.inject_wand_homo interp_split'
            sep_disj_get_name_eq[symmetric]
            simp del: sep_disj_get_name_eq)
  using sep_disj_multD2 by force

lemma expand_subj:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (\<psi> x)) \<s>\<u>\<b>\<j> r ## mk (\<psi> x))
  = \<phi>Res_Spec (\<I> INTERP r * { R.mk x })\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify, rule)
  apply (clarsimp simp add: R.basic_fiction_\<I> interp_comp_\<I> \<phi>expns
            share.sep_inj_proj \<phi>Res_Spec_def R.\<r>_valid_split'
            R.inject_wand_homo interp_split' prj.homo_mult)
  thm interp_split'
  subgoal for res_r a r'
    apply (rule exI[where x=\<open>res_r * R.mk a\<close>]; rule)
    apply (metis R.inj.homo_mult R.sep_disj_mk fun_1upd_homo_right1 sep_mult_assoc')
    by (metis R.mk_homo_mult R.sep_disj_mk sep_disj_multD1 sep_disj_multI1)

  apply (clarsimp simp add: R.basic_fiction_\<I> \<phi>expns \<phi>Res_Spec_def R.\<r>_valid_split'
        R.inject_wand_homo interp_split' sep_mult_assoc prj.homo_mult interp_comp_\<I>)
  subgoal premises prems for res_r a y proof -
    have t1[simp]: \<open>y ## x\<close>
      using prems(5) prems(7) sep_disj_multD2 by force

    show ?thesis
      apply rule
      apply (rule exI[where x=\<open>a\<close>], rule exI[where x=\<open>R.mk (y * x)\<close>])
      apply (metis R.inj.homo_mult fun_1upd_homo prems(5) prems(6) prems(7) sep_disj_multI2 share.homo_mult t1)
      by (metis prems(1) prems(8) sep_disj_get_name_eq share.sep_disj_homo_semi t1)

  qed .

lemma expand:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> r ## mk (\<psi> x)
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (\<psi> x))) =
    \<phi>Res_Spec (\<I> INTERP r * {R.mk x})\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

(*lemma expand_conj:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> INTERP (r * mk (perm_ins_homo x))) \<and> r ## mk (perm_ins_homo x)
\<longleftrightarrow> (\<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> INTERP r * { R.mk x })\<close>
  unfolding \<phi>Res_Sat_def
  subgoal premises prems
    using expand_subj[where r=r and x=x, OF prems(1)]
      by (simp add: \<phi>expns) . *)


lemma partial_implies_raw:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (share n (\<psi> x))
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (share n (\<psi> x)))
\<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L R.get res\<close>
  unfolding \<phi>Res_Spec_def \<phi>Res_Sat_def
  apply (clarsimp simp add: R.basic_fiction_\<I> interp_comp_\<I> \<phi>expns
            \<phi>Res_Spec_def R.\<r>_valid_split' R.inject_wand_homo
            R.prj.homo_mult interp_split' prj.homo_mult)
  apply (cases \<open>n \<le> 1\<close>)
  apply (metis join_sub_def join_sub_ext_left sep_disj_get_name share.join_sub_share_join_sub_whole)
  subgoal premises prems for u y a proof -
    have t0: \<open>1 / n * n = 1\<close>
      by (metis nonzero_eq_divide_eq order_less_irrefl prems(2))
    have t1: \<open>1 / n \<le> 1 \<and> 0 < 1 / n\<close>
      using prems(13) by force
    have t2: \<open>share (1/n) (share n (\<psi> x)) \<preceq>\<^sub>S\<^sub>L share n (\<psi> x)\<close>
      by (simp add: order_less_imp_le prems(2) share.\<psi>_self_disj share_sub t1)
    then have t3: \<open>\<psi> x \<preceq>\<^sub>S\<^sub>L share n (\<psi> x)\<close>
      using share_share_not0
      by (metis prems(2) share_left_one t0 t1)
    then show ?thesis
      by (metis join_sub_ext_left prems(10) prems(3) prems(8) resource_kind_axioms resource_kind_def sep_space_entry.sep_disj_get_name share.homo_join_sub)
  qed .

paragraph \<open>Reasoning Rules\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_transformation
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end





subsubsection \<open>Itself Fiction\<close>

locale identity_fiction =
   R: resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_it\<close>
for Res :: "'T::sep_algebra resource_entry"
and Fic :: "'T fiction_entry"
begin

sublocale basic_fiction where I = \<open>\<F>_it\<close> ..

lemma sep_disj_fiction:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> s \<i>\<s> \<I> INTERP r * { R.mk x }
\<Longrightarrow> r ## mk x\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: R.basic_fiction_\<I> interp_comp_\<I> \<phi>expns
            \<phi>Res_Spec_def R.\<r>_valid_split'
            R.inject_wand_homo interp_split'
            sep_disj_get_name_eq[symmetric]
            simp del: sep_disj_get_name_eq)
  using sep_disj_multD2 by force

lemma expand_subj:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> (\<phi>Res_Spec (\<I> INTERP (r * mk x) \<s>\<u>\<b>\<j> r ## mk x)) = \<phi>Res_Spec (\<I> INTERP r * {R.mk x}) \<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify; rule; clarsimp simp add: \<phi>expns R.basic_fiction_\<I> interp_split' prj.homo_mult interp_comp_\<I>)
  apply (simp add: R.mk_homo_mult)
  apply (metis (no_types, lifting) R.sep_disj_mk sep_disj_get_name sep_disj_multD1 sep_disj_multI1 sep_mult_assoc')
  apply (simp add: R.mk_homo_mult[symmetric] sep_mult_assoc)
  by (metis R.mk_homo_mult R.sep_disj_mk sep_disj_get_name_eq sep_disj_multD2 sep_disj_multI2)

lemma expand:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> r ## mk x
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk x)) = \<phi>Res_Spec (\<I> INTERP r * {R.mk x})\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

declare ToSA_by_structural_extraction
   [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_transformation
   [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end


subsection \<open>Nosep Monolithic Resource\<close>
  \<comment> \<open>The resource non-sepable and having type shape \<^typ>\<open>'a::nonsepable_semigroup option\<close>\<close>

locale nonsepable_mono_resource =
  resource Res
for Res :: "'T nosep option resource_entry"
begin

definition fiction_agree
  where \<open>fiction_agree = basic_fiction ;\<^sub>\<I> \<F>_optionwise \<F>_agree\<close>

end


subsubsection \<open>Interp Agreement\<close>

(*TODO: ('k \<Rightarrow> 'v) nosep option ----> ('k \<Rightarrow> 'v share option)
  total to that
  none to none
 *)

locale agreement_fiction_for_nosepable_mono_resource =
   R: nonsepable_mono_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.fiction_agree\<close>
for Res :: "'T nosep option resource_entry"
and Fic :: "'T nosep agree option fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_optionwise \<F>_agree\<close> Fic
  by (standard; simp add: R.fiction_agree_def raw_domain)

lemma partial_implies:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> r ## mk (Some (agree (nosep x)))
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (Some (agree (nosep x))))
\<Longrightarrow> R.get res = Some (nosep x)\<close>
  unfolding \<phi>Res_Spec_def \<phi>Res_Sat_def
  apply (clarsimp simp add: interp_split'
     R.fiction_agree_def R.basic_fiction_\<I> interp_comp_\<I> \<phi>expns R.\<r>_valid_split'
     R.inject_wand_homo R.prj.homo_mult \<F>_optionwise_\<I> image_iff Bex_def
     \<F>_agree_def prj.homo_mult)
  apply (cases \<open>get r\<close>; simp)
  subgoal for u y a aa
    apply (cases aa; simp)
    subgoal premises prems for xa proof -
      have \<open>get r ## Some (agree (nosep x))\<close>
        by (metis prems(2) sep_disj_get_name)
      from this [unfolded \<open>get r = _\<close>, simplified]
      show ?thesis .
    qed . .

lemma double:
  \<open>{mk x |x. P x} \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {mk x |x. P x} * {mk x |x. P x}\<close>
  unfolding Transformation_def
  apply (clarsimp simp add: \<phi>expns mk_homo_mult[symmetric])
  subgoal for x'
    apply (rule exI[where x=\<open>mk x'\<close>], rule exI[where x=\<open>mk x'\<close>])
    by (cases x'; simp add: mk_homo_mult[symmetric]) .

lemma contract:
  \<open>{mk x |x. P x} * {mk x |x. P x} \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {mk x |x. P x} \<close>
  unfolding Transformation_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for x y by (cases x; cases y; simp add: mk_homo_mult[symmetric]) .

paragraph \<open>\<phi>-Type\<close>

abbreviation \<open>\<phi>_ag T \<equiv> \<phi> (Agreement (Nosep T))\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_transformation
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

lemma \<phi>_double_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nosep v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: double)
qed

lemma \<phi>_contract_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nosep v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: contract)
qed

end



subsection \<open>Resources based on Mapping\<close>

locale mapping_resource =
  resource Res
for Res :: "('key \<Rightarrow> 'val::sep_algebra) resource_entry"
begin

lemma "__allocation_rule__":
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> k \<notin> dom1 (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> updt (\<lambda>f. f(k := u)) res \<i>\<s> R * {mk (1(k := u))}\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def inject_wand_homo
          prj.homo_mult times_fun_upd)
  subgoal premises prems for m proof -
    {
      assume A: \<open>k \<notin> dom1 m\<close>
      have t2: \<open>m ## 1(k := u)\<close>
        using A dom1_def sep_disj_fun_def by fastforce
      have t3: \<open>res(name := inject m) = res\<close>
        by (simp add: fun_upd_idem prems(5))
      have t1: \<open>res(name := inject (m(k := u))) = res * mk (1(k := u)) \<and> res ## mk (1(k := u))\<close>
        thm fun_split_1_not_dom1[where f=m]
        apply (subst fun_split_1_not_dom1[where k=k]) using A apply this
        apply (simp add: t2 inj.homo_mult split)
        by (metis fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1) inj.sep_disj_homo_semi t2 t3)
    }
    then show ?thesis
      using prems(2) prems(4) by blast
  qed .

end

locale fiction_base_for_mapping_resource =
  R: mapping_resource Res
+ fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> I\<close>
for Res :: "('key \<Rightarrow> 'val::sep_algebra) resource_entry"
and I   :: "('T::sep_algebra, 'key \<Rightarrow> 'val) interp"
and Fic :: "'T fiction_entry"
begin

sublocale

end


subsection \<open>One Level Parital Mapping\<close>

subsubsection \<open>Locale for Resource\<close>

locale partial_map_resource =
  mapping_resource Res
for Res :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> updt (\<lambda>f. f(k := u)) res \<i>\<s> R * {mk (1(k := u))}\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def inject_wand_homo
          prj.homo_mult times_fun_upd )
  apply (clarsimp simp add: sep_disj_partial_map_upd
          nonsepable_semigroup_sepdisj_fun mk_homo_mult)
  subgoal premises prems for x aa proof -
    have t1: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(7))
    have t2: \<open>clean x ## (mk aa * mk (1(k := u)))\<close>
      by (simp add: fun_1upd_homo)
    show ?thesis
      by (metis (no_types, opaque_lifting) fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1) inj.sep_disj_homo_semi mult_1_class.mult_1_left nonsepable_semigroup_sepdisj_fun prems(5) prems(8) t1)
  qed .

lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k := None) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> updt (\<lambda>f. f(k := None)) res \<i>\<s> R\<close>
  using "__updt_rule__"[where u=None, simplified, simplified,
            simplified, simplified one_set_def[symmetric], simplified] .

(*depreciate*)
abbreviation perm_ins_homo :: \<open>('key \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'val share option)\<close>
  where \<open>perm_ins_homo \<equiv> (o) to_share\<close>
(*depreciate*)
abbreviation \<open>share_fiction \<equiv> basic_fiction ;\<^sub>\<I> \<F>_functional perm_ins_homo\<close>

(* lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> 1 \<Znrres> v))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k \<mapsto> v)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' inject_wand_homo)
  subgoal premises prems for res_r y a r
    apply (insert \<open>a * _ = _\<close>[unfolded to_share_wand_homo[where b=\<open>1(k \<mapsto> v)\<close>, simplified, OF \<open>a ## _\<close>]])
    apply (clarsimp simp add: times_fine'[symmetric] mk_homo_mult mult.assoc[symmetric])
    using prems(3) by blast
  subgoal premises prems for res_r a r proof -
    have t1[simp]: \<open>a ## 1(k \<mapsto> v)\<close>
      by (metis prems(6) prems(7) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
    show ?thesis
    apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine')
      apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k \<mapsto> v)))"], simp add: prems)
      by (metis (no_types, lifting) map_option_o_map_upd t1 to_share_funcomp_1 to_share_funcomp_sep_disj_I to_share_wand_homo)
  qed .


lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> n \<Znrres> v))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' inject_wand_homo
            proj_homo_mult)
  subgoal premises prems for res_r y a r proof -
    from \<open>a * _ = _\<close>[THEN fun_cong[where x=k], simplified times_fun, simplified]
    have t1: \<open>y k = Some v\<close>
      using prems(6) prems(7) strip_share_fun_mult by force
    then show ?thesis apply (simp add: t1 times_fun)
      using prems(9) sep_disj_partial_map_some_none t1 by fastforce
  qed .

lemma
  assumes A: \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> n \<Znrres> v))))\<close>
  shows share_fiction_partially_implies'[simp]: \<open>!!( get res) k = Some v\<close>
proof -
  from A[THEN share_fiction_partially_implies]
  show ?thesis by fastforce
qed
*)
lemma raw_unit_assertion_implies[simp]:
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * { mk (1(k \<mapsto> v))}
\<Longrightarrow> get res k = Some v\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' inject_wand_homo
      prj.homo_mult sep_disj_fun_def times_fun)
  by (metis (mono_tags, lifting) sep_disj_option_nonsepable(1) sep_mult_commute times_option(2))


end

subsubsection \<open>Itself Fiction\<close>

locale identity_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_it\<close>
for Res :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val option) fiction_entry"
begin

sublocale identity_fiction Res Fic ..

end


subsubsection \<open>Permission Fiction\<close>

locale share_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.share_fiction\<close>
for Res :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val share option) fiction_entry"
begin

sublocale permission_fiction Res \<open>R.perm_ins_homo\<close> ..

lemma expand:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> r ## mk (R.perm_ins_homo x)
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (R.perm_ins_homo x))) =
    \<phi>Res_Spec (\<I> INTERP r * {R.mk x} )\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

lemma partial_implies:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k \<mapsto> Share n v))
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k \<mapsto> Share n v)))
\<Longrightarrow> R.get res k = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k \<mapsto> v)\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, ccfv_threshold) fun_split_1 fun_upd_same join_sub_def one_option_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep)

lemma partial_implies'[simp]:
  assumes FS: \<open>r \<in> FIC.SPACE\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k \<mapsto> Share n v))\<close>
    and A: \<open>\<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k \<mapsto> Share n v)))\<close>
  shows \<open>R.get res k = Some v\<close>
proof -
  from partial_implies[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

(* lemma VS_merge_ownership_identity:
  \<open> na + nb \<le> 1
\<Longrightarrow> x \<Ztypecolon> \<phi> (share.\<phi> na Itself) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Itself) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi> (share.\<phi> (na + nb) Itself)\<close>
  by (rule VS_merge_ownership; simp add: \<phi>expns)

lemma VS_split_ownership_identity:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (0 < n \<longrightarrow> na + nb = n \<and> 0 < na \<and> 0 < nb)
\<Longrightarrow> x \<Ztypecolon> \<phi> (share.\<phi> n Itself) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi> (share.\<phi> na Itself) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Itself)\<close>
  by (rule VS_split_ownership; simp add: \<phi>expns sep_disj_fun_def share_fun_def; clarify)
  (* subgoal premises prems for a
    by (insert \<open>\<forall>_. _\<close>[THEN spec[where x=a]], cases \<open>x a\<close>; simp add: share_All prems) . *)


lemma VS_divide_ownership:
  \<open>FIX x \<Ztypecolon> \<phi> (share.\<phi> n Itself) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Itself) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Itself)\<close>
  unfolding Fix_def
  by (rule VS_split_ownership_identity; simp add: Premise_def)
*)
end

locale share_fiction_for_partial_mapping_resource_nonsepable =
  share_fiction_for_partial_mapping_resource Res Fic
for Res :: "('key \<Rightarrow> 'val nosep option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val nosep share option) fiction_entry"
begin

lemma \<phi>nonsepable_normalize:
  \<open>(x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some (Nosep Itself)))))
 = (nosep x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some Itself))))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

end



subsection \<open>Two Level Parital Mapping\<close>

definition \<open>map_fun_at g k f = (\<lambda>x. if x = k then g (f x) else f x)\<close>

lemma map_fun_at_1[simp]: \<open>map_fun_at g k 1 = 1(k := g 1)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp

lemma map_fun_at_const[simp]:
  \<open>map_fun_at (\<lambda>_. u) k f = f(k := u)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp


subsubsection \<open>Locale of Resource\<close>

locale partial_map_resource2 =
  mapping_resource Res
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> updt (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
      \<i>\<s> R * {mk (1(k := 1(k2 := u)))} \<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def inject_wand_homo
          prj.homo_mult times_fun_upd)
  subgoal premises prems for x aa proof -
    have [simp]: \<open>aa k k2 = None\<close>
      by (metis fun_upd_same prems(8) sep_disj_fun_def sep_disj_option_nonsepable(1))
    then have [simp]:
        \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (aa * 1(k := 1(k2 \<mapsto> any)))
            = aa * 1(k := 1(k2 := u))\<close>
      unfolding map_fun_at_def fun_eq_iff times_fun_def
      by simp
    have t1[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(7))
    have t2[simp]: \<open>aa ## 1(k := 1(k2 := u))\<close>
      by (simp add: sep_disj_fun_def)
    have t3[simp]:
      \<open>clean x ## (mk aa * mk (1(k := 1(k2 := u))))\<close>
      by (simp add: fun_1upd_homo)
    have t4:
      \<open>x ## mk (1(k := 1(k2 := u)))\<close>
      by (metis sep_disj_mk sep_disj_multI1 t1 t2 t3)

    show ?thesis
      apply (simp add: prems mk_homo_mult sep_mult_assoc')
      using prems(6) t4
      by (metis prems(5))
  qed .


lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := any))}
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> updt (\<lambda>f. f(k := 1)) res \<i>\<s> R\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def inject_wand_homo
          prj.homo_mult times_fun_upd )
  subgoal premises prems for x aa proof -
    have \<open>dom (aa k) = {}\<close>
    proof -
      obtain kk :: "('key2 \<Rightarrow> 'val option) \<Rightarrow> 'key2" where
        f1: "\<forall>f. 1 \<noteq> f (kk f) \<or> dom f = {}"
        by (metis dom_eq_empty_conv one_option_def)
      have "aa k ## any"
        by (metis fun_upd_same prems(9) sep_disj_fun)
      then have "\<forall>ka. 1 = aa k ka \<or> 1 = any ka"
        by (metis one_option_def option.exhaust sep_disj_fun_nonsepable(2))
      then show ?thesis
        by (metis domIff f1 mult_1_class.mult_1_right one_option_def prems(2) times_fun)
    qed
    then have t1[simp]: \<open>(aa * 1(k := any))(k := 1) = aa\<close>
      by (smt (verit, del_insts) Diff_iff dom1_upd dom_1 dom_eq_empty_conv fun_split_1_not_dom1 fun_upd_triv fun_upd_upd insertCI)
    have t2[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(8))
    show ?thesis
      using prems(10) prems(6) t1 by force
  qed .

abbreviation perm_ins_homo :: \<open>('key \<Rightarrow> 'key2 \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option)\<close>
  where \<open>perm_ins_homo \<equiv> (o) ((o) to_share)\<close>
abbreviation \<open>share_fiction \<equiv> basic_fiction ;\<^sub>\<I> \<F>_functional perm_ins_homo\<close>

(*depreciated!*)
(*lemma share_fiction_expn_full':
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := to_share o f))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := f)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' inject_wand_homo times_fun)
  subgoal premises prems for res_r y a r
    apply (insert \<open>\<forall>x. a x * _ = _\<close>[THEN spec[where x=k], simplified,
          unfolded to_share_wand_homo[where b=f, simplified,
                      OF sep_disj_fun[where x=k, OF \<open>a ## _\<close>, simplified]]])
      apply (clarify)
      subgoal premises prems2 for a' proof -
        have t1: \<open>y = y(k := a') * 1(k := f)\<close>
          unfolding fun_eq_iff times_fun
          apply simp
          by (metis fun_upd_apply mult_1_class.mult_1_right prems2(2) times_fun_def)
        have t2: \<open>y(k := a') ## 1(k := f)\<close>
          using prems2(3) sep_disj_fun_def by fastforce
        show ?thesis
          apply (subst t1)
          apply (clarsimp simp add: times_fine'[OF t2, symmetric] mk_homo_mult mult.assoc[symmetric])
          apply (rule exI[where x="res_r * mk (Fine (y(k := a')))"], simp)
          apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (y(k := a')))"], simp add: prems)
          by (smt (verit, del_insts) mult_1_class.mult_1_right one_fun prems(4) prems2(1))
      qed .
    subgoal premises prems for res_r a fic_r r proof -
      have t1: \<open>a ## 1(k := f)\<close>
        by (metis prems(7) prems(8) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
      have t2: \<open>fic_r ## 1(k := to_share o f)\<close>
        unfolding sep_disj_fun_def
        apply (clarsimp)
        by (metis comp_apply fun_upd_same prems(4) sep_disj_fun_def t1 to_share_funcomp_sep_disj_I)

      show ?thesis
        apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine'[OF t1])
        apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k := f))) "],
                simp add: prems t2)
        by (smt (verit, best) fun_split_1 fun_upd_def fun_upd_same map_option_o_map_upd prems(4) sep_disj_fun t1 t2 times_fun to_share_funcomp_1 to_share_wand_homo)
    qed .

lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> 1 \<Znrres> v)))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := 1(k2 \<mapsto> v))))})\<close>
  using share_fiction_expn_full'[where f=\<open>1(k2 \<mapsto> v)\<close>, simplified] .

(*depreciated!*)
lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k k2 = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' inject_wand_homo
            proj_homo_mult)
  subgoal premises prems for res_r y a r proof -
    note t1 = \<open>a ## _\<close>[THEN sep_disj_fun[where x=k], simplified,
                 THEN sep_disj_fun[where x=k2], simplified]
    from \<open>\<forall>_. (a * _) _ = _\<close>[THEN spec[where x=k], simplified times_fun, simplified,
          THEN fun_cong[where x=k2],
          simplified times_fun, simplified]
    have t2: \<open>y k k2 = Some v\<close>
      using t1 apply (cases \<open>a k k2\<close>; cases \<open>y k k2\<close>; simp)
      by (metis sep_disj_share share.collapse share.inject times_share)

    then show ?thesis apply (simp add: t2 times_fun)
      by (metis mult_1_class.mult_1_left one_option_def prems(9) sep_disj_fun sep_disj_option_nonsepable(1) t2)
  qed .

lemma
  assumes A: \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))\<close>
  shows share_fiction_partially_implies'[simp]: \<open>!!( get res) k k2 = Some v\<close>
proof -
  from A[THEN share_fiction_partially_implies]
  show ?thesis by fastforce
qed
*)

lemma raw_unit_assertion_implies[simp]:
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * { mk (1(k := 1(k2 \<mapsto> v)))}
\<Longrightarrow> get res k k2 = Some v\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' inject_wand_homo
      prj.homo_mult sep_disj_fun_def times_fun)
  by (metis (full_types) fun_upd_same sep_disj_option_nonsepable(1) times_option(3))

lemma raw_unit_assertion_implies':
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * { mk (1(k := f))}
\<Longrightarrow> f \<subseteq>\<^sub>m get res k\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' inject_wand_homo)
  subgoal premises prems for x a proof -
    have t1[simp]: \<open>inject a ## inject (1(k := f))\<close>
      using prems(6) by fastforce
    show ?thesis apply (clarsimp simp add: prj.homo_mult[OF t1] sep_disj_fun_def times_fun map_le_def)
      by (metis (mono_tags, lifting) fun_sep_disj_1_fupdt(1) fun_upd_triv mult_1_class.mult_1_left one_option_def prems(6) sep_disj_fun_nonsepable(2))
  qed .

lemma raw_unit_assertion_implies''[simp]:
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * { mk (1(k := f))}
\<Longrightarrow> k2 \<in> dom f
\<Longrightarrow> get res k k2 = f k2\<close>
  using raw_unit_assertion_implies'[unfolded map_le_def]
  by simp

end

subsubsection \<open>Permission Fiction\<close>

locale share_fiction_for_partial_mapping_resource2 =
  R: partial_map_resource2 Res
  +  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.share_fiction\<close>
  for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
    and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option) fiction_entry"
begin

sublocale permission_fiction Res \<open>R.perm_ins_homo\<close> ..

lemma [simp]:
  \<open>R.perm_ins_homo (1(k := f)) = 1(k := to_share o f)\<close>
  unfolding fun_eq_iff by simp

lemmas partial_implies = partial_implies_raw

lemma partial_implies':
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k := 1(k2 \<mapsto> Share n v)))
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v))))
\<Longrightarrow> R.get res k k2 = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, del_insts) fun_upd_same join_sub_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep times_option(3))

lemma partial_implies'':
  assumes FS: \<open>r \<in> FIC.SPACE\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k := 1(k2 \<mapsto> Share n v)))\<close>
    and A: \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v)))) \<close>
  shows [simp]: \<open>R.get res k k2 = Some v\<close>
proof -
  from partial_implies'[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

end


section \<open>Common Instructions\<close>

subsection \<open>Drop & Duplicate Value\<close>

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> Val ?raw ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action action_dup\<close>]:
  \<open>x \<Ztypecolon> Val raw T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Val raw T \<heavy_comma> x \<Ztypecolon> Val raw T @action action_dup\<close>
  unfolding Transformation_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?R \<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action action_drop\<close>]:
  \<open>Void \<heavy_comma> x \<Ztypecolon> Val raw T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Void @action action_drop\<close>
  unfolding Transformation_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)


subsection \<open>Abnormal\<close>

definition throw :: \<open>ABNM \<Rightarrow> 'ret proc\<close>
  where \<open>throw raw = det_lift (Abnormal raw)\<close>

lemma throw_reduce_tail[procedure_simps,simp]:
  \<open>(throw any \<ggreater> f) = throw any\<close>
  unfolding throw_def bind_def det_lift_def by simp

lemma "__throw_rule__"[intro!]:
  \<open> (\<And>a. X a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' a)
\<Longrightarrow> \<p>\<r>\<o>\<c> (throw excep :: 'ret proc) \<lbrace> X excep \<longmapsto> Any \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> X'\<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Transformation_def
  apply clarsimp
  by (meson Transformation_def View_Shift_def view_shift_by_implication)

lemma throw_\<phi>app:
  \<open> (\<And>v. Remove_Values (X v) (X' v))
\<Longrightarrow> \<p>\<r>\<o>\<c> throw excep \<lbrace> X excep \<longmapsto> 0 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> X' \<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Remove_Values_def Transformation_def
  apply clarsimp
  by (meson Transformation_def View_Shift_def view_shift_by_implication)

definition op_try :: "'ret proc \<Rightarrow> (ABNM \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc"
  where \<open>op_try f g s = \<Union>((\<lambda>y. case y of Success x s' \<Rightarrow> {Success x s'}
                                       | Abnormal v s' \<Rightarrow> g v s'
                                       | AssumptionBroken \<Rightarrow> {AssumptionBroken}
                                       | NonTerm \<Rightarrow> {NonTerm}
                                       | Invalid \<Rightarrow> {Invalid}) ` f s)\<close>

lemma "__op_try__"[intro!]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. E v)
\<Longrightarrow> (\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 )
\<Longrightarrow> \<p>\<r>\<o>\<c> op_try f g \<lbrace> X \<longmapsto> \<lambda>v. Y1 v + Y2 v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2  \<close>
  unfolding op_try_def \<phi>Procedure_def subset_iff
  apply clarsimp subgoal for comp R x s
    apply (cases s; simp; cases x; clarsimp simp add: \<phi>expns ring_distribs)
    subgoal premises prems for a b u v
      using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
      by (metis (no_types, lifting) INTERP_SPEC LooseStateSpec_expn(1) prems(3) prems(6) prems(7) prems(8) prems(9) set_mult_expn)
    subgoal premises prems for a b c d u v2 proof -
      have \<open>Abnormal a b \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Success c d \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E2 v))\<close>
        using prems(2)[of a, THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_SPEC prems(4) set_mult_expn)
      note this[simplified]
      then show ?thesis
        by (metis INTERP_SPEC prems(11) set_mult_expn)
    qed
    subgoal premises prems for a b c d u v proof -
      have \<open>Abnormal a b \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Abnormal c d \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E2 v))\<close>
        using prems(2)[THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_SPEC prems(4) set_mult_expn)
      note this[simplified]
      then show ?thesis
        by (simp add: INTERP_SPEC set_mult_expn)
    qed
     apply (smt (z3) INTERP_SPEC LooseStateSpec_expn(2) LooseStateSpec_expn(3) set_mult_expn)
    by blast .

definition "Union_the_Same_Or_Arbitrary_when_Var Z X Y \<longleftrightarrow> (\<forall>v. (Z::'v \<Rightarrow> 'a set) v = X v + Y v)"

lemma Union_the_Same_Or_Arbitrary_when_Var__the_Same:
  \<open>Union_the_Same_Or_Arbitrary_when_Var Z Z Z\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by simp

lemma Union_the_Same_Or_Arbitrary_when_Var__Arbitrary:
  \<open>Union_the_Same_Or_Arbitrary_when_Var (\<lambda>v. X v + Y v) X Y\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by blast

\<phi>reasoner_ML Union_the_Same_Or_Arbitrary_when_Var 1200
  (\<open>Union_the_Same_Or_Arbitrary_when_Var ?Z ?X ?Y\<close>) = \<open>
fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Union_the_Same_Or_Arbitrary_when_Var\<close>, _)
          $ Z $ _ $ _) = Thm.major_prem_of sequent
  in (ctxt,
        (if is_Var (Envir.beta_eta_contract Z)
         then @{thm Union_the_Same_Or_Arbitrary_when_Var__Arbitrary}
         else @{thm Union_the_Same_Or_Arbitrary_when_Var__the_Same})
        RS sequent) |> Seq.single
  end
\<close>

proc (nodef) try'':
  assumes F: \<open>\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  assumes G: \<open>(\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE2 )\<close>
  input  X
    output YY
  throws EE2
  \<medium_left_bracket> "__op_try__"
    F
    G
  \<medium_right_bracket> .

proc (nodef) try':
  assumes A: \<open>Union_the_Same_Or_Arbitrary_when_Var Z Y1 Y2\<close>
  assumes F: \<open>\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  assumes G: \<open>\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 \<close>
  input  X
    output Z
  throws E2
  \<medium_left_bracket> "__op_try__" F G
    unfold A[unfolded Union_the_Same_Or_Arbitrary_when_Var_def, THEN spec, symmetric]
  \<medium_right_bracket>.


subsection \<open>Access the Resource\<close>

subsubsection \<open>Legacy\<close>

definition \<phi>M_get_res :: \<open>(resource \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>M_get_res R F = (\<lambda>res. F (R res) res)\<close>

definition \<phi>M_get_res_entry :: \<open>(resource \<Rightarrow> ('k \<rightharpoonup> 'a)) \<Rightarrow> 'k \<Rightarrow> ('a \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>M_get_res_entry R k F =
    \<phi>M_get_res R (\<lambda>res. case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition \<phi>M_set_res :: \<open> (('x \<Rightarrow> 'x) \<Rightarrow> resource \<Rightarrow> resource) \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> unit proc \<close>
  where \<open>\<phi>M_set_res Updt F = (\<lambda>res. {Success (\<phi>arg ()) (Updt F res)})\<close>

subsubsection \<open>Getters\<close>

paragraph \<open>basic resource\<close>

context resource begin

definition \<phi>R_get_res :: \<open>('T \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close> \<comment> \<open>depreciated\<close>
  where \<open>\<phi>R_get_res F = (\<lambda>res. F (get res) res)\<close>

definition \<phi>R_get_res' :: \<open>'T proc\<close> \<comment> \<open>use this\<close>
  where \<open>\<phi>R_get_res' = (\<lambda>res. Return (\<phi>arg (get res)) res)\<close>

lemma \<phi>R_get_res'_valid:
  \<open>Valid_Proc \<phi>R_get_res'\<close>
  unfolding Valid_Proc_def \<phi>R_get_res'_def Return_def det_lift_def
  by simp

lemma \<phi>R_get_res[intro!]:
  \<open> get res = v
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_def subset_iff by simp

end

paragraph \<open>nonsepable_mono_resource\<close>

definition (in nonsepable_mono_resource) \<phi>R_get_res_entry :: \<open>('T \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_get_res_entry F = \<phi>R_get_res (\<lambda>v. case v of Some v' \<Rightarrow> F (nosep.dest v')
                                                      | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in nonsepable_mono_resource) \<phi>R_get_res_entry:
  \<open> get res = Some (nosep v)
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res_entry F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

paragraph \<open>partial_map_resource\<close>

definition (in partial_map_resource)
  \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> ('val \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_get_res_entry k F =
    \<phi>R_get_res (\<lambda>res. case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition (in partial_map_resource)
  \<phi>R_get_res_entry' :: \<open>'key \<Rightarrow> 'val proc\<close>
  where \<open>\<phi>R_get_res_entry' k =
    \<phi>R_get_res' \<bind> (\<lambda>res. case \<phi>arg.dest res k of Some v \<Rightarrow> Return (\<phi>arg v) | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in partial_map_resource) \<phi>R_get_res_entry[intro!]:
  \<open> get res k = Some v
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res_entry k F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

subparagraph \<open>identity_fiction_for_partial_mapping_resource\<close>

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_get_res_entry_frm[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> \<black_circle> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry key F
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> \<black_circle> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_Hybrid_DL \<phi>Res_Spec_expn_R imp_conjL
            \<phi>Res_Sat_expn_impEx \<phi>Res_Sat_expn_impSubj
  by (clarsimp simp add: \<phi>expns expand; rule R.\<phi>R_get_res_entry[where v=v]; simp)

lemmas \<phi>R_get_res_entry[intro!] = \<phi>R_get_res_entry_frm[where R=1, simplified]

end

subparagraph \<open>share_fiction_for_partial_mapping_resource\<close>

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_get_res_entry_frm[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry key F
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_Hybrid_DL
    \<phi>Res_Spec_expn_R \<phi>Res_Sat_expn_impEx \<phi>Res_Sat_expn_impSubj imp_conjL
  apply (clarsimp simp add: \<phi>expns zero_set_def)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

lemmas \<phi>R_get_res_entry[intro!] = \<phi>R_get_res_entry_frm[where R=1, simplified]

end

paragraph \<open>partial_map_resource2\<close>

definition (in partial_map_resource2) \<comment> \<open>depreciated\<close>
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> ('val \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_get_res_entry k k2 F = \<phi>R_get_res (\<lambda>res.
    case res k k2 of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition (in partial_map_resource2)
  \<phi>R_get_res_entry' :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> 'val proc\<close>
  where \<open>\<phi>R_get_res_entry' k k2 =
    \<phi>R_get_res' \<bind> (\<lambda>res. case \<phi>arg.dest res k k2 of Some v \<Rightarrow> Return (\<phi>arg v) | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>


lemma (in partial_map_resource2) \<phi>R_get_res_entry[intro!]:
  \<open> get res k k2 = Some v
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res_entry k k2 F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry1[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  using \<phi>R_get_res_entry[where n=1, simplified] .


subsubsection \<open>Setters\<close>

definition (in resource) \<phi>R_set_res :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> unit proc\<close>
  where \<open>\<phi>R_set_res F = (\<lambda>res. {Success (\<phi>arg ()) (updt F res)})\<close>

definition (in resource) \<phi>R_set_res' :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> unit proc\<close>
  where \<open>\<phi>R_set_res' F = (\<lambda>res. if updt F res \<in> SPACE
                                then {Success (\<phi>arg ()) (updt F res)}
                                else {Invalid})\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_set_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R * {mk (1(k := u))}) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def
  by (simp add: \<phi>expns "__updt_rule__")

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_set_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k \<mapsto> u) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. (\<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Itself) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Itself) \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def
          expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
          expand_subj[where x=\<open>1(k \<mapsto> u)\<close>, simplified])
  subgoal for r res
    thm R.\<phi>R_set_res[where k=k and res=res]
    by (rule R.\<phi>R_set_res[where k=k and res=res], assumption, simp, assumption) .

declare \<phi>R_set_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_set_res_frm[intro!] = \<phi>R_set_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]
end

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_set_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k \<mapsto> u) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Itself) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Itself) \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def
          expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
          expand_subj[where x=\<open>1(k \<mapsto> u)\<close>, simplified])
  subgoal for r res
    by (rule R.\<phi>R_set_res[where k=k and res=res], assumption, simp, assumption) .

declare \<phi>R_set_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_set_res_frm[intro!] = \<phi>R_set_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]

end


paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_set_res[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> \<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
      \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R * {mk (1(k := 1(k2 := u)))}) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__")

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_set_res"[THEN \<phi>CONSEQ'E0, intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k) m \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k := 1(k2 \<mapsto> v)))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k)
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Itself) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Itself) \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def
                            expand[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close>, simplified]
                            expand_subj[where x=\<open>1(k := 1(k2 \<mapsto> u))\<close>, simplified])
  subgoal for r res
    by (rule R.\<phi>R_set_res, assumption, simp, assumption) .


subsubsection \<open>Dispose\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_dispose_res[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k := None) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := None)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__")

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_dispose_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k := None) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k := None))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Itself) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified])
  subgoal for r res
    by (rule R.\<phi>R_dispose_res, assumption, simp, simp) .

declare \<phi>R_dispose_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_dispose_res_frm[intro!] = \<phi>R_dispose_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]

end

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_dispose_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k := None) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k := None))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Itself) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified])
  subgoal for r res by (rule R.\<phi>R_dispose_res, assumption, simp, simp) .

declare \<phi>R_dispose_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_dispose_res_frm[intro!] = \<phi>R_dispose_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]

end

paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_dispose_res[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := 1)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__")

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_dispose_res"[THEN \<phi>CONSEQ'E0, intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k := 1) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k := f))}
      \<Longrightarrow> P (R.get res) \<and> dom f = dom (R.get res k))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k := 1))
         \<lbrace> to_share o f \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> Itself) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k := f)\<close>, simplified])
  subgoal for r res
    apply (rule R.\<phi>R_dispose_res, assumption, standard, simp)
    subgoal premises prems proof -
      have t1: \<open>dom f = dom (R.get res k)\<close>
        using prems(2) prems(3) by blast
      have t2: \<open>f \<subseteq>\<^sub>m R.get res k\<close>
        using R.raw_unit_assertion_implies' prems(3) by blast
      have t3: \<open>R.get res k = f\<close>
        by (metis (no_types, lifting) map_le_antisym map_le_def t1 t2)
      show ?thesis
        using prems(3) t3 by blast
    qed . .

subsubsection \<open>Allocate\<close>

context mapping_resource begin

definition
    \<phi>R_allocate_res_entry :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> ('key \<Rightarrow> 'ret proc)
                           \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_allocate_res_entry P init F =
    \<phi>R_get_res (\<lambda>res.
    let k = (@k. res k = 1 \<and> P k)
     in \<phi>R_set_res (\<lambda>f. f(k := init))
        \<ggreater> F k
)\<close>

definition
    \<phi>R_allocate_res_entry' :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> 'key proc\<close>
  where \<open>\<phi>R_allocate_res_entry' P init =
    \<phi>R_get_res (\<lambda>res.
    let k = (@k. res k = 1 \<and> P k)
     in \<phi>R_set_res (\<lambda>f. f(k := init))
        \<ggreater> Return (\<phi>arg k)
)\<close>

lemma \<phi>R_set_res_new[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> k \<notin> dom1 (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R * {mk (1(k := u))}) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def
  by (simp add: \<phi>expns "__allocation_rule__")

lemma \<phi>R_allocate_res_entry[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m(k := init) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> (\<And>k res. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := init))} \<s>\<u>\<b>\<j> P k
      \<Longrightarrow> F k res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R
\<Longrightarrow> \<phi>R_allocate_res_entry P init F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_allocate_res_entry_def \<phi>R_get_res_def
  subgoal premises prems proof -
    let ?m = \<open>get res\<close>
    define k' where \<open>k' = (SOME k. ?m k = 1 \<and> P k)\<close>
    have \<open>\<exists>k'. ?m k' = 1 \<and> P k'\<close>
      using get_res_Valid prems(1) prems(4) by blast
    note this[THEN someI_ex]
    then have t1[simp]: \<open>?m k' = 1 \<and> P k'\<close> unfolding k'_def by blast
    show ?thesis
      unfolding k'_def[symmetric]
      apply (simp, rule \<phi>M_RS_WP_SEQ, rule \<phi>R_set_res_new)
      using prems(2) t1 apply blast
      apply (simp add: dom1_def)
      using \<open>\<s>\<t>\<a>\<t>\<e> res \<i>\<s> _\<close> apply this
      by (simp add: prems(3))
  qed .

end

lemma (in identity_fiction_for_partial_mapping_resource) "\<phi>R_allocate_res_entry"[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> m(k \<mapsto> init) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>new. P new \<Longrightarrow> \<p>\<r>\<o>\<c> F new \<lbrace> X \<heavy_comma> init \<Ztypecolon> \<phi> (new \<^bold>\<rightarrow> \<black_circle> Itself) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_allocate_res_entry P (Some init) F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
 apply (clarsimp simp add: \<phi>expns \<phi>Procedure_Hybrid_DL)
  subgoal for r res c
  apply (rule R.\<phi>R_allocate_res_entry[where R="(\<I> INTERP (r * c))"])
  apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp)
  subgoal premises prems for k res'
  apply (rule prems(3)[OF \<open>P _\<close>, THEN spec[where x=r], THEN spec[where x=res'],
              simplified prems, simplified, THEN mp])
    apply (rule exI[where x=\<open>c * mk (1(k \<mapsto> init))\<close>])
    apply rule
    apply (smt (verit, ccfv_threshold) SPACE_mult_homo expand prems(6) prems(7) prems(8) prems(9) sep_disj_commute sep_disj_fiction sep_disj_multD2 sep_mult_commute sep_mult_left_commute)
    apply rule
    using FIC.SPACE_mult_homo prems(5) prems(6) prems(7) prems(8) prems(9) sep_disj_fiction sep_disj_multD2 apply blast
    by (metis Fic_Space_m SPACE_mult_homo identity_fiction.sep_disj_fiction identity_fiction_axioms prems(6) prems(7) prems(8) prems(9) sep_disj_multD2 sep_disj_multI2)
  . .



(*


(*
subsection \<open>Tuple Operations\<close>



subsubsection \<open>Construct Tuple\<close>

definition cons_tup :: "TY list \<Rightarrow> VAL list \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "cons_tup tys vs = (
    let N = length tys in
    \<phi>M_assert (N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (rev (take N vs)) tys)
    \<ggreater> Success (V_tup.mk (rev (take N vs))))"

lemma cons_tup_nil:
  \<open>cons_tup [] = \<phi>M_put_Val (V_tup.mk [])\<close>
  unfolding cons_tup_def \<phi>M_put_Val_def
  by simp

lemma cons_tup_cons:
  \<open>cons_tup (TY#TYs) =
    cons_tup TYs \<ggreater>
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (V_tup.mk [v] * tup)
    ))\<close>
  apply (auto split: list.split
    simp add: cons_tup_def fun_eq_iff pair_forall instr_comp_def bind_def
    \<phi>M_get_Val_def \<phi>M_assert_def \<phi>M_put_Val_def Let_def V_tup_mult)
  apply (metis Suc_le_eq list.sel(1) take_hd_drop)
  apply (metis Cons_nth_drop_Suc Suc_le_eq list.sel(3))
  apply (metis Suc_le_eq drop_all leI list.simps(3))
  apply (metis (no_types, lifting) drop_all leI list.ctr_transfer(1) list.sel(1) list.simps(3) list_all2_Cons2 list_all2_appendI list_all2_rev1 rev.simps(2) take_hd_drop)
  apply (smt (verit, del_insts) Suc_le_eq append1_eq_conv list.sel(1) list_all2_Cons2 rev_eq_Cons_iff take_hd_drop)
  by (simp add: take_Suc_conv_app_nth)

lemma (in \<phi>empty) op_cons_tup_nil:
  \<open> \<p>\<r>\<o>\<c> cons_tup [] \<lbrace> Void \<longmapsto> () \<Ztypecolon> EmptyTuple \<rbrace>\<close>
  unfolding cons_tup_nil by \<phi>reason

lemma (in \<phi>empty) op_cons_tup_cons:
  \<open> \<p>\<r>\<o>\<c> cons_tup TYs \<lbrace> X \<longmapsto> VAL y \<Ztypecolon> Y \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> cons_tup (TY#TYs) \<lbrace> VAL a \<Ztypecolon> A\<heavy_comma> X \<longmapsto> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> Y) \<rbrace>\<close>
  unfolding cons_tup_cons
  apply \<phi>reason apply (rule \<phi>frame0, assumption)
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  apply \<phi>reason apply (simp add: \<phi>expns) by blast


subsubsection \<open>Destruct Tuple\<close>


definition op_dest_tup :: "TY list \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "op_dest_tup tys =
    \<phi>M_getV (\<tau>Tuple tys) V_tup.dest (\<lambda>tup.
    \<lambda>(vs, res). Success (rev tup@vs, res))"

lemma op_dest_tup_nil_expn:
  \<open>op_dest_tup [] = \<phi>M_getV (\<tau>Tuple []) V_tup.dest (\<lambda>_. SKIP)\<close>
  by (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)

lemma op_dest_tup_cons_expn:
  \<open>op_dest_tup (TY#TYs) =
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_assert (\<exists>h tup'. tup = V_tup.mk (h#tup') \<and> h \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (hd (V_tup.dest tup)) \<ggreater>
    \<phi>M_put_Val (V_tup.mk (tl (V_tup.dest tup))) \<ggreater>
    op_dest_tup TYs)\<close>
  apply (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)
  by (metis list.discI list.exhaust_sel list.rel_sel list.sel(1))

lemma (in \<phi>empty) op_dest_tup_nil:
  \<open>\<p>\<r>\<o>\<c> op_dest_tup [] \<lbrace> () \<Ztypecolon> EmptyTuple \<longmapsto> Void \<rbrace> \<close>
  unfolding op_dest_tup_nil_expn by \<phi>reason

lemma (in \<phi>empty) op_dest_tup_cons:
  \<open> \<p>\<r>\<o>\<c> op_dest_tup TYs \<lbrace> VAL y \<Ztypecolon> Y \<longmapsto> X \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_dest_tup (TY#TYs) \<lbrace> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> \<phi>Is_Tuple Y) \<longmapsto> VAL a \<Ztypecolon> A\<heavy_comma> X \<rbrace>\<close>
  unfolding op_dest_tup_cons_expn
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  by (rule \<phi>frame0, assumption)



subsubsection \<open>Accessing Elements\<close>


definition op_get_element :: "nat list \<Rightarrow> TY \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "op_get_element idx TY =
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx) \<ggreater>
    \<phi>M_put_Val (index_value idx v))"

definition op_set_element :: "nat list \<Rightarrow> TY \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "op_set_element idx TY =
    \<phi>M_get_Val (\<lambda>u.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx \<and> u \<in> Well_Type (index_type idx TY)) \<ggreater>
    \<phi>M_put_Val (index_mod_value idx (\<lambda>_. u) v)
  ))"

lemma (in \<phi>empty) op_get_element:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> valid_index TY idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>Aggregate_Getter idx X Y f
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_element idx TY \<lbrace> VAL x \<Ztypecolon> X \<longmapsto> VAL f x \<Ztypecolon> Y \<rbrace> \<close>
  unfolding op_get_element_def \<phi>Aggregate_Getter_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason

lemma (in \<phi>empty) op_set_element:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> valid_index TY idx
\<Longrightarrow> \<phi>Aggregate_Mapper idx X Y f
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> Y) (index_type idx TY)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_element idx TY \<lbrace> VAL x \<Ztypecolon> X\<heavy_comma> VAL y \<Ztypecolon> Y \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> X \<rbrace>\<close>
  unfolding op_set_element_def \<phi>Aggregate_Mapper_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
   apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason


*)

*)

end
