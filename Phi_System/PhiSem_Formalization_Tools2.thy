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


end
