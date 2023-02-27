theory PhiSem_Formalization_Tools
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

definition \<phi>M_getV :: \<open>TY \<Rightarrow> (VAL \<Rightarrow> 'v) \<Rightarrow> VAL \<phi>arg \<Rightarrow> ('v \<Rightarrow> 'y proc) \<Rightarrow> 'y::VALs proc\<close>
  where \<open>\<phi>M_getV TY VDT_dest v F =
    (\<phi>M_assert (\<phi>arg.dest v \<in> Well_Type TY) \<ggreater> F (VDT_dest (\<phi>arg.dest v)))\<close>

definition \<phi>M_caseV :: \<open>(VAL \<phi>arg \<Rightarrow> ('vr,'ret) proc') \<Rightarrow> (VAL \<times> 'vr::FIX_ARITY_VALs,'ret) proc'\<close>
  where \<open>\<phi>M_caseV F = (\<lambda>arg. case arg of \<phi>arg (a1,a2) \<Rightarrow> F (\<phi>arg a1) (\<phi>arg a2))\<close>

subsection \<open>Reasoning for Elementary Constructions\<close>

declare \<phi>SEQ[intro!]

lemma \<phi>M_assert[intro!]:
  \<open>(Inhabited X \<Longrightarrow> P) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_assert P \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace>\<close>
  unfolding \<phi>M_assert_def
  by (rule \<phi>Inhabited; simp; rule)

lemma \<phi>M_assert_True[simp]:
  \<open>\<phi>M_assert True = Return \<phi>V_none\<close>
  unfolding \<phi>M_assert_def by simp

lemma \<phi>M_assert':
  \<open>P \<Longrightarrow> Q (F args) \<Longrightarrow> Q ((\<phi>M_assert P \<ggreater> F) args)\<close>
  unfolding \<phi>M_assert_def bind_def Return_def det_lift_def by simp

lemma \<phi>M_assume[intro!]:
  \<open>(P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (\<phi>M_assume P \<ggreater> F) \<lbrace> X \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_assume_def bind_def Return_def det_lift_def
  by clarsimp

lemma \<phi>M_tail_left:  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_tail_right: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. 1 \<heavy_comma> Y v \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_tail_right_right: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. Y v\<heavy_comma> 1 \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_detail_left[intro!]:  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_detail_right[intro!]: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. 1\<heavy_comma> Y v \<rbrace>\<close> by simp

lemma \<phi>M_getV_raw[intro!]:
   \<open>(v \<in> (x \<Ztypecolon> A) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_raw VDT_dest (\<phi>arg v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (\<phi>arg v) A \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding \<phi>M_getV_raw_def Premise_def
  by (clarsimp simp add: \<phi>expns norm_precond_conj)

declare \<phi>M_getV_raw[where X=1, simplified, intro!]

lemma \<phi>M_getV[intro!]:
   \<open>(v \<in> (x \<Ztypecolon> A) \<Longrightarrow> <\<phi>expn> v \<in> Well_Type TY)
\<Longrightarrow> (v \<in> (x \<Ztypecolon> A) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV TY VDT_dest (\<phi>arg v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (\<phi>arg v) A \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding \<phi>M_getV_def Premise_def
  by (clarsimp simp add: \<phi>expns norm_precond_conj)

declare \<phi>M_getV[where X=1, simplified, intro!]

lemma \<phi>M_caseV[intro!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F va vb \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_caseV F (\<phi>V_pair va vb) \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding \<phi>M_caseV_def \<phi>V_pair_def by simp


subsection \<open>Elementary Constructions for Reasoning Fictions\<close>

definition \<phi>Res_Spec :: \<open>rassn \<Rightarrow> rassn\<close>
  where \<open>\<phi>Res_Spec P = (Valid_Resource \<inter> P)\<close>

lemma \<phi>Res_Spec_0[iff]:
  \<open>\<phi>Res_Spec {} = {}\<close>
  \<open>\<phi>Res_Spec 0 = {}\<close>
  unfolding \<phi>Res_Spec_def by (simp add: zero_set_def)+

lemma \<phi>Res_Spec_1[iff]:
  \<open>\<phi>Res_Spec 1 = 1\<close>
  unfolding \<phi>Res_Spec_def by (simp add: set_eq_iff; blast)

lemma \<phi>Res_Spec_mult_homo:
  \<open>\<phi>Res_Spec (A * B) = \<phi>Res_Spec A * \<phi>Res_Spec B\<close>
  unfolding \<phi>Res_Spec_def
  by (clarsimp simp add: set_eq_iff times_set_def; rule; clarsimp simp add: Valid_Resource_mult_homo; blast)

lemma \<phi>Res_Spec_subj[iff]:
  \<open> \<phi>Res_Spec (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (\<phi>Res_Spec S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<close>
  unfolding \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Spec_subj_\<S>:
  \<open> P
\<Longrightarrow> res \<subseteq> \<S> S E
\<Longrightarrow> res \<subseteq> (\<S> (\<lambda>v. S v \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) E)\<close>
  by (clarsimp simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Spec_ex[iff]:
  \<open> \<phi>Res_Spec (ExSet S) = (\<exists>*x. \<phi>Res_Spec (S x))\<close>
  unfolding \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Spec_ex_\<S>:
  \<open> res \<subseteq> \<S> (S x) E
\<Longrightarrow> res \<subseteq> (\<S> (\<lambda>v. (\<exists>*x. S x v)) E)\<close>
  apply (clarsimp simp add: \<phi>expns set_eq_iff subset_iff)
  subgoal for x by (cases x; clarsimp simp add: \<phi>expns set_eq_iff subset_iff; blast) .

lemma \<phi>INTERP_RES_\<phi>Res_Spec:
  \<open>res \<in> INTERP_RES fic \<longleftrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP fic) \<and> Fic_Space fic\<close>
  unfolding In_INTERP_RES \<phi>Res_Spec_def by simp blast

lemma \<phi>Procedure_\<phi>Res_Spec:
  \<open> (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> P \<longmapsto> Q \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E )
\<longleftrightarrow> (\<forall>r res. res \<in> \<phi>Res_Spec (\<I> INTERP (r * p) \<^bold>s\<^bold>u\<^bold>b\<^bold>j p. p \<in> P \<and> Fic_Space r \<and> Fic_Space p \<and> r ## p)
      \<longrightarrow> f res \<subseteq> \<S> (\<lambda>v. \<phi>Res_Spec (\<I> INTERP (r * q) \<^bold>s\<^bold>u\<^bold>b\<^bold>j q. q \<in> Q v \<and> Fic_Space r \<and> Fic_Space q \<and> r ## q))
                    (\<lambda>v. \<phi>Res_Spec (\<I> INTERP (r * e) \<^bold>s\<^bold>u\<^bold>b\<^bold>j e. e \<in> E v \<and> Fic_Space r \<and> Fic_Space e \<and> r ## e)))\<close>
  apply rule
   apply (unfold \<phi>Procedure_alt INTERP_SPEC \<phi>Res_Spec_def subset_iff)
   apply (clarsimp simp add: times_set_def \<phi>expns In_INTERP_RES)
  thm In_INTERP_RES
  subgoal premises prems for r res s c proof-
    have t1: \<open>(\<exists>fic. (\<exists>y. fic = r * y \<and> y \<in> P \<and> r ## y) \<and> res \<in> Valid_Resource \<and> Fic_Space fic \<and> res \<in> \<I> INTERP fic)\<close>
      using Fic_Space_Un prems by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=res], THEN spec[where x=r], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> f res\<close>])
      apply (cases s; clarsimp simp add: \<phi>expns In_INTERP_RES Fic_Space_Un)
      apply force
      using Fic_Space_Un by blast
  qed
  apply (clarsimp simp add: times_set_def \<phi>expns In_INTERP_RES)
  subgoal premises prems for res r s c proof-
    have t1: \<open>res \<in> Valid_Resource \<and> (\<exists>c. res \<in> \<I> INTERP (r * c) \<and> c \<in> P \<and> Fic_Space r \<and> Fic_Space c \<and> r ## c)\<close>
      using prems Fic_Space_Un by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=r], THEN spec[where x=res], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> _\<close>])
      apply (cases s; simp add: \<phi>expns In_INTERP_RES)
      using Fic_Space_Un apply blast
      using Fic_Space_Un by blast
  qed .

lemma \<phi>Res_Spec_expn_R:
  \<open>\<phi>Res_Spec (\<I> INTERP (r * p) \<^bold>s\<^bold>u\<^bold>b\<^bold>j p. p \<in> (R \<heavy_comma> X) \<and> Fic_Space r \<and> Fic_Space p \<and> r ## p)
 = \<phi>Res_Spec (\<I> INTERP (r * u * x) \<^bold>s\<^bold>u\<^bold>b\<^bold>j u x. u \<in> R \<and> x \<in> X \<and> Fic_Space (r * u) \<and> Fic_Space x
                                           \<and> r ## u \<and> (r * u) ## x)\<close>
  unfolding set_eq_iff
  apply (clarsimp simp add: \<phi>expns; rule; clarify)
  apply (metis Fic_Space_Un sep_disj_multD1 sep_disj_multI1 sep_mult_assoc')
  by (metis Fic_Space_Un sep_disj_multD2 sep_disj_multI2 sep_mult_assoc)

lemma \<phi>Res_Spec_expn_impEx:
  \<open>(x \<in> \<phi>Res_Spec (ExSet A) \<longrightarrow> P) \<longleftrightarrow> (\<forall>a. x \<in> \<phi>Res_Spec (A a) \<longrightarrow> P)\<close>
  by (simp add: ExSet_def \<phi>Res_Spec_def)

lemma \<phi>Res_Spec_expn_impSubj:
  \<open>(x \<in> \<phi>Res_Spec (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j B) \<longrightarrow> P) \<longleftrightarrow> (B \<longrightarrow> x \<in> \<phi>Res_Spec A \<longrightarrow> P)\<close>
  by (metis Subjection_expn \<phi>Res_Spec_subj)


paragraph \<open>Weakest Precondition Transformer for \<phi>Res_Spec\<close>

lemma \<phi>M_RS_WP_SEQ[intro!]:
  \<open> F res \<subseteq> \<S> P E
\<Longrightarrow> (\<And>ret res. res \<in> P ret \<Longrightarrow> G ret res \<subseteq> \<S> Q E)
\<Longrightarrow> (F \<bind> G) res \<subseteq> \<S> Q E\<close>
  unfolding bind_def subset_iff
  apply clarsimp subgoal for s s'
    by (cases s'; simp; cases s; clarsimp ; blast) .


section \<open>Predefined Resource Snippet\<close>

subsection \<open>Minimal Resource\<close>

type_synonym 'T resource_entry = "(RES_N, RES, 'T) Virtual_Datatype.Field"
type_synonym 'T fiction_entry = "(FIC_N, FIC, 'T) Virtual_Datatype.Field"

locale resource =
  resource_kind entry for entry :: "'T::sep_algebra resource_entry"
+ fixes Valid :: \<open>'T set\<close>
  assumes Valid_1: \<open>1 \<in> Valid\<close>
  assumes Resource_Validator[simp]: \<open>Resource_Validator name = inject ` Valid\<close>
begin

lemma \<r>_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    clean res \<in> Valid_Resource \<and> (\<exists>m. res name = inject m \<and> m \<in> Valid)\<close>
  by (subst split, simp add: Valid_Resource_def times_fun_def image_iff Valid_1, blast)

lemma \<r>_valid_split': \<open>
  NO_MATCH (clean res') res
\<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow> clean res \<in> Valid_Resource \<and> (\<exists>m. res name = inject m \<and> m \<in> Valid)\<close>
  using \<r>_valid_split .

lemma get_res_valid_raw:
  \<open> res \<in> Valid_Resource
\<Longrightarrow> get res \<in> Valid\<close>
  unfolding Valid_Resource_def
  apply simp
  subgoal premises prems
    using prems(1)[THEN spec[where x=name], simplified Resource_Validator]
    by fastforce .

lemma get_res_Valid:
  \<open> res \<in> \<phi>Res_Spec S
\<Longrightarrow> (get res) \<in> Valid\<close>
  unfolding \<phi>Res_Spec_def by (clarsimp simp add: \<r>_valid_split')


definition \<open>raw_basic_fiction I = Interp (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x })\<close>
lemma raw_basic_fiction_\<I>:
  "\<I> (raw_basic_fiction I) = (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x})"
  unfolding raw_basic_fiction_def
  by (rule Interp_inverse) (clarsimp simp add: Interpretation_def one_set_def)

lemma \<F>_itself_expn[\<phi>expns]:
  \<open>R2 ## x
\<Longrightarrow> \<phi>Res_Spec (\<I> (raw_basic_fiction \<F>_it) (R2 * x))
  = \<phi>Res_Spec (\<I> (raw_basic_fiction \<F>_it) R2) * \<phi>Res_Spec {mk x}\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: \<phi>expns raw_basic_fiction_\<I> prj.homo_mult)
  apply (rule; clarify)
   apply (simp add: mk_homo_mult sep_mult_assoc')
  using Valid_Resource_mult_homo sep_disj_mk apply blast
  using Valid_Resource_mult_homo inj.homo_mult by force

lemma implies_part:
  \<open> res \<in> R * \<phi>Res_Spec {mk x}
\<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L get res\<close>
  unfolding \<phi>Res_Spec_def join_sub_def times_set_def apply clarsimp
  using get_homo_mult by fastforce

end


subsection \<open>Fictions\<close>

subsubsection \<open>Basic Fiction\<close>

locale basic_fiction =
   R: resource Res Valid
+  fictional_project_inject INTERPRET Fic \<open>R.raw_basic_fiction I\<close>
for Valid :: "'T::sep_algebra set"
and I :: "('U::sep_algebra, 'T) interp"
and Res :: "'T resource_entry"
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

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp

lemma [\<phi>reason 1300 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = 1 @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp


(*
lemma [\<phi>reason 1500 for \<open>(x \<Ztypecolon> \<phi> \<circle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action (?Act::?'act::simplification action)\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (() \<Ztypecolon> \<circle>) @action Act\<close>
  for Act :: \<open>'act::simplification action\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None
  by (simp add: implies_refl) *)

paragraph \<open>Reasoning Rules\<close>

lemma \<phi>_cast:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi> U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns)

lemma \<phi>_Structural_Extract:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W) P\<close>
  unfolding Structural_Extract_def
  by (simp add: \<phi>Prod_expn'[symmetric] \<phi>_Prod \<phi>_cast)

declare \<phi>_Structural_Extract[THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> \<phi> U') (w' \<Ztypecolon> \<phi> W') (x' \<Ztypecolon> \<phi> T') (r' \<Ztypecolon> \<phi> R') P') \<and> P)\<close>
  unfolding Morphism_def Action_Tag_def
  by (blast intro: \<phi>_Structural_Extract[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)

lemma ToSA_by_structural_extraction:
  " Structure_Info U Q
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y Q' : Q
\<Longrightarrow> (Q' \<Longrightarrow> \<r>CALL Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W P2))
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2 \<heavy_comma> \<blangle> W \<brangle> \<^bold>a\<^bold>n\<^bold>d P1
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> \<phi> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>a\<^bold>n\<^bold>d P1 \<and> P2"
  unfolding Premise_def FOCUS_TAG_def Structural_Extract_def Simplify_def Try_def \<r>Call_def
  \<medium_left_bracket> premises SI and Q and SE and A
  have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
  ;;  A[THEN implies_right_prod]
     SE[OF \<open>Q'\<close>]
  \<medium_right_bracket> using \<phi> by simp .

lemma ToSA_by_structural_extraction__reverse_morphism:
  " Structure_Info U Q
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y Q' : Q
\<Longrightarrow> (Q' \<Longrightarrow> \<r>CALL Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W
             (Automatic_Morphism RP2 (Structural_Extract (x' \<Ztypecolon> \<phi> T') W' (y' \<Ztypecolon> \<phi> U') R1' P2') \<and> P2)))
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2 \<heavy_comma> \<blangle> W \<brangle> \<^bold>a\<^bold>n\<^bold>d (Automatic_Morphism RP1 (R2'\<heavy_comma> \<blangle> W' \<brangle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A' \<^bold>a\<^bold>n\<^bold>d P1') \<and> P1)
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> \<phi> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>a\<^bold>n\<^bold>d
      (Automatic_Morphism (RP2 \<and>\<^sub>\<r> RP1) (R2'\<heavy_comma> R1'\<heavy_comma> \<blangle> x' \<Ztypecolon> \<phi> T' \<brangle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A'\<heavy_comma> y' \<Ztypecolon> \<phi> U' \<^bold>a\<^bold>n\<^bold>d P1' \<and> P2')
          \<and> P1 \<and> P2)"
  unfolding Premise_def FOCUS_TAG_def Structural_Extract_def Simplify_def
            Morphism_def Compact_Antecedent_def Try_def \<r>Call_def
  \<medium_left_bracket> premises SI and Q and SE and A
  have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
  ;; A[THEN implies_right_prod]
     SE[OF \<open>Q'\<close>]
  \<medium_right_bracket> apply (simp add: \<phi>)
    \<medium_left_bracket>
    have A : \<open>R2' \<heavy_comma> W' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A' \<^bold>a\<^bold>n\<^bold>d P1'\<close> using \<phi>_previous \<open>RP2 \<and> RP1\<close> by simp
    have SE: \<open>(R1' \<heavy_comma> x' \<Ztypecolon> \<phi> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s W' \<heavy_comma> y' \<Ztypecolon> \<phi> U' \<^bold>a\<^bold>n\<^bold>d P2')\<close> using \<phi>_previous \<open>RP2 \<and> RP1\<close> by simp
    ;; SE A[THEN implies_right_prod]
  \<medium_right_bracket>. . .


lemma ToSA_skip [\<phi>reason 1200 except \<open> _ \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>a\<^bold>n\<^bold>d _\<close> ]:
  " R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R'\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> R \<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Action_Tag_def FOCUS_TAG_def split_paired_All Action_Tag_def
  by (metis ab_semigroup_mult_class.mult_ac(1) implies_left_prod mult.commute)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi> U \<^bold>a\<^bold>n\<^bold>d P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def using \<phi>_cast .

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P @action to Target
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi> U \<^bold>a\<^bold>n\<^bold>d P @action to Target \<close>
  unfolding Action_Tag_def using \<phi>_cast .


lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> \<phi> T) \<close>
  unfolding \<r>Clean_def Imply_def apply (simp add: \<phi>expns)
  using mk_homo_one by blast

lemma [\<phi>reason 1200 for \<open>If ?P (\<phi> ?T) (\<phi> ?U) = (\<phi> ?Z) @action branch_convergence\<close>]:
  \<open> If P T U = Z @action branch_convergence
\<Longrightarrow> If P (\<phi> T) (\<phi> U) = (\<phi> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by fastforce

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>(\<phi> (ExTyp T)) = (\<exists>\<phi> c. \<phi> (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (\<phi> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi> T) = (x' \<Ztypecolon> \<phi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>\<phi>_simp_cong ("x \<Ztypecolon> \<phi> T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>_simp_cong} ctxt)
\<close>

paragraph \<open>Synthesis for moving\<close>

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse (\<phi> ?T) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (\<phi> T) (\<lambda>_. x \<Ztypecolon> \<phi> T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

(* lemma [\<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S1 \<longmapsto> \<lambda>ret. ?S2\<heavy_comma>  \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E\<close>]:
  \<open> SUBGOAL G G'
\<Longrightarrow> S1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S2\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle>
\<Longrightarrow> SOLVE_SUBGOAL G'
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> S1 \<longmapsto> \<lambda>_. S2\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<rbrace>\<close>
  unfolding FOCUS_TAG_def Synthesis_def Action_Tag_def
  using \<phi>__Return_rule__ view_shift_by_implication by blast *)

end


subsubsection \<open>Permission Fiction\<close>

locale permission_fiction =
   R: resource Res Valid
+  share: perm_functor perm_functor
+  fictional_project_inject INTERPRET Fic
      \<open>R.raw_basic_fiction (\<F>_functional perm_functor)\<close>
for Valid :: "'T::sep_algebra set"
and perm_functor :: \<open>'T \<Rightarrow> 'U::{share_sep_disj,share_module_sep,sep_algebra}\<close>
and Res :: "'T resource_entry"
and Fic :: "'U fiction_entry"
begin

sublocale basic_fiction Valid \<open>\<F>_functional perm_functor\<close> ..

lemma sep_disj_fiction:
  \<open> Fic_Space r
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }
\<Longrightarrow> r ## mk (perm_functor x)\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            share.sep_mult_strip_011 R.\<r>_valid_split'
            R.mult_strip_inject_011 interp_split' sep_disj_get_name_eq[symmetric]
            simp del: sep_disj_get_name_eq)
  using sep_disj_multD2 by force

lemma expand_subj:
  \<open> Fic_Space r
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_functor x)) \<^bold>s\<^bold>u\<^bold>b\<^bold>j r ## mk (perm_functor x))
  = \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify, rule)
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            share.sep_mult_strip_011 \<phi>Res_Spec_def R.\<r>_valid_split'
            R.mult_strip_inject_011 interp_split' prj.homo_mult)
  subgoal for res_r a r'
    apply (rule exI[where x=\<open>res_r * R.mk a\<close>]; rule)
    apply (metis R.inj.homo_mult R.sep_disj_mk fun_1upd_homo_right1 sep_mult_assoc')
    by (metis R.get_homo_mult R.proj_inj R.sep_disj_get_name_eq fun_upd_same sep_disj_multD1 sep_disj_multI1)

  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns \<phi>Res_Spec_def R.\<r>_valid_split'
        R.mult_strip_inject_011 interp_split' sep_mult_assoc prj.homo_mult)
  subgoal premises prems for res_r a y proof -
    have t1[simp]: \<open>y ## x\<close>
      using prems(5) prems(7) sep_disj_multD2 by force

    show ?thesis
      apply rule
      apply (rule exI[where x=\<open>a\<close>], rule exI[where x=\<open>R.mk (y * x)\<close>])
      apply (metis R.inj.homo_mult fun_1upd_homo prems(5) prems(6) prems(7) sep_disj_multI2 share.homo_mult t1)
      by (metis prems(8) sep_disj_get_name_eq share.sep_disj_homo_semi t1)

  qed .

lemma expand:
  \<open>Fic_Space r
\<Longrightarrow> r ## mk (perm_functor x)
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_functor x))) =
    \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

lemma expand_conj:
  \<open> Fic_Space r
\<Longrightarrow> a \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_functor x))) \<and> r ## mk (perm_functor x)
\<longleftrightarrow> a \<in> \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, OF prems(1), unfolded set_eq_iff]
      by (simp add: \<phi>expns) .



lemma partial_implies_raw:
  \<open> Fic_Space r
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (share n (perm_functor x))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (share n (perm_functor x))))
\<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L R.get res\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            \<phi>Res_Spec_def R.\<r>_valid_split' R.mult_strip_inject_011
            R.prj.homo_mult interp_split' prj.homo_mult)
  apply (cases \<open>n \<le> 1\<close>)
  apply (metis join_sub_def join_sub_ext_left sep_disj_get_name_eq share.join_sub_share_join_sub_whole)
  subgoal premises prems for u y a proof -
    have t0: \<open>1 / n * n = 1\<close> using prems(12) by force
    have t1: \<open>1 / n \<le> 1 \<and> 0 < 1 / n\<close> using prems(12) by force
    have t2: \<open>share (1/n) (share n (perm_functor x)) \<preceq>\<^sub>S\<^sub>L share n (perm_functor x)\<close>
      by (simp add: order_less_imp_le prems(2) share.\<psi>_self_disj share_sub t1)
    then have t3: \<open>perm_functor x \<preceq>\<^sub>S\<^sub>L share n (perm_functor x)\<close>
      using share_share_not0
      by (metis prems(2) share_left_one t0 t1)
    then show ?thesis
      by (metis join_sub_ext_left prems(11) prems(3) prems(9) sep_disj_get_name_eq share.homo_join_sub)
  qed .

paragraph \<open>Reasoning Rules\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end





subsubsection \<open>Identity Fiction\<close>

locale identity_fiction =
   R: resource Res
+  fictional_project_inject INTERPRET Fic \<open>R.raw_basic_fiction \<F>_it\<close>
for Res :: "'T::sep_algebra resource_entry"
and Fic :: "'T fiction_entry"
begin

sublocale basic_fiction where I = \<open>\<F>_it\<close> ..

lemma sep_disj_fiction:
  \<open> Fic_Space r
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }
\<Longrightarrow> r ## mk x\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            \<phi>Res_Spec_def R.\<r>_valid_split'
            R.mult_strip_inject_011 interp_split'
            sep_disj_get_name_eq[symmetric]
            simp del: sep_disj_get_name_eq)
  using sep_disj_multD2 by force

lemma expand_subj:
  \<open> Fic_Space r
\<Longrightarrow> (\<phi>Res_Spec (\<I> INTERP (r * mk x)) \<^bold>s\<^bold>u\<^bold>b\<^bold>j r ## mk x) = \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify; rule; clarsimp simp add: \<phi>expns R.raw_basic_fiction_\<I> interp_split' prj.homo_mult)
  apply (simp add: R.mk_homo_mult)
  using R.sep_disj_mk sep_disj_get_name_eq sep_disj_multD1 sep_disj_multI1 sep_mult_assoc' apply blast
  apply (simp add: R.mk_homo_mult[symmetric] sep_mult_assoc)
  by (metis R.mk_homo_mult R.sep_disj_mk sep_disj_get_name_eq sep_disj_multD2 sep_disj_multI2)

lemma expand:
  \<open> Fic_Space r
\<Longrightarrow> r ## mk x
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk x)) = \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

declare ToSA_by_structural_extraction
   [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
   [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end


subsection \<open>Nonsepable Mono-Resource\<close>
  \<comment> \<open>The resource non-sepable and having type shape \<^typ>\<open>'a::nonsepable_semigroup option\<close>\<close>

locale nonsepable_mono_resource =
  resource entry \<open>{None} \<union> Some ` nonsepable ` Valid\<close>
for entry :: "'T nonsepable option resource_entry"
and Valid :: "'T set"
begin

definition fiction_agree
  where \<open>fiction_agree = raw_basic_fiction (\<F>_optionwise \<F>_agree)\<close>

end


subsubsection \<open>Interp Agreement\<close>

locale agreement_fiction_for_nosepable_mono_resource =
   R: nonsepable_mono_resource Res Valid
+  fictional_project_inject INTERPRET Fic \<open>R.fiction_agree\<close>
for Valid :: "'T set"
and Res :: "'T nonsepable option resource_entry"
and Fic :: "'T nonsepable agree option fiction_entry"
begin

sublocale basic_fiction \<open>{None} \<union> Some ` nonsepable ` Valid\<close>
  \<open>\<F>_optionwise \<F>_agree\<close>
  by (standard; simp add: R.fiction_agree_def)

lemma partial_implies:
  \<open> Fic_Space r
\<Longrightarrow> r ## mk (Some (agree (nonsepable x)))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Some (agree (nonsepable x)))))
\<Longrightarrow> R.get res = Some (nonsepable x)\<close>
  unfolding \<phi>Res_Spec_def apply (clarsimp simp add: interp_split'
     R.fiction_agree_def R.raw_basic_fiction_\<I> \<phi>expns R.\<r>_valid_split'
     R.mult_strip_inject_011 R.prj.homo_mult \<F>_optionwise_\<I> image_iff Bex_def
     \<F>_agree_def prj.homo_mult)
  apply (cases \<open>get r\<close>; simp)
  subgoal for u y a aa
    apply (cases aa; simp)
    subgoal premises prems for xa proof -
      have \<open>get r ## Some (agree (nonsepable x))\<close>
        by (simp add: prems(2))
      from this [unfolded \<open>get r = _\<close>, simplified]
      show ?thesis .
    qed . .

lemma double:
  \<open>{mk x |x. P x} \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s {mk x |x. P x} * {mk x |x. P x}\<close>
  unfolding Imply_def
  apply (clarsimp simp add: \<phi>expns mk_homo_mult[symmetric])
  subgoal for x'
    apply (rule exI[where x=\<open>mk x'\<close>], rule exI[where x=\<open>mk x'\<close>])
    by (cases x'; simp add: mk_homo_mult[symmetric]) .

lemma contract:
  \<open>{mk x |x. P x} * {mk x |x. P x} \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s {mk x |x. P x} \<close>
  unfolding Imply_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for x y by (cases x; cases y; simp add: mk_homo_mult[symmetric]) .

paragraph \<open>\<phi>-Type\<close>

abbreviation \<open>\<phi>_ag T \<equiv> \<phi> (Agreement (Nonsepable T))\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

lemma \<phi>_double_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nonsepable v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: double)
qed

lemma \<phi>_contract_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nonsepable v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: contract)
qed

end



subsection \<open>Resources based on Mapping\<close>

locale mapping_resource =
  resource entry
for entry :: "('key \<Rightarrow> 'val::sep_algebra) resource_entry"
begin

lemma "__new_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> k \<notin> dom1 (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> updt (\<lambda>f. f(k := u)) res
       \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := u))}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
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
        by (metis fun_1upd_homo_right1 prems(5) proj_inj sep_disj_get_name_eq t2 t3)
    }
    then show ?thesis
      using prems(2) prems(4) by blast
  qed .

end

subsection \<open>One Level Parital Mapping\<close>

subsubsection \<open>Locale for Resource\<close>

locale partial_map_resource =
  mapping_resource Valid entry
for Valid :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) set"
and entry :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k \<mapsto> any))}
\<Longrightarrow> updt (\<lambda>f. f(k := u)) res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := u))}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          prj.homo_mult times_fun_upd )
  apply (clarsimp simp add: sep_disj_partial_map_upd
          nonsepable_semigroup_sepdisj_fun mk_homo_mult)
  subgoal premises prems for x aa proof -
    have t1: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(8))
    have t2: \<open>clean x ## (mk aa * mk (1(k := u)))\<close>
      by (simp add: fun_1upd_homo)
    show ?thesis
      by (metis nonsepable_semigroup_sepdisj_fun prems(6) prems(9) sep_disj_mk sep_disj_multI1 sep_mult_assoc' t1 t2)
  qed .

lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k \<mapsto> any))}
\<Longrightarrow> updt (\<lambda>f. f(k := None)) res \<in> \<phi>Res_Spec R\<close>
  using "__updt_rule__"[where u=None, simplified, simplified,
            simplified, simplified one_set_def[symmetric], simplified] .

abbreviation perm_functor :: \<open>('key \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'val share option)\<close>
  where \<open>perm_functor \<equiv> (o) to_share\<close>
abbreviation \<open>share_fiction \<equiv> raw_basic_fiction (\<F>_functional perm_functor)\<close>

(* lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> 1 \<Znrres> v))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k \<mapsto> v)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011)
  subgoal premises prems for res_r y a r
    apply (insert \<open>a * _ = _\<close>[unfolded to_share_strip_011[where b=\<open>1(k \<mapsto> v)\<close>, simplified, OF \<open>a ## _\<close>]])
    apply (clarsimp simp add: times_fine'[symmetric] mk_homo_mult mult.assoc[symmetric])
    using prems(3) by blast
  subgoal premises prems for res_r a r proof -
    have t1[simp]: \<open>a ## 1(k \<mapsto> v)\<close>
      by (metis prems(6) prems(7) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
    show ?thesis
    apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine')
      apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k \<mapsto> v)))"], simp add: prems)
      by (metis (no_types, lifting) map_option_o_map_upd t1 to_share_funcomp_1 to_share_funcomp_sep_disj_I to_share_strip_011)
  qed .


lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> n \<Znrres> v))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011
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
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k \<mapsto> v))}
\<Longrightarrow> get res k = Some v\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011
      prj.homo_mult sep_disj_fun_def times_fun)
  by (metis (mono_tags, lifting) sep_disj_option_nonsepable(1) sep_mult_commute times_option(2))


end

subsubsection \<open>Identity Fiction\<close>

locale identity_fiction_for_partial_mapping_resource =
   R: partial_map_resource Valid Res
+  fictional_project_inject INTERPRET Fic \<open>R.raw_basic_fiction \<F>_it\<close>
for Valid :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) set"
and Res :: "('key \<Rightarrow> 'val option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val option) fiction_entry"
begin

sublocale identity_fiction Valid Res Fic ..

end


subsubsection \<open>Permission Fiction\<close>

locale share_fiction_for_partial_mapping_resource =
   R: partial_map_resource Valid Res
+  fictional_project_inject INTERPRET Fic \<open>R.share_fiction\<close>
for Valid :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) set"
and Res :: "('key \<Rightarrow> 'val option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val share option) fiction_entry"
begin

sublocale permission_fiction Valid \<open>R.perm_functor\<close> by standard blast

lemma expand:
  \<open>Fic_Space r
\<Longrightarrow> r ## mk (R.perm_functor x)
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (R.perm_functor x))) =
    \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

lemma partial_implies:
  \<open> Fic_Space r
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k \<mapsto> Share n v))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k \<mapsto> Share n v))))
\<Longrightarrow> R.get res k = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k \<mapsto> v)\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, ccfv_threshold) fun_split_1 fun_upd_same join_sub_def one_option_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep)

lemma partial_implies'[simp]:
  assumes FS: \<open>Fic_Space r\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k \<mapsto> Share n v))\<close>
    and A: \<open>res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k \<mapsto> Share n v))))\<close>
  shows \<open>R.get res k = Some v\<close>
proof -
  from partial_implies[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

(* lemma VS_merge_ownership_identity:
  \<open> na + nb \<le> 1
\<Longrightarrow> x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<phi> (share.\<phi> (na + nb) Identity)\<close>
  by (rule VS_merge_ownership; simp add: \<phi>expns)

lemma VS_split_ownership_identity:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (0 < n \<longrightarrow> na + nb = n \<and> 0 < na \<and> 0 < nb)
\<Longrightarrow> x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity)\<close>
  by (rule VS_split_ownership; simp add: \<phi>expns sep_disj_fun_def share_fun_def; clarify)
  (* subgoal premises prems for a
    by (insert \<open>\<forall>_. _\<close>[THEN spec[where x=a]], cases \<open>x a\<close>; simp add: share_All prems) . *)


lemma VS_divide_ownership:
  \<open>FIX x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity)\<close>
  unfolding Fix_def
  by (rule VS_split_ownership_identity; simp add: Premise_def)
*)
end

locale share_fiction_for_partial_mapping_resource_nonsepable =
  share_fiction_for_partial_mapping_resource
    Valid Res Fic
for Valid :: "('key \<Rightarrow> 'val nonsepable option) set"
and Res :: "('key \<Rightarrow> 'val nonsepable option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val nonsepable share option) fiction_entry"
begin

lemma \<phi>nonsepable_normalize:
  \<open>(x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some (Nonsepable Identity)))))
 = (nonsepable x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some Identity))))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

end



subsection \<open>Two Level Parital Mapping\<close>

definition \<open>map_fun_at g k f = (\<lambda>x. if x = k then g (f x) else f x)\<close>

lemma map_fun_at_1[simp]: \<open>map_fun_at g k 1 = 1(k := g 1)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp

lemma map_fun_at_const[simp]:
  \<open>map_fun_at (\<lambda>_. u) k f = f(k := u)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp


subsubsection \<open>Locale of Resources\<close>

locale partial_map_resource2 =
  mapping_resource Valid entry
for Valid :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) set"
and entry :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> updt (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
       \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 := u)))}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          prj.homo_mult times_fun_upd)
  subgoal premises prems for x aa proof -
    have [simp]: \<open>aa k k2 = None\<close>
      by (metis (mono_tags, lifting) fun_upd_same prems(9) sep_disj_fun sep_disj_fun_nonsepable(2))
    then have [simp]:
        \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (aa * 1(k := 1(k2 \<mapsto> any)))
            = aa * 1(k := 1(k2 := u))\<close>
      unfolding map_fun_at_def fun_eq_iff times_fun_def
      by simp
    have t1[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(8))
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
      using prems(6) t4 by blast
  qed .


lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in> Valid)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := any))}
\<Longrightarrow> updt (\<lambda>f. f(k := 1)) res \<in> \<phi>Res_Spec R\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          prj.homo_mult times_fun_upd )
  subgoal premises prems for x aa proof -
    have \<open>dom (aa k) = {}\<close>
      by (metis Un_Int_eq(3) dom_mult fun_upd_same prems(10) prems(2) sep_disj_fun sep_disj_partial_map_disjoint)
    then have t1[simp]: \<open>(aa * 1(k := any))(k := 1) = aa\<close>
      by (smt (verit, del_insts) Diff_iff dom1_upd dom_1 dom_eq_empty_conv fun_split_1_not_dom1 fun_upd_triv fun_upd_upd insertCI)
    have t2[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(9))
    show ?thesis
      using prems(1) prems(3) prems(5) prems(7) t1 by force
  qed .

abbreviation perm_functor :: \<open>('key \<Rightarrow> 'key2 \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option)\<close>
  where \<open>perm_functor \<equiv> (o) ((o) to_share)\<close>
abbreviation \<open>share_fiction \<equiv> raw_basic_fiction (\<F>_functional perm_functor)\<close>

(*depreciated!*)
(*lemma share_fiction_expn_full':
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := to_share o f))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := f)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011 times_fun)
  subgoal premises prems for res_r y a r
    apply (insert \<open>\<forall>x. a x * _ = _\<close>[THEN spec[where x=k], simplified,
          unfolded to_share_strip_011[where b=f, simplified,
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
        by (smt (verit, best) fun_split_1 fun_upd_def fun_upd_same map_option_o_map_upd prems(4) sep_disj_fun t1 t2 times_fun to_share_funcomp_1 to_share_strip_011)
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
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011
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
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k := 1(k2 \<mapsto> v)))}
\<Longrightarrow> get res k k2 = Some v\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011
      prj.homo_mult sep_disj_fun_def times_fun)
  by (metis (full_types) fun_upd_same sep_disj_option_nonsepable(1) times_option(3))

lemma raw_unit_assertion_implies':
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k := f))}
\<Longrightarrow> f \<subseteq>\<^sub>m get res k\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011)
  subgoal premises prems for x a proof -
    have t1[simp]: \<open>inject a ## inject (1(k := f))\<close>
      by (simp add: prems(7))
    show ?thesis apply (clarsimp simp add: prj.homo_mult[OF t1] sep_disj_fun_def times_fun map_le_def)
      by (metis fun_upd_same mult_1_class.mult_1_right one_option_def prems(7) sep_disj_fun sep_disj_option_nonsepable(1) sep_mult_commute)
  qed .

lemma raw_unit_assertion_implies''[simp]:
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k := f))}
\<Longrightarrow> k2 \<in> dom f
\<Longrightarrow> get res k k2 = f k2\<close>
  using raw_unit_assertion_implies'[unfolded map_le_def]
  by simp

end

subsubsection \<open>Permission Fiction\<close>

locale share_fiction_for_partial_mapping_resource2 =
   R: partial_map_resource2 Valid Res
+  fictional_project_inject INTERPRET Fic \<open>R.share_fiction\<close>
for Valid :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) set"
and Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val option) resource_entry"
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option) fiction_entry"
begin

sublocale permission_fiction Valid \<open>R.perm_functor\<close> by standard  blast

lemma [simp]:
  \<open>R.perm_functor (1(k := f)) = 1(k := to_share o f)\<close>
  unfolding fun_eq_iff by simp

lemmas partial_implies = partial_implies_raw

lemma partial_implies':
  \<open> Fic_Space r
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k := 1(k2 \<mapsto> Share n v)))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v)))))
\<Longrightarrow> R.get res k k2 = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, del_insts) fun_upd_same join_sub_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep times_option(3))

lemma partial_implies'':
  assumes FS: \<open>Fic_Space r\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k := 1(k2 \<mapsto> Share n v)))\<close>
    and A: \<open> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v)))))\<close>
  shows [simp]: \<open>R.get res k k2 = Some v\<close>
proof -
  from partial_implies'[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

end


section \<open>Common Instructions\<close>

subsection \<open>Drop & Duplicate Value\<close>

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action action_dup\<close>]:
  \<open>x \<Ztypecolon> Val raw T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> Val raw T \<heavy_comma> x \<Ztypecolon> Val raw T @action action_dup\<close>
  unfolding Imply_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?R \<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action action_drop\<close>]:
  \<open>Void \<heavy_comma> x \<Ztypecolon> Val raw T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Void @action action_drop\<close>
  unfolding Imply_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)


subsection \<open>Abnormality\<close>

definition throw :: \<open>ABNM \<Rightarrow> 'ret::VALs proc\<close>
  where \<open>throw raw = det_lift (Abnormality raw)\<close>

lemma throw_reduce_tail[procedure_simps,simp]:
  \<open>(throw any \<ggreater> f) = throw any\<close>
  unfolding throw_def bind_def det_lift_def by simp

lemma "__throw_rule__"[intro!]:
  \<open> (\<And>a. X a \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' a)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (throw excep :: 'ret::VALs proc) \<lbrace> X excep \<longmapsto> Any \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s X'\<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Imply_def
  apply clarsimp
  by (meson Imply_def View_Shift_def view_shift_by_implication)

lemma throw_\<phi>app:
  \<open> (\<And>v. Remove_Values (X v) (X' v))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c throw excep \<lbrace> X excep \<longmapsto> 0 \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s X' \<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Remove_Values_def Imply_def
  apply clarsimp
  by (meson Imply_def View_Shift_def view_shift_by_implication)

definition op_try :: "'ret proc \<Rightarrow> (ABNM \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc"
  where \<open>op_try f g s = \<Union>((\<lambda>y. case y of Success x s' \<Rightarrow> {Success x s'}
                                       | Abnormality v s' \<Rightarrow> g v s'
                                       | AssumptionBroken \<Rightarrow> {AssumptionBroken}
                                       | NonTerm \<Rightarrow> {NonTerm}
                                       | Invalid \<Rightarrow> {Invalid}) ` f s)\<close>

lemma "__op_try__"[intro!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>v. E v)
\<Longrightarrow> (\<And>v. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_try f g \<lbrace> X \<longmapsto> \<lambda>v. Y1 v + Y2 v \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2  \<close>
  unfolding op_try_def \<phi>Procedure_def subset_iff
  apply clarsimp subgoal for comp R x s
    apply (cases s; simp; cases x; clarsimp simp add: \<phi>expns ring_distribs)
    subgoal premises prems for a b u v
      using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
      by (metis (no_types, lifting) INTERP_SPEC LooseStateSpec_expn(1) prems(3) prems(6) prems(7) prems(8) prems(9) set_mult_expn)
    subgoal premises prems for a b c d u v2 proof -
      have \<open>Abnormality a b \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
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
      have \<open>Abnormality a b \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Abnormality c d \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E2 v))\<close>
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
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> YY \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  assumes G: \<open>(\<And>v. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g v \<lbrace> E v \<longmapsto> YY \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s EE2 )\<close>
  input  X
  output YY
  throws EE2
  \<medium_left_bracket> "__op_try__"
    F
    G
  \<medium_right_bracket> .. .

proc (nodef) try':
  assumes A: \<open>Union_the_Same_Or_Arbitrary_when_Var Z Y1 Y2\<close>
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  assumes G: \<open>\<And>v. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<close>
  input  X
  output Z
  throws E2
  \<medium_left_bracket> "__op_try__" F G
      unfold A[unfolded Union_the_Same_Or_Arbitrary_when_Var_def, THEN spec, symmetric]
  \<medium_right_bracket>. .


subsection \<open>Access the Resource\<close>

subsubsection \<open>Legacy\<close>

definition \<phi>M_get_res :: \<open>(resource \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>M_get_res R F = (\<lambda>res. F (R res) res)\<close>

definition \<phi>M_get_res_entry :: \<open>(resource \<Rightarrow> ('k \<rightharpoonup> 'a)) \<Rightarrow> 'k \<Rightarrow> ('a \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc\<close>
  where \<open>\<phi>M_get_res_entry R k F =
    \<phi>M_get_res R (\<lambda>res. case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition \<phi>M_set_res :: \<open> (('x \<Rightarrow> 'x) \<Rightarrow> resource \<Rightarrow> resource) \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> unit proc \<close>
  where \<open>\<phi>M_set_res Updt F = (\<lambda>res. {Success (\<phi>arg ()) (Updt F res)})\<close>

subsubsection \<open>Getters\<close>

paragraph \<open>basic resource\<close>

definition (in resource) \<phi>R_get_res :: \<open>('T \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_get_res F = (\<lambda>res. F (get res) res)\<close>

lemma (in resource) \<phi>R_get_res[intro!]:
  \<open> get res = v
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_def subset_iff by simp

paragraph \<open>nonsepable_mono_resource\<close>

definition (in nonsepable_mono_resource) \<phi>R_get_res_entry :: \<open>('T \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc\<close>
  where \<open>\<phi>R_get_res_entry F = \<phi>R_get_res (\<lambda>v. case v of Some v' \<Rightarrow> F (nonsepable.dest v')
                                                      | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in nonsepable_mono_resource) \<phi>R_get_res_entry:
  \<open> get res = Some (nonsepable v)
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

paragraph \<open>partial_map_resource\<close>

definition (in partial_map_resource)
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> ('val \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc\<close>
  where \<open>\<phi>R_get_res_entry k F =
    \<phi>R_get_res (\<lambda>res. case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in partial_map_resource) \<phi>R_get_res_entry[intro!]:
  \<open> get res k = Some v
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry k F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

subparagraph \<open>identity_fiction_for_partial_mapping_resource\<close>

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_get_res_entry_frm[intro!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_get_res_entry key F
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
    \<phi>Res_Spec_expn_R \<phi>Res_Spec_expn_impEx \<phi>Res_Spec_expn_impSubj imp_conjL
  by (clarsimp simp add: \<phi>expns expand simp del: set_mult_expn del: subsetI;
      rule R.\<phi>R_get_res_entry[where v=v]; simp)

lemmas \<phi>R_get_res_entry[intro!] = \<phi>R_get_res_entry_frm[where R=1, simplified]

end

subparagraph \<open>share_fiction_for_partial_mapping_resource\<close>

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_get_res_entry_frm[intro!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_get_res_entry key F
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
    \<phi>Res_Spec_expn_R \<phi>Res_Spec_expn_impEx \<phi>Res_Spec_expn_impSubj imp_conjL
  apply (clarsimp simp add: \<phi>expns zero_set_def del: subsetI)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

lemmas \<phi>R_get_res_entry[intro!] = \<phi>R_get_res_entry_frm[where R=1, simplified]

end

paragraph \<open>partial_map_resource2\<close>

definition (in partial_map_resource2)
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> ('val \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc\<close>
  where \<open>\<phi>R_get_res_entry k k2 F = \<phi>R_get_res (\<lambda>res.
    case res k k2 of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in partial_map_resource2) \<phi>R_get_res_entry[intro!]:
  \<open> get res k k2 = Some v
\<Longrightarrow> F v res \<subseteq> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry k k2 F res \<subseteq> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry[intro!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def del: subsetI)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry1[intro!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  using \<phi>R_get_res_entry[where n=1, simplified] .


subsubsection \<open>Setters\<close>

paragraph \<open>fine_resource\<close>

definition (in resource) \<phi>R_set_res :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> unit proc\<close>
  where \<open>\<phi>R_set_res F = (\<lambda>res. {Success (\<phi>arg ()) (updt F res)})\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_set_res:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := u))}) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__" del: set_mult_expn)

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_set_res:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k \<mapsto> u) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def
          expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
          expand_subj[where x=\<open>1(k \<mapsto> u)\<close>, simplified] simp del: set_mult_expn
          del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_set_res[where k=k and res=res], assumption,
        simp add: \<phi>Res_Spec_mult_homo, assumption) .

declare \<phi>R_set_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_set_res_frm[intro!] = \<phi>R_set_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0]
end

context share_fiction_for_partial_mapping_resource begin
lemma \<phi>R_set_res:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k \<mapsto> u) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def
          expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
          expand_subj[where x=\<open>1(k \<mapsto> u)\<close>, simplified] simp del: set_mult_expn
          del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_set_res[where k=k and res=res], assumption,
        simp add: \<phi>Res_Spec_mult_homo, assumption) .

declare \<phi>R_set_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_set_res_frm[intro!] = \<phi>R_set_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0]
end


paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_set_res[intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> \<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 := u)))}) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__" del: set_mult_expn)

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_set_res"[THEN \<phi>CONSEQ'E0, intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k) m \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k := 1(k2 \<mapsto> v)))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k)
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def
                            expand[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close>, simplified]
                            expand_subj[where x=\<open>1(k := 1(k2 \<mapsto> u))\<close>, simplified]
                  simp del: set_mult_expn
                  del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_set_res, assumption, simp add: \<phi>Res_Spec_mult_homo, assumption) .


subsubsection \<open>Dispose\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_dispose_res[intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (1(k \<mapsto> any))})
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := None)) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__" \<phi>Res_Spec_mult_homo)

context identity_fiction_for_partial_mapping_resource begin
lemma \<phi>R_dispose_res:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k := None))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
                  simp del: set_mult_expn del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_dispose_res, assumption, simp add: \<phi>Res_Spec_mult_homo, simp add: \<phi>Res_Spec_mult_homo) .

declare \<phi>R_dispose_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_dispose_res_frm[intro!] = \<phi>R_dispose_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0]
end

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_dispose_res:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k := None))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
                  simp del: set_mult_expn del: subsetI)
  subgoal for r res
    by (rule R.\<phi>R_dispose_res, assumption, simp add: \<phi>Res_Spec_mult_homo, simp add: \<phi>Res_Spec_mult_homo) .

declare \<phi>R_dispose_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_dispose_res_frm[intro!] = \<phi>R_dispose_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0]
end

paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_dispose_res[intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in> Valid)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (1(k := any))})
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := 1)) res \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec R) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__" \<phi>Res_Spec_mult_homo)

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_dispose_res"[THEN \<phi>CONSEQ'E0, intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := 1) \<in> Valid)
\<Longrightarrow> (\<And>res r. res \<in> \<phi>Res_Spec (\<I> INTERP r * {R.mk (1(k := f))})
      \<Longrightarrow> P (R.get res) \<and> dom f = dom (R.get res k))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_set_res (\<lambda>f. f(k := 1))
         \<lbrace> to_share o f \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k := f)\<close>, simplified]
                            \<phi>Res_Spec_mult_homo
                  simp del: set_mult_expn del: subsetI)
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
        using prems(3) t3 \<phi>Res_Spec_mult_homo by blast
    qed . .

subsubsection \<open>Allocate\<close>

definition (in mapping_resource)
    \<phi>R_allocate_res_entry :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> ('key \<Rightarrow> 'ret proc)
                           \<Rightarrow> 'ret::VALs proc\<close>
  where \<open>\<phi>R_allocate_res_entry P init F =
    \<phi>R_get_res (\<lambda>res.
    let k = (@k. res k = 1 \<and> P k)
     in \<phi>R_set_res (\<lambda>f. f(k := init))
        \<ggreater> F k
)\<close>

lemma (in mapping_resource) \<phi>R_set_res_new[intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> k \<notin> dom1 (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res
      \<subseteq> \<S> (\<lambda>_. \<phi>Res_Spec (R * {mk (1(k := u))})) Any\<close>
  unfolding \<phi>R_set_res_def
  by (simp add: \<phi>expns "__new_rule__" \<phi>Res_Spec_mult_homo del: set_mult_expn)

lemma (in mapping_resource) \<phi>R_allocate_res_entry[intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in> Valid \<longrightarrow> m(k := init) \<in> Valid)
\<Longrightarrow> (\<And>k res. res \<in> \<phi>Res_Spec (R * {mk (1(k := init))} \<^bold>s\<^bold>u\<^bold>b\<^bold>j P k)
      \<Longrightarrow> F k res \<subseteq> \<S> Y E)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> \<phi>R_allocate_res_entry P init F res \<subseteq> \<S> Y E\<close>
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
      using \<open>res \<in> \<phi>Res_Spec _\<close> apply this
      by (simp add: prems(3))
  qed .

lemma (in identity_fiction_for_partial_mapping_resource) "\<phi>R_allocate_res_entry"[intro!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in> Valid \<longrightarrow> m(k \<mapsto> init) \<in> Valid)
\<Longrightarrow> (\<And>new. P new \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F new \<lbrace> X \<heavy_comma> init \<Ztypecolon> \<phi> (new \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R.\<phi>R_allocate_res_entry P (Some init) F \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
 apply (clarsimp simp add: \<phi>expns \<phi>Procedure_\<phi>Res_Spec simp del: set_mult_expn del: subsetI)
  subgoal for r res c
  apply (rule R.\<phi>R_allocate_res_entry[where R="(\<I> INTERP (r * c))"])
  apply (clarsimp)
      apply (clarsimp)
  apply (clarsimp simp add: Subjection_expn
                  simp del: \<phi>Res_Spec_mult_homo set_mult_expn del: subsetI)
  subgoal premises prems for k res'
  apply (rule prems(3)[OF \<open>P _\<close>, THEN spec[where x=r], THEN spec[where x=res'],
              simplified prems, simplified, THEN mp])
    apply (rule exI[where x=\<open>c * mk (1(k \<mapsto> init))\<close>])
    apply (simp add: \<phi>expns prems)
    apply rule
    apply (metis Fic_Space_Un Subjection_expn \<phi>Res_Spec_mult_homo expand_subj prems(6) prems(7) prems(8) prems(9) sep_mult_assoc)
    apply rule
    using Fic_Space_Un \<phi>Res_Spec_mult_homo prems(5) prems(6) prems(7) prems(8) prems(9) sep_disj_fiction sep_disj_multD2 apply blast
    using Fic_Space_Un \<phi>Res_Spec_mult_homo prems(6) prems(7) prems(8) prems(9) sep_disj_fiction sep_disj_multI2 by blast
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
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup [] \<lbrace> Void \<longmapsto> () \<Ztypecolon> EmptyTuple \<rbrace>\<close>
  unfolding cons_tup_nil by \<phi>reason

lemma (in \<phi>empty) op_cons_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup TYs \<lbrace> X \<longmapsto> VAL y \<Ztypecolon> Y \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup (TY#TYs) \<lbrace> VAL a \<Ztypecolon> A\<heavy_comma> X \<longmapsto> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> Y) \<rbrace>\<close>
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
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup [] \<lbrace> () \<Ztypecolon> EmptyTuple \<longmapsto> Void \<rbrace> \<close>
  unfolding op_dest_tup_nil_expn by \<phi>reason

lemma (in \<phi>empty) op_dest_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup TYs \<lbrace> VAL y \<Ztypecolon> Y \<longmapsto> X \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup (TY#TYs) \<lbrace> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> \<phi>Is_Tuple Y) \<longmapsto> VAL a \<Ztypecolon> A\<heavy_comma> X \<rbrace>\<close>
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
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_element idx TY \<lbrace> VAL x \<Ztypecolon> X \<longmapsto> VAL f x \<Ztypecolon> Y \<rbrace> \<close>
  unfolding op_get_element_def \<phi>Index_getter_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason

lemma (in \<phi>empty) op_set_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> Y) (index_type idx TY)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_element idx TY \<lbrace> VAL x \<Ztypecolon> X\<heavy_comma> VAL y \<Ztypecolon> Y \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> X \<rbrace>\<close>
  unfolding op_set_element_def \<phi>Index_mapper_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
   apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason


*)

*)

end
