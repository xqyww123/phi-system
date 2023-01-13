chapter \<open>Generic Boolean\<close>

theory PhiSem_Generic_Boolean
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantic\<close>

consts bool :: TY

debt_axiomatization V_bool :: \<open>bool value_entry\<close>
  where V_bool_ax: \<open>VDT_field V_bool\<close>
  
interpretation V_bool: VDT_field V_bool using V_bool_ax .

debt_axiomatization
      can_eq_bool: \<open>Can_EqCompare res (V_bool.mk x1) (V_bool.mk x2)\<close>
  and eq_bool:     \<open>EqCompare (V_bool.mk x1) (V_bool.mk x2) = (x1 = x2)\<close>
  and zero_bool:   \<open>Zero bool = Some (V_bool.mk False)\<close>
  and WT_bool:     \<open>Well_Type bool = { V_bool.mk x |x. True }\<close>

section \<open>Instructions\<close>

definition op_not :: "(VAL, VAL) proc'"
  where "op_not v =
    \<phi>M_getV bool V_bool.dest v (\<lambda>v.
    Return (sem_value (V_bool.mk (\<not> v)))
  )"

definition op_and :: "(VAL \<times> VAL, VAL) proc'"
  where "op_and =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV bool V_bool.dest va (\<lambda>v.
    \<phi>M_getV bool V_bool.dest vb (\<lambda>u.
    Return (sem_value (V_bool.mk (v \<and> u)))
  )))"

definition op_or :: "(VAL \<times> VAL, VAL) proc'"
  where "op_or =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV bool V_bool.dest va (\<lambda>v.
    \<phi>M_getV bool V_bool.dest vb (\<lambda>u.
    Return (sem_value (V_bool.mk (v \<or> u)))
  )))"

definition op_equal :: "TY \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_equal TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV TY id va (\<lambda>v.
    \<phi>M_getV TY id vb (\<lambda>u.
    (\<lambda>res. \<phi>M_assert (Can_EqCompare res u v) res) \<ggreater>
    Return (sem_value (V_bool.mk (EqCompare u v)))
)))"


section \<open>\<phi>-Type\<close>

definition \<phi>Bool :: "(VAL, bool) \<phi>" ("\<bool>")
  where "\<bool> x = { V_bool.mk x }"

lemma \<phi>Bool_expn[\<phi>expns]:
  " p \<in> (x \<Ztypecolon> \<bool>) \<longleftrightarrow> p = V_bool.mk x"
  unfolding \<phi>Type_def \<phi>Bool_def by simp

lemma \<phi>Bool_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<bool>) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>Bool_eqcmp[\<phi>reason 1000]:
  "\<phi>Equal \<bool> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns can_eq_bool eq_bool)

lemma \<phi>Bool_zero[\<phi>reason 1000]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e TY = bool \<Longrightarrow> \<phi>Zero TY \<bool> False"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_bool)

lemma \<phi>Bool_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<bool>) bool\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns WT_bool)

lemma [\<phi>reason]:
  \<open>is_singleton (x \<Ztypecolon> \<bool>)\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)

abbreviation \<open>Predicate_About x \<equiv> (\<bool> <func-over> x)\<close>


section \<open>Abstractions of Boolean Arithmetic\<close>

\<phi>overloads "=" and "\<not>" and "\<and>" and "\<or>"

paragraph \<open>Not\<close>

lemma op_not[\<phi>overload \<not>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_not raw \<lbrace> x \<Ztypecolon> Val raw \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l \<not> x \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_not_def
  by (cases raw, simp, rule, simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns)

schematic_goal
  [\<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R1\<heavy_comma> SYNTHESIS \<not>?b \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l b \<Ztypecolon> \<bool> \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  shows \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?G \<lbrace> R \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l \<not>b \<Ztypecolon> \<bool> \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  \<medium_left_bracket> F1 \<not> \<medium_right_bracket> .. .

paragraph \<open>And\<close>

lemma op_and[\<phi>overload \<and>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_and (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vb] \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l (a \<and> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_and_def
  by (cases va; cases vb; simp, rule, rule, simp add: \<phi>expns WT_bool, rule,
      simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns, blast)

schematic_goal
  [\<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x \<and> ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  shows \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?G \<lbrace> R \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x \<and> y) \<Ztypecolon> \<bool> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 + E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  \<medium_left_bracket> F1 F2 \<and> \<medium_right_bracket>. .

paragraph \<open>Or\<close>

lemma op_or[\<phi>overload \<or>]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_or (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[vb] \<bool> \<longmapsto> \<^bold>v\<^bold>a\<^bold>l (a \<or> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_or_def
  by(cases va; cases vb, simp, rule, rule, simp add: \<phi>expns WT_bool, rule,
      simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns, blast)


paragraph \<open>Equal\<close>

lemma op_equal_\<phi>app[\<phi>overload =]:
  \<open> \<phi>SemType (a \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Equal T can_eq eq
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e can_eq a b
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal TY (\<phi>V_pair rawb rawa) \<lbrace> a \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawa] T\<heavy_comma> b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[rawb] T \<longmapsto> eq a b \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<bool> \<rbrace>\<close>
  unfolding op_equal_def
  apply (cases rawa; cases rawb; simp, rule, rule)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, rule)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, rule)
   apply (unfold \<phi>Equal_def Premise_def, simp)
  by (rule \<phi>M_Success', rule, simp add: \<phi>expns)

proc \<phi>__synthesis_eq[
    \<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> SYNTHESIS (?x = ?y) \<Ztypecolon> ?T ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  assumes F1: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f1 \<lbrace> R  \<longmapsto> R1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   F2: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f2 \<lbrace> R1 \<longmapsto> R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
    and   [\<phi>reason]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason]: \<open>\<phi>SemType (y \<Ztypecolon> T) TY\<close>
    and   [\<phi>reason]: \<open>\<phi>Equal T can_eq (=)\<close>
  input \<open>R\<close>
  premises \<open>can_eq x y\<close>
  output \<open>R2\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (x = y) \<Ztypecolon> \<bool>\<close>
  throws \<open>E1 + E2\<close>
  goal G
  \<medium_left_bracket> F1 F2 = \<medium_right_bracket>. .


end