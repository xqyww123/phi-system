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

definition op_const_bool :: "bool \<Rightarrow> VAL proc"
  where "op_const_bool b = Return (\<phi>arg (V_bool.mk b))"

definition op_not :: "(VAL, VAL) proc'"
  where "op_not v =
    \<phi>M_getV bool V_bool.dest v (\<lambda>v.
    Return (\<phi>arg (V_bool.mk (\<not> v)))
  )"

definition op_and :: "(VAL \<times> VAL, VAL) proc'"
  where "op_and =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV bool V_bool.dest va (\<lambda>v.
    \<phi>M_getV bool V_bool.dest vb (\<lambda>u.
    Return (\<phi>arg (V_bool.mk (v \<and> u)))
  )))"

definition op_or :: "(VAL \<times> VAL, VAL) proc'"
  where "op_or =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV bool V_bool.dest va (\<lambda>v.
    \<phi>M_getV bool V_bool.dest vb (\<lambda>u.
    Return (\<phi>arg (V_bool.mk (v \<or> u)))
  )))"

definition op_equal :: "TY \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_equal TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV TY id va (\<lambda>v.
    \<phi>M_getV TY id vb (\<lambda>u.
    (\<lambda>res. \<phi>M_assert (Can_EqCompare res u v) res) \<ggreater>
    Return (\<phi>arg (V_bool.mk (EqCompare u v)))
)))"


section \<open>\<phi>-Type\<close>

definition \<phi>Bool :: "(VAL, bool) \<phi>" ("\<bool>")
  where "\<bool> x = { V_bool.mk x }"

lemma \<phi>Bool_expn[\<phi>expns]:
  " p \<in> (x \<Ztypecolon> \<bool>) \<longleftrightarrow> p = V_bool.mk x"
  unfolding \<phi>Type_def \<phi>Bool_def by simp

lemma \<phi>Bool_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<bool>) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>Bool_eqcmp[\<phi>reason 2000]:
  "\<phi>Equal \<bool> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns can_eq_bool eq_bool)

lemma \<phi>Bool_zero[\<phi>reason 2000]:
  "\<p>\<r>\<e>\<m>\<i>\<s>\<e> TY = bool \<Longrightarrow> \<phi>Zero TY \<bool> False"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_bool)

lemma \<phi>Bool_semty[\<phi>reason 2000]:
  \<open>\<phi>SemType (x \<Ztypecolon> \<bool>) bool\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns WT_bool)

lemma [\<phi>reason 2000]:
  \<open>is_singleton (x \<Ztypecolon> \<bool>)\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)

abbreviation \<open>Predicate_About x \<equiv> (\<bool> <func-over> x)\<close>


section \<open>Abstractions of Boolean Arithmetic\<close>

\<phi>overloads "=" and "\<not>" and "\<and>" and "\<or>"

subsection \<open>Constant\<close>


declare [[\<phi>trace_reasoning = 1]]

lemma op_const_bool[\<phi>synthesis for \<open>\<lambda>v. True \<Ztypecolon> ?T v\<close> (1200) and \<open>\<lambda>v. False \<Ztypecolon> ?T v\<close> (1200)]:
  \<open> Check_Literal b
\<Longrightarrow> \<p>\<r>\<o>\<c> op_const_bool b \<lbrace> Void \<longmapsto> \<v>\<a>\<l> b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_const_bool_def
  by (rule, simp add: \<phi>Bool_expn)

print_\<phi>reasoners \<open>\<p>\<r>\<o>\<c> ?f4 \<lbrace> XXX \<longmapsto> \<lambda>v. True \<Ztypecolon> ?X v \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?S \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E4  @action synthesis\<close>

subsection \<open>Not\<close>

lemma op_not[\<phi>overload \<not>, \<phi>synthesis 100]:
  \<open>\<p>\<r>\<o>\<c> op_not raw \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw] \<bool> \<longmapsto> \<v>\<a>\<l> \<not> x \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_not_def
  by (cases raw, simp, rule, simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns)


subsection \<open>And\<close>

lemma op_and[\<phi>overload \<and>, \<phi>synthesis add]:
  \<open>\<p>\<r>\<o>\<c> op_and (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> \<v>\<a>\<l>[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<v>\<a>\<l>[vb] \<bool> \<longmapsto> \<v>\<a>\<l> (a \<and> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_and_def
  by (cases va; cases vb; simp, rule, rule, simp add: \<phi>expns WT_bool, rule,
      simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns, blast)

subsection \<open>Or\<close>

lemma op_or[\<phi>overload \<or>, \<phi>synthesis 100]:
  \<open>\<p>\<r>\<o>\<c> op_or (\<phi>V_pair vb va) \<lbrace> a \<Ztypecolon> \<v>\<a>\<l>[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<v>\<a>\<l>[vb] \<bool> \<longmapsto> \<v>\<a>\<l> (a \<or> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_or_def
  by(cases va; cases vb, simp, rule, rule, simp add: \<phi>expns WT_bool, rule,
      simp add: \<phi>expns WT_bool, rule, simp add: \<phi>expns, blast)


subsection \<open>Equal\<close>

declare [[
    overloaded_operator_in_synthesis \<open>\<lambda>v. x \<Ztypecolon> T v\<close> \<open>\<lambda>v. y \<Ztypecolon> U v\<close> \<Rightarrow> \<open>\<lambda>v. x = y \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>,
    overloaded_operator_in_synthesis
        \<open>\<lambda>v. x mod N \<Ztypecolon> T v\<close> \<open>\<lambda>v. y mod N \<Ztypecolon> U v\<close> \<Rightarrow> \<open>\<lambda>v. x mod N = y mod N \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>
]]

lemma op_equal_\<phi>app[\<phi>overload =]:
  \<open> \<phi>Equal T can_eq eq
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (b \<Ztypecolon> T) TY
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> can_eq a b
\<Longrightarrow> \<p>\<r>\<o>\<c> op_equal TY (\<phi>V_pair rawb rawa) \<lbrace> a \<Ztypecolon> \<v>\<a>\<l>[rawa] T\<heavy_comma> b \<Ztypecolon> \<v>\<a>\<l>[rawb] T \<longmapsto> eq a b \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close>
  unfolding op_equal_def
  apply (cases rawa; cases rawb; simp, rule, rule)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, rule)
    apply (simp add: \<phi>SemType_def subset_iff Premise_def, rule)
   apply (unfold \<phi>Equal_def Premise_def, simp)
  by (rule \<phi>M_Success', rule, simp add: \<phi>expns)


declare op_equal_\<phi>app[where eq=\<open>(=)\<close>, \<phi>synthesis 100]
declare op_equal_\<phi>app[where eq=\<open>(\<lambda>x y. x mod N = y mod N)\<close> for N, \<phi>synthesis 100]


end
