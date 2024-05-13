chapter \<open>Generic Boolean\<close>

theory PhiSem_Generic_Boolean
  imports PhiSem_Base
  abbrevs "<bool>" = "\<b>\<o>\<o>\<l>"
begin

section \<open>Semantics\<close>

consts bool :: TY ("\<b>\<o>\<o>\<l>")

debt_axiomatization V_bool :: \<open>bool value_entry\<close>
  where V_bool_ax: \<open>VDT_field V_bool\<close>

interpretation V_bool: VDT_field V_bool using V_bool_ax .

debt_axiomatization
      can_eq_bool: \<open>Can_EqCompare res (V_bool.mk x1) (V_bool.mk x2)\<close>
  and eq_bool:     \<open>EqCompare (V_bool.mk x1) (V_bool.mk x2) = (x1 = x2)\<close>
  and zero_bool[simp]: \<open>Zero bool = Some (V_bool.mk False)\<close>
  and WT_bool[simp]:   \<open>Well_Type bool = { V_bool.mk x |x. True }\<close>

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
    (\<lambda>res. \<phi>M_assert (Can_EqCompare res v u) res) \<then>
    Return (\<phi>arg (V_bool.mk (EqCompare v u)))
)))"


section \<open>\<phi>-Type\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>Bool :: "(VAL, bool) \<phi>" ("\<bool>")
  where \<open>x \<Ztypecolon> \<bool> \<equiv> V_bool.mk x \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality
       and \<open>Weak_Semantic_Type \<bool> bool\<close>
       and \<open>Semantic_Zero_Val bool \<bool> False\<close>


(*
lemma
  \<open>P (\<t>\<y>\<p>\<e>\<o>\<f> \<bool>)\<close>
  apply simp *)

lemma \<phi>Bool_eqcmp[\<phi>reason 2000]:
  "\<phi>Equal \<bool> (\<lambda>x y. True) (=)" (*TODO: auto derive!*)
  unfolding \<phi>Equal_def
  by (simp add: can_eq_bool eq_bool)


section \<open>Abstractions of Boolean Arithmetic\<close>
 
declare_\<phi>lang_operator
  infix 50 "="
  infix 35 "\<and>"
  infix 30 "\<or>"
  prefix 40 "\<not>"


subsection \<open>Constant\<close>

lemma op_const_bool_\<phi>app[\<phi>synthesis for \<open>\<lambda>v. True \<Ztypecolon> ?T v\<close> (1200) and \<open>\<lambda>v. False \<Ztypecolon> ?T v\<close> (1200)]:
  \<open> Is_Literal b
\<Longrightarrow> \<p>\<r>\<o>\<c> op_const_bool b \<lbrace> Void \<longmapsto> \<v>\<a>\<l> b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_const_bool_def
  by (rule, simp)

lemma True_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_const_bool True \<lbrace> Void \<longmapsto> \<v>\<a>\<l> True \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> \<open>True\<close> \<medium_right_bracket>.

lemma False_\<phi>app:
  \<open>\<p>\<r>\<o>\<c> op_const_bool False \<lbrace> Void \<longmapsto> \<v>\<a>\<l> False \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> \<open>False\<close> \<medium_right_bracket>.


subsection \<open>Not\<close>

lemma op_not[\<phi>overload \<not>, \<phi>synthesis 100]:
  \<open>\<p>\<r>\<o>\<c> op_not raw \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[raw] \<bool> \<longmapsto> \<v>\<a>\<l> \<not> x \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_not_def
  by (cases raw, simp, rule, simp, rule, simp)

subsection \<open>And\<close>

lemma op_and[\<phi>overload \<and>, \<phi>synthesis add]:
  \<open>\<p>\<r>\<o>\<c> op_and (\<phi>V_pair va vb) \<lbrace> a \<Ztypecolon> \<v>\<a>\<l>[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<v>\<a>\<l>[vb] \<bool> \<longmapsto> \<v>\<a>\<l> (a \<and> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_and_def
  by (cases va; cases vb; simp, rule, rule, simp, rule, simp, rule, simp)

subsection \<open>Or\<close>

lemma op_or[\<phi>overload \<or>, \<phi>synthesis 100]:
  \<open>\<p>\<r>\<o>\<c> op_or (\<phi>V_pair va vb) \<lbrace> a \<Ztypecolon> \<v>\<a>\<l>[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<v>\<a>\<l>[vb] \<bool> \<longmapsto> \<v>\<a>\<l> (a \<or> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_or_def
  by(cases va; cases vb, simp, rule, rule, simp, rule, simp, rule, simp)


subsection \<open>Equal\<close>

declare [[
    overloaded_operator_in_synthesis \<open>\<lambda>v. x \<Ztypecolon> T v\<close> \<open>\<lambda>v. y \<Ztypecolon> U v\<close> \<Rightarrow> \<open>\<lambda>v. x = y \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>,
    overloaded_operator_in_synthesis
        \<open>\<lambda>v. x mod N \<Ztypecolon> T v\<close> \<open>\<lambda>v. y mod N \<Ztypecolon> U v\<close> \<Rightarrow> \<open>\<lambda>v. x mod N = y mod N \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>
]]

lemma op_equal_\<phi>app[\<phi>overload =]:
  \<open> \<phi>Equal T can_eq eq
\<Longrightarrow> Weak_Semantic_Type' (a \<Ztypecolon> T) TY
\<Longrightarrow> Weak_Semantic_Type' (b \<Ztypecolon> T) TY
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> can_eq a b
\<Longrightarrow> \<p>\<r>\<o>\<c> op_equal TY (\<phi>V_pair rawa rawb) \<lbrace> a \<Ztypecolon> \<v>\<a>\<l>[rawa] T\<heavy_comma> b \<Ztypecolon> \<v>\<a>\<l>[rawb] T \<longmapsto> eq a b \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close>
  unfolding op_equal_def
  by ((cases rawa; cases rawb; simp, rule, rule),
      simp add: Weak_Semantic_Type'_def subset_iff Premise_def, rule,
      simp add: Weak_Semantic_Type'_def subset_iff Premise_def, rule,
      unfold \<phi>Equal_def Premise_def, simp,
      rule \<phi>M_Success', rule, simp)

declare op_equal_\<phi>app[where eq=\<open>(=)\<close>, \<phi>synthesis 100]
declare op_equal_\<phi>app[where eq=\<open>(\<lambda>x y. x mod N = y mod N)\<close> for N, \<phi>synthesis 100]


end
