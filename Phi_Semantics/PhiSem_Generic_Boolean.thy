chapter \<open>Generic Boolean\<close>

theory PhiSem_Generic_Boolean
  imports PhiSem_Base
  abbrevs "<bool>" = "\<bool'>"
begin

section \<open>Semantics\<close>

debt_axiomatization sem_bool_T    :: TY ("\<bool'>")
                and sem_mk_bool   :: \<open>bool \<Rightarrow> VAL\<close>
                and sem_dest_bool :: \<open>VAL \<Rightarrow> bool\<close>
  where sem_mk_dest_bool[simp]: \<open>sem_dest_bool (sem_mk_bool b) = b\<close>
    and bool_neq_poison[simp]: \<open>\<bool'> \<noteq> \<poison>\<close>
    and can_eq_bool: \<open>Can_EqCompare res (sem_mk_bool x1) (sem_mk_bool x2)\<close>
    and eq_bool:     \<open>EqCompare (sem_mk_bool x1) (sem_mk_bool x2) = (x1 = x2)\<close>
    and zero_bool[simp]: \<open>Zero \<bool'> = Some (sem_mk_bool False)\<close>
    and WT_bool[simp]:   \<open>Well_Type \<bool'> = { sem_mk_bool x |x. True }\<close>  

lemma sem_mk_bool_inj[simp]:
  \<open>sem_mk_bool x = sem_mk_bool y \<equiv> x = y\<close>
  by (smt (verit, del_insts) sem_mk_dest_bool)

lemma poison_neq_bool[simp]:
  \<open>\<poison> \<noteq> \<bool'>\<close>
  using bool_neq_poison by fastforce

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal \<bool'> \<close>
  unfolding Is_Type_Literal_def ..

section \<open>Instructions\<close>

definition op_const_bool :: "bool \<Rightarrow> VAL proc"
  where "op_const_bool b = Return (\<phi>arg (sem_mk_bool b))"

definition op_not :: "(VAL, VAL) proc'"
  where "op_not v =
    \<phi>M_getV \<bool'> sem_dest_bool v (\<lambda>v.
    Return (\<phi>arg (sem_mk_bool (\<not> v)))
  )"

definition op_and :: "(VAL \<times> VAL, VAL) proc'"
  where "op_and =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV \<bool'> sem_dest_bool va (\<lambda>v.
    \<phi>M_getV \<bool'> sem_dest_bool vb (\<lambda>u.
    Return (\<phi>arg (sem_mk_bool (v \<and> u)))
  )))"

definition op_or :: "(VAL \<times> VAL, VAL) proc'"
  where "op_or =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV \<bool'> sem_dest_bool va (\<lambda>v.
    \<phi>M_getV \<bool'> sem_dest_bool vb (\<lambda>u.
    Return (\<phi>arg (sem_mk_bool (v \<or> u)))
  )))"

definition op_xor :: "(VAL \<times> VAL, VAL) proc'"
  where "op_xor =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV \<bool'> sem_dest_bool va (\<lambda>v.
    \<phi>M_getV \<bool'> sem_dest_bool vb (\<lambda>u.
    Return (\<phi>arg (sem_mk_bool (v \<and> \<not> u \<or> \<not> v \<and> u)))
  )))"

definition op_equal :: "TY \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_equal TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_getV TY id va (\<lambda>v.
    \<phi>M_getV TY id vb (\<lambda>u.
    (\<lambda>res. \<phi>M_assert (Can_EqCompare res v u) res) \<then>
    Return (\<phi>arg (sem_mk_bool (EqCompare v u)))
)))"


section \<open>\<phi>-Type\<close>
 
\<phi>type_def \<phi>Bool :: "(VAL, bool) \<phi>" ("\<bool>")
  where \<open>x \<Ztypecolon> \<bool> \<equiv> sem_mk_bool x \<Ztypecolon> Itself\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and \<open>Semantic_Zero_Val \<bool'> \<bool> False\<close>
       and Inhabited
       and \<open>\<typeof> \<bool> = \<bool'>\<close>
       and Equiv_Class

lemma \<phi>Bool_eqcmp[\<phi>reason 2000]:
  "\<phi>Equal \<bool> (\<lambda>x y. True) (=)" (*TODO: auto derive!*)
  unfolding \<phi>Equal_def
  by (simp add: can_eq_bool eq_bool)


section \<open>Abstractions of Boolean Arithmetic\<close>
 
declare_\<phi>lang_operator
  infix 50 "="
  infix 35 "\<and>"
  infix 30 "\<or>"
  infix 30 \<oplus> \<comment> \<open>Xor\<close>
  prefix 40 "\<not>"


subsection \<open>Constant\<close>

lemma op_const_bool_\<phi>app[\<phi>synthesis for \<open>\<lambda>v. True \<Ztypecolon> ?T v\<close> (1200) and \<open>\<lambda>v. False \<Ztypecolon> ?T v\<close> (1200)]:
  \<open> Is_Literal b
\<Longrightarrow> \<proc> op_const_bool b \<lbrace> Void \<longmapsto> \<val> b \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_const_bool_def
  by (rule, simp)

lemma True_\<phi>app:
  \<open>\<proc> op_const_bool True \<lbrace> Void \<longmapsto> \<val> True \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> \<open>True\<close> \<medium_right_bracket>.

lemma False_\<phi>app:
  \<open>\<proc> op_const_bool False \<lbrace> Void \<longmapsto> \<val> False \<Ztypecolon> \<bool> \<rbrace>\<close>
  \<medium_left_bracket> \<open>False\<close> \<medium_right_bracket>.


subsection \<open>Not\<close>

lemma op_not[\<phi>overload \<not>, \<phi>synthesis 100]:
  \<open>\<proc> op_not raw \<lbrace> x \<Ztypecolon> \<val>[raw] \<bool> \<longmapsto> \<val> \<not> x \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_not_def
  by (cases raw, simp, rule, simp, rule,  simp)

subsection \<open>And\<close>

lemma op_and[\<phi>overload \<and>, \<phi>synthesis add]:
  \<open>\<proc> op_and (va\<^bold>, vb) \<lbrace> a \<Ztypecolon> \<val>[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<val>[vb] \<bool> \<longmapsto> \<val> (a \<and> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_and_def
  by (cases va; cases vb; simp, rule, rule, simp, rule, simp, rule, simp)


subsection \<open>Or\<close>

lemma op_or[\<phi>overload \<or>, \<phi>synthesis 100]:
  \<open>\<proc> op_or (va\<^bold>, vb) \<lbrace> a \<Ztypecolon> \<val>[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<val>[vb] \<bool> \<longmapsto> \<val> (a \<or> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_or_def
  by (cases va; cases vb, simp, rule, rule, simp, rule, simp, rule, simp)

subsection \<open>Xor\<close>

lemma op_xor[\<phi>overload \<oplus>, \<phi>synthesis 100]:
  \<open>\<proc> op_xor (va\<^bold>, vb) \<lbrace> a \<Ztypecolon> \<val>[va] \<bool>\<heavy_comma> b \<Ztypecolon> \<val>[vb] \<bool> \<longmapsto> \<val> (a \<and> \<not> b \<or> \<not> a \<and> b) \<Ztypecolon> \<bool> \<rbrace>\<close>
  unfolding op_xor_def
  by (cases va; cases vb, simp, rule, rule, simp, rule, simp, rule, simp)

subsection \<open>Equal\<close>

declare [[
    overloaded_operator_in_synthesis \<open>\<lambda>v. x \<Ztypecolon> T v\<close> \<open>\<lambda>v. y \<Ztypecolon> U v\<close> \<Rightarrow> \<open>\<lambda>v. x = y \<Ztypecolon> \<val>[v] \<bool>\<close>,
    overloaded_operator_in_synthesis
        \<open>\<lambda>v. x mod N \<Ztypecolon> T v\<close> \<open>\<lambda>v. y mod N \<Ztypecolon> U v\<close> \<Rightarrow> \<open>\<lambda>v. x mod N = y mod N \<Ztypecolon> \<val>[v] \<bool>\<close>
]]

lemma op_equal_\<phi>app[\<phi>overload =]:
  \<open> \<phi>Equal T can_eq eq
\<Longrightarrow> Semantic_Type' (a \<Ztypecolon> T) TY
\<Longrightarrow> Semantic_Type' (b \<Ztypecolon> T) TY
\<Longrightarrow> \<premise> can_eq a b
\<Longrightarrow> \<proc> op_equal TY (\<phi>V_pair rawa rawb) \<lbrace> a \<Ztypecolon> \<val>[rawa] T\<heavy_comma> b \<Ztypecolon> \<val>[rawb] T \<longmapsto> eq a b \<Ztypecolon> \<val> \<bool> \<rbrace>\<close>
  unfolding op_equal_def
  by ((cases rawa; cases rawb; simp, rule, rule),
      simp add: Semantic_Type'_def subset_iff Premise_def,
      simp add: Semantic_Type'_def subset_iff Premise_def, rule,
      unfold \<phi>Equal_def Premise_def, simp, simp,
      rule, simp)

declare op_equal_\<phi>app[where eq=\<open>(=)\<close>, \<phi>synthesis 100]
declare op_equal_\<phi>app[where eq=\<open>(\<lambda>x y. x mod N = y mod N)\<close> for N, \<phi>synthesis 100]



end
