theory PhiSem_Common_Int
  imports PhiSem_Generic_Boolean "HOL-Library.Signed_Division"
begin

section \<open>Preliminary\<close>

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

abbreviation LshR (infixl "LSHR" 70) where \<open>x LSHR y \<equiv> x div 2 ^ Big y\<close>
abbreviation LshL (infixl "LSHL" 70) where \<open>x LSHL y \<equiv> x  *  2 ^ Big y\<close>

\<phi>overloads nat and int

\<phi>overloads "+" and "-" and "*" and "/" and "<" and "\<le>" and ">" and "\<ge>" and "=" and "\<not>"
  and "\<and>" and "\<or>"

declare [[
    overloaded_operator_in_synthesis \<open>(+)\<close>,
    overloaded_operator_in_synthesis \<open>(-)\<close>,
    overloaded_operator_in_synthesis \<open>(*)\<close>,
    overloaded_operator_in_synthesis \<open>(div)\<close>,
    overloaded_operator_in_synthesis \<open>(sdiv)\<close>,
    overloaded_operator_in_synthesis \<open>(/)\<close>,
    overloaded_operator_in_synthesis \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 < x2 \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 \<le> x2 \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>drop_bit\<close>,
    overloaded_operator_in_synthesis \<open>push_bit\<close>
]]

definition \<open>MK_CONST x \<equiv> x\<close>

lemma overloaded_synthesis_const:
  \<open>OPTIMAL_SYNTHESIS
   (\<^bold>p\<^bold>r\<^bold>o\<^bold>c H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2 \<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action overloaded_synthesis)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> const \<Ztypecolon> T ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis\<close>
  unfolding Optimal_Synthesis_def Action_Tag_def MK_CONST_def .

lemma make_overloaded_synthesis_rule_for_const:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs::unit \<phi>arg. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. const \<Ztypecolon> T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))
          Ant
          (X' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<phi>V_none \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<^bold>a\<^bold>n\<^bold>d Any1
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<phi>V_none \<lbrace> X' \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E'
           @action overloaded_synthesis)\<close>
  unfolding MK_CONST_def split_paired_All_\<phi>arg_unit
  using make_overloaded_synthesis_rule[where 'a = \<open>unit \<phi>arg\<close> and X' = \<open>\<lambda>_. X'\<close>,
      unfolded split_paired_All_\<phi>arg_unit split_paired_all_\<phi>arg_unit] .

lemma make_overloaded_synthesis_rule'_for_const:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R'\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs::unit \<phi>arg. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> const \<Ztypecolon> T ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))
          Ant
          (X' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<phi>V_none \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<^bold>a\<^bold>n\<^bold>d Any1
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<phi>V_none \<lbrace> X' \<longmapsto> \<lambda>ret. R'\<heavy_comma> R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E'
           @action overloaded_synthesis)\<close>
  unfolding MK_CONST_def split_paired_All_\<phi>arg_unit
  using make_overloaded_synthesis_rule'[where 'a = \<open>unit \<phi>arg\<close>,
      unfolded split_paired_All_\<phi>arg_unit split_paired_all_\<phi>arg_unit] .


lemmas [\<phi>reason 60]
  = overloaded_synthesis_const[where const=\<open>0\<close>]
lemmas [\<phi>reason 60]
  = overloaded_synthesis_const[where const=\<open>1\<close>]
lemmas [\<phi>reason 60]
  = overloaded_synthesis_const[where const=\<open>numeral x\<close> for x]

lemmas [\<phi>reason 2000 for \<open>PROP Gen_Synthesis_Rule (
          Trueprop (\<forall>vs. \<^bold>p\<^bold>r\<^bold>o\<^bold>c _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[ret] ?T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E )) _ _ \<close>]
  = make_overloaded_synthesis_rule_for_const [where const = x for x :: \<open>'a::numeral\<close>]
lemmas [\<phi>reason 2010 for \<open>PROP Gen_Synthesis_Rule (
          Trueprop (\<forall>vs. \<^bold>p\<^bold>r\<^bold>o\<^bold>c _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[ret] ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E )) _ _ \<close>]
  = make_overloaded_synthesis_rule'_for_const[where const = x for x :: \<open>'a::numeral\<close>]

lemma [\<phi>reason 200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> 1 \<Ztypecolon> T ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> Suc 0 \<Ztypecolon> T ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis\<close>
  unfolding One_nat_def .

lemma [\<phi>reason 200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> push_bit n x \<Ztypecolon> Y ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x * 2 ^ n \<Ztypecolon> Y ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis\<close>
  for x :: nat
  unfolding push_bit_nat_def .

lemma [\<phi>reason 200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> push_bit n x \<Ztypecolon> Y ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x * 2 ^ n \<Ztypecolon> Y ret \<brangle> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis\<close>
  for x :: int
  unfolding push_bit_int_def .


(*TODO:

disable the auto evaluation when the exponent is too large!

declare power_numeral[simp del]
*)
end