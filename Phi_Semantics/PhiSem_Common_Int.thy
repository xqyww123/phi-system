theory PhiSem_Common_Int
  imports PhiSem_Generic_Boolean "HOL-Library.Signed_Division"
begin

section \<open>Preliminary\<close>

ML \<open>structure PhiSem_Common_Int_Notation_Patch = Theory_Data (
  type T = string; val empty = ""; val merge = K ""
)\<close>

setup \<open>
let val remove_synt = Sign.notation false Syntax.mode_default [
    (Const (\<^const_abbrev>\<open>inter\<close>, dummyT), Infixl (Input.string "Int", 70, Position.no_range)),
    (Const (\<^const_abbrev>\<open>union\<close>, dummyT), Infixl (Input.string "Un", 65, Position.no_range)),
    (Const (\<^const_name>\<open>Nats\<close>, dummyT), Mixfix (Input.string "\<nat>", [], 1000, Position.no_range)),
    (Const (\<^const_name>\<open>Ints\<close>, dummyT), Mixfix (Input.string "\<int>", [], 1000, Position.no_range))
  ]
in remove_synt
#> Theory.at_begin (fn thy =>
      if PhiSem_Common_Int_Notation_Patch.get thy = Context.theory_long_name thy
      then NONE
      else SOME (thy |> PhiSem_Common_Int_Notation_Patch.put (Context.theory_long_name thy)
                     |> remove_synt))
end\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

abbreviation LshR (infixl "LSHR" 70) where \<open>x LSHR y \<equiv> x div 2 ^ Big y\<close>
abbreviation LshL (infixl "LSHL" 70) where \<open>x LSHL y \<equiv> x  *  2 ^ Big y\<close>

\<phi>overloads nat and int


\<phi>overloads add and sub and mul and div and less and less_equal and greater and greater_equal
  and floor and ceiling and neg

declare [[
    overloaded_operator_in_synthesis \<open>(+)\<close>,
    overloaded_operator_in_synthesis \<open>(-)\<close>,
    overloaded_operator_in_synthesis \<open>uminus\<close>,
    overloaded_operator_in_synthesis \<open>(*)\<close>,
    overloaded_operator_in_synthesis \<open>(div)\<close>,
    overloaded_operator_in_synthesis \<open>(sdiv)\<close>,
    overloaded_operator_in_synthesis \<open>(/)\<close>,
    overloaded_operator_in_synthesis \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 < x2 \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 \<le> x2 \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>drop_bit\<close>,
    overloaded_operator_in_synthesis \<open>push_bit\<close>
]]

definition \<open>MK_CONST x \<equiv> x\<close>

lemma overloaded_synthesis_const:
  \<open>OPTIMAL_SYNTHESIS
   (\<p>\<r>\<o>\<c> H \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
\<Longrightarrow> \<p>\<r>\<o>\<c> H \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding Optimal_Synthesis_def Action_Tag_def MK_CONST_def .

lemma make_overloaded_synthesis_rule_for_const:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs::unit \<phi>arg. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. const \<Ztypecolon> T ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          (X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<phi>V_none \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<a>\<n>\<d> Any1
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<p>\<r>\<o>\<c> F \<phi>V_none \<lbrace> X' \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action overloaded_synthesis)\<close>
  unfolding MK_CONST_def split_paired_All_\<phi>arg_unit
  using make_overloaded_synthesis_rule[where 'a = \<open>unit \<phi>arg\<close> and X' = \<open>\<lambda>_. X'\<close>,
      unfolded split_paired_All_\<phi>arg_unit split_paired_all_\<phi>arg_unit] .

lemma make_overloaded_synthesis_rule'_for_const:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R'\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs::unit \<phi>arg. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          (X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<phi>V_none \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<a>\<n>\<d> Any1
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<p>\<r>\<o>\<c> F \<phi>V_none \<lbrace> X' \<longmapsto> \<lambda>ret. R'\<heavy_comma> R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
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
          Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<v>\<a>\<l>[ret] ?T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) _ _ \<close>]
  = make_overloaded_synthesis_rule_for_const [where const = x for x :: \<open>'a::numeral\<close>]
lemmas [\<phi>reason 2010 for \<open>PROP Gen_Synthesis_Rule (
          Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<v>\<a>\<l>[ret] ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) _ _ \<close>]
  = make_overloaded_synthesis_rule'_for_const[where const = x for x :: \<open>'a::numeral\<close>]

lemma [\<phi>reason 200]:
  \<open> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> 1 \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> Suc 0 \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding One_nat_def .

lemma [\<phi>reason 200]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> push_bit n x \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x * 2 ^ n \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  for x :: nat
  unfolding push_bit_nat_def .

lemma [\<phi>reason 200]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> push_bit n x \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x * 2 ^ n \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  for x :: int
  unfolding push_bit_int_def .


(*TODO:

disable the auto evaluation when the exponent is too large!

declare power_numeral[simp del]
*)
end