theory PhiSem_Common_Int
  imports PhiSem_Generic_Boolean
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
    overloaded_operator_in_synthesis \<open>(/)\<close>,
    overloaded_operator_in_synthesis \<open>(<)\<close>
      :: \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 < x2 \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>(\<le>)\<close>
      :: \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 \<le> x2 \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>drop_bit\<close>,
    overloaded_operator_in_synthesis \<open>push_bit\<close>
]]

declare [[overloaded_operator_in_synthesis 1300 \<open>\<lambda>x n. x * 2 ^ n\<close>]]


(*TODO:

disable the auto evaluation when the exponent is too large!

declare power_numeral[simp del]
*)
end