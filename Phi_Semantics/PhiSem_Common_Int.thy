theory PhiSem_Common_Int
  imports Phi_System.PhiSem_Formalization_Tools
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

end