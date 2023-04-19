theory PhiTest_1
  imports Phi_Semantics.PhiSem_Generic_Boolean
          Phi_Semantics.PhiSem_CF_Basic
          Phi_Semantics.PhiSem_Int_ArbiPrec
          Phi_Semantics.PhiSem_Machine_Integer
begin

proc
  input \<open>Void\<close>
  output \<open>Void\<close>
  \<medium_left_bracket>
    while \<open>Inv: True \<and> Guard: False\<close>
    \<medium_left_bracket> \<open>False\<close> \<medium_right_bracket>.
    \<medium_left_bracket> have \<open>False\<close> using that(2) by blast \<medium_right_bracket>.
  \<medium_right_bracket>. .

end