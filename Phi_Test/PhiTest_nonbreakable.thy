theory PhiTest_nonbreakable
  imports Phi_Semantics.PhiSem_CF_Basic
begin

proc
  input  \<open>Void\<close>
  output \<open>Void\<close>
  \<medium_left_bracket>
    while \<open>Void \<s>\<u>\<b>\<j> Inv: True \<and> Guard: False\<close>
    \<medium_left_bracket> False \<medium_right_bracket>.
    \<medium_left_bracket>
      have \<open>False\<close> using that(2) by force
    \<medium_right_bracket>.
    \<medium_right_bracket>. .

end