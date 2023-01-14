theory PhiSem_CF_Return
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantic\<close>

virtual_datatype \<phi>CF_return_abnormal = \<phi>empty_abnormal +
  ABN_break    :: \<open>VAL list\<close> \<comment> \<open>in unit of bits\<close>


print_locale \<phi>CF_return_abnormal



end