theory PhiSem_Base
  imports Phi_System.PhiSem_Formalization_Tools
begin


type_synonym symbol = string \<comment> \<open>Right now we are using string directly which is very inefficient.
  In future, we will instead use a global stateful symbol table that assigns each string dynamically
  to a numeric index that is unique throughout the ML execution session.
  The approach ensures semantic equity and, only takes logarithm space to the total number of symbols.
\<close>
type_synonym field_name = symbol

end