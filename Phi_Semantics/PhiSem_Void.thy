theory PhiSem_Void
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantics\<close>

debt_axiomatization \<v>\<o>\<i>\<d> :: TY
  where WT_void  [simp]: \<open>Well_Type \<v>\<o>\<i>\<d> = {} \<close>

end