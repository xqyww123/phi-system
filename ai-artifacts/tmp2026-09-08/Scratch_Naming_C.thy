theory Scratch_Naming_C
  imports Phi_Examples.Linked_List
begin

text \<open>Section 10.4 of the plan: an export name spelled like a local variable is refused.\<close>

declare pop_llist_def [\<phi>export "_v12" for \<int'>]

declare [[\<phi>export_code = C]]

end
