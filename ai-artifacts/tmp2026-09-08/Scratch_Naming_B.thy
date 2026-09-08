theory Scratch_Naming_B
  imports Phi_Examples.Linked_List
begin

text \<open>Section 10.4 of the plan: an export name with the shape of a generated name is refused.\<close>

declare pop_llist_def [\<phi>export f__x for \<int'>]

declare [[\<phi>export_code = C]]

end
