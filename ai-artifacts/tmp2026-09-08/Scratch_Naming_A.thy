theory Scratch_Naming_A
  imports Phi_Examples.Linked_List
begin

text \<open>Section 10.4 of the plan: one instance exported under two names gives two functions.\<close>

declare prepend_llist_def [\<phi>export prepend_a for \<int'>]
declare prepend_llist_def [\<phi>export prepend_b for \<int'>]

declare [[\<phi>export_code = C]]

end
