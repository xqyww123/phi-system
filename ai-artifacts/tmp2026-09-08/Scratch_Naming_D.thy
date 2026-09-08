theory Scratch_Naming_D
  imports Phi_Examples.Linked_List
begin

text \<open>Section 10.4 of the plan: an export whose body reaches no routine is refused.\<close>

proc identity_inline:
  input  \<open>x \<Ztypecolon> \<val> \<nat>(\<int'>)\<close>
  output \<open>x \<Ztypecolon> \<val> \<nat>(\<int'>)\<close>
\<medium_left_bracket>
  $x
\<medium_right_bracket> .

declare identity_inline_def [\<phi>export]

declare [[\<phi>export_code = C]]

end
