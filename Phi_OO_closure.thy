theory Phi_OO_closure
  imports Phi_OO
begin

section \<open>Closure of State Transitions\<close>

print_locale \<phi>resource_sem
locale transition_closure =
  \<phi>resource_sem Resource_Validator
  for Resource_Validator :: "'RES_N \<Rightarrow> 'RES::{comm_monoid_mult,no_inverse} set"
+ fixes 

end