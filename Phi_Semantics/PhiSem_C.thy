theory PhiSem_C
  imports PhiSem_Mem_C
          PhiSem_Mem_C_Ag_NT
          PhiSem_Mem_C_Ag_Ar
          PhiSem_CF_Routine
          PhiSem_CF_Breakable
          PhiSem_Variable
          PhiSem_Machine_Integer
          PhiSem_Machine_Integer_Boolean
          PhiSem_Mem_C_Ar_MI
begin

debt_axiomatization
  where ptr_neq_\<i>\<n>\<t>'  [simp]: \<open>\<ptr> \<noteq> sem_int_T n\<close>
    and ptr_neq_struct [simp]: \<open>\<ptr> \<noteq> semty_ntup f\<close>


lemma TY_neqs[simp]:
  \<open>\<ptr> \<noteq> \<i>\<n>\<t>('n)\<close>         \<open>\<i>\<n>\<t>('n) \<noteq> \<ptr>\<close>
  \<open>\<ptr> \<noteq> \<b>\<o>\<o>\<l>\<close>            \<open>\<b>\<o>\<o>\<l> \<noteq> \<ptr>\<close>
  \<open>semty_ntup f \<noteq> \<ptr>\<close>
  unfolding mk_int_T_def bool_def'
  by simp_all (metis ptr_neq_\<i>\<n>\<t>' ptr_neq_struct)+



(*declare [[\<phi>infer_requirements]]*)

(*
setup \<open>Context.theory_map (Phi_Hacks.Thy_At_Begin.add 66 (K (
  Simplifier.map_theory_simpset (fn ctxt => ctxt delsimps @{thms' Nat.One_nat_def Num.add_2_eq_Suc'}))))
\<close> 

declare One_nat_def[\<phi>sledgehammer_simps] *)

end