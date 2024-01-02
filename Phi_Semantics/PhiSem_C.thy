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

setup \<open>Context.theory_map (Phi_Hacks.Thy_At_Begin.add 66 (K (
  Simplifier.map_theory_simpset (fn ctxt => ctxt delsimps @{thms' Nat.One_nat_def Num.add_2_eq_Suc'}))))
\<close>

end