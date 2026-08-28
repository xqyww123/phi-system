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
  where ptr_neq_int_t'  [simp]: \<open>\<ptr> \<noteq> sem_int_T n\<close>
    and ptr_neq_struct [simp]: \<open>\<ptr> \<noteq> sem_ntup_T f\<close>
    and int_t_neq_struct [simp]: \<open>sem_int_T n \<noteq> sem_ntup_T f\<close>
    and struct_neq_array [simp]: \<open>sem_ntup_T f \<noteq> \<poison> \<Longrightarrow> sem_ntup_T f \<noteq> \<array>[N] TY\<close>
      \<comment> \<open>This is the earliest theory that sees both the named tuple and the array
          constructor (they enter through the sibling theories PhiSem_Mem_C_Ag_NT
          and PhiSem_Mem_C_Ag_Ar).  Unlike \<open>\<ptr>\<close> and \<open>sem_int_T\<close>, BOTH of these
          constructors degenerate to \<open>\<poison>\<close> -- \<open>\<array>[N] TY = \<poison>\<close> when \<open>TY = \<poison>\<close> and
          \<open>N \<noteq> 0\<close> (semty_array_eq_poison), \<open>sem_ntup_T f = \<poison>\<close> when a field is
          \<open>\<poison>\<close> (semty_ntup_eq_poison) -- and there they really are equal, so an
          unguarded distinctness axiom would be FALSE.  One guarded direction
          suffices; the other is derived below.\<close>


lemma TY_neqs[simp]:
  \<open>\<ptr> \<noteq> \<int'>('n)\<close>         \<open>\<int'>('n) \<noteq> \<ptr>\<close>
  \<open>\<ptr> \<noteq> \<bool'>\<close>            \<open>\<bool'> \<noteq> \<ptr>\<close>
  \<open>sem_ntup_T f \<noteq> \<ptr>\<close>
  unfolding mk_int_T_def bool_def'
  by simp_all (metis ptr_neq_int_t' ptr_neq_struct)+

lemma struct_neq_int_t [simp]:
  \<open>sem_ntup_T f \<noteq> sem_int_T n\<close>
  using int_t_neq_struct by (rule not_sym)

lemma array_neq_struct [simp]:
  \<open>\<array>[N] TY \<noteq> \<poison> \<Longrightarrow> \<array>[N] TY \<noteq> sem_ntup_T f\<close>
  by (metis struct_neq_array)



(*declare [[\<phi>infer_requirements]]*)

(*
setup \<open>Context.theory_map (Phi_Hacks.Thy_At_Begin.add 66 (K (
  Simplifier.map_theory_simpset (fn ctxt => ctxt delsimps @{thms' Nat.One_nat_def Num.add_2_eq_Suc'}))))
\<close> 

declare One_nat_def[\<phi>sledgehammer_simps] *)

end