theory Before_T1
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>Before-transcript 1 (plan section 8.3-0, recorded on the UNPATCHED worktree):
  a premised monomorphic debt, discharged by a monomorphic certificate of the
  same statement.  EXPECT: the discharge fails with "Proof failed." --- the
  production tactic is a single ares_tac application, which resolves once and
  cannot close the residual premise subgoal (defect 3).\<close>

print_debt_axiom

debt_axiomatization before1: \<open>n < m \<Longrightarrow> n \<le> (m::nat)\<close>

print_debt_axiom

lemma before1_cert: \<open>n < m \<Longrightarrow> n \<le> (m::nat)\<close>
  by (rule less_imp_le)

discharge_debt_axiom before1 : before1_cert

print_debt_axiom

end
