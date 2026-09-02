theory Deps
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>Plan section 8.4-5 NEGATIVE: a certificate derived FROM a debt is
  rejected by the kernel's oracle-dependency check (the certificate's
  proposition equals the ledger entry, so the op = acceptance is also on the
  path --- the dep check fires first).\<close>

debt_axiomatization dep1: \<open>(0::nat) < 1\<close>

lemma derived: \<open>(0::nat) < 1\<close> by (rule dep1)

discharge_debt_axiom dep1 : derived

print_debt_axiom

end
