theory Before_T2
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>Before-transcript 2 (plan section 8.3-0, recorded on the UNPATCHED worktree):
  an unconditional monomorphic debt, discharged by a POLYMORPHIC library
  certificate (add.commute at sort ab_semigroup_add, instantiated to nat by
  resolution).  EXPECT: success --- this is the ground-instantiation case that
  already works today, and it must keep working after the patch (section 8.3-4).\<close>

print_debt_axiom

debt_axiomatization before2: \<open>(x::nat) + y = y + x\<close>

print_debt_axiom

discharge_debt_axiom before2 : add.commute

print_debt_axiom

end
