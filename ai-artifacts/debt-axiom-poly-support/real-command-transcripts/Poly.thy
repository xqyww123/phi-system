theory Poly
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>Plan section 8.4 items 1-4 and 7: the new polymorphic capability through
  the real commands.\<close>

text \<open>8.4-1 nontrivial sort; also 8.4-7: suite 1 C1's exact proposition ---
  before the fix this very declaration crashed with "Illegal fixed variable".\<close>
debt_axiomatization comm: \<open>x + y = y + (x::'a::comm_monoid_add)\<close>

thm comm
declare [[show_sorts = true]]
thm comm \<comment> \<open>8.4-1's "returned theorem = user-stated sorted form": the sorts survive\<close>
declare [[show_sorts = false]]
print_debt_axiom

text \<open>8.4-1 the two-variable different-sorts declaration.\<close>
debt_axiomatization two: \<open>(x::'a::linorder) \<le> x \<and> (y::'b::comm_monoid_add) + 0 = y\<close>

thm two
print_debt_axiom

text \<open>8.4-2 use the polymorphic debt at two instance types.\<close>
lemma use_nat: \<open>(3::nat) + 4 = 4 + 3\<close> by (rule comm)
lemma use_int: \<open>a + b = b + (a::int)\<close> by (rule comm)

text \<open>8.4-3 discharge at a strictly weaker certificate sort
  (debt at comm_monoid_add, certificate add.commute at ab_semigroup_add).\<close>
discharge_debt_axiom comm : add.commute

print_debt_axiom

text \<open>8.4-3 composite-type obligation: suite 3 G2a in situ
  (obligation OFCLASS('a set, preorder) closed by the reflected rule).\<close>
debt_axiomatization setrefl: \<open>(x::'a set) \<le> x\<close>

discharge_debt_axiom setrefl : order_refl

text \<open>8.4-4 NEGATIVE: certificate sort strictly exceeds the debt's.
  EXPECT the named error with the residual OFCLASS obligation displayed.\<close>
debt_axiomatization neg: \<open>x + y = y + (x::'a::ab_semigroup_add)\<close>

lemma strong_comm: \<open>x + y = y + (x::'a::comm_monoid_add)\<close>
  by (rule add.commute)

discharge_debt_axiom neg : strong_comm

print_debt_axiom

end
