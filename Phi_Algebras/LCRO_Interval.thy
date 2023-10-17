theory LCRO_Interval
  imports Algebras
begin

section \<open>Left Closed Right Open Intervals\<close>

subsection \<open>Definition\<close>

typedef (overloaded) 'a lcro_interval =
  "{(a::'a::preorder, b). a \<le> b}"
  morphisms bounds_of_interval Interval'
  by auto

setup_lifting type_definition_lcro_interval

definition Interval :: \<open>'a::preorder \<Rightarrow> 'a \<Rightarrow> 'a lcro_interval\<close> ("[_,_')" [51,51] 1000)
  where \<open>[l,u) \<equiv> Interval' (l,u)\<close>

lift_definition lower::"('a::preorder) lcro_interval \<Rightarrow> 'a" is fst .

lift_definition upper::"('a::preorder) lcro_interval \<Rightarrow> 'a" is snd .

lemma lower_interval[simp]:
  \<open>a \<le> b \<Longrightarrow> lower [a,b) = a\<close>
  unfolding Interval_def lower_def
  by (simp add: Interval'_inverse)

lemma upper_interval[simp]:
  \<open>a \<le> b \<Longrightarrow> upper [a,b) = b\<close>
  unfolding Interval_def upper_def
  by (simp add: Interval'_inverse)

lemma interval_eq_iff: "a = b \<longleftrightarrow> lower a = lower b \<and> upper a = upper b"
  by transfer auto

lemma interval_eqI: "lower a = lower b \<Longrightarrow> upper a = upper b \<Longrightarrow> a = b"
  by (auto simp: interval_eq_iff)

lemma lower_le_upper[simp]: "lower i \<le> upper i"
  by transfer auto


subsubsection \<open>Set of\<close>

lift_definition set_of :: "'a::preorder lcro_interval \<Rightarrow> 'a set" is "\<lambda>x. {fst x ..< snd x}" .
  
lemma set_of_eq: "set_of x = {lower x ..< upper x}"
  by transfer simp


subsection \<open>Properties\<close>

subsubsection \<open>Equal\<close>

instantiation lcro_interval :: ("{preorder,equal}") equal
begin

definition "equal_class.equal a b \<equiv> (lower a = lower b) \<and> (upper a = upper b)"

instance proof qed (simp add: equal_lcro_interval_def interval_eq_iff)
end


subsubsection \<open>Order \& Lattice\<close>

instantiation lcro_interval :: ("preorder") ord begin

definition less_eq_lcro_interval :: "'a lcro_interval \<Rightarrow> 'a lcro_interval \<Rightarrow> bool"
  where "less_eq_lcro_interval a b \<longleftrightarrow> lower b \<le> lower a \<and> upper a \<le> upper b"

definition less_lcro_interval :: "'a lcro_interval \<Rightarrow> 'a lcro_interval \<Rightarrow> bool"
  where  "less_lcro_interval x y = (x \<le> y \<and> \<not> y \<le> x)"

instance proof qed
end


instantiation lcro_interval :: ("lattice") semilattice_sup
begin

lift_definition sup_lcro_interval :: "'a lcro_interval \<Rightarrow> 'a lcro_interval \<Rightarrow> 'a lcro_interval"
  is "\<lambda>(a, b) (c, d). (inf a c, sup b d)"
  by (auto simp: le_infI1 le_supI1)

lemma lower_sup[simp]: "lower (sup A B) = inf (lower A) (lower B)"
  by transfer auto

lemma upper_sup[simp]: "upper (sup A B) = sup (upper A) (upper B)"
  by transfer auto

instance proof qed (auto simp: less_eq_lcro_interval_def less_lcro_interval_def interval_eq_iff)
end

lemma set_of_interval_union:
  "set_of A \<union> set_of B \<subseteq> set_of (sup A B)"
  for A::"'a::lattice lcro_interval"
  apply (auto simp: set_of_eq le_infI1 less_supI1 )
  using le_infI2 apply blast
  by (simp add: less_supI2)

lemma interval_union_commute: "sup A B = sup B A" for A::"'a::lattice lcro_interval"
  by (auto simp add: interval_eq_iff inf.commute sup.commute)

lemma interval_union_mono1: "set_of a \<subseteq> set_of (sup a A)" for A :: "'a::lattice lcro_interval"
  using set_of_interval_union by blast

lemma interval_union_mono2: "set_of A \<subseteq> set_of (sup a A)" for A :: "'a::lattice lcro_interval"
  using set_of_interval_union by blast



subsubsection \<open>Partial Addition\<close>

text \<open>Defined as concatenating two adjoint intervals.\<close>

instantiation lcro_interval :: (preorder) partial_add_cancel begin

lift_definition plus_lcro_interval :: \<open>'a lcro_interval \<Rightarrow> 'a lcro_interval \<Rightarrow> 'a lcro_interval\<close>
  is \<open>\<lambda>(a,b) (c,d). if b = c then (a,d) else (undefined, undefined)\<close>
  by (clarsimp; metis Pair_inject dual_order.trans order_eq_refl)

lift_definition dom_of_add_lcro_interval :: \<open>'a lcro_interval \<Rightarrow> 'a lcro_interval \<Rightarrow> bool\<close>
  is \<open>\<lambda>(a,b) (c,d). b = c\<close> .

lemma dom_of_add_lcro_interval[simp]:
  \<open>a ##\<^sub>+ b \<longleftrightarrow> upper a = lower b\<close>
  by (transfer; clarsimp)

lemma add_lcro_interval_inj[simp]:
  \<open>a ##\<^sub>+ b \<Longrightarrow> lower (a + b) = lower a\<close>
  \<open>a ##\<^sub>+ b \<Longrightarrow> upper (a + b) = upper b\<close>
  by (transfer; clarsimp)+

instance by (standard; clarsimp simp add: interval_eq_iff)
end

lemma dom_of_add_lcro_interval'[simp]:
  \<open>\<lbrakk> a \<le> b ; c \<le> d \<rbrakk> \<Longrightarrow> [a,b) ##\<^sub>+ [c,d) \<longleftrightarrow> b = c\<close>
  by simp

lemma add_lcro_interval [simp]:
  \<open>\<lbrakk> a \<le> b ; b \<le> c \<rbrakk> \<Longrightarrow> [a,b) + [b,c) = [a,c)\<close>
  using interval_eq_iff order_trans by fastforce

lemma set_of_add_interval:
  \<open>a ##\<^sub>+ b \<Longrightarrow> set_of (a + b) = set_of a \<union> set_of b\<close>
  for a :: \<open>'a::linorder lcro_interval\<close>
  by (clarsimp simp add: set_of_eq; metis ivl_disj_un_two(3) lower_le_upper)

lemma additive_join_sub_interval:
  \<open>y \<preceq>\<^sub>+ z \<longleftrightarrow> upper y = upper z \<and> lower z \<le> lower y\<close>
  unfolding additive_join_sub_def
  by (simp add: interval_eq_iff, rule,
      metis add_lcro_interval_inj dom_of_add_lcro_interval lower_le_upper,
      rule exI[where x=\<open>[lower z, lower y)\<close>]; clarsimp)

instance lcro_interval :: (order) positive_partial_add_magma
  by (standard;
      clarsimp simp add: additive_join_sub_def interval_eq_iff;
      metis lower_le_upper order_antisym)

text \<open>lcro_interval is not strict positive as there are zero element [x,x)\<close>

instance lcro_interval :: (order) partial_semigroup_add
  by (standard; clarsimp simp add: interval_eq_iff)

text \<open>lcro_interval is also a good example where it is not dom_of_add_intuitive,
      and also where has unique neutral for each element but not a unique one.\<close>

instance lcro_interval :: (order) partial_cancel_semigroup_add
  by (standard; clarsimp simp add: interval_eq_iff)


subsubsection \<open>Membership\<close>

definition interval_membership :: \<open>'a::preorder \<Rightarrow> 'a lcro_interval \<Rightarrow> bool\<close> (infix "\<in>\<^sub>I" 50)
  where [simp]: \<open>x \<in>\<^sub>I i \<longleftrightarrow> lower i \<le> x \<and> x < upper i\<close>

lemma not_in_empty_interval[simp]:
  \<open>\<not> (x \<in>\<^sub>I [a,a))\<close>
  for x :: \<open>'a::order\<close>
  by (simp add: leD)

subsubsection \<open>Width\<close>

abbreviation width_of :: \<open>'a::{preorder, minus} lcro_interval \<Rightarrow> 'a\<close>
  where \<open>width_of i \<equiv> (upper i - lower i)\<close>

hide_const (open) width_of lower upper

end