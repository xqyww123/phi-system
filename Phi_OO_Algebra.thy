theory Phi_OO_Algebra
  imports Main
begin

chapter \<open>Algebra of Class Dependency\<close>

datatype 'fields "class" = Class (name: string) (parents: \<open>'fields class list\<close>) (fields: 'fields)
hide_const (open) name parents fields

text \<open>Name of a class is not its identity but the name plus parents.
  It simplifies the model by ensuring two identical classes have identical parents.\<close>

fun parents_of_with_self
  where \<open>parents_of_with_self (Class name parents fields) =
            insert (Class name parents fields) (\<Union> (parents_of_with_self ` set parents))\<close>

instantiation "class" :: (type) order begin

definition \<open>less_eq_class C1 C2 \<longleftrightarrow> C2 \<in> parents_of_with_self C1\<close>
definition \<open>less_class (C1::'a class) C2 \<longleftrightarrow> C1 \<le> C2 \<and> C1 \<noteq> C2\<close>

instance proof
  fix x y z :: \<open>'a class\<close>

  have \<open>\<And>x y S'. x \<in> parents_of_with_self y \<Longrightarrow> x \<noteq> y \<Longrightarrow> size_class S' x < size_class S' y\<close>
  subgoal for x y S'
  apply (induct y arbitrary: x)
  subgoal for name parents fields x
    apply clarsimp
    subgoal for z
      apply (cases \<open>x = z\<close>)
       apply (metis not_add_less1 not_less_eq size_list_estimation)
      by (simp add: less_Suc_eq size_list_estimation trans_less_add1) . . .
  then have t1: \<open>\<And>x y. y \<in> parents_of_with_self x \<and> x \<in> parents_of_with_self y \<Longrightarrow> x = y\<close>
    by (metis order_less_asym)
  then  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    apply (simp_all add: less_eq_class_def less_class_def)
    by blast

  show \<open> x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_class_def less_class_def t1)

  show \<open>x \<le> x\<close>
    by (cases x; simp add: less_eq_class_def less_class_def)

  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    unfolding less_eq_class_def less_class_def
    by (induct x, auto)
qed
end

lemma [simp]: \<open>x \<in> parents_of_with_self x\<close>
  by (cases x, simp)

lemma [simp]: \<open>Class name (x # L) fields \<noteq> x\<close>
proof
  assume A: \<open>Class name (x # L) fields = x\<close>
  then have t: \<open>\<And>S. size_class S (Class name (x # L) fields) = size_class S x\<close> by simp
  then show False
    by (metis A add_Suc_right class.size(2) list.set_intros(1) not_add_less1 not_less_eq size_list_estimation)
qed

lemma prop_subclass_1[intro]: \<open>Class name (x#L) fields < x\<close>
  unfolding less_class_def less_eq_class_def by simp

lemma subclass_1[intro]: \<open>Class name (x#L) fields \<le> x\<close>
  unfolding less_class_def less_eq_class_def by simp

lemma subclass_0[intro]: \<open>x \<le> x\<close> for x :: \<open>'a class\<close> by simp

(* TODO!
 lemma [intro]: \<open>Class name L \<le> x \<Longrightarrow> Class name (y#L) \<le> x\<close>
  unfolding less_class_def less_eq_class_def apply simp*)



end