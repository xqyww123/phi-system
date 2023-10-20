theory PhiSem_OO_Class_Algebra
  imports PhiSem_Base
begin

section \<open>Algebraic Model of Class dependency\<close>

datatype 'members class_algebra =
  Class (name: string) (parents: \<open>'members class_algebra list\<close>) (members: 'members)

text \<open>If two classes having the same name but different parents or members,
  they are merely two different classes having the same name.

  If two classes having the identical parents and members but different names,
  they are still two different classes despite of similarity.

  The name may be used as a syntactical identifier in language implementations, but the equity of
    the names in the semantics never means the equity of the classes.

  The member is generic, which may contain types of fields, table of virtual functions.
\<close>

hide_const (open) name parents members

fun self_and_parents_of :: "'a class_algebra \<Rightarrow> 'a class_algebra set" 
  where \<open>self_and_parents_of (Class name parents fields) =
            insert (Class name parents fields) (\<Union> (self_and_parents_of ` set parents))\<close>

instantiation class_algebra :: (type) order begin

definition \<open>less_eq_class_algebra C1 C2 \<longleftrightarrow> C2 \<in> self_and_parents_of C1\<close>
definition \<open>less_class_algebra (C1::'a class_algebra) C2 \<longleftrightarrow> C1 \<le> C2 \<and> C1 \<noteq> C2\<close>

instance proof
  fix x y z :: \<open>'a class_algebra\<close>

  have \<open>\<And>x y S'. x \<in> self_and_parents_of y \<Longrightarrow> x \<noteq> y
            \<Longrightarrow> size_class_algebra S' x < size_class_algebra S' y\<close>
  subgoal for x y S'
  apply (induct y arbitrary: x)
  subgoal for name parents fields x
    apply clarsimp
    subgoal for z
      apply (cases \<open>x = z\<close>)
       apply (metis not_add_less1 not_less_eq size_list_estimation)
      by (simp add: less_Suc_eq size_list_estimation trans_less_add1) . . .
  then have t1: \<open>\<And>x y. y \<in> self_and_parents_of x \<and> x \<in> self_and_parents_of y \<Longrightarrow> x = y\<close>
    by (metis order_less_asym)
  then  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    apply (simp_all add: less_eq_class_algebra_def less_class_algebra_def)
    by blast

  show \<open> x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_class_algebra_def less_class_algebra_def t1)

  show \<open>x \<le> x\<close>
    by (cases x; simp add: less_eq_class_algebra_def less_class_algebra_def)

  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    unfolding less_eq_class_algebra_def less_class_algebra_def
    by (induct x, auto)
qed
end

lemma [simp]: \<open>x \<in> self_and_parents_of x\<close>
  by (cases x, simp)

lemma [simp]: \<open>Class name (x # L) members \<noteq> x\<close>
proof
  assume A: \<open>Class name (x # L) members = x\<close>
  then have t: \<open>\<And>S. size_class_algebra S (Class name (x # L) members) = size_class_algebra S x\<close> by simp
  then show False
    by (metis A add_Suc_right class_algebra.size(2) list.set_intros(1) not_add_less1 not_less_eq size_list_estimation)
qed

lemma prop_subclass_1[intro]: \<open>Class name (x#L) members < x\<close>
  unfolding less_class_algebra_def less_eq_class_algebra_def by simp

lemma subclass_1[intro]: \<open>Class name (x#L) members \<le> x\<close>
  unfolding less_class_algebra_def less_eq_class_algebra_def by simp

lemma subclass_0[intro]: \<open>x \<le> x\<close> for x :: \<open>'a class_algebra\<close> by simp

(* TODO: Give more automation for evaluating the inheritance.


 lemma [intro]: \<open>Class name L \<le> x \<Longrightarrow> Class name (y#L) \<le> x\<close>
  unfolding less_class_def less_eq_class_def apply simp*)

lemma self_and_parents_of__finite:
  \<open>finite (self_and_parents_of x)\<close>
  by (induct x; simp)


(*I'm thinking if we use product or addition.*)
definition inherited_members_of :: \<open>'m class_algebra \<Rightarrow> 'm::comm_monoid_mult\<close>
  where \<open>inherited_members_of cls = prod class_algebra.members (self_and_parents_of cls)\<close>


type_synonym "class" = \<open>(field_name \<rightharpoonup> TY discrete) class_algebra\<close>

setup \<open>Sign.mandatory_path "class"\<close>

abbreviation fields_of :: \<open>class \<Rightarrow> field_name \<rightharpoonup> TY discrete\<close>
  where \<open>fields_of \<equiv> inherited_members_of\<close>

setup \<open>Sign.parent_path\<close>


end