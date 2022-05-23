theory Resource_Algebra
  imports Main "Statespace/StateSpaceLocale"
    "Statespace/StateSpaceSyntax"
    "HOL.Rat"
    "HOL-Library.Simps_Case_Conv"
  keywords "resource_space" :: thy_defn
    and "fiction_space" :: thy_defn
begin

section \<open>Resource Algebra\<close>

subsection \<open>Algebric Structures\<close>

class undef =
  fixes undef :: "'a"

class validity =
  fixes \<V> :: "'a \<Rightarrow> bool"

class trivial_validity = validity +
  assumes trivial_validity[simp]: "\<V> x"

class unital_add = plus + zero +
  assumes unital_add_left[simp]: "0 + x = x"
    and unital_add_right[simp]: "x + 0 = x"

subclass (in monoid_add) unital_add by standard simp_all

class unital_ra = validity + unital_add +
  assumes unit_valid[simp]: "\<V> 0"

class discrete_ura = unital_ra + undef +
  assumes plus_discrete_ura[simp]:
    "x + y = (if x = 0 then y else if y = 0 then x else if x = y then x else undef)"
  assumes validity_discrete_ura[simp]: "\<V> x \<longleftrightarrow> (x \<noteq> undef)"
begin
lemma [simp]: "undef \<noteq> 0"
  using local.unit_valid local.validity_discrete_ura by blast
end

subsection \<open>Instances of Algebric Structures\<close>

subsubsection \<open>Function\<close>

instantiation "fun" :: (type, unital_ra) unital_ra begin
definition "zero_fun = (\<lambda>_. 0)"
definition "\<V>_fun f \<longleftrightarrow> (\<forall>x. \<V> (f x))"
definition "plus_fun f g = (\<lambda>x. f x + g x)"
lemmas unital_ra_fun_simps = zero_fun_def \<V>_fun_def plus_fun_def
instance by standard (simp_all add: unital_ra_fun_simps)
end

subsubsection \<open>List\<close>

instantiation list :: (type) monoid_add begin
definition "plus_list = (@)"
definition "zero_list = []"
instance by standard (simp_all add: plus_list_def zero_list_def)
end

instantiation list :: (validity) unital_ra begin
definition "\<V>_list = list_all \<V>"
instance by standard (simp add: \<V>_list_def zero_list_def)
end

instantiation list :: (trivial_validity) trivial_validity begin
instance by standard (simp add: \<V>_list_def list_all_length)
end

subsubsection \<open>Option\<close>


instantiation option :: (validity) discrete_ura begin
definition "undef_option = (None::'a option)"
primrec \<V>_option where "\<V>_option (Some x) \<longleftrightarrow> \<V> x" | "\<V>_option None \<longleftrightarrow> True"
definition "plus_option x' y' =
  (case x' of Some x \<Rightarrow> (case y' of Some y \<Rightarrow> if x = y then Some x else None))"
end

subsubsection \<open>Nat\<close>

instantiation nat :: unital_ra begin
definition [simp]: "\<V>_nat (_::nat) \<longleftrightarrow> True"
instance by standard simp
end


subsection \<open>Algebras\<close>


subsubsection \<open>Fractional Ownership\<close>

typedef ownership = \<open>{ ow::rat. 0 < ow }\<close>
  using zero_less_one by blast 
setup_lifting type_definition_ownership

instantiation ownership :: one begin
lift_definition one_ownership :: ownership is 1 by simp
instance ..
end

instantiation ownership :: linorder begin
lift_definition less_eq_ownership :: "ownership \<Rightarrow> ownership \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_ownership :: "ownership \<Rightarrow> ownership \<Rightarrow> bool" is "(<)" .
instance proof
  fix x y z :: ownership
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by transfer auto
  show "x \<le> x" by transfer simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by transfer simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by transfer simp
  show "x \<le> y \<or> y \<le> x" by transfer auto
qed
end

instantiation ownership :: strict_ordered_ab_semigroup_add begin

lift_definition plus_ownership :: "ownership \<Rightarrow> ownership \<Rightarrow> ownership" is "(+)" by simp

instance proof
  fix a b c d :: ownership
  show "a + b + c = a + (b + c)" by transfer simp
  show "a + b = b + a" by transfer simp
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b" by transfer simp
  show "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d" by transfer simp
qed
end

lemma ownership_add_leD1[dest]: "a + b \<le> c \<Longrightarrow> a \<le> c"
  and ownership_add_leD2[dest]: "a + b \<le> c \<Longrightarrow> b \<le> c"
  for a :: ownership by (transfer, simp)+

instantiation ownership :: numeral begin
instance ..
end

class ab_group_mult = inverse + comm_monoid_mult +
  assumes ab_left_inverse: "inverse a * a = 1"
  assumes ab_diff_conv_add_uminus: "a / b = a * (inverse b)"

instantiation ownership :: ab_group_mult begin
lift_definition inverse_ownership :: "ownership \<Rightarrow> ownership" is inverse by simp
lift_definition divide_ownership :: "ownership \<Rightarrow> ownership \<Rightarrow> ownership" is "(/)" by simp
lift_definition times_ownership :: "ownership \<Rightarrow> ownership \<Rightarrow> ownership" is "(*)" by simp

instance proof
  fix a b c :: ownership
  show "a * b * c = a * (b * c)" by transfer simp
  show "a * b = b * a" by transfer simp
  show "1 * a = a" by transfer simp
  show "inverse a * a = 1" by transfer simp
  show "a div b = a * inverse b" apply transfer
    using divide_rat_def by blast
qed
end

declare algebra_simps(1-6)[where 'a = ownership, simp]

instantiation ownership :: trivial_validity begin
definition [simp]: "\<V>_ownership (_::ownership) \<longleftrightarrow> True"
instance by standard simp
end


subsubsection \<open>Fractional SA\<close>

datatype 'a owned = Own ownership 'a (infix "\<Znrres>" 50) | OwnNone

instantiation owned :: (type) unital_add begin

definition "zero_owned = OwnNone"

primrec plus_owned :: "'a owned \<Rightarrow> 'a owned \<Rightarrow> 'a owned" where
    "plus_owned (n \<Znrres> x) my = (
        case my of (m \<Znrres> y) \<Rightarrow> (if x = y then n+m \<Znrres> x else undefined)
                 | _ \<Rightarrow> (n \<Znrres> x))"
  | "plus_owned OwnNone my = my"

case_of_simps xx: plus_owned.simps
thm xx
simps_of_case aa: xx
thm aa

lemma [simp]:
  "(n \<Znrres> x) + (m \<Znrres> y) = (if x = y then n+m \<Znrres> x else undefined)"
  "w + 0 = w" "0 + w = w" for w :: "'a owned"
  unfolding zero_owned_def
  by (simp, cases w, simp_all)

declare plus_owned.simps[simp del]

instance by standard simp_all
end

instantiation owned :: (validity) validity begin
primrec \<V>_owned where
  "\<V>_owned (n \<Znrres> x) \<longleftrightarrow> \<V> x" | "\<V>_owned OwnNone \<longleftrightarrow> True"

lemma [simp]: "\<V> (0::'a owned)"
  unfolding zero_owned_def by simp

instance by standard
end

instantiation owned :: (trivial_validity) trivial_validity begin
instance by (standard, case_tac x, simp_all)
end

instantiation owned :: (unital_ra) unital_ra begin
instance by standard simp
end








subsection \<open>Resource Space\<close>

text \<open>see theory "HOL-Statespace.StateSpaceEx"\<close>

locale project_inject_RA =
  project_inject project _ for project :: "('value::unital_ra) \<Rightarrow> ('a::unital_ra)" +
assumes inject_plus[simp]: "inject x + inject y = inject (x + y)"
  and validity_reduct[simp]: "\<V> (inject x) \<longleftrightarrow> \<V> x"
  and inject_zero[simp]: "inject 0 = 0"
begin
lemma project_zero[simp]: "project 0 = 0"
  by (metis project_inject_cancel inject_zero)
end

ML \<open>
val _ = StateSpace.define_statespace_command
  \<^command_keyword>\<open>resource_space\<close>
  "define a resource locale involving given resources, see ????"
  ("Resource_Algebra.unital_ra", \<^locale>\<open>project_inject_RA\<close>, "RES")

val _ = StateSpace.define_statespace_command
  \<^command_keyword>\<open>fiction_space\<close>
  "define a the fictional resources"
  ("Resource_Algebra.unital_ra", \<^locale>\<open>project_inject_RA\<close>, "FIC")

\<close>


lemma statespace_comm:
  assumes "name1 \<noteq> name2"
  shows "StateFun.update proj1 inj1 name1 f1 0 + StateFun.update proj2 inj2 name2 f2 0
       = StateFun.update proj2 inj2 name2 f2 0 + StateFun.update proj1 inj1 name1 f1 0"
  unfolding StateFun.update_def fun_upd_def unital_ra_fun_simps
  using assms by fastforce

lemma statespace_assoc:
  assumes "name2 \<noteq> name3"
  shows "s + (StateFun.update proj2 inj2 name2 f2 0 + StateFun.update proj3 inj3 name3 f3 0)
       = s + StateFun.update proj2 inj2 name2 f2 0 + StateFun.update proj3 inj3 name3 f3 0"
  unfolding StateFun.update_def fun_upd_def unital_ra_fun_simps
  using assms by fastforce



(*
example:
  resource_space res = n::nat n2::nat

see theory "HOL-Statespace.StateSpaceEx"!

print_locale res
print_locale res_valuetypes
*)

end