theory NoeMisc
  imports Main
    HOL.Rat
(*  abbrevs
    "<own>" = "\<Znrres>" *)
begin

text \<open>Supplementary mathematical notions for the \<nu>-system\<close>


notation rel_prod (infixr "\<times>\<^sub>r" 80)
notation pred_prod (infixr "\<times>\<^sub>p" 80)

lemma pair_exists: "Ex P \<longleftrightarrow> (\<exists>a b. P (a,b))" using split_paired_Ex .
lemma pair_forall: "All P \<longleftrightarrow> (\<forall>a b. P (a,b))" using split_paired_All .
lemmas pair_All = split_paired_all


lemma conj_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)" by rule simp+


datatype ('value,'type) dynamic (infix ":::" 3)
  = dynamic (val_of: 'value) (typ_of: 'type) (infix ":::" 3)


(*

locale monomorphism =
  fixes \<phi> :: "'a \<Rightarrow> 'b" and \<phi>' :: "'b \<Rightarrow> 'a"
  assumes inj[simp]: "\<phi>' (\<phi> x) = x"
begin
lemma inj_alt: "\<phi> x = \<phi> y \<Longrightarrow> x = y"
  using inj by metis 
end 


 section \<open>Instantiations of SA\<close>

instantiation prod :: (zero,zero) zero begin
definition zero_prod :: "'a \<times> 'b"
  where [simp]: "zero_prod = (0,0)"
instance by standard
end

instantiation prod :: (plus,plus) plus begin
fun plus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
  where "plus_prod (x,y) (x',y') = (x+x', y+y')"
instance by standard
end

 declare sep_disj_commuteI[simp] sep_add_commute[simp] sep_add_assoc[simp]

instantiation prod :: (partial_ab_semigroup, partial_ab_semigroup) partial_ab_semigroup begin
fun sep_disj_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  where "sep_disj_prod (x,y) (x',y') \<longleftrightarrow> (x ## x') \<and> (y ## y')"
instance by standard (auto simp add: pair_All)
end

instantiation prod :: (cancl_partial_ab_semigroup, cancl_partial_ab_semigroup) cancl_partial_ab_semigroup begin
instance apply (standard, simp_all add: pair_All)
  apply (metis sep_disj_addD1)
  by (metis sep_disj_addI1)
end

instantiation prod :: (pre_sep_algebra, pre_sep_algebra) pre_sep_algebra begin
instance by standard (auto simp add: pair_All)
end

instantiation prod :: (sep_algebra, sep_algebra) sep_algebra begin
instance by (standard, simp_all add: pair_All)
    (metis sep_disj_addD sep_disj_addI1)+
end


section \<open>Homomorphism\<close>


locale plus_hom =
  fixes \<phi> :: "'a :: plus \<Rightarrow> 'b :: plus"
  assumes hom_add: "\<phi> (x + y) = \<phi> x + \<phi> y"

locale zero_hom =
  fixes \<phi> :: "'a :: zero \<Rightarrow> 'b :: zero"
  assumes hom_zero[simp]: "\<phi> 0 = 0"

locale pre_sep_algebra_hom =
  fixes \<phi> :: "'a :: pre_sep_algebra \<Rightarrow> 'b :: pre_sep_algebra"
  assumes hom_pre_sep_algebra: "x ## y \<longleftrightarrow> \<phi> x ## \<phi> y"

locale SA_hom =
  plus_hom \<phi> + zero_hom \<phi> + pre_sep_algebra_hom \<phi>
  for \<phi> :: "'a :: pre_sep_algebra \<Rightarrow> 'b :: pre_sep_algebra"

locale SA_inj =
  SA_hom \<phi> + monomorphism \<phi> \<phi>'
  for \<phi> :: "'a :: pre_sep_algebra \<Rightarrow> 'b :: pre_sep_algebra"
  and \<phi>' :: "'b \<Rightarrow> 'a"

section \<open>Option SA\<close>

instantiation option :: (type) zero begin
definition zero_option :: "'a option" where [simp]: "zero_option = None"
instance ..
end

instantiation option :: (plus) plus begin
fun plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
    "plus_option (Some x) (Some y) = (Some (x + y))"
  | "plus_option None y = y"
  | "plus_option x None = x"
instance ..
end

instantiation option :: (partial_ab_semigroup) pre_sep_algebra begin

fun sep_disj_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
    "sep_disj_option (Some x) (Some y) \<longleftrightarrow> x ## y"
  | "sep_disj_option _ _ \<longleftrightarrow> True"

instance proof
  fix x y z :: "'a option"
  show "x ## 0" by simp
  show "x ## y \<Longrightarrow> y ## x" by (cases x; cases y; simp)
  show "x + 0 = x" by (cases x) simp_all
  show "x ## y \<Longrightarrow> x + y = y + x" by (cases x; cases y) simp_all
  show "x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x + y + z = x + (y + z)"
    by (cases x; cases y; cases z) simp_all
qed
end

instantiation option :: (cancl_partial_ab_semigroup) sep_algebra begin
instance proof
  fix x y z :: "'a option"
  show "x ## y + z \<Longrightarrow> y ## z \<Longrightarrow> x ## y"
    apply (cases x; cases y; cases z) apply simp_all
    using sep_disj_addD1 by blast
  show "x ## y + z \<Longrightarrow> y ## z \<Longrightarrow> x + y ## z"
    apply (cases x; cases y; cases z) apply simp_all
    using sep_disj_addI1 by blast
qed
end

section \<open>Fractional Ownership\<close>

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
*)
declare algebra_simps(1-6)[where 'a = ownership, simp]

instantiation ownership :: partial_ab_semigroup begin
definition sep_disj_ownership :: "ownership \<Rightarrow> ownership \<Rightarrow> bool"
  where [simp]: "sep_disj_ownership _ _ = True"
instance by standard simp_all
end

instantiation ownership :: cancl_partial_ab_semigroup begin
instance by standard simp_all
end

section \<open>Fractional SA\<close>

type_synonym 'a owned = "(ownership \<times> 'a) option"


(* section \<open>Fractional SA\<close>

datatype 'a owned = Own ownership 'a (infix "\<Znrres>" 50) | OwnNone

instantiation owned :: (type) sep_algebra begin

definition zero_owned :: "'a owned"
  where [simp]: "zero_owned = OwnNone"

fun plus_owned :: "'a owned \<Rightarrow> 'a owned \<Rightarrow> 'a owned" where
    "plus_owned (n \<Znrres> x) (m \<Znrres> y) = (if x = y then n+m \<Znrres> x else undefined)"
  | "plus_owned mx OwnNone = mx"
  | "plus_owned OwnNone my = my"

fun sep_disj_owned :: "'a owned \<Rightarrow> 'a owned \<Rightarrow> bool" where
    "sep_disj_owned (n \<Znrres> x) (m \<Znrres> y) \<longleftrightarrow> n + m \<le> 1 \<and> x = y"
  | "sep_disj_owned mx OwnNone = True"
  | "sep_disj_owned OwnNone my = True"

instance proof
  fix x y z :: "'a owned"
  show "x ## 0" by (cases x) simp_all
  show "x ## y \<Longrightarrow> y ## x" by (cases x; cases y) simp_all
  show "x + 0 = x" by (cases x) simp_all
  show "x ## y \<Longrightarrow> x + y = y + x" by (cases x; cases y) simp_all
  show "x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x + y + z = x + (y + z)"
    by (cases x; cases y; cases z) simp_all
  show "x ## y + z \<Longrightarrow> y ## z \<Longrightarrow> x ## y"
    apply (cases x; cases y; cases z) apply simp_all
    by (metis add.assoc ownership_add_leD1)
  show "x ## y + z \<Longrightarrow> y ## z \<Longrightarrow> x + y ## z"
    by (cases x; cases y; cases z) simp_all
qed

end
*)
section \<open>Partial Map\<close>

instantiation "fun" :: (type, sep_algebra) sep_algebra
begin

definition
  zero_fun_def[simp]: "zero_fun x = 0"

definition
  plus_fun_def[simp]: "(m1 + m2) x = m1 x + m2 x"

definition
  sep_disj_fun_def: "sep_disj m1 m2 = (\<forall>x. m1 x ## m2 x)"

instance proof
  fix x y z :: "'a \<Rightarrow> 'b"
  show "x ## 0" unfolding sep_disj_fun_def by simp
  show "x ## y \<Longrightarrow> y ## x" unfolding sep_disj_fun_def by simp
  show "x + 0 = x" by (rule ext) simp
  show "x ## y \<Longrightarrow> x + y = y + x" unfolding sep_disj_fun_def fun_eq_iff by simp
  show "x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x + y + z = x + (y + z)"
    unfolding sep_disj_fun_def fun_eq_iff by simp
  show "x ## y + z \<Longrightarrow> y ## z \<Longrightarrow> x ## y"
    unfolding sep_disj_fun_def fun_eq_iff
    by (metis plus_fun_def sep_disj_addD1)
  show "x ## y + z \<Longrightarrow> y ## z \<Longrightarrow> x + y ## z"
    unfolding sep_disj_fun_def fun_eq_iff
    by (metis plus_fun_def sep_disj_addI1)
qed
end



instantiation unit :: sep_algebra begin
definition sep_disj_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where [simp]: "sep_disj_unit _ _ = True"
definition plus_unit :: "unit \<Rightarrow> unit \<Rightarrow> unit" where [simp]: "plus_unit _ _ = ()"
definition zero_unit :: unit where [simp]: "zero_unit = ()"
instance by standard simp_all
end

section \<open>Exclusive PCS\<close>

typedef 'a ex = \<open>UNIV :: 'a set\<close> morphisms Abs_ex ex .. 

setup_lifting type_definition_ex
lift_bnf 'a ex by blast +
free_constructors case_ex for ex
  by (metis UNIV_I ex_inverse ex_cases)+

instantiation ex :: (type) cancl_partial_ab_semigroup begin
definition sep_disj_ex :: "'a ex \<Rightarrow> 'a ex \<Rightarrow> bool" where [simp]: "sep_disj_ex = (=)"
definition plus_ex :: "'a ex \<Rightarrow> 'a ex \<Rightarrow> 'a ex" where [simp]: "plus_ex a b = a"
instance by standard simp_all
end

*)

end