theory NoePreliminary
  imports Main HOL.Rat
(*  abbrevs
    "<own>" = "\<Znrres>" *)
begin


section \<open>Preliminary\<close>

paragraph \<open>Configurations\<close>

named_theorems \<phi>elim "\<nu>-type elimination rules"
named_theorems \<phi>def \<open>primitive definitions used to unfold in proofs of primitive instructions.\<close>
  (* and \<nu>address_def \<open>primitive definitions for unfolding in proofs for address\<close> *)
  and \<nu>post_construct and \<nu>auto_destruct
named_theorems typing_expn "expansion theorems for abstractions" and lrep_exps and \<phi>expns


paragraph \<open>Mathematical Helpers and Settings\<close>

notation rel_prod (infixr "\<times>\<^sub>r" 80)
notation pred_prod (infixr "\<times>\<^sub>p" 80)

lemma pair_exists: "Ex P \<longleftrightarrow> (\<exists>a b. P (a,b))" using split_paired_Ex .
lemma pair_forall: "All P \<longleftrightarrow> (\<forall>a b. P (a,b))" using split_paired_All .
lemmas pair_All = split_paired_all

lemma conj_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)" by rule simp+

definition \<open>pred_option1 P x \<longleftrightarrow> (case x of Some x' \<Rightarrow> P x' | None \<Rightarrow> False)\<close>
lemma pred_option1[simp]:
  \<open>pred_option1 P (Some x) \<longleftrightarrow> P x\<close>
  \<open>\<not>pred_option1 P None\<close>
  unfolding pred_option1_def by simp_all

definition \<open>S_Assert P = (if P then UNIV else {})\<close>

lemma In_S_Assert[simp]:
  \<open>x \<in> S_Assert P \<longleftrightarrow> P\<close>
  unfolding S_Assert_def by simp

lemma fold_tail:
  \<open>fold f (l @ [x]) = f x o fold f l\<close>
  by (induct l; simp)


locale homo_one =
  fixes \<phi> :: " 'a::one \<Rightarrow> 'b::one "
  assumes homo_one[simp]: "\<phi> 1 = 1"

locale homo_mult = homo_one \<phi>
  for \<phi> :: " 'a::{one,times} \<Rightarrow> 'b::{one,times} "
+ assumes homo_mult: "\<phi> (x * y) = \<phi> x * \<phi> y"


definition Inhabited :: " 'a set \<Rightarrow> bool" where  "Inhabited S = (\<exists>p. p \<in> S)"

class no_inverse = times + one +
  assumes no_inverse[simp]: \<open>a * b = 1 \<longleftrightarrow> a = 1 \<and> b = 1\<close>

class no_negative = plus + zero +
  assumes no_negative[simp]: \<open>a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0\<close>

class ab_group_mult = inverse + comm_monoid_mult +
  assumes ab_left_inverse: "inverse a * a = 1"
  assumes ab_diff_conv_add_uminus: "a / b = a * (inverse b)"


instantiation nat :: no_negative begin
instance by standard simp
end

instantiation nat :: no_inverse begin
instance by standard simp
end


subsection \<open>Positive Rational\<close>

typedef posrat = \<open>{ n::rat. 0 < n }\<close>
  morphisms rat_of_posrat posrat
  using zero_less_one by blast

setup_lifting type_definition_posrat

lemmas rat_of_posrat = rat_of_posrat[simplified]
lemmas posrat_inverse = posrat_inverse[simplified]

declare rat_of_posrat_inverse[simp]

class to_posrat =
  fixes to_posrat :: \<open>'a \<Rightarrow> posrat\<close>

instantiation posrat :: to_posrat begin
definition [simp]: \<open>to_posrat_posrat = (id :: posrat \<Rightarrow> posrat)\<close>
instance ..
end


instantiation posrat :: one begin
lift_definition one_posrat :: posrat is 1 by simp
instance ..
end

instantiation posrat :: linorder begin
lift_definition less_eq_posrat :: "posrat \<Rightarrow> posrat \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_posrat :: "posrat \<Rightarrow> posrat \<Rightarrow> bool" is "(<)" .
instance proof
  fix x y z :: posrat
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by transfer auto
  show "x \<le> x" by transfer simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by transfer simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by transfer simp
  show "x \<le> y \<or> y \<le> x" by transfer auto
qed
end

instantiation posrat :: comm_semiring begin

lift_definition plus_posrat :: "posrat \<Rightarrow> posrat \<Rightarrow> posrat" is "(+)" by simp
lift_definition times_posrat :: "posrat \<Rightarrow> posrat \<Rightarrow> posrat" is "(*)" by simp

instance proof
  fix a b c :: posrat
  show "a + b + c = a + (b + c)" by transfer simp
  show "a + b = b + a" by transfer simp
  show \<open>(a + b) * c = a * c + b * c\<close> by transfer (simp add: distrib_right)
  show \<open>a * b * c = a * (b * c)\<close> by transfer simp
  show \<open>a * b = b * a\<close> by transfer simp
qed
end

instantiation posrat :: strict_ordered_ab_semigroup_add begin

instance proof
  fix a b c d :: posrat
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b" by transfer simp
  show \<open>a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d\<close> by transfer simp
qed
end

instantiation posrat :: lattice begin
lift_definition inf_posrat :: "posrat \<Rightarrow> posrat \<Rightarrow> posrat" is "inf"
  by (simp add: inf_rat_def)
lift_definition sup_posrat :: "posrat \<Rightarrow> posrat \<Rightarrow> posrat" is "sup"
  using semilattice_sup_class.less_supI2 .
  
instance by (standard; transfer; simp)
end

lemma posrat_add_leD1[dest]: "a + b \<le> c \<Longrightarrow> a \<le> c"
  and posrat_add_leD2[dest]: "a + b \<le> c \<Longrightarrow> b \<le> c"
  for a :: posrat by (transfer, linarith)+

lemma posrat_add_ltD1[dest]: "a + b < c \<Longrightarrow> a < c"
  and posrat_add_ltD2[dest]: "a + b < c \<Longrightarrow> b < c"
  for a :: posrat by (transfer, linarith)+

instantiation posrat :: numeral begin
instance ..
end

instantiation posrat :: ab_group_mult begin

lift_definition inverse_posrat :: "posrat \<Rightarrow> posrat" is inverse by simp
lift_definition divide_posrat :: "posrat \<Rightarrow> posrat \<Rightarrow> posrat" is \<open>(div)\<close> by simp

instance proof
  fix a b :: posrat
  show "1 * a = a" by transfer simp
  show \<open>inverse a * a = 1\<close> by transfer simp
  show \<open>a div b = a * inverse b\<close> apply transfer
    using divide_inverse by blast
qed
end



subsection \<open>Non-negative Rational\<close>

typedef pos0rat = \<open>{ n::rat. 0 \<le> n }\<close>
  morphisms rat_of_pos0rat pos0rat
  using zero_less_one by blast

setup_lifting type_definition_pos0rat

lemmas rat_of_pos0rat = rat_of_pos0rat[simplified]
lemmas pos0rat_inverse = pos0rat_inverse[simplified]

declare rat_of_pos0rat_inverse[simp]

class to_pos0rat =
  fixes to_pos0rat :: \<open>'a \<Rightarrow> pos0rat\<close>

instantiation pos0rat :: to_pos0rat begin
definition [simp]: \<open>to_pos0rat_pos0rat = (id :: pos0rat \<Rightarrow> pos0rat)\<close>
instance ..
end

instantiation posrat :: to_pos0rat begin
definition \<open>to_pos0rat_posrat x = pos0rat (rat_of_posrat x)\<close>
instance ..
end

instantiation pos0rat :: to_posrat begin
definition \<open>to_posrat_pos0rat x = posrat (rat_of_pos0rat x)\<close>
instance ..
end

lemma to_posrat_to_pos0rat[simp]: \<open>to_posrat (to_pos0rat x) = x\<close> for x :: posrat
  unfolding to_posrat_pos0rat_def to_pos0rat_posrat_def
  by (metis NoePreliminary.pos0rat_inverse NoePreliminary.rat_of_posrat less_le_not_le rat_of_posrat_inverse)


instantiation pos0rat :: zero begin
lift_definition zero_pos0rat :: pos0rat is 0 by simp
instance ..
end

instantiation pos0rat :: one begin
lift_definition one_pos0rat :: pos0rat is 1 by simp
instance ..
end

instantiation pos0rat :: linorder begin
lift_definition less_eq_pos0rat :: "pos0rat \<Rightarrow> pos0rat \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_pos0rat :: "pos0rat \<Rightarrow> pos0rat \<Rightarrow> bool" is "(<)" .
instance proof
  fix x y z :: pos0rat
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by transfer auto
  show "x \<le> x" by transfer simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by transfer simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by transfer simp
  show "x \<le> y \<or> y \<le> x" by transfer auto
qed
end

instantiation pos0rat :: linordered_comm_semiring_strict begin

lift_definition plus_pos0rat :: "pos0rat \<Rightarrow> pos0rat \<Rightarrow> pos0rat" is "(+)" by simp
lift_definition minus_pos0rat :: \<open>pos0rat \<Rightarrow> pos0rat \<Rightarrow> pos0rat\<close>
  is \<open>\<lambda>x y. if y \<le> x then x - y else 0\<close> by simp
lift_definition times_pos0rat :: "pos0rat \<Rightarrow> pos0rat \<Rightarrow> pos0rat" is "(*)" by simp

lemma pos0rat_LE0[simp]: \<open>0 \<le> x\<close> for x :: pos0rat by transfer simp

instance proof
  fix a b c d :: pos0rat
  show "a + b + c = a + (b + c)" by transfer simp
  show "a + b = b + a" by transfer simp
  show "0 + a = a" by transfer simp
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b" by transfer simp
  show \<open>a + b - a = b\<close> by transfer simp
  show \<open>a - b - c = a - (b + c)\<close> by transfer simp
  show \<open>(a + b) * c = a * c + b * c\<close> by transfer (simp add: distrib_right)
  show \<open>a * b * c = a * (b * c)\<close> by transfer simp
  show \<open>a * b = b * a\<close> by transfer simp
  show \<open>0 * a = 0\<close> by transfer simp
  show \<open>a * 0 = 0\<close> by transfer simp
  show \<open>a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b\<close> by transfer simp
qed
end

instantiation pos0rat :: lattice begin
lift_definition inf_pos0rat :: "pos0rat \<Rightarrow> pos0rat \<Rightarrow> pos0rat" is "inf"
  by (simp add: inf_rat_def)
lift_definition sup_pos0rat :: "pos0rat \<Rightarrow> pos0rat \<Rightarrow> pos0rat" is "sup"
  using semilattice_sup_class.le_supI1 .
  
instance by (standard; transfer; simp)
end

lemma pos0rat_add_leD1[dest]: "a + b \<le> c \<Longrightarrow> a \<le> c"
  and pos0rat_add_leD2[dest]: "a + b \<le> c \<Longrightarrow> b \<le> c"
  for a :: pos0rat by (transfer, linarith)+

lemma pos0rat_add_ltD1[dest]: "a + b < c \<Longrightarrow> a < c"
  and pos0rat_add_ltD2[dest]: "a + b < c \<Longrightarrow> b < c"
  for a :: pos0rat by (transfer, linarith)+

instantiation pos0rat :: numeral begin
instance ..
end

instantiation pos0rat :: comm_monoid_mult begin
lift_definition inverse_pos0rat :: "pos0rat \<Rightarrow> pos0rat" is inverse by simp

instance proof
  fix a b c :: pos0rat
  show "1 * a = a" by transfer simp
qed
end


instantiation pos0rat :: linordered_semidom begin
instance proof
  fix a b c :: pos0rat
  show \<open>(0::pos0rat) \<noteq> 1\<close> by transfer simp
  show \<open>a * (b - c) = a * b - a * c\<close> apply transfer
    using nle_le right_diff_distrib' by fastforce
  show \<open>a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a * b \<noteq> 0\<close> by transfer simp
  show \<open>(0::pos0rat) < 1\<close> by transfer simp
  show \<open> b \<le> a \<Longrightarrow> a - b + b = a\<close> by transfer simp
qed
end

instantiation pos0rat :: algebraic_semidom begin
lift_definition divide_pos0rat :: "pos0rat \<Rightarrow> pos0rat \<Rightarrow> pos0rat" is "(/)" by simp
instance proof
  fix a b c :: pos0rat
  show \<open>b \<noteq> 0 \<Longrightarrow> a * b div b = a\<close> apply transfer by simp
  show \<open>a div 0 = 0\<close> apply transfer by simp
qed
end

instantiation pos0rat :: no_negative begin
instance by (standard, transfer) (simp add: add_nonneg_eq_0_iff)
end

lemma to_posrat_1_pos0rat[simp]:
  \<open>to_posrat (1::pos0rat) = 1\<close>
  unfolding to_posrat_pos0rat_def
  by (simp add: one_pos0rat.rep_eq one_posrat_def) 

lemma to_posrat_mult_homo_pos0rat:
  \<open>x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> to_posrat (x * y) = to_posrat x * to_posrat y\<close>
  for x :: pos0rat
  unfolding to_posrat_pos0rat_def
  by transfer (simp add: posrat_inverse times_posrat_def)

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
instance ..
end

instantiation prod :: (plus,plus) plus begin
fun plus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
  where "plus_prod (x,y) (x',y') = (x+x', y+y')"
instance ..
end

 declare sep_disj_commuteI[simp] sep_add_commute[simp] sep_add_assoc[simp]

instantiation prod :: (partial_ab_semigroup, partial_ab_semigroup) partial_ab_semigroup begin
fun sep_disj_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  where "sep_disj_prod (x,y) (x',y') \<longleftrightarrow> (x ## x') \<and> (y ## y')"
instance .. (auto simp add: pair_All)
end

instantiation prod :: (cancl_partial_ab_semigroup, cancl_partial_ab_semigroup) cancl_partial_ab_semigroup begin
instance apply (standard, simp_all add: pair_All)
  apply (metis sep_disj_addD1)
  by (metis sep_disj_addI1)
end

instantiation prod :: (pre_sep_algebra, pre_sep_algebra) pre_sep_algebra begin
instance .. (auto simp add: pair_All)
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


declare algebra_simps(1-6)[where 'a = ownership, simp]

instantiation ownership :: partial_ab_semigroup begin
definition sep_disj_ownership :: "ownership \<Rightarrow> ownership \<Rightarrow> bool"
  where [simp]: "sep_disj_ownership _ _ = True"
instance .. simp_all
end

instantiation ownership :: cancl_partial_ab_semigroup begin
instance .. simp_all
end

section \<open>Fractional SA\<close>

type_synonym 'a owned = "(ownership \<times> 'a) option"


(* 
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
instance .. simp_all
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
instance .. simp_all
end

*)



(*subsubsection \<open>Fractional Ownership\<close>


 *)

end