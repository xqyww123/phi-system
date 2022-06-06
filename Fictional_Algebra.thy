theory Fictional_Algebra
  imports Main HOL.Rat "Statespace/StateFun"
    NoePreliminary
  keywords "fiction_space" :: thy_decl
    and "resource_space" :: thy_defn
  abbrevs "!!" = "!!"
begin

section \<open>Algebras\<close>


subsection \<open>Algebra Structures\<close>

class ab_group_mult = inverse + comm_monoid_mult +
  assumes ab_left_inverse: "inverse a * a = 1"
  assumes ab_diff_conv_add_uminus: "a / b = a * (inverse b)"


class sep_disj = times +
  fixes sep_disj :: "'a => 'a => bool" (infix "##" 60)

class sep_ab_semigroup = sep_disj +
  assumes sep_disj_commuteI: "x ## y \<Longrightarrow> y ## x"
  assumes sep_mult_commute[simp]: "x ## y \<Longrightarrow> x * y = y * x"
  assumes sep_mult_assoc:
    "\<lbrakk> x ## y; y ## z; x ## z \<rbrakk> \<Longrightarrow> (x * y) * z = x * (y * z)"
begin
lemma sep_disj_commute[simp]: "x ## y \<longleftrightarrow> y ## x"
  by (blast intro: sep_disj_commuteI)
end

class cancl_sep_ab_semigroup = sep_ab_semigroup +
  assumes sep_disj_multD1: "\<lbrakk> x ## y * z; y ## z \<rbrakk> \<Longrightarrow> x ## y"
  assumes sep_disj_multI1: "\<lbrakk> x ## y * z; y ## z \<rbrakk> \<Longrightarrow> x * y ##  z"


class pre_sep_algebra = one + sep_ab_semigroup +
  assumes sep_disj_one [simp]: "x ## 1"
  assumes sep_mult_one [simp]: "x * 1 = x"
begin

lemma disjoint_zero_sym [simp]: "1 ## x"
  using local.sep_disj_one sep_disj_commute by blast
  

lemma sep_add_zero_sym [simp]: "1 * x = x"
  by (metis local.sep_disj_one local.sep_mult_commute local.sep_mult_one)
  

lemma sep_mult_left_commute[simp]:
  assumes a: "a ## b" "b ## c" "a ## c"
  shows "b * (a * c) = a * (b * c)" (is "?lhs = ?rhs")
proof -
  have "?lhs = b * a * c" using a
    by (simp add: sep_mult_assoc[symmetric] sep_disj_commute)
  also have "... = a * b * c" using a
    by (simp add: sep_mult_commute sep_disj_commute)
  also have "... = ?rhs" using a
    by (simp add: sep_mult_assoc sep_disj_commute)
  finally show ?thesis .
qed

lemmas sep_mult_ac = sep_mult_assoc sep_mult_commute sep_mult_left_commute
                    sep_disj_commute (* nearly always necessary *)
end

declare sep_mult_assoc[simp]

class sep_algebra = pre_sep_algebra + cancl_sep_ab_semigroup

class discrete_sep_semigroup = sep_disj +
  assumes discrete_sep_disj[simp]: "x ## y \<longleftrightarrow> x = y"
    and discrete_mult[simp]: "x * y = (if x = y then x else undefined)"
begin
subclass sep_ab_semigroup
  apply standard unfolding discrete_sep_disj discrete_mult by simp_all
subclass cancl_sep_ab_semigroup
  apply standard unfolding discrete_sep_disj discrete_mult by simp_all
end

class nonsepable_semigroup = sep_disj +
  assumes nonsepable_disj[simp]: "\<not> x ## y"
begin
subclass sep_ab_semigroup by standard simp_all
subclass cancl_sep_ab_semigroup by standard simp_all
end

(* class unital_mult = plus + one +
  assumes unital_add_left[simp]: "1 * x = x"
    and unital_add_right[simp]: "x * 1 = x"

subclass (in monoid_mult) unital_mult .. simp_all *)


subsection \<open>Instances of Algebras\<close>

subsubsection \<open>Option\<close>

instantiation option :: (times) times begin
definition "times_option x' y' =
  (case x' of Some x \<Rightarrow> (case y' of Some y \<Rightarrow> Some (x * y) | _ \<Rightarrow> x')
      | None \<Rightarrow> y')"
lemma times_option[simp]:
  "Some x * Some y = Some (x * y)"
  "x' * None = x'"
  "None * x' = x'"
  by (cases x', simp_all add: times_option_def)+
instance ..
end

instantiation option :: (type) one begin
definition [simp]: "one_option = None"
instance ..
end

instantiation option :: (sep_ab_semigroup) sep_ab_semigroup begin
definition "sep_disj_option x' y' =
  (case x' of Some x \<Rightarrow> (case y' of Some y \<Rightarrow> x ## y | _ \<Rightarrow> True) | _ \<Rightarrow> True)"
lemma sep_disj_option[simp]:
    "Some x ## Some y \<longleftrightarrow> x ## y"
    "None ## z" "z ## None"
  unfolding sep_disj_option_def by (cases z, simp_all)+
instance by (standard; case_tac x; simp_all; case_tac y; simp_all; case_tac z; simp_all)
end

instantiation option :: (sep_ab_semigroup) pre_sep_algebra begin
instance by (standard; case_tac x; simp_all; case_tac y; simp_all; case_tac z; simp_all)
end

instantiation option :: (cancl_sep_ab_semigroup) cancl_sep_ab_semigroup begin
instance apply (standard; case_tac x; simp_all; case_tac y; simp_all; case_tac z; simp_all)
  using sep_disj_multD1 apply blast
  using sep_disj_commuteI sep_disj_multI1 by blast
end

instantiation option :: (cancl_sep_ab_semigroup) sep_algebra begin
instance by (standard; case_tac x; simp_all; case_tac y; simp_all; case_tac z; simp_all)
end



subsubsection \<open>Product\<close>

instantiation prod :: (times, times) times begin
definition "times_prod = (\<lambda>(x1,x2) (y1,y2). (x1 * y1, x2 * y2))"
lemma times_prod[simp]: "(x1,x2) * (y1,y2) = (x1 * y1, x2 * y2)"
  unfolding times_prod_def by simp
instance ..
end

instantiation prod :: (zero, zero) zero begin
definition "zero_prod = (0,0)"
instance ..
end

instantiation prod :: (one, one) one begin
definition "one_prod = (1,1)"
instance ..
end

instantiation prod :: (semigroup_mult, semigroup_mult) semigroup_mult begin
instance by standard (simp_all add: pair_All algebra_simps)
end

instantiation prod :: (monoid_mult, monoid_mult) monoid_mult begin
instance by standard (simp_all add: one_prod_def pair_All algebra_simps)
end

instantiation prod :: (ab_semigroup_mult, ab_semigroup_mult) ab_semigroup_mult begin
instance apply standard
  by (metis mult.commute prod.collapse times_prod) 
end

instantiation prod :: (comm_monoid_mult, comm_monoid_mult) comm_monoid_mult begin
instance apply standard by simp 
end


subsubsection \<open>List\<close>

instantiation list :: (type) times begin
definition [simp]: "times_list = (@)"
instance ..
end

instantiation list :: (type) zero begin
definition [simp]: "zero_list = []"
instance ..
end

instantiation list :: (type) one begin
definition [simp]: "one_list = []"
instance ..
end

instantiation list :: (type) semigroup_mult begin
instance by standard simp_all
end

instantiation list :: (type) monoid_mult begin
instance by standard simp_all
end


subsubsection \<open>Function\<close>

instantiation "fun" :: (type,times) times begin
definition "times_fun f g = (\<lambda>x. f x * g x)"
instance ..
end

lemma times_fun: "(f * g) x = f x * g x"
  unfolding times_fun_def by simp

instantiation "fun" :: (type,one) one begin
definition "one_fun = (\<lambda>(x::'a). (1::'b))"
instance ..
end

lemma one_fun[simp]: "1 x = 1" unfolding one_fun_def by simp

instantiation "fun" :: (type, semigroup_mult) semigroup_mult begin
instance apply standard
  by (simp add: mult.assoc times_fun_def) 
end

instantiation "fun" :: (type,sep_ab_semigroup) sep_ab_semigroup begin
definition "sep_disj_fun m1 m2 = (\<forall>x. m1 x ## m2 x)"
instance by standard (simp_all add: sep_disj_fun_def times_fun_def fun_eq_iff)
end

instantiation "fun" :: (type,sep_algebra) sep_algebra begin
instance apply standard
  apply (simp_all add: sep_disj_fun_def times_fun_def fun_eq_iff)
  using sep_disj_multD1 apply blast
  using sep_disj_multI1 sep_disj_commute by blast
end

instantiation "fun" :: (type,comm_monoid_mult) comm_monoid_mult begin
instance by standard (simp_all add: mult.commute times_fun_def fun_eq_iff)

lemmas fun_mult_norm = mult.assoc[where ?'a = "'a \<Rightarrow> 'b", symmetric]

lemma [simp]: "(f * 1(k := x)) k = f k * x" for f :: "'a \<Rightarrow> 'b"
  by (simp add: times_fun_def)

lemma [simp]: "k' \<noteq> k \<Longrightarrow> (f * 1(k':=x)) k = f k" for f :: "'a \<Rightarrow> 'b"
  by (simp add: times_fun_def)

lemma [simp]: "(f * 1(k := x))(k:=1) = f(k:=1)" for f :: "'a \<Rightarrow> 'b"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma [simp]: "k' \<noteq> k \<Longrightarrow> (f * 1(k' := x))(k:=1) = f(k:=1) * 1(k' := x)" for f :: "'a \<Rightarrow> 'b"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma fun_split_1: "f = f(k:=1) * 1(k:= f k)" for f :: "'a \<Rightarrow> 'b"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

end

lemma fun_1upd1[simp]:
  "1(k := 1) = 1"
  unfolding one_fun_def fun_upd_def by simp

lemma fun_1upd_homo[simp]:
    "1(k := x) * 1(k := y) = 1(k := x * y)" for x :: "'a::comm_monoid_mult"
  unfolding one_fun_def fun_upd_def times_fun_def
  by fastforce

lemma [simp]: "NO_MATCH (a::'a) (1::'a::one) \<Longrightarrow> i \<noteq> k \<Longrightarrow> f(i := a, k := 1) = f(k := 1, i := a)"
  using fun_upd_twist .




definition "dom1 f = {x. f x \<noteq> 1}"

lemma dom1_1[simp]: "dom1 1 = {}"
  unfolding dom1_def by simp

lemma dom1_upd[simp]: "dom1 (f(x:=y)) = (if y = 1 then dom1 f - {x} else insert x (dom1 f))"
  unfolding dom1_def by auto


lemma "dom1 f = dom f"
  by (metis dom1_def dom_def one_option_def)

lemma one_updt_one[simp]: "1(a:=1) = 1" unfolding one_fun_def fun_upd_def by simp

lemma [simp]: "x \<noteq> 1 \<Longrightarrow> f(k:=x) \<noteq> 1"
  unfolding one_fun_def fun_upd_def fun_eq_iff by simp blast

lemma [simp]: "1 o f = 1"
  unfolding one_fun_def fun_eq_iff by simp

lemma finite_dom1_mult1[simp]:
  "finite (dom1 (f * 1(k:=v))) \<longleftrightarrow> finite (dom1 f)"
  for f :: "'a \<Rightarrow> 'b :: comm_monoid_mult"
proof -
  have "dom1 (f * 1(k:=v)) = dom1 f \<or> dom1 (f * 1(k:=v)) = insert k (dom1 f)
    \<or> dom1 (f * 1(k:=v)) = dom1 f - {k}"
  for f :: "'a \<Rightarrow> 'b :: comm_monoid_mult"
  unfolding dom1_def times_fun_def fun_upd_def set_eq_iff by simp
  then show ?thesis
    by (metis finite_Diff finite_insert infinite_remove)
qed



subsubsection \<open>Unit\<close>

instantiation unit :: times begin
definition [simp]: "times_unit (f::unit) (g::unit) = ()"
instance ..
end

instantiation unit :: one begin
definition [simp]: "one_unit = ()"
instance ..
end

instantiation unit :: monoid_mult begin
instance by standard simp_all
end



subsubsection \<open>Set\<close>

instantiation set :: (type) zero begin
definition "zero_set = {}"
instance ..
end

instantiation set :: (one) one begin
definition "one_set = {1::'a}"
instance ..
end

lemma set_in_1[simp]: "x \<in> 1 \<longleftrightarrow> x = 1"
  unfolding one_set_def by simp

instantiation set :: (times) times begin
definition "times_set P Q = { x * y | x y. x \<in> P \<and> y \<in> Q }"
instance ..
end

lemma set_mult_zero[simp]: "{} * S = {}" "S * {} = {}"
  unfolding times_set_def by simp_all

lemma set_mult_expn[\<phi>expns]:
  \<open>uv \<in> (S * T) \<longleftrightarrow> (\<exists>u v. uv = u * v \<and> u \<in> S \<and> v \<in> T)\<close>
  unfolding times_set_def by simp

lemma set_mult_inhabited[\<phi>elim,elim!]:
  \<open>Inhabited (S * T) \<Longrightarrow> (Inhabited S \<Longrightarrow> Inhabited T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def times_set_def by simp

instantiation set :: (times) mult_zero begin
instance by standard (simp_all add: zero_set_def)
end

instantiation set :: (semigroup_mult) semigroup_mult begin
instance apply standard
  apply (auto simp add: times_set_def algebra_simps)
  apply blast
  by (metis mult.assoc) 
end

instantiation set :: (monoid_mult) monoid_mult begin
instance by standard (simp_all add: one_set_def times_set_def)
end

instantiation set :: (comm_monoid_mult) comm_monoid_mult begin
instance apply standard
  apply (simp_all add: one_set_def times_set_def)
  using mult.commute by blast
end


subsubsection \<open>Partial Map\<close>

lemma "f ## g \<longleftrightarrow> dom f \<inter> dom g = {}" for f :: "'a \<rightharpoonup> ('b :: nonsepable_semigroup)"
  unfolding sep_disj_fun_def sep_disj_option_def disjoint_iff
  by (metis (no_types, lifting) domIff nonsepable_disj option.case_eq_if)



subsubsection \<open>Partiality\<close>


datatype 'a fine ("_ ?" [100] 101) = Fine (the_fine: 'a) | Undef
notation the_fine ("!!_" [1000] 1000)

hide_const pred_fine
definition "pred_fine P x = (case x of Fine x' \<Rightarrow> P x' | _ \<Rightarrow> False)"
lemma pred_fine[simp]:
  "pred_fine P (Fine x') \<longleftrightarrow> P x'"  "\<not> pred_fine P Undef"
  unfolding pred_fine_def by simp_all


instantiation fine :: (type) zero begin
definition [simp]: "zero_fine = Undef"
instance ..
end

instantiation fine :: (one) one begin
definition "one_fine = Fine 1"
instance ..
end

instantiation fine :: (sep_disj) times begin

definition "times_fine x y =
  (case x of Fine a \<Rightarrow> (case y of Fine b \<Rightarrow> if a ## b then Fine (a*b) else Undef
    | _ \<Rightarrow> Undef) | _ \<Rightarrow> Undef)"

lemma times_fine[simp]:
  "Fine a * Fine b = (if a ## b then Fine (a*b) else Undef)"
  "Undef * a' = Undef" "a' * Undef = Undef"
  unfolding times_fine_def by (cases a'; simp_all)+

instance ..
end

instantiation fine :: (sep_disj) mult_zero begin
instance by standard simp_all
end

instantiation fine :: (cancl_sep_ab_semigroup) ab_semigroup_mult begin
instance apply (standard; case_tac a; simp; case_tac b; simp; case_tac c; simp)
  by (metis sep_disj_commuteI sep_disj_multD1 sep_disj_multI1 sep_mult_assoc sep_mult_commute)
end

instantiation fine :: (sep_algebra) comm_monoid_mult begin
instance by standard (case_tac a; simp add: one_fine_def)
end




subsubsection \<open>Fractional SA\<close>

datatype 'a share = Share rat 'a (infix "\<Znrres>" 50)

instantiation share :: (type) cancl_sep_ab_semigroup begin

definition times_share :: "'a share \<Rightarrow> 'a share \<Rightarrow> 'a share" where
  "times_share x' y' = (case x' of n \<Znrres> x \<Rightarrow> (case y' of m \<Znrres> y \<Rightarrow>
    if x = y then n+m \<Znrres> x else undefined))"

lemma times_share[simp]:
  "(n \<Znrres> x) * (m \<Znrres> y) = (if x = y then n+m \<Znrres> x else undefined)"
  unfolding times_share_def by simp_all

definition sep_disj_share :: "'a share \<Rightarrow> 'a share \<Rightarrow> bool" where
  "sep_disj_share x' y' \<longleftrightarrow> (case x' of n \<Znrres> x \<Rightarrow>
    (case y' of m \<Znrres> y \<Rightarrow> 0 < n \<and> 0 < m \<and> n + m \<le> 1 \<and> x = y))"

lemma sep_disj_share[simp]:
  "(n \<Znrres> x) ## (m \<Znrres> y) \<longleftrightarrow> 0 < n \<and> 0 < m \<and> n + m \<le> 1 \<and> x = y"
  unfolding sep_disj_share_def by simp_all

instance proof
  fix x y z :: "'a share"
  show "x ## y \<Longrightarrow> y ## x" by (cases x; cases y) simp_all
  show "x ## y \<Longrightarrow> x * y = y * x" by (cases x; cases y) simp_all
  show "x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x * y * z = x * (y * z)"
    by (cases x; cases y; cases z) simp_all
  show "x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y"
    by (cases x; cases y; cases z) simp_all
  show "x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z"
    by (cases x; cases y; cases z) simp_all
qed
end



subsection \<open>Fictional Algebra\<close>

subsubsection \<open>Algebra Structure\<close>

definition Fictional :: "('a::one \<Rightarrow> 'b::one set) \<Rightarrow> bool"
  where "Fictional \<I> \<longleftrightarrow> \<I> 1 = 1"

typedef (overloaded) ('a::one,'b::one) fiction
    = \<open>Collect (Fictional :: ('a \<Rightarrow> 'b set) \<Rightarrow> bool)\<close>
  morphisms \<I> Fiction
  by (rule exI[where x = \<open>\<lambda>_. 1\<close>]) (simp add: Fictional_def)

lemmas Fiction_inverse[simp] = Fiction_inverse[simplified]

lemma Fiction_one[simp]: "\<I> I 1 = 1"
  using Fictional_def \<I> by blast



subsubsection \<open>Instance\<close>

locale fiction
begin

paragraph \<open>Function\<close>

definition "fun' I = Fiction (\<lambda>f. prod (\<lambda>x. \<I> (I x) (f x)) (dom1 f))"
lemma fun'_\<I>[simp]: "\<I> (fun' I) = (\<lambda>f. prod (\<lambda>x. \<I> (I x) (f x)) (dom1 f))"
  unfolding fun'_def by (rule Fiction_inverse) (simp add: Fictional_def)

lemma fun'_split:
  "finite (dom1 f) \<Longrightarrow> \<I> (fiction.fun' I) f = \<I> (fiction.fun' I) (f(k:=1)) * \<I> (I k) (f k)"
  for f :: "'a \<Rightarrow> 'b::comm_monoid_mult"
  by simp (smt (verit, best) Fiction_one dom1_upd fun_upd_triv mult.comm_neutral mult.commute prod.insert_remove)

definition "fun I = fun' (\<lambda>_. I)"
lemma fun_\<I>[simp]: "\<I> (fun I) = (\<lambda>f. prod (\<I> I o f) (dom1 f))"
  unfolding fun_def by simp

lemma fun_split:
  "finite (dom1 f) \<Longrightarrow> \<I> (fiction.fun I) f = \<I> (fiction.fun I) (f(k:=1)) * \<I> I (f k)"
  for f :: "'a \<Rightarrow> 'b::comm_monoid_mult"
  unfolding fun_def using fun'_split .

definition "pointwise I = Fiction (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"
lemma pointwise_\<I>[simp]:
  "\<I> (pointwise I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"
  unfolding pointwise_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_fun_def fun_eq_iff)


paragraph \<open>Pair\<close>

definition "pair I1 I2 = Fiction (\<lambda>(x,y). \<I> I1 x * \<I> I2 y) "
lemma pair_\<I>[simp]: "\<I> (pair I1 I2) = (\<lambda>(x,y). \<I> I1 x * \<I> I2 y)"
  for I1 :: "('a::one,'b::monoid_mult) fiction"
  unfolding pair_def by (rule Fiction_inverse) (simp add: Fictional_def one_prod_def)
notation pair (infixl "\<bullet>" 50)


paragraph \<open>Option\<close>

definition "option I = Fiction (case_option 1 I)"
lemma option_\<I>[simp]: "\<I> (option I) = (case_option 1 I)"
  unfolding option_def by (rule Fiction_inverse) (simp add: Fictional_def)

definition "optionwise I = Fiction (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"
lemma optionwise_\<I>[simp]:
  "\<I> (optionwise I) = (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"
  unfolding optionwise_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def)


paragraph \<open>Partiality\<close>

definition "fine I = Fiction (case_fine (\<I> I) {})"
lemma fine_\<I>[simp]: "\<I> (fine I) = case_fine (\<I> I) {}"
  unfolding fine_def by (rule Fiction_inverse) (simp add: Fictional_def one_fine_def)

definition "defined I = Fiction (\<lambda>x. Fine ` \<I> I x)"
lemma defined_\<I>[simp]: "\<I> (defined I) = (\<lambda>x. Fine ` \<I> I x)"
  unfolding defined_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_fine_def)

definition "partialwise I = fiction.fine (defined I)"
lemma partialwise_\<I>[simp]: "\<I> (partialwise I) (Fine x) = { Fine y |y. y \<in> \<I> I x }"
  unfolding partialwise_def by auto


paragraph \<open>Exact Itself\<close>

definition [simp]: "it' x = {x}"

definition "it = Fiction it'"
lemma it_\<I>[simp]: "\<I> it = it'"
  unfolding it_def by (rule Fiction_inverse) (simp add: Fictional_def one_set_def)


paragraph \<open>Share by Fractional Ownership\<close>

definition "share s = (case s of w \<Znrres> v \<Rightarrow> if w = 1 then {v} else {})"
lemma share_\<I>[simp]: "share (w \<Znrres> v) = (if w = 1 then {v} else {})"
  unfolding share_def by simp

end


lemmas [simp] = fiction.fun_\<I> fiction.fun'_\<I> fiction.option_\<I> fiction.fine_\<I>
  fiction.it'_def fiction.it_\<I> fiction.share_\<I>

lemma [simp]: "\<I> (fiction.fun I) (1(k:=v)) = \<I> I v" by simp


subsection \<open>Extensible Locales\<close>

subsubsection \<open>Basic Project-Inject Structure\<close>

datatype ('NAME,'REP,'T) Entry =
  Entry (name: 'NAME) (project: "'REP \<Rightarrow> 'T") (inject: "'T \<Rightarrow> 'REP")

hide_const (open) name project inject

locale project_inject =
  inj: homo_mult \<open>Entry.inject entry\<close> + prj: homo_mult \<open>Entry.project entry\<close>
  for entry :: "('NAME, 'REP::comm_monoid_mult, 'T::comm_monoid_mult) Entry"
+ assumes proj_inj[simp]: "Entry.project entry (Entry.inject entry x) = x"
begin

abbreviation "name \<equiv> Entry.name entry"
abbreviation "inject \<equiv> Entry.inject entry"
abbreviation "project \<equiv> Entry.project entry"
abbreviation "clean f \<equiv> f(name := 1)"
abbreviation "get f \<equiv> project (f name)"
abbreviation "updt g f \<equiv> f(name := inject (g (get f)))"

end


ML_file_debug \<open>Resource_Space.ML\<close>


paragraph \<open>Syntax\<close>

syntax
  "_entry_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"     ("(2_ #=/ _)")
  "_fine_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"  ("_/'((_)')\<^sub>?" [1000, 0] 900)

definition "fine_fun_updt f x y \<equiv> map_fine (\<lambda>g. fun_upd g x y) f"

lemma fine_fun_updt[simp]:
  "fine_fun_updt (Fine f) x y = Fine (fun_upd f x y)"
  "fine_fun_updt Undef x y = Undef"
  unfolding fine_fun_updt_def by simp_all

translations
  "_fine_Update f (_updbinds b bs)" \<rightleftharpoons> "_fine_Update (_fine_Update f b) bs"
  "f(x#=y)" => "f(CONST Entry.name x := CONST Entry.inject x y)"
  "f(x:=y)\<^sub>?" \<rightleftharpoons> "CONST fine_fun_updt f x y"
  "f(x#=y)\<^sub>?" => "f(CONST Entry.name x := CONST Entry.inject x y)\<^sub>?"


subsubsection \<open>Fictional Space\<close>

locale fictional_space =
  fixes INTERPRET :: "'NAME \<Rightarrow> ('REP::comm_monoid_mult,'RES::comm_monoid_mult) fiction"
begin
definition "INTERP = fiction.fun' INTERPRET"
definition "Fic_Space f \<longleftrightarrow> finite (dom1 f)"
end

locale fictional_project_inject =
  fictional_space INTERPRET + project_inject entry +
  inj: homo_mult \<open>Entry.inject entry\<close> + prj: homo_mult \<open>Entry.project entry\<close>
  for INTERPRET :: "'NAME \<Rightarrow> ('REP::comm_monoid_mult,'RES::comm_monoid_mult) fiction"
  and entry :: "('NAME,'REP,'T::comm_monoid_mult) Entry"
+ fixes I :: "('T,'RES) fiction"
  assumes proj_inj[simp]: "Entry.project entry (Entry.inject entry x) = x"
    and interpret_reduct[simp]: "\<I> (INTERPRET (Entry.name entry)) = \<I> I o Entry.project entry"
begin

abbreviation "m x \<equiv> 1(name := inject x)"

lemmas inj_homo_mult[simp] = inj.homo_mult[symmetric]
lemmas inj_homo_one = inj.homo_one
lemmas prj_homo_mult[simp] = prj.homo_mult
lemmas prj_homo_one = prj.homo_one


lemma [simp]: "R * inject x * inject y = R * inject (x * y)"
  by (simp add: mult.assoc) 

lemma m_homo[simp]: "m x * m y = m (x * y)" by simp
lemma m_1[simp]: "m 1 = 1" by simp
lemma interp_m[simp]: "\<I> INTERP (m x) = \<I> I x"
  unfolding INTERP_def by simp (metis Fiction_one prj_homo_one proj_inj)

lemmas split = fun_split_1[where ?k = name and ?'a = 'NAME and ?'b = 'REP]

lemma interp_split:
  "Fic_Space f \<Longrightarrow>
    \<I> INTERP f = \<I> INTERP (clean f) * \<I> I (project (f name))"
  unfolding INTERP_def Fic_Space_def
  by (subst fiction.fun'_split[where ?f = f and ?k = name]) simp_all

lemma Fic_Space_m[simp]: "Fic_Space (m x)"
  unfolding Fic_Space_def by simp

lemma Fic_Space_mc[simp]: "Fic_Space (clean f) \<longleftrightarrow> Fic_Space f"
  unfolding Fic_Space_def by simp

lemma Fic_Space_mm[simp]: "Fic_Space (f * m x) \<longleftrightarrow> Fic_Space f"
  unfolding Fic_Space_def finite_dom1_mult1 times_fun by simp

end

ML_file_debug \<open>fiction_space.ML\<close>


subsubsection \<open>Finalization\<close>

hide_const (open) Entry
hide_type (open) Entry

end