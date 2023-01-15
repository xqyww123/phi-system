theory Algebras
  imports Main HOL.Rat
    "Phi_Statespace.StateFun" "Phi_Document.Base"
  abbrevs "!!" = "!!"
begin

section \<open>Algebra Structures\<close>

subsection \<open>Preliminary Structures\<close>

subsubsection \<open>Homomorphism-like\<close>

locale homo_one =
  fixes \<phi> :: " 'a::one \<Rightarrow> 'b::one "
  assumes homo_one[simp]: "\<phi> 1 = 1"

locale homo_mult = homo_one \<phi>
  for \<phi> :: " 'a::{one,times} \<Rightarrow> 'b::{one,times} "
+ assumes homo_mult: "\<phi> (x * y) = \<phi> x * \<phi> y"

lemma homo_mult:
  \<open>homo_mult \<phi> \<longleftrightarrow> (\<phi> 1 = 1) \<and> (\<forall> x y. \<phi> (x * y) = \<phi> x * \<phi> y)\<close>
  unfolding homo_mult_def homo_mult_axioms_def homo_one_def ..

locale mult_strip_011 =
  fixes \<psi> :: " 'a::times \<Rightarrow> 'b::times "
  assumes mult_strip_011: \<open>a * \<psi> b = \<psi> c \<longleftrightarrow> (\<exists>a'. a = \<psi> a' \<and> a' * b = c)\<close>

subsubsection \<open>Group-like\<close>

class mult_1 = times + one +
  assumes mult_1_left [simp]: "1 * x = x"
      and mult_1_right[simp]: "x * 1 = x"

subclass (in monoid_mult) mult_1
  by (standard; simp)

class ab_group_mult = inverse + comm_monoid_mult +
  assumes ab_left_inverse: "inverse a * a = 1"
  assumes ab_diff_conv_add_uminus: "a / b = a * (inverse b)"

class semigroup_mult_left_cancel = semigroup_mult +
  assumes semigroup_mult_left_cancel: \<open>a * c = b * c \<longleftrightarrow> a = b\<close>

class no_inverse = times + one +
  assumes no_inverse[simp]: \<open>a * b = 1 \<longleftrightarrow> a = 1 \<and> b = 1\<close>

class no_negative = plus + zero +
  assumes no_negative[simp]: \<open>a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0\<close>

instantiation nat :: no_negative begin
instance by standard simp
end

instantiation nat :: no_inverse begin
instance by standard simp
end

subsection \<open>Separation Algebra\<close>

subsubsection \<open>Separation Disjunction\<close>

class sep_disj =
  fixes sep_disj :: "'a => 'a => bool" (infix "##" 60)

class total_sep_disj = sep_disj +
  assumes total_sep_disj[simp]: \<open>x ## y\<close>

class comm_sep_disj = sep_disj +
  assumes sep_disj_commuteI: "x ## y \<Longrightarrow> y ## x"
begin
lemma sep_disj_commute: "x ## y \<longleftrightarrow> y ## x"
  by (blast intro: sep_disj_commuteI)
end

subsubsection \<open>Separation Magma\<close>

class sep_magma = sep_disj + times
begin
definition join_sub (infix "\<preceq>\<^sub>S\<^sub>L" 50) 
  where \<open>join_sub y z \<longleftrightarrow> (\<exists>x. z = x * y \<and> x ## y)\<close>
end

class positive_sep_magma = sep_magma+
  assumes join_positivity: \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>

subsubsection \<open>Separation Semigroup\<close>

class sep_semigroup = positive_sep_magma +
  assumes sep_mult_assoc:
    "\<lbrakk> x ## y; x * y ## z \<rbrakk> \<Longrightarrow> (x * y) * z = x * (y * z)"
  assumes sep_disj_multD1: "\<lbrakk> x ## y * z; y ## z \<rbrakk> \<Longrightarrow> x ## y"
  assumes sep_disj_multI1: "\<lbrakk> x ## y * z; y ## z \<rbrakk> \<Longrightarrow> x * y ## z"
  assumes sep_disj_multD2: "\<lbrakk> x * y ## z; x ## y \<rbrakk> \<Longrightarrow> y ## z"
  assumes sep_disj_multI2: "\<lbrakk> x * y ## z; x ## y \<rbrakk> \<Longrightarrow> x ## y * z"
begin
lemma sep_mult_assoc':
    "\<lbrakk> y ## z; x ## y * z \<rbrakk> \<Longrightarrow> x * (y * z) = (x * y) * z"
  by (metis local.sep_disj_multD1 local.sep_disj_multI1 local.sep_mult_assoc)
end

class sep_ab_semigroup = sep_semigroup + comm_sep_disj +
  assumes sep_mult_commute: "x ## y \<Longrightarrow> x * y = y * x"
begin
lemma self_sep_disj:
  \<open>x ## y \<Longrightarrow> x * y ## x * y \<Longrightarrow> x ## x\<close>
  \<open>x ## y \<Longrightarrow> x * y ## x * y \<Longrightarrow> y ## y\<close>
  using local.sep_disj_commute local.sep_disj_multD1 sep_disj_multD2 by blast+
end

class sep_disj_intuitive = sep_magma +
  assumes sep_disj_intuitive_right[simp]: \<open>b ## c \<Longrightarrow> a ## b * c \<longleftrightarrow> a ## b \<and> a ## c\<close>
  assumes sep_disj_intuitive_left [simp]: \<open>a ## b \<Longrightarrow> a * b ## c \<longleftrightarrow> a ## c \<and> b ## c\<close>

subsubsection \<open>Unital Separation\<close>

class sep_magma_1 = sep_magma + mult_1 +
  assumes sep_magma_1_left  [simp]: "x ## 1"
  assumes sep_magma_1_right [simp]: "1 ## x"

class positive_sep_magma_1 = sep_magma_1 + positive_sep_magma
begin
lemma sep_no_negative [simp]:
  \<open>x ## y \<Longrightarrow> x * y = 1 \<longleftrightarrow> x = 1 \<and> y = 1\<close>
  by (metis local.join_positivity local.mult_1_right local.sep_magma_1_left sep_magma.join_sub_def)
end

subsubsection \<open>Separation Monoid\<close>

class sep_monoid = sep_magma_1 + sep_semigroup
begin
subclass positive_sep_magma_1 ..
end

definition (in times) subsume (infix "\<preceq>\<^sub>\<times>" 50) 
  where \<open>subsume y z \<longleftrightarrow> (\<exists>x. z = x * y)\<close>

class positive_mult = times +
  assumes positive_mult: \<open>x \<preceq>\<^sub>\<times> y \<Longrightarrow> y \<preceq>\<^sub>\<times> x \<Longrightarrow> x = y\<close>

class positive_mult_one = positive_mult + mult_1
begin
subclass no_inverse apply standard
  by (metis local.mult_1_right local.positive_mult local.subsume_def)
end

class total_sep_monoid = monoid_mult + positive_mult + total_sep_disj
begin
subclass sep_magma .
subclass sep_monoid proof
  fix x y z :: 'a
  show \<open>x ## 1\<close> by simp
  show \<open>1 ## x\<close> by simp
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close>
    using mult_assoc by blast
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    by (clarsimp simp add: join_sub_def, metis local.positive_mult times.subsume_def)
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close> by simp
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z \<close> by simp
qed
subclass positive_mult_one ..
end

subsubsection \<open>Separation Algebra\<close>

class sep_algebra = sep_magma_1 + sep_ab_semigroup
begin

subclass sep_monoid ..

lemma sep_mult_left_commute[simp]:
  "b ## (a * c) \<Longrightarrow> a ## c \<Longrightarrow> b * (a * c) = a * (b * c)"
  by (metis local.sep_disj_commute local.sep_disj_multD2 local.sep_mult_assoc local.sep_mult_commute)

lemma join_sub_frame:
  \<open>r ## y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> r * x \<preceq>\<^sub>S\<^sub>L r * y\<close>
  unfolding join_sub_def
  by (clarsimp, metis local.sep_disj_commuteI local.sep_disj_multI1 local.sep_mult_commute)

(*lemma
  \<open>r ## y \<Longrightarrow> r ## x \<Longrightarrow> r * x \<preceq>\<^sub>S\<^sub>L r * y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y\<close>
  unfolding join_sub_def apply clarsimp *)

lemma join_sub_ext_left:
  \<open>z ## y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L z * y\<close>
  unfolding join_sub_def
  by (clarsimp, metis local.sep_disj_multD1 local.sep_disj_multI1 local.sep_mult_assoc sep_mult_left_commute)

lemma join_sub_ext_right:
  \<open>y ## z \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y * z\<close>
  unfolding join_sub_def
  by (clarsimp, metis local.sep_disj_commute local.sep_disj_multD1 local.sep_disj_multI1 local.sep_mult_assoc local.sep_mult_commute)
end

subsubsection \<open>Special Separation Algebra\<close>

class total_sep_algebra = comm_monoid_mult + positive_mult + total_sep_disj
begin
subclass sep_magma .
subclass sep_algebra proof
  fix x y z :: 'a
  show \<open>x ## 1\<close> by simp
  show \<open>1 ## x\<close> by simp
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by (simp add: mult_commute)
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close> by simp
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close> by simp
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    by (metis local.join_sub_def local.positive_mult times.subsume_def)
  show \<open>x ## y \<Longrightarrow> y ## x\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close> by simp
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close>
    by (simp add: mult_assoc)
qed
subclass total_sep_monoid ..
end

class discrete_sep_semigroup = sep_disj + times +
  assumes discrete_sep_disj[simp]: "x ## y \<longleftrightarrow> x = y"
    and discrete_mult[simp]: "x * y = (if x = y then x else undefined)"
begin
subclass sep_magma .
subclass sep_ab_semigroup proof
  fix x y z :: 'a
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by simp 
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close> unfolding join_sub_def by force
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close> by simp
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close> by simp
  show \<open>x ## y \<Longrightarrow> y ## x\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close> by simp
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close> by simp
  (*show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    using local.join_sub_def by force*)
qed
end

class nonsepable_semigroup = sep_disj + times +
  assumes nonsepable_disj[simp]: "\<not> x ## y"
begin
subclass sep_magma .
subclass sep_ab_semigroup by (standard; simp add: local.join_sub_def)
end

class nonsepable_monoid = sep_disj + mult_1 +
  assumes nonsepable_disj_1[simp]: \<open>x ## y \<longleftrightarrow> x = 1 \<or> y = 1\<close>
begin
subclass sep_magma .
subclass sep_algebra proof
  fix x y z :: 'a
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by fastforce
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close>
    by (metis local.mult_1_right local.nonsepable_disj_1)
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close>
    by (metis local.mult_1_left local.nonsepable_disj_1) 
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def apply clarsimp
    by (metis local.mult_1_left)
  show \<open>x ## 1\<close> by simp
  show \<open>1 ## x\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close>
    by (metis local.mult_1_left local.nonsepable_disj_1)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close>
    by (metis local.mult_1_right local.nonsepable_disj_1)
  show \<open>x ## y \<Longrightarrow> y ## x\<close>
    using local.nonsepable_disj_1 by blast
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close> by force
qed
end



subsubsection \<open>Strict Subsumption\<close>

definition join_sub_strict :: \<open>'a::sep_ab_semigroup \<Rightarrow> 'a::sep_ab_semigroup \<Rightarrow> bool\<close> (infix "\<prec>\<^sub>S\<^sub>L" 50) 
  where \<open>join_sub_strict y z \<longleftrightarrow> join_sub y z \<and> y \<noteq> z\<close>


interpretation join_sub: order \<open>join_sub::'a::sep_algebra \<Rightarrow> 'a \<Rightarrow> bool\<close> join_sub_strict
proof
  fix x y z :: 'a
  show \<open>(x \<prec>\<^sub>S\<^sub>L y) = (x \<preceq>\<^sub>S\<^sub>L y \<and> \<not> y \<preceq>\<^sub>S\<^sub>L x)\<close>
    using join_positivity join_sub_strict_def by blast
  show \<open>x \<preceq>\<^sub>S\<^sub>L x\<close>
    unfolding join_sub_strict_def join_sub_def
    by (rule exI[where x=1], simp)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L z \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L z\<close>
    unfolding join_sub_strict_def join_sub_def
    by (meson join_sub_def join_sub_ext_left)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_strict_def join_sub_def
    using join_positivity join_sub_def by blast
qed
 
interpretation join_sub: order_bot 1 \<open>join_sub::'a::sep_algebra \<Rightarrow> 'a \<Rightarrow> bool\<close> join_sub_strict
proof
  fix a :: 'a
  show \<open>1 \<preceq>\<^sub>S\<^sub>L a\<close>
    unfolding join_sub_strict_def join_sub_def
    by force
qed



subsection \<open>Hierarchical Algebra\<close>

text \<open>Hierarchical Algebra models tree-like data structures.

It is a module-like structure with a path as its scalar, e.g. a list.
The monoid operation of the scalar is path concatenation, and the monoid operation of the elements
is composition of two separated parts of the data structure.
It is different with semimodule in that the scalar is not a semiring but only a monoid.
The scalar does not have addition operation.\<close>

locale hierarchical_alg =
  fixes locate :: \<open>'path::monoid_mult \<Rightarrow> 'a::sep_algebra \<Rightarrow> 'a\<close> (infixr ":\<^enum>" 75)
  assumes locate_distrib_right: \<open>path :\<^enum> (x * y) = path :\<^enum> x * path :\<^enum> y\<close>
    and   locate_assoc: \<open>pa :\<^enum> pb :\<^enum> x = (pa * pb) :\<^enum> x\<close>
    and   locate_left_1:  \<open>1 :\<^enum> x = x\<close>
    and   locate_right_1: \<open>path :\<^enum> 1 = 1\<close>

text \<open>As an example, a structure \<open>struct { struct {A a; B b} c; D d; }\<close> may be represented by
\<open>c :\<^enum> (a :\<^enum> va * b :\<^enum> vb) * d :\<^enum> vd\<close>. \<close>

subsection \<open>Permission Algebra\<close>

text \<open>An algebra for objects that can be partially owned, and shared.

The range of the ownership is [0,\<infinity>). Albeit the total permission is 1, the permission can be
greater than 1.
This relaxation eases various things.
We do not need to check the permission does not exceed 1 when merge two permissions.
The share (division by 2) and the merge are then free of side conditions.
In the hierarchical algebra, the permission of a leaf can be greater than 1 when the permission
of the node is less than 1, e.g. \<open>0.5 :\<Znrres> node_a :\<^enum> (leaf_a :\<^enum> 2 :\<Znrres> a * leaf_b 1 :\<Znrres> a ) \<close> which actually means
\<open>node_a :\<^enum> (leaf_a :\<^enum> 1 :\<Znrres> a * leaf_b :\<^enum> 0.5 :\<Znrres> a )\<close>.
This helps the localized reasoning that focuses on the \<open>node_a\<close> by allowing disregarding to the
environmental permission totally.

TODO: limited by automation, the ownership of an object is represented by \<^typ>\<open>rat\<close>
which includes negative rationals.
It is rather cumbersome cuz assertions have to again and again assert the permission is greater than
(or equal to) 0.
A better choice is using non-negative rationals only, like the type \<open>posrat\<close>, see comments in
Phi-Preliminary.\<close>

class raw_share =
  fixes share :: \<open>rat \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr ":\<Znrres>" 75)

class share = raw_share + \<comment> \<open>share algebra for semigroup, where unit \<open>1\<close> is not defined\<close>
  assumes share_share_not0: \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n (share m x) = share (n * m) x\<close>
    and   share_left_one[simp]:  \<open>share 1 x = x\<close>

class share_one = share + one +
  assumes share_right_one[simp]: \<open>share n 1 = 1\<close>
    and   share_left_0[simp]:    \<open>share 0 x = 1\<close>
begin
lemma share_share: \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> share n (share m x) = share (n * m) x\<close>
  using less_eq_rat_def local.share_share_not0 by fastforce
end

class share_one_eq_one_iff = share_one +
  assumes share_one_eq_one_iff[simp]: \<open>0 < n \<Longrightarrow> share n x = 1 \<longleftrightarrow> x = 1\<close>

class share_sep_disj = share + comm_sep_disj +
  assumes share_sep_disj_left[simp]: \<open>0 < n \<Longrightarrow> share n x ## y \<longleftrightarrow> x ## y\<close>
(*    and   share_sep_disj_refl[simp]:  \<open>n \<noteq> 0 \<Longrightarrow> m \<noteq> 0 \<Longrightarrow> share n x ## share m x\<close> *)
begin

(* lemma share_sep_disj_refl_1 [simp]:
  \<open>m \<noteq> 0 \<Longrightarrow> x ## share m x\<close>  \<open>m \<noteq> 0 \<Longrightarrow> share m x ## x\<close>
  by (metis share_left_one share_sep_disj_refl)+ *)
  
lemma share_sep_disj_right[simp]:
        \<open>0 < n \<Longrightarrow> y ## share n x \<longleftrightarrow> y ## x\<close>
  using local.share_sep_disj_left sep_disj_commute by force

end

class share_semimodule_sep = share_sep_disj + sep_ab_semigroup +
  assumes share_sep_left_distrib_0:  \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> x ## x \<Longrightarrow> share n x * share m x = share (n+m) x\<close>
    and   share_sep_right_distrib_0: \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    and   share_sub_0: \<open>0 < n \<and> n < 1 \<Longrightarrow> x ## x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close>
begin
lemma self_disj_I: \<open>x ## y \<Longrightarrow> x ## x \<Longrightarrow> y ## y \<Longrightarrow> x * y ## x * y\<close>
  by (smt (verit, best) less_numeral_extra(1) local.sep_disj_commuteI local.sep_disj_multI2 local.sep_mult_assoc local.sep_mult_commute local.share_sep_disj_left local.share_sep_left_distrib_0 local.share_sep_right_distrib_0 zero_less_two)
end

class share_module_sep = share_sep_disj + share_one + sep_algebra +
  assumes share_sep_left_distrib:  \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> x ## x \<Longrightarrow> share n x * share m x = share (n+m) x\<close>
    and   share_sep_right_distrib: \<open>0 \<le> n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    and   share_sub: \<open>0 \<le> n \<and> n \<le> 1 \<Longrightarrow> x ## x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x\<close>
begin

subclass share_semimodule_sep proof
  fix x y :: 'a
  fix n m :: rat
  show \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> x ## x \<Longrightarrow> share n x * share m x = share (n + m) x\<close>
    by (meson local.share_sep_left_distrib order_less_le)
  show \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    using local.share_sep_right_distrib order_less_imp_le by blast
  show \<open>0 < n \<and> n < 1 \<Longrightarrow> x ## x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close>
    by (simp add: local.share_sub)
qed
end

class share_semimodule_mult = share_one + monoid_mult +
  assumes share_left_distrib:  \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> share n x * share m x = share (n+m) x\<close>
    and   share_right_distrib: \<open>0 \<le> n \<Longrightarrow> share n x * share n y = share n (x * y)\<close>

class share_resistence_semi = raw_share +
  assumes share_resistence_semi[simp]: \<open>share n x = x\<close>
begin
subclass share by (standard; simp)
end

class share_resistence = raw_share + one +
  assumes share_resistence_semi[simp]: \<open>share n x = (if n = 0 then 1 else x)\<close>
begin
subclass share by (standard; simp)
end

class share_resistence_sep_assms = raw_share + sep_disj + times +
  assumes share_resistence_sep_mult[simp]: \<open>x ## x \<Longrightarrow> x * x = x\<close>

class share_resistence_semimodule_sep = share_resistence_semi + sep_disj + sep_ab_semigroup + share_resistence_sep_assms
begin
subclass share_semimodule_sep by (standard; simp add: join_sub_def)
end

class share_resistence_module_sep = share_resistence + sep_disj + sep_algebra + share_resistence_sep_assms
begin
subclass share_module_sep apply (standard; clarsimp simp add: join_sub_def)
  by (metis local.mult_1_left local.sep_magma_1_right)
end

subsection \<open>Homomorphisms\<close>

locale homo_sep_disj =
  fixes \<psi> :: \<open>'a::sep_disj \<Rightarrow> 'b::sep_disj\<close>
  assumes sep_disj_homo[simp]: \<open>\<psi> a ## \<psi> b \<longleftrightarrow> a ## b\<close>

locale homo_sep_disj_semi =
  fixes \<psi> :: \<open>'a::sep_disj \<Rightarrow> 'b::sep_disj\<close>
  assumes sep_disj_homo_semi[simp]: \<open>a ## b \<longrightarrow> \<psi> a ## \<psi> b\<close> (* TODO: improve this to be a \<longleftrightarrow> ! *)

locale homo_join_sub =
  fixes \<psi> :: \<open>'a::sep_ab_semigroup \<Rightarrow> 'b::sep_ab_semigroup\<close>
  assumes homo_join_sub: \<open>\<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> y \<longleftrightarrow> x \<preceq>\<^sub>S\<^sub>L y\<close>

locale homo_sep_mult = homo_one \<psi>
  for \<psi> :: " 'a::{one,times,sep_disj} \<Rightarrow> 'b::{one,times,sep_disj} "
+ assumes homo_mult: "x ## y \<Longrightarrow> \<psi> (x * y) = \<psi> x * \<psi> y"

locale sep_mult_strip_011 =
  fixes \<psi> :: " 'a::{sep_disj,times} \<Rightarrow> 'b::{sep_disj,times} "
  assumes sep_mult_strip_011: \<open>a ## \<psi> b \<Longrightarrow> a * \<psi> b = \<psi> c \<longleftrightarrow> (\<exists>a'. a = \<psi> a' \<and> a' * b = c \<and> a' ## b)\<close>

locale inj_at_1 =
  fixes \<psi> :: " 'a::one \<Rightarrow> 'b::one"
  assumes inj_at_1: \<open>\<forall>x. \<psi> x = 1 \<longleftrightarrow> x = 1\<close>

text \<open>A homomorphism from Separation Algebra to Share Algebra, which
   maps each element in a separation algebra to the one of the total
   ownership in the share algebra.\<close>

locale perm_transformer' = homo_sep_mult \<psi> + homo_sep_disj_semi \<psi> + sep_mult_strip_011 \<psi> + homo_join_sub \<psi> + inj_at_1 \<psi>
  for \<psi> :: \<open>'a::sep_algebra \<Rightarrow> 'b::share_module_sep\<close>
+ assumes join_sub_share_join_sub_whole: \<open>0 < n \<and> n \<le> 1 \<Longrightarrow> share n (\<psi> x) \<preceq>\<^sub>S\<^sub>L \<psi> y \<longleftrightarrow> x \<preceq>\<^sub>S\<^sub>L y\<close>
    and   inj_\<psi>[simp]: \<open>inj \<psi>\<close>
    and   \<psi>_self_disj: \<open>\<psi> x ## \<psi> x\<close>

text \<open>Given an element of a separation algebra x, a permission transformer \<phi> gives the complete
  permission of x.\<close>

locale perm_transformer =
  fixes \<psi> :: \<open>'a::sep_algebra \<Rightarrow> 'b::share_module_sep\<close>
  assumes perm_transformer': \<open>id perm_transformer' \<psi>\<close>
begin
sublocale perm_transformer' using perm_transformer'[simplified] .
lemma [simp]: \<open>perm_transformer' \<psi>\<close> using perm_transformer' by simp
end

lemma perm_transformer'_id[intro!,simp]:
  \<open>perm_transformer' F \<Longrightarrow> id perm_transformer' F\<close>
  by simp


(* class unital_mult = plus + one +
  assumes unital_add_left[simp]: "1 * x = x"
    and unital_add_right[simp]: "x * 1 = x"

subclass (in monoid_mult) unital_mult .. simp_all *)


section \<open>Instances of Algebras\<close>

(*TODO: some structures like partial map contain plenty of various helper lemmas that
are not settled down properly.*)

subsection \<open>Option\<close>

instantiation option :: (times) times begin
definition "times_option x' y' =
  (case x' of Some x \<Rightarrow> (case y' of Some y \<Rightarrow> Some (x * y) | _ \<Rightarrow> x')
      | None \<Rightarrow> y')"

lemma times_option[simp]:
  "Some x * Some y = Some (x * y)"
  "x' * None = x'"
  "None * x' = x'"
  by (cases x', simp_all add: times_option_def)+

lemma times_option_not_none[simp]:
  \<open>x * Some y \<noteq> None\<close>
  \<open>Some y * x \<noteq> None\<close>
  by (cases x; simp)+

instance ..
end

instantiation option :: (type) one begin
definition [simp]: "one_option = None"
instance ..
end

instantiation option :: (times) mult_1 begin
instance proof
  fix x :: \<open>'a option\<close>
  show \<open>1 * x = x\<close> by (cases x; simp)
  show \<open>x * 1 = x\<close> by (cases x; simp)
qed
end

instantiation option :: (sep_disj) sep_disj begin

definition "sep_disj_option x' y' =
  (case x' of Some x \<Rightarrow> (case y' of Some y \<Rightarrow> x ## y | None \<Rightarrow> True) | _ \<Rightarrow> True)"

lemma sep_disj_option[simp]:
    "Some x ## Some y \<longleftrightarrow> x ## y"
    "None ## z"
    "z ## None"
  unfolding sep_disj_option_def
  apply simp by (cases z; simp)+

instance ..
end

lemma sep_disj_option_nonsepable[simp]:
  \<open>x ## Some y \<longleftrightarrow> x = None\<close>
  \<open>Some y ## x \<longleftrightarrow> x = None\<close>
  for y :: \<open>'a :: nonsepable_semigroup\<close>
  by (cases x; simp)+

instantiation option :: (comm_sep_disj) comm_sep_disj begin
instance apply (standard; case_tac x; case_tac y; simp)
  using sep_disj_commute by blast
end

instantiation option :: (sep_magma) sep_magma begin
instance ..
end

instantiation option :: (sep_magma) sep_magma_1 begin
instance proof
  fix x y :: \<open>'a option\<close>
  show \<open>x ## 1\<close> by simp
  show \<open>1 ## x\<close> by simp
qed
end

instantiation option :: (positive_sep_magma) positive_sep_magma_1 begin
instance proof
  fix x y :: \<open>'a option\<close>
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def
    apply (cases x; clarsimp simp add: sep_disj_commute sep_mult_commute;
           cases y; clarsimp simp add: sep_disj_commute sep_mult_commute)
    apply (metis times_option_not_none(1))
     apply (metis times_option_not_none(1))
    apply (auto simp add: sep_disj_option_def split: option.split)
    subgoal for _ u v _ apply (cases u; cases v; simp)
      by (metis join_positivity join_sub_def) .
qed
end


instantiation option :: (sep_semigroup) sep_semigroup begin
instance proof
  fix x y z :: \<open>'a option\<close>
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close>
    by (cases x; cases y; cases z; simp add: sep_disj_commute sep_mult_commute sep_mult_assoc)
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close>
    apply (cases x; simp; cases y; simp; cases z; simp)
    using sep_disj_multD1 by blast
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close>
    apply (cases x; simp; cases y; simp; cases z; simp)
    using sep_disj_multI1 by blast
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close>
    apply (cases x; simp; cases y; simp; cases z; simp)
    using sep_disj_multD2 by blast
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close>
    apply (cases x; simp; cases y; simp; cases z; simp)
    using sep_disj_multI2 by blast
qed
end

instantiation option :: (sep_ab_semigroup) sep_ab_semigroup begin
instance proof
  fix x y z :: \<open>'a option\<close>
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by (cases x; cases y; simp add: sep_disj_commute sep_mult_commute)
qed
end

instantiation option :: (sep_ab_semigroup) sep_algebra begin
instance ..
end


instantiation option :: (share) share begin

definition \<open>share_option n = (if 0 < n then map_option (share n) else (\<lambda>_. None))\<close>

lemma share_option_simps[simp]:
  \<open>share n None = None\<close> \<open>share 0 x = None\<close> \<open>0 < n \<Longrightarrow> share n (Some x') = Some (share n x')\<close>
  unfolding share_option_def by simp_all

instance by (standard; simp add: share_option_def; case_tac x; simp add: share_share_not0)
end

instantiation option :: (sep_disj_intuitive) sep_disj_intuitive begin
instance proof
  fix a b c :: \<open>'a option\<close>
  show \<open>b ## c \<Longrightarrow> a ## b * c = (a ## b \<and> a ## c)\<close> by (cases a; cases b; cases c; simp)
  show \<open>a ## b \<Longrightarrow> a * b ## c = (a ## c \<and> b ## c)\<close> by (cases a; cases b; cases c; simp)
qed
end

instantiation option :: (share) share_one_eq_one_iff begin
instance by (standard; simp add: share_option_def; case_tac x; simp)
end

instantiation option :: (share_sep_disj) share_sep_disj begin
instance by (standard; case_tac x; simp add: share_option_def; case_tac y;
             simp add: share_sep_left_distrib_0 order_less_le)
end

instantiation option :: (share_semimodule_sep) share_module_sep begin
instance proof
  fix n m :: rat
  fix x y :: \<open>'a option\<close>
  show \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> x ## x \<Longrightarrow> share n x * share m x = share (n + m) x\<close>
    by (case_tac x; clarsimp simp add: share_option_def share_sep_left_distrib_0 order_less_le)
  show \<open>0 \<le> n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    by (case_tac x; case_tac y; clarsimp simp add: share_option_def share_sep_right_distrib_0)
  show \<open>0 \<le> n \<and> n \<le> 1 \<Longrightarrow> x ## x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x\<close>
    unfolding join_sub_def apply (cases x; clarsimp simp add: share_option_def)
    apply (cases \<open>n = 1\<close>)
    apply (metis sep_disj_option(2) share_left_one times_option(3))
    apply (cases \<open>n = 0\<close>, simp)
    subgoal premises prems for x'
    proof -
      have t1: \<open>share n x' \<preceq>\<^sub>S\<^sub>L x' \<or> share n x' = x'\<close>
        by (meson antisym_conv2 prems(1) prems(3) prems(4) prems(5) share_sub_0)
      show ?thesis apply (insert t1)
        unfolding join_sub_def apply (elim disjE; clarsimp)
        apply (metis sep_disj_option(1) times_option(1))
        by (metis mult_1_class.mult_1_left sep_magma_1_right) 
    qed .
qed
end

instantiation option :: (times) no_inverse begin
instance by (standard, case_tac a; case_tac b; simp)
end

lemma times_option_none[simp]:
  \<open>x * y = None \<longleftrightarrow> x = None \<and> y = None\<close>
  using no_inverse one_option_def by metis

lemma Some_nonsepable_semigroup_sub_join[simp]:
  \<open>Some x \<preceq>\<^sub>S\<^sub>L X \<longleftrightarrow> X = Some x\<close>
  for x :: \<open>'a::nonsepable_semigroup\<close>
  by (simp add: join_sub_def)


subsection \<open>Product\<close>

instantiation prod :: (times, times) times begin
definition "times_prod = (\<lambda>(x1,x2) (y1,y2). (x1 * y1, x2 * y2))"
lemma times_prod[simp]: "(x1,x2) * (y1,y2) = (x1 * y1, x2 * y2)"
  unfolding times_prod_def by simp
instance ..
end

instantiation prod :: (plus, plus) plus begin
definition "plus_prod = (\<lambda>(x1,x2) (y1,y2). (x1 + y1, x2 + y2))"
lemma plus_prod[simp]: "(x1,x2) + (y1,y2) = (x1 + y1, x2 + y2)"
  unfolding plus_prod_def by simp
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
instance by standard (simp_all add: split_paired_all algebra_simps)
end

instantiation prod :: (monoid_mult, monoid_mult) monoid_mult begin
instance by standard (simp_all add: one_prod_def split_paired_all algebra_simps)
end

instantiation prod :: (no_inverse, no_inverse) no_inverse begin
instance by (standard, simp add: one_prod_def times_prod_def split: prod.split) blast
end

instantiation prod :: (no_negative, no_negative) no_negative begin
instance by (standard, simp add: zero_prod_def plus_prod_def split: prod.split) blast
end

instantiation prod :: (ab_semigroup_mult, ab_semigroup_mult) ab_semigroup_mult begin
instance apply standard
  by (metis mult.commute prod.collapse times_prod) 
end

instantiation prod :: (comm_monoid_mult, comm_monoid_mult) comm_monoid_mult begin
instance apply standard by simp 
end

instantiation prod :: (sep_disj,sep_disj) sep_disj begin
definition \<open>sep_disj_prod x y = (case x of (x1,x2) \<Rightarrow> case y of (y1,y2) \<Rightarrow> x1 ## y1 \<and> x2 ## y2)\<close>
lemma sep_disj_prod[simp]:
  \<open>(x1,y1) ## (x2,y2) \<longleftrightarrow> x1 ## x2 \<and> y1 ## y2\<close>
  unfolding sep_disj_prod_def by simp
instance ..
end

instantiation prod :: (sep_magma,sep_magma) sep_magma begin
instance ..
end

instantiation prod :: (sep_disj_intuitive,sep_disj_intuitive) sep_disj_intuitive begin
instance by (standard; case_tac a; case_tac b; case_tac c; simp; blast)
end


subsection \<open>List\<close>

instantiation list :: (type) times begin
definition "times_list a b = b @ a"
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

instantiation list :: (type) no_inverse begin
instance by (standard, simp add: times_list_def) blast
end

instantiation list :: (type) semigroup_mult begin
instance by standard (simp_all add: times_list_def)
end

instantiation list :: (type) monoid_mult begin
instance by standard (simp_all add: times_list_def)
end

instantiation list :: (type) sep_magma begin
definition sep_disj_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>
  where [simp]: \<open>sep_disj_list _ _ = True\<close>
instance by (standard; simp)
end

instantiation list :: (type) sep_monoid begin
instance by (standard; clarsimp simp add: times_list_def join_sub_def)
end

instantiation list :: (type) sep_disj_intuitive begin
instance by (standard; simp)
end



subsection \<open>Function\<close>

paragraph \<open>Instantiations of Algebra\<close>

instantiation "fun" :: (type,plus) plus begin
definition "plus_fun f g = (\<lambda>x. f x + g x)"
instance ..
end

instantiation "fun" :: (type,times) times begin
definition "times_fun f g = (\<lambda>x. f x * g x)"
instance ..
end

lemma times_fun: "(f * g) x = f x * g x"
  unfolding times_fun_def by simp

lemma plus_fun: "(f + g) x = f x + g x"
  unfolding plus_fun_def by simp

instantiation "fun" :: (type,zero) zero begin
definition "zero_fun = (\<lambda>(x::'a). (0::'b))"
instance ..
end

instantiation "fun" :: (type,one) one begin
definition "one_fun = (\<lambda>(x::'a). (1::'b))"
instance ..
end

lemma one_fun[simp]: "1 x = 1" unfolding one_fun_def by simp
lemma zero_fun[simp]: "0 x = 0" unfolding zero_fun_def by simp
lemmas zero_fun_eta[simp] = zero_fun_def[symmetric]

instantiation "fun" :: (type, no_inverse) no_inverse begin
instance by (standard, simp add: one_fun_def times_fun fun_eq_iff, blast) 
end

instantiation "fun" :: (type, no_negative) no_negative begin
instance by (standard, simp del: zero_fun_eta add: zero_fun_def plus_fun fun_eq_iff, blast) 
end

instantiation "fun" :: (type, semigroup_mult) semigroup_mult begin
instance apply standard
  by (simp add: mult.assoc times_fun_def)
end

instantiation "fun" :: (type,sep_disj) sep_disj begin
definition "sep_disj_fun m1 m2 = (\<forall>x. m1 x ## m2 x)"
instance ..
end

instantiation "fun" :: (type,comm_sep_disj) comm_sep_disj begin
instance by (standard, simp_all add: sep_disj_fun_def times_fun fun_eq_iff
                                add: sep_disj_commute sep_mult_commute )
end

lemma sep_disj_fun[simp]: \<open>(f ## g) \<Longrightarrow> f x ## g x\<close>
  unfolding sep_disj_fun_def by blast

lemma sep_disj_fun_nonsepable:
  \<open>f x = Some v \<Longrightarrow> f ## g \<Longrightarrow> g x = None\<close>
  \<open>f x = Some v \<Longrightarrow> g ## f \<Longrightarrow> g x = None\<close>
  for v :: \<open>'a :: nonsepable_semigroup\<close>
  by (metis sep_disj_fun sep_disj_option_nonsepable)+
  

instantiation "fun" :: (type,mult_1) mult_1 begin
instance by (standard; simp add: one_fun_def times_fun_def)
end

instantiation "fun" :: (type,sep_magma) sep_magma begin
instance ..
end

instantiation "fun" :: (type,sep_magma_1) sep_magma_1 begin
instance by (standard; simp add: sep_disj_fun_def)
end

instantiation "fun" :: (type,sep_semigroup) sep_semigroup begin
instance proof
  fix x y z :: "'a \<Rightarrow> 'b"
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close>
    apply (simp add: sep_disj_fun_def times_fun_def fun_eq_iff)
    using sep_mult_assoc by blast
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def apply (clarsimp simp add: times_fun fun_eq_iff)
    by (metis join_positivity join_sub_def sep_disj_fun)
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close>
    apply (simp add: sep_disj_fun_def times_fun_def fun_eq_iff)
    using sep_disj_multD1 by blast
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close>
    apply (simp add: sep_disj_fun_def times_fun_def fun_eq_iff)
    using sep_disj_multI1 by blast
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close>
    apply (simp add: sep_disj_fun_def times_fun_def fun_eq_iff)
    using sep_disj_multD2 by blast
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close>
    apply (simp add: sep_disj_fun_def times_fun_def fun_eq_iff)
    using sep_disj_multI2 by blast
qed
end

instantiation "fun" :: (type,sep_ab_semigroup) sep_ab_semigroup begin
instance proof
  fix x y z :: "'a \<Rightarrow> 'b"
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close>
    by (simp add: sep_disj_fun_def times_fun_def fun_eq_iff sep_disj_commute sep_mult_commute)
qed
end

instantiation "fun" :: (type, sep_monoid) sep_monoid begin
instance by (standard; simp add: sep_disj_fun_def fun_eq_iff times_fun_def; blast)
end

instantiation "fun" :: (type, sep_algebra) sep_algebra begin
instance by (standard; simp add: sep_disj_fun_def fun_eq_iff times_fun_def; blast)
end

instantiation "fun" :: (type,sep_disj_intuitive) sep_disj_intuitive begin
instance by (standard; simp add: sep_disj_fun_def times_fun; blast)
end

instantiation "fun" :: (type,monoid_mult) monoid_mult begin
instance by standard (simp_all add: mult.commute times_fun_def fun_eq_iff)
end

instantiation "fun" :: (type,comm_monoid_mult) comm_monoid_mult begin
instance by standard (simp_all add: mult.commute times_fun_def fun_eq_iff)
end


instantiation "fun" :: (type,monoid_add) monoid_add begin
instance proof
  fix a b c :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>a + b + c = a + (b + c)\<close> unfolding plus_fun_def fun_eq_iff by (simp add: add.assoc)
  show \<open>0 + a = a\<close> unfolding plus_fun_def fun_eq_iff by (simp add: add.assoc)
  show \<open>a + 0 = a\<close> unfolding plus_fun_def fun_eq_iff by (simp add: add.assoc)
qed
end

instantiation "fun" :: (type,comm_monoid_add) comm_monoid_add begin
instance proof
  fix a b :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>a + b = b + a\<close> unfolding plus_fun_def fun_eq_iff using add.commute by blast 
  show \<open>0 + a = a\<close> unfolding plus_fun_def fun_eq_iff by simp
qed
end

paragraph \<open>Multiplication with Function Update\<close>

lemma times_fupdt_1_apply[simp]:
  "(f * 1(k := x)) k = f k * x" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  by (simp add: times_fun_def)

lemma times_fupdt_1_apply_sep[simp]:
  "(f * 1(k := x)) k = f k * x" for f :: "'a \<Rightarrow> 'b::sep_monoid"
  by (simp add: times_fun_def)

lemma times_fupdt_1_apply'[simp]:
  "k' \<noteq> k \<Longrightarrow> (f * 1(k':=x)) k = f k" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  by (simp add: times_fun_def)

lemma times_fupdt_1_apply'_sep[simp]:
  "k' \<noteq> k \<Longrightarrow> (f * 1(k':=x)) k = f k" for f :: "'a \<Rightarrow> 'b::sep_monoid"
  by (simp add: times_fun_def)

lemma times_fupdt_1_fupdt_1[simp]:
  "(f * 1(k := x))(k:=1) = f(k:=1)" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma times_fupdt_1_fupdt_1_sep[simp]:
  "(f * 1(k := x))(k:=1) = f(k:=1)" for f :: "'a \<Rightarrow> 'b::sep_monoid"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma [simp]:
  "k' \<noteq> k \<Longrightarrow> (f * 1(k' := x))(k:=1) = f(k:=1) * 1(k' := x)" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma [simp]:
  "k' \<noteq> k \<Longrightarrow> (f * 1(k' := x))(k:=1) = f(k:=1) * 1(k' := x)" for f :: "'a \<Rightarrow> 'b::sep_monoid"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp


instantiation "fun" :: (type,total_sep_monoid) total_sep_monoid begin
instance proof
  fix x y :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>x \<preceq>\<^sub>\<times> y \<Longrightarrow> y \<preceq>\<^sub>\<times> x \<Longrightarrow> x = y\<close>
    unfolding subsume_def apply (clarsimp simp add: times_fun_def fun_eq_iff)
    using positive_mult_class.positive_mult subsume_def by blast
  show \<open>x ## y\<close> by (simp add: sep_disj_fun_def)
qed
end

instantiation "fun" :: (type,total_sep_algebra) total_sep_algebra begin
instance ..
end


lemma fun_split_1: "f = f(k:=1) * 1(k:= f k)" for f :: "'a \<Rightarrow> 'b :: mult_1"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma fun_1upd1[simp]:
  "1(k := 1) = 1"
  unfolding one_fun_def fun_upd_def by simp

lemma fun_1upd_homo:
    "1(k := x) * 1(k := y) = 1(k := x * y)" for x :: "'a::sep_monoid"
  unfolding one_fun_def fun_upd_def times_fun_def
  by fastforce

lemma fun_1upd_homo_right1:
    "f(k := x) * 1(k := y) = f(k := x * y)" for x :: "'a::sep_monoid"
  unfolding one_fun_def fun_upd_def times_fun_def fun_eq_iff
  by clarsimp

lemma fun_1upd_homo_left1:
    "1(k := x) * f(k := y) = f(k := x * y)" for x :: "'a::sep_monoid"
  unfolding one_fun_def fun_upd_def times_fun_def fun_eq_iff
  by clarsimp

lemma [simp]: "NO_MATCH (a::'a) (1::'a::one) \<Longrightarrow> i \<noteq> k \<Longrightarrow> f(i := a, k := 1) = f(k := 1, i := a)"
  using fun_upd_twist .


paragraph \<open>Share\<close>

instantiation "fun" :: (type, share) share begin

definition share_fun :: \<open>rat \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  where \<open>share_fun n f = share n o f\<close>

instance by (standard; simp add: share_fun_def fun_eq_iff share_share_not0)
end

instantiation "fun" :: (type,share_one) share_one begin
instance by (standard; simp add: share_fun_def fun_eq_iff)
end

instantiation "fun" :: (type,share_one_eq_one_iff) share_one_eq_one_iff begin
instance by (standard; simp add: share_fun_def fun_eq_iff)
end

instantiation "fun" :: (type, share_sep_disj) share_sep_disj begin
instance by (standard; simp add: share_fun_def fun_eq_iff sep_disj_fun_def)
end

instantiation "fun" :: (type, share_module_sep) share_module_sep begin
instance apply (standard; simp_all add: share_fun_def fun_eq_iff times_fun_def share_sep_left_distrib
      sep_disj_fun_def share_sep_right_distrib join_sub_def)
  subgoal premises prems for n x proof -
    have t1: \<open>\<forall>a. share n (x a) \<preceq>\<^sub>S\<^sub>L (x a)\<close>
      by (simp add: prems share_sub)
    show ?thesis apply (insert t1; clarsimp simp add: join_sub_def)
      by metis
  qed .
end

instantiation "fun" :: (type, share_semimodule_mult) share_semimodule_mult begin
instance by standard (simp_all add: share_fun_def fun_eq_iff times_fun_def share_left_distrib share_right_distrib)
end

lemma share_fun_updt[simp]:
  \<open>share n (f(k := v)) = (share n f)(k := share n v)\<close>
  unfolding share_fun_def fun_eq_iff by simp


paragraph \<open>Complete Permission\<close>

ML \<open>
structure ML_Attribute = Generic_Data (
  type T = Thm.attribute option
  val empty : T = NONE
  fun merge (a,_) = a
)
\<close>

attribute_setup ML_attr = \<open>Scan.peek (fn ctxt => Parse.ML_source >> (fn src =>
  ML_Context.expression (Input.pos_of src)
    ( ML_Lex.read "Context.>> (ML_Attribute.put (SOME (Thm.rule_attribute [] (("
    @ ML_Lex.read_source src
    @ ML_Lex.read ") o Context.proof_of))))") ctxt
  |> ML_Attribute.get |> the
))\<close>


subsection \<open>Unit\<close>

instantiation unit :: plus begin
definition [simp]: "plus_unit (f::unit) (g::unit) = ()"
instance ..
end

instantiation unit :: times begin
definition [simp]: "times_unit (f::unit) (g::unit) = ()"
instance ..
end

instantiation unit :: zero begin
definition [simp]: "zero_unit = ()"
instance ..
end

instantiation unit :: one begin
definition [simp]: "one_unit = ()"
instance ..
end

instantiation unit :: monoid_mult begin
instance by standard simp_all
end

instantiation unit :: no_inverse begin
instance by standard simp_all
end

instantiation unit :: no_negative begin
instance by standard simp_all
end

instantiation unit :: sep_disj_intuitive begin
definition sep_disj_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> bool\<close> where [simp]: \<open>sep_disj_unit _ _ = True\<close>
instance by (standard; simp)
end


subsection \<open>Set\<close>

definition Inhabited :: " 'a set \<Rightarrow> bool" where  "Inhabited S = (\<exists>p. p \<in> S)"

lemma Inhabited_I:
  \<open>x \<in> S \<Longrightarrow> Inhabited S\<close>
  unfolding Inhabited_def ..



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

instantiation set :: ("{sep_disj,times}") times begin
definition "times_set P Q = { x * y | x y. x \<in> P \<and> y \<in> Q \<and> x ## y }"
instance ..
end

lemma times_set_I:
  \<open>x \<in> P \<Longrightarrow> y \<in> Q \<Longrightarrow> x ## y \<Longrightarrow> x * y \<in> P * Q\<close>
  unfolding times_set_def by simp blast

lemma set_mult_zero[iff]: "{} * S = {}" "S * {} = {}"
  unfolding times_set_def by simp_all

lemma set_mult_single: \<open>A ## B \<Longrightarrow> {A} * {B} = {A * B}\<close>
  unfolding times_set_def set_eq_iff by simp

lemma set_mult_expn:
  \<open>uv \<in> (S * T) \<longleftrightarrow> (\<exists>u v. uv = u * v \<and> u \<in> S \<and> v \<in> T \<and> u ## v)\<close>
  unfolding times_set_def by simp

lemma set_mult_inhabited[elim!]:
  \<open>Inhabited (S * T) \<Longrightarrow> (Inhabited S \<Longrightarrow> Inhabited T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def times_set_def by (simp, blast)

lemma times_set_subset[intro, simp]:
  \<open>B \<subseteq> B' \<Longrightarrow> A * B \<subseteq> A * B'\<close>
  \<open>B \<subseteq> B' \<Longrightarrow> B * A \<subseteq> B' * A\<close>
  unfolding subset_iff times_set_def by simp_all blast+

instantiation set :: ("{sep_disj,times}") mult_zero begin
instance by (standard; simp add: zero_set_def times_set_def)
end

instantiation set :: ("{sep_magma_1,no_inverse}") no_inverse begin
instance apply (standard, simp add: one_set_def times_set_def set_eq_iff)
  by (metis (no_types, opaque_lifting) no_inverse sep_magma_1_left sep_magma_1_right)
end

instantiation set :: (type) total_sep_disj begin
definition sep_disj_set :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where [simp]: \<open>sep_disj_set _ _ = True\<close>
instance by (standard; simp)
end

instantiation set :: (sep_magma) sep_magma begin
instance ..
end

instantiation set :: (sep_magma_1) sep_magma_1 begin
instance proof
  fix x :: \<open>'a set\<close>
  show \<open>1 * x = x\<close> unfolding one_set_def times_set_def by simp
  show \<open>x * 1 = x\<close> unfolding one_set_def times_set_def by simp
  show \<open>x ## 1\<close> unfolding one_set_def sep_disj_set_def by simp
  show \<open>1 ## x\<close> unfolding one_set_def sep_disj_set_def by simp
qed
end

instantiation set :: (sep_disj_intuitive) sep_disj_intuitive begin
instance by (standard; simp)
end

instantiation set :: (sep_semigroup) semigroup_mult begin
instance
  apply (standard; clarsimp simp add: times_set_def algebra_simps set_eq_iff; rule; clarsimp)
  using sep_disj_multD2 sep_disj_multI2 sep_mult_assoc apply blast
  by (metis sep_disj_multD1 sep_disj_multI1 sep_mult_assoc)
end

instantiation set :: (sep_monoid) monoid_mult begin
instance by standard (simp_all add: one_set_def times_set_def)
end

instantiation set :: (sep_ab_semigroup) ab_semigroup_mult begin
instance apply (standard; simp add: times_set_def set_eq_iff)
  using sep_disj_commute sep_mult_commute by blast
end

instantiation set :: (sep_algebra) comm_monoid_mult begin
instance by (standard; simp_all add: one_set_def times_set_def)
end

instantiation set :: (type) comm_monoid_add begin
definition \<open>plus_set = union\<close>
instance by standard (auto simp add: plus_set_def zero_set_def)
end

instantiation set :: (type) ordered_comm_monoid_add begin
instance by standard (auto simp add: plus_set_def zero_set_def)
end

lemma plus_set_in_iff[iff]:
  \<open>x \<in> A + B \<longleftrightarrow> x \<in> A \<or> x \<in> B\<close> unfolding plus_set_def by simp

lemma plus_set_S_S [simp]: \<open>S + S = S\<close> for S :: \<open>'a set\<close> unfolding plus_set_def by simp

instantiation set :: (sep_semigroup) ordered_semiring_0 begin
instance by standard (auto simp add: zero_set_def plus_set_def times_set_def)
end

instantiation set :: (sep_monoid) semiring_1 begin
instance by standard (auto simp add: zero_set_def plus_set_def times_set_def)
end

instantiation set :: (sep_ab_semigroup) ordered_comm_semiring begin
instance apply standard
  apply (simp add: zero_set_def plus_set_def times_set_def)
  using mult.commute apply blast
  by simp
end

instantiation set :: (sep_algebra) comm_semiring_1 begin
instance by standard (auto simp add: zero_set_def plus_set_def times_set_def)
end

subsection \<open>Partial Map\<close>

lemma one_partial_map: \<open>1 = Map.empty\<close>
  unfolding one_fun_def one_option_def ..

lemma times_fun_map_add_right:
  \<open>dom f \<inter> dom h = {} \<Longrightarrow> (f * g) ++ h = f * (g ++ h)\<close>
  unfolding times_fun_def fun_eq_iff map_add_def
  by (simp add: disjoint_iff domIff option.case_eq_if times_option_def)

subsubsection \<open>Separation Disjunction\<close>

lemma sep_disj_partial_map_del:
  \<open>f ## g \<Longrightarrow> f ## g(k := None)\<close>
  unfolding sep_disj_fun_def sep_disj_option_def
  apply clarify subgoal premises prems for x
    apply (insert prems[THEN spec[where x=x]])
    by (cases \<open>f x\<close>; simp; cases \<open>g x\<close>; simp) .

lemma sep_disj_partial_map_disjoint:
  "f ## g \<longleftrightarrow> dom f \<inter> dom g = {}"
  for f :: "'a \<rightharpoonup> ('b :: nonsepable_semigroup)"
  unfolding sep_disj_fun_def sep_disj_option_def disjoint_iff
  by (smt (verit, ccfv_SIG) domD domIff nonsepable_disj option.simps(4) option.simps(5))
  

lemma sep_disj_partial_map_some_none:
  \<open>f ## g \<Longrightarrow> g k = Some v \<Longrightarrow> f k = None\<close>
  for f :: "'a \<rightharpoonup> ('b :: nonsepable_semigroup)"
  using disjoint_iff sep_disj_partial_map_disjoint by fastforce

lemma sep_disj_partial_map_not_1_1:
  \<open>f ## g \<Longrightarrow> g k \<noteq> 1 \<Longrightarrow> f k = 1\<close>
  for f :: "'a \<Rightarrow> ('b :: nonsepable_monoid)"
  unfolding sep_disj_fun_def apply simp
  by blast
  

lemma sep_disj_partial_map_upd:
  \<open>f ## g \<Longrightarrow> k \<in> dom g \<Longrightarrow> (f * g)(k := v) = (f * g(k:=v))\<close>
  for f :: "'a \<rightharpoonup> ('b :: nonsepable_semigroup)"
  unfolding sep_disj_partial_map_disjoint fun_upd_def times_fun fun_eq_iff
  by simp (metis disjoint_iff domIff times_option(3))

lemma nonsepable_semigroup_sepdisj_fun:
  \<open>a ## 1(k \<mapsto> x) \<Longrightarrow> a ## 1(k := any)\<close>
  for x :: \<open>'b::nonsepable_semigroup\<close>
  unfolding sep_disj_fun_def
  by (metis fun_upd_other fun_upd_same sep_magma_1_right sep_disj_option_nonsepable(1))


lemma fun_sep_disj_fupdt[simp]:
  \<open>f1 ## f2 \<Longrightarrow> x1 ## x2 \<Longrightarrow> f1(k := x1) ## f2(k := x2)\<close>
  unfolding sep_disj_fun_def by simp

lemma fun_sep_disj_1_fupdt[simp]:
  \<open>f(k := x1) ## 1(k := x2) \<longleftrightarrow> x1 ## x2\<close>
  \<open>1(k := x1) ## f(k := x2) \<longleftrightarrow> x1 ## x2\<close>
  for x1 :: \<open>'b :: sep_magma_1\<close>
  unfolding sep_disj_fun_def by (simp; rule; clarsimp)+

lemma fun_sep_disj_imply_v:
  \<open>f(k := x1) ## g(k := x2) \<Longrightarrow> x1 ## x2\<close>
  unfolding sep_disj_fun_def
  apply (clarsimp simp add: sep_disj_fun_def)
  by presburger

lemma share_1_fupdt[simp]:
  \<open>share n (1(k := v)) = 1(k := share n v)\<close>
  for v :: \<open>'b::share_one\<close>
  by simp


subsubsection \<open>dom1: Domain except one\<close>

definition "dom1 f = {x. f x \<noteq> 1}"

lemma dom1_1[simp]: "dom1 1 = {}"
  unfolding dom1_def by simp

lemma dom_1[simp]: "dom 1 = {}"
  by (simp add: one_fun_def)

lemma dom1_upd[simp]: "dom1 (f(x:=y)) = (if y = 1 then dom1 f - {x} else insert x (dom1 f))"
  unfolding dom1_def by auto

lemma dom1_dom: "dom1 f = dom f"
  by (metis dom1_def dom_def one_option_def)

lemma one_updt_one[simp]: "1(a:=1) = 1" unfolding one_fun_def fun_upd_def by simp

lemma v_neq_1_fupdt_neq_1[simp]: "x \<noteq> 1 \<Longrightarrow> f(k:=x) \<noteq> 1"
  unfolding one_fun_def fun_upd_def fun_eq_iff by simp blast

lemma one_ringop_f_is_1[simp]: "1 o f = 1"
  unfolding one_fun_def fun_eq_iff by simp

lemma finite_dom1_mult1[simp]:
  "finite (dom1 (f * 1(k:=v))) \<longleftrightarrow> finite (dom1 f)"
  for f :: "'a \<Rightarrow> 'b :: sep_monoid"
proof -
  have "dom1 (f * 1(k:=v)) = dom1 f \<or> dom1 (f * 1(k:=v)) = insert k (dom1 f)
    \<or> dom1 (f * 1(k:=v)) = dom1 f - {k}"
  for f :: "'a \<Rightarrow> 'b :: sep_monoid"
  unfolding dom1_def times_fun_def fun_upd_def set_eq_iff by simp
  then show ?thesis
    by (metis finite_Diff finite_insert infinite_remove)
qed

lemma dom1_disjoint_sep_disj:
  \<open>dom1 g \<inter> dom1 f = {} \<Longrightarrow> g ## f\<close>
  for f :: \<open>'a \<Rightarrow> 'b::sep_magma_1\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff
  by (simp; metis sep_magma_1_left sep_magma_1_right)

lemma sep_disj_dom1_disj_disjoint:
  \<open>g ## f \<longleftrightarrow> dom1 g \<inter> dom1 f = {}\<close>
  for f :: \<open>'a \<Rightarrow> 'b::nonsepable_monoid\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff
  by clarsimp

lemma dom1_mult: \<open>f ## g \<Longrightarrow> dom1 (f * g) = dom1 f \<union> dom1 g\<close>
  for f :: \<open>'a \<Rightarrow> 'b :: {no_inverse,sep_disj}\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff times_fun by simp

lemma dom_mult: \<open>f ## g \<Longrightarrow> dom (f * g) = dom f \<union> dom g\<close>
  using dom1_mult dom1_dom by metis

(* lemma dom1_mult_disjoint: \<open>dom1 (f * g) = dom1 f \<union> dom1 g\<close>
  for f :: \<open>'a \<Rightarrow> 'b :: no_inverse\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff times_fun by simp *)

lemma dom1_sep_mult_disjoint:
  \<open>f ## g \<Longrightarrow>  dom1 (f * g) = dom1 f \<union> dom1 g\<close>
  for f :: \<open>'a \<Rightarrow> 'b :: positive_sep_magma_1\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff times_fun by simp

lemma disjoint_dom1_eq_1:
  \<open>dom1 f \<inter> dom1 g = {} \<Longrightarrow> k \<in> dom1 f \<Longrightarrow> g k = 1\<close>
  \<open>dom1 f \<inter> dom1 g = {} \<Longrightarrow> k \<in> dom1 g \<Longrightarrow> f k = 1\<close>
  unfolding dom1_def set_eq_iff by simp_all blast+

lemma fun_split_1_not_dom1:
  "k \<notin> dom1 f \<Longrightarrow> f(k := v) = f * 1(k:= v)" for f :: "'a \<Rightarrow> 'b::mult_1"
  unfolding fun_upd_def fun_eq_iff times_fun_def dom1_def by simp

lemma fun_split_1_not_dom:
  "k \<notin> dom f \<Longrightarrow> f(k := v) = f * 1(k:= v)"
  unfolding fun_upd_def fun_eq_iff times_fun_def dom_def by simp


subsubsection \<open>Multiplication with Prod\<close>

lemma fun_prod_homo:
  \<open>prod (f * g) S = prod f S * prod g S\<close>
  by (simp add: prod.distrib times_fun)

lemma prod_superset_dom1:
  \<open> finite S
\<Longrightarrow> dom1 f \<subseteq> S
\<Longrightarrow> prod f S = prod f (dom1 f)\<close>
  subgoal premises prems proof -
    define R where \<open>R \<equiv> S - dom1 f\<close>
    have t1: \<open>dom1 f \<inter> R = {}\<close>    using R_def by blast
    have t2: \<open>S = dom1 f \<union> R\<close>     using R_def prems(2) by blast
    have t3: \<open>finite R\<close>           using prems(1) t2 by blast
    have t4: \<open>finite (dom1 f)\<close>    using prems(1) t2 by blast
    have t5: \<open>prod f S = prod f (dom1 f) * prod f R\<close>
      using prod.union_disjoint t1 t2 t3 t4 by blast
    show ?thesis
      by (simp add: R_def dom1_def t5)
  qed .


subsubsection \<open>Total Permission Transformation\<close>


lemma perm_transformer_pointwise:
  \<open>perm_transformer' \<psi> \<Longrightarrow> perm_transformer' ((\<circ>) \<psi>)\<close>
  unfolding comp_def
  subgoal premises prem proof
    note t1[simp] = prem[unfolded comp_def perm_transformer'_axioms_def
        perm_transformer_def homo_one_def homo_mult_def homo_mult_axioms_def mult_strip_011_def
        homo_sep_disj_semi_def homo_join_sub_def perm_transformer'_def homo_sep_mult_def
        homo_sep_mult_axioms_def sep_mult_strip_011_def inj_at_1_def]
    have t2[unfolded join_sub_def]:
      \<open>(\<forall>n x y. 0 < n \<and> n \<le> 1 \<longrightarrow> (share n (\<psi> x) \<preceq>\<^sub>S\<^sub>L \<psi> y) = (x \<preceq>\<^sub>S\<^sub>L y))\<close>
      using t1 by blast

    fix x y z a b c :: \<open>'c \<Rightarrow> 'a\<close>
    fix a' :: \<open>'c \<Rightarrow> 'b\<close>
    fix n :: rat
    show \<open>(\<lambda>x. \<psi> (1 x)) = 1\<close> by (simp add: fun_eq_iff)
    show \<open>a ## b \<longrightarrow> (\<lambda>x. \<psi> (a x)) ## (\<lambda>x. \<psi> (b x))\<close>
      by (simp add: fun_eq_iff times_fun sep_disj_fun_def)
    show \<open>x ## y \<Longrightarrow> (\<lambda>xa. \<psi> ((x * y) xa)) = (\<lambda>xa. \<psi> (x xa)) * (\<lambda>x. \<psi> (y x))\<close>
      by (simp add: fun_eq_iff times_fun sep_disj_fun_def)
    show \<open>a' ## (\<lambda>x. \<psi> (b x)) \<Longrightarrow>
       (a' * (\<lambda>x. \<psi> (b x)) = (\<lambda>x. \<psi> (c x))) = (\<exists>a. a' = (\<lambda>x. \<psi> (a x)) \<and> a * b = c \<and> a ## b)\<close>
      by (simp add: fun_eq_iff times_fun sep_disj_fun_def
              all_conj_distrib[symmetric], subst choice_iff[symmetric], rule; clarify)
    show \<open>((\<lambda>xa. \<psi> (x xa)) \<preceq>\<^sub>S\<^sub>L (\<lambda>x. \<psi> (y x))) = (x \<preceq>\<^sub>S\<^sub>L y)\<close>
      apply (simp add: join_sub_def fun_eq_iff times_fun sep_disj_fun_def all_conj_distrib[symmetric],
        subst choice_iff[symmetric], subst choice_iff[symmetric])
      by (rule; clarsimp; metis t1)

    show \<open>0 < n \<and> n \<le> 1 \<Longrightarrow> (share n (\<lambda>xa. \<psi> (x xa)) \<preceq>\<^sub>S\<^sub>L (\<lambda>x. \<psi> (y x))) = (x \<preceq>\<^sub>S\<^sub>L y)\<close>
      apply (simp add: join_sub_def fun_eq_iff times_fun sep_disj_fun_def share_fun_def
        all_conj_distrib[symmetric],
        subst choice_iff[symmetric], subst choice_iff[symmetric])
      using t2 by simp

    show \<open>inj (\<lambda>g x. \<psi> (g x))\<close>
      by (rule, simp add: fun_eq_iff inj_eq)
    show \<open>\<forall>x. ((\<lambda>xa. \<psi> (x xa)) = 1) = (x = 1)\<close>
      by (simp add: one_fun_def fun_eq_iff)
    show \<open>(\<lambda>xa. \<psi> (x xa)) ## (\<lambda>xa. \<psi> (x xa))\<close>
      by (simp add: sep_disj_fun_def)
  qed .

lemma perm_transformer_pointwise_eq[iff]:
  \<open>perm_transformer' ((\<circ>) \<psi>) \<longleftrightarrow> perm_transformer' \<psi>\<close>
  for \<psi> :: \<open>'b::sep_algebra \<Rightarrow> 'c::share_module_sep\<close>
  apply rule prefer 2 using perm_transformer_pointwise apply blast
  unfolding comp_def
  subgoal premises prem proof
    note t1 = prem[unfolded comp_def perm_transformer'_axioms_def
        perm_transformer_def homo_one_def homo_mult_def homo_mult_axioms_def mult_strip_011_def
        homo_sep_disj_semi_def homo_join_sub_def perm_transformer'_def homo_sep_mult_def
        homo_sep_mult_axioms_def sep_mult_strip_011_def inj_at_1_def]
    ML_prf \<open>Context.>> (Context.map_proof (Proof_Context.put_thms false ("t2", SOME (
        HOLogic.conj_elims @{context} @{thm t1}
    ))))\<close>
    note t3 = t2[unfolded sep_disj_fun_def times_fun one_fun_def fun_eq_iff, simplified]
    fix x y z a b c :: \<open>'b\<close>
    fix a' :: 'c
    fix n :: rat

    show \<psi>1[simp]: \<open>\<psi> 1 = 1\<close> using t3 by simp

    have x1[simp]: \<open>\<And>k v x. \<psi> ((1(k := v)) x) = (1(k := \<psi> v)) x\<close> by simp
    have x2[simp]: \<open>\<And>k a b. (1(k := a) \<preceq>\<^sub>S\<^sub>L 1(k := b)) \<longleftrightarrow> a \<preceq>\<^sub>S\<^sub>L (b::'x::sep_algebra)\<close>
      unfolding join_sub_def
      by (metis fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1) fun_upd_same fun_upd_triv) 
    have x3[simp]: \<open>\<And>k a b. 1(k := a) = 1(k := b) \<longleftrightarrow> a = b\<close>
      by (metis fun_upd_same)

    show \<open>a ## b \<longrightarrow> \<psi> a ## \<psi> b\<close> by (meson t3(3))
    show \<open>x ## y \<Longrightarrow> \<psi> (x * y) = \<psi> x * \<psi> y\<close> by (meson t3(2))
    show \<open>a' ## \<psi> b \<Longrightarrow> (a' * \<psi> b = \<psi> c) = (\<exists>a. a' = \<psi> a \<and> a * b = c \<and> a ## b)\<close>
      unfolding t2(4)[THEN spec[where x=\<open>1(undefined := a')\<close>],
                THEN spec[where x=\<open>1(undefined := b)\<close>],
                THEN spec[where x=\<open>1(undefined := c)\<close>],
                simplified x1 fun_sep_disj_1_fupdt fun_1upd_homo x3]
      apply (rule; clarsimp)
      apply (metis fun_upd_same sep_disj_fun_def times_fun)
      by (metis fun_1upd_homo_right1 fun_sep_disj_1_fupdt(2) x1)
    show \<open>(\<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> y) = (x \<preceq>\<^sub>S\<^sub>L y)\<close>
      using t3(5)[THEN spec[where x=\<open>1(undefined := x)\<close>],
                  THEN spec[where x=\<open>1(undefined := y)\<close>], simplified x1 x2] .
    show \<open>\<forall>x. (\<psi> x = 1) = (x = 1)\<close>
      by (meson join_sub.bot.extremum_unique t3(6))
    show \<open>0 < n \<and> n \<le> 1 \<Longrightarrow> (share n (\<psi> x) \<preceq>\<^sub>S\<^sub>L \<psi> y) = (x \<preceq>\<^sub>S\<^sub>L y)\<close>
      using t3(7)[THEN spec, of n, THEN mp, THEN spec[where x=\<open>1(undefined := x)\<close>],
                  THEN spec[where x=\<open>1(undefined := y)\<close>], simplified x1 x2 share_1_fupdt] .
    show \<open>inj \<psi>\<close>
      apply (insert t3(8); simp add: inj_def fun_eq_iff)
      by meson
    show \<open>\<psi> x ## \<psi> x\<close>
      using t3(9)[THEN spec[where x=\<open>\<lambda>_. x\<close>], simplified] .
  qed .

subsubsection \<open>Subsumption\<close>

lemma nonsepable_partial_map_subsumption:
  \<open>f \<preceq>\<^sub>S\<^sub>L g \<Longrightarrow> k \<in> dom1 f \<Longrightarrow> g k = f k\<close>
  for f :: \<open>'k \<Rightarrow> 'v::nonsepable_monoid\<close>
  unfolding join_sub_def
  apply (clarsimp simp add: times_fun)
  by (metis disjoint_dom1_eq_1(1) mult_1_class.mult_1_left sep_disj_commute sep_disj_dom1_disj_disjoint)

lemma nonsepable_1_fupdt_subsumption:
  \<open> 1(k := v) \<preceq>\<^sub>S\<^sub>L objs
\<Longrightarrow> v \<noteq> 1
\<Longrightarrow> objs k = v\<close>
  for v :: \<open>'v::nonsepable_monoid\<close>
  using nonsepable_partial_map_subsumption[where f=\<open>1(k := v)\<close>]
  by (clarsimp simp add: times_fun)

lemma nonsepable_partial_map_subsumption_L2:
  \<open> 1(k := v) \<preceq>\<^sub>S\<^sub>L objs
\<Longrightarrow> v \<subseteq>\<^sub>m objs k\<close>
  for v :: \<open>'b \<Rightarrow> 'c::nonsepable_semigroup option\<close>
  unfolding join_sub_def map_le_def
  apply (clarsimp simp add: times_fun)
  by (metis (mono_tags, opaque_lifting) fun_upd_same mult_1_class.mult_1_left one_option_def sep_disj_fun_def sep_disj_partial_map_some_none)


(* subsection \<open>Partiality\<close>


datatype 'a fine ("_ ?" [100] 101) = Fine (the_fine: 'a) | Undef
notation the_fine ("!!_" [1000] 1000)

lemma split_fine_all: \<open>All P \<longleftrightarrow> (\<forall>x. P (Fine x)) \<and> P Undef\<close> by (metis fine.exhaust_sel)
lemma split_fine_ex : \<open>Ex  P \<longleftrightarrow> (\<exists>x. P (Fine x)) \<or> P Undef\<close> by (metis fine.exhaust_sel) 

lemma Fine_inject[simp]: \<open>inj Fine\<close>
  by (meson fine.inject injI)

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

instantiation fine :: ("{sep_disj,times}") times begin

definition "times_fine x y =
  (case x of Fine a \<Rightarrow> (case y of Fine b \<Rightarrow> if a ## b then Fine (a*b) else Undef
    | _ \<Rightarrow> Undef) | _ \<Rightarrow> Undef)"

lemma times_fine:
  "Fine a * Fine b = (if a ## b then Fine (a*b) else Undef)"
  "Undef * a' = Undef" "a' * Undef = Undef"
  unfolding times_fine_def by (cases a'; simp_all)+

lemma times_fine':
  \<open>a ## b \<Longrightarrow> Fine a * Fine b = Fine (a*b)\<close>
  using times_fine by simp

lemma times_fine''[simp]:
  \<open>a ## b \<Longrightarrow> !!(Fine a * Fine b) = (a*b)\<close>
  using times_fine by simp

instance ..
end

instantiation fine :: (sep_magma_1) mult_1 begin
instance by (standard; case_tac x; simp add: one_fine_def times_fine_def)
end


instantiation fine :: ("{sep_disj,times}") mult_zero begin
instance by standard (simp_all add: times_fine)
end

instantiation fine :: (sep_semigroup) semigroup_mult begin
instance proof
  fix a b c :: \<open>'a ?\<close>
  show \<open>a * b * c = a * (b * c)\<close>
    apply (cases a; cases b; cases c; clarsimp simp add: sep_disj_commute sep_mult_commute times_fine)
    by (metis sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc)
qed
end

instantiation fine :: (sep_ab_semigroup) ab_semigroup_mult begin
instance proof
  fix a b c :: \<open>'a ?\<close>
  show \<open>a * b = b * a\<close>
    by (cases a; cases b; clarsimp simp add: sep_disj_commute sep_mult_commute times_fine)
qed
end

instantiation fine :: (sep_monoid) monoid_mult begin
instance by (standard; simp)
end

instantiation fine :: (sep_algebra) comm_monoid_mult begin
instance by standard (case_tac a; simp add: one_fine_def times_fine)
end

instantiation fine :: (type) total_sep_disj begin
definition sep_disj_fine :: \<open>'a ? \<Rightarrow> 'a ? \<Rightarrow> bool\<close> where
  [simp]: \<open>sep_disj_fine x y = True\<close>
instance by (standard; simp)
end

instantiation fine :: (sep_magma) sep_magma begin
instance by (standard; case_tac x; case_tac y; simp add: sep_disj_commute one_fine_def)
end

instantiation fine :: (sep_monoid) total_sep_monoid begin
instance proof
  fix x y z :: \<open>'a fine\<close>
  show \<open>x \<preceq>\<^sub>\<times> y \<Longrightarrow> y \<preceq>\<^sub>\<times> x \<Longrightarrow> x = y\<close>
    apply (cases x; cases y; simp add: subsume_def split_fine_ex times_fine)
    apply clarsimp
    by (metis fine.sel fine.simps(3) join_positivity join_sub_def)
qed
end

instantiation fine :: (sep_algebra) total_sep_algebra begin
instance ..
end

instantiation fine :: (sep_disj_intuitive) sep_disj_intuitive begin
instance by (standard; case_tac a; case_tac b; case_tac c; simp)
end


lemma mult_strip_fine_111:
  \<open>Fine a * Fine b = Fine c \<longleftrightarrow> (a ## b \<and> a * b = c)\<close>
  by (simp add: times_fine)

lemma mult_strip_fine_011:
  \<open>NO_MATCH (Fine a'') a' \<Longrightarrow>
   a' * Fine b = Fine c \<longleftrightarrow> (\<exists>a. a' = Fine a \<and> a ## b \<and> a * b = c)\<close>
  by (cases a'; simp add: times_fine)

lemma mult_strip_fine_001:
  \<open>NO_MATCH (Fine a'') a' \<Longrightarrow> NO_MATCH (Fine b'') b' \<Longrightarrow>
   a' * b' = Fine c \<longleftrightarrow> (\<exists>a b. a' = Fine a \<and> b' = Fine b \<and> a ## b \<and> a * b = c)\<close>
  by (cases a'; cases b'; simp add: times_fine)

*)

subsection \<open>Fractional SA\<close>

datatype 'a share = Share (perm:rat) (val: 'a)
hide_const (open) val perm

lemma share_exists: \<open>Ex  P \<longleftrightarrow> (\<exists>n x. P (Share n x))\<close> by (metis share.exhaust_sel)
lemma share_forall: \<open>All P \<longleftrightarrow> (\<forall>n x. P (Share n x))\<close> by (metis share.exhaust_sel)
lemma share_All: \<open>(\<And>x. PROP P x) \<equiv> (\<And>n x'. PROP (P (Share n x')))\<close> proof
  fix n x' assume \<open>(\<And>x. PROP P x)\<close> then show \<open>PROP P (Share n x')\<close> .
next fix x assume \<open>\<And>n x'. PROP P (Share n x')\<close>
  from \<open>PROP P (Share (share.perm x) (share.val x))\<close> show \<open>PROP P x\<close> by simp
qed

instantiation share :: (type) sep_magma begin

definition times_share :: "'a share \<Rightarrow> 'a share \<Rightarrow> 'a share" where
  "times_share x' y' = (case x' of Share n x \<Rightarrow> (case y' of Share m y \<Rightarrow>
    if x = y then Share (n+m) x else undefined))"

lemma times_share[simp]:
  "(Share n x) * (Share m y) = (if x = y then Share (n+m) x else undefined)"
  unfolding times_share_def by simp_all

definition sep_disj_share :: "'a share \<Rightarrow> 'a share \<Rightarrow> bool" where
  "sep_disj_share x' y' \<longleftrightarrow> (case x' of Share n x \<Rightarrow>
    (case y' of Share m y \<Rightarrow> 0 < n \<and> 0 < m \<and> x = y))"

lemma sep_disj_share[simp]:
  "(Share n x) ## (Share m y) \<longleftrightarrow> 0 < n \<and> 0 < m \<and> x = y"
  unfolding sep_disj_share_def by simp_all

instance ..
end

instantiation share :: (type) sep_ab_semigroup begin
instance proof
  fix x y z :: "'a share"
  show "x ## y \<Longrightarrow> x * y = y * x" by (cases x; cases y) (simp add: add.commute) 
  show "x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)"
    by (cases x; cases y; cases z) (simp add: add.assoc)
  show "x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y"
    by (cases x; cases y; cases z; simp)
  show "x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z"
    by (cases x; cases y; cases z)
       (simp add: ab_semigroup_add_class.add_ac(1) order_less_le)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def
    apply (clarsimp; cases x; cases y; clarsimp)
    by (metis add.commute add_cancel_left_left add_le_cancel_left le_add_same_cancel1 less_le_not_le nle_le sep_disj_share share.exhaust share.inject share.sel(2) times_share)
  show "x ## y \<Longrightarrow> y ## x" by (cases x; cases y) (simp add: add.commute)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close>
    by (cases x; cases y; cases z; simp)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close>
    by (cases x; cases y; cases z; simp)
qed
end

instantiation share :: (type) sep_disj_intuitive begin
instance by (standard; case_tac a; case_tac b; case_tac c; simp)
end

instantiation share :: (type) share begin

definition share_share :: "rat \<Rightarrow> 'a share \<Rightarrow> 'a share"
  where \<open>share_share n x = (case x of Share m x' \<Rightarrow> Share (n*m) x')\<close>
lemma share_share[simp]: \<open>share n (Share m x) = Share (n*m) x\<close>
  unfolding share_share_def by simp

instance by (standard; case_tac x; simp add: share_share_def mult.assoc mult_le_one)

end

instantiation share :: (type) share_semimodule_sep begin
instance proof
  fix x y :: \<open>'a share\<close>
  fix n n' m :: rat

  show \<open>0 < n \<Longrightarrow> share n x ## y = x ## y\<close>
    by (cases x; cases y; simp add: zero_less_mult_iff)
  show \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n x * share m x = share (n + m) x\<close>
    by (cases x; cases y; simp add: distrib_right)
  show \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    by (cases x; cases y; simp add: distrib_left)
  show \<open>0 < n \<and> n < 1 \<Longrightarrow> x ## x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close>
    apply (cases x; cases y; simp add: join_sub_def share_exists)
    by (metis add.commute add_le_same_cancel1 diff_add_cancel linorder_not_le mult_1_class.mult_1_left mult_less_cancel_right)
qed
end



subsubsection \<open>Convert a function to sharing or back\<close>

abbreviation \<open>to_share \<equiv> map_option (Share 1)\<close>
abbreviation \<open>strip_share \<equiv> map_option share.val\<close>

lemma perm_transformer_to_share[iff]:
  \<open>perm_transformer' (to_share::'a::nonsepable_semigroup option \<Rightarrow> 'a share option)\<close>
proof
  fix x y z a b c :: \<open>'a option\<close>
  fix a' :: \<open>'a share option\<close>
  fix n :: rat
  show \<open>to_share 1 = 1\<close> by simp
  show \<open>a ## b \<longrightarrow> to_share a ## to_share b\<close> by (cases a; cases b; simp)
  show \<open>x ## y \<Longrightarrow> to_share (x * y) = to_share x * to_share y\<close> by (cases x; cases y; simp)
  show \<open>a' ## to_share b \<Longrightarrow>
       (a' * to_share b = to_share c) = (\<exists>a. a' = to_share a \<and> a * b = c \<and> a ## b)\<close>
    apply (cases a'; cases b; cases c; simp add: split_option_ex)
    subgoal for a'' by (cases a''; simp) .
  show \<open>(to_share x \<preceq>\<^sub>S\<^sub>L to_share y) = (x \<preceq>\<^sub>S\<^sub>L y)\<close>
    apply (cases x; cases y; simp add: join_sub_def split_option_all split_option_ex)
    by (metis sep_disj_multD1 sep_disj_share share.collapse)
  show \<open>0 < n \<and> n \<le> 1 \<Longrightarrow> (share n (to_share x) \<preceq>\<^sub>S\<^sub>L to_share y) = (x \<preceq>\<^sub>S\<^sub>L y)\<close>
    apply (cases a'; cases x; cases y; simp add: join_sub_def split_option_ex share_forall share_exists
          share_All)
    apply (metis add.commute add_le_same_cancel1 diff_add_cancel linorder_not_le nle_le)
    by (metis Orderings.order_eq_iff diff_add_cancel less_add_same_cancel2 linorder_le_less_linear)
  show \<open>inj to_share\<close>
    by (rule, simp, metis option.inj_map_strong share.inject)
  show \<open>\<forall>x. (to_share x = 1) = (x = 1)\<close> by simp
  show \<open>to_share x ## to_share x\<close> by (cases x; simp)
qed


lemma strip_share_Share[simp]:
  \<open>strip_share (map_option (Share n) x) = x\<close>
  by (cases x; simp)

lemma to_share_funcomp_1[simp]:
  \<open>to_share o 1 = 1\<close>
  unfolding fun_eq_iff by simp

lemma strip_share_share_funcomp[simp]:
  \<open>strip_share o map_option (Share n) = id\<close>
  \<open>strip_share o (map_option (Share n) o f) = f\<close>
  by (simp add: fun_eq_iff)+

lemma strip_share_fun_mult:
 \<open>f ## g \<Longrightarrow> strip_share o (f * g) = (strip_share o f) ++ (strip_share o g)\<close>
  unfolding fun_eq_iff times_fun map_add_def times_option_def
        times_share_def comp_def sep_disj_fun_def sep_disj_share_def sep_disj_option_def
  apply (clarsimp split: option.split share.split)
  subgoal premises prems for x
    by (insert prems(1)[THEN spec[where x=x]] prems(2,3,4), simp) .

lemma strip_share_share[simp]:
  \<open>0 < n \<Longrightarrow> strip_share (share n x) = strip_share x\<close>
  by (cases x; simp; case_tac a; simp)

lemma strip_share_fun_share[simp]:
  \<open>0 < n \<Longrightarrow> strip_share o share n f = strip_share o f\<close>
  unfolding fun_eq_iff share_fun_def by simp


interpretation to_share_homo_one: homo_one to_share
  by standard simp

lemma to_share_eq_1_iff[simp]:
  \<open>to_share x = 1 \<longleftrightarrow> x = 1\<close> by simp

lemma to_share_funcomp_eq_1_iff[simp]:
  \<open>to_share o f = 1 \<longleftrightarrow> f = 1\<close> by (simp add: fun_eq_iff)

lemma to_share_total_disjoint:
  \<open>g ## (to_share o h) \<Longrightarrow>
  to_share o f = g * (to_share o h) \<Longrightarrow> dom g \<inter> dom (to_share o h) = {}\<close>
  unfolding fun_eq_iff times_fun times_share_def times_option_def
      sep_disj_fun_def sep_disj_option_def sep_disj_share_def
  apply auto
  subgoal premises prems for x y z
    using prems(1)[THEN spec[where x = x]]
          prems(2)[THEN spec[where x = x]]
          prems(3,4)
    by (cases y, simp)
  done

lemma to_share_funcomp_map_add:
  \<open>to_share o (f ++ g) = (to_share o f) ++ (to_share o g)\<close>
  unfolding fun_eq_iff map_add_def by (auto split: option.split)


lemma to_share_strip_011:
  \<open> a ## (to_share o b)
\<Longrightarrow> a * (to_share o b) = to_share \<circ> y
\<longleftrightarrow> (\<exists>a'. a = to_share o a' \<and> a' * b = y \<and> a' ## b)\<close>
  for a :: \<open>'a \<Rightarrow> 'b::nonsepable_semigroup share option\<close>
  unfolding times_fun fun_eq_iff sep_disj_fun_def all_conj_distrib[symmetric]
  apply (simp, subst choice_iff[symmetric])
  apply (rule; clarsimp)
  subgoal premises prems for x
    apply (insert prems[THEN spec[where x=x]])
    apply (cases \<open>b x\<close>; cases \<open>a x\<close>; cases \<open>y x\<close>; simp)
    by (metis add_cancel_left_left less_numeral_extra(3) sep_disj_share share.collapse share.sel(1) times_share)
  subgoal premises prems for x
    apply (insert prems[THEN spec[where x=x]])
    by (cases \<open>b x\<close>; cases \<open>a x\<close>; cases \<open>y x\<close>; clarsimp) .

lemma to_share_funcomp_sep_disj_I:
  \<open>a ## b \<Longrightarrow> (to_share o a) ## (to_share o b)\<close>
  for a :: \<open>'a \<Rightarrow> 'b::nonsepable_semigroup option\<close>
  unfolding sep_disj_fun_def apply simp
   apply clarsimp subgoal premises prems for x
    apply (insert prems[THEN spec[where x=x]])
    by (cases \<open>a x\<close>; cases \<open>b x\<close>; simp) .

lemma to_share_ringop_id[simp]:
  \<open>to_share \<circ> x = to_share \<circ> y \<longleftrightarrow> x = y\<close>
  unfolding fun_eq_iff
  by (simp, metis strip_share_Share)


subsection \<open>Non-sepable Semigroup\<close>

datatype 'a nonsepable = nonsepable (dest: 'a)
hide_const (open) dest

instantiation nonsepable :: (type) nonsepable_semigroup begin
definition \<open>sep_disj_nonsepable (x :: 'a nonsepable) (y :: 'a nonsepable) = False\<close>
definition share_nonsepable :: \<open>rat \<Rightarrow> 'a nonsepable \<Rightarrow> 'a nonsepable\<close>
  where [simp]: \<open>share_nonsepable _ x = x\<close>
definition times_nonsepable :: \<open>'a nonsepable \<Rightarrow> 'a nonsepable \<Rightarrow> 'a nonsepable\<close>
  where [simp]: \<open>times_nonsepable x y = x\<close>
instance by (standard; case_tac x; simp; case_tac y; simp add: sep_disj_nonsepable_def)
end

instantiation nonsepable :: (type) sep_disj_intuitive begin
instance by (standard; case_tac a; case_tac b; case_tac c; simp)
end

subsection \<open>Agreement\<close>

datatype 'a agree = agree 'a

lemma agree_forall: \<open>All P \<longleftrightarrow> (\<forall>x. P (agree x))\<close> by (metis agree.exhaust) 
lemma agree_exists: \<open>Ex P  \<longleftrightarrow> (\<exists>x. P (agree x))\<close> by (metis agree.exhaust) 

instantiation agree :: (type) sep_magma begin
definition times_agree :: \<open>'a agree \<Rightarrow> 'a agree \<Rightarrow> 'a agree\<close>
  where [simp]: \<open>times_agree x y = x\<close>
definition sep_disj_agree :: \<open>'a agree \<Rightarrow> 'a agree \<Rightarrow> bool\<close>
  where [simp]: \<open>sep_disj_agree x y \<longleftrightarrow> x = y\<close>

instance ..
end

instantiation agree :: (type) share_semimodule_sep begin

definition share_agree :: \<open>rat \<Rightarrow> 'a agree \<Rightarrow> 'a agree\<close>
  where [simp]: \<open>share_agree _ x = x\<close>

instance proof
  fix x y z :: \<open>'a agree\<close>
  fix n n' m :: rat
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by (case_tac x; case_tac y; simp)
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close> by (case_tac x; case_tac y; simp)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close> unfolding join_sub_def by simp
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close> by (case_tac x; case_tac y; case_tac z; simp)
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close> by (case_tac x; case_tac y; case_tac z; simp)
  show \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n (share m x) = share (n * m) x\<close> by (cases x; simp)
  show \<open>share 1 x = x\<close> by (cases x; simp)
  show \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n x * share m x = share (n + m) x\<close> by (cases x; simp)
  show \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close> by (cases x; simp)
  show \<open>0 < n \<and> n < 1 \<Longrightarrow> x ## x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close> by (cases x; simp)
  show \<open>x ## y \<Longrightarrow> y ## x\<close> by (cases x; cases y; simp)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close> by (cases x; cases y; cases z; simp)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close> by (cases x; cases y; cases z; simp)
  show \<open>0 < n \<Longrightarrow> share n x ## y = x ## y\<close> by (cases x; cases y; simp)
qed
end

instantiation agree :: (type) sep_disj_intuitive begin
instance by (standard; case_tac a; case_tac b; case_tac c; simp)
end


section \<open>Interpretation of Fictional Separation\<close>

subsection \<open>Algebric Structure\<close>

text \<open>
  Referring to Fictional Separation Logic~\cite{FSL}, the interpretation of fictional separation
  maps a fictional resource to a set of concrete resource.
  The interpretation can be any map to set that preserves \<open>1\<close>, the unit of the separation algebra.\<close>

definition Interpretation :: "('a::one \<Rightarrow> 'b::one set) \<Rightarrow> bool"
  where "Interpretation \<I> \<longleftrightarrow> \<I> 1 = 1"

typedef (overloaded) ('a::one,'b::one) interp
    = \<open>Collect (Interpretation :: ('a \<Rightarrow> 'b set) \<Rightarrow> bool)\<close>
  morphisms \<I> Interp
  by (rule exI[where x = \<open>\<lambda>_. 1\<close>]) (simp add:sep_mult_commute Interpretation_def)

text \<open>Type \<open>('a,'b) interp\<close> encapsulating the 1-preserving condition, represents an interpretation.
\<^const>\<open>\<I>\<close> activates the interpretation; \<^const>\<open>Interp\<close> constructs an interpretation by checking
the 1-preserving condition.
\[@{thm Interp_inverse[simplified]}\]\<close>

lemmas Interp_inverse[simp] = Interp_inverse[simplified]

lemma Interp_one[simp]: "\<I> I 1 = 1"
  using Interpretation_def \<I> by blast


subsection \<open>Instances\<close>


subsubsection \<open>Function, pointwise\<close>

definition "\<F>_fun' I = Interp (\<lambda>f. prod (\<lambda>x. \<I> (I x) (f x)) (dom1 f))"

lemma \<F>_fun'_\<I>[simp]: "\<I> (\<F>_fun' I) = (\<lambda>f. prod (\<lambda>x. \<I> (I x) (f x)) (dom1 f))"
  unfolding \<F>_fun'_def by (rule Interp_inverse) (simp add: Interpretation_def)

lemma \<F>_fun'_split:
  " finite (dom1 f)
\<Longrightarrow> \<I> (\<F>_fun' I) f = \<I> (\<F>_fun' I) (f(k:=1)) * \<I> (I k) (f k)
   \<and> \<I> (\<F>_fun' I) (f(k:=1)) ## \<I> (I k) (f k)"
  for f :: "'a \<Rightarrow> 'b::sep_algebra"
  by simp (smt (verit, best) Interp_one dom1_upd fun_upd_triv mult.comm_neutral mult.commute prod.insert_remove)


definition "\<F>_fun I = \<F>_fun' (\<lambda>_. I)"

lemma \<F>_fun_\<I>[simp]: "\<I> (\<F>_fun I) = (\<lambda>f. prod (\<I> I o f) (dom1 f))"
  unfolding \<F>_fun_def by simp

lemma \<F>_fun_split:
  " finite (dom1 f)
\<Longrightarrow> \<I> (\<F>_fun I) f = \<I> (\<F>_fun I) (f(k:=1)) * \<I> I (f k)
  \<and> \<I> (\<F>_fun I) (f(k:=1)) ## \<I> I (f k)"
  for f :: "'a \<Rightarrow> 'b::sep_algebra"
  unfolding \<F>_fun_def using \<F>_fun'_split .

lemma \<F>_interp_fun_\<I>_1_fupdt[simp]: "\<I> (\<F>_fun I) (1(k:=v)) = \<I> I v" by simp


definition "\<F>_pointwise I = Interp (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"

lemma \<F>_pointwise_\<I>[simp]:
  "\<I> (\<F>_pointwise I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> I (f x) })"
  unfolding \<F>_pointwise_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fun_def fun_eq_iff)


definition "\<F>_pointwise' I = Interp (\<lambda>f. {g. \<forall>x. g x \<in> \<I> (I x) (f x) })"

lemma \<F>_pointwise'_\<I>[simp]:
  "\<I> (\<F>_pointwise' I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> (I x) (f x) })"
  unfolding \<F>_pointwise'_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fun_def fun_eq_iff)



subsubsection \<open>Pairwise\<close>

definition "\<F>_pair I1 I2 = Interp (\<lambda>(x,y). \<I> I1 x * \<I> I2 y) "

lemma \<F>_pair_\<I>[simp]: "\<I> (\<F>_pair I1 I2) = (\<lambda>(x,y). \<I> I1 x * \<I> I2 y)"
  for I1 :: "('a::one,'b::sep_monoid) interp"
  unfolding \<F>_pair_def
  by (rule Interp_inverse) (simp add: Interpretation_def one_prod_def)

notation \<F>_pair (infixl "\<bullet>\<^sub>\<F>" 50)


subsubsection \<open>Option\<close>

definition "\<F>_option I = Interp (case_option 1 I)"

lemma \<F>_option_\<I>[simp]: "\<I> (\<F>_option I) = (case_option 1 I)"
  unfolding \<F>_option_def
  by (rule Interp_inverse) (simp add: Interpretation_def)


definition "\<F>_optionwise I = Interp (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"

lemma \<F>_optionwise_\<I>[simp]:
  "\<I> (\<F>_optionwise I) = (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"
  unfolding \<F>_optionwise_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def)


(* subsubsection \<open>Partiality\<close>

definition "fine I = Interp (case_fine (\<I> I) {})"
lemma fine_\<I>[simp]: "\<I> (fine I) = case_fine (\<I> I) {}"
  unfolding fine_def by (rule Interp_inverse) (simp add: Interpretation_def one_fine_def)

definition "defined I = Interp (\<lambda>x. Fine ` \<I> I x)"
lemma defined_\<I>[simp]: "\<I> (defined I) = (\<lambda>x. Fine ` \<I> I x)"
  unfolding defined_def
  by (rule Interp_inverse) (auto simp add: Interpretation_def one_fine_def)

definition "partialwise I = \<F>_fine (defined I)"
lemma partialwise_\<I>[simp]: "\<I> (partialwise I) (Fine x) = { Fine y |y. y \<in> \<I> I x }"
  unfolding partialwise_def by auto
*)

subsubsection \<open>Exact Itself\<close>

definition [simp]: "\<F>_it' x = {x}"
  
definition "\<F>_it = Interp \<F>_it'"

lemma \<F>_it_\<I>[simp]: "\<I> \<F>_it = \<F>_it'"
  unfolding \<F>_it_def
  by (rule Interp_inverse) (simp add: Interpretation_def one_set_def)



subsubsection \<open>Functional Fiction\<close>

definition \<open>\<F>_functional \<psi> = Interp (\<lambda>x. {y. x = \<psi> y})\<close>

lemma (in inj_at_1) \<F>_functional_\<I>[simp]:
  \<open>\<I> (\<F>_functional \<psi>) = (\<lambda>x. {y. x = \<psi> y})\<close>
  unfolding \<F>_functional_def
  by (rule Interp_inverse, simp add: Interpretation_def one_set_def set_eq_iff inj_at_1)

lemma map_option_inj_at_1[simp]:
  \<open>inj_at_1 (map_option f)\<close>
  unfolding one_option_def inj_at_1_def
  by (simp add: split_option_all)


definition "\<F>_share s = (case s of Share w v \<Rightarrow> if w = 1 then {v} else {})"

lemma \<F>_share_\<I>[simp]: "\<F>_share (Share w v) = (if w = 1 then {v} else {})"
  unfolding \<F>_share_def by simp

(* lemma In_ficion_fine [simp]:
  \<open>x \<in> (case some_fine of Fine y \<Rightarrow> f y | Undef \<Rightarrow> {})
        \<longleftrightarrow> (\<exists>y. some_fine = Fine y \<and> x \<in> f y)\<close>
  by (cases some_fine; simp)
*)

subsubsection \<open>Agreement\<close>

definition \<open>\<F>_agree = (\<lambda>x. case x of agree x' \<Rightarrow> {x'})\<close>



end