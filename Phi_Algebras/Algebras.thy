theory Algebras
  imports Phi_Spec_Pre HOL.Rat
    "Phi_Document.Base" "HOL-Library.Product_Plus"
    "HOL-Library.Finite_Map"
begin

setup \<open>
   Attrib.setup \<^binding>\<open>locale_intro\<close> (Scan.succeed Locale.intro_add) ""
#> Attrib.setup \<^binding>\<open>locale_witness\<close> (Scan.succeed Locale.witness_add) ""
\<close> (*TODO: move this*)

(*TODO: do not add \<open>locale_intro\<close> everywhere, the performance of locale_intro_tactic is bad.
  They do not use an indexing structure. The Locale package of Isabelle is not that good. *)

section \<open>Algebra Structures\<close>

subsection \<open>Preliminary Structures\<close>

subsubsection \<open>Homomorphism-like\<close>

locale homo_one =
  fixes \<psi> :: " 'a::one \<Rightarrow> 'b::one "
  assumes homo_one[iff]: "\<psi> 1 = 1"
begin

declare homo_one_axioms[simp]

end

locale simple_homo_mul =
  fixes \<psi> :: \<open> 'a::one \<Rightarrow> 'b::one \<close>
    and D :: \<open> 'a set \<close> \<comment> \<open>The domain is still required. For example, consider the homomorphism
                            from mult-element algebra to single element algebra,
                            the homomorphism cannot be simple unless the domain of the homomorphism
                            is limited to {1}.\<close>
  assumes kernel_is_1[iff]: \<open>x \<in> D \<Longrightarrow> \<psi> x = 1 \<longleftrightarrow> x = 1\<close>
      and simple_homo_mul_dom[simp]: \<open>1 \<in> D\<close>
begin

sublocale homo_one by (standard; simp)

end

lemma simple_homo_mul_sub_dom:
  \<open> D' \<subseteq> D \<and> 1 \<in> D'
\<Longrightarrow> simple_homo_mul \<psi> D
\<Longrightarrow> simple_homo_mul \<psi> D' \<close>
  unfolding simple_homo_mul_def
  by clarsimp blast

locale homo_zero =
  fixes \<phi> :: \<open> 'a::zero \<Rightarrow> 'b::zero \<close>
  assumes homo_zero[iff]: \<open>\<phi> 0 = 0\<close>

locale homo_mult =
  fixes \<phi> :: " 'a::times \<Rightarrow> 'b::times "
  assumes homo_mult: "\<phi> (x * y) = \<phi> x * \<phi> y"

(*lemma homo_mult:
  \<open>homo_mult \<phi> \<longleftrightarrow> (\<phi> 1 = 1) \<and> (\<forall> x y. \<phi> (x * y) = \<phi> x * \<phi> y)\<close>
  unfolding homo_mult_def homo_mult_axioms_def homo_one_def .. *)

(*
locale mult_strip_011 = \<comment> \<open>it is an orthogonal property\<close>
  fixes \<psi> :: " 'a::times \<Rightarrow> 'b::times "
  assumes mult_strip_011: \<open>a * \<psi> b = \<psi> c \<longleftrightarrow> (\<exists>a'. a = \<psi> a' \<and> a' * b = c)\<close>
*)

locale homo_add =
  fixes \<phi> :: \<open> 'a::plus \<Rightarrow> 'b::plus \<close>
  assumes homo_add: \<open>\<phi> (x + y) = \<phi> x + \<phi> y\<close>


subsubsection \<open>Group-like\<close>

class mult_1 = times + one +
  assumes mult_1_left [simp]: "1 * x = x"
      and mult_1_right[simp]: "x * 1 = x"

subclass (in monoid_mult) mult_1
  by (standard; simp)

(* TODO
class add_left_neutral = plus +
  fixes left_neutral_0 :: \<open>'a \<Rightarrow> 'a\<close> ("\<zero>\<^sub>L")
  assumes \<open>\<zero>\<^sub>L x + x = x\<close>*)

class add_0 = plus + zero +
  assumes add_0_add_0_left [simp]: \<open>0 + x = x\<close>
      and add_0_add_0_right[simp]: \<open>x + 0 = x\<close>

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

class add_order_0 = ord + zero + plus +
  assumes add_nonneg_nonneg: \<open>0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a + b\<close>
      and add_pos_pos: \<open>0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a + b\<close>

subclass (in ordered_comm_monoid_add) add_order_0
  by (standard; simp add: add_nonneg_nonneg add_pos_pos)

subsection \<open>Separation Algebras\<close>

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
  where \<open>join_sub y z \<longleftrightarrow> (\<exists>x. z = y * x \<and> y ## x)\<close>
end

class sep_cancel = sep_magma +
  assumes sep_cancel: \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> c * a = c * b \<Longrightarrow> a = b\<close>

class positive_sep_magma = sep_magma +
  assumes join_positivity: \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>

class strict_positive_sep_magma = sep_magma +
  assumes join_strict_positivity: \<open>a ## b \<Longrightarrow> a = a * b \<Longrightarrow> False\<close>

text \<open>Usually, we extend the carrier set of the partial algebra to the total universe by
  importing the outside elements with no defined multiplication on them (except that to
  identity element and zero). It works in most cases
  but an exception is in semimodule structures where a notion of carrier set is required, so we
  give this below.\<close>

class mul_carrier =
  fixes mul_carrier :: \<open>'a \<Rightarrow> bool\<close>

(*
class extended_partial_mul_algebra = mul_carrier + sep_disj +
  \<comment> \<open>characterizes the partial algebras extended to the universe carrier set\<close>
  assumes sep_disj_gives_carrier: \<open>a ## b \<Longrightarrow> mul_carrier a \<and> mul_carrier b\<close>
*)

class sep_carrier = mul_carrier + sep_magma +
  assumes mul_carrier_closed: \<open> \<lbrakk> mul_carrier a; mul_carrier b; a ## b \<rbrakk> \<Longrightarrow> mul_carrier (a * b) \<close>

class sep_refl = sep_magma +
  assumes sep_refl_mult_I: \<open>a ## b \<Longrightarrow> a ## a \<Longrightarrow> b ## b \<Longrightarrow> a * b ## a * b\<close>
  \<comment> \<open>Sometimes, \<open>x ## x\<close> can be used to represent if \<open>x\<close> is in the carrier set,
      recall the sep algebras as partial algebras are implicitly extended to the whole universe
      and leaving the elements out the carrier having no defined group operation. \<close>

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

lemma join_sub_antisym: \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> False\<close>
  for x :: \<open>'a :: {sep_semigroup, strict_positive_sep_magma}\<close>
  unfolding join_sub_def apply clarsimp
  using join_positivity join_strict_positivity join_sub_def by blast

class sep_ab_semigroup = sep_semigroup + comm_sep_disj +
  assumes sep_mult_commute: "x ## y \<Longrightarrow> x * y = y * x"
begin

lemma self_sep_disj:
  \<open>x ## y \<Longrightarrow> x * y ## x * y \<Longrightarrow> x ## x\<close>
  \<open>x ## y \<Longrightarrow> x * y ## x * y \<Longrightarrow> y ## y\<close>
  using local.sep_disj_commute local.sep_disj_multD1 sep_disj_multD2 by blast+

end

class sep_disj_distrib = sep_magma +
  assumes sep_disj_distrib_right[simp]: \<open>b ## c \<Longrightarrow> a ## b * c \<longleftrightarrow> a ## b \<and> a ## c\<close>
  assumes sep_disj_distrib_left [simp]: \<open>a ## b \<Longrightarrow> a * b ## c \<longleftrightarrow> a ## c \<and> b ## c\<close>

subsubsection \<open>Unital Separation\<close>

class sep_magma_1 = sep_magma + mult_1 +
  assumes sep_magma_1_left  [simp]: "x ## 1"
  assumes sep_magma_1_right [simp]: "1 ## x"

class sep_magma_0 = sep_magma_1 + mult_zero + zero_neq_one +
  assumes sep_magma_0_left  [simp]: "x ## 0 \<longleftrightarrow> x = 1"
  assumes sep_magma_0_right [simp]: "0 ## x \<longleftrightarrow> x = 1"

class sep_carrier_1 = sep_carrier + sep_magma_1 +
  assumes sep_carrier_1[simp]: \<open>mul_carrier 1\<close>

class sep_carrier_0 = sep_carrier + sep_magma_0 +
  assumes sep_carrier_0[simp]: \<open>mul_carrier 0\<close>

class sep_no_inverse = sep_magma_1 +
  assumes sep_no_inverse[simp]: \<open>x ## y \<Longrightarrow> x * y = 1 \<longleftrightarrow> x = 1 \<and> y = 1\<close>

class positive_sep_magma_1 = sep_magma_1 + positive_sep_magma
begin
subclass sep_no_inverse
  by (standard, metis local.join_positivity local.join_sub_def local.mult_1_left local.sep_magma_1_right)
end

subsubsection \<open>Separation Monoid\<close>

class sep_monoid = sep_magma_1 + sep_semigroup
begin
subclass positive_sep_magma_1 ..
end

definition (in times) subsume (infix "\<preceq>\<^sub>\<times>" 50)
  where \<open>subsume y z \<longleftrightarrow> (\<exists>x. z = y * x)\<close>

class positive_mult = times +
  assumes positive_mult: \<open>x \<preceq>\<^sub>\<times> y \<Longrightarrow> y \<preceq>\<^sub>\<times> x \<Longrightarrow> x = y\<close>

class positive_mult_one = positive_mult + mult_1
begin
subclass no_inverse by (standard, metis local.mult_1_left local.positive_mult times.subsume_def)
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

lemma join_sub_frame_left:
  \<open>r ## y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> r * x \<preceq>\<^sub>S\<^sub>L r * y\<close>
  unfolding join_sub_def
  by(clarsimp, metis local.sep_disj_multD1 local.sep_disj_multI1 local.sep_mult_assoc)

lemma join_sub_frame_right:
  \<open>r ## y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> r * x \<preceq>\<^sub>S\<^sub>L r * y\<close>
  unfolding join_sub_def
  by(clarsimp, metis local.sep_disj_multD1 local.sep_disj_multI1 local.sep_mult_assoc)

(*lemma
  \<open>r ## y \<Longrightarrow> r ## x \<Longrightarrow> r * x \<preceq>\<^sub>S\<^sub>L r * y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y\<close>
  unfolding join_sub_def apply clarsimp *)

lemma join_sub_ext_left:
  \<open>z ## y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L z * y\<close>
  unfolding join_sub_def
  by (clarsimp, metis local.sep_disj_commuteI local.sep_disj_multI1 local.sep_mult_commute)

lemma join_sub_ext_right:
  \<open>y ## z \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L y * z\<close>
  unfolding join_sub_def
  by (clarsimp, metis local.sep_disj_commute local.sep_disj_multD1 local.sep_disj_multI1 local.sep_mult_assoc local.sep_mult_commute)

end

subsubsection \<open>Special Separation Algebras\<close>

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

class discrete_semigroup = sep_disj + times +
  assumes discrete_disj[simp]: "\<not> x ## y"
begin
subclass sep_magma .
subclass sep_ab_semigroup by (standard; simp add: local.join_sub_def)
subclass sep_cancel by (standard; simp)
subclass strict_positive_sep_magma by (standard; simp)
end

class discrete_monoid = sep_disj + mult_1 +
  assumes discrete_disj_1[simp]: \<open>x ## y \<longleftrightarrow> x = 1 \<or> y = 1\<close>
begin
subclass sep_magma .
subclass sep_algebra proof
  fix x y z :: 'a
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by fastforce
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close>
    by (metis local.mult_1_right local.discrete_disj_1)
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close>
    by (metis local.mult_1_left local.discrete_disj_1)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def by (clarsimp, metis local.mult_1_right)
  show \<open>x ## 1\<close> by simp
  show \<open>1 ## x\<close> by simp
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close>
    by (metis local.mult_1_left local.discrete_disj_1)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close>
    by (metis local.mult_1_right local.discrete_disj_1)
  show \<open>x ## y \<Longrightarrow> y ## x\<close>
    using local.discrete_disj_1 by blast
  show \<open>x ## y \<Longrightarrow> x * y ## z \<Longrightarrow> x * y * z = x * (y * z)\<close> by force
qed
end



subsubsection \<open>Strict Subsumption\<close>

definition join_sub_strict :: \<open>'a::sep_magma \<Rightarrow> 'a::sep_magma \<Rightarrow> bool\<close> (infix "\<prec>\<^sub>S\<^sub>L" 50)
  where \<open>join_sub_strict y z \<longleftrightarrow> join_sub y z \<and> y \<noteq> z\<close>


interpretation join_sub: order \<open>join_sub::'a::sep_monoid \<Rightarrow> 'a \<Rightarrow> bool\<close> join_sub_strict
proof
  fix x y z :: 'a
  show \<open>(x \<prec>\<^sub>S\<^sub>L y) = (x \<preceq>\<^sub>S\<^sub>L y \<and> \<not> y \<preceq>\<^sub>S\<^sub>L x)\<close>
    using join_positivity join_sub_strict_def by blast
  show \<open>x \<preceq>\<^sub>S\<^sub>L x\<close>
    unfolding join_sub_strict_def join_sub_def
    by (rule exI[where x=1], simp)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L z \<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L z\<close>
    unfolding join_sub_strict_def join_sub_def
    using sep_disj_multI2 sep_mult_assoc by blast
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_strict_def join_sub_def
    using join_positivity join_sub_def by blast
qed

interpretation join_sub: order_bot 1 \<open>join_sub::'a::sep_monoid \<Rightarrow> 'a \<Rightarrow> bool\<close> join_sub_strict
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

(*It is nothing but just a semimodule, or even not, just containing scalar associativity
  and separation homo*)

(*locale hierarchical_alg =
  fixes locate :: \<open>'path::monoid_mult \<Rightarrow> 'a::sep_algebra \<Rightarrow> 'a\<close> (infixr ":\<tribullet>" 75)
  assumes locate_distrib_right: \<open>path :\<tribullet> (x * y) = path :\<tribullet> x * path :\<tribullet> y\<close>
    and   locate_assoc: \<open>pa :\<tribullet> pb :\<tribullet> x = (pa * pb) :\<tribullet> x\<close>
    and   locate_left_1:  \<open>1 :\<tribullet> x = x\<close>
    and   locate_right_1: \<open>path :\<tribullet> 1 = 1\<close>*)

text \<open>As an example, a structure \<open>struct { struct {A a; B b} c; D d; }\<close> may be represented by
\<open>c :\<tribullet> (a :\<tribullet> va * b :\<tribullet> vb) * d :\<tribullet> vd\<close>. \<close>


subsection \<open>Permission Algebra\<close>

text \<open>An algebra for objects that can be partially owned, and shared.

The range of the ownership is [0,\<infinity>). Albeit the total permission is 1, the permission can be
greater than 1.
This relaxation eases various things.
We do not need to check the permission does not exceed 1 when merge two permissions.
The share (division by 2) and the merge are then free of side conditions.
In the hierarchical algebra, the permission of a leaf can be greater than 1 when the permission
of the node is less than 1, e.g. \<open>0.5 \<odiv> node_a :\<tribullet> (leaf_a :\<tribullet> 2 \<odiv> a * leaf_b 1 \<odiv> a ) \<close> which actually means
\<open>node_a :\<tribullet> (leaf_a :\<tribullet> 1 \<odiv> a * leaf_b :\<tribullet> 0.5 \<odiv> a )\<close>.
This helps the localized reasoning that focuses on the \<open>node_a\<close> by allowing disregarding to the
environmental permission totally.

TODO: limited by automation, the ownership of an object is represented by \<^typ>\<open>rat\<close>
which includes negative rationals.
It is rather cumbersome cuz assertions have to again and again assert the permission is greater than
(or equal to) 0.
A better choice is using non-negative rationals only, like the type \<open>posrat\<close>, see comments in
Phi-Preliminary.\<close>

class raw_share =
  fixes share :: \<open>rat \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr "\<odivr>" 75)
    \<comment> \<open>\<open>n \<odivr> a\<close> divides \<open>a\<close> into \<open>n\<close> proportion of the original share, for \<open>0 < n < 1\<close>\<close>

class share = raw_share + \<comment> \<open>share algebra for semigroup, where unit \<open>1\<close> is not defined\<close>
  assumes share_share_assoc0: \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n (share m x) = share (n * m) x\<close>
    and   share_left_one[simp]:  \<open>share 1 x = x\<close>

class share_one = share + one +
  assumes share_right_one[simp]: \<open>share n 1 = 1\<close>
    and   share_left_0[simp]:    \<open>share 0 x = 1\<close>
begin
lemma share_share: \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> share n (share m x) = share (n * m) x\<close>
  using less_eq_rat_def local.share_share_assoc0 by fastforce
end

class share_one_eq_one_iff = share_one +
  assumes share_one_eq_one_iff[simp]: \<open>0 < n \<Longrightarrow> share n x = 1 \<longleftrightarrow> x = 1\<close>

class share_carrier = sep_carrier + share +
  assumes share_carrier_closed: \<open>0 < n \<Longrightarrow> mul_carrier x \<Longrightarrow> mul_carrier (share n x)\<close>

class share_carrier_1 = sep_carrier_1 + share_one +
  assumes share_carrier_closed_1: \<open>0 \<le> n \<Longrightarrow> mul_carrier x \<Longrightarrow> mul_carrier (share n x)\<close>
begin
subclass share_carrier by (standard; simp add: share_carrier_closed_1)
end

class share_inj = raw_share +
  assumes share_inj[simp]: \<open>0 < n \<Longrightarrow> share n x = share n y \<longleftrightarrow> x = y\<close>
begin

lemma share_inj': \<open>0 < n \<Longrightarrow> inj (share n)\<close>
  unfolding inj_def
  by clarsimp

end

class share_sep_disj = share + comm_sep_disj + sep_carrier +
  assumes share_sep_disj_left[simp]: \<open>0 < n \<Longrightarrow> share n x ## y \<longleftrightarrow> x ## y\<close>
          \<comment> \<open>the share operation is independent with sep_disj. The multiplication defined between
              two elements are also defined on their shared portions. \<close>
      and share_disj_sdistr: \<open> mul_carrier x \<Longrightarrow> x ## x\<close>
          \<comment> \<open>The original form of the condition is,
                  \<open>\<lbrakk> n < 0 ; m < 0 ; mul_carrier x \<rbrakk> \<Longrightarrow> share n x ## share m x\<close>
              any element in the algebra can be divided into any portions.
              By simplifying using share_sep_disj_left, we get the form above.\<close>
begin

lemma share_sep_disj_right[simp]:
        \<open>0 < n \<Longrightarrow> y ## share n x \<longleftrightarrow> y ## x\<close>
  using local.share_sep_disj_left sep_disj_commute by force

end

class share_nun_semimodule = share_sep_disj + sep_ab_semigroup + share_carrier +
      \<comment>\<open>nun stands for non-unital\<close>
  assumes share_sep_left_distrib_0:  \<open> \<lbrakk> 0 < n ; 0 < m ; mul_carrier x \<rbrakk> \<Longrightarrow> share n x * share m x = share (n+m) x\<close>
    and   share_sep_right_distrib_0: \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    and   share_sub_0: \<open>0 < n \<and> n < 1 \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close>

class share_semimodule = share_sep_disj + share_one + sep_algebra + share_carrier_1 +
  assumes share_sep_left_distrib:  \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x * share m x = share (n+m) x\<close>
    and   share_sep_right_distrib: \<open>0 \<le> n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    and   share_sub: \<open>0 \<le> n \<and> n \<le> 1 \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x\<close>
begin

subclass share_nun_semimodule proof
  fix x y :: 'a
  fix n m :: rat
  show \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x * share m x = share (n + m) x\<close>
    by (meson local.share_sep_left_distrib order_less_le)
  show \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    using local.share_sep_right_distrib order_less_imp_le by blast
  show \<open>0 < n \<and> n < 1 \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close>
    by (simp add: local.share_sub)
qed

end

subsubsection \<open>Derivatives\<close>

class share_resistence_nun = raw_share +
  assumes share_resistence_nun[simp]: \<open>share n x = x\<close>
begin
subclass share by (standard; simp)
end

class share_resistence = raw_share + one +
  assumes share_resistence[simp]: \<open>share n x = (if n = 0 then 1 else x)\<close>
begin
subclass share by (standard; simp)
end


subsection \<open>Homomorphisms\<close>

locale homo_mul_carrier =
  fixes \<psi> :: \<open>'a::mul_carrier \<Rightarrow> 'b::mul_carrier\<close>
  assumes homo_mul_carrier: \<open>mul_carrier x \<Longrightarrow> mul_carrier (\<psi> x)\<close>

locale homo_sep_disj =
  fixes \<psi> :: \<open>'a::sep_disj \<Rightarrow> 'b::sep_disj\<close>
  assumes sep_disj_homo_semi[simp]: \<open>a ## b \<longrightarrow> \<psi> a ## \<psi> b\<close>

locale closed_homo_sep_disj =
  fixes \<psi> :: \<open>'a::sep_disj \<Rightarrow> 'b::sep_disj\<close>
  assumes sep_disj_homo[iff]: \<open>\<psi> a ## \<psi> b \<longleftrightarrow> a ## b\<close>
begin
sublocale homo_sep_disj by standard simp
end

locale homo_sep_mult =
  fixes \<psi> :: " 'a::sep_magma \<Rightarrow> 'b::sep_magma "
  assumes homo_mult: "x ## y \<Longrightarrow> \<psi> (x * y) = \<psi> x * \<psi> y"

locale homo_join_sub =
  fixes \<psi> :: \<open>'a::sep_magma \<Rightarrow> 'b::sep_magma\<close>
    and D :: \<open>'a set\<close>
  assumes homo_join_sub: \<open>x \<in> D \<and> y \<in> D \<Longrightarrow> \<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> y \<longleftrightarrow> x \<preceq>\<^sub>S\<^sub>L y\<close>

locale homo_sep = homo_sep_mult \<psi> + homo_sep_disj \<psi>
  for \<psi> :: \<open>'a::sep_magma \<Rightarrow> 'b::sep_magma\<close>
  \<comment> \<open>Non-closed (weak) homomorphism. This is the standard homomorphism in partial algebras. []\<close>

text \<open>
  Note a non-closed homomorphism only requires the right-half entailment of the separation disjunction
  (\<open>x ## y \<longrightarrow> \<psi> x ## \<psi> y\<close>, it is an implication instead of an equation).

  It provides more flexibility where the target algebra \<open>\<BB>\<close>
  can define more behaviors between the projected elements of the source algebra \<open>\<A>\<close>.
  As an instance showing the value of the flexibility, we consider
  the embedding into a permission algebra from a discrete unital algebra (where the separation
  between any two elements are undefined unless one of the element is the identity)
  \<open>\<psi> 1 = 1    \<psi> x = Perm(1,x)    where fraction p in Perm(p,x) is the permission, and 1 is the total permission\<close>
  it requires this flexibility if we allow super-permission in our formalization.
  Note the permission algebra supports scalar operation, \<open>c \<cdot> Perm(p,x) = Perm(c\<cdot>p, x)\<close>, a permission
  can be temporarily larger than 1 inside the inner operation of a scalar expression, only if after
  the scalar operation, the permission is less or equal than 1.
  It means \<open>Perm(1,x) * Perm(1,x) = Prem(2,x)\<close> is defined, and if the insertion requires bi-direction
  homomorphism of the separation disjunction, from it we have \<open>x * x\<close> is defined, which is contrast
  with the discrete source algebra.
  The bi-direction homomorphism is allowed only if we prohibit super-permission, but it destroys the
  semimodule property of the permission algebra.
  The super-permission frees us from checking the overflow of the permission addition and makes
  the expressiveness more flexible.

  (Unclosed separation homomorphism does not represent any problem in this case,
   because the domain domain of the embedding is usually structures of memory objects,
   of which the domainoid is usually determined, and therefore of which the separation disjunction can be
   decided.)

  By contrast, if the homomorphism is not assumed to be closed, i.e., from \<open>\<psi> x ## \<psi> y\<close> we cannot have \<open>x ## y\<close>,
  we can only have one side transformation \<open>\<psi> (x * y) \<longrightarrow> \<psi> x * \<psi> y\<close> but not the other side
  \<open>\<psi> x * \<psi> y \<longrightarrow> \<psi> (x * y)\<close> because we don't know if \<open>x ## y\<close>.
  This side of transformation is still important and necessary.

  There is no alternative way to the flexibility including super-permission, but the separatablity
  can be checked automatically and in most cases, the separatablity between
  two \<phi>-types \<open>x : T\<close> and \<open>y : U\<close> can be inferred from the types \<open>T\<close> and \<open>U\<close>. A type usually
  records which part of the resource does this \<phi>-type assertion specifies (otherwise, it is impossible
  to reason the transformation that extracts a certain part of the resource which is used locally by
  a subroutine, note the reasoning is type-guided).
  From this domain of specification, we can check the separatablity by checking the domains are disjoint.

  The reasoning procedure is given by \<open>\<phi>Sep_Disj\<close> later.
\<close>

locale closed_homo_sep = homo_sep + closed_homo_sep_disj

locale homo_share =
  fixes \<psi> :: " 'a::raw_share \<Rightarrow> 'b::raw_share "
  assumes share_homo: \<open>\<psi> (n \<odivr> x) = n \<odivr> (\<psi> x)\<close>


subsubsection \<open>Orthogonal Homomorphism\<close>

text \<open>
The property specifies the homomorphism is right-orthogonal to every group action.
See https://math.stackexchange.com/questions/4748364

This property essentially says we put something into another big container where the 'factors' of
the original things are independent with other stuffs, e.g. this sort of resource has no
interference with other sorts, so they are orthogonal.
\<close>

locale sep_orthogonal = homo_sep \<psi>
  for \<psi> :: \<open>'a::sep_magma \<Rightarrow> 'b::sep_magma\<close>
  and D :: \<open>'a set\<close> \<comment> \<open>carrier set of the source algebra,
            Previously we implicitly extend the carrier set to be the universe of the type.
            It can be done because for any element \<open>d\<close> not belonging to the carrier set,
            only if \<open>d\<close> has no defined operation with any element including itself,
            the introduction of \<open>d\<close> doesn't affect anything.
            However here, if \<open>a = \<psi> d\<close> accidentally belongs to the target algebra, \<open>d\<close> matters,
            so we must give the carrier set explicitly to exclude such \<open>d\<close>.\<close>
        \<comment> \<open>It is a bad idea to reuse \<open>mul_carrier\<close> to replace \<open>D\<close> here. \<open>sep_orthogonal\<close> is mainly
            used in fictional SL where the actual domain can be various and even for example dependent
            on the key of the map (e.g., later in the memory model of C, the domain of each block
            depends on the type of the block which is acquired from the key of the map modelling
            the memory). \<open>mul_carrier\<close> is fixed to its logic type can never be so flexible.
            \<open>mul_carrier\<close> is designed for simplifying the specification of separation semimodules.
            Properties of separation semimodules are bound to the type, by means of type classes,
            so it is okay to again use a type class to bind the carrier set to the types.\<close>
+ assumes sep_orthogonal: \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> \<psi> b * a = \<psi> c \<longleftrightarrow> (\<exists>a'. a = \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
begin


lemma sep_orthogonal'[no_atp]:
  \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> \<psi> c = \<psi> b * a \<longleftrightarrow> (\<exists>a'. a = \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
  by (metis sep_orthogonal)

sublocale homo_join_sub \<psi>
  apply standard
  unfolding join_sub_def
  by (metis homo_mult sep_disj_homo_semi sep_orthogonal)

text \<open>The weak homomorphism of \<open>\<preceq>\<^sub>S\<^sub>L\<close>, \<open>x \<preceq>\<^sub>S\<^sub>L z \<longrightarrow> \<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> z\<close> is trivially true but the reversed
so-called closed homo \<open>\<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> z \<longrightarrow> x \<preceq>\<^sub>S\<^sub>L z\<close> is not seen even in closed separation homo.

\<open>\<psi> x \<preceq>\<^sub>S\<^sub>L \<psi> z \<longrightarrow> x \<preceq>\<^sub>S\<^sub>L z  \<Longleftrightarrow>  \<forall>y'. \<psi> z = y' * \<psi> x \<longrightarrow> \<exists>y. z = y * x\<close>
can be unfolded to a form really similar (but weaker) to the orthogonal homo
(the only difference is it doesn't require \<open>y' = \<psi> y\<close>). So orthogonal homo entails the closed homo
of join_sub, but not reversely.\<close>

end

locale sep_orthogonal_1 = sep_orthogonal \<psi> D
  for \<psi> :: \<open>'a::sep_magma_1 \<Rightarrow> 'b::sep_magma_1\<close> and D
+ assumes one_in_D: \<open>1 \<in> D\<close>
begin

sublocale homo_one \<psi>
  by (standard, metis mult_1_class.mult_1_left mult_1_class.mult_1_right one_in_D sep_magma_1_left sep_orthogonal)

end



locale sep_orthogonal_monoid = sep_orthogonal_1 \<psi> D
  for \<psi> :: \<open>'a::sep_monoid \<Rightarrow> 'b::sep_monoid\<close> and D
begin

lemma simple_homo_mul[simp]:
  \<open>simple_homo_mul \<psi> D\<close>
  unfolding simple_homo_mul_def
  by (metis homo_join_sub homo_one join_sub.bot.extremum join_sub.bot.extremum_uniqueI one_in_D)

end

locale cancl_sep_orthogonal_monoid = sep_orthogonal_monoid \<psi> D
  for \<psi> :: \<open>'a::{sep_cancel, sep_monoid} \<Rightarrow> 'b::sep_monoid\<close> and D

locale share_orthogonal_homo = sep_orthogonal_monoid \<psi> D
  for \<psi> :: \<open>'a::sep_algebra \<Rightarrow> 'b::share_semimodule\<close> and D
+ assumes share_orthogonal: \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
                           share n (\<psi> b) * a = \<psi> c \<longleftrightarrow> (\<exists>a'. a = share (1-n) (\<psi> b) * \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
    and   share_bounded: \<open>\<lbrakk> b \<in> D \<and> c \<in> D ; \<psi> b ## a ; n > 1 ; \<psi> b \<noteq> 1 \<rbrakk> \<Longrightarrow> share n (\<psi> b) * a \<noteq> \<psi> c\<close>
    and   \<psi>_mul_carrier: \<open>x \<in> D \<Longrightarrow> mul_carrier (\<psi> x) \<close>
begin

lemma share_orthogonal'[no_atp]:
  \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
      \<psi> c = share n (\<psi> b) * a \<longleftrightarrow> (\<exists>a'. a = share (1-n) (\<psi> b) * \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
  by (metis share_orthogonal)

lemma
  join_sub_share_join_sub_whole: \<open>0 < n \<and> n \<le> 1 \<Longrightarrow> x \<in> D \<and> y \<in> D \<Longrightarrow> share n (\<psi> x) \<preceq>\<^sub>S\<^sub>L \<psi> y \<longleftrightarrow> x \<preceq>\<^sub>S\<^sub>L y\<close>
  unfolding join_sub_def
  by ((rule; clarsimp simp add: homo_mult),
      metis share_orthogonal,
      meson \<psi>_mul_carrier join_sub_def join_sub_ext_right less_eq_rat_def sep_disj_homo_semi share_sep_disj_left share_sub)
  

(* lemma \<open>0 < n \<and> n \<le> 1 \<Longrightarrow> share n (\<psi> x) \<preceq>\<^sub>S\<^sub>L \<psi> x\<close>
  by (simp add: \<psi>_mul_carrier share_sub) *)

end

(*
locale share_orthogonal_homo_L =
  fixes \<psi> :: \<open>'a::sep_algebra \<Rightarrow> 'b::share_semimodule\<close>
  assumes share_orthogonal_homo': \<open>id share_orthogonal_homo \<psi>\<close>
begin
sublocale share_orthogonal_homo using share_orthogonal_homo'[simplified] .
end *)


locale cancl_share_orthogonal_homo = share_orthogonal_homo \<psi> D
  for \<psi> :: \<open>'a::{sep_cancel, sep_algebra} \<Rightarrow> 'b::share_semimodule\<close> and D
begin

sublocale cancl_sep_orthogonal_monoid ..

end


subsubsection \<open>With Discrete Algebra\<close>

lemma homo_sep_disj_discrete[simp]:
  \<open>homo_sep_disj \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_semigroup \<Rightarrow> 'b::sep_disj\<close>
  unfolding homo_sep_disj_def
  by simp

lemma homo_sep_disj_discrete_1[simp]:
  \<open> homo_one \<psi>
\<Longrightarrow> homo_sep_disj \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_monoid \<Rightarrow> 'b::sep_magma_1\<close>
  unfolding homo_sep_disj_def homo_one_def
  by simp

lemma closed_homo_sep_disj_discrete[simp]:
  \<open>closed_homo_sep_disj \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_semigroup \<Rightarrow> 'b::discrete_semigroup\<close>
  unfolding closed_homo_sep_disj_def
  by simp

lemma closed_homo_sep_disj_discrete_1[simp]:
  \<open> simple_homo_mul \<psi> UNIV
\<Longrightarrow> closed_homo_sep_disj \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_monoid \<Rightarrow> 'b::discrete_monoid\<close>
  unfolding closed_homo_sep_disj_def simple_homo_mul_def
  by simp

lemma homo_sep_mult_discrete[simp]:
  \<open>homo_sep_mult \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_semigroup \<Rightarrow> 'b::sep_magma\<close>
  unfolding homo_sep_mult_def
  by simp

lemma homo_sep_discrete[simp]:
  \<open>homo_sep \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_semigroup \<Rightarrow> 'b::sep_magma\<close>
  unfolding homo_sep_def
  by simp

lemma closed_homo_sep_discrete[simp]:
  \<open>closed_homo_sep \<psi>\<close>
  for \<psi> :: \<open>'a::discrete_semigroup \<Rightarrow> 'b::discrete_semigroup\<close>
  unfolding closed_homo_sep_def
  by simp


subsection \<open>Partial Additive Structures\<close>

subsubsection \<open>Domain of the Addition\<close>

paragraph \<open>Addition\<close>

class dom_of_add =
  fixes dom_of_add :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix "##\<^sub>+" 60)

class total_dom_of_add = dom_of_add +
  assumes total_dom_of_add[simp]: \<open>x ##\<^sub>+ y\<close>

class comm_dom_of_add = dom_of_add +
  assumes dom_of_add_commuteI: "x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ x"
begin
lemma dom_of_add_commute: "x ##\<^sub>+ y \<longleftrightarrow> y ##\<^sub>+ x"
  by (blast intro: dom_of_add_commuteI)
end

paragraph \<open>Subtraction\<close>

class dom_of_minus =
  fixes dom_of_minus :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix "##\<^sub>-" 60)

class total_dom_of_minus = dom_of_minus +
  assumes total_dom_of_minus[simp]: \<open>x ##\<^sub>- y\<close>


subsubsection \<open>Partial Additive Magma\<close>

class partial_add_magma = dom_of_add + plus
begin

definition additive_join_sub (infix "\<preceq>\<^sub>+" 50)
  where \<open>additive_join_sub y z \<longleftrightarrow> (\<exists>x. z = x + y \<and> x ##\<^sub>+ y)\<close>

end

class partial_add_cancel = partial_add_magma +
  assumes partial_add_cancel: \<open>a ##\<^sub>+ c \<Longrightarrow> b ##\<^sub>+ c \<Longrightarrow> a + c = b + c \<Longrightarrow> a = b\<close>

class positive_partial_add_magma = partial_add_magma +
  assumes additive_join_positivity: \<open>x \<preceq>\<^sub>+ y \<Longrightarrow> y \<preceq>\<^sub>+ x \<Longrightarrow> x = y\<close>

class strict_positive_partial_add_magma = partial_add_magma +
  assumes additive_join_strict_positivity: \<open>b ##\<^sub>+ a \<Longrightarrow> a = b + a \<Longrightarrow> False\<close>


subsubsection \<open>Partial Additive Semigroup\<close>

class partial_semigroup_add = partial_add_magma +
  assumes partial_add_assoc:
    "\<lbrakk> x ##\<^sub>+ y; x + y ##\<^sub>+ z \<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
  assumes partial_add_dom_multD1: "\<lbrakk> x ##\<^sub>+ y + z; y ##\<^sub>+ z \<rbrakk> \<Longrightarrow> x ##\<^sub>+ y"
  assumes partial_add_dom_multI1: "\<lbrakk> x ##\<^sub>+ y + z; y ##\<^sub>+ z \<rbrakk> \<Longrightarrow> x + y ##\<^sub>+ z"
  assumes partial_add_dom_multD2: "\<lbrakk> x + y ##\<^sub>+ z; x ##\<^sub>+ y \<rbrakk> \<Longrightarrow> y ##\<^sub>+ z"
  assumes partial_add_dom_multI2: "\<lbrakk> x + y ##\<^sub>+ z; x ##\<^sub>+ y \<rbrakk> \<Longrightarrow> x ##\<^sub>+ y + z"
begin

lemma partial_add_assoc':
    "\<lbrakk> y ##\<^sub>+ z; x ##\<^sub>+ y + z \<rbrakk> \<Longrightarrow> x + (y + z) = (x + y) + z"
  by (metis local.partial_add_assoc local.partial_add_dom_multD1 local.partial_add_dom_multI1)

end

lemma positive_join_sub_antisym: \<open>x \<preceq>\<^sub>+ y \<Longrightarrow> y \<preceq>\<^sub>+ x \<Longrightarrow> False\<close>
  for x :: \<open>'a :: {partial_semigroup_add, strict_positive_partial_add_magma}\<close>
  unfolding additive_join_sub_def
  by (clarsimp, metis additive_join_strict_positivity partial_add_assoc' partial_add_dom_multI1)

class partial_ab_semigroup_add = partial_semigroup_add + comm_dom_of_add +
  assumes partial_add_commute: "x ##\<^sub>+ y \<Longrightarrow> x + y = y + x"
begin

lemma self_dom_of_add_destruct:
  \<open>x ##\<^sub>+ y \<Longrightarrow> x + y ##\<^sub>+ x + y \<Longrightarrow> x ##\<^sub>+ x\<close>
  \<open>x ##\<^sub>+ y \<Longrightarrow> x + y ##\<^sub>+ x + y \<Longrightarrow> y ##\<^sub>+ y\<close>
  using local.dom_of_add_commute local.partial_add_dom_multD1 apply blast
  using local.dom_of_add_commute local.partial_add_dom_multD2 by blast

end

class dom_of_add_intuitive = partial_add_magma +
  assumes dom_of_add_intuitive_right[simp]: \<open>b ##\<^sub>+ c \<Longrightarrow> a ##\<^sub>+ b + c \<longleftrightarrow> a ##\<^sub>+ b \<and> a ##\<^sub>+ c\<close>
  assumes dom_of_add_intuitive_left [simp]: \<open>a ##\<^sub>+ b \<Longrightarrow> a + b ##\<^sub>+ c \<longleftrightarrow> a ##\<^sub>+ c \<and> b ##\<^sub>+ c\<close>

paragraph \<open>Cancellative\<close>

class partial_cancel_semigroup_add = partial_semigroup_add +
  assumes partial_add_left_imp_eq : "\<lbrakk> a ##\<^sub>+ b; a ##\<^sub>+ c \<rbrakk> \<Longrightarrow> a + b = a + c \<Longrightarrow> b = c"
  assumes partial_add_right_imp_eq: "\<lbrakk> b ##\<^sub>+ a; c ##\<^sub>+ a \<rbrakk> \<Longrightarrow> b + a = c + a \<Longrightarrow> b = c"
begin

lemma partial_add_left_cancel [simp]: "\<lbrakk> a ##\<^sub>+ b ; a ##\<^sub>+ c \<rbrakk> \<Longrightarrow> a + b = a + c \<longleftrightarrow> b = c"
  using local.partial_add_left_imp_eq by blast
  
lemma partial_add_right_cancel [simp]: "\<lbrakk> b ##\<^sub>+ a ; c ##\<^sub>+ a \<rbrakk> \<Longrightarrow> b + a = c + a \<longleftrightarrow> b = c"
  using local.partial_add_right_imp_eq by blast

end

class partial_cancel_ab_semigroup_add = partial_ab_semigroup_add + dom_of_minus + minus +
  assumes partial_add_diff_cancel_left'[simp]: \<open>a ##\<^sub>+ b \<Longrightarrow> (a + b) - a = b\<close>
      and partial_add_diff_cancel_left'_dom: \<open>a ##\<^sub>+ b \<Longrightarrow> (a + b) ##\<^sub>- a\<close>
  assumes partial_diff_diff_add: \<open>b ##\<^sub>+ c \<Longrightarrow> a ##\<^sub>- (b + c) \<Longrightarrow> a - b - c = a - (b + c)\<close>
      and partial_diff_diff_add_dom: \<open>a ##\<^sub>- b \<and> (a - b) ##\<^sub>- c \<longleftrightarrow> b ##\<^sub>+ c \<and> a ##\<^sub>- (b + c)\<close>
begin

lemma partial_add_diff_cancel_right'_dom [simp]:
  \<open>a ##\<^sub>+ b \<Longrightarrow> a + b ##\<^sub>- b\<close>
  by (metis local.dom_of_add_commute local.partial_add_commute local.partial_add_diff_cancel_left'_dom)

lemma partial_add_diff_cancel_right' [simp]:
  "a ##\<^sub>+ b \<Longrightarrow> (a + b) - b = a"
  by (metis local.dom_of_add_commute local.partial_add_commute local.partial_add_diff_cancel_left')

subclass partial_cancel_semigroup_add
  by (standard,
      metis local.partial_add_diff_cancel_left',
      metis partial_add_diff_cancel_right')

lemma partial_add_diff_cancel_left_dom[simp]:
  \<open>\<lbrakk> c ##\<^sub>+ a ; c ##\<^sub>+ b \<rbrakk> \<Longrightarrow> c + a ##\<^sub>- c + b \<longleftrightarrow> a ##\<^sub>- b\<close>
  by (metis local.partial_add_diff_cancel_left' local.partial_add_diff_cancel_left'_dom local.partial_diff_diff_add_dom)

lemma partial_add_diff_cancel_left [simp]:
  "\<lbrakk> c ##\<^sub>+ a ; c ##\<^sub>+ b ; a ##\<^sub>- b \<rbrakk> \<Longrightarrow> (c + a) - (c + b) = a - b"
  by (metis local.partial_add_diff_cancel_left' local.partial_diff_diff_add partial_add_diff_cancel_left_dom)

lemma partial_add_diff_cancel_right_dom [simp]:
  "\<lbrakk> a ##\<^sub>+ c ; b ##\<^sub>+ c \<rbrakk> \<Longrightarrow> a + c ##\<^sub>- b + c = a ##\<^sub>- b"
  by (metis local.dom_of_add_commute local.partial_add_commute partial_add_diff_cancel_left_dom)

lemma add_diff_cancel_right [simp]:
  "\<lbrakk> a ##\<^sub>+ c ; b ##\<^sub>+ c; a ##\<^sub>- b \<rbrakk> \<Longrightarrow> (a + c) - (b + c) = a - b"
  by (metis local.dom_of_add_commute local.partial_add_commute partial_add_diff_cancel_left)


lemma partial_diff_right_commute: "b ##\<^sub>+ c \<Longrightarrow> a ##\<^sub>- (b + c) \<Longrightarrow> a - c - b = a - b - c"
  by (simp add: dom_of_add_commute local.partial_add_commute local.partial_diff_diff_add)

lemma partial_add_implies_diff_dom:
  \<open>c ##\<^sub>+ b \<Longrightarrow> c + b = a \<Longrightarrow> a ##\<^sub>- b\<close>
  by fastforce

lemma partial_add_implies_diff:
  \<open>c ##\<^sub>+ b \<Longrightarrow> c + b = a \<Longrightarrow> c = a - b\<close>
  by fastforce

end

paragraph \<open>ed\<close>

class partial_canonically_ordered_ab_semigroup_add = partial_cancel_semigroup_add + order +
  assumes partial_le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c \<and> a ##\<^sub>+ c)"


subsubsection \<open>Unital Partial Additive Structures\<close>

class partial_add_magma_0 = partial_add_magma + add_0 +
  assumes partial_add_0_left  [simp]: "x ##\<^sub>+ 0"
  assumes partial_add_0_right [simp]: "0 ##\<^sub>+ x"

class partial_add_no_negative = partial_add_magma_0 +
  assumes partial_add_no_negative[simp]: \<open>x ##\<^sub>+ y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0\<close>

class positive_partial_add_magma_0 = partial_add_magma_0 + positive_partial_add_magma
begin
subclass partial_add_no_negative
  by standard (metis add_0_add_0_right local.additive_join_positivity local.additive_join_sub_def local.partial_add_0_left)
end

subsubsection \<open>Partial Additive Monoid\<close>

class partial_add_monoid = partial_add_magma_0 + partial_semigroup_add

(* definition (in plus) additive_subsume (infix "\<preceq>\<^sub>+''" 50)
  where \<open>additive_subsume y z \<longleftrightarrow> (\<exists>x. z = x + y)\<close>

class positive_add = plus +
  assumes positive_add: \<open>x \<preceq>\<^sub>+' y \<Longrightarrow> y \<preceq>\<^sub>+' x \<Longrightarrow> x = y\<close>

class positive_add_0 = positive_add + add_0
begin

subclass no_negative
  by standard  (metis add_0_add_0_right local.positive_add plus.additive_subsume_def)
  
end *)

class total_partial_add_monoid = monoid_add + total_dom_of_add
begin
subclass partial_add_magma .
subclass partial_add_monoid proof
  fix x y z :: 'a
  show \<open>x ##\<^sub>+ 0\<close> by simp
  show \<open>0 ##\<^sub>+ x\<close> by simp
  show \<open>x ##\<^sub>+ y \<Longrightarrow> x + y ##\<^sub>+ z \<Longrightarrow> x + y + z = x + (y + z)\<close>
    by (simp add: add_assoc)
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y\<close> by simp
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x + y ##\<^sub>+ z\<close> by simp
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ z\<close> by simp
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> x ##\<^sub>+ y + z \<close> by simp
  show \<open>0 + x = x\<close> by simp
  show \<open>x + 0 = x\<close> by simp
qed
end

subsubsection \<open>Partial Commutative Addition Monoid\<close>

class partial_add_ab_monoid = partial_add_magma_0 + partial_ab_semigroup_add
begin

subclass partial_add_monoid ..

lemma partial_add_left_commute[simp]:
  "b ##\<^sub>+ (a + c) \<Longrightarrow> a ##\<^sub>+ c \<Longrightarrow> b + (a + c) = a + (b + c)"
  by (metis local.dom_of_add_commuteI local.partial_add_assoc local.partial_add_commute local.partial_add_dom_multD1)

lemma additive_join_sub_frame:
  \<open>r ##\<^sub>+ y \<Longrightarrow> x \<preceq>\<^sub>+ y \<Longrightarrow> r + x \<preceq>\<^sub>+ r + y\<close>
  unfolding additive_join_sub_def
  by (clarsimp, metis local.dom_of_add_commute local.partial_add_commute local.partial_add_dom_multI1)

lemma additive_join_sub_ext_left:
  \<open>z ##\<^sub>+ y \<Longrightarrow> x \<preceq>\<^sub>+ y \<Longrightarrow> x \<preceq>\<^sub>+ z + y\<close>
  unfolding additive_join_sub_def
  using local.partial_add_assoc' local.partial_add_dom_multI1 by auto

lemma additive_join_sub_ext_right:
  \<open>y ##\<^sub>+ z \<Longrightarrow> x \<preceq>\<^sub>+ y \<Longrightarrow> x \<preceq>\<^sub>+ y + z\<close>
  unfolding additive_join_sub_def
  by (metis local.dom_of_add_commute local.partial_add_assoc' local.partial_add_commute local.partial_add_dom_multI1)

end


class total_partial_add_ab_monoid = comm_monoid_add + total_dom_of_add
begin
subclass partial_add_magma .
subclass partial_add_ab_monoid proof
  fix x y z :: 'a
  show \<open>x ##\<^sub>+ 0\<close> by simp
  show \<open>0 ##\<^sub>+ x\<close> by simp
  show \<open>x ##\<^sub>+ y \<Longrightarrow> x + y = y + x\<close> by (simp add: add_commute) 
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x + y ##\<^sub>+ z\<close> by simp
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y\<close> by simp
(*  show \<open>x \<preceq>\<^sub>+ y \<Longrightarrow> y \<preceq>\<^sub>+ x \<Longrightarrow> x = y\<close>
    by (metis local.additive_join_sub_def local.positive_add plus.additive_subsume_def) *)
  show \<open>x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ x\<close> by simp
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ z\<close> by simp
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> x ##\<^sub>+ y + z\<close> by simp
  show \<open>x ##\<^sub>+ y \<Longrightarrow> x + y ##\<^sub>+ z \<Longrightarrow> x + y + z = x + (y + z)\<close> using add_assoc by blast
  show \<open>x + 0 = x\<close> by simp
  show \<open>0 + x = x\<close> by simp
qed
subclass total_partial_add_monoid ..
end

class discrete_partial_semigroup_add = dom_of_add + plus +
  assumes discrete_dom_of_add[simp]: "x ##\<^sub>+ y \<longleftrightarrow> x = y"
    and discrete_add[simp]: "x + y = (if x = y then x else undefined)"
begin
subclass partial_add_magma .
subclass partial_ab_semigroup_add proof
  fix x y z :: 'a
  show \<open>x ##\<^sub>+ y \<Longrightarrow> x + y = y + x\<close> by simp
(*  show \<open>x \<preceq>\<^sub>+ y \<Longrightarrow> y \<preceq>\<^sub>+ x \<Longrightarrow> x = y\<close> unfolding additive_join_sub_def by force *)
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y\<close> by simp
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x + y ##\<^sub>+ z\<close> by simp
  show \<open>x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ x\<close> by simp
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ z\<close> by simp
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> x ##\<^sub>+ y + z\<close> by simp
  show \<open>x ##\<^sub>+ y \<Longrightarrow> x + y ##\<^sub>+ z \<Longrightarrow> x + y + z = x + (y + z)\<close> by simp
  (*show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    using local.join_sub_def by force*)
qed
end

class empty_partial_semigroup_add = dom_of_add + plus +
  assumes empty_dom_of_add[simp]: "\<not> x ##\<^sub>+ y"
begin
subclass partial_add_magma .
subclass partial_ab_semigroup_add by (standard; simp add: additive_join_sub_def)
subclass partial_add_cancel by (standard; simp)
subclass strict_positive_partial_add_magma by (standard; simp)
end

class empty_partial_add_monoid = dom_of_add + add_0 +
  assumes empty_dom_of_add_1[simp]: \<open>x ##\<^sub>+ y \<longleftrightarrow> x = 0 \<or> y = 0\<close>
begin
subclass partial_add_magma .
subclass partial_add_ab_monoid proof
  fix x y z :: 'a
  show \<open>x ##\<^sub>+ y \<Longrightarrow> x + y = y + x\<close> by fastforce
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y\<close>
    using local.empty_dom_of_add_1 by fastforce
  show \<open>x ##\<^sub>+ y + z \<Longrightarrow> y ##\<^sub>+ z \<Longrightarrow> x + y ##\<^sub>+ z\<close>
    using local.empty_dom_of_add_1 by fastforce
(*  show \<open>x \<preceq>\<^sub>+ y \<Longrightarrow> y \<preceq>\<^sub>+ x \<Longrightarrow> x = y\<close>
    unfolding additive_join_sub_def by (clarsimp, metis add_0_add_0_left) *)
  show \<open>x ##\<^sub>+ 0\<close> by simp
  show \<open>0 ##\<^sub>+ x\<close> by simp
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ z\<close>
    by (metis add_0_add_0_left local.empty_dom_of_add_1)
  show \<open>x + y ##\<^sub>+ z \<Longrightarrow> x ##\<^sub>+ y \<Longrightarrow> x ##\<^sub>+ y + z\<close>
    using local.empty_dom_of_add_1 by fastforce
  show \<open>x ##\<^sub>+ y \<Longrightarrow> y ##\<^sub>+ x\<close>
    using local.empty_dom_of_add_1 by blast
  show \<open>x ##\<^sub>+ y \<Longrightarrow> x + y ##\<^sub>+ z \<Longrightarrow> x + y + z = x + (y + z)\<close> by force
qed
end

subsection \<open>Module Structures for Separation\<close>

text \<open>The right distributivity of a module forms a homomorphism over the group operation,
  so we don't cover it here.\<close>

locale module_for_sep =
  fixes smult :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 'a\<close>
    and Ds :: \<open>'s \<Rightarrow> bool\<close> \<comment> \<open>gives the carrier set of the scalars\<close>

text \<open>It seems there is not a standard definition for modules on partial rings.
  In our formalization, we assume the scalar distributivity is available on any elements of the ring.
\<close>

locale module_S_distr = module_for_sep +
  assumes module_scalar_distr: \<open> \<lbrakk> Ds (s::'s::partial_add_magma); Ds t; s ##\<^sub>+ t ; mul_carrier (a :: 'a :: sep_carrier) \<rbrakk>
                             \<Longrightarrow> smult (s + t) a = smult s a * smult t a \<and> smult s a ## smult t a \<close>

locale module_scalar_assoc = module_for_sep +
  assumes module_scalar_assoc: \<open>\<lbrakk> Ds s; Ds t \<rbrakk> \<Longrightarrow> smult s (smult t a) = smult (s * t) a\<close>
  \<comment> \<open>Recall we always follow the order of the associativity.

      Here we do not require \<open>mul_carrier a\<close> in order to get a type equation \<open>F s (F t T) = F (t * s) T\<close>
      that is condition-less about abstract objects.

      For elements outside the carrier set, simply extend the scalar multiplication on them to identity
      function.
\<close>

locale module_scalar_identity = module_for_sep +
  assumes module_scalar_identity: \<open>smult 1 a = a\<close>

locale module_scalar_zero = module_for_sep +
  assumes module_scalar_zero: \<open>smult 0 a = 1\<close>

lemma module_scalar_identity_share[simp]:
  \<open>module_scalar_identity (share :: rat \<Rightarrow> 'a::share \<Rightarrow> 'a)\<close>
  unfolding module_scalar_identity_def
  by simp

lemma module_scalar_zero_share[simp]:
  \<open>module_scalar_zero (share :: rat \<Rightarrow> 'a::share_one \<Rightarrow> 'a)\<close>
  unfolding module_scalar_zero_def
  by simp

lemma module_scalar_assoc_share0[simp]:
  \<open>module_scalar_assoc (share :: rat \<Rightarrow> 'a::share \<Rightarrow> 'a) (\<lambda>n. 0 < n)\<close>
  unfolding module_scalar_assoc_def
  by (simp add: share_share_assoc0)

lemma module_scalar_assoc_share[simp]:
  \<open>module_scalar_assoc (share :: rat \<Rightarrow> 'a::share_one \<Rightarrow> 'a) (\<lambda>n. 0 \<le> n)\<close>
  unfolding module_scalar_assoc_def
  by (simp add: share_share)

instantiation rat :: total_partial_add_ab_monoid
begin
definition dom_of_add_rat :: \<open>rat \<Rightarrow> rat \<Rightarrow> bool\<close> where [iff]: \<open>dom_of_add_rat _ _ \<longleftrightarrow> True\<close>
instance by standard simp
end

lemma module_S_distr_share:
  \<open>module_S_distr (share :: rat \<Rightarrow> 'a::share_semimodule \<Rightarrow> 'a) (\<lambda>n. 0 \<le> n)\<close>
  unfolding module_S_distr_def
  using share_disj_sdistr
  by (auto simp add: less_eq_rat_def share_sep_left_distrib )

lemma module_S_distr_share_0:
  \<open>module_S_distr (share :: rat \<Rightarrow> 'a::share_nun_semimodule \<Rightarrow> 'a) (\<lambda>n. 0 < n)\<close>
  unfolding module_S_distr_def
  using share_disj_sdistr
  by (auto simp add: share_sep_left_distrib_0)



section \<open>Instances of Algebras\<close>

(*TODO: some structures like partial map contain many helper lemmas that
are not settled down properly.*)

subsection \<open>Lambda Identity\<close>

lemma simple_homo_mul_id[simp]:
  \<open>1 \<in> D \<Longrightarrow> simple_homo_mul (\<lambda>x. x) D\<close>
  unfolding simple_homo_mul_def
  by simp

lemma homo_one_id[simp, locale_intro]:
  \<open> homo_one (\<lambda>x. x) \<close>
  unfolding homo_one_def
  by simp

lemma homo_mul_carrier_id[simp, locale_intro]:
  \<open>homo_mul_carrier (\<lambda>x. x)\<close>
  unfolding homo_mul_carrier_def
  by blast

lemma homo_sep_disj_id[simp, locale_intro]:
  \<open>homo_sep_disj (\<lambda>x. x)\<close>
  unfolding homo_sep_disj_def
  by simp

lemma closed_homo_sep_disj_id[simp, locale_intro]:
  \<open> closed_homo_sep_disj (\<lambda>x. x) \<close>
  unfolding closed_homo_sep_disj_def
  by simp

lemma homo_sep_mult_id[simp, locale_intro]:
  \<open> homo_sep_mult (\<lambda>x. x) \<close>
  unfolding homo_sep_mult_def
  by simp

lemma homo_sep_id[simp, locale_intro]:
  \<open>homo_sep (\<lambda>x. x)\<close>
  unfolding homo_sep_def
  by simp

lemma closed_homo_sep_id[simp, locale_intro]:
  \<open> closed_homo_sep (\<lambda>x. x) \<close>
  unfolding closed_homo_sep_def
  by simp

lemma homo_share_id[simp, locale_intro]:
  \<open> homo_share (\<lambda>x. x) \<close>
  unfolding homo_share_def
  by blast

(*
lemma
  \<open> sep_orthogonal (\<lambda>x. x) D \<close>
  unfolding sep_orthogonal_def sep_orthogonal_axioms_def
  by simp *)


subsection \<open>Functional Composition\<close>

text \<open>Most of homomorphic properties have both identity rule and composition rule, forming them a sub-category.\<close>

lemma simple_homo_mul_comp[simp]:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> simple_homo_mul f Df
\<Longrightarrow> simple_homo_mul g Dg
\<Longrightarrow> simple_homo_mul (f o g) Dg\<close>
  unfolding simple_homo_mul_def
  by (simp add: image_subset_iff)

lemma homo_one_comp[simp, locale_intro]:
  \<open> homo_one f
\<Longrightarrow> homo_one g
\<Longrightarrow> homo_one (f o g) \<close>
  unfolding homo_one_def
  by simp

lemma homo_mul_carrier_comp[simp, locale_intro]:
  \<open> homo_mul_carrier g
\<Longrightarrow> homo_mul_carrier f
\<Longrightarrow> homo_mul_carrier (f o g)\<close>
  unfolding homo_mul_carrier_def
  by clarsimp

lemma homo_sep_disj_comp[simp, locale_intro]:
  \<open> homo_sep_disj f
\<Longrightarrow> homo_sep_disj g
\<Longrightarrow> homo_sep_disj (f o g) \<close>
  unfolding homo_sep_disj_def
  by simp

lemma closed_homo_sep_disj_comp[simp, locale_intro]:
  \<open> closed_homo_sep_disj f
\<Longrightarrow> closed_homo_sep_disj g
\<Longrightarrow> closed_homo_sep_disj (f o g)\<close>
  unfolding closed_homo_sep_disj_def
  by simp

lemma homo_sep_mult_comp[simp, locale_intro]:
  \<open> homo_sep_disj f
\<Longrightarrow> homo_sep_mult f
\<Longrightarrow> homo_sep_mult g
\<Longrightarrow> homo_sep_mult (g o f)\<close>
  unfolding homo_sep_mult_def homo_sep_disj_def
  by clarsimp

lemma homo_sep_comp[simp, locale_intro]:
  \<open>homo_sep f \<Longrightarrow> homo_sep g \<Longrightarrow> homo_sep (f o g)\<close>
  unfolding homo_sep_mult_def homo_sep_disj_def homo_sep_def
  by simp

lemma closed_homo_sep_comp[simp, locale_intro]:
  \<open> closed_homo_sep f
\<Longrightarrow> closed_homo_sep g
\<Longrightarrow> closed_homo_sep (f o g)\<close>
  unfolding closed_homo_sep_def
  by simp

lemma homo_share_comp[simp]:
  \<open> homo_share f
\<Longrightarrow> homo_share g
\<Longrightarrow> homo_share (f o g) \<close>
  unfolding homo_share_def
  by clarsimp

lemma sep_orthogonal_comp:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> sep_orthogonal f Df \<Longrightarrow> sep_orthogonal g Dg \<Longrightarrow> sep_orthogonal (f o g) Dg\<close>
  unfolding sep_orthogonal_def sep_orthogonal_axioms_def
  by (clarsimp simp add: homo_sep_comp subset_iff image_iff Bex_def,
      smt (verit, ccfv_threshold) homo_sep.axioms(2) homo_sep_disj.sep_disj_homo_semi)

lemma sep_orthogonal_1_comp:
  \<open> g ` Dg \<subseteq> Df
\<Longrightarrow> sep_orthogonal_1 f Df \<Longrightarrow> sep_orthogonal_1 g Dg \<Longrightarrow> sep_orthogonal_1 (f o g) Dg\<close>
  unfolding sep_orthogonal_1_def
  by (clarsimp simp add: homo_sep_comp subset_iff image_iff Bex_def,
      metis image_subsetI sep_orthogonal_comp)

lemma sep_orthogonal_monoid_comp[locale_intro]:
  \<open> g ` Dg \<subseteq> Df \<Longrightarrow> sep_orthogonal_monoid f Df \<Longrightarrow> sep_orthogonal_monoid g Dg \<Longrightarrow> sep_orthogonal_monoid (f o g) Dg\<close>
  unfolding sep_orthogonal_monoid_def using sep_orthogonal_1_comp .

lemma share_orthogonal_homo_composition[locale_intro]:
  assumes dom_trans: \<open>g ` Dg \<subseteq> Df\<close>
      and f: \<open>share_orthogonal_homo f Df\<close>
      and g: \<open>sep_orthogonal_monoid g Dg\<close>
    shows \<open>share_orthogonal_homo (f o g) Dg\<close>
proof -
  interpret f: share_orthogonal_homo f Df using f .
  interpret g: sep_orthogonal_monoid g Dg using g .
  have f': \<open>sep_orthogonal_monoid f Df\<close> by (simp add: f.sep_orthogonal_monoid_axioms)
  have g': \<open>sep_orthogonal_monoid g Dg\<close> by (simp add: g.sep_orthogonal_monoid_axioms)
  have t[simp]: \<open>x \<in> Dg \<Longrightarrow> g x \<in> Df\<close> for x using dom_trans by blast 

  show ?thesis
    unfolding share_orthogonal_homo_def share_orthogonal_homo_axioms_def
    apply (auto simp add: f.share_orthogonal)
    apply (meson dom_trans f' g' sep_orthogonal_monoid_comp)
    using g.sep_orthogonal apply auto[1]
    using g.homo_mult apply auto[1]
    using f.share_bounded t apply blast
    using f.\<psi>_mul_carrier t by blast 

qed


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

instantiation option :: (plus) plus begin
definition \<open>plus_option x' y' = (case x' of Some x \<Rightarrow> (case y' of Some y \<Rightarrow> Some (x + y) | _ \<Rightarrow> x') | _ \<Rightarrow> y')\<close>

lemma plus_option[simp]:
  \<open>Some x + Some y = Some (x + y)\<close>
  \<open>x' + None = x'\<close>
  \<open>None + x' = x'\<close>
  by (cases x'; simp add: plus_option_def)+

lemma plus_option_not_none[simp]:
  \<open>x + Some y \<noteq> None\<close>
  \<open>Some y + x \<noteq> None\<close>
  by (cases x; simp)+

instance ..
end

instantiation option :: (type) one begin
definition [simp]: "one_option = None"
instance ..
end

instantiation option :: (type) zero begin
definition [simp]: "zero_option = None"
instance ..
end

instantiation option :: (times) mult_1 begin
instance proof
  fix x :: \<open>'a option\<close>
  show \<open>1 * x = x\<close> by (cases x; simp)
  show \<open>x * 1 = x\<close> by (cases x; simp)
qed
end

instantiation option :: (plus) add_0 begin
instance proof
  fix x :: \<open>'a option\<close>
  show \<open>0 + x = x\<close> by (cases x; simp)
  show \<open>x + 0 = x\<close> by (cases x; simp)
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

lemma sep_disj_option_discrete[simp]:
  \<open>x ## Some y \<longleftrightarrow> x = None\<close>
  \<open>Some y ## x \<longleftrightarrow> x = None\<close>
  for y :: \<open>'a :: discrete_semigroup\<close>
  by (cases x; simp)+

instantiation option :: (comm_sep_disj) comm_sep_disj begin
instance apply (standard; case_tac x; case_tac y; simp)
  using sep_disj_commute by blast
end

instance option :: ("{sep_disj,times}") sep_magma ..

instance option :: ("{sep_disj,times}") sep_magma_1 proof
  fix x y :: \<open>'a option\<close>
  show \<open>x ## 1\<close> by simp
  show \<open>1 ## x\<close> by simp
qed

instantiation option :: (mul_carrier) mul_carrier begin

definition mul_carrier_option :: \<open>'a option \<Rightarrow> bool\<close>
  where \<open>mul_carrier_option = pred_option mul_carrier \<close>

lemma mul_carrier_option[simp]:
  \<open>mul_carrier None\<close>
  \<open>mul_carrier (Some x) \<longleftrightarrow> mul_carrier x\<close>
  unfolding mul_carrier_option_def
  by simp_all

instance ..

end

instance option :: (sep_carrier) sep_carrier
  by (standard; case_tac a; case_tac b; simp add: mul_carrier_closed)

instance option :: (positive_sep_magma) positive_sep_magma_1 proof
  fix x y :: \<open>'a option\<close>
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def
    apply (cases x; clarsimp simp add: sep_disj_commute sep_mult_commute;
           cases y; clarsimp simp add: sep_disj_commute sep_mult_commute)
    apply (metis times_option_not_none(2))
     apply (metis times_option_not_none(2))
    apply (auto simp add: sep_disj_option_def split: option.split)
    subgoal for _ u v _ apply (cases u; cases v; simp)
      by (metis join_positivity join_sub_def) .
qed

instance option :: (sep_carrier) sep_carrier_1 by (standard; simp)

instance option :: (sep_semigroup) sep_monoid proof
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

instance option :: ("{strict_positive_sep_magma,sep_cancel}") sep_cancel
  apply (standard)
  apply (case_tac a; case_tac b; case_tac c; simp)
  using join_strict_positivity apply blast
  using join_strict_positivity apply fastforce
  using sep_cancel by blast

instance option :: (sep_ab_semigroup) sep_algebra proof
  fix x y z :: \<open>'a option\<close>
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by (cases x; cases y; simp add: sep_disj_commute sep_mult_commute)
qed

instance option :: (discrete_semigroup) discrete_monoid
  by (standard; case_tac x; case_tac y; simp)

instantiation option :: (raw_share) raw_share begin
definition \<open>share_option n = (if 0 < n then map_option (share n) else (\<lambda>_. None))\<close>
instance ..
end

lemma share_option_simps[simp]:
  \<open>share n None = None\<close> \<open>share 0 x = None\<close> \<open>0 < n \<Longrightarrow> share n (Some x') = Some (share n x')\<close>
  unfolding share_option_def by simp_all

instance option :: (share) share 
  by (standard; simp add: share_option_def; case_tac x; simp add: share_share_assoc0)

instance option :: (share_inj) share_inj
  by (standard; case_tac x; case_tac y; simp)

instance option :: (sep_disj_distrib) sep_disj_distrib proof
  fix a b c :: \<open>'a option\<close>
  show \<open>b ## c \<Longrightarrow> a ## b * c = (a ## b \<and> a ## c)\<close> by (cases a; cases b; cases c; simp)
  show \<open>a ## b \<Longrightarrow> a * b ## c = (a ## c \<and> b ## c)\<close> by (cases a; cases b; cases c; simp)
qed

instantiation option :: (share) share_one_eq_one_iff begin
instance by (standard; simp add: share_option_def; case_tac x; simp)
end

instance option :: (share_sep_disj) share_sep_disj
  by (standard; case_tac x; simp add: share_disj_sdistr;
                case_tac y; simp)

instantiation option :: (share_nun_semimodule) share_semimodule begin
instance proof
  fix n m :: rat
  fix x y :: \<open>'a option\<close>
  show \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x * share m x = share (n + m) x\<close>
    by (case_tac x; clarsimp simp add: share_option_def share_sep_left_distrib_0 order_less_le)
  show \<open>0 \<le> n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    by (case_tac x; case_tac y; clarsimp simp add: share_option_def share_sep_right_distrib_0)
  show \<open>0 \<le> n \<Longrightarrow> mul_carrier x \<Longrightarrow> mul_carrier (n \<odivr> x)\<close>
    by (cases \<open>n=0\<close>; cases x; simp add: share_carrier_closed)
  show \<open>0 \<le> n \<and> n \<le> 1 \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x\<close>
    unfolding join_sub_def apply (cases x; clarsimp simp add: share_option_def)
    apply (cases \<open>n = 1\<close>)
    apply (metis mult_1_class.mult_1_right sep_magma_1_left share_left_one)
    apply (cases \<open>n = 0\<close>, simp)
    subgoal premises prems for x'
    proof -
      have t1: \<open>share n x' \<preceq>\<^sub>S\<^sub>L x' \<or> share n x' = x'\<close>
        by (meson antisym_conv2 prems(1) prems(3) prems(4) prems(5) share_sub_0)
      show ?thesis apply (insert t1)
        unfolding join_sub_def apply (elim disjE; clarsimp)
        apply (metis sep_disj_option(1) times_option(1))
        by (metis sep_disj_option(3) times_option(2))
    qed .
qed
end

instance option :: ("{sep_disj,times}") sep_no_inverse 
  by (standard; case_tac x; case_tac y; simp)

lemma times_option_none[simp]:
  \<open>x * y = None \<longleftrightarrow> x = None \<and> y = None\<close>
  by (simp add: option.case_eq_if times_option_def)

lemma Some_discrete_semigroup_sub_join[simp]:
  \<open>Some x \<preceq>\<^sub>S\<^sub>L X \<longleftrightarrow> X = Some x\<close>
  for x :: \<open>'a::discrete_semigroup\<close>
  by (simp add: join_sub_def)


instantiation option :: (ab_semigroup_mult) comm_monoid_mult begin
instance apply (standard)
    apply (case_tac a; case_tac b; case_tac c; simp add: mult.assoc)
   apply (case_tac a; case_tac b; simp add: mult.commute)
  apply (case_tac a; simp) .
end

subsubsection \<open>Homomorphism\<close>

lemma homo_one_map_option[simp]:
  \<open>homo_one (map_option f)\<close>
  unfolding homo_one_def by simp

lemma simple_homo_mul_map_option[simp]:
  \<open>simple_homo_mul (map_option f) UNIV\<close>
  unfolding simple_homo_mul_def
  by simp

lemma homo_mul_carrier_map_option[simp]:
  \<open> homo_mul_carrier f
\<Longrightarrow> homo_mul_carrier (map_option f)\<close>
  unfolding homo_mul_carrier_def
  by (clarsimp simp add: split_option_all)

lemma homo_sep_disj_map_option[simp]:
  \<open> homo_sep_disj f
\<Longrightarrow> homo_sep_disj (map_option f) \<close>
  unfolding homo_sep_disj_def
  by (clarsimp simp add: split_option_all)

lemma closed_homo_sep_disj_map_option[simp]:
  \<open> closed_homo_sep_disj f
\<Longrightarrow> closed_homo_sep_disj (map_option f) \<close>
  unfolding closed_homo_sep_disj_def
  by (clarsimp simp add: split_option_all)

lemma homo_sep_mult_map_option[simp]:
  \<open> homo_sep_mult f
\<Longrightarrow> homo_sep_mult (map_option f)  \<close>
  unfolding homo_sep_mult_def
  by (clarsimp simp add: split_option_all)

lemma homo_sep_map_option[simp]:
  \<open> homo_sep f
\<Longrightarrow> homo_sep (map_option f)  \<close>
  unfolding homo_sep_def
  by (clarsimp simp add: split_option_all)

lemma closed_homo_sep_map_option[simp, locale_intro]:
  \<open> closed_homo_sep f
\<Longrightarrow> closed_homo_sep (map_option f) \<close>
  unfolding closed_homo_sep_def
  by (clarsimp simp add: split_option_all)

lemma homo_share_map_option[simp]:
  \<open> homo_share \<psi>
\<Longrightarrow> homo_share (map_option \<psi>) \<close>
  unfolding homo_share_def
  by (clarsimp simp add: split_option_all share_option_def)

subsection \<open>Product\<close>

subsubsection \<open>Auxiliary\<close>

instantiation prod :: (one, one) one begin
definition "one_prod = (1,1)"
instance ..
end

instance prod :: (numeral, numeral) numeral ..

instantiation prod :: (divide, divide) divide begin
definition divide_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>divide_prod x y = (fst x div fst y, snd x div snd y)\<close>
instance ..
end


subsubsection \<open>Total Algebras\<close>

instantiation prod :: (times, times) times begin
definition "times_prod = (\<lambda>(x1,x2) (y1,y2). (x1 * y1, x2 * y2))"
lemma times_prod[simp]: "(x1,x2) * (y1,y2) = (x1 * y1, x2 * y2)"
  unfolding times_prod_def by simp
instance ..
end

lemma fst_one [simp]: "fst 1 = 1"
  unfolding one_prod_def by simp

lemma snd_one [simp]: "snd 1 = 1"
  unfolding one_prod_def by simp

instantiation prod :: (mult_zero, mult_zero) mult_zero begin
instance by (standard, simp_all add: zero_prod_def split_paired_all)
end

instantiation prod :: (semigroup_mult, semigroup_mult) semigroup_mult begin
instance by standard (simp_all add: split_paired_all algebra_simps)
end

instance prod :: (mult_1, mult_1) mult_1
  by (standard; simp add: one_prod_def split_paired_all)


instance prod :: (monoid_mult, monoid_mult) monoid_mult
  by standard (simp_all add: one_prod_def split_paired_all algebra_simps)

instance prod :: (no_inverse, no_inverse) no_inverse
  by (standard, simp add: one_prod_def times_prod_def split: prod.split) blast

instance prod :: (no_negative, no_negative) no_negative
  by (standard, simp add: zero_prod_def plus_prod_def split_paired_all split: prod.split, blast)

instance prod :: (ab_semigroup_mult, ab_semigroup_mult) ab_semigroup_mult
  by (standard, metis mult.commute prod.collapse times_prod)

instance prod :: (comm_monoid_mult, comm_monoid_mult) comm_monoid_mult by standard simp

instance prod :: (semiring, semiring) semiring
 by (standard, simp_all add: split_paired_all distrib_right distrib_left)

instance prod :: (semiring_0, semiring_0) semiring_0 ..

instance prod :: (comm_semiring, comm_semiring) comm_semiring
 by (standard, simp add: split_paired_all comm_semiring_class.distrib)

instance prod :: (semiring_0_cancel, semiring_0_cancel) semiring_0_cancel ..

instance prod :: (ring, ring) ring ..

instance prod :: (comm_ring, comm_ring) comm_ring ..


subsubsection \<open>Partial Algebras\<close>

instantiation prod :: (sep_disj,sep_disj) sep_disj begin
definition \<open>sep_disj_prod x y = (case x of (x1,x2) \<Rightarrow> case y of (y1,y2) \<Rightarrow> x1 ## y1 \<and> x2 ## y2)\<close>
lemma sep_disj_prod[simp]:
  \<open>(x1,y1) ## (x2,y2) \<longleftrightarrow> x1 ## x2 \<and> y1 ## y2\<close>
  unfolding sep_disj_prod_def by simp
instance ..
end

instance prod :: (sep_magma,sep_magma) sep_magma ..


instantiation prod :: (mul_carrier, mul_carrier) mul_carrier  begin

definition mul_carrier_prod :: \<open>'a \<times> 'b \<Rightarrow> bool\<close>
  where \<open>mul_carrier_prod = pred_prod mul_carrier mul_carrier\<close>

lemma mul_carrier_prod[simp]:
  \<open> mul_carrier (x,y) \<longleftrightarrow> mul_carrier x \<and> mul_carrier y \<close>
  unfolding mul_carrier_prod_def by simp

instance ..

end

instance prod :: (sep_carrier, sep_carrier) sep_carrier
  by (standard; clarsimp simp add: mul_carrier_closed)

instance prod :: (sep_magma_1, sep_magma_1) sep_magma_1
  by (standard; simp add: one_prod_def split_paired_all)

instance prod :: (sep_carrier_1, sep_carrier_1) sep_carrier_1
  by (standard; simp add: one_prod_def)

instance prod :: (sep_no_inverse, sep_no_inverse) sep_no_inverse
  by (standard, simp add: one_prod_def times_prod_def split: prod.split) force

instance prod :: (sep_cancel,sep_cancel) sep_cancel
  by (standard; case_tac a; case_tac b; case_tac c; simp; meson sep_cancel)

instance prod :: (sep_disj_distrib,sep_disj_distrib) sep_disj_distrib
  by (standard; case_tac a; case_tac b; case_tac c; simp; blast)


instance prod :: (zero_neq_one, zero_neq_one) zero_neq_one
  by (standard, simp add: zero_prod_def one_prod_def)

instance prod :: (semiring_1, semiring_1) semiring_1 ..

instance prod :: (ring_1, ring_1) ring_1 ..

instantiation prod :: (comm_ring_1, comm_ring_1) comm_ring_1 begin
instance ..
end



instantiation prod :: (inverse, inverse) inverse begin
definition inverse_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>inverse_prod x = (case x of (a,b) \<Rightarrow> (inverse a, inverse b))\<close>
instance ..
end

subsubsection \<open>\<close>

instantiation prod :: (ord, ord) ord begin
definition less_eq_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close>
  where \<open>less_eq_prod x y \<longleftrightarrow> fst x \<le> fst y \<and> snd x \<le> snd y\<close>
definition less_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close>
  where \<open>less_prod x y \<longleftrightarrow> fst x < fst y \<and> snd x < snd y\<close>

lemma [simp]: \<open>(x1,x2) < (y1,y2) \<longleftrightarrow> x1 < y1 \<and> x2 < y2\<close> unfolding less_prod_def by simp
lemma [simp]: \<open>(x1,x2) \<le> (y1,y2) \<longleftrightarrow> x1 \<le> y1 \<and> x2 \<le> y2\<close> unfolding less_eq_prod_def by simp

instance ..
end

lemma less_eq_prod:
  \<open>a \<le> b \<longleftrightarrow> fst a \<le> fst b \<and> snd a \<le> snd b\<close>
  by (cases a; cases b; simp)

lemma less_prod:
  \<open>a < b \<longleftrightarrow> fst a < fst b \<and> snd a < snd b\<close>
  by (cases a; cases b; simp)

instance prod :: (add_order_0, add_order_0) add_order_0
  by (standard; case_tac a; case_tac b; simp add: zero_prod_def add_nonneg_nonneg add_pos_pos)


subsection \<open>Coproduct\<close>

instantiation sum :: (times, times) times begin
definition times_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b\<close>
  where "times_sum = (\<lambda>x y. case x of Inl x1 \<Rightarrow> (case y of Inl y1 \<Rightarrow> Inl (x1 * y1))
                                    | Inr x2 \<Rightarrow> (case y of Inr y2 \<Rightarrow> Inr (x2 * y2)))"
lemma times_sum:
  \<open>Inl x1 * Inl y1 = Inl (x1 * y1)\<close>
  \<open>Inr x2 * Inr y2 = Inr (x2 * y2)\<close>
  unfolding times_sum_def by simp_all
instance ..
end

instantiation sum :: (plus, plus) plus begin
definition plus_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b\<close>
  where "plus_sum = (\<lambda>x y. case x of Inl x1 \<Rightarrow> (case y of Inl y1 \<Rightarrow> Inl (x1 + y1))
                                   | Inr x2 \<Rightarrow> (case y of Inr y2 \<Rightarrow> Inr (x2 + y2)))"
lemma plus_sum[simp]:
  \<open>Inl x1 + Inl y1 = Inl (x1 + y1)\<close>
  \<open>Inr x2 + Inr y2 = Inr (x2 + y2)\<close>
  unfolding plus_sum_def by simp_all
instance ..
end




subsection \<open>List\<close>

text \<open>We always follow the order of associativity. The list appending is right associative,
  meaning the new elements are at left, and multiplication is left associative where
  new elements are at the right, so here there is a reverse between the multiplication of list
  and concatenation.\<close>

instantiation list :: (type) times begin
definition "times_list a b = a @ b"
instance ..
end

instantiation list :: (type) plus begin
definition [simp]: "plus_list a b = a @ b"
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

instance list :: (type) no_inverse by (standard, simp add: times_list_def)

instance list :: (type) no_negative by (standard, simp add: plus_list_def)

instance list :: (type) semigroup_mult by standard (simp_all add: times_list_def)

instance list :: (type) semigroup_add by standard (simp_all add: plus_list_def)

instance list :: (type) monoid_mult by standard (simp_all add: times_list_def)

instance list :: (type) monoid_add by standard (simp_all add: plus_list_def)

instantiation list :: (type) sep_magma begin
definition sep_disj_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>
  where [simp]: \<open>sep_disj_list _ _ = True\<close>
instance by (standard; simp)
end

instantiation list :: (mul_carrier) mul_carrier begin

definition mul_carrier_list :: \<open>'a list \<Rightarrow> bool\<close>
  where [simp]: \<open>mul_carrier_list = list_all mul_carrier\<close>

instance ..
end

instance list :: (sep_carrier) sep_carrier
  by (standard; simp add: times_list_def)

instance list :: (type) sep_monoid
  by (standard; clarsimp simp add: times_list_def join_sub_def)

instance list :: (sep_carrier_1) sep_carrier_1
  by (standard; simp add: times_list_def)

instance list :: (type) sep_disj_distrib by (standard; simp)

instance list :: (type) sep_cancel
  by (standard; simp add: times_list_def)


subsection \<open>Function\<close>

subsubsection \<open>Instantiations of Algebra\<close>

paragraph \<open>Basics\<close>

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
lemmas zero_fun_eta = zero_fun_def[symmetric]

lemma fun_updt_1_1[simp]:
  \<open>1(x := 1) = 1\<close>
  unfolding fun_eq_iff by simp

lemma fun_updt_0_0[simp]:
  \<open>0(x := 0) = 0\<close>
  unfolding fun_eq_iff by simp


paragraph \<open>Partial Multiplicative Algebras\<close>

instance "fun" :: (type, no_inverse) no_inverse
  by (standard, simp add: one_fun_def times_fun fun_eq_iff, blast)

instance "fun" :: (type, no_negative) no_negative
  by (standard, simp del: zero_fun_eta add: zero_fun_def plus_fun fun_eq_iff, blast)

instance "fun" :: (type, semigroup_mult) semigroup_mult
  by (standard; simp add: mult.assoc times_fun_def)

instantiation "fun" :: (type,sep_disj) sep_disj begin
definition "sep_disj_fun m1 m2 = (\<forall>x. m1 x ## m2 x)"
instance ..
end

instance "fun" :: (type,comm_sep_disj) comm_sep_disj
  by (standard, simp_all add: sep_disj_fun_def times_fun fun_eq_iff
                         add: sep_disj_commute sep_mult_commute )

lemma sep_disj_fun[simp]: \<open>(f ## g) \<Longrightarrow> f x ## g x\<close>
  unfolding sep_disj_fun_def by blast

lemma sep_disj_fun_discrete:
  \<open>f x = Some v \<Longrightarrow> f ## g \<Longrightarrow> g x = None\<close>
  \<open>f x = Some v \<Longrightarrow> g ## f \<Longrightarrow> g x = None\<close>
  for v :: \<open>'a :: discrete_semigroup\<close>
  by (metis sep_disj_fun sep_disj_option_discrete)+


instance "fun" :: (type,mult_1) mult_1
  by (standard; simp add: one_fun_def times_fun_def)

instance "fun" :: (type,sep_magma) sep_magma ..

instance "fun" :: (type,sep_magma_1) sep_magma_1
 by (standard; simp add: sep_disj_fun_def)

instantiation "fun" :: (type, mul_carrier) mul_carrier begin

definition mul_carrier_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>mul_carrier_fun = (\<lambda>f. \<forall>k. mul_carrier (f k))\<close>

lemma mul_carrier_fun[simp]: \<open>mul_carrier f = (\<forall>k. mul_carrier (f k))\<close>
  unfolding mul_carrier_fun_def ..

instance ..
end

instance "fun" :: (type, sep_carrier) sep_carrier
  by (standard; simp add: times_fun mul_carrier_closed)

instance "fun" :: (type, sep_carrier_1) sep_carrier_1
  by (standard; simp)

instance "fun" :: (type, sep_cancel) sep_cancel
  apply (standard; simp add: fun_eq_iff times_fun sep_disj_fun_def)
  using sep_cancel by blast

instance "fun" :: (type, sep_no_inverse) sep_no_inverse
  by (standard; simp add: one_fun_def fun_eq_iff times_fun; blast)

instance "fun" :: (type, sep_semigroup) sep_semigroup proof
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

instance "fun" :: (type,sep_ab_semigroup) sep_ab_semigroup proof
  fix x y z :: "'a \<Rightarrow> 'b"
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close>
    by (simp add: sep_disj_fun_def times_fun_def fun_eq_iff sep_disj_commute sep_mult_commute)
qed

instance "fun" :: (type, sep_monoid) sep_monoid
  by (standard; simp add: sep_disj_fun_def fun_eq_iff times_fun_def; blast)

instance "fun" :: (type, sep_algebra) sep_algebra
  by (standard; simp add: sep_disj_fun_def fun_eq_iff times_fun_def; blast)

instance "fun" :: (type, sep_disj_distrib) sep_disj_distrib
  by (standard; simp add: sep_disj_fun_def times_fun; blast)

instance "fun" :: (type,monoid_mult) monoid_mult
  by standard (simp_all add: mult.commute times_fun_def fun_eq_iff)

instance "fun" :: (type,comm_monoid_mult) comm_monoid_mult
  by standard (simp_all add: mult.commute times_fun_def fun_eq_iff)

instance "fun" :: (type,monoid_add) monoid_add proof
  fix a b c :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>a + b + c = a + (b + c)\<close> unfolding plus_fun_def fun_eq_iff by (simp add: add.assoc)
  show \<open>0 + a = a\<close> unfolding plus_fun_def fun_eq_iff by (simp add: add.assoc)
  show \<open>a + 0 = a\<close> unfolding plus_fun_def fun_eq_iff by (simp add: add.assoc)
qed

instance "fun" :: (type,comm_monoid_add) comm_monoid_add proof
  fix a b :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>a + b = b + a\<close> unfolding plus_fun_def fun_eq_iff using add.commute by blast
  show \<open>0 + a = a\<close> unfolding plus_fun_def fun_eq_iff by simp
qed


subsubsection \<open>Properties\<close>

definition \<open>pointwise_set D = {f. \<forall> k. f k \<in> D}\<close>


subsubsection \<open>Multiplication with Function Update\<close>

lemma times_fupdt_1_apply[simp]:
  "(1(k := x) * f) k = x * f k" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  by (simp add: times_fun_def)

lemma times_fupdt_1_apply_sep[simp]:
  "(1(k := x) * f) k = x * f k" for f :: "'a \<Rightarrow> 'b::sep_monoid"
  by (simp add: times_fun_def)

lemma times_fupdt_1_apply'[simp]:
  "k' \<noteq> k \<Longrightarrow> (1(k':=x) * f) k = f k" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  by (simp add: times_fun_def)

lemma times_fupdt_1_apply'_sep[simp]:
  "k' \<noteq> k \<Longrightarrow> (1(k':=x) * f) k = f k" for f :: "'a \<Rightarrow> 'b::sep_monoid"
  by (simp add: times_fun_def)

lemma times_fupdt_1_fupdt_1[simp]:
  "(1(k := x) * f)(k:=1) = f(k:=1)" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma times_fupdt_1_fupdt_1_sep[simp]:
  "(1(k := x) * f)(k:=1) = f(k:=1)" for f :: "'a \<Rightarrow> 'b::sep_monoid"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma [simp]:
  "k' \<noteq> k \<Longrightarrow> (1(k' := x) * f)(k:=1) = 1(k' := x) * f(k:=1)" for f :: "'a \<Rightarrow> 'b::monoid_mult"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma [simp]:
  "k' \<noteq> k \<Longrightarrow> (1(k' := x) * f)(k:=1) = 1(k' := x) * f(k:=1)" for f :: "'a \<Rightarrow> 'b::sep_monoid"
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


lemma fun_split_1: "f = 1(k:= f k) * f(k:=1)" for f :: "'a \<Rightarrow> 'b :: mult_1"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma fun_1upd1[simp]:
  "1(k := 1) = 1"
  unfolding one_fun_def fun_upd_def by simp

lemma fun_1upd_homo:
    "1(k := x) * 1(k := y) = 1(k := x * y)" for x :: "'a::sep_magma_1"
  unfolding one_fun_def fun_upd_def times_fun_def
  by fastforce

lemma fun_1upd_homo_right1:
    "f(k := x) * 1(k := y) = f(k := x * y)" for x :: "'a::sep_magma_1"
  unfolding one_fun_def fun_upd_def times_fun_def fun_eq_iff
  by clarsimp

lemma fun_1upd_homo_left1:
    "1(k := x) * f(k := y) = f(k := x * y)" for x :: "'a::sep_magma_1"
  unfolding one_fun_def fun_upd_def times_fun_def fun_eq_iff
  by clarsimp

lemma [simp]: "NO_MATCH (a::'a) (1::'a::one) \<Longrightarrow> i \<noteq> k \<Longrightarrow> f(i := a, k := 1) = f(k := 1, i := a)"
  using fun_upd_twist .


subsubsection \<open>Share\<close>

instantiation "fun" :: (type, raw_share) raw_share begin

definition share_fun :: \<open>rat \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  where \<open>share_fun n f = share n o f\<close>

instance ..
end

instance "fun" :: (type, share) share
  by (standard; simp add: share_fun_def fun_eq_iff share_share_assoc0)

instance "fun" :: (type, share_inj) share_inj
  by (standard; simp add: share_fun_def fun_eq_iff)

instance "fun" :: (type,share_one) share_one
  by (standard; simp add: share_fun_def fun_eq_iff)

instance "fun" :: (type,share_one_eq_one_iff) share_one_eq_one_iff
  by (standard; simp add: share_fun_def fun_eq_iff)

instance "fun" :: (type, share_sep_disj) share_sep_disj
  by (standard; simp add: share_fun_def fun_eq_iff sep_disj_fun_def share_disj_sdistr)

instance "fun" :: (type, share_semimodule) share_semimodule
proof
  fix n m :: rat
  and x y :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>0 \<le> n \<Longrightarrow> mul_carrier x \<Longrightarrow> mul_carrier (n \<odivr> x)\<close>
    by (clarsimp simp add: share_fun_def share_carrier_closed_1)
  show \<open>0 \<le> n \<Longrightarrow> 0 \<le> m \<Longrightarrow> mul_carrier x \<Longrightarrow> n \<odivr> x * m \<odivr> x = (n + m) \<odivr> x\<close>
    by (clarsimp simp add: share_fun_def fun_eq_iff times_fun_def share_sep_left_distrib)
  show \<open>0 \<le> n \<Longrightarrow> x ## y \<Longrightarrow> n \<odivr> x * n \<odivr> y = n \<odivr> (x * y)\<close>
    by (clarsimp simp add: share_fun_def fun_eq_iff times_fun_def share_sep_right_distrib)
  have t1: \<open>0 \<le> n \<and> n \<le> 1 \<Longrightarrow> \<forall>k. mul_carrier (x k) \<Longrightarrow> \<forall>a. share n (x a) \<preceq>\<^sub>S\<^sub>L (x a)\<close>
    using share_sub by blast
  then show \<open>0 \<le> n \<and> n \<le> 1 \<Longrightarrow> mul_carrier x \<Longrightarrow> n \<odivr> x \<preceq>\<^sub>S\<^sub>L x\<close>
    by (clarsimp simp add: join_sub_def share_fun_def fun_eq_iff times_fun_def sep_disj_fun_def; metis)
qed

lemma share_fun_updt[simp]:
  \<open>share n (f(k := v)) = (share n f)(k := share n v)\<close>
  unfolding share_fun_def fun_eq_iff by simp


subsubsection \<open>Homomorphisms\<close>

lemma homo_add_funcomp[locale_intro]:
  assumes hom_f: \<open>homo_add f\<close>
  shows \<open>homo_add ((o) f)\<close>
proof -
  interpret f: homo_add f using hom_f .
  show ?thesis by (standard; simp add: fun_eq_iff plus_fun f.homo_add)
qed

lemma homo_zero_funcomp[locale_intro]:
  assumes hom_f: \<open>homo_zero f\<close>
  shows \<open>homo_zero ((o) f)\<close>
proof -
  interpret f: homo_zero f using hom_f .
  show ?thesis by (standard; simp add: fun_eq_iff)
qed

lemma homo_mult_funcomp[locale_intro]:
  assumes hom_f: \<open>homo_mult f\<close>
  shows \<open>homo_mult ((o) f)\<close>
proof -
  interpret f: homo_mult f using hom_f .
  show ?thesis by (standard; simp add: fun_eq_iff times_fun f.homo_mult)
qed

lemma homo_one_funcomp[simp, locale_intro]:
  assumes hom_f: \<open>homo_one f\<close>
  shows \<open>homo_one ((o) f)\<close>
proof -
  interpret f: homo_one f using hom_f .
  show ?thesis by (standard; simp add: fun_eq_iff)
qed

lemma simple_homo_mul_funcomp[simp]:
  \<open> simple_homo_mul f D
\<Longrightarrow> simple_homo_mul ((o) f) (pointwise_set D)\<close>
  unfolding simple_homo_mul_def pointwise_set_def
  by (clarsimp simp add: Ball_def fun_eq_iff)

lemma homo_mul_funcomp[simp, locale_intro]:
  \<open> homo_mul_carrier f
\<Longrightarrow> homo_mul_carrier ((o) f) \<close>
  unfolding homo_mul_carrier_def
  by clarsimp

lemma homo_sep_disj_funcomp[simp, locale_intro]:
  \<open> homo_sep_disj f
\<Longrightarrow> homo_sep_disj ((o) f) \<close>
  unfolding homo_sep_disj_def
  by (clarsimp simp add: sep_disj_fun_def)

lemma closed_homo_sep_disj_funcomp[simp, locale_intro]:
  \<open> closed_homo_sep_disj f
\<Longrightarrow> closed_homo_sep_disj ((o) f) \<close>
  unfolding closed_homo_sep_disj_def
  by (clarsimp simp add: sep_disj_fun_def)

lemma homo_sep_mult_funcomp[simp, locale_intro]:
  \<open> homo_sep_mult f
\<Longrightarrow> homo_sep_mult ((o) f) \<close>
  unfolding homo_sep_mult_def
  by (clarsimp simp add: fun_eq_iff times_fun_def)

lemma homo_sep_funcomp[simp, locale_intro]:
  \<open> homo_sep f
\<Longrightarrow> homo_sep ((o) f) \<close>
  unfolding homo_sep_def
  by (clarsimp simp add: fun_eq_iff times_fun_def)

lemma closed_homo_sep_funcomp[simp, locale_intro]:
  \<open> closed_homo_sep f
\<Longrightarrow> closed_homo_sep ((o) f) \<close>
  unfolding closed_homo_sep_def
  by (clarsimp simp add: fun_eq_iff times_fun_def)

lemma (in homo_zero) fun_updt_single_point[simp]:
  \<open>\<phi> o 0(i := x) = 0(i := \<phi> x)\<close>
  unfolding fun_eq_iff by simp

lemma fun_updt_single_point[simp]:
  \<open>homo_one \<phi> \<Longrightarrow> \<phi> o 1(i := x) = 1(i := \<phi> x)\<close>
  unfolding fun_eq_iff homo_one_def by simp

lemma homo_share_funcomp[simp]:
  \<open> homo_share \<psi>
\<Longrightarrow> homo_share ((o) \<psi>)\<close>
  unfolding homo_share_def
  by (clarsimp simp add: fun_eq_iff share_fun_def)


subsection \<open>Finite Map\<close>

instantiation fmap :: (type,times) times begin
context includes fmap.lifting begin
lift_definition times_fmap :: \<open>('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap\<close> is "(\<lambda>f g x. (f x::'b option) * g x)"
  by (simp add: dom_def)
instance ..
end
end

context includes fmap.lifting begin
lemma times_fmlookup[simp]:
  \<open>fmlookup (f * g) x = fmlookup f x * fmlookup g x\<close> by (transfer; simp)
end

instantiation "fmap" :: (type,type) one begin
definition one_fmap :: \<open>('a, 'b) fmap\<close>
  where [iff]: \<open>one_fmap = fmempty\<close>
instance ..
end

lemma one_fmap[simp]: "fmlookup 1 x = 1" including fmap.lifting by (transfer; simp)

instantiation fmap :: (type,sep_disj) sep_disj begin
context includes fmap.lifting begin
lift_definition sep_disj_fmap :: \<open>('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool\<close>
  is "\<lambda>m1 m2. (\<forall>x. m1 x ## m2 x)" .
instance ..
end
end

context includes fmap.lifting begin

lemma fmap_times_fempty[simp]:
  \<open>f * fmempty = f\<close>
  \<open>fmempty * f = f\<close>
  by (transfer, auto, transfer, auto)

lemma fmap_sepdisj_fmempty[simp]:
  \<open>f ## fmempty\<close>
  \<open>fmempty ## f\<close>
  by (transfer, auto, transfer, auto)

end

instance "fmap" :: (type,times) mult_1
  including fmap.lifting
  by (standard; transfer; simp)


instance "fmap" :: (type,sep_magma) sep_magma ..

instantiation "fmap" :: (type, sep_carrier) sep_carrier begin

context includes fmap.lifting begin
lift_definition mul_carrier_fmap :: \<open>('a, 'b) fmap \<Rightarrow> bool\<close>
  is \<open>\<lambda>f. (\<forall>k. mul_carrier (f k))\<close> .

instance by (standard; transfer; simp add: mul_carrier_closed)

end

end

instance "fmap" :: (type,sep_magma) sep_magma_1
  including fmap.lifting
  by (standard; transfer; simp)
  
context includes fmap.lifting fset.lifting begin

lemma fmap_times_single[simp]:
  \<open>s |\<notin>| fmdom y \<Longrightarrow> y * fmupd s x fmempty = fmupd s x y\<close>
proof (transfer, auto)
  fix sa :: 'a and ya :: "'a \<Rightarrow> 'b option" and xa :: 'b
  assume a1: "(\<lambda>x. ya x * map_upd sa xa (\<lambda>x. None) x) \<noteq> map_upd sa xa ya"
  obtain zz :: "'a \<Rightarrow> 'b option" where
    f2: "\<forall>X23. zz X23 = None"
    by moura
  obtain aa :: 'a and zza :: "'a \<Rightarrow> 'b option" where
    "ya aa * map_upd sa xa zza aa \<noteq> map_upd sa xa ya aa"
    using a1 by blast
  then show "\<exists>b. ya sa = Some b"
  proof -
    obtain aaa :: 'a where
      f1: "ya aaa * map_upd sa xa (\<lambda>a. None) aaa \<noteq> map_upd sa xa ya aaa"
      using a1 by blast
    obtain zzb :: "'a \<Rightarrow> 'b option" where
      f2: "\<forall>X1. zzb X1 = None"
      by moura
    then have "ya aaa * map_upd sa xa zzb aaa \<noteq> map_upd sa xa ya aaa"
      using f1 by presburger
    then show ?thesis
      using f2 by (metis fun_upd_other fun_upd_same map_upd_def option.exhaust_sel times_option(2) times_option(3))
  qed
qed


lemma fmdom_times[simp]:
  \<open>fmdom (fm1 * fm2) = fmdom fm1 |\<union>| fmdom fm2\<close>
  by (transfer, auto simp add: domD domIff)

lemma fmupd_times_right:
  \<open> k |\<notin>| fmdom y
\<Longrightarrow> fmupd k v (x * y) = fmupd k v x * y\<close>
  by (transfer, auto simp: map_upd_def fun_eq_iff, insert domIff, fastforce)

lemma fmupd_times_left:
  \<open> k |\<notin>| fmdom x
\<Longrightarrow> fmupd k v (x * y) = x * fmupd k v y\<close>
  by (transfer, auto simp: map_upd_def fun_eq_iff, insert domIff, fastforce)

lemma sep_disj_fmupd_right[simp]:
  \<open> k |\<notin>| fmdom f
\<Longrightarrow> k |\<notin>| fmdom g
\<Longrightarrow> f ## g
\<Longrightarrow> f ## fmupd k v g \<close>
  by (transfer, auto simp add: map_upd_def)

lemma sep_disj_fmupd_left[simp]:
  \<open> k |\<notin>| fmdom f
\<Longrightarrow> k |\<notin>| fmdom g
\<Longrightarrow> g ## f
\<Longrightarrow> fmupd k v g ## f \<close>
  by (transfer, auto simp add: map_upd_def)

end


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

instance unit :: no_inverse by standard simp_all

instantiation unit :: no_negative begin
instance by standard simp_all
end

instantiation unit :: sep_disj_distrib begin
definition sep_disj_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> bool\<close> where [simp]: \<open>sep_disj_unit _ _ = True\<close>
instance by (standard; simp)
end

instance unit :: sep_no_inverse by standard simp_all

instance unit :: sep_cancel by standard simp

instantiation unit :: sep_carrier_1 begin

definition mul_carrier_unit :: \<open>unit \<Rightarrow> bool\<close> where [simp]: \<open>mul_carrier_unit x = True \<close>

instance by (standard; simp)

end

subsection \<open>Set\<close>


instantiation set :: (type) zero begin
definition zero_set where "zero_set = {}"
instance ..
end

lemma zero_set_iff[simp]: \<open>x \<notin> 0\<close> unfolding zero_set_def by simp

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

lemma times_set_I[simp]: (*TODO: dangerous? ? I just added this to simp*)
  \<open>x \<in> P \<Longrightarrow> y \<in> Q \<Longrightarrow> x ## y \<Longrightarrow> x * y \<in> P * Q\<close>
  unfolding times_set_def by simp blast

lemma set_mult_zero[iff]: "{} * S = {}" "S * {} = {}"
  unfolding times_set_def by simp_all

lemma set_mult_single: \<open>A ## B \<Longrightarrow> {A} * {B} = {A * B}\<close>
  unfolding times_set_def set_eq_iff by simp

lemma set_mult_expn:
  \<open>uv \<in> (S * T) \<longleftrightarrow> (\<exists>u v. uv = u * v \<and> u \<in> S \<and> v \<in> T \<and> u ## v)\<close>
  unfolding times_set_def by simp

lemma times_set_subset[intro, simp]:
  \<open>B \<subseteq> B' \<Longrightarrow> A * B \<subseteq> A * B'\<close>
  \<open>B \<subseteq> B' \<Longrightarrow> B * A \<subseteq> B' * A\<close>
  unfolding subset_iff times_set_def by simp_all blast+

instantiation set :: ("{sep_disj,times}") mult_zero begin
instance by (standard; simp add: zero_set_def times_set_def)
end

instance set :: ("{sep_magma_1,no_inverse}") no_inverse
  apply (standard, simp add: one_set_def times_set_def set_eq_iff)
  by (metis (no_types, opaque_lifting) no_inverse sep_magma_1_left sep_magma_1_right)

instantiation set :: (type) total_sep_disj begin
definition sep_disj_set :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where [simp]: \<open>sep_disj_set _ _ = True\<close>
instance by (standard; simp)
end

instance set :: (sep_magma) sep_magma ..

instance set :: (sep_magma_1) sep_magma_1 proof
  fix x :: \<open>'a set\<close>
  show \<open>1 * x = x\<close> unfolding one_set_def times_set_def by simp
  show \<open>x * 1 = x\<close> unfolding one_set_def times_set_def by simp
  show \<open>x ## 1\<close> unfolding one_set_def sep_disj_set_def by simp
  show \<open>1 ## x\<close> unfolding one_set_def sep_disj_set_def by simp
qed

instance set :: (sep_no_inverse) sep_no_inverse
  apply (standard, simp add: one_set_def times_set_def set_eq_iff)
  by (metis (no_types, opaque_lifting) sep_magma_1_left sep_magma_1_right sep_no_inverse)

instantiation set :: (sep_disj_distrib) sep_disj_distrib begin
instance by (standard; simp)
end

instance set :: (sep_semigroup) semigroup_mult
  apply (standard; clarsimp simp add: times_set_def algebra_simps set_eq_iff; rule; clarsimp)
  using sep_disj_multD2 sep_disj_multI2 sep_mult_assoc apply blast
  by (metis sep_disj_multD1 sep_disj_multI1 sep_mult_assoc)

instance set :: (sep_monoid) monoid_mult
  by standard (simp_all add: one_set_def times_set_def)

instance set :: (sep_ab_semigroup) ab_semigroup_mult
  apply (standard; simp add: times_set_def set_eq_iff)
  using sep_disj_commute sep_mult_commute by blast

instance set :: (sep_algebra) comm_monoid_mult
  by (standard; simp_all add: one_set_def times_set_def)

instantiation set :: (type) comm_monoid_add begin
definition \<open>plus_set = union\<close>
instance by standard (auto simp add: plus_set_def zero_set_def)
end

instance set :: (type) ordered_comm_monoid_add
  by standard (auto simp add: plus_set_def zero_set_def)

lemma plus_set_in_iff[iff]:
  \<open>x \<in> A + B \<longleftrightarrow> x \<in> A \<or> x \<in> B\<close> unfolding plus_set_def by simp

lemma plus_set_S_S [simp]: \<open>S + S = S\<close> for S :: \<open>'a set\<close> unfolding plus_set_def by simp

instance set :: (sep_semigroup) ordered_semiring_0
  by standard (auto simp add: zero_set_def plus_set_def times_set_def)

instance set :: (sep_monoid) semiring_1
  by standard (auto simp add: zero_set_def plus_set_def times_set_def)

instance set :: (sep_ab_semigroup) ordered_comm_semiring
  by (standard, simp add: zero_set_def plus_set_def times_set_def,
      (insert mult.commute, blast)[1],
      simp)

instance set :: (sep_algebra) comm_semiring_1
  by standard (auto simp add: zero_set_def plus_set_def times_set_def)



paragraph \<open>Partial Additive Commutative Monoid\<close>

instantiation set :: (type) comm_dom_of_add begin
definition dom_of_add_set :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where [iff]: \<open>dom_of_add_set A B \<longleftrightarrow> (A \<inter> B = {})\<close>

instance by (standard, simp add: dom_of_add_set_def, blast)
end

instantiation set :: (type) dom_of_minus begin
definition dom_of_minus_set :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where [simp]: \<open>dom_of_minus_set A B \<longleftrightarrow> B \<subseteq> A\<close>
instance ..
end

instance set :: (type) partial_cancel_ab_semigroup_add
  by (standard; simp add: dom_of_add_set_def plus_set_def; blast)

instance set :: (type) partial_canonically_ordered_ab_semigroup_add
  by (standard; simp add: dom_of_add_set_def; blast)

instance set :: (type) positive_partial_add_magma_0
  by (standard; simp add: dom_of_add_set_def zero_set_def additive_join_sub_def; blast)

instance set :: (type) partial_add_ab_monoid ..

paragraph \<open>Rules for Specific Cases\<close>

lemma dom_of_add_lcro_intvl[simp]:
  \<open> {a..<b} ##\<^sub>+ {c..<d} \<longleftrightarrow> b \<le> a \<or> b \<le> c \<or> d \<le> c \<or> d \<le> a\<close>
  for a :: \<open>'a::linorder\<close>
  unfolding dom_of_add_set_def
  by (auto simp add: set_eq_iff; meson leI nle_le)
  

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
  for f :: "'a \<rightharpoonup> ('b :: discrete_semigroup)"
  unfolding sep_disj_fun_def sep_disj_option_def disjoint_iff
  by (smt (verit, ccfv_SIG) domD domIff discrete_disj option.simps(4) option.simps(5))


lemma sep_disj_partial_map_some_none:
  \<open>f ## g \<Longrightarrow> g k = Some v \<Longrightarrow> f k = None\<close>
  for f :: "'a \<rightharpoonup> ('b :: discrete_semigroup)"
  using sep_disj_fun by fastforce

lemma sep_disj_partial_map_not_1_1:
  \<open>f ## g \<Longrightarrow> g k \<noteq> 1 \<Longrightarrow> f k = 1\<close>
  for f :: "'a \<Rightarrow> ('b :: discrete_monoid)"
  unfolding sep_disj_fun_def apply simp
  by blast


lemma sep_disj_partial_map_upd:
  \<open>f ## g \<Longrightarrow> k \<in> dom f \<Longrightarrow> (f * g)(k := v) = (f(k:=v) * g)\<close>
  for f :: "'a \<rightharpoonup> ('b :: discrete_semigroup)"
  unfolding sep_disj_partial_map_disjoint fun_upd_def times_fun fun_eq_iff
  by (simp add: disjoint_iff domIff)

lemma discrete_semigroup_sepdisj_fun:
  \<open>1(k \<mapsto> x) ## a \<Longrightarrow> 1(k := any) ## a\<close>
  for x :: \<open>'b::discrete_semigroup\<close>
  unfolding sep_disj_fun_def
  by (metis discrete_disj_1 fun_upd_apply sep_disj_option_discrete(1))


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

lemma dom1_dom: "dom1 = dom"
  by (metis fun_eq_iff dom1_def dom_def one_option_def)

lemma one_updt_one[simp]: "1(a:=1) = 1" unfolding one_fun_def fun_upd_def by simp

lemma v_neq_1_fupdt_neq_1[simp]: "x \<noteq> 1 \<Longrightarrow> f(k:=x) \<noteq> 1"
  unfolding one_fun_def fun_upd_def fun_eq_iff by simp blast

lemma one_ringop_f_is_1[simp]: "1 o f = 1"
  unfolding one_fun_def fun_eq_iff by simp

lemma finite_dom1_mult1[simp]:
  "finite (dom1 (1(k:=v) * f)) \<longleftrightarrow> finite (dom1 f)"
  for f :: "'a \<Rightarrow> 'b :: sep_monoid"
proof -
  have "dom1 (1(k:=v) * f) = dom1 f \<or> dom1 (1(k:=v) * f) = insert k (dom1 f)
    \<or> dom1 (1(k:=v) * f) = dom1 f - {k}"
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
  for f :: \<open>'a \<Rightarrow> 'b::discrete_monoid\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff
  by clarsimp

lemma dom1_mult: \<open>f ## g \<Longrightarrow> dom1 (f * g) = dom1 f \<union> dom1 g\<close>
  for f :: \<open>'a \<Rightarrow> 'b :: {sep_no_inverse,sep_disj}\<close>
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
  "k \<notin> dom1 f \<Longrightarrow> f(k := v) = 1(k:= v) * f" for f :: "'a \<Rightarrow> 'b::mult_1"
  unfolding fun_upd_def fun_eq_iff times_fun_def dom1_def by simp

lemma fun_split_1_not_dom:
  "k \<notin> dom f \<Longrightarrow> f(k := v) = 1(k:= v) * f"
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

lemma pointwise_set_UNIV:
  \<open>pointwise_set UNIV = UNIV\<close>
  unfolding pointwise_set_def by simp

lemma sep_orthogonal_monoid_pointwise[locale_intro]:
  assumes D':   \<open>D' = pointwise_set D\<close>
      and prem: \<open>sep_orthogonal_monoid \<psi> D\<close>
  shows \<open>sep_orthogonal_monoid ((\<circ>) \<psi>) D'\<close>
  unfolding comp_def
proof
  interpret xx: sep_orthogonal_monoid \<psi> D using prem .
  fix x y a b c :: \<open>'a \<Rightarrow> 'b\<close>
  fix a' :: \<open>'a \<Rightarrow> 'c\<close>
  show \<open>x ## y \<Longrightarrow> (\<lambda>xa. \<psi> ((x * y) xa)) = (\<lambda>xa. \<psi> (x xa)) * (\<lambda>x. \<psi> (y x))\<close>
    by (simp add: fun_eq_iff times_fun sep_disj_fun_def xx.homo_mult)
  show \<open>a ## b \<longrightarrow> (\<lambda>x. \<psi> (a x)) ## (\<lambda>x. \<psi> (b x))\<close>
    by (simp add: fun_eq_iff times_fun sep_disj_fun_def D' pointwise_set_def)
  show \<open>b \<in> D' \<and> c \<in> D' \<Longrightarrow> (\<lambda>x. \<psi> (b x)) ## a' \<Longrightarrow>
     ((\<lambda>x. \<psi> (b x)) * a' = (\<lambda>x. \<psi> (c x))) = (\<exists>a. a' = (\<lambda>x. \<psi> (a x)) \<and> b * a = c \<and> b ## a \<and> a \<in> D')\<close>
    by (auto simp add: D' fun_eq_iff times_fun sep_disj_fun_def xx.sep_orthogonal pointwise_set_def; metis)
  show \<open>1 \<in> D'\<close>
    by (simp add: D' pointwise_set_def xx.one_in_D)
qed

lemma share_orthogonal_homo_pointwise[locale_intro]:
  assumes D':   \<open>D' = pointwise_set D\<close>
      and prem: \<open>share_orthogonal_homo \<psi> D\<close>
    shows \<open>share_orthogonal_homo ((\<circ>) \<psi>) D'\<close>
proof (rule share_orthogonal_homo.intro, rule sep_orthogonal_monoid_pointwise,
       rule D', rule share_orthogonal_homo.axioms(1)[OF prem], standard)
  interpret xx: share_orthogonal_homo \<psi> D using prem .

  fix x y z a b c :: \<open>'a \<Rightarrow> 'b\<close>
  fix a' :: \<open>'a \<Rightarrow> 'c\<close>
  fix n :: rat

  show \<open>x \<in> D' \<Longrightarrow> mul_carrier (\<psi> \<circ> x)\<close>
    by (simp add: D' sep_disj_fun_def xx.\<psi>_mul_carrier pointwise_set_def)
  
  show \<open>b \<in> D' \<and> c \<in> D' \<Longrightarrow> (\<psi> \<circ> b) ## a' \<Longrightarrow>
       0 < n \<and> n \<le> 1 \<Longrightarrow> (n \<odivr> (\<psi> \<circ> b) * a' = (\<psi> \<circ> c))
                        = (\<exists>a''. a' = (1 - n) \<odivr> (\<psi> \<circ> b) * (\<psi> \<circ> a'') \<and> b * a'' = c \<and> b ## a'' \<and> a'' \<in> D')\<close>
    by (auto simp add: join_sub_def fun_eq_iff times_fun sep_disj_fun_def xx.share_orthogonal
            share_fun_def pointwise_set_def D'; metis)

  show \<open>b \<in> D' \<and> c \<in> D' \<Longrightarrow> (\<psi> \<circ> b) ## a' \<Longrightarrow> 1 < n \<Longrightarrow> \<psi> \<circ> b \<noteq> 1 \<Longrightarrow> n \<odivr> (\<psi> \<circ> b) * a' \<noteq> \<psi> \<circ> c\<close>
    by (clarsimp simp add: fun_eq_iff sep_disj_fun_def times_fun_def share_fun_def,
        metis D' mem_Collect_eq pointwise_set_def xx.share_bounded)

qed

lemma sep_orthogonal_monoid_pointwise_eq:
  \<open>sep_orthogonal_monoid ((\<circ>) \<psi>) (pointwise_set D) \<longleftrightarrow> sep_orthogonal_monoid \<psi> D\<close>
  for \<psi> :: \<open>'b::sep_monoid \<Rightarrow> 'c::sep_monoid\<close>
proof
  assume prem: \<open>sep_orthogonal_monoid ((\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) (pointwise_set D)\<close>
  show \<open>sep_orthogonal_monoid \<psi> D\<close>
  proof
    interpret xx: sep_orthogonal_monoid \<open>(\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close> \<open>(pointwise_set D)\<close> using prem .
    fix x y a b c :: \<open>'b\<close> and a2 :: 'c
    show \<open>x ## y \<Longrightarrow> \<psi> (x * y) = \<psi> x * \<psi> y\<close>
      using xx.homo_mult[unfolded sep_disj_fun_def times_fun one_fun_def fun_eq_iff, simplified]
      by meson
    show \<open>a ## b \<longrightarrow> \<psi> a ## \<psi> b\<close>
      using xx.sep_disj_homo_semi[unfolded sep_disj_fun_def times_fun one_fun_def fun_eq_iff, simplified]
      by meson
    show \<open>1 \<in> D\<close>
      using xx.one_in_D by (auto simp add: pointwise_set_def)
    show \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a2 \<Longrightarrow>
            (\<psi> b * a2 = \<psi> c) = (\<exists>a'. a2 = \<psi> a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
      using xx.sep_orthogonal[unfolded sep_disj_fun_def times_fun one_fun_def fun_eq_iff,
          where a=\<open>\<lambda>_. a2\<close> and b=\<open>\<lambda>_. b\<close> and c=\<open>\<lambda>_. c\<close>, simplified pointwise_set_def, simplified]
      by auto
  qed
next
  show \<open>sep_orthogonal_monoid \<psi> D \<Longrightarrow> sep_orthogonal_monoid ((\<circ>) \<psi>) (pointwise_set D)\<close>
    using sep_orthogonal_monoid_pointwise by blast 
qed

lemma share_orthogonal_homo_pointwise_eq:
  \<open>share_orthogonal_homo ((\<circ>) \<psi>) (pointwise_set D) \<longleftrightarrow> share_orthogonal_homo \<psi> D\<close>
  for \<psi> :: \<open>'b::sep_algebra \<Rightarrow> 'c::share_semimodule\<close>
proof
  assume prem: \<open>share_orthogonal_homo ((\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) (pointwise_set D)\<close>
  show \<open>share_orthogonal_homo \<psi> D\<close>
  proof (rule share_orthogonal_homo.intro[OF share_orthogonal_homo.axioms(1)[OF prem, unfolded sep_orthogonal_monoid_pointwise_eq]],
         standard)
    interpret xx: share_orthogonal_homo \<open>((\<circ>) \<psi> :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c)\<close> \<open>(pointwise_set D)\<close> using prem .
    fix x y a b c :: \<open>'b\<close> and a2 :: 'c and n :: rat

    show \<open> x \<in> D \<Longrightarrow> mul_carrier (\<psi> x) \<close>
      using xx.\<psi>_mul_carrier[of \<open>\<lambda>_. x\<close>, simplified pointwise_set_def, simplified]
      by (auto simp add: sep_disj_fun_def)

    show \<open> b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a2 \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
            (n \<odivr> \<psi> b * a2 = \<psi> c) = (\<exists>a'. a2 = (1 - n) \<odivr> \<psi> b * \<psi> a'\<and> b * a' = c \<and> b ## a' \<and> a' \<in> D)\<close>
      by (insert xx.share_orthogonal[where a=\<open>\<lambda>_. a2\<close> and b=\<open>\<lambda>_. b\<close> and c=\<open>\<lambda>_. c\<close>];
          clarsimp simp add: sep_disj_fun_def share_fun_def fun_eq_iff times_fun pointwise_set_def; rule; auto)

    show \<open>b \<in> D \<and> c \<in> D \<Longrightarrow> \<psi> b ## a2 \<Longrightarrow> 1 < n \<Longrightarrow> \<psi> b \<noteq> 1 \<Longrightarrow> n \<odivr> \<psi> b * a2 \<noteq> \<psi> c\<close>
      by (insert xx.share_bounded[where a=\<open>\<lambda>_. a2\<close> and b=\<open>\<lambda>_. b\<close> and c=\<open>\<lambda>_. c\<close>];
          clarsimp simp add: sep_disj_fun_def share_fun_def fun_eq_iff times_fun pointwise_set_def)

  qed
next
  show \<open>share_orthogonal_homo \<psi> D \<Longrightarrow> share_orthogonal_homo ((\<circ>) \<psi>) (pointwise_set D)\<close>
    using share_orthogonal_homo_pointwise by blast 
qed



subsubsection \<open>Subsumption\<close>

lemma discrete_partial_map_subsumption:
  \<open>f \<preceq>\<^sub>S\<^sub>L g \<Longrightarrow> k \<in> dom1 f \<Longrightarrow> g k = f k\<close>
  for f :: \<open>'k \<Rightarrow> 'v::discrete_monoid\<close>
  unfolding join_sub_def
  apply (clarsimp simp add: times_fun)
  by (simp add: disjoint_iff dom1_def sep_disj_dom1_disj_disjoint)

lemma discrete_1_fupdt_subsumption:
  \<open> 1(k := v) \<preceq>\<^sub>S\<^sub>L objs
\<Longrightarrow> v \<noteq> 1
\<Longrightarrow> objs k = v\<close>
  for v :: \<open>'v::discrete_monoid\<close>
  using discrete_partial_map_subsumption[where f=\<open>1(k := v)\<close>]
  by (clarsimp simp add: times_fun)

lemma discrete_partial_map_subsumption_L2:
  \<open> 1(k := v) \<preceq>\<^sub>S\<^sub>L objs
\<Longrightarrow> v \<subseteq>\<^sub>m objs k\<close>
  for v :: \<open>'b \<Rightarrow> 'c::discrete_semigroup option\<close>
  unfolding join_sub_def map_le_def
  by (clarsimp simp add: times_fun,
      metis fun_upd_same mult_1_class.mult_1_right one_option_def sep_disj_fun_def sep_disj_option_discrete(2))


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

subsubsection \<open>Instantiating Algebraic Properties\<close>

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

instance share :: (type) strict_positive_sep_magma
  by (standard; case_tac a; case_tac b; simp)

instantiation share :: (mul_carrier) mul_carrier begin

definition mul_carrier_share :: \<open>'a share \<Rightarrow> bool\<close>
  where \<open>mul_carrier_share x = (case x of Share n x' \<Rightarrow> 0 < n \<and> mul_carrier x')\<close>

lemma mul_carrier_share[simp]:
  \<open>mul_carrier (Share n x) \<longleftrightarrow> 0 < n \<and> mul_carrier x\<close>
  unfolding mul_carrier_share_def
  by simp

instance ..

end

instance share :: (sep_carrier) sep_carrier
  by (standard; case_tac a; case_tac b; simp)

instance share :: (type) sep_ab_semigroup proof
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

instance share :: (type) sep_disj_distrib
  by (standard; case_tac a; case_tac b; case_tac c; simp)

instantiation share :: (type) share begin

definition share_share :: "rat \<Rightarrow> 'a share \<Rightarrow> 'a share"
  where \<open>share_share n x = (case x of Share m x' \<Rightarrow> Share (n*m) x')\<close>

lemma share_share[simp]: \<open>share n (Share m x) = Share (n*m) x\<close>
  unfolding share_share_def by simp

instance by (standard; case_tac x; simp add: share_share_def mult.assoc mult_le_one)

end

instance share :: (type) share_inj
  by (standard; case_tac x; case_tac y; simp)

instance share :: (sep_carrier) share_nun_semimodule proof
  fix x y :: \<open>'a share\<close>
  fix n n' m :: rat

  show \<open>0 < n \<Longrightarrow> share n x ## y = x ## y\<close>
    by (cases x; cases y; simp add: zero_less_mult_iff)
  show \<open>mul_carrier x \<Longrightarrow> x ## x\<close>
    by (cases x; simp)
  show \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n x * share m x = share (n + m) x\<close>
    by (cases x; cases y; simp add: distrib_right)
  show \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    by (cases x; cases y; simp add: distrib_left)
  show \<open>0 < n \<and> n < 1 \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close>
    by (cases x; cases y; simp add: join_sub_def share_exists;
        metis add.commute add_le_same_cancel1 diff_add_cancel linorder_not_le mult_1_class.mult_1_left mult_less_cancel_right)
  show \<open>0 < n \<Longrightarrow> mul_carrier x \<Longrightarrow> mul_carrier (n \<odivr> x)\<close>
    by (cases x; simp)
qed

instance share :: (type) sep_cancel
  by (standard; case_tac a; case_tac b; case_tac c; simp)


subsubsection \<open>Homomorphism of \<open>map_share\<close>\<close>

lemma homo_sep_disj_map_share[simp]:
  \<open> homo_sep_disj (map_share f)\<close>
  unfolding homo_sep_disj_def
  by (clarsimp simp add: share_forall)

lemma closed_homo_sep_disj_map_share[simp]:
  \<open> inj f
\<Longrightarrow> closed_homo_sep_disj (map_share f) \<close>
  unfolding closed_homo_sep_disj_def inj_def
  by (clarsimp simp add: share_forall; blast)

lemma homo_sep_mult_map_share[simp]:
  \<open> homo_sep_mult (map_share f) \<close>
  unfolding homo_sep_mult_def
  by (clarsimp simp add: share_forall)

lemma homo_sep_map_share[simp]:
  \<open> homo_sep (map_share f) \<close>
  unfolding homo_sep_def
  by clarsimp

lemma closed_homo_sep_map_share[simp]:
  \<open> inj f
\<Longrightarrow> closed_homo_sep (map_share f) \<close>
  unfolding closed_homo_sep_def
  by (clarsimp simp add: share_forall)

subsubsection \<open>\<open>Share\<close> as an Embedding Homomorphism\<close>

lemma homo_mul_carrier_Share_discrete[simp]:
  \<open> 0 < n \<Longrightarrow> homo_mul_carrier (Share n) \<close>
  unfolding homo_mul_carrier_def
  by clarsimp

lemma homo_sep_disj_Share_discrete[simp]:
  \<open> 0 < n \<Longrightarrow> homo_sep_disj (Share n :: 'a::discrete_semigroup \<Rightarrow> 'a share) \<close>
  unfolding homo_sep_disj_def
  by clarsimp

lemma
  \<open> 0 < n \<Longrightarrow> closed_homo_sep_disj (Share n) \<close>
  unfolding closed_homo_sep_disj_def
  apply clarsimp (*TODO: maybe we shall introduce an 'agreement' class?*)
  oops

lemma homo_sep_mult_Share_discrete[simp]:
  \<open> 0 < n \<Longrightarrow> homo_sep_mult (Share n :: 'a::discrete_semigroup \<Rightarrow> 'a share) \<close>
  unfolding homo_sep_mult_def
  by clarsimp

lemma homo_sep_Share_discrete[simp]:
  \<open> 0 < n \<Longrightarrow> homo_sep (Share n :: 'a::discrete_semigroup \<Rightarrow> 'a share) \<close>
  unfolding homo_sep_def
  by clarsimp



subsubsection \<open>Convert a function to sharing or back\<close>

abbreviation \<open>to_share \<equiv> map_option (Share 1)\<close>
abbreviation \<open>strip_share \<equiv> map_option share.val\<close>

lemma share_orthogonal_homo_to_share[locale_witness]:
  \<open>share_orthogonal_homo (to_share::'a::{sep_carrier, discrete_semigroup} option \<Rightarrow> 'a share option) (Collect mul_carrier)\<close>
proof
  fix x y z a b c :: \<open>'a option\<close>
  fix xx yy aa bb cc :: \<open>'a\<close>
  fix a' a2 :: \<open>'a share option\<close>
  fix n :: rat
  show \<open>x ## y \<Longrightarrow> to_share (x * y) = to_share x * to_share y\<close> by (cases x; cases y; simp)
  show \<open>a ## b \<longrightarrow> to_share a ## to_share b\<close> by simp
  show \<open>b \<in> Collect mul_carrier \<and> c \<in> Collect mul_carrier \<Longrightarrow>
        to_share b ## a' \<Longrightarrow>
       (to_share b * a' = to_share c) = (\<exists>a. a' = to_share a \<and> b * a = c \<and> b ## a \<and> a \<in> Collect mul_carrier)\<close>
    apply (cases a'; cases b; cases c; simp add: split_option_ex)
    subgoal for a'' by (cases a''; simp) .
  show \<open>(1::'a option) \<in> Collect mul_carrier\<close> by simp
  (* show \<open>inj to_share\<close>
    by (rule, simp, metis option.inj_map_strong share.inject) *)
  show \<open>x \<in> Collect mul_carrier \<Longrightarrow> mul_carrier (to_share x)\<close> by (cases x; simp)
  show \<open>b \<in> Collect mul_carrier \<and> c \<in> Collect mul_carrier \<Longrightarrow>
        to_share b ## a2 \<Longrightarrow> 0 < n \<and> n \<le> 1 \<Longrightarrow>
        (n \<odivr> to_share b * a2 = to_share c) = (\<exists>a'. a2 = (1 - n) \<odivr> to_share b * to_share a' \<and> b * a' = c \<and> b ## a' \<and> a' \<in> Collect mul_carrier)\<close>
    apply (cases a2; cases b; cases c; simp add: share_option_def)
    apply (cases \<open>n < 1\<close>; simp)
    apply (smt (verit, ccfv_SIG) diff_add_cancel diff_gt_0_iff_gt sep_cancel sep_disj_commuteI sep_disj_multD2 sep_disj_multI2 sep_disj_share sep_mult_commute times_share)
    by (metis join_strict_positivity sep_disj_distrib_left sep_disj_share zero_less_one)

  show \<open>b \<in> Collect mul_carrier \<and> c \<in> Collect mul_carrier \<Longrightarrow> to_share b ## a2 \<Longrightarrow> 1 < n \<Longrightarrow> to_share b \<noteq> 1 \<Longrightarrow>
        n \<odivr> to_share b * a2 \<noteq> to_share c\<close>
    by (cases a2; cases b; cases c; simp; case_tac a; simp)
  
qed


lemma to_share_kernel_is_1[locale_witness]:
  \<open> 1 \<in> D
\<Longrightarrow> simple_homo_mul to_share D\<close>
  by (simp add: simple_homo_mul_def)

lemma strip_share_Share[simp]:
  \<open>strip_share (map_option (Share n) x) = x\<close>
  by (cases x; simp)

lemma map_option_funcomp_1[simp]:
  \<open>map_option f o 1 = 1\<close>
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

lemma map_option_funcomp_map_add:
  \<open>(map_option f o (g ++ h)) = (map_option f o g) ++ (map_option f o h)\<close>
  unfolding fun_eq_iff map_add_def by (clarsimp simp add: fun_eq_iff split: option.split)

(* lemma to_share_funcomp_map_add: (*deprecated*)
  \<open>to_share o (f ++ g) = (to_share o f) ++ (to_share o g)\<close>
  unfolding fun_eq_iff map_add_def by (auto split: option.split) *)


lemma to_share_wand_homo:
  \<open> a ## (to_share o b)
\<Longrightarrow> a * (to_share o b) = to_share \<circ> y
\<longleftrightarrow> (\<exists>a'. a = to_share o a' \<and> a' * b = y \<and> a' ## b)\<close>
  for a :: \<open>'a \<Rightarrow> 'b::discrete_semigroup share option\<close>
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
  for a :: \<open>'a \<Rightarrow> 'b::discrete_semigroup option\<close>
  unfolding sep_disj_fun_def apply simp
   apply clarsimp subgoal premises prems for x
    apply (insert prems[THEN spec[where x=x]])
    by (cases \<open>a x\<close>; cases \<open>b x\<close>; simp) .

lemma pointwise_to_share_bij[simp]:
  \<open>to_share \<circ> x = to_share \<circ> y \<longleftrightarrow> x = y\<close>
  unfolding fun_eq_iff
  by (simp, metis strip_share_Share)


subsection \<open>Non-sepable Semigroup\<close>

(*TODO: rename this to discrete injector or other*)

datatype 'a discrete = discrete (dest: 'a)
hide_const (open) dest

lemma split_discrete_all: \<open>All P \<longleftrightarrow> (\<forall>x. P (discrete x))\<close> by (metis discrete.exhaust)
lemma split_discrete_ex : \<open>Ex P \<longleftrightarrow> (\<exists>x. P (discrete x))\<close> by (metis discrete.exhaust)
lemma split_discrete_ExSet: \<open>ExSet P = (\<exists>*x. P (discrete x))\<close>
  unfolding set_eq_iff ExSet_expn_set split_discrete_ex by simp
lemma split_discrete_meta_all: \<open>Pure.all P \<equiv> (\<And>x. PROP P (discrete x))\<close>
proof
  fix x
  assume \<open>\<And>x. PROP P x\<close>
  then show \<open>PROP P (discrete x)\<close> .
next
  fix x :: \<open>'a discrete\<close>
  assume \<open>(\<And>x. PROP P (discrete x))\<close>
  note this[of \<open>discrete.dest x\<close>, simplified]
  then show \<open>PROP P x\<close> .
qed

lemma inj_discrete[simp]:
  \<open>inj discrete\<close>
  unfolding inj_def by simp

instantiation discrete :: (type) discrete_semigroup begin
definition \<open>sep_disj_discrete (x :: 'a discrete) (y :: 'a discrete) = False\<close>
definition share_discrete :: \<open>rat \<Rightarrow> 'a discrete \<Rightarrow> 'a discrete\<close>
  where [simp]: \<open>share_discrete _ x = x\<close>
definition times_discrete :: \<open>'a discrete \<Rightarrow> 'a discrete \<Rightarrow> 'a discrete\<close>
  where [simp]: \<open>times_discrete x y = undefined\<close>
instance by (standard; case_tac x; simp; case_tac y; simp add: sep_disj_discrete_def)
end

instantiation discrete :: (type) sep_carrier begin
definition mul_carrier_discrete :: \<open>'a discrete \<Rightarrow> bool\<close>
  where [simp]: \<open>mul_carrier_discrete = (\<lambda>_. True)\<close>
instance by (standard; simp)
end

instance discrete :: (type) sep_cancel by (standard; case_tac a; case_tac b; case_tac c; simp)

instance discrete :: (type) sep_disj_distrib by (standard; case_tac a; case_tac b; case_tac c; simp)

instance discrete :: (type) ab_semigroup_mult
  by (standard; case_tac a; case_tac b; simp)

instance discrete :: (type) strict_positive_sep_magma
  by (standard; case_tac a; case_tac b; simp)


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

instantiation agree :: (mul_carrier) mul_carrier begin

definition mul_carrier_agree :: \<open>'a agree \<Rightarrow> bool\<close>
  where \<open>mul_carrier_agree = pred_agree mul_carrier\<close>

lemma mul_carrier_agree:
  \<open>mul_carrier (agree x) \<longleftrightarrow> mul_carrier x\<close>
  unfolding mul_carrier_agree_def
  by simp

instance ..
end

instance agree :: (sep_carrier) sep_carrier
  by (standard; simp)

instantiation agree :: (sep_carrier) share_nun_semimodule begin

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
  show \<open>0 < n \<and> n < 1 \<Longrightarrow> mul_carrier x \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x \<or> share n x = x\<close> by (cases x; simp)
  show \<open>x ## y \<Longrightarrow> y ## x\<close> by (cases x; cases y; simp)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> y ## z\<close> by (cases x; cases y; cases z; simp)
  show \<open>x * y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y * z\<close> by (cases x; cases y; cases z; simp)
  show \<open>0 < n \<Longrightarrow> share n x ## y = x ## y\<close> by (cases x; cases y; simp)
  show \<open>mul_carrier x \<Longrightarrow> x ## x\<close> by (cases x; simp)
  show \<open>0 < n \<Longrightarrow> mul_carrier x \<Longrightarrow> mul_carrier (n \<odivr> x)\<close> by (cases x; simp)
qed
end

instance agree :: (type) sep_disj_distrib
  by (standard; case_tac a; case_tac b; case_tac c; simp)

instance agree :: (type) sep_cancel
  by (standard; case_tac a; case_tac c; case_tac b; simp)



end