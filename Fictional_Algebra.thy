theory Fictional_Algebra
  imports Main HOL.Rat "Statespace/StateFun"
    NoePreliminary
  keywords "fiction_space" :: thy_decl
    and "resource_space" :: thy_defn
  abbrevs "!!" = "!!"
begin


chapter \<open>First Order Fictional Algebra\<close>

section \<open>Algebra Structures\<close>

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

class sep_disj =
  fixes sep_disj :: "'a => 'a => bool" (infix "##" 60)
  assumes sep_disj_commuteI: "x ## y \<Longrightarrow> y ## x"
begin
lemma sep_disj_commute: "x ## y \<longleftrightarrow> y ## x"
  by (blast intro: sep_disj_commuteI)
end

class pre_sep_ab_semigroup = sep_disj + times
begin
definition join_sub (infix "\<preceq>\<^sub>S\<^sub>L" 50) 
  where \<open>join_sub y z \<longleftrightarrow> (\<exists>x. z = x * y \<and> x ## y)\<close>
end

class sep_ab_semigroup = pre_sep_ab_semigroup +
  assumes sep_mult_commute: "x ## y \<Longrightarrow> x * y = y * x"
  assumes sep_mult_assoc:
    "\<lbrakk> x ## y; y ## z; x ## z \<rbrakk> \<Longrightarrow> (x * y) * z = x * (y * z)"
  assumes join_positivity: \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>

class cancl_sep_ab_semigroup = sep_ab_semigroup +
  assumes sep_disj_multD1: "\<lbrakk> x ## y * z; y ## z \<rbrakk> \<Longrightarrow> x ## y"
  assumes sep_disj_multI1: "\<lbrakk> x ## z; y ## z \<rbrakk> \<Longrightarrow> x * y ##  z"
begin
lemma sep_disj_multD2: "\<lbrakk> x ## y * z; y ## z \<rbrakk> \<Longrightarrow> x ## z"
  by (metis local.sep_disj_commute local.sep_disj_multD1 local.sep_mult_commute)
end

class sep_disj_one = sep_disj + mult_1 +
  assumes sep_disj_one [simp]: "x ## 1"
begin

lemma sep_disj_one' [simp]: "1 ## x"
  using local.sep_disj_one sep_disj_commute by blast

end

class pre_sep_algebra = sep_disj_one + sep_ab_semigroup

lemma sep_no_negative [simp]:
  \<open>x ## y \<Longrightarrow> x * y = 1 \<longleftrightarrow> x = 1 \<and> y = 1\<close>
  for x :: \<open>'a::pre_sep_algebra\<close>
  by (metis join_positivity join_sub_def mult_1_class.mult_1_right sep_disj_one)

lemma sep_mult_left_commute[simp]:
  fixes a :: \<open>'a::pre_sep_algebra\<close>
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

declare sep_mult_assoc[simp]

class sep_algebra = pre_sep_algebra + cancl_sep_ab_semigroup

class discrete_sep_semigroup = sep_disj + times +
  assumes discrete_sep_disj[simp]: "x ## y \<longleftrightarrow> x = y"
    and discrete_mult[simp]: "x * y = (if x = y then x else undefined)"
begin
subclass pre_sep_ab_semigroup ..
subclass sep_ab_semigroup proof
  fix x y z :: 'a
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by simp 
  show \<open>x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x * y * z = x * (y * z)\<close> by simp
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    using local.join_sub_def by force
qed
end

class nonsepable_semigroup = sep_disj + times +
  assumes nonsepable_disj[simp]: "\<not> x ## y"
begin
subclass pre_sep_ab_semigroup ..
subclass sep_ab_semigroup by (standard; simp add: local.join_sub_def)
subclass cancl_sep_ab_semigroup by standard simp_all
end

class nonsepable_monoid = sep_disj_one +
  assumes nonsepable_disj_1[simp]: \<open>x ## y \<longleftrightarrow> x = 1 \<or> y = 1\<close>
begin
subclass pre_sep_ab_semigroup ..
subclass sep_algebra proof
  fix x y z :: 'a
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by fastforce
  show \<open>x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x * y * z = x * (y * z)\<close> by fastforce
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close>
    by (metis local.mult_1_right local.nonsepable_disj_1)
  show \<open>x ## z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close> by fastforce
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def apply clarsimp
    by (metis local.mult_1_left)
qed
end


locale homo_sep_disj =
  fixes \<psi> :: \<open>'a::sep_disj \<Rightarrow> 'b::sep_disj\<close>
  assumes sep_disj_homo[simp]: \<open>\<psi> a ## \<psi> b \<longleftrightarrow> a ## b\<close>

class share =
  fixes share :: \<open>pos0rat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes share_share_not0: \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n (share m x) = share (n * m) x\<close>
    and   share_left_one[simp]:  \<open>share 1 x = x\<close>

class share_one = share + one +
  assumes share_right_one[simp]: \<open>share n 1 = 1\<close>
    and   share_left_0[simp]:    \<open>share 0 x = 1\<close>
begin
lemma share_share: \<open>share n (share m x) = share (n * m) x\<close>
  by (metis local.share_left_0 local.share_right_one local.share_share_not0 mult_not_zero order_le_less pos0rat_LE0)
end

class share_one_eq_one_iff = share_one +
  assumes share_one_eq_one_iff[simp]: \<open>0 < n \<Longrightarrow> share n x = 1 \<longleftrightarrow> x = 1\<close>

class share_sep_disj = share + sep_disj +
  assumes share_sep_disj_left_L0[simp]: \<open>0 < n \<Longrightarrow> share n x ## y \<longleftrightarrow> x ## y\<close>
(*    and   share_sep_disj_refl[simp]:  \<open>n \<noteq> 0 \<Longrightarrow> m \<noteq> 0 \<Longrightarrow> share n x ## share m x\<close> *)
begin

(* lemma share_sep_disj_refl_1 [simp]:
  \<open>m \<noteq> 0 \<Longrightarrow> x ## share m x\<close>  \<open>m \<noteq> 0 \<Longrightarrow> share m x ## x\<close>
  by (metis share_left_one share_sep_disj_refl)+ *)
  
lemma share_sep_disj_right_L0[simp]: \<open>0 < n \<Longrightarrow> x ## share n y \<longleftrightarrow> x ## y\<close>
  using local.share_sep_disj_left_L0 sep_disj_commute by force

end

class share_semimodule_sep = share_sep_disj + sep_ab_semigroup +
  assumes share_sep_left_distrib_0:  \<open>0 < n \<Longrightarrow> 0 < m \<Longrightarrow> share n x * share m x = share (n+m) x\<close>
    and   share_sep_right_distrib_0: \<open>0 < n \<Longrightarrow> x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
    and   share_sub: \<open>n \<le> 1 \<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L x\<close>

class share_module_sep = share_sep_disj + share_one + pre_sep_algebra +
  assumes share_sep_left_distrib:  \<open>share n x * share m x = share (n+m) x\<close>
    and   share_sep_right_distrib: \<open>x ## y \<Longrightarrow> share n x * share n y = share n (x * y)\<close>
begin

subclass share_semimodule_sep
  by standard (simp_all add: local.share_sep_left_distrib share_sep_right_distrib) 

end

class share_semimodule_mult = share_one + monoid_mult +
  assumes share_left_distrib:  \<open>share n x * share m x = share (n+m) x\<close>
    and   share_right_distrib: \<open>share n x * share n y = share n (x * y)\<close>


(* class unital_mult = plus + one +
  assumes unital_add_left[simp]: "1 * x = x"
    and unital_add_right[simp]: "x * 1 = x"

subclass (in monoid_mult) unital_mult .. simp_all *)

section \<open>Algebra\<close>

subsection \<open>Subsumption\<close>


definition join_sub_strict :: \<open>'a::sep_ab_semigroup \<Rightarrow> 'a::sep_ab_semigroup \<Rightarrow> bool\<close> (infix "\<prec>\<^sub>S\<^sub>L" 50) 
  where \<open>join_sub_strict y z \<longleftrightarrow> join_sub y z \<and> y \<noteq> z\<close>

print_locale order_bot


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
    by (metis sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_mult_ac(1))
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_strict_def join_sub_def
    using \<open>(x \<prec>\<^sub>S\<^sub>L y) = (x \<preceq>\<^sub>S\<^sub>L y \<and> \<not> y \<preceq>\<^sub>S\<^sub>L x)\<close> join_sub_def join_sub_strict_def by blast
qed

interpretation join_sub: order_bot 1 \<open>join_sub::'a::sep_algebra \<Rightarrow> 'a \<Rightarrow> bool\<close> join_sub_strict
proof
  fix a :: 'a
  show \<open>1 \<preceq>\<^sub>S\<^sub>L a\<close>
    unfolding join_sub_strict_def join_sub_def
    by force
qed

lemma
  \<open> x \<preceq>\<^sub>S\<^sub>L y
\<Longrightarrow> 0 < n
\<Longrightarrow> n \<le> 1
\<Longrightarrow> share n x \<preceq>\<^sub>S\<^sub>L y\<close>
  for x :: \<open>'a::{share_semimodule_sep,cancl_sep_ab_semigroup}\<close>
  unfolding join_sub_def
  apply clarsimp
  apply (cases \<open>n = 1\<close>, simp, blast)
  subgoal premises prems for a proof -
    have t1[simp]: \<open>0 < 1 - n\<close>
      by (metis add.commute add_0 le_add_diff_inverse order_le_imp_less_or_eq pos0rat_LE0 prems(2) prems(5))
    have t2: \<open>a ## share (1 - n) x\<close>
      using prems(3) share_sep_disj_right_L0 t1 by blast
    have t3: \<open>a * share (1 - n) x ## x\<close>
      by (simp add: prems(3) sep_disj_multI1)
    show ?thesis
      apply (rule exI[where x=\<open>a * share (1-n) x\<close>])
      by (metis add.commute le_add_diff_inverse prems(1) prems(2) sep_mult_assoc share_left_one share_sep_disj_refl share_sep_disj_right_L0 share_sep_left_distrib_0 t1 t2 t3)
  qed .




section \<open>Instances of Algebras\<close>

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

instantiation option :: (sep_disj) sep_disj begin

definition "sep_disj_option x' y' =
  (case x' of Some x \<Rightarrow> (case y' of Some y \<Rightarrow> x ## y | _ \<Rightarrow> True) | _ \<Rightarrow> True)"

lemma sep_disj_option[simp]:
    "Some x ## Some y \<longleftrightarrow> x ## y"
    "None ## z" "z ## None"
  unfolding sep_disj_option_def by (cases z, simp_all)+
instance by standard (case_tac x; case_tac y; simp add: sep_disj_commute)

end

lemma sep_disj_option_nonsepable[simp]:
  \<open>x ## Some y \<longleftrightarrow> x = None\<close> \<open>Some y ## x \<longleftrightarrow> x = None\<close>
  for y :: \<open>'a :: nonsepable_semigroup\<close>
  by (cases x; simp)+

instantiation option :: (pre_sep_ab_semigroup) pre_sep_ab_semigroup begin
instance ..
end

instantiation option :: (sep_ab_semigroup) sep_ab_semigroup begin
instance proof
  fix x y z :: \<open>'a option\<close>
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by (cases x; cases y; simp add: sep_disj_commute sep_mult_commute)
  show \<open>x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x * y * z = x * (y * z)\<close>
    by (cases x; cases y; cases z; simp add: sep_disj_commute sep_mult_commute)

  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def
    apply (cases x; clarsimp simp add: sep_disj_commute sep_mult_commute;
           cases y; clarsimp simp add: sep_disj_commute sep_mult_commute)
    apply (metis times_option_not_none(1))
     apply (metis times_option_not_none(1))
    subgoal for _ u v _ apply (cases u; cases v; simp)
      by (metis join_positivity join_sub_def) .
  qed
end

instantiation option :: (sep_ab_semigroup) pre_sep_algebra begin
instance proof
  fix x y :: \<open>'a option\<close>
  show \<open>1 * x = x\<close> by simp
  show \<open>x * 1 = x\<close> by simp
  show \<open>x ## 1\<close> by simp
qed
end

instantiation option :: (cancl_sep_ab_semigroup) cancl_sep_ab_semigroup begin
instance apply (standard; case_tac x; simp_all; case_tac y; simp_all; case_tac z; simp_all)
  using sep_disj_multD1 apply blast
  using sep_disj_commuteI sep_disj_multI1 by blast
end

instantiation option :: (cancl_sep_ab_semigroup) sep_algebra begin
instance ..
end

instantiation option :: (share) share begin

definition \<open>share_option n = (if 0 < n then map_option (share n) else (\<lambda>_. None))\<close>

lemma share_option_simps[simp]:
  \<open>share n None = None\<close> \<open>share 0 x = None\<close> \<open>0 <n \<Longrightarrow> share n (Some x') = Some (share n x')\<close>
  unfolding share_option_def by simp_all

instance by (standard; simp add: share_option_def; case_tac x; simp add: share_share_not0)
end

instantiation option :: (share) share_one_eq_one_iff begin
instance by (standard; simp add: share_option_def; case_tac x; simp)
end

instantiation option :: (share_sep_disj) share_sep_disj begin
instance by (standard; case_tac x; simp add: share_option_def; case_tac y;
             simp add: share_sep_left_distrib_0 order_less_le)
end

instantiation option :: (share_semimodule_sep) share_module_sep begin
instance apply standard
   apply (case_tac x; simp add: share_option_def share_sep_left_distrib_0 order_less_le)
   by (case_tac x; case_tac y; simp add: share_option_def share_sep_right_distrib_0)
end

instantiation option :: (times) no_inverse begin
instance by (standard, case_tac a; case_tac b; simp)
end

lemma times_option_none[simp]:
  \<open>x * y = None \<longleftrightarrow> x = None \<and> y = None\<close>
  using no_inverse one_option_def by metis

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
instance by standard (simp_all add: pair_All algebra_simps)
end

instantiation prod :: (monoid_mult, monoid_mult) monoid_mult begin
instance by standard (simp_all add: one_prod_def pair_All algebra_simps)
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


instantiation "fun" :: (type, no_inverse) no_inverse begin
instance by (standard, simp add: one_fun_def times_fun_def fun_eq_iff, blast) 
end

instantiation "fun" :: (type, no_negative) no_negative begin
instance by (standard, simp add: zero_fun_def plus_fun_def fun_eq_iff, blast) 
end

instantiation "fun" :: (type, semigroup_mult) semigroup_mult begin
instance apply standard
  by (simp add: mult.assoc times_fun_def) 
end

instantiation "fun" :: (type,sep_disj) sep_disj begin
definition "sep_disj_fun m1 m2 = (\<forall>x. m1 x ## m2 x)"
instance by standard (simp_all add: sep_disj_fun_def times_fun_def fun_eq_iff
                               add: sep_disj_commute sep_mult_commute)
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

instantiation "fun" :: (type,pre_sep_ab_semigroup) pre_sep_ab_semigroup begin
instance ..
end

instantiation "fun" :: (type,sep_ab_semigroup) sep_ab_semigroup begin
instance proof (standard; simp_all add: sep_disj_fun_def times_fun_def fun_eq_iff
                               add: sep_disj_commute sep_mult_commute)
  fix x y :: "'a \<Rightarrow> 'b"
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> \<forall>xa. x xa = y xa\<close>
    unfolding join_sub_def apply (clarsimp simp add: times_fun)
    by (metis join_positivity join_sub_def sep_disj_fun times_fun_def)
qed
end

instantiation "fun" :: (type,pre_sep_algebra) pre_sep_algebra begin
instance by (standard; simp add: sep_disj_fun_def fun_eq_iff times_fun_def; blast)
end

instantiation "fun" :: (type,sep_algebra) sep_algebra begin
instance apply standard
  apply (simp_all add: sep_disj_fun_def times_fun_def fun_eq_iff)
  using sep_disj_multD1 apply blast
  using sep_disj_commute sep_disj_multI1 by blast
end

instantiation "fun" :: (type,monoid_mult) monoid_mult begin
instance by standard (simp_all add: mult.commute times_fun_def fun_eq_iff)
end

instantiation "fun" :: (type,comm_monoid_mult) comm_monoid_mult begin
instance by standard (simp_all add: mult.commute times_fun_def fun_eq_iff)

paragraph \<open>Multiplication with Function Update\<close>

lemmas fun_mult_norm = mult.assoc[where ?'a = "'a \<Rightarrow> 'b", symmetric]

lemma [simp]: "(f * 1(k := x)) k = f k * x" for f :: "'a \<Rightarrow> 'b"
  by (simp add: times_fun_def)

lemma [simp]: "k' \<noteq> k \<Longrightarrow> (f * 1(k':=x)) k = f k" for f :: "'a \<Rightarrow> 'b"
  by (simp add: times_fun_def)

lemma [simp]: "(f * 1(k := x))(k:=1) = f(k:=1)" for f :: "'a \<Rightarrow> 'b"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma [simp]: "k' \<noteq> k \<Longrightarrow> (f * 1(k' := x))(k:=1) = f(k:=1) * 1(k' := x)" for f :: "'a \<Rightarrow> 'b"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp
end

lemma fun_split_1: "f = f(k:=1) * 1(k:= f k)" for f :: "'a \<Rightarrow> 'b :: mult_1"
  unfolding fun_upd_def fun_eq_iff times_fun_def by simp

lemma fun_1upd1[simp]:
  "1(k := 1) = 1"
  unfolding one_fun_def fun_upd_def by simp

lemma fun_1upd_homo:
    "1(k := x) * 1(k := y) = 1(k := x * y)" for x :: "'a::pre_sep_algebra"
  unfolding one_fun_def fun_upd_def times_fun_def
  by fastforce

lemma fun_1upd_homo_right1:
    "f(k := x) * 1(k := y) = f(k := x * y)" for x :: "'a::pre_sep_algebra"
  unfolding one_fun_def fun_upd_def times_fun_def fun_eq_iff
  by clarsimp

lemma fun_1upd_homo_left1:
    "1(k := x) * f(k := y) = f(k := x * y)" for x :: "'a::comm_monoid_mult"
  unfolding one_fun_def fun_upd_def times_fun_def fun_eq_iff
  by clarsimp

lemma [simp]: "NO_MATCH (a::'a) (1::'a::one) \<Longrightarrow> i \<noteq> k \<Longrightarrow> f(i := a, k := 1) = f(k := 1, i := a)"
  using fun_upd_twist .


paragraph \<open>Share\<close>

instantiation "fun" :: (type, share) share begin

definition share_fun :: \<open>pos0rat \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close>
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

instantiation "fun" :: (type, share_semimodule_sep) share_semimodule_sep begin
instance by (standard; simp add: share_fun_def fun_eq_iff sep_disj_fun_def times_fun_def
             share_sep_left_distrib_0 share_sep_right_distrib_0)
end

instantiation "fun" :: (type, share_module_sep) share_module_sep begin
instance by standard (simp_all add: share_fun_def fun_eq_iff times_fun_def share_sep_left_distrib
      sep_disj_fun_def share_sep_right_distrib)
end

instantiation "fun" :: (type, share_semimodule_mult) share_semimodule_mult begin
instance by standard (simp_all add: share_fun_def fun_eq_iff times_fun_def share_left_distrib share_right_distrib)
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

instantiation unit :: no_inverse begin
instance by standard simp_all
end

instantiation unit :: no_negative begin
instance by standard simp_all
end


subsection \<open>Set\<close>

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

lemma times_set_I:
  \<open>x \<in> P \<Longrightarrow> y \<in> Q \<Longrightarrow> x * y \<in> P * Q\<close>
  unfolding times_set_def by simp blast

lemma set_mult_zero[iff]: "{} * S = {}" "S * {} = {}"
  unfolding times_set_def by simp_all

lemma set_mult_single: \<open>{A} * {B} = {A * B}\<close>
  unfolding times_set_def set_eq_iff by simp

lemma set_mult_expn[\<phi>expns]:
  \<open>uv \<in> (S * T) \<longleftrightarrow> (\<exists>u v. uv = u * v \<and> u \<in> S \<and> v \<in> T)\<close>
  unfolding times_set_def by simp

lemma set_mult_inhabited[elim!]:
  \<open>Inhabited (S * T) \<Longrightarrow> (Inhabited S \<Longrightarrow> Inhabited T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def times_set_def by simp

lemma times_set_subset[intro, simp]:
  \<open>B \<subseteq> B' \<Longrightarrow> A * B \<subseteq> A * B'\<close>
  \<open>B \<subseteq> B' \<Longrightarrow> B * A \<subseteq> B' * A\<close>
  unfolding subset_iff times_set_def by simp_all blast+

instantiation set :: (times) mult_zero begin
instance by standard (simp_all add: zero_set_def)
end

instantiation set :: (no_inverse) no_inverse begin
instance by (standard, simp add: one_set_def times_set_def set_eq_iff) (metis no_inverse)
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

instantiation set :: (semigroup_mult) ordered_semiring_0 begin
instance by standard (auto simp add: zero_set_def plus_set_def times_set_def)
end

instantiation set :: (monoid_mult) semiring_1 begin
instance by standard (auto simp add: zero_set_def plus_set_def times_set_def)
end

instantiation set :: (ab_semigroup_mult) ordered_comm_semiring begin
instance apply standard
  apply (simp add: zero_set_def plus_set_def times_set_def)
  using mult.commute apply blast
   apply (simp add: distrib_right)
  by simp
end

instantiation set :: (comm_monoid_mult) comm_semiring_1 begin
instance by standard (auto simp add: zero_set_def plus_set_def times_set_def)
end

subsection \<open>Partial Map\<close>

lemma one_partial_map: \<open>1 = Map.empty\<close>
  unfolding one_fun_def one_option_def ..

lemma times_fun_map_add_right:
  \<open>dom f \<inter> dom h = {} \<Longrightarrow> (f * g) ++ h = f * (g ++ h)\<close>
  unfolding times_fun_def fun_eq_iff map_add_def
  by (simp add: disjoint_iff domIff option.case_eq_if times_option_def)

paragraph \<open>Separation Disjunction\<close>

lemma sep_disj_partial_map_del:
  \<open>f ## g \<Longrightarrow> f ## g(k := None)\<close>
  unfolding sep_disj_fun_def sep_disj_option_def
  by (metis fun_upd_apply option.case_eq_if)

lemma sep_disj_partial_map_disjoint:
  "f ## g \<longleftrightarrow> dom f \<inter> dom g = {}"
  for f :: "'a \<rightharpoonup> ('b :: nonsepable_semigroup)"
  unfolding sep_disj_fun_def sep_disj_option_def disjoint_iff
  by (metis (no_types, lifting) domIff nonsepable_disj option.case_eq_if)

lemma sep_disj_partial_map_some_none:
  \<open>f ## g \<Longrightarrow> g k = Some v \<Longrightarrow> f k = None\<close>
  for f :: "'a \<rightharpoonup> ('b :: nonsepable_semigroup)"
  using disjoint_iff sep_disj_partial_map_disjoint by fastforce

lemma sep_disj_partial_map_upd:
  \<open>f ## g \<Longrightarrow> k \<in> dom g \<Longrightarrow> (f * g)(k := v) = (f * g(k:=v))\<close>
  for f :: "'a \<rightharpoonup> ('b :: nonsepable_semigroup)"
  unfolding sep_disj_partial_map_disjoint fun_upd_def times_fun fun_eq_iff
  by simp (metis disjoint_iff domIff times_option(3))

lemma nonsepable_semigroup_sepdisj_fun:
  \<open>a ## 1(k \<mapsto> x) \<Longrightarrow> a ## 1(k := any)\<close>
  for x :: \<open>'b::nonsepable_semigroup\<close>
  unfolding sep_disj_fun_def
  apply clarify subgoal premises prems for x
    apply (insert prems[THEN spec[where x=x]])
    by (cases \<open>a x\<close>; simp; cases "x = k"; simp) .

lemma fun_sep_disj_fupdt[simp]:
  \<open>f1 ## f2 \<Longrightarrow> x1 ## x2 \<Longrightarrow> f1(k := x1) ## f2(k := x2)\<close>
  unfolding sep_disj_fun_def by simp

lemma fun_sep_disj_1_fupdt[simp]:
  \<open>f(k := x1) ## 1(k := x2) \<longleftrightarrow> x1 ## x2\<close>
  \<open>1(k := x1) ## f(k := x2) \<longleftrightarrow> x1 ## x2\<close>
  for x1 :: \<open>'b :: sep_disj_one\<close>
  unfolding sep_disj_fun_def by simp_all


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

lemma dom1_disjoint_sep_disj:
  \<open>dom1 g \<inter> dom1 f = {} \<Longrightarrow> g ## f\<close>
  for f :: \<open>'a \<Rightarrow> 'b::sep_disj_one\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff
  by simp (metis sep_disj_one sep_disj_one')

lemma dom1_mult: \<open>f ## g \<Longrightarrow> dom1 (f * g) = dom1 f \<union> dom1 g\<close>
  for f :: \<open>'a \<Rightarrow> 'b :: {no_inverse,sep_disj}\<close>
  unfolding sep_disj_fun_def dom1_def set_eq_iff times_fun by simp

lemma dom_mult: \<open>f ## g \<Longrightarrow> dom (f * g) = dom f \<union> dom g\<close>
  using dom1_mult dom1_dom by metis

lemma dom1_mult_disjoint: \<open>dom1 (f * g) = dom1 f \<union> dom1 g\<close>
  for f :: \<open>'a \<Rightarrow> 'b :: no_inverse\<close>
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


subsection \<open>Partiality\<close>


datatype 'a fine ("_ ?" [100] 101) = Fine (the_fine: 'a) | Undef
notation the_fine ("!!_" [1000] 1000)

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

instantiation fine :: (sep_disj_one) mult_1 begin
instance by (standard; case_tac x; simp add: one_fine_def times_fine_def)
end


instantiation fine :: ("{sep_disj,times}") mult_zero begin
instance by standard (simp_all add: times_fine)
end

instantiation fine :: (cancl_sep_ab_semigroup) ab_semigroup_mult begin
instance apply (standard; case_tac a; simp add: sep_disj_commute sep_mult_commute times_fine;
                          case_tac b; simp add: sep_disj_commute sep_mult_commute times_fine;
                          case_tac c; simp add: times_fine)
  by (metis sep_disj_commuteI sep_disj_multD1 sep_disj_multI1 sep_mult_assoc sep_mult_commute)
end

instantiation fine :: (sep_algebra) comm_monoid_mult begin
instance by standard (case_tac a; simp add: one_fine_def times_fine)
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


subsection \<open>Fractional SA\<close>

datatype 'a share = Share posrat (val: 'a) (infix "\<Znrres>" 61)

hide_const (open) val

instantiation share :: (type) pre_sep_ab_semigroup begin

definition times_share :: "'a share \<Rightarrow> 'a share \<Rightarrow> 'a share" where
  "times_share x' y' = (case x' of n \<Znrres> x \<Rightarrow> (case y' of m \<Znrres> y \<Rightarrow>
    if x = y then n+m \<Znrres> x else undefined))"

lemma times_share[simp]:
  "(n \<Znrres> x) * (m \<Znrres> y) = (if x = y then n+m \<Znrres> x else undefined)"
  unfolding times_share_def by simp_all

definition sep_disj_share :: "'a share \<Rightarrow> 'a share \<Rightarrow> bool" where
  "sep_disj_share x' y' \<longleftrightarrow> (case x' of n \<Znrres> x \<Rightarrow>
    (case y' of m \<Znrres> y \<Rightarrow> x = y))"

lemma sep_disj_share[simp]:
  "(n \<Znrres> x) ## (m \<Znrres> y) \<longleftrightarrow> x = y"
  unfolding sep_disj_share_def by simp_all

instance proof
fix x y z :: "'a share"
  show "x ## y \<Longrightarrow> y ## x" by (cases x; cases y) (simp add: add.commute)
qed
end

instantiation share :: (type) cancl_sep_ab_semigroup begin
instance proof
  fix x y z :: "'a share"
  show "x ## y \<Longrightarrow> x * y = y * x" by (cases x; cases y) (simp add: add.commute) 
  show "x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x * y * z = x * (y * z)"
    by (cases x; cases y; cases z) (simp add: add.assoc)
  show "x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y"
    by (cases x; cases y; cases z; simp)
  show "x ## z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z"
    by (cases x; cases y; cases z)
       (simp add: ab_semigroup_add_class.add_ac(1) order_less_le)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close>
    unfolding join_sub_def
    apply (cases x; clarsimp; cases y; clarsimp)
    by (metis (no_types, opaque_lifting) add.commute nle_le posrat_add_leD1 sep_disj_share share.collapse share.inject times_share)
qed
end


instantiation share :: (type) share begin
definition share_share :: "pos0rat \<Rightarrow> 'a share \<Rightarrow> 'a share"
  where \<open>share_share n x = (case x of m \<Znrres> x' \<Rightarrow> (to_posrat n*m) \<Znrres> x')\<close>
lemma [simp]: \<open>share n (m \<Znrres> x) = to_posrat n * m \<Znrres> x\<close>
  unfolding share_share_def by simp
instance apply (standard; case_tac x; simp add: share_share_def mult.assoc)
  by (metis mult.assoc to_posrat_times)
end

instantiation share :: (type) share_semimodule_sep begin
instance apply (standard; case_tac x)
    apply (case_tac y, simp add: sep_disj_commute sep_mult_commute)
  using mult_pos_pos zero_less_mult_pos apply blast
    apply (simp add: distrib_right)
    apply (simp add: distrib_right)
  apply (metis distrib_right to_posrat_plus)
    by (case_tac y; simp add: distrib_left)
end



subsubsection \<open>Convert a function to sharing or back\<close>

abbreviation \<open>to_share \<equiv> map_option (Share 1)\<close>
abbreviation \<open>strip_share \<equiv> map_option share.val\<close>

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
  by (auto split: option.split share.split)
     (metis option.simps(5) sep_disj_share sep_disj_share_def)

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
    apply (cases y, simp)
    by (metis NoePreliminary.rat_of_posrat add_cancel_left_left less_numeral_extra(3) plus_posrat.rep_eq)
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
    by (metis NoePreliminary.rat_of_posrat add_cancel_left_left less_numeral_extra(3) plus_posrat.rep_eq sep_disj_share share.collapse share.sel(1) times_share)
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
instance by (standard; case_tac x; case_tac y; simp add: sep_disj_nonsepable_def)
end


subsection \<open>Agreement\<close>

datatype 'a agree = agree 'a

lemma agree_forall: \<open>All P \<longleftrightarrow> (\<forall>x. P (agree x))\<close> by (metis agree.exhaust) 
lemma agree_exists: \<open>Ex P  \<longleftrightarrow> (\<exists>x. P (agree x))\<close> by (metis agree.exhaust) 

instantiation agree :: (type) pre_sep_ab_semigroup begin
definition times_agree :: \<open>'a agree \<Rightarrow> 'a agree \<Rightarrow> 'a agree\<close>
  where [simp]: \<open>times_agree x y = x\<close>
definition sep_disj_agree :: \<open>'a agree \<Rightarrow> 'a agree \<Rightarrow> bool\<close>
  where [simp]: \<open>sep_disj_agree x y \<longleftrightarrow> x = y\<close>

instance proof
  fix x y z :: \<open>'a agree\<close>
  show \<open>x ## y \<Longrightarrow> y ## x\<close> by (case_tac x; case_tac y; simp)
qed
end

instantiation agree :: (type) cancl_sep_ab_semigroup begin
instance proof
  fix x y z :: \<open>'a agree\<close>
  show \<open>x ## y \<Longrightarrow> x * y = y * x\<close> by (case_tac x; case_tac y; simp)
  show \<open>x ## y \<Longrightarrow> y ## z \<Longrightarrow> x ## z \<Longrightarrow> x * y * z = x * (y * z)\<close> by (case_tac x; case_tac y; simp)
  show \<open>x \<preceq>\<^sub>S\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>S\<^sub>L x \<Longrightarrow> x = y\<close> unfolding join_sub_def by simp
  show \<open>x ## y * z \<Longrightarrow> y ## z \<Longrightarrow> x ## y\<close> by (case_tac x; case_tac y; case_tac z; simp)
  show \<open>x ## z \<Longrightarrow> y ## z \<Longrightarrow> x * y ## z\<close> by (case_tac x; case_tac y; case_tac z; simp)
qed
end

section \<open>Interpretation of Fiction\<close>

subsection \<open>Algebric Structure\<close>

definition Fictional :: "('a::one \<Rightarrow> 'b::one set) \<Rightarrow> bool"
  where "Fictional \<I> \<longleftrightarrow> \<I> 1 = 1"

typedef (overloaded) ('a::one,'b::one) fiction
    = \<open>Collect (Fictional :: ('a \<Rightarrow> 'b set) \<Rightarrow> bool)\<close>
  morphisms \<I> Fiction
  by (rule exI[where x = \<open>\<lambda>_. 1\<close>]) (simp add:sep_mult_commute Fictional_def)

lemmas Fiction_inverse[simp] = Fiction_inverse[simplified]

lemma Fiction_one[simp]: "\<I> I 1 = 1"
  using Fictional_def \<I> by blast


subsection \<open>Instances\<close>

locale fiction
begin

subsubsection \<open>Function\<close>

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

definition "pointwise' I = Fiction (\<lambda>f. {g. \<forall>x. g x \<in> \<I> (I x) (f x) })"
lemma pointwise'_\<I>[simp]:
  "\<I> (pointwise' I) = (\<lambda>f. {g. \<forall>x. g x \<in> \<I> (I x) (f x) })"
  unfolding pointwise'_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_fun_def fun_eq_iff)



subsubsection \<open>Pair\<close>

definition "pair I1 I2 = Fiction (\<lambda>(x,y). \<I> I1 x * \<I> I2 y) "
lemma pair_\<I>[simp]: "\<I> (pair I1 I2) = (\<lambda>(x,y). \<I> I1 x * \<I> I2 y)"
  for I1 :: "('a::one,'b::monoid_mult) fiction"
  unfolding pair_def by (rule Fiction_inverse) (simp add: Fictional_def one_prod_def)
notation pair (infixl "\<bullet>" 50)


subsubsection \<open>Option\<close>

definition "option I = Fiction (case_option 1 I)"
lemma option_\<I>[simp]: "\<I> (option I) = (case_option 1 I)"
  unfolding option_def by (rule Fiction_inverse) (simp add: Fictional_def)

definition "optionwise I = Fiction (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"
lemma optionwise_\<I>[simp]:
  "\<I> (optionwise I) = (\<lambda>x. case x of Some x' \<Rightarrow> Some ` I x' | _ \<Rightarrow> {None})"
  unfolding optionwise_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def)


subsubsection \<open>Partiality\<close>

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


subsubsection \<open>Exact Itself\<close>

definition [simp]: "it' x = {x}"

definition "it = Fiction it'"
lemma it_\<I>[simp]: "\<I> it = it'"
  unfolding it_def by (rule Fiction_inverse) (simp add: Fictional_def one_set_def)

end


lemmas [simp] = fiction.fun_\<I> fiction.fun'_\<I> fiction.option_\<I> fiction.fine_\<I>
  fiction.it'_def fiction.it_\<I> fiction.defined_\<I> fiction.pointwise'_\<I>

lemma [simp]: "\<I> (fiction.fun I) (1(k:=v)) = \<I> I v" by simp

subsubsection \<open>Share by Fractional Ownership\<close>

definition "fiction_share s = (case s of w \<Znrres> v \<Rightarrow> if w = 1 then {v} else {})"

lemma fiction_share_\<I>[simp]: "fiction_share (w \<Znrres> v) = (if w = 1 then {v} else {})"
  unfolding fiction_share_def by simp

lemma In_ficion_fine [simp]:
  \<open>x \<in> (case some_fine of Fine y \<Rightarrow> f y | Undef \<Rightarrow> {})
        \<longleftrightarrow> (\<exists>y. some_fine = Fine y \<and> x \<in> f y)\<close>
  by (cases some_fine; simp)

definition \<open>fiction_to_share = Fiction (\<lambda>m. {f. m = to_share o f})\<close>

lemma fiction_to_share_\<I>:
  \<open>\<I> fiction_to_share = (\<lambda>m. {f. m = to_share o f})\<close>
  unfolding fiction_to_share_def
  by (rule Fiction_inverse, simp add: Fictional_def one_set_def)


subsubsection \<open>Agreement\<close>

definition \<open>fiction_agree = (\<lambda>x. case x of agree x' \<Rightarrow> {x'})\<close>


section \<open>Extensible Resource & Fiction Space\<close>

subsection \<open>Basic Entry Structure\<close>

datatype ('NAME,'REP,'T) Entry =
  Entry (name: 'NAME) (project: "'REP \<Rightarrow> 'T") (inject: "'T \<Rightarrow> 'REP")

hide_const (open) name project inject

subsubsection \<open>Syntax\<close>

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


subsubsection \<open>Projector & Injector\<close>

text \<open>The resources in the model are designed to be commutative monoids. It is beneficial
  for abstracting different part of a kind of resource by different fictions, if the resource
  is naturally separable.
  Note it does not require the resource to be separable because any structure can be lifted to a
  a discrete commutative monoid by introducing a 1 element standing for not-specified and
  a 0 element to be the result of applying the monoid operation on undefined operands.\<close>

locale project_inject =
  inj: homo_mult \<open>Entry.inject entry\<close> + prj: homo_mult \<open>Entry.project entry\<close>
  for entry :: "('NAME, 'REP::comm_monoid_mult, 'T::comm_monoid_mult) Entry"
+ assumes proj_inj[simp]: "Entry.project entry (Entry.inject entry x) = x"
    and   mult_in_dom:    \<open>a * b = Entry.inject entry c \<longleftrightarrow>
                           (\<exists>a' b'. a = Entry.inject entry a' \<and> b = Entry.inject entry b' \<and> a' * b' = c)\<close>
begin

abbreviation "name \<equiv> Entry.name entry"
abbreviation "inject \<equiv> Entry.inject entry"
abbreviation "project \<equiv> Entry.project entry"
abbreviation "clean f \<equiv> f(name := 1)"
abbreviation "get f \<equiv> project (f name)"
abbreviation "updt g f \<equiv> f(name := inject (g (get f)))"
abbreviation "mk x \<equiv> 1(name := inject x)"

lemma inject_inj[simp]:
  \<open>inject a = inject b \<longleftrightarrow> a = b\<close>
  by (metis proj_inj)

lemma get_homo_mult:
  \<open>get (a * b) = get a * get b\<close>
  by (simp add: prj.homo_mult times_fun)

lemma mk_homo_one[simp]: \<open>mk x = 1 \<longleftrightarrow> x = 1\<close>
  by (metis fun_1upd1 fun_upd_eqD inj.homo_one proj_inj)

lemma mk_homo_mult: \<open>mk (a * b) = mk a * mk b\<close>
  by (simp add: fun_1upd_homo_left1 inj.homo_mult)

lemma mk_inj[simp]: \<open>mk a = mk b \<longleftrightarrow> a = b\<close>
  unfolding fun_eq_iff by simp

lemma inj_homo_one[simp]: \<open>inject x = 1 \<longleftrightarrow> x = 1\<close>
  by (metis inj.homo_one proj_inj)

lemmas proj_homo_one  = prj.homo_one
lemmas proj_homo_mult = prj.homo_mult
lemmas inj_homo_mult = inj.homo_mult

lemmas split = fun_split_1[where ?k = name and ?'a = 'NAME and ?'b = 'REP]

lemma mult_strip_inject_011: \<open>NO_MATCH (inject a'') a' \<Longrightarrow>
  a' * inject b = inject c \<longleftrightarrow> (\<exists>a. a' = inject a \<and> a * b = c)\<close>
  by (metis mult_in_dom proj_inj)

lemma times_fun_upd:
  \<open>(R * mk x)(name := inject y) = (clean R * mk y)\<close>
  unfolding times_fun_def fun_upd_def fun_eq_iff by simp

end


subsection \<open>Extensive Resource Space\<close>

ML_file_debug \<open>Resource_Space.ML\<close>



subsection \<open>Extensive Fictional Space\<close>

locale fictional_space =
  fixes INTERPRET :: "'NAME \<Rightarrow> ('REP::{no_inverse,comm_monoid_mult},'RES::{comm_monoid_mult}) fiction"
begin

definition "INTERP = fiction.fun' INTERPRET"

end

definition "Fic_Space (f::'a\<Rightarrow>'b::no_inverse) \<longleftrightarrow> finite (dom1 f)"

lemma Fic_Space_Un[simp]: \<open>Fic_Space (a*b) \<longleftrightarrow> Fic_Space a \<and> Fic_Space b\<close>
  unfolding Fic_Space_def by (simp add: dom1_mult_disjoint finite_Un)

lemma Fic_Space_1[simp]: \<open>Fic_Space 1\<close>
  unfolding Fic_Space_def by simp


locale fictional_project_inject =
  fictional_space INTERPRET + project_inject entry +
  inj: homo_mult \<open>Entry.inject entry\<close> + prj: homo_mult \<open>Entry.project entry\<close>
  for INTERPRET :: "'NAME \<Rightarrow> ('REP::{no_inverse,comm_monoid_mult},'RES::comm_monoid_mult) fiction"
  and entry :: "('NAME,'REP,'T::comm_monoid_mult) Entry"
+ fixes I :: "('T,'RES) fiction"
  assumes proj_inj[simp]: "Entry.project entry (Entry.inject entry x) = x"
    and interpret_reduct[simp]: "\<I> (INTERPRET (Entry.name entry)) = \<I> I o Entry.project entry"
begin

lemmas inj_homo_mult[simp] = inj.homo_mult[symmetric]
lemmas inj_homo_one = inj.homo_one
lemmas prj_homo_mult[simp] = prj.homo_mult
lemmas prj_homo_one = prj.homo_one


lemma [simp]: "R * inject x * inject y = R * inject (x * y)"
  by (simp add: mult.assoc) 

lemma interp_m[simp]: "\<I> INTERP (mk x) = \<I> I x"
  unfolding INTERP_def by (simp add: sep_disj_commute sep_mult_commute)

lemma interp_split:
  "Fic_Space f \<Longrightarrow>
    \<I> INTERP f = \<I> INTERP (clean f) * \<I> I (project (f name))"
  unfolding INTERP_def Fic_Space_def
  by (subst fiction.fun'_split[where ?f = f and ?k = name]) simp_all

lemma interp_split':
  "NO_MATCH (clean f') f \<Longrightarrow> Fic_Space f \<Longrightarrow>
    \<I> INTERP f = \<I> INTERP (clean f) * \<I> I (project (f name))"
  using interp_split .

lemma Fic_Space_m[simp]: "Fic_Space (mk x)"
  unfolding Fic_Space_def by simp

lemma Fic_Space_mc[simp]: "Fic_Space (clean f) \<longleftrightarrow> Fic_Space f"
  unfolding Fic_Space_def by simp

lemma Fic_Space_mm[simp]: "Fic_Space (f * mk x) \<longleftrightarrow> Fic_Space f"
  unfolding Fic_Space_def finite_dom1_mult1 times_fun by simp

end

ML_file_debug \<open>fiction_space.ML\<close>



hide_const (open) Entry
hide_type (open) Entry

end