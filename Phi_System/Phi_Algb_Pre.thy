theory Phi_Algb_Pre
  imports IDE_CP_Reasoning1
          Phi_Algebras.Map_of_Tree
          Phi_Algebras.LCRO_Interval
          Phi_Algebras.Len_Intvl
begin 


section \<open>Arithmetic Evaluation\<close>

consts \<A>arith_eval :: action

subsection \<open>Partial Addition\<close>

text \<open>Solves partial addition equations consisting of

\<^item> \<open>given + ?unknown = given\<close>, \<open>?unknown + given = given\<close>,
  \<open>given = given + ?unknown\<close>, \<open>given = ?unknown + given\<close>
\<^item> \<open>given + ?unknown = ?unknown + given\<close>, \<open>?unknown + given = given + ?unknown\<close> (only for non-commutative group)
\<^item> \<open>?unknown + given + ?unknown = given\<close>, \<open>given = ?unknown + given + ?unknown\<close> (only for non-commutative group)

Note some forms are only meaningful for non-commutative group as if not they can be reduced to the
first form.
Also not, as addition can be associative, we use \<open>id\<close> to annotate explicitly each element in the equation.
For instance, \<open>id a + id b + id c = id d\<close> to distinguish with \<open>id (a + b) + id c = id d\<close>.

System rules first normalize the problem into one of
\<^item> \<open>?unknown_d + given_a = given_b\<close> or
  \<open>given_b + ?unknown_c = given_a\<close> (only for non-commutative group)
\<^item> \<open>?unknown + given = given + ?unknown\<close> (only for non-commutative group)
\<^item> \<open>?unknown + given + ?unknown = given\<close> (only for non-commutative group)

Then the above three forms are what user rules have to handle for specific algebras.

There are pre-built reasoning rules for,
\<^item> cancellative and canonically ordered commutative monoid, including the version for both partial algebras
  and total. This is the weakest algebraic structure to have a general algorithm,
  if an algorithm deciding the order relation is assumed.
\<^item> group, (only that for total algebra is installed), which is though not the minimal requirement,
  the weakest one available in Isabelle standard library, as the minimal one, quasigroup, is not
  formalized in Isabelle standard library.
\<close>

\<phi>reasoner_group \<A>_partial_add = (1000, [1, 4000]) for \<open>_ = _ @action \<A>arith_eval\<close>
    \<open>Decision procedure solving equantions of partial additive groups, with finding appropriate instantiations
     for schematic variables inside.\<close>
 and \<A>_partial_add_success = (4000, [4000, 4000]) for \<open>_ = _ @action \<A>arith_eval\<close> in \<A>_partial_add
    \<open>Rules leading to success directly\<close>
 and \<A>_partial_add_normalizing = (3000, [2801, 3399]) for \<open>_ = _ @action \<A>arith_eval\<close>
                                                       in \<A>_partial_add and < \<A>_partial_add_success
    \<open>Rules normalizing the reasoning\<close>
 and \<A>_partial_add_splitting = (2500, [2500, 2599]) for \<open>_ = _ @action \<A>arith_eval\<close>
                                                     in \<A>_partial_add and < \<A>_partial_add_normalizing
    \<open>Spliting a complicated equation like \<open>a + b + c = d\<close> into several minimal equations \<open>a + b = c\<close>\<close>
 and \<A>_partial_add_cut = (1000, [1000, 1100]) for \<open>_ = _ @action \<A>arith_eval\<close>
                                               in \<A>_partial_add and < \<A>_partial_add_splitting
    \<open>Cutting rules\<close>

declare [[\<phi>reason_default_pattern \<open>?Eq @action \<A>arith_eval\<close> \<Rightarrow> \<open>?Eq @action \<A>arith_eval\<close> (100)]]


subsubsection \<open>Normalizing Equations\<close>

lemma [\<phi>reason %\<A>_partial_add_success]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a = b
\<Longrightarrow> id a = id b @action \<A>arith_eval \<close>
  unfolding Premise_def Action_Tag_def
  by simp

paragraph \<open>Flipping\<close>

lemma [\<phi>reason %\<A>_partial_add_normalizing]:
  \<open> A = id a @action \<A>arith_eval
\<Longrightarrow> id a = A @action \<A>arith_eval\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>id _ + id ?var_d = id ?var_c + id _ @action \<A>arith_eval\<close>
                                           except \<open>id ?var_d + _ = _ + id ?var_c @action _\<close>]:
  \<open> id c + id b = id a + id d @action \<A>arith_eval
\<Longrightarrow> id a + id d = id c + id b @action \<A>arith_eval \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>id _ + id ?var_d = id (_::?'a::ab_semigroup_add) @action \<A>arith_eval\<close>
                                           except \<open>id ?var_d + _ = id _  @action _\<close>]:
  \<open> id c + id b = id a @action \<A>arith_eval
\<Longrightarrow> id b + id c = id a @action \<A>arith_eval \<close>
  for a :: \<open>'a::ab_semigroup_add\<close>
  unfolding Action_Tag_def
  by (simp add: add.commute)

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>id _ + id ?var_d = id (_::?'a::partial_ab_semigroup_add) @action \<A>arith_eval\<close>
                                           except \<open>id ?var_d + _ = id _  @action _\<close>]:
  \<open> id c + id b = id a @action \<A>arith_eval
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c ##\<^sub>+ b
\<Longrightarrow> id b + id c = id a @action \<A>arith_eval \<close>
  for a :: \<open>'a::partial_ab_semigroup_add\<close>
  unfolding Action_Tag_def Premise_def
  by (simp add: partial_add_commute)



paragraph \<open>Error Check\<close>

lemma [\<phi>reason %\<A>_partial_add_normalizing
               for \<open>id _ + id _ = (id _ + id _ :: ?'a :: partial_ab_semigroup_add) @action \<A>arith_eval\<close>]:
  \<open> ERROR TEXT(\<open>Invalid equation\<close> (id a + id d = id c + id b) \<open>on commutative group,\<close>
               \<open>which can always be reduced to either \<open>c + a = b\<close> or \<open>c + b = a\<close>. Some reasoning rule is configured wrong.\<close>)
\<Longrightarrow> id a + id d = id c + id b @action \<A>arith_eval \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason %\<A>_partial_add_normalizing
               for \<open>id _ + id _ + id _ = (id _ :: ?'a :: partial_ab_semigroup_add) @action \<A>arith_eval\<close>]:
  \<open> ERROR TEXT(\<open>Invalid equation\<close> (id c + id a + id d = id b) \<open>on commutative group,\<close>
               \<open>which can always be reduced to \<open>c + a = b\<close>. Some reasoning rule is configured wrong.\<close>)
\<Longrightarrow> id c + id a + id d = id b @action \<A>arith_eval \<close>
  unfolding ERROR_def
  by blast



subsubsection \<open>Solving the Equations on Specific Algberas\<close>

paragraph \<open>Direct Success\<close>

lemma [\<phi>reason %\<A>_partial_add_success for \<open>id ?a + id ?b = id (?a + ?b) @action \<A>arith_eval\<close>
                                           \<open>id ?a + id ?var = id (?a + ?b) @action \<A>arith_eval\<close>
                                           \<open>id ?var + id ?b = id (?a + ?b) @action \<A>arith_eval\<close> ]:
  \<open> id a + id b = id (a + b) @action \<A>arith_eval \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_success for \<open>id ?a + id ?b + id ?c = id (?a + ?b + ?c) @action \<A>arith_eval\<close>
                                           \<open>id ?var_a + id ?b + id ?var_c = id (_ + ?b + _) @action \<A>arith_eval\<close>]:
  \<open> id a + id b + id c = id (a + b + c) @action \<A>arith_eval \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_success for \<open>id ?c + id (?x + ?d) = id (?c + ?x) + id ?d @action \<A>arith_eval\<close>
                                           \<open>id ?var_c + id (?x + ?d) = id (?c + ?x) + id ?var_d @action \<A>arith_eval\<close>]:
  \<open> id c + id (x + d) = id (c + x) + id d @action \<A>arith_eval \<close>
  for x :: \<open>'a :: semigroup_add\<close>
  unfolding Action_Tag_def
  by (simp add: add.assoc)


paragraph \<open>Cancellative and Canonically Ordered Commutative Partial Monoid\<close>

text \<open>The rules do not conflict with those for groups because a canonically ordered monoid can never
  be a group.\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id ?a + id (?b - ?a) = id (?a :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}) @action \<A>arith_eval\<close> 
                                      \<open>id _ + (?var :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}) = id _ @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b      
\<Longrightarrow> id a + id (b - a) = id b @action \<A>arith_eval \<close>
  for a :: \<open>'a::{partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}\<close>
  unfolding Action_Tag_def Premise_def
  by (simp add: partial_le_iff_add; force)

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id (?b - ?a) + id ?a = id (?a :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}) @action \<A>arith_eval\<close>
                                       \<open>(?var :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}) + id _ = id _ @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b
\<Longrightarrow> id (b - a) + id a = id b @action \<A>arith_eval \<close>
  for a :: \<open>'a::{partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}\<close>
  unfolding Action_Tag_def Premise_def
  by (simp, metis partial_add_commute partial_add_diff_cancel_left' partial_le_iff_add)


paragraph \<open>Cancellative and Canonically Ordered Commutative Total Monoid\<close>

text \<open>The rules do not conflict with those for groups because a canonically ordered monoid can never
  be a group.\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id ?a + id (?b - ?a) = id (?a :: ?'a :: {canonically_ordered_monoid_add, cancel_ab_semigroup_add}) @action \<A>arith_eval\<close> 
                                      \<open>id _ + (?var :: ?'a :: {canonically_ordered_monoid_add, cancel_ab_semigroup_add}) = id _ @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b
\<Longrightarrow> id a + id (b - a) = id b @action \<A>arith_eval \<close>
  for a :: \<open>'a::{canonically_ordered_monoid_add, cancel_ab_semigroup_add}\<close>
  \<comment>\<open>The unital property is not required.
     It can be even weaker as {canonically_ordered_ab_semigroup_add, cancel_ab_semigroup_add}, but
     the Isabelle std-lib only formalizes canonically_ordered_monoid_add.\<close>
  unfolding Action_Tag_def Premise_def
  by (simp, metis add_diff_cancel_left' le_iff_add)
  

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id (?b - ?a) + id ?a = id (?a :: ?'a :: {canonically_ordered_monoid_add, cancel_ab_semigroup_add}) @action \<A>arith_eval\<close>
                                       \<open>(?var :: ?'a :: {canonically_ordered_monoid_add, cancel_ab_semigroup_add}) + id _ = id _ @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b
\<Longrightarrow> id (b - a) + id a = id b @action \<A>arith_eval \<close>
  for a :: \<open>'a::{canonically_ordered_monoid_add, cancel_ab_semigroup_add}\<close>
  unfolding Action_Tag_def Premise_def
  by (simp, metis add.commute add_diff_cancel_left' le_iff_add)


paragraph \<open>Total Group\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id (?b - ?a) + id ?a = id ?b @action \<A>arith_eval\<close>
                                       \<open>id ?var + id ?a = id ?b @action \<A>arith_eval\<close> ]:
  \<open> id (b - a) + id a = id b @action \<A>arith_eval \<close>
  for a :: \<open>'a::group_add\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id ?a + id (?b - ?a) = id ?b @action \<A>arith_eval\<close>
                                       \<open>id ?a + id ?var = id ?b @action \<A>arith_eval\<close> ]:
  \<open> id a + id (b - a) = id b @action \<A>arith_eval \<close>
  for a :: \<open>'a::ab_group_add\<close>
  unfolding Action_Tag_def
  by (simp add: algebra_simps)


paragraph \<open>LCRO Interval\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id [?a,?b) + id [?b,?c) = id [?a,?c) @action \<A>arith_eval\<close>
                                       \<open>id [?a,?b) + id ?var = id [?a,?c) @action \<A>arith_eval\<close>
                                       \<open>id ?var + id [?b,?c) = id [?a,?c) @action \<A>arith_eval\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b \<and> b \<le> c
\<Longrightarrow> id [a,b) + id [b,c) = id [a,c) @action \<A>arith_eval \<close>
  unfolding Premise_def Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id [?a,?b) + id [?b,?d) = id [?a,?c) + id [?c,?d) @action \<A>arith_eval\<close>
                                       \<open>id ?var_c + id [?b,?d) = id [?a,?c) + id ?var_d @action \<A>arith_eval\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b \<and> b \<le> d \<and> a \<le> c \<and> c \<le> d
\<Longrightarrow> id [a,b) + id [b,d) = id [a,c) + id [c,d) @action \<A>arith_eval \<close>
  unfolding Premise_def Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id [?a,?b) + id [?b,?c) + id [?c,?d) = id [?a,?d) @action \<A>arith_eval\<close>
                                       \<open>id ?var_c + id [?b,?c) + id ?var_d = id [?a,?d) @action \<A>arith_eval\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b \<and> b \<le> c \<and> c \<le> d
\<Longrightarrow> id [a,b) + id [b,c) + id [c,d) = id [a,d) @action \<A>arith_eval \<close>
  unfolding Premise_def Action_Tag_def
  by (simp, insert order_trans, fastforce)


paragraph \<open>Len Intvl\<close>

subparagraph \<open>Direct\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id ?var + id (_::_ len_intvl) = id (_::_ len_intvl) @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.len c \<ge> len_intvl.len b \<and>
             len_intvl.start c + len_intvl.len c - len_intvl.len b = len_intvl.start b
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> a : \<lbrakk>len_intvl.start c : len_intvl.len c - len_intvl.len b\<rwpar>
\<Longrightarrow> id a + id b = id c @action \<A>arith_eval\<close>
  unfolding Action_Tag_def Premise_def Simplify_def
  by (cases b; cases c; clarsimp)

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id (_::_ len_intvl) + id ?var = id (_::_ len_intvl) @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.len a \<le> len_intvl.len c \<and> len_intvl.start a = len_intvl.start c
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> b : \<lbrakk>len_intvl.start a + len_intvl.len a : len_intvl.len c - len_intvl.len a\<rwpar>
\<Longrightarrow> id a + id b = id c @action \<A>arith_eval \<close>
  unfolding Action_Tag_def Premise_def Simplify_def
  by (cases a; cases c; clarsimp)

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id ?var_a + id (_::_ len_intvl) = id (_::_ len_intvl) + id ?var_d @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start c \<le> len_intvl.start b \<and>
            len_intvl.start b \<le> len_intvl.start c + len_intvl.len c \<and>
            len_intvl.start c + len_intvl.len c \<le> len_intvl.start b + len_intvl.len b
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> a : \<lbrakk>len_intvl.start c : len_intvl.start b - len_intvl.start c\<rwpar>
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> d : \<lbrakk>len_intvl.start c + len_intvl.len c : len_intvl.start b + len_intvl.len b - len_intvl.start c - len_intvl.len c\<rwpar>
\<Longrightarrow> id a + id b = id c + id d @action \<A>arith_eval \<close>
  unfolding Action_Tag_def Premise_def Simplify_def
  by (cases b; cases c; clarsimp)

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id ?var_a + id (_::_ len_intvl) + id ?var_c = id (_::_ len_intvl) @action \<A>arith_eval\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start d \<le> len_intvl.start b \<and>
            len_intvl.start b + len_intvl.len b \<le> len_intvl.start d + len_intvl.len d
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> a : \<lbrakk>len_intvl.start d : len_intvl.start b - len_intvl.start d\<rwpar>
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> c : \<lbrakk>len_intvl.start b + len_intvl.len b : len_intvl.start d + len_intvl.len d - len_intvl.start b - len_intvl.len b\<rwpar>
\<Longrightarrow> id a + id b + id c = id d @action \<A>arith_eval \<close>
  unfolding Action_Tag_def Premise_def Simplify_def
  by (cases b; cases d; clarsimp)

subparagraph \<open>Wrapped by set\<close>

lemma [\<phi>reason %\<A>_partial_add_cut+100
           for \<open>id ?var + id (Len_Intvl.set _) = id (Len_Intvl.set _) @action \<A>arith_eval\<close>
               \<open>id (Len_Intvl.set _) + id ?var = id (Len_Intvl.set _) @action \<A>arith_eval\<close>]:
  \<open> id a + id b = id c @action \<A>arith_eval
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start a + len_intvl.len a = len_intvl.start b
\<Longrightarrow> id (Len_Intvl.set a) + id (Len_Intvl.set b) = id (Len_Intvl.set c) @action \<A>arith_eval \<close>
  unfolding Action_Tag_def
  by (cases a; cases b; cases c; clarsimp simp add: plus_set_def set_eq_iff shift_by_nat_ord;
      metis (full_types) Premise_D add.assoc add_leD1 linorder_not_less)

lemma [\<phi>reason %\<A>_partial_add_cut
           for \<open>id ?var + id (Len_Intvl.set _) + id ?var = id (Len_Intvl.set _) @action \<A>arith_eval\<close>]:
  \<open> id a + id b + id c = id d @action \<A>arith_eval
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start a + len_intvl.len a = len_intvl.start b \<and>
            len_intvl.start b + len_intvl.len b = len_intvl.start c
\<Longrightarrow> id (Len_Intvl.set a) + id (Len_Intvl.set b) + id (Len_Intvl.set c) = id (Len_Intvl.set d) @action \<A>arith_eval \<close>
  unfolding Action_Tag_def
  by (cases a; cases b; cases c; clarsimp simp add: plus_set_def set_eq_iff shift_by_nat_ord;
      metis (full_types) Premise_E add.assoc add_leE leI trans_less_add1)

lemma [\<phi>reason %\<A>_partial_add_cut
           for \<open>id ?var + id (Len_Intvl.set _) = id (Len_Intvl.set _) + id ?var @action \<A>arith_eval\<close>]:
  \<open> id a + id b = id c + id d @action \<A>arith_eval
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start a + len_intvl.len a = len_intvl.start b \<and>
            len_intvl.start c + len_intvl.len c = len_intvl.start d
\<Longrightarrow> id (Len_Intvl.set a) + id (Len_Intvl.set b) = id (Len_Intvl.set c) + id (Len_Intvl.set d) @action \<A>arith_eval \<close>
  unfolding Action_Tag_def
  by (cases a; cases b; cases c; clarsimp simp add: plus_set_def set_eq_iff shift_by_nat_ord;
      smt (verit, best) Premise_D group_cancel.add1 len_intvl.sel(1) len_intvl.sel(2) linorder_not_le plus_len_intvl_def trans_less_add1)

paragraph \<open>List\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id _ + id (_#_) = id (_#_) @action \<A>arith_eval\<close>
                                       \<open>id (_ # _) + id ?var = id (_#_) @action \<A>arith_eval\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = z
\<Longrightarrow> id ys + id xs = id zs @action \<A>arith_eval
\<Longrightarrow> id ys + id (x#xs) = id (z#zs) @action \<A>arith_eval \<close>
  unfolding Premise_def Action_Tag_def plus_list_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id _ + id [] = id _ @action \<A>arith_eval\<close>,
       \<phi>reason %\<A>_partial_add_cut+10 for \<open>id _ + id ?var = id _ @action \<A>arith_eval\<close>]:
  \<open> id zs + id [] = id zs @action \<A>arith_eval \<close>
  unfolding Premise_def Action_Tag_def plus_list_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>id [] + id _ = id _ @action \<A>arith_eval\<close> ]:
  \<open> id [] + id zs = id zs @action \<A>arith_eval \<close>
  unfolding Premise_def Action_Tag_def plus_list_def
  by simp

text \<open>TODO:

\<^item> \<open>?unknown + given = given + ?unknown\<close> (only for non-commutative group)
\<^item> \<open>?unknown + given + ?unknown = given\<close> (only for non-commutative group)

need some ML
\<close>

subsection \<open>Existence of Solutions of Addition Equation\<close>

definition partial_add_overlaps :: \<open>'a::plus \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>partial_add_overlaps a b \<longleftrightarrow> True\<close>

\<phi>reasoner_group partial_add_overlaps_all = (100, [0,3000]) for \<open>partial_add_overlaps a b\<close>
    \<open>used in the reasoning of semimodule \<phi>-type for a quick check of whether two semimodules overlap\<close>
  and partial_add_overlaps_default = (10, [10,10]) in partial_add_overlaps_all \<open>\<close>
  and partial_add_overlaps_default_comm = (12, [12,12]) in partial_add_overlaps_all \<open>\<close>
  and partial_add_overlaps_direct_success = (3000, [3000,3000]) in partial_add_overlaps_all \<open>\<close>
  and partial_add_overlaps_cancl = (1000, [1000,1000]) in partial_add_overlaps_all \<open>\<close>
  and partial_add_overlaps_specific = (2000, [2000,2100]) in partial_add_overlaps_all \<open>\<close>

declare [[\<phi>reason_default_pattern \<open>partial_add_overlaps ?a ?b\<close> \<Rightarrow> \<open>partial_add_overlaps ?a ?b\<close> (100)]]

subsubsection \<open>Default Implementation falling back to solving the equations\<close>

paragraph \<open>Commutative Additive Group\<close>

lemma [\<phi>reason default %partial_add_overlaps_default,
       \<phi>reason default %partial_add_overlaps_default_comm
       for \<open>partial_add_overlaps (_::_::ab_semigroup_add) _\<close>
           \<open>partial_add_overlaps (_::_::partial_ab_semigroup_add) _\<close>]:
  \<open> id d + id a = id b @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default,
       \<phi>reason default %partial_add_overlaps_default_comm
       for \<open>partial_add_overlaps (_::_::ab_semigroup_add) _\<close>
           \<open>partial_add_overlaps (_::_::partial_ab_semigroup_add) _\<close>]:
  \<open> id d + id b = id a @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

paragraph \<open>None_Commutative Additive Group\<close>

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id b + id c = id a @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id a + id d = id b @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id d + id a + id c = id b @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id d + id b + id c = id a @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id d + id a = id b + id c @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id a + id d = id c + id b @action \<A>arith_eval
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

subsubsection \<open>Specific Instances\<close>

paragraph \<open>Direct Success\<close>

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps a a \<close>
  unfolding partial_add_overlaps_def
  by blast

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps a (d + a + c) \<close>
  unfolding partial_add_overlaps_def
  by blast

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps (d + b + c) b \<close>
  unfolding partial_add_overlaps_def
  by blast

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps a (d + a) \<close>
  unfolding partial_add_overlaps_def
  by blast

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps a (a + d) \<close>
  unfolding partial_add_overlaps_def
  by blast

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps (c + b) b \<close>
  unfolding partial_add_overlaps_def
  by blast

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps (b + c) b \<close>
  unfolding partial_add_overlaps_def
  by blast

paragraph \<open>Cancellative and Canonically Ordered Commutative Partial Monoid\<close>

lemma [\<phi>reason %partial_add_overlaps_cancl]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b \<or> b \<le> a
\<Longrightarrow> partial_add_overlaps a b \<close>
  for a :: \<open>'a::{partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}\<close>
  unfolding partial_add_overlaps_def ..

lemma [\<phi>reason %partial_add_overlaps_cancl]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b \<or> b \<le> a
\<Longrightarrow> partial_add_overlaps a b \<close>
  for a :: \<open>'a::{canonically_ordered_monoid_add, cancel_ab_semigroup_add}\<close>
  unfolding partial_add_overlaps_def ..

paragraph \<open>Total Group\<close>

lemma [\<phi>reason %partial_add_overlaps_direct_success]:
  \<open> partial_add_overlaps a b \<close>
  for a :: \<open>'a::group_add\<close>
  unfolding partial_add_overlaps_def ..

paragraph \<open>LCRO Interval\<close>

lemma [\<phi>reason %partial_add_overlaps_specific]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c \<le> a \<and> a < d \<or> a \<le> c \<and> c < b
\<Longrightarrow> partial_add_overlaps [a,b) [c,d) \<close>
  unfolding partial_add_overlaps_def
  ..

paragraph \<open>Len Intvl\<close>

lemma [\<phi>reason %partial_add_overlaps_specific]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start b \<le> len_intvl.start a \<and> len_intvl.start a < len_intvl.start b + len_intvl.len b \<or>
            len_intvl.start a \<le> len_intvl.start b \<and> len_intvl.start b < len_intvl.start a + len_intvl.len a
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding partial_add_overlaps_def
  ..

lemma [\<phi>reason %partial_add_overlaps_specific+11]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start a \<le> i \<and> i < len_intvl.start a + len_intvl.len a
\<Longrightarrow> partial_add_overlaps a \<lbrakk>i:1\<rwpar> \<close>
  unfolding partial_add_overlaps_def
  ..

lemma [\<phi>reason %partial_add_overlaps_specific+10]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start b \<le> i \<and> i < len_intvl.start b + len_intvl.len b
\<Longrightarrow> partial_add_overlaps \<lbrakk>i:1\<rwpar> b \<close>
  unfolding partial_add_overlaps_def
  ..

lemma leq_le_Suc_eq[simp]:
  \<open>j \<le> x \<and> x < Suc j \<longleftrightarrow> x = j\<close>
  by fastforce
  

subparagraph \<open>Wrapped by set\<close>

lemma [\<phi>reason %partial_add_overlaps_specific + 100]:
  \<open> partial_add_overlaps a b
\<Longrightarrow> partial_add_overlaps (Len_Intvl.set a) (Len_Intvl.set b) \<close>
  unfolding partial_add_overlaps_def ..

paragraph \<open>List\<close>

(*TODO*)


subsection \<open>Auxiliary Annotations\<close>

definition scalar_mult :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close> where \<open>scalar_mult f \<equiv> f\<close>
  \<comment> \<open>A tag annotating the function is a scalar multiplication so that the automation for semimodules
      will be activated. It also distinguishes the function part and the parameter part, so that
      resolves multi-unification.\<close>

lemma scalar_mult_red[iff]:
  \<open>scalar_mult f s x = f s x\<close>
  unfolding scalar_mult_def ..

subsubsection \<open>Reasoning Rules\<close>

lemma [\<phi>reason %cutting]:
  \<open> f = g
\<Longrightarrow> u = v
\<Longrightarrow> scalar_mult f u = scalar_mult g v\<close>
  unfolding scalar_mult_def by simp

lemma [\<phi>reason %cutting]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> f = g
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> u = v
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> scalar_mult f u = scalar_mult g v\<close>
  unfolding scalar_mult_def Premise_def by simp

lemma inj_scalar_mult[simp]:
  \<open>inj (scalar_mult f s) \<equiv> inj (f s)\<close>
  unfolding scalar_mult_def .

section \<open>Preliminary for \<open>\<phi>\<close>-Type Algebra\<close>

subsection \<open>Definitions of Properties\<close>

subsubsection \<open>Local Inverse\<close>

definition local_inverse
  where \<open>local_inverse D f g \<longleftrightarrow> (\<forall>x \<in> D. g (f x) = x)\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> local_inverse D f g \<longrightarrow> (\<forall>x \<in> D. g (f x) = x) @action \<A>EIF \<close>
  unfolding Action_Tag_def local_inverse_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> (\<forall>x \<in> D. g (f x) = x) \<longrightarrow> local_inverse D f g @action \<A>ESC \<close>
  unfolding Action_Tag_def local_inverse_def
  by blast


subsection \<open>Configuration of Existing Procedures\<close>

declare [[\<phi>reason_default_pattern \<open>module_scalar_assoc ?\<psi> _\<close> \<Rightarrow> \<open>module_scalar_assoc ?\<psi> _\<close>   (100)
                              and \<open>module_scalar_identity ?\<psi>\<close> \<Rightarrow> \<open>module_scalar_identity ?\<psi>\<close> (100)
                              and \<open>module_S_distr ?\<psi> _\<close> \<Rightarrow> \<open>module_S_distr ?\<psi> _\<close> (100) ]]

\<phi>reasoner_group algb_prop_all = (100, [1, 4000]) for \<open>_\<close>
    \<open>General group of algberaic properties\<close>
 and algb_falling_lattice = (10,[1,29]) for \<open>_\<close> in algb_prop_all
    \<open>General lattice of fallbacks for deriving algberaic properties\<close>
 and algb_default = (50, [30,60]) for \<open>_\<close> in algb_prop_all and > algb_falling_lattice
    \<open>Default rules for general structures\<close>
 and algb_funcomp = (40, [40,40]) for \<open>_\<close> in algb_default
    \<open>Default rules for function composition\<close>
 and algb_derived = (70, [61,99]) for \<open>_\<close> in algb_prop_all and > algb_default
    \<open>Derived rules\<close>
 and algb_prop = (100, [100, 4000]) for \<open>_\<close> in algb_prop_all and > algb_derived
    \<open>Normal rules giving algberaic properties\<close>
 and algb_cut = (1000, [1000,1030]) for \<open>_\<close> in algb_prop
    \<open>General group of cutting rules giving algberaic properties\<close>

subsubsection \<open>Separation Algebra\<close>

paragraph \<open>Setup Reasoning Rules\<close>

declare (in homo_one) homo_one_axioms[\<phi>reason %algb_cut]

lemma [\<phi>reason %extract_pure]:
  \<open> homo_one \<psi> \<longrightarrow> \<psi> 1 = 1 @action \<A>EIF \<close>
  unfolding Action_Tag_def homo_one_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<psi> 1 = 1 \<longrightarrow> homo_one \<psi> @action \<A>ESC \<close>
  unfolding Action_Tag_def homo_one_def
  by blast

lemma [\<phi>reason default %algb_falling_lattice]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<psi> 1 = 1)
\<Longrightarrow> homo_one \<psi>\<close>
  unfolding homo_one_def Premise_def
  by simp

declare (in homo_sep) homo_sep_axioms [\<phi>reason %algb_cut]

declare (in closed_homo_sep) closed_homo_sep_axioms [\<phi>reason %algb_cut]

subparagraph \<open>homo_mul_carrier\<close>

declare (in homo_mul_carrier) homo_mul_carrier_axioms[\<phi>reason %algb_cut]

lemma homo_mul_carrier_EIF:
  \<open> homo_mul_carrier \<psi> \<longrightarrow> (\<forall>x. mul_carrier x \<longrightarrow> mul_carrier (\<psi> x)) @action \<A>EIF \<close>
  unfolding homo_mul_carrier_def Action_Tag_def
  by blast

lemma homo_mul_carrier_ESC:
  \<open> (\<forall>x. mul_carrier x \<longrightarrow> mul_carrier (\<psi> x)) \<longrightarrow> homo_mul_carrier \<psi> @action \<A>EIF \<close>
  unfolding homo_mul_carrier_def Action_Tag_def
  by blast

bundle extract_mul_carrier = homo_mul_carrier_EIF [\<phi>reason %extract_pure]
                             homo_mul_carrier_ESC [\<phi>reason %extract_pure]

lemma [\<phi>reason default %algb_falling_lattice]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>x. mul_carrier x \<longrightarrow> mul_carrier (\<psi> x))
\<Longrightarrow> homo_mul_carrier \<psi>\<close>
  unfolding homo_mul_carrier_def Premise_def .

lemma [\<phi>reason no explorative backtrack %fail]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show the multiplicative carrier homomorphism of\<close> \<psi>)
\<Longrightarrow> homo_mul_carrier \<psi> \<close>
  unfolding TRACE_FAIL_def
  by blast

subparagraph \<open>Sep Homo\<close>

lemma [\<phi>reason no explorative backtrack %fail]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show the separation homomorphism of\<close> \<psi>)
\<Longrightarrow> homo_sep \<psi> \<close>
  unfolding TRACE_FAIL_def
  by blast

lemma [\<phi>reason no explorative backtrack %fail]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show the closed separation homomorphism of\<close> \<psi>)
\<Longrightarrow> closed_homo_sep \<psi> \<close>
  unfolding TRACE_FAIL_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open>closed_homo_sep \<psi> \<longrightarrow> closed_homo_sep \<psi> @action \<A>EIF\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open>closed_homo_sep \<psi> \<longrightarrow> closed_homo_sep \<psi> @action \<A>ESC\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open>homo_sep \<psi> \<longrightarrow> homo_sep \<psi> @action \<A>EIF\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open>homo_sep \<psi> \<longrightarrow> homo_sep \<psi> @action \<A>ESC\<close>
  unfolding Action_Tag_def
  by simp

paragraph \<open>Reasoning Hierarchy\<close>
(*
lemmas [\<phi>reason default %algb_falling_lattice] =
        closed_homo_sep.intro
        homo_sep.intro
*)

(*
lemma [\<phi>reason default %algb_falling_lattice]:
  \<open>closed_homo_sep \<psi> \<Longrightarrow> homo_sep \<psi>\<close>
  using closed_homo_sep.axioms(1) by blast*)

declare closed_homo_sep.axioms(1)[simp]

lemma [\<phi>reason default %algb_falling_lattice]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> homo_sep \<psi>
\<Longrightarrow> homo_sep \<psi> \<close>
  unfolding \<r>Guard_def Premise_def .

lemma [\<phi>reason default %algb_falling_lattice]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> closed_homo_sep \<psi>
\<Longrightarrow> closed_homo_sep \<psi> \<close>
  unfolding \<r>Guard_def Premise_def .

lemma [\<phi>reason default %algb_falling_lattice]:
  \<open> closed_homo_sep_disj \<psi>
\<Longrightarrow> homo_sep_disj \<psi>\<close>
  unfolding homo_sep_disj_def closed_homo_sep_disj_def
  by blast

lemmas [\<phi>reason %algb_funcomp] =
        closed_homo_sep_disj_comp
        homo_sep_disj_comp
        homo_sep_comp
        homo_sep_mult_comp


subsection \<open>Constant Functions\<close>

subsubsection \<open>Constant One\<close>

definition \<open>constant_1 \<psi> \<equiv> (\<forall>x. \<psi> x = 1)\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> constant_1 \<psi> \<longrightarrow> (\<forall>x. \<psi> x = 1) @action \<A>EIF \<close>
  unfolding Action_Tag_def constant_1_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> (\<forall>x. \<psi> x = 1) \<longrightarrow> constant_1 \<psi> @action \<A>ESC \<close>
  unfolding Action_Tag_def constant_1_def
  by blast

lemma [\<phi>reason default %algb_falling_lattice]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>x. \<psi> x = 1)
\<Longrightarrow> constant_1 \<psi>\<close>
  unfolding constant_1_def Premise_def
  by simp


subsubsection \<open>Constantly inside the Carrier Set\<close>

definition \<open>constantly_inside_carrier f \<longleftrightarrow> (\<forall>x. mul_carrier (f x))\<close>

declare [[\<phi>reason_default_pattern \<open>constantly_inside_carrier ?\<psi>\<close> \<Rightarrow> \<open>constantly_inside_carrier ?\<psi>\<close> (100) ]]

paragraph \<open>Basic Properties\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> constantly_inside_carrier \<psi> \<longrightarrow> (\<forall>x. mul_carrier (\<psi> x)) @action \<A>EIF \<close>
  unfolding Action_Tag_def constantly_inside_carrier_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> (\<forall>x. mul_carrier (\<psi> x)) \<longrightarrow> constantly_inside_carrier \<psi> @action \<A>ESC \<close>
  unfolding Action_Tag_def constantly_inside_carrier_def
  by blast

paragraph \<open>Fallback\<close>

lemma [\<phi>reason %algb_falling_lattice]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>x. mul_carrier (\<psi> x))
\<Longrightarrow> constantly_inside_carrier \<psi> \<close>
  unfolding \<r>Guard_def Premise_def constantly_inside_carrier_def .

paragraph \<open>Instances\<close>

lemma [\<phi>reason %algb_cut]:
  \<open> constantly_inside_carrier discrete \<close>
  unfolding constantly_inside_carrier_def
  by simp


subsection \<open>Instances of the Algebraic Properties\<close>

subsubsection \<open>Identity Function\<close>

lemmas [\<phi>reason %algb_cut] =
    homo_one_id
    homo_sep_id
    closed_homo_sep_id
    homo_mul_carrier_id

subsubsection \<open>Functional Point-wise\<close>

declare homo_sep_funcomp[\<phi>reason %algb_cut]
        closed_homo_sep_funcomp[\<phi>reason %algb_cut]
        homo_one_funcomp[\<phi>reason %algb_cut]
        homo_mul_funcomp[\<phi>reason %algb_cut]

subsubsection \<open>Function Update\<close>

\<phi>reasoner_group algb_fun_upd_1 = (1300, [1300, 1330]) for \<open>_ (fun_upd 1 k)\<close> in algb_prop
    \<open>Algebraic properties for \<open>fun_upd 1 k\<close>\<close>
 and algb_fun_upd_1_comp = (1000, [1000, 1030]) for \<open>_ (\<lambda>x. fun_upd 1 k (f x))\<close>
                                                in algb_prop and < algb_fun_upd_1
    \<open>Algebraic properties for \<open>\<lambda>x. fun_upd 1 k (f x)\<close>\<close>

lemma homo_mul_carrier_fun_upd [\<phi>reason %algb_fun_upd_1]:
  \<open>homo_mul_carrier (fun_upd (1::'k \<Rightarrow> 'a::sep_carrier_1) k)\<close>
  unfolding homo_mul_carrier_def
  by simp

lemma homo_mul_carrier_fun_upd' [\<phi>reason %algb_fun_upd_1_comp]:
  \<open> homo_mul_carrier f
\<Longrightarrow> homo_mul_carrier (\<lambda>x. fun_upd (1 :: 'k \<Rightarrow> 'a::sep_carrier_1) k (f x))\<close>
  unfolding homo_mul_carrier_def
  by clarsimp

lemma closed_homo_sep_disj_fun_upd [\<phi>reason %algb_fun_upd_1]:
  \<open>closed_homo_sep_disj (fun_upd (1 :: 'k \<Rightarrow> 'a::sep_magma_1) k)\<close>
  unfolding closed_homo_sep_disj_def
  by (simp add: sep_disj_fun_def)

lemma closed_homo_sep_disj_fun_upd' [\<phi>reason %algb_fun_upd_1_comp]:
  \<open> closed_homo_sep_disj f
\<Longrightarrow> closed_homo_sep_disj (\<lambda>x. fun_upd (1 :: 'k \<Rightarrow> 'a::sep_magma_1) k (f x))\<close>
  unfolding closed_homo_sep_disj_def
  by (simp add: sep_disj_fun_def)

lemma homo_sep_mult_fun_upd[\<phi>reason %algb_fun_upd_1]:
  \<open>homo_sep_mult (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k)\<close>
  unfolding homo_sep_mult_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_sep_mult_fun_upd'[\<phi>reason %algb_fun_upd_1_comp]:
  \<open> homo_sep_mult f
\<Longrightarrow> homo_sep_mult (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x))\<close>
  unfolding homo_sep_mult_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_one_fun_upd[\<phi>reason %algb_fun_upd_1]:
  \<open>homo_one (fun_upd 1 k)\<close>
  unfolding homo_one_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_one_fun_upd'[\<phi>reason %algb_fun_upd_1_comp]:
  \<open> homo_one f
\<Longrightarrow> homo_one (\<lambda>x. fun_upd 1 k (f x))\<close>
  unfolding homo_one_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_sep_fun_upd[\<phi>reason %algb_fun_upd_1]:
  \<open> homo_sep (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k) \<close>
  by (rule homo_sep.intro; simp add: homo_sep_mult_fun_upd homo_sep_disj_def)

lemma homo_sep_fun_upd'[\<phi>reason %algb_fun_upd_1_comp]:
  \<open> homo_sep f
\<Longrightarrow> homo_sep (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x)) \<close>
  unfolding homo_sep_def
  by (simp add: homo_sep_mult_fun_upd' homo_sep_disj_def)

lemma closed_homo_sep_fun_upd[\<phi>reason %algb_fun_upd_1]:
  \<open> closed_homo_sep (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k) \<close>
  by (rule closed_homo_sep.intro; simp add: homo_sep_fun_upd closed_homo_sep_disj_fun_upd)

lemma closed_homo_sep_fun_upd'[\<phi>reason %algb_fun_upd_1_comp]:
  \<open> closed_homo_sep f
\<Longrightarrow> closed_homo_sep (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x)) \<close>
  unfolding closed_homo_sep_def
  by (simp add: closed_homo_sep_disj_fun_upd' homo_sep_fun_upd')

lemma [\<phi>reason %algb_fun_upd_1_comp]:
  \<open> constant_1 \<psi>
\<Longrightarrow> constant_1 (\<lambda>x. fun_upd 1 k (\<psi> x))\<close>
  unfolding constant_1_def
  by simp


subsubsection \<open>With Discrete Algebra\<close>

declare homo_sep_discrete [\<phi>reason %algb_cut+30]
        closed_homo_sep_discrete [\<phi>reason %algb_cut+30]


subsubsection \<open>Push map\<close>

declare homo_mul_carrier_push_map [\<phi>reason %algb_cut]
        closed_homo_sep_push_map [\<phi>reason %algb_cut]
        homo_sep_push_map [\<phi>reason %algb_cut]
        homo_one_push_map [\<phi>reason %algb_cut]
        module_scalar_identity_push_map [\<phi>reason %algb_cut]
        module_scalar_assoc_push_map [\<phi>reason %algb_cut]

subsubsection \<open>Share Division\<close>

lemma homo_mul_carrier_share [\<phi>reason %algb_cut]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_mul_carrier ((\<odivr>) n :: 'a::share_carrier \<Rightarrow> 'a)\<close>
  unfolding homo_mul_carrier_def Premise_def
  by (clarsimp simp add: share_carrier_closed)

lemma homo_mul_carrier_share_1[\<phi>reason %algb_cut+10]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_mul_carrier ((\<odivr>) n :: 'a::share_carrier_1 \<Rightarrow> 'a)\<close>
  unfolding homo_mul_carrier_def Premise_def
  by (clarsimp simp add: share_carrier_closed_1)

lemma homo_one_share[\<phi>reason %algb_cut]:
  \<open>homo_one ((\<odivr>) n :: 'a::share_one \<Rightarrow> 'a)\<close>
  unfolding homo_one_def
  by simp

lemma homo_sep_mult_share0[\<phi>reason %algb_cut]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep_mult ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_mult_def Premise_def
  by (simp add: share_sep_right_distrib_0)

lemma homo_sep_mult_share[\<phi>reason %algb_cut+10]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_sep_mult ((\<odivr>) n :: 'a::share_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_mult_def Premise_def
  by (simp add: share_sep_right_distrib)

lemma homo_sep_disj_share0[\<phi>reason %algb_cut]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep_disj ((\<odivr>) n :: 'a::share_sep_disj \<Rightarrow> 'a)\<close>
  unfolding homo_sep_disj_def Premise_def
  by simp

lemma homo_sep_disj_share [\<phi>reason %algb_cut+10]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_sep_disj ((\<odivr>) n :: 'a::{share_sep_disj, share_one, sep_magma_1} \<Rightarrow> 'a)\<close>
  unfolding homo_sep_disj_def Premise_def
  by (cases \<open>n = 0\<close>; simp)

lemma closed_homo_sep_disj_share0[\<phi>reason %algb_cut]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> closed_homo_sep_disj ((\<odivr>) n :: 'a::share_sep_disj \<Rightarrow> 'a)\<close>
  unfolding closed_homo_sep_disj_def Premise_def
  by simp

lemma homo_sep_share0[\<phi>reason %algb_cut]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_def Premise_def
  by (simp add: homo_sep_mult_share0 homo_sep_disj_share0)

lemma homo_sep_share [\<phi>reason %algb_cut]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_sep ((\<odivr>) n :: 'a::share_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_def Premise_def
  by (simp add: homo_sep_mult_share homo_sep_disj_share)

lemma closed_homo_sep_share[\<phi>reason %algb_cut]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> closed_homo_sep ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding closed_homo_sep_def Premise_def
  by (simp add: homo_sep_share0 closed_homo_sep_disj_share0)

lemma [\<phi>reason %algb_cut]:
  \<open>constant_1 ((\<odivr>) 0 :: 'a::share_one \<Rightarrow> 'a)\<close>
  unfolding constant_1_def
  by simp

declare module_scalar_assoc_share0   [\<phi>reason %algb_cut, assertion_simps]
        module_scalar_assoc_share    [\<phi>reason %algb_cut+10, assertion_simps]
        module_scalar_identity_share [\<phi>reason %algb_cut, assertion_simps]
        module_S_distr_share         [\<phi>reason %algb_cut+10]
        module_S_distr_share_0       [\<phi>reason %algb_cut]

subsubsection \<open>Map Option\<close>

declare homo_one_map_option [\<phi>reason %algb_cut]
        homo_mul_carrier_map_option [\<phi>reason %algb_cut]
        closed_homo_sep_map_option [\<phi>reason %algb_cut]
        homo_sep_map_option [\<phi>reason %algb_cut]
        homo_share_map_option [\<phi>reason %algb_cut]


subsubsection \<open>Some\<close>

lemma homo_mul_carrier_Some[simp, \<phi>reason %algb_cut]:
  \<open> homo_mul_carrier Some \<close>
  unfolding homo_mul_carrier_def
  by simp

lemma homo_sep_Some[simp, \<phi>reason %algb_cut]:
  \<open> homo_sep Some \<close>
  unfolding homo_sep_def homo_sep_mult_def homo_sep_disj_def
  by simp

lemma closed_homo_sep_Some[simp, \<phi>reason %algb_cut]:
  \<open> closed_homo_sep Some \<close>
  unfolding closed_homo_sep_def closed_homo_sep_disj_def
  by simp


subsubsection \<open>Share\<close>

lemma [\<phi>reason %algb_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n
\<Longrightarrow> homo_mul_carrier (Share n) \<close>
  unfolding homo_mul_carrier_def Premise_def
  by clarsimp

text \<open>\<open>homo_sep_disj (Share n :: 'a::discrete_semigroup \<Rightarrow> 'a share)\<close> and
      \<open>homo_sep_mult (Share n :: 'a::discrete_semigroup \<Rightarrow> 'a share)\<close> are covered by \<open>homo_sep_disj_discrete\<close>\<close>


subsubsection \<open>Annotation of Scalar Multiplication\<close>

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> homo_mul_carrier (\<psi> s)
\<Longrightarrow> homo_mul_carrier (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> homo_one (\<psi> s)
\<Longrightarrow> homo_one (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> homo_sep_mult (\<psi> s)
\<Longrightarrow> homo_sep_mult (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> homo_sep_disj (\<psi> s)
\<Longrightarrow> homo_sep_disj (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> closed_homo_sep_disj (\<psi> s)
\<Longrightarrow> closed_homo_sep_disj (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> homo_sep (\<psi> s)
\<Longrightarrow> homo_sep (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> closed_homo_sep (\<psi> s)
\<Longrightarrow> closed_homo_sep (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason default %algb_default[bottom]]:
  \<open> constant_1 (\<psi> s)
\<Longrightarrow> constant_1 (scalar_mult \<psi> s)\<close>
  unfolding scalar_mult_def
  by simp


section \<open>Supplementary Algebraic Operations\<close>

subsection \<open>Disjoint Union of Function\<close>

abbreviation fun_disj_union :: \<open>('k \<Rightarrow> 'v) \<Rightarrow> 'k set \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> 'k \<Rightarrow> 'v\<close> ("_ \<oplus>\<^sub>f[_] _" [65,10,66] 65)
  where \<open>fun_disj_union f K\<^sub>g g \<equiv> (\<lambda>k. if k \<in> K\<^sub>g then g k else f k)\<close>

subsection \<open>Commutative Morphism\<close>

(* A --\<psi>'--> B'
   \<down> \<phi>       \<down> \<phi>'
   B --\<psi> --> C *)
definition fun_commute :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b') \<Rightarrow> ('b' \<Rightarrow> 'c) \<Rightarrow> bool\<close>
  where \<open>fun_commute \<psi> \<phi> \<psi>' \<phi>' \<longleftrightarrow> (\<psi> o \<phi> = \<phi>' o \<psi>') \<close>
  \<comment> \<open>Given \<open>\<psi>\<close> and \<open>\<phi>\<close>, looks for what are their variant \<open>\<psi>'\<close> and \<open>\<phi>'\<close> (maybe varied in type or
      parameters) giving the swapping of them.\<close>

declare [[\<phi>reason_default_pattern
  \<open>fun_commute ?\<psi> ?\<phi> ?\<psi>' ?\<phi>'\<close> \<Rightarrow> \<open>fun_commute ?\<psi> ?\<phi> _ _\<close> \<open>fun_commute _ _ ?\<psi>' ?\<phi>'\<close> (100) ]]

subsubsection \<open>Reasoning Configure\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> fun_commute \<psi> \<phi> \<psi>' \<phi>' \<longrightarrow> (\<forall>x. \<psi> (\<phi> x) = \<phi>' (\<psi>' x)) @action \<A>EIF \<close>
  unfolding Action_Tag_def fun_commute_def fun_eq_iff
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> (\<forall>x. \<psi> (\<phi> x) = \<phi>' (\<psi>' x)) \<longrightarrow> fun_commute \<psi> \<phi> \<psi>' \<phi>' @action \<A>ESC \<close>
  unfolding Action_Tag_def fun_commute_def fun_eq_iff
  by simp
  

subsubsection \<open>Fallback\<close>

lemma [\<phi>reason %algb_falling_lattice for \<open>fun_commute ?var_\<phi> ?var_\<psi> _ _\<close>
                                     except \<open>fun_commute _ _ ?var_\<phi> ?var_\<psi>\<close>]:
  \<open> fun_commute \<phi>' \<psi>' \<phi> \<psi>
\<Longrightarrow> fun_commute \<psi> \<phi> \<psi>' \<phi>'\<close>
  unfolding fun_commute_def
  by (rule; simp)

subsubsection \<open>Instances\<close>

lemma [\<phi>reason %algb_cut]:
  \<open>fun_commute f f f f\<close>
  unfolding fun_commute_def ..

lemma [\<phi>reason %algb_cut]:
  \<open>fun_commute (scalar_mult (\<odivr>) n) (fun_upd 1 k :: 'b \<Rightarrow> 'a \<Rightarrow> 'b::share_one) (scalar_mult (\<odivr>) n) (fun_upd 1 k)\<close>
  unfolding fun_commute_def
  by (clarsimp simp add: fun_eq_iff share_fun_def)

lemma [\<phi>reason %algb_cut]:
  \<open>fun_commute (fun_upd 1 k :: 'b \<Rightarrow> 'a \<Rightarrow> 'b::share_one) (scalar_mult (\<odivr>) n) (fun_upd 1 k) (scalar_mult (\<odivr>) n)\<close>
  unfolding fun_commute_def
  by (clarsimp simp add: fun_eq_iff share_fun_def)

lemma [\<phi>reason %algb_cut]:
  \<open> fun_commute (scalar_mult (\<tribullet>\<^sub>m) k :: ('a list \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b::share_one)
                (scalar_mult (\<odivr>) n) (scalar_mult (\<tribullet>\<^sub>m) k) (scalar_mult (\<odivr>) n) \<close>
  unfolding fun_commute_def fun_eq_iff
  by (clarsimp simp add: push_map_def share_fun_def)

lemma [\<phi>reason %algb_cut]:
  \<open> fun_commute (scalar_mult (\<odivr>) n :: ('a list \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b::share_one)
                (scalar_mult (\<tribullet>\<^sub>m) k) (scalar_mult (\<odivr>) n) (scalar_mult (\<tribullet>\<^sub>m) k) \<close>
  unfolding fun_commute_def fun_eq_iff
  by (clarsimp simp add: push_map_def share_fun_def)

lemma [\<phi>reason default %algb_falling_lattice for \<open>fun_commute _ _ _ _\<close>]:
  \<open> TRACE_FAIL TEXT(\<open>The commutativity for\<close> (fun_commute \<psi> \<phi> \<psi>' \<phi>') \<open>is not given\<close>)
\<Longrightarrow> fun_commute \<psi> \<phi> \<psi>' \<phi>' \<close>
  unfolding TRACE_FAIL_def
  by blast

(*

*)





end