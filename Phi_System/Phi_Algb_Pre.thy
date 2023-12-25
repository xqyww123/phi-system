theory Phi_Algb_Pre
  imports IDE_CP_Reasoning1
          Phi_Algebras.Map_of_Tree
          Phi_Algebras.LCRO_Interval
          Phi_Algebras.Len_Intvl
begin 

section \<open>Setup Reasoning Rules\<close>

subsection \<open>List\<close>

subsubsection \<open>Length Preserving Maps\<close>

\<phi>reasoner_group length_preserving_map__all = (100, [1, 2000]) for \<open>length_preserving_map D f\<close> \<open>\<close>
  and length_preserving_map = (1000, [1000,1030]) in length_preserving_map__all \<open>\<close>
  and length_preserving__default = (10, [10, 10]) in length_preserving_map__all \<open>\<close>

declare [[
  \<phi>reason_default_pattern \<open>length_preserving_map _ ?f\<close> \<Rightarrow> \<open>length_preserving_map _ ?f\<close> (100),
  \<phi>default_reasoner_group \<open>length_preserving_map _ ?f\<close> : %length_preserving_map (100)
]]

declare length_preserving_map__map[\<phi>reason add]
        length_preserving_map__id [\<phi>reason add]
        length_preserving_map__id'[\<phi>reason add]
        length_preserving_map__funcomp [\<phi>reason add]

        length_preserving_map__list_upd_map  [\<phi>reason add]

        length_preserving_map__sublist_map_R [\<phi>reason add]
        length_preserving_map__sublist_map_L [\<phi>reason add]

lemma [\<phi>reason default %length_preserving__default]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. length (f x) = length x)
\<Longrightarrow> length_preserving_map D f \<close>
  unfolding length_preserving_map_def Premise_def
  by simp



subsubsection \<open>Declarations\<close>

lemmas [\<phi>safe_simp] =
  sublist_map_L_id sublist_map_R_id sublist_map_L_id' sublist_map_R_id'
  list_upd_map_const_f

subsection \<open>Len Interval\<close>

lemmas [\<phi>safe_simp] =
  len_intvl.sel len_intvl.collapse len_intvl.pred_inject len_intvl.pred_True len_intvl.rel_eq
  len_intvl.size len_intvl.simps
  Len_Intvl.set_def plus_len_intvl dom_of_add_len_intvl plus_len_intvl_start plus_len_intvl_len

  shift_by_nat_nat_def shift_by_nat_int_def

lemma atLeastLessThan_singleton_alt[\<phi>safe_simp]:
  \<open> {i..<i + 1} = {i} \<close>
  for i :: nat
  by simp

section \<open>Arithmetic Evaluation\<close>

consts \<A>arith_eq :: action

subsection \<open>Preliminary\<close>


definition cond ("?\<^sub>+") where \<open>?\<^sub>+ C x = (if C then Some x else None) \<close>

hide_const (open) cond

lemma conditioned_eq_red[simp]:
  \<open> ?\<^sub>+ True A = ?\<^sub>+ True B \<longleftrightarrow> A = B \<close>
  \<open> ?\<^sub>+ False A = ?\<^sub>+ False B \<close>
  unfolding cond_def
  by simp_all

lemma conditioned_plus[simp]:
  \<open> ?\<^sub>+ C A + ?\<^sub>+ C B = ?\<^sub>+ C (A + B) \<close>
  unfolding cond_def
  by clarsimp

lemma conditioned_times[simp]:
  \<open> ?\<^sub>+ C A * ?\<^sub>+ C B = ?\<^sub>+ C (A * B) \<close>
  unfolding cond_def
  by clarsimp

lemma conditioned_plus_red[simp]:
  \<open> ?\<^sub>+ False A + ?\<^sub>+ C B = ?\<^sub>+ C B \<close>
  \<open> ?\<^sub>+ C B + ?\<^sub>+ False A = ?\<^sub>+ C B \<close>
  \<open> X + ?\<^sub>+ False A + ?\<^sub>+ C B = X + ?\<^sub>+ C B \<close>
  \<open> X + ?\<^sub>+ C B + ?\<^sub>+ False A = X + ?\<^sub>+ C B \<close>
  unfolding cond_def
  by simp_all


subsection \<open>Partial Addition\<close>

definition dabc_equation
  where \<open>dabc_equation d a b c \<longleftrightarrow>
      (d + a = b + c) \<and>
      (\<exists>x. x + c = a \<and> d + x = b \<and> x ##\<^sub>+ c \<and> d ##\<^sub>+ x) \<and>
      d ##\<^sub>+ a \<and> b ##\<^sub>+ c \<close>
  \<comment> \<open>in principle, \<open>d, c \<noteq> 0\<close>\<close>

definition equation\<^sub>3\<^sub>1
  where \<open>equation\<^sub>3\<^sub>1 d a c b \<longleftrightarrow> (d + a + c = b) \<and> d + a ##\<^sub>+ c \<and> d ##\<^sub>+ a\<close>

definition equation\<^sub>3\<^sub>1_cond
  where \<open>equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d a da c b \<longleftrightarrow> (?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True a + ?\<^sub>+ C\<^sub>c c = ?\<^sub>+ True b) \<and>
                                             (?\<^sub>+ True da = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True a) \<and>
                                             (C\<^sub>c \<longrightarrow> da ##\<^sub>+ c) \<and> (C\<^sub>d \<longrightarrow> d ##\<^sub>+ a)\<close>

definition equation\<^sub>2\<^sub>1
  where \<open>equation\<^sub>2\<^sub>1 d a b \<longleftrightarrow> (d + a = b) \<and> d ##\<^sub>+ a\<close>

lemma dabc_equation_D_main:
  \<open>dabc_equation d a b c \<Longrightarrow> d + a = b + c \<and> d ##\<^sub>+ a \<and> b ##\<^sub>+ c\<close>
  unfolding dabc_equation_def
  by blast

text \<open>Solves partial addition equations consisting of

\<^item> \<open>given + ?unknown = given\<close>, \<open>?unknown + given = given\<close>,
  \<open>given = given + ?unknown\<close>, \<open>given = ?unknown + given\<close>
\<^item> \<open>given + ?unknown = ?unknown + given\<close>, \<open>?unknown + given = given + ?unknown\<close> (only for non-commutative group)
\<^item> \<open>?\<^sub>+ ?unknown + ?\<^sub>+ given + ?\<^sub>+ ?unknown = ?\<^sub>+ given\<close>,
  \<open>?\<^sub>+ given = ?\<^sub>+ ?unknown + ?\<^sub>+ given + ?\<^sub>+ ?unknown\<close> (only for non-commutative group)

NOTE, the reasoning ignores any case when the given in the LHS equals the given in the RHS.
You MUST check the trivial case before calling the reasoning process if can happen.

Note some forms are only meaningful for non-commutative group as if not they can be reduced to the
first form.
Also not, as addition can be associative, we use \<open>id\<close> to annotate explicitly each element in the equation.
For instance, \<open>id a + id b + id c = id d\<close> to distinguish with \<open>id (a + b) + id c = id d\<close>.

System rules first normalize the problem into one of
\<^item> \<open>equation\<^sub>2\<^sub>1\<close> \<open>?unknown_d + given_a = given_b\<close> (the only property required in commutative algebra) or
  \<open>equation\<^sub>2\<^sub>1\<close> \<open>given_b + ?unknown_c = given_a\<close> (only for non-commutative algebra)
\<^item> \<open>dabc_equation ?unknown given given ?unknown\<close> (only for non-commutative algebra)
\<^item> \<open>equation\<^sub>3\<^sub>1\<close> \<open>?\<^sub>+ ?unknown + ?\<^sub>+ given + ?\<^sub>+ ?unknown = ?\<^sub>+ given\<close> (necessary for non-commutative algebra, optional
    for commutative algebra in which it reduces to \<open>?unknown_d + given_a = given_b\<close>)

Then the above three forms are what user rules have to handle for specific algebras.

There are pre-built reasoning rules for,
\<^item> cancellative and canonically ordered commutative monoid, including the version for both partial algebras
  and total. This is the weakest algebraic structure to have a general algorithm,
  if an algorithm deciding the order relation is assumed.
\<^item> group, (only that for total algebra is installed), which is though not the minimal requirement,
  the weakest one available in Isabelle standard library, as the minimal one, quasigroup, is not
  formalized in Isabelle standard library.
\<close>

\<phi>reasoner_group \<A>_partial_add = (1000, [1, 4000]) for \<open>_ = _ @action \<A>arith_eq\<close>
      \<open>Decision procedure solving equantions of partial additive groups, with finding appropriate instantiations
       for schematic variables inside.\<close>
  and \<A>_partial_add_default = (10, [10,20]) in \<A>_partial_add \<open>\<close>
  and \<A>_partial_add_success = (4000, [4000, 4000]) for \<open>_ = _ @action \<A>arith_eq\<close> in \<A>_partial_add
      \<open>Rules leading to success directly\<close>
  and \<A>_partial_add__top = (3800, [3800, 3899]) in \<A>_partial_add and < \<A>_partial_add_success \<open>\<close>
  and \<A>_partial_add_normalizing = (3000, [2801, 3399]) in \<A>_partial_add and < \<A>_partial_add__top
      \<open>Rules normalizing the reasoning\<close>
  and \<A>_partial_add_splitting = (2500, [2500, 2599]) in \<A>_partial_add and < \<A>_partial_add_normalizing
      \<open>Spliting a complicated equation like \<open>a + b + c = d\<close> into several minimal equations \<open>a + b = c\<close>\<close>
  and \<A>_partial_add_cut = (1000, [1000, 1100]) in \<A>_partial_add and < \<A>_partial_add_splitting
      \<open>Cutting rules\<close>
  and \<A>_partial_add_specific = (1300, [1300, 1700]) in \<A>_partial_add and > \<A>_partial_add_cut
      \<open>for speicifc structures\<close>

\<phi>reasoner_group EIF_dabc = (%cutting, [10, 3000]) for \<open>\<r>EIF (dabc_equation d a b c) what\<close>
                                                   in extract_pure_all
      \<open>extracting pure facts implied inside a dbac-equation of specific algberas\<close>
  and EIF_dabc_default = (5, [5,5]) in extract_pure_all and < EIF_dabc
      \<open>default rules\<close>


declare [[
  \<phi>reason_default_pattern
      \<open>?Eq @action \<A>arith_eq\<close> \<Rightarrow> \<open>?Eq @action \<A>arith_eq\<close> (10)
  and \<open>equation\<^sub>3\<^sub>1 _ ?a _ ?b\<close> \<Rightarrow> \<open>equation\<^sub>3\<^sub>1 _ ?a _ ?b\<close>     (100)
  and \<open>equation\<^sub>3\<^sub>1_cond _ _ _ ?a _ _ ?b\<close> \<Rightarrow>
      \<open>equation\<^sub>3\<^sub>1_cond _ _ _ ?a _ _ ?b\<close>                (100)

  and \<open> ?\<^sub>+ _ _ + ?\<^sub>+ True ?b + ?\<^sub>+ _ _ = ?\<^sub>+ True ?a @action \<A>arith_eq \<close> \<Rightarrow>
      \<open> ?\<^sub>+ _ _ + ?\<^sub>+ True ?b + ?\<^sub>+ _ _ = ?\<^sub>+ True ?a @action \<A>arith_eq \<close>    (100)
  and \<open>dabc_equation _ ?a ?b _\<close> \<Rightarrow> \<open>dabc_equation _ ?a ?b _\<close>             (100)

  and \<open>equation\<^sub>2\<^sub>1 ?c ?a ?b\<close> \<Rightarrow> \<open>ERROR TEXT((equation\<^sub>2\<^sub>1 ?c ?a ?b) \<open>must be indicated with explicit LPR pattern\<close>)\<close> (0),

  \<phi>default_reasoner_group
      \<open>\<r>EIF (dabc_equation _ _ _ _) _ \<close> : %EIF_dabc            (100)
]]


subsubsection \<open>Extract Implied Facts inside\<close>

lemma [\<phi>reason default %EIF_dabc_default]:
  \<open> \<r>EIF (dabc_equation d a b c) (d + a = b + c \<and> d ##\<^sub>+ a \<and> b ##\<^sub>+ c)\<close>
  unfolding \<r>EIF_def dabc_equation_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF (equation\<^sub>2\<^sub>1 d a b) (b = d + a \<and> d ##\<^sub>+ a) \<close>
  unfolding \<r>EIF_def equation\<^sub>2\<^sub>1_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF (equation\<^sub>3\<^sub>1 d b c a) (a = d + b + c \<and> d ##\<^sub>+ b \<and> d + b ##\<^sub>+ c) \<close>
  unfolding \<r>EIF_def equation\<^sub>3\<^sub>1_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF (equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d b db c a)
     (?\<^sub>+ True a = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True b + ?\<^sub>+ C\<^sub>c c \<and>
      (?\<^sub>+ True db = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True b) \<and>
      (C\<^sub>c \<longrightarrow> db ##\<^sub>+ c) \<and> (C\<^sub>d \<longrightarrow> d ##\<^sub>+ b)) \<close>
  unfolding \<r>EIF_def equation\<^sub>3\<^sub>1_cond_def
  by simp


subsubsection \<open>Normalizing Equations\<close>

paragraph \<open>Flip\<close>

(*
lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>id _ + id ?var_d = id ?var_c + id _ @action \<A>arith_eq\<close>
                                           except \<open>id ?var_d + _ = _ + id ?var_c @action _\<close>]:
  \<open> id c + id b = id a + id d @action \<A>arith_eq
\<Longrightarrow> id a + id d = id c + id b @action \<A>arith_eq \<close>
  unfolding Action_Tag_def
  by simp
*)

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>equation\<^sub>2\<^sub>1 _ ?var_d (_::?'a::{comm_dom_of_add,ab_semigroup_add})\<close>
                                        except \<open>equation\<^sub>2\<^sub>1 ?var_d _ _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 c b a
\<Longrightarrow> equation\<^sub>2\<^sub>1 b c a \<close>
  for a :: \<open>'a::{comm_dom_of_add,ab_semigroup_add}\<close>
  unfolding Action_Tag_def equation\<^sub>2\<^sub>1_def
  by (simp add: add.commute dom_of_add_commuteI)

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>equation\<^sub>2\<^sub>1 _ ?var_d (_::?'a::partial_ab_semigroup_add)\<close>
                                        except \<open>equation\<^sub>2\<^sub>1 ?var_d _ _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 c b a
\<Longrightarrow> equation\<^sub>2\<^sub>1 b c a \<close>
  for a :: \<open>'a::partial_ab_semigroup_add\<close>
  unfolding Action_Tag_def equation\<^sub>2\<^sub>1_def
  by (simp add: dom_of_add_commuteI, metis partial_add_commute)


paragraph \<open>Reduce 3-1 equation on commutative algebra\<close>

lemma [\<phi>reason default %\<A>_partial_add_default]:
  \<open> equation\<^sub>2\<^sub>1 a b d
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond True False a b d undefined d \<close>
  for a :: \<open>'a::partial_ab_semigroup_add\<close>
  unfolding equation\<^sub>3\<^sub>1_cond_def equation\<^sub>2\<^sub>1_def
  by simp

lemma [\<phi>reason default %\<A>_partial_add_default+1]:
  \<open> equation\<^sub>2\<^sub>1 b c d
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond False True undefined b b c d \<close>
  for a :: \<open>'a::ab_semigroup_add\<close>
  unfolding equation\<^sub>3\<^sub>1_cond_def equation\<^sub>2\<^sub>1_def
  by simp


paragraph \<open>Error Check\<close>

lemma [\<phi>reason %\<A>_partial_add_normalizing
               for \<open>dabc_equation _ _ _ (_ :: ?'a :: partial_ab_semigroup_add)\<close>]:
  \<open> ERROR TEXT(\<open>Invalid equation\<close> (dabc_equation a d c b) \<open>on commutative group,\<close>
               \<open>which can always be reduced to either \<open>c + a = b\<close> or \<open>c + b = a\<close>. Some reasoning rule is configured wrong.\<close>)
\<Longrightarrow> dabc_equation a d c b \<close>
  unfolding ERROR_def
  by blast


subsubsection \<open>Algorithms for Specific Algberas\<close>

paragraph \<open>Direct Success\<close>

lemma [\<phi>reason %\<A>_partial_add_success for \<open>equation\<^sub>2\<^sub>1 ?a ?b (?a + ?b)\<close>
                                           \<open>equation\<^sub>2\<^sub>1 ?a ?var (?a + ?b)\<close>
                                           \<open>equation\<^sub>2\<^sub>1 ?var ?b (?a + ?b)\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a ##\<^sub>+ b
\<Longrightarrow> equation\<^sub>2\<^sub>1 a b (a + b) \<close>
  unfolding equation\<^sub>2\<^sub>1_def Premise_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_success for \<open>equation\<^sub>3\<^sub>1 ?a ?b ?c (?a + ?b + ?c)\<close>
                                           \<open>equation\<^sub>3\<^sub>1 ?var_a ?b ?var_c (_ + ?b + _)\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a ##\<^sub>+ b \<and> a + b ##\<^sub>+ c
\<Longrightarrow> equation\<^sub>3\<^sub>1 a b c (a + b + c) \<close>
  unfolding equation\<^sub>3\<^sub>1_def Premise_def  
  by simp

lemma [\<phi>reason %\<A>_partial_add_success for \<open>dabc_equation ?c (?x + ?d) (?c + ?x) ?d\<close>
                                           \<open>dabc_equation ?var_c (?x + ?d) (?c + ?x) ?var_d\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x ##\<^sub>+ d \<and> c ##\<^sub>+ x \<and> c ##\<^sub>+ x + d \<and> c + x ##\<^sub>+ d
\<Longrightarrow> dabc_equation c (x + d) (c + x) d \<close>
  for x :: \<open>'a :: partial_semigroup_add\<close>
  unfolding dabc_equation_def Premise_def
  using partial_add_assoc' by blast

lemma [\<phi>reason %\<A>_partial_add_success]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a ##\<^sub>+ b \<and> a + b ##\<^sub>+ c
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond True True a b (a + b) c (a + b + c)\<close>
  unfolding equation\<^sub>3\<^sub>1_cond_def Premise_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_success]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> b ##\<^sub>+ c
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond False True undefined b b c (b + c) \<close>
  unfolding equation\<^sub>3\<^sub>1_cond_def Premise_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_success]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a ##\<^sub>+ b
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond True False a b (a + b) undefined (a + b) \<close>
  unfolding equation\<^sub>3\<^sub>1_cond_def Premise_def
  by simp


paragraph \<open>Cancellative and Canonically Ordered Commutative Partial Monoid\<close>

text \<open>The rules do not conflict with those for groups because a canonically ordered monoid can never
  be a group.\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 ?a (?b - ?a) (?a :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}) \<close> 
                                      \<open>equation\<^sub>2\<^sub>1 _ (?var :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}) _ \<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b
\<Longrightarrow> equation\<^sub>2\<^sub>1 a (b - a) b\<close>
  for a :: \<open>'a::{partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}\<close>
  unfolding equation\<^sub>2\<^sub>1_def Premise_def
  by (simp add: partial_le_iff_add; force)

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 (?b - ?a) ?a (?a :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add})\<close>
                                       \<open>equation\<^sub>2\<^sub>1 (?var :: ?'a :: {partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}) _ _ \<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<le> b
\<Longrightarrow> equation\<^sub>2\<^sub>1 (b - a) a b \<close>
  for a :: \<open>'a::{partial_canonically_ordered_ab_semigroup_add, partial_cancel_ab_semigroup_add}\<close>
  unfolding equation\<^sub>2\<^sub>1_def Premise_def
  by (metis dom_of_add_commute partial_add_commute partial_add_diff_cancel_left' partial_le_iff_add)


paragraph \<open>Total Group\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 (?b - ?a) ?a ?b\<close>
                                       \<open>equation\<^sub>2\<^sub>1 ?var ?a ?b\<close> ]:
  \<open> equation\<^sub>2\<^sub>1 (b - a) a b \<close>
  for a :: \<open>'a::{total_dom_of_add, group_add}\<close>
  unfolding equation\<^sub>2\<^sub>1_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 ?a (?b - ?a) ?b\<close>
                                       \<open>equation\<^sub>2\<^sub>1 ?a ?var ?b\<close> ]:
  \<open> equation\<^sub>2\<^sub>1 a (b - a) b \<close>
  for a :: \<open>'a::{total_dom_of_add, ab_group_add}\<close>
  unfolding equation\<^sub>2\<^sub>1_def
  by (simp add: algebra_simps)


paragraph \<open>LCRO Interval\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 [?a,?b) [?b,?c) [?a,?c)\<close>
                                       \<open>equation\<^sub>2\<^sub>1 [?a,?b) ?var [?a,?c)\<close>
                                       \<open>equation\<^sub>2\<^sub>1 ?var [?b,?c) [?a,?c)\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] a \<le> b \<and> b \<le> c
\<Longrightarrow> equation\<^sub>2\<^sub>1 [a,b) [b,c) [a,c) \<close>
  unfolding Premise_def equation\<^sub>2\<^sub>1_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] a \<le> b \<and> b \<le> d \<and> b < c \<and> a \<le> c \<and> c \<le> d
\<Longrightarrow> dabc_equation [a,b) [b,d) [a,c) [c,d) \<close>
  unfolding dabc_equation_def Premise_def
  by (clarsimp, metis add_lcro_intvl lower_interval order_less_imp_le upper_interval)

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>3\<^sub>1 [?a,?b) [?b,?c) [?c,?d) [?a,?d)\<close>
                                       \<open>equation\<^sub>3\<^sub>1 ?var_c [?b,?c) ?var_d [?a,?d)\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] a \<le> b \<and> b \<le> c \<and> c \<le> d
\<Longrightarrow> equation\<^sub>3\<^sub>1 [a,b) [b,c) [c,d) [a,d) \<close>
  unfolding Premise_def equation\<^sub>3\<^sub>1_def
  by (simp, meson add_lcro_intvl order_trans upper_interval)

lemma [\<phi>reason %\<A>_partial_add_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] a \<le> b \<and> b \<le> c \<and> c \<le> d
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] a = b \<and>\<^sub>\<r> C\<^sub>A = False \<or>\<^sub>c\<^sub>u\<^sub>t C\<^sub>A = True
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] c = d \<and>\<^sub>\<r> C\<^sub>C = False \<or>\<^sub>c\<^sub>u\<^sub>t C\<^sub>C = True
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond C\<^sub>A C\<^sub>C [a,b) [b,c) [a,c) [c,d) [a,d)\<close>
  unfolding Premise_def equation\<^sub>3\<^sub>1_cond_def Orelse_shortcut_def Ant_Seq_def
  by (cases C\<^sub>A; cases C\<^sub>C; simp; meson add_lcro_intvl order_trans upper_interval)


paragraph \<open>Set\<close>

\<phi>reasoner_group \<A>_partial_add__set = (1300, [1300, 1300]) in \<A>_partial_add_specific \<open>Set\<close>

lemma [\<phi>reason %\<A>_partial_add__set for \<open>equation\<^sub>2\<^sub>1 ?var _ _\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] A \<subseteq> B
\<Longrightarrow> equation\<^sub>2\<^sub>1 (B - A) A B \<close>
  unfolding Premise_def equation\<^sub>2\<^sub>1_def
  by clarsimp blast


paragraph \<open>Len Intvl\<close>

subparagraph \<open>Direct\<close>

lemma [\<phi>reason %\<A>_partial_add_specific for \<open>equation\<^sub>2\<^sub>1 ?var (_::_ len_intvl) (_::_ len_intvl)\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>] len_intvl.len c \<ge> len_intvl.len b \<and>
                      len_intvl.start c + len_intvl.len c - len_intvl.len b = len_intvl.start b
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] a : \<lbrakk>len_intvl.start c : len_intvl.len c - len_intvl.len b\<rwpar>
\<Longrightarrow> equation\<^sub>2\<^sub>1 a b c\<close>
  unfolding equation\<^sub>2\<^sub>1_def Premise_def Simplify_def
  by (cases b; cases c; clarsimp)

lemma [\<phi>reason %\<A>_partial_add_specific for \<open>equation\<^sub>2\<^sub>1 (_::_ len_intvl) ?var (_::_ len_intvl)\<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>] len_intvl.len a \<le> len_intvl.len c \<and> len_intvl.start a = len_intvl.start c
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] b : \<lbrakk>len_intvl.start a + len_intvl.len a : len_intvl.len c - len_intvl.len a\<rwpar>
\<Longrightarrow> equation\<^sub>2\<^sub>1 a b c \<close>
  unfolding equation\<^sub>2\<^sub>1_def Premise_def Simplify_def
  by (cases a; cases c; clarsimp)

lemma [\<phi>reason %\<A>_partial_add_specific]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>]
      len_intvl.start c < len_intvl.start b \<and>
      len_intvl.start b \<le> len_intvl.start c + len_intvl.len c \<and>
      len_intvl.start c + len_intvl.len c \<le> len_intvl.start b + len_intvl.len b
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] a : \<lbrakk>len_intvl.start c : len_intvl.start b - len_intvl.start c\<rwpar>
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] d : \<lbrakk>len_intvl.start c + len_intvl.len c : len_intvl.start b + len_intvl.len b - len_intvl.start c - len_intvl.len c\<rwpar>
\<Longrightarrow> dabc_equation a b c d\<close>
  unfolding dabc_equation_def Premise_def Simplify_def
  by (cases b; cases c; clarsimp simp: len_intvl_ex;
      smt (verit, del_insts) add.assoc add.commute add_diff_cancel_left' le_iff_add)
      

lemma [\<phi>reason %\<A>_partial_add_specific]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>]
            len_intvl.start d \<le> len_intvl.start b \<and>
            len_intvl.start b + len_intvl.len b \<le> len_intvl.start d + len_intvl.len d
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] a : \<lbrakk>len_intvl.start d : len_intvl.start b - len_intvl.start d\<rwpar>
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] c : \<lbrakk>len_intvl.start b + len_intvl.len b : len_intvl.start d + len_intvl.len d - len_intvl.start b - len_intvl.len b\<rwpar>
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] ab : \<lbrakk>len_intvl.start d : len_intvl.start b - len_intvl.start d + len_intvl.len b\<rwpar>
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>] len_intvl.len a = 0 \<and>\<^sub>\<r> C\<^sub>a = False \<or>\<^sub>c\<^sub>u\<^sub>t C\<^sub>a = True \<comment> \<open>TODO: optimize the reasoning here by one step\<close>
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>] len_intvl.len c = 0 \<and>\<^sub>\<r> C\<^sub>c = False \<or>\<^sub>c\<^sub>u\<^sub>t C\<^sub>c = True \<comment> \<open>TODO: optimize the reasoning here by one step\<close>
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond C\<^sub>a C\<^sub>c a b ab c d \<close>
  unfolding equation\<^sub>3\<^sub>1_cond_def Premise_def Simplify_def \<r>Guard_def
            Orelse_shortcut_def Ant_Seq_def
  by (cases b; cases d; auto)


subparagraph \<open>Wrapped by set\<close>

\<phi>reasoner_group \<A>_partial_add__len_intvl_set = (1350, [1350, 1350])
                                                in \<A>_partial_add_specific and > \<A>_partial_add__set
                 \<open>Len_Intvl.set\<close>

lemma [\<phi>reason %\<A>_partial_add__len_intvl_set
           for \<open>equation\<^sub>2\<^sub>1 ?var (Len_Intvl.set _) (Len_Intvl.set _)\<close>
               \<open>equation\<^sub>2\<^sub>1 (Len_Intvl.set _) ?var (Len_Intvl.set _)\<close>]:
  \<open> equation\<^sub>2\<^sub>1 a b c
\<Longrightarrow> equation\<^sub>2\<^sub>1 (Len_Intvl.set a) (Len_Intvl.set b) (Len_Intvl.set c) \<close>
  unfolding Action_Tag_def equation\<^sub>2\<^sub>1_def Premise_def
  by (cases a; cases b; cases c; clarsimp simp add: plus_set_def set_eq_iff shift_by_nat_ord,
      metis (mono_tags, lifting) dual_order.asym not_le_imp_less order.strict_trans2 shift_by_nat_assoc shift_by_nat_ord)

lemma [\<phi>reason %\<A>_partial_add__len_intvl_set]:
  \<open> dabc_equation a b c d
\<Longrightarrow> dabc_equation (Len_Intvl.set a) (Len_Intvl.set b) (Len_Intvl.set c) (Len_Intvl.set d) \<close>
  unfolding dabc_equation_def
  apply (cases a; cases b; cases c; cases d; clarsimp simp add: plus_set_def set_eq_iff shift_by_nat_ord)
  subgoal for e f g h i j
    apply (rule)
    apply (smt (verit, best) dual_order.trans len_intvl.sel(1) len_intvl.sel(2) linorder_not_le plus_len_intvl_len plus_len_intvl_start shift_by_nat_assoc shift_by_nat_ord)
    apply rule
    apply (cases j; clarsimp)
    subgoal for k
      by (rule exI[where x=\<open>Len_Intvl.set \<lbrakk>shift_by_nat e f : k\<rwpar>\<close>], clarsimp,
          smt (verit, best) linorder_not_le order_le_less_trans shift_by_nat_assoc shift_by_nat_ord)
    by force .
    

lemma [\<phi>reason %\<A>_partial_add__len_intvl_set
           for \<open>equation\<^sub>3\<^sub>1 ?var (Len_Intvl.set _) ?var (Len_Intvl.set _)\<close>]:
  \<open> equation\<^sub>3\<^sub>1 a b c d
\<Longrightarrow> equation\<^sub>3\<^sub>1 (Len_Intvl.set a) (Len_Intvl.set b) (Len_Intvl.set c) (Len_Intvl.set d) \<close>
  unfolding equation\<^sub>3\<^sub>1_def
  by (cases a; cases b; cases c; clarsimp simp add: plus_set_def set_eq_iff shift_by_nat_ord,
      smt (verit, ccfv_SIG) dual_order.trans linorder_not_less shift_by_nat_assoc shift_by_nat_ord)

lemma [\<phi>reason %\<A>_partial_add__len_intvl_set]:
  \<open> equation\<^sub>3\<^sub>1_cond C\<^sub>a C\<^sub>c a b ab c d
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond C\<^sub>a C\<^sub>c (Len_Intvl.set a) (Len_Intvl.set b) (Len_Intvl.set ab) (Len_Intvl.set c) (Len_Intvl.set d) \<close>
  unfolding equation\<^sub>3\<^sub>1_cond_def Premise_def
  by ((cases a; cases b; cases c; cases C\<^sub>a; cases C\<^sub>c;
       clarsimp simp add: plus_set_def set_eq_iff shift_by_nat_ord),
      smt (verit, best) dual_order.trans linorder_not_less shift_by_nat_assoc shift_by_nat_ord,
      smt (z3) linorder_le_less_linear order.trans order_less_le_trans shift_by_nat_assoc shift_by_nat_ord,
      metis (no_types, lifting) not_le_imp_less order.strict_trans2 order_less_asym shift_by_nat_assoc shift_by_nat_ord)

subparagraph \<open>EIF\<close>

lemma dabc_equation__len_intvl_D:
  \<open>dabc_equation d a b c
\<Longrightarrow> d + a = b + c \<and>
    len_intvl.start b = len_intvl.start d \<and>
    len_intvl.start a = len_intvl.start d + len_intvl.len d \<and>
    len_intvl.start c = len_intvl.start d + len_intvl.len b \<and>
    len_intvl.len d \<le> len_intvl.len b \<and>
    len_intvl.len d + len_intvl.len a = len_intvl.len b + len_intvl.len c \<close>
  unfolding Action_Tag_def dabc_equation_def
  by clarsimp

lemma [\<phi>reason add]:
  \<open>\<r>EIF (dabc_equation d a b c)
       (d + a = b + c \<and>
        len_intvl.start b = len_intvl.start d \<and>
        len_intvl.start a = len_intvl.start d + len_intvl.len d \<and>
        len_intvl.start c = len_intvl.start d + len_intvl.len b \<and>
        len_intvl.len d \<le> len_intvl.len b \<and>
        len_intvl.len d + len_intvl.len a = len_intvl.len b + len_intvl.len c) \<close>
  unfolding \<r>EIF_def dabc_equation_def
  by clarsimp


(*
paragraph \<open>List\<close>

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 _ (_#_) (_#_)\<close>
                                       \<open>equation\<^sub>2\<^sub>1 (_ # _) ?var (_#_)\<close> ]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = z
\<Longrightarrow> equation\<^sub>2\<^sub>1 ys xs zs
\<Longrightarrow> equation\<^sub>2\<^sub>1 ys (x#xs) (z#zs) \<close>
  unfolding Premise_def equation\<^sub>2\<^sub>1_def plus_list_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 _ [] _\<close>,
       \<phi>reason %\<A>_partial_add_cut+10 for \<open>equation\<^sub>2\<^sub>1 _ ?var _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 zs [] zs @action \<A>arith_eq \<close>
  unfolding Premise_def Action_Tag_def plus_list_def
  by simp

lemma [\<phi>reason %\<A>_partial_add_cut for \<open>equation\<^sub>2\<^sub>1 [] _ _\<close> ]:
  \<open> equation\<^sub>2\<^sub>1 [] zs zs \<close>
  unfolding Premise_def Action_Tag_def plus_list_def
  by simp

text \<open>TODO:

\<^item> \<open>?unknown + given = given + ?unknown\<close> (only for non-commutative group)
\<^item> \<open>?unknown + given + ?unknown = given\<close> (only for non-commutative group)

need some ML
\<close>
*)

paragraph \<open>Arrow\<close>

lemma [\<phi>reason %\<A>_partial_add_specific for \<open>equation\<^sub>2\<^sub>1 _ _ (_ \<BRarrow> _)\<close>
                                            \<open>equation\<^sub>2\<^sub>1 _ (_ \<BRarrow> _) _\<close>
                                            \<open>equation\<^sub>2\<^sub>1 (_ \<BRarrow> _) _ _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 (s \<BRarrow> t) (t \<BRarrow> u) (s \<BRarrow> u) \<close>
  unfolding equation\<^sub>2\<^sub>1_def
  by simp



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
  and partial_add_overlaps_norm = (2500, [2500, 2500]) in partial_add_overlaps_all \<open>\<close>

declare [[\<phi>reason_default_pattern \<open>partial_add_overlaps ?a ?b\<close> \<Rightarrow> \<open>partial_add_overlaps ?a ?b\<close> (100)]]

subsubsection \<open>Default Implementation falling back to solving the equations\<close>

paragraph \<open>Commutative Additive Group\<close>

lemma [\<phi>reason default %partial_add_overlaps_default,
       \<phi>reason default %partial_add_overlaps_default_comm
       for \<open>partial_add_overlaps (_::_::ab_semigroup_add) _\<close>
           \<open>partial_add_overlaps (_::_::partial_ab_semigroup_add) _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 d a b
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default,
       \<phi>reason default %partial_add_overlaps_default_comm
       for \<open>partial_add_overlaps (_::_::ab_semigroup_add) _\<close>
           \<open>partial_add_overlaps (_::_::partial_ab_semigroup_add) _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 d b a
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

paragraph \<open>None_Commutative Additive Group\<close>

(*
lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id b + id c = id a @action \<A>arith_eq
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> id a + id d = id b @action \<A>arith_eq
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast
*)

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d a da c b
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d b db c a
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> dabc_equation d a b c
\<Longrightarrow> partial_add_overlaps a b \<close>
  unfolding Action_Tag_def partial_add_overlaps_def
  by blast

lemma [\<phi>reason default %partial_add_overlaps_default]:
  \<open> dabc_equation d a b c
\<Longrightarrow> partial_add_overlaps b a \<close>
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

lemma [\<phi>reason default %partial_add_overlaps_default]:
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

lemma [\<phi>reason %partial_add_overlaps_specific+11]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start a \<le> i \<and> i < len_intvl.start a + len_intvl.len a
\<Longrightarrow> partial_add_overlaps a \<lbrakk>i:Suc 0\<rwpar> \<close>
  unfolding partial_add_overlaps_def
  ..

lemma [\<phi>reason %partial_add_overlaps_specific+10]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start b \<le> i \<and> i < len_intvl.start b + len_intvl.len b
\<Longrightarrow> partial_add_overlaps \<lbrakk>i:Suc 0\<rwpar> b \<close>
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

paragraph \<open>Set\<close>

lemma [\<phi>reason %partial_add_overlaps_specific]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x \<in> S
\<Longrightarrow> partial_add_overlaps S {x} \<close>
  unfolding partial_add_overlaps_def ..

lemma [\<phi>reason %partial_add_overlaps_specific]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x \<in> S
\<Longrightarrow> partial_add_overlaps {x} S \<close>
  unfolding partial_add_overlaps_def ..

lemma [\<phi>reason %partial_add_overlaps_specific+1]:
  \<open> partial_add_overlaps S {var} \<close>
  unfolding partial_add_overlaps_def ..

lemma [\<phi>reason %partial_add_overlaps_specific+1]:
  \<open> partial_add_overlaps {var} S \<close>
  unfolding partial_add_overlaps_def ..


paragraph \<open>List\<close>

(*TODO*)


paragraph \<open>Permission\<close>

lemma [\<phi>reason default %partial_add_overlaps_specific]:
  \<open> partial_add_overlaps a b \<close> 
  for a :: rat
  unfolding partial_add_overlaps_def ..



subsection \<open>Multiplication Equations\<close>

definition common_multiplicator_2 :: \<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>common_multiplicator_2 mul a b c \<longleftrightarrow> mul a b = c\<close>

\<phi>reasoner_group common_multiplicator_2 = (1000, [1,3000]) for \<open>common_multiplicator_2 mul a b c\<close>
    \<open>Equation \<open>?a * b = c\<close>\<close>
  and common_multiplicator_2_algos = (1000, [1000, 1050]) in common_multiplicator_2
    \<open>default group for algorithms of specific algebras\<close>
  and common_multiplicator_2_direct_success = (2950, [2950, 2980]) in common_multiplicator_2 \<open>\<close>

declare [[\<phi>reason_default_pattern
    \<open>common_multiplicator_2 ?mul _ ?b ?c\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>explict pattern has to be given\<close>)\<close> (100),

  \<phi>default_reasoner_group
    \<open>common_multiplicator_2 _ _ _ _\<close> : %common_multiplicator_2_algos (100)
]]

subsubsection \<open>Algorithms for Specific Algberas\<close>

paragraph \<open>Direct Solution\<close>

lemma [\<phi>reason %common_multiplicator_2_direct_success for \<open>common_multiplicator_2 ?mul ?a _ (?mul ?a _)\<close>
                                                          \<open>common_multiplicator_2 ?mul ?a _ (?mul _ ?b)\<close> ]:
  \<open> common_multiplicator_2 mul a b (mul a b) \<close>
  unfolding common_multiplicator_2_def ..

paragraph \<open>List\<close>

\<phi>reasoner_group common_multiplicator_2_list =
  (%common_multiplicator_2_algos, [%common_multiplicator_2_algos, %common_multiplicator_2_algos+20]) \<open>\<close>


lemma [\<phi>reason %common_multiplicator_2_list[bottom] for \<open>common_multiplicator_2 (\<lambda>a b. b * a) ?var _ _\<close>]:
  \<open> common_multiplicator_2 (@) a b c
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] a' : a
\<Longrightarrow> common_multiplicator_2 (\<lambda>a b. b * a) a' b c \<close>
  unfolding common_multiplicator_2_def times_list_def Simplify_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list[bottom] for \<open>common_multiplicator_2 (\<lambda>a b. b * a) _ ?var _\<close>]:
  \<open> common_multiplicator_2 (@) a b c
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] b' : b
\<Longrightarrow> common_multiplicator_2 (\<lambda>a b. b * a) a b' c \<close>
  unfolding common_multiplicator_2_def times_list_def Simplify_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list+10 for \<open>common_multiplicator_2 (@) ?b _ ?b\<close>
                                                   \<open>common_multiplicator_2 (@) _ [] ?b\<close>]:
  \<open> common_multiplicator_2 (@) b [] b \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list+10 for \<open>common_multiplicator_2 (@) _ ?b ?b\<close>
                                                   \<open>common_multiplicator_2 (@) [] _ ?b\<close>]:
  \<open> common_multiplicator_2 (@) [] b b \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list+5 for \<open>common_multiplicator_2 (@) _ _ (_ # _)\<close>]:
  \<open> common_multiplicator_2 (@) a b L
\<Longrightarrow> common_multiplicator_2 (@) (h # a) b (h # L) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list+5 for \<open>common_multiplicator_2 (@) (_ @ _) _ (_ @ _)\<close>]:
  \<open> common_multiplicator_2 (@) a b c
\<Longrightarrow> common_multiplicator_2 (@) (L @ a) b (L @ c) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) ((_ # _) @ _) _ _\<close>]:
  \<open> common_multiplicator_2 (@) (h # L @ a) b c
\<Longrightarrow> common_multiplicator_2 (@) ((h # L) @ a) b c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) _ ((_ # _) @ _) _\<close>]:
  \<open> common_multiplicator_2 (@) a (h # L @ b) c
\<Longrightarrow> common_multiplicator_2 (@) a ((h # L) @ b) c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) _ _ ((_ # _) @ _)\<close>]:
  \<open> common_multiplicator_2 (@) a b (h # L @ c)
\<Longrightarrow> common_multiplicator_2 (@) a b ((h # L) @ c) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) ([] @ _) _ _\<close>]:
  \<open> common_multiplicator_2 (@) a b c
\<Longrightarrow> common_multiplicator_2 (@) ([] @ a) b c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) _ ([] @ _) _\<close>]:
  \<open> common_multiplicator_2 (@) a b c
\<Longrightarrow> common_multiplicator_2 (@) a ([] @ b) c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) _ _ ([] @ _)\<close>]:
  \<open> common_multiplicator_2 (@) a b c
\<Longrightarrow> common_multiplicator_2 (@) a b ([] @ c) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp


subsection \<open>Checking if a given element is an identity element\<close>

definition is_id_element :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>is_id_element template_one x \<longleftrightarrow> template_one = x\<close>

\<phi>reasoner_group is_id_element__all = (100, [10, 3000]) for \<open>is_id_element template_one x\<close>
      \<open>Checking if the given element \<open>x\<close> is an identity element unifying \<open>template_one\<close>\<close>
  and is_id_element = (1000, [1000,1030]) in is_id_element__all \<open>\<close>
  and is_id_element_direct = (2500, [2500, 2500]) in is_id_element__all and > is_id_element \<open>direct success\<close>

declare [[\<phi>reason_default_pattern \<open>is_id_element ?template ?one\<close> \<Rightarrow>
              \<open>ERROR TEXT(\<open>reasoner pattern has to be given for\<close> (is_id_element ?template ?one))\<close> (0),
          \<phi>default_reasoner_group \<open>is_id_element _ _\<close> : %is_id_element (100) ]]

subsubsection \<open>system\<close>

lemma [\<phi>reason %is_id_element_direct for \<open>is_id_element ?x ?x\<close>]:
  \<open> is_id_element x x \<close>
  unfolding is_id_element_def ..

subsubsection \<open>Set\<close>

lemma [\<phi>reason for \<open>is_id_element {_} {_}\<close>]:
  \<open> is_id_element {x} {x} \<close>
  unfolding is_id_element_def
  by simp

subsubsection \<open>List\<close>

lemma [\<phi>reason for \<open>is_id_element [] 0\<close>]:
  \<open> is_id_element [] 0 \<close>
  unfolding is_id_element_def
  by simp

subsubsection \<open>Len Intvl\<close>

lemma [\<phi>reason for \<open>is_id_element \<lbrakk>_ : Suc 0\<rwpar> \<lbrakk>_ : _\<rwpar> \<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>] len = 1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] i = j
\<Longrightarrow> is_id_element \<lbrakk>i : Suc 0\<rwpar> \<lbrakk>j : len\<rwpar> \<close>
  unfolding is_id_element_def Premise_def
  by simp

lemma [\<phi>reason for \<open>is_id_element \<lbrakk>_ : 1\<rwpar> \<lbrakk>_ : _\<rwpar> \<close>]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<n>\<o>-\<i>\<n>\<s>\<t>-\<s>\<a>\<f>\<e>] len = 1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] i = j
\<Longrightarrow> is_id_element \<lbrakk>i : 1\<rwpar> \<lbrakk>j : len\<rwpar> \<close>
  unfolding is_id_element_def Premise_def
  by simp


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
  \<open> \<r>EIF (local_inverse D f g) (\<forall>x \<in> D. g (f x) = x) \<close>
  unfolding \<r>EIF_def local_inverse_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC (\<forall>x \<in> D. g (f x) = x) (local_inverse D f g) \<close>
  unfolding \<r>ESC_def local_inverse_def
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
  \<open> \<r>EIF (homo_one \<psi>) (\<psi> 1 = 1) \<close>
  unfolding \<r>EIF_def homo_one_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC (\<psi> 1 = 1) (homo_one \<psi>) \<close>
  unfolding \<r>ESC_def homo_one_def
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
  \<open> \<r>EIF (homo_mul_carrier \<psi>) (\<forall>x. mul_carrier x \<longrightarrow> mul_carrier (\<psi> x)) \<close>
  unfolding homo_mul_carrier_def \<r>EIF_def
  by blast

lemma homo_mul_carrier_ESC:
  \<open> \<r>ESC (\<forall>x. mul_carrier x \<longrightarrow> mul_carrier (\<psi> x)) (homo_mul_carrier \<psi>) \<close>
  unfolding homo_mul_carrier_def \<r>ESC_def
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
  \<open> \<r>EIF (closed_homo_sep \<psi>) (closed_homo_sep \<psi>) \<close>
  unfolding \<r>EIF_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC (closed_homo_sep \<psi>) (closed_homo_sep \<psi>) \<close>
  unfolding \<r>ESC_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF (homo_sep \<psi>) (homo_sep \<psi>) \<close>
  unfolding \<r>EIF_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC (homo_sep \<psi>) (homo_sep \<psi>) \<close>
  unfolding \<r>ESC_def
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
  \<open> \<r>EIF (constant_1 \<psi>) (\<forall>x. \<psi> x = 1) \<close>
  unfolding \<r>EIF_def constant_1_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC (\<forall>x. \<psi> x = 1) (constant_1 \<psi>) \<close>
  unfolding \<r>ESC_def constant_1_def
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
  \<open> \<r>EIF (constantly_inside_carrier \<psi>) (\<forall>x. mul_carrier (\<psi> x)) \<close>
  unfolding \<r>EIF_def constantly_inside_carrier_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC (\<forall>x. mul_carrier (\<psi> x)) (constantly_inside_carrier \<psi>) \<close>
  unfolding \<r>ESC_def constantly_inside_carrier_def
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
  \<open> \<r>EIF (fun_commute \<psi> \<phi> \<psi>' \<phi>') (\<forall>x. \<psi> (\<phi> x) = \<phi>' (\<psi>' x)) \<close>
  unfolding \<r>EIF_def fun_commute_def fun_eq_iff
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC (\<forall>x. \<psi> (\<phi> x) = \<phi>' (\<psi>' x)) (fun_commute \<psi> \<phi> \<psi>' \<phi>') \<close>
  unfolding \<r>ESC_def fun_commute_def fun_eq_iff
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