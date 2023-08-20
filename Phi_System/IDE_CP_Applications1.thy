chapter \<open>IDE-CP Functions \& Applications - Part I\<close>


theory IDE_CP_Applications1
  imports IDE_CP_Core
  keywords "val" :: quasi_command
  abbrevs "<vals>" = "\<v>\<a>\<l>s"
      and "<orelse>" = "\<o>\<r>\<e>\<l>\<s>\<e>"
      and "<pattern>" = "\<p>\<a>\<t>\<t>\<e>\<r>\<n>"
      and "<traverse>" = "\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e>"
      and "<split>" = "\<s>\<p>\<l>\<i>\<t>"
      and "<strip>" = "\<s>\<t>\<r>\<i>\<p>"
begin

text \<open> 

Note: Our reasoning is a calculus of sequents, but not the sequent calculus.
      The \<^prop>\<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close> is a sequent \<open>X \<turnstile> Y\<close>.
TODO: Maybe we should rename the word 'sequent' in MLs to 'state' as it is proof state instead of a sequent.

TODO: move me somewhere

There are essentially two transformation mechanism in the system, \<exists>-free ToA and the To-Transformation.

\<exists>-free ToA is the major reasoning process in the system. It is between BI assertions and limited in
introducing existential quantification, i.e., it cannot open an abstraction.
This limitation is reasonable and also due to technical reasons.

When a transformation from \<open>x \<Ztypecolon> T\<close> introduces existentially quantification, e.g., to \<open>{ y \<Ztypecolon> U |y. P y }\<close>,
it opens the abstraction of \<open>x \<Ztypecolon> T\<close>.
The \<open>x\<close> has no enough information to determine a unique value of \<open>y\<close> but only a set of candidates,
which means the representation of \<open>y \<Ztypecolon> U\<close> is more specific and therefore in a lower abstraction level.
For example, \<open>x \<Ztypecolon> Q\<close> is a rational number and \<open>{ (a,b) \<Ztypecolon> \<int> \<times> \<int> |a b. a/b = x }\<close> is its representation.

As the major reasoning process in the system, the ToA reasoning should maintain the abstraction level,
and degenerate to a lower abstraction only when users ask so.
Reducing to a lower abstraction, should only happen when building the interfaces or internal
operations of the data structure.
Manually writing two annotations to open and to close the abstraction at the beginning and the ending
of the building of the interface, does not bring any thinking burden to users because the users of course
know, he is going to enter the representation of the abstraction in order to make the internal operation.
To-Transformation has capability to open an abstraction, as it supports the transformation introducing
existential quantification.

The technical difficulty to support introducing existential quantification is that, we instantiate
the existential quantification in the right side of a transformation goal to schematic variables
that can be instantiated to whatever later, so that we can enter the existential quantification
in the right and let the inner structure guide the next reasoning (like a goal-directed proof search).
The existential quantification at the left side is fixed before instantiating those in the right,
so the schematic variable can capture, i.e., can instantiate to any expression containing the fixed
existentially quantified variable of the left.
However, later when an existential quantification is introduced at the left side after
the instantiation of the right, the schematic variables cannot capture the new introduced existentially
quantified variables.
It is a deficiency of the current reasoning because it should not instantiate the right existential
quantification that early, but if we remain them, the quantifier brings a lot of troubles in the pattern
matching and the resolution of \<phi>-LPR. Just like the meta universal quantifier is specially processed
by the resolution of Isabelle's kernel, the handling of the existential quantification should also
be integrated in our resolution kernel, but it is hard and the performance would be a problem as
we cannot enter the kernel as what Isabelle's resolution does.

The expected resolution:
\<open>A a \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y a\<close>    \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<exists>a. Y a \<Longrightarrow> B\<close>
-------------------------------------------------------
                    \<open>\<exists>a. A a \<Longrightarrow> B\<close>


The To-Transformation is about a single \<phi>-type term \<open>x \<Ztypecolon> T\<close>. Given a \<phi>-type \<open>U\<close>, it transforms \<open>x \<Ztypecolon> T\<close>
to a \<phi>-type term \<open>y \<Ztypecolon> U\<close> with whatever \<open>y\<close> it could be, or even a set \<open>{ y \<Ztypecolon> U | y. P y }\<close>.


-------------------------------------------------------------------------------------

ToA reasoning in the system by default does not change the abstraction level. Therefore, they are
writen in a function form \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> U\<close> instead of a relation form
\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y\<close>. We also call this function form \<open>\<exists>\<close>-free ToA.

To open an abstraction, you can use To-Transformation:

    \<^verbatim>\<open>to \<open>List OPEN\<close>\<close>, in order to open \<open>List T\<close> into \<open>List Rep\<close>
    you can also use \<^verbatim>\<open>open_abstraction \<open>List _\<close>\<close> which is a syntax sugar of \<open>to \<open>List OPEN\<close>\<close>

To make an abstraction, just give the desired form and it invokes the synthesis process,

    \<^verbatim>\<open> \<open>_ \<Ztypecolon> MAKE U\<close> \<close>

Note you should not use To-Transformation to make an abstraction if the target \<open>U\<close> that you want to make
requires to be assembled from more than one \<phi>-type terms. It is because To-Transformation is used
to transform the first \<phi>-type term \<open>x \<Ztypecolon> T\<close> on your state sequent to whatever.
It considers the first \<phi>-type term only.


--------------------------------------------------------------------------------------

\<phi>-system provides 5 syntax to annotate \<phi>-types, or in another words, to invoke transformation.

\<^item> to \<open>the target \<phi>-type you want\<close>, it transforms the leading \<phi>-type term \<open>x \<Ztypecolon> T\<close> to \<open>{ y \<Ztypecolon> U |y. P y}\<close>
                                   for the given \<open>U\<close> and a set of object \<open>y\<close> it can be.
                                   It can also generate program code to achieve the target.
                                   For example, if the leading term is \<open>x \<Ztypecolon> \<nat>\<close>, the \<open>to Float\<close> can
                                   generate the program casting the integer.
\<^item> is \<open>the expected object\<close>, it transforms the leading \<phi>-type term \<open>x \<Ztypecolon> T\<close> to \<open>y \<Ztypecolon> T\<close> for the given y.
\<^item> as \<open>the expected object \<Ztypecolon> the target \<phi>-type\<close>, as \<open>y \<Ztypecolon> U\<close> is a syntax sugar of
                                   \<^verbatim>\<open>to U\<close> followed by \<^verbatim>\<open>is y\<close>.
\<^item> assert \<open>BI assertion\<close>, asserts the entire of the current state is what. It is pure transformation
                         and never generates code.
\<^item> \<open>x \<Ztypecolon> T\<close>, (directly giving a BI assertion without a leading keyword),
           synthesis \<open>x \<Ztypecolon> T\<close> using whatever terms in the current state.
           It may generate program code.
\<close>


section \<open>Convention\<close>

text \<open>Priority:

\<^item> 59: Fallback of Make Abstraction
\<close>

section \<open>Elements of Actions\<close>

subsubsection \<open>Actions only for implication only\<close>

consts \<A>_transformation :: \<open>action \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close>    (100)
]]

lemma [\<phi>reason 1010]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1100]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_implication by blast

lemma [\<phi>reason 1100]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Transformation_def ToA_Construction_def
  by blast


subsubsection \<open>View Shift\<close>

consts \<A>_view_shift_or_imp :: \<open>action \<Rightarrow> action\<close>

lemma [\<phi>reason 1100]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Transformation_def ToA_Construction_def
  by blast

lemma do_\<A>_view_shift_or_imp_VS:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift by blast

lemma do_\<A>_view_shift_or_imp_VS_degrade:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_implication by blast

declare [[\<phi>reason 1100 do_\<A>_view_shift_or_imp_VS do_\<A>_view_shift_or_imp_VS_degrade
      for \<open>PROP Do_Action (\<A>_view_shift_or_imp ?action)
                (Trueprop (CurrentConstruction ?mode ?s ?H ?X))
                ?Result\<close>]]

hide_fact do_\<A>_view_shift_or_imp_VS do_\<A>_view_shift_or_imp_VS_degrade

subsubsection \<open>Nap, a space for injection\<close>

consts \<A>nap :: \<open>action \<Rightarrow> action\<close>

lemma [\<phi>reason 10]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>nap A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for \<open>\<exists>\<and>\<close>-free MTF\<close>

consts \<A>_simple_MTF :: \<open>action \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close>    (100)
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1010]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y x \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp, blast)

paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<s>\<h>\<i>\<f>\<t>\<s> Y \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: INTERP_SPEC_subj, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<s>\<h>\<i>\<f>\<t>\<s> Y x \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<s>\<h>\<i>\<f>\<t>\<s> ExSet Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: INTERP_SPEC_ex, metis)

paragraph \<open>Finish\<close>

lemma [\<phi>reason 1000]:
  \<open> XXX @action A
\<Longrightarrow> XXX @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for the leading item only\<close>

consts \<A>_leading_item' :: \<open>action \<Rightarrow> action\<close>

abbreviation \<open>\<A>_leading_item A \<equiv> \<A>_simple_MTF (\<A>_leading_item' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close>    (100)
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1050]:
  \<open> ERROR TEXT(\<open>There is no item!\<close>)
\<Longrightarrow> TECHNICAL X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Any \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def ERROR_def by blast

lemma [\<phi>reason 1050]:
  \<open> ERROR TEXT(\<open>There is no item!\<close>)
\<Longrightarrow> Void \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Any \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def ERROR_def by blast


lemma [\<phi>reason 1020]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A
\<Longrightarrow> R * (TECHNICAL X) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * (TECHNICAL X) \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def
  using implies_right_frame .

lemma [\<phi>reason 1010]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using implies_left_frame .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action A
\<Longrightarrow> X \<s>\<u>\<b>\<j> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp


paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> R\<heavy_comma> X \<s>\<h>\<i>\<f>\<t>\<s> R\<heavy_comma> Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using \<phi>view_shift_intro_frame .

lemma [\<phi>reason 1000]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> Q @action A
\<Longrightarrow> X \<s>\<u>\<b>\<j> P \<s>\<h>\<i>\<f>\<t>\<s> Y \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: INTERP_SPEC_subj, blast)


subsubsection \<open>Actions for every \<phi>-type item\<close>

consts \<A>_map_each_item :: \<open>action \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_map_each_item _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_map_each_item _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_map_each_item _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_map_each_item _\<close>    (100)
]]


paragraph \<open>Implication\<close>

lemma [\<phi>reason 1050]:
  \<open> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 @action \<A>_map_each_item A \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1050]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 @action \<A>_map_each_item A \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1050]:
  \<open> \<top> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> @action \<A>_map_each_item A \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1050]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A)
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A\<close>
  unfolding Action_Tag_def Premise_def Transformation_def
  by simp blast

lemma [\<phi>reason 1050]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action \<A>_map_each_item \<A>
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action \<A>_map_each_item \<A>
\<Longrightarrow> A \<and>\<^sub>B\<^sub>I B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<and>\<^sub>B\<^sub>I Y \<w>\<i>\<t>\<h> P \<and> Q @action \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Transformation_def
  by simp blast

lemma [\<phi>reason 1050]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action \<A>_map_each_item \<A>
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action \<A>_map_each_item \<A>
\<Longrightarrow> A + B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X + Y \<w>\<i>\<t>\<h> P \<or> Q @action \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Transformation_def
  by simp

lemma [\<phi>reason 1050]:
  \<open> (\<And>c. X c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y c \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A)
\<Longrightarrow> ExSet X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet Y \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A\<close>
  unfolding Action_Tag_def
  using ExSet_transformation .

lemma [\<phi>reason 1050]:
  \<open> (\<And>c. X c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y c \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A)
\<Longrightarrow> AllSet X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> AllSet Y \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A\<close>
  unfolding Action_Tag_def Transformation_def
  by simp blast

lemma [\<phi>reason 1050]:
  \<open> TECHNICAL X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL X @action \<A>_map_each_item \<A>\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def Technical_def
  by simp

lemma [\<phi>reason 1050]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action \<A>_map_each_item \<A>
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action \<A>_map_each_item \<A>
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action \<A>_map_each_item \<A> \<close>
  unfolding Action_Tag_def Transformation_def
  by simp blast

lemma [\<phi>reason 1050]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A
\<Longrightarrow> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> Q @action \<A>_map_each_item A
\<Longrightarrow> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<and> (C \<longrightarrow> Q) @action \<A>_map_each_item A\<close>
  unfolding REMAINS_def
  by (cases C; simp add: Action_Tag_def implies_bi_frame)

lemma [\<phi>reason 1050]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<w>\<i>\<t>\<h> P @action \<A>_map_each_item \<A>)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B' \<w>\<i>\<t>\<h> Q @action \<A>_map_each_item \<A>)
\<Longrightarrow> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C A' B' \<w>\<i>\<t>\<h> If C P Q @action \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Premise_def
  by (cases C; simp)

lemma [\<phi>reason 1050]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' a \<w>\<i>\<t>\<h> P a @action \<A>_map_each_item \<A>)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B' b \<w>\<i>\<t>\<h> Q b @action \<A>_map_each_item \<A>)
\<Longrightarrow> (case_sum A B x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (case_sum A' B' x) \<w>\<i>\<t>\<h> case_sum P Q x @action \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Premise_def
  by (cases x; simp)

lemma [\<phi>reason 1000]: \<comment> \<open>fallback\<close>
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_map_each_item A\<close>
  unfolding Action_Tag_def .

(*
lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action \<A>_map_each_item A\<close>
  unfolding Action_Tag_def by simp
*)

(* depreciated
subsubsection \<open>Actions of multi-arity\<close>

text \<open>for transformations containing remainder, of form \<open>?R\<heavy_comma> X \<longmapsto> ?R\<heavy_comma> Y\<close>
  so padding Void is required when there is only one item.\<close>

consts \<A>_multi_arity' :: \<open>action \<Rightarrow> action\<close>

abbreviation \<open>multi_arity A \<equiv> \<A>_simple_MTF (\<A>_multi_arity' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close>    (100)
]]

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y1\<heavy_comma> ?Y2 \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Void\<heavy_comma> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y1\<heavy_comma> ?Y2 \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Void\<heavy_comma> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def .
*)

(* Not really useful, I think?
   DO NOT REMOVE, let me think more
subsubsection \<open>Structural\<close>

consts \<A>_structural :: \<open>action \<Rightarrow> action\<close>
consts \<A>_structural_1_2 :: \<open>action \<Rightarrow> action\<close>
consts \<A>_structural_2_1 :: \<open>action \<Rightarrow> action\<close>

text \<open>
\<^descr> \<^const>\<open>\<A>_structural\<close> \<A>_structural homomorphism in shape:
  \<open> X \<longmapsto> Y \<Longrightarrow> C(X) \<longmapsto> C(Y) \<close>
  typically used in containers.

\<^descr> \<^const>\<open>\<A>_structural_1_2\<close> \<A>_structural homomorphism in shape:
  \<open> X \<longmapsto> Y * Z \<Longrightarrow> C(X) \<longmapsto> C(Y) * C(Z) \<close>

\<^descr> \<^const>\<open>\<A>_structural_2_1\<close> \<A>_structural homomorphism in shape:
  \<open> X * Y \<longmapsto> Z \<Longrightarrow> C(X) * C(Y) \<longmapsto> C(Z) \<close>
\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close>     (100)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close>     (100)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close>     (100)
]]

paragraph \<open>Fallbacks\<close>

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>_structural A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>_structural_1_2 A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>_structural_2_1 A\<close>
  unfolding Action_Tag_def .
*)

section \<open>Basic Applications\<close>

subsection \<open>General Syntax\<close>

consts synt_orelse :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'a\<close> (infixr "\<o>\<r>\<e>\<l>\<s>\<e>" 30)

subsection \<open>Is \& Assert\<close>

lemma is_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> y
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<close>
  unfolding Premise_def Object_Equiv_def
  by blast

lemma assert_\<phi>app:
  \<open>\<p>\<a>\<r>\<a>\<m> Y \<Longrightarrow> \<^bold>d\<^bold>o X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Any @action NToA \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close>
  unfolding Action_Tag_def Do_def
  using transformation_weaken by blast




subsection \<open>Simplification\<close>

consts \<A>simp' :: \<open> bool \<Rightarrow> action \<close> (*bool: if the simplification must change something.
                                  it is used prevent infinite loop of unchanging simplifications*)
abbreviation \<open>\<A>simp \<equiv> \<A>simp' True\<close>

text \<open>Potentially weakening transformations designed for simplifying state sequents of the CoP.

  \<^prop>\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y @action \<A>simp\<close>

  Doing this simplification in the framework of To-Transformation benefits it by reusing the
  To-Transformation support in transformation functors, which brings the simplification into the elements.

  The simplification is very heavy.
  For the sake of performance, it is indolent and is applied only when the state sequent
  needs the simplification. There is a mechanism to detect such need. The default strategy is,
  we collect all the registered simplification rules, get the pattern of the source type of the
  transformations, and if the types of a state sequent match any of a pattern, the simplification
  is required and activated.

  This default strategy is not perfect, so we provide hooks by which users can provide ML checkers.
  The checker can bind on either the whole types or subterms of specific constant heads.
  The checker only checks the type part.

  Note \<^prop>\<open>A @action \<A>simp\<close> requires the process at least make one meaningful simplification
  step, while \<^prop>\<open>A @action \<A>simp' False\<close> allows no-change simplification.
  Semantically, a meaningful step is the one that at least simplifies something.
  User can indicate to the system that his reasoning rule \<^prop>\<open>A @action \<A>simp' flag\<close> is
  meaningful by set \<open>flag \<equiv> True\<close>, or \<open>False\<close> otherwise.
\<close>

declare [[ \<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. _) \<w>\<i>\<t>\<h> ?P @action \<A>simp' ?flag\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>simp' ?flag\<close> (100)
  and \<open>?X @action \<A>simp' ?flag\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Bad form: \<close> (?X @action \<A>simp' ?flag) \<newline>
                  \<open>Expect: \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> ?Y \<s>\<u>\<b>\<j> y. ?r y) @action \<A>simp\<close>\<close>)\<close> (1)
]]

consts \<A>chk_need_simp :: \<open>bool \<Rightarrow> action\<close>
       \<A>_apply_simplication :: action

lemma [\<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_apply_simplication\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<w>\<i>\<t>\<h> Any @action \<A>_map_each_item (\<A>chk_need_simp False)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> Y : Ya
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>_apply_simplication \<close>
  unfolding Action_Tag_def Transformation_def Simplify_def
  by simp


lemma \<A>simp_stage_1:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Any @action \<A>_map_each_item (\<A>chk_need_simp False)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<close>
  unfolding Action_Tag_def
  by (simp add: transformation_weaken)

lemma \<A>simp_chk_no_need:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action \<A>chk_need_simp Any\<close>
  unfolding Action_Tag_def
  by simp

lemma \<A>simp_chk_no_need':
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x @action \<A>chk_need_simp Any\<close>
  unfolding Action_Tag_def
  by simp

lemma \<A>simp_chk_go:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>simp' M
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>chk_need_simp M\<close>
  unfolding Action_Tag_def .

lemma \<A>simp_trans:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y @action \<A>simp' Any
\<Longrightarrow> (\<And>y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> r y \<Longrightarrow> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w y z @action \<A>chk_need_simp M)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. (\<exists>y. r y \<and> w y z) @action \<A>simp' Any2 \<close>
  unfolding Action_Tag_def Transformation_def
  by simp blast

lemma \<A>simp_trans':
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. y = y' @action \<A>simp' Any
\<Longrightarrow> y' \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w z @action \<A>chk_need_simp M
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w z @action \<A>simp' Any2 \<close>
  unfolding Action_Tag_def Transformation_def
  by simp

lemma \<A>simp_trans'P:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. y = y' \<and> P y @action \<A>simp' Any
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P y' \<Longrightarrow> y' \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w z @action \<A>chk_need_simp M)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Z \<s>\<u>\<b>\<j> z. w z \<and> P y' @action \<A>simp' Any2 \<close>
  unfolding Action_Tag_def Transformation_def
  by simp

ML_file \<open>library/tools/CoP_simp.ML\<close>
               
\<phi>reasoner_ML \<A>chk_need_simp 1000 (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>chk_need_simp _\<close>) = \<open>
fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (X, Y, _) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
   in if Phi_CoP_Simp.is_simp_needed (Context.Proof ctxt) X
   then SOME ((ctxt, @{thm' \<A>simp_chk_go} RS' (ctxt, sequent)), Seq.empty)
   else let val rule = case Y of Const(\<^const_name>\<open>ExSet\<close>, _) $ Abs (_, _,
                                    Const(\<^const_name>\<open>Subjection\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ Bound 0 $ _) $ _)
                                   => @{thm' \<A>simp_chk_no_need'}
                               | _ => @{thm' \<A>simp_chk_no_need}
    in SOME ((ctxt, rule RS' (ctxt, sequent)), Seq.empty)
   end
  end)
\<close>



lemma [\<phi>reason no explorative backtrack !2]:
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x @action \<A>simp' False\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason no explorative backtrack !1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>simp' False\<close>]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action \<A>simp' False\<close>
  unfolding Action_Tag_def by simp

print_\<phi>reasoners \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action \<A>simp' False\<close> 
print_\<phi>reasoners \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action \<A>simp' _\<close> ? ?

\<phi>processor \<phi>transformation_based_simplifier 101 (\<open>CurrentConstruction ?mode ?blk ?H ?T\<close> | \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?x) \<i>\<s> ?S\<close>)
  \<open>fn (ctxt,sequent) => Scan.succeed (fn _ =>
    case Phi_Working_Mode.mode ctxt
      of SOME mode => raise Bypass (SOME (ctxt, Phi_CoP_Simp.invoke_when_needed (ctxt,mode) sequent))
       | NONE => raise Bypass NONE)\<close>

setup \<open>Config.put_global Phi_CoP_Simp.enable_rule_pass true\<close>
    (*Enable it until the internal rules are registered as it will modify the rules under the table.
      It modifies any rule in form \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close> into \<open>Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?? \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ??\<close>*)

hide_fact \<A>simp_stage_1 \<A>simp_chk_no_need \<A>simp_chk_no_need'
          \<A>simp_chk_go \<A>simp_trans \<A>simp_trans' \<A>simp_trans'P


subsubsection \<open>Simplification Protect\<close>

definition [simplification_protect]:
  \<open>\<phi>TBS_Simp_Protect X U r flag \<equiv> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y @action \<A>simp' flag\<close>

lemma [cong]:
  \<open> X \<equiv> X'
\<Longrightarrow> U \<equiv> U'
\<Longrightarrow> r \<equiv> r'
\<Longrightarrow> \<phi>TBS_Simp_Protect X U r flag \<equiv> \<phi>TBS_Simp_Protect X' U' r' flag \<close>
  by simp



subsection \<open>To\<close>

consts to :: \<open>('a,'b) \<phi> \<Rightarrow> action\<close>
       \<A>pattern :: \<open>('a,'b) \<phi> \<Rightarrow> ('c,'d) \<phi> \<Rightarrow> ('a,'b) \<phi>\<close> ("\<p>\<a>\<t>\<t>\<e>\<r>\<n> _ \<Rightarrow> _" [32,32] 31)
       \<A>traverse :: \<open>('a,'b) \<phi> \<Rightarrow> ('c,'d) \<phi>\<close> ("\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> _" [27] 26)
          \<comment> \<open>enter to elements recursively\<close>


(* abbreviation \<open>\<A>_transform_to T \<equiv> \<A>_leading_item (\<A>nap (to T)) \<close> *)

ML \<open>fun mk_pattern_for_to_transformation ctxt term =
  let val idx = Term.maxidx_of_term term + 1
      fun chk_P (Const(\<^const_name>\<open>True\<close>, _)) = Var(("P",idx), HOLogic.boolT)
        | chk_P X = error ("To-Transformation should not contain a \<w>\<i>\<t>\<h> clause, but given\n" ^
                           Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt X)
      val i = Unsynchronized.ref idx
      fun relax (Const(N, _)) = (i := !i + 1; Const(N, TVar(("t",!i), [])))
        | relax (A $ B) = relax A $ relax B
        | relax (Abs(N,_,X)) = (i := !i + 1; Abs(N, TVar(("t",!i),[]), relax X))
        | relax (Free X) = Free X
        | relax (Var _) = (i := !i + 1; Var(("v",!i), TVar(("t",!i),[])))
        | relax (Bound i) = Bound i
   in case term
        of Trueprop $ (Action_Tag $ (Trans $ X $ _ $ P) $ To_Tag) =>
           SOME [Trueprop $ (Action_Tag
              $ (relax Trans $ X $ Var(("Y",idx), TVar(("model",idx),[])) $ chk_P P)
              $ relax To_Tag)]
  end\<close>

declare [[

  \<phi>reason_default_pattern_ML \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. ?R y) \<w>\<i>\<t>\<h> ?P @action to ?T\<close> \<Rightarrow>
    \<open>mk_pattern_for_to_transformation\<close> (100),

  \<phi>reason_default_pattern
    \<open>?X @action to ?A\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Malformed To-Transformation: \<close> (?X @action to ?A) \<newline>
                                      \<open>Expect: \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> ?Y \<s>\<u>\<b>\<j> y. ?r y) @action to _\<close>\<close>)\<close> (1)
(*depreciate
and \<open>x \<Ztypecolon> ?T \<s>\<u>\<b>\<j> x. ?rel x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. _ @action \<A>\<T>split_step\<close> \<Rightarrow>
    \<open>x \<Ztypecolon> ?T \<s>\<u>\<b>\<j> x. ?rel x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. _ \<w>\<i>\<t>\<h> _ @action \<A>\<T>split_step\<close> (100)
and \<open>?X @action \<A>\<T>split_step\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Bad form: \<close> (?X @action \<A>\<T>split_step))\<close> (1)*)
]]

(*
definition \<A>ction_parser :: \<open>'a \<Rightarrow> action \<Rightarrow> bool\<close>
  where \<open>\<A>ction_parser _ _ \<equiv> True\<close>

declare [[\<phi>reason_default_pattern \<open>\<A>ction_parser ?X _\<close> \<Rightarrow> \<open>\<A>ction_parser ?X _\<close> (100) ]]

lemma [\<phi>reason 1000]:
  \<open> \<A>ction_parser \<A> \<A> \<close>
  unfolding \<A>ction_parser_def ..

lemma [\<phi>reason 1000]:
  \<open> \<A>ction_parser T (to T) \<close>
  unfolding \<A>ction_parser_def ..

lemma [\<phi>reason default 0]:
  \<open> FAIL TEXT(\<open>Do not know how to transform to\<close> A)
\<Longrightarrow> \<A>ction_parser A B \<close>
  unfolding \<A>ction_parser_def ..*)

(*depreciated
lemma destruct_\<phi>app:
  \<open> \<^bold>d\<^bold>o X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transform_to RAW
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Do_def Action_Tag_def .*)

subsubsection \<open>Simplification Protect\<close>

definition [simplification_protect]:
  \<open>\<phi>To_Transformation_Simp_Protect X U r A \<equiv> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y @action to A\<close>

lemma [cong]:
  \<open> X \<equiv> X'
\<Longrightarrow> U \<equiv> U'
\<Longrightarrow> r \<equiv> r'
\<Longrightarrow> \<phi>To_Transformation_Simp_Protect X U r A \<equiv> \<phi>To_Transformation_Simp_Protect X' U' r' A \<close>
  by simp


subsubsection \<open>Termination\<close>

lemma ToA_trivial:
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<s>\<u>\<b>\<j> x'. x' = x @action to any\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason no explorative backtrack 0 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to _\<close>]:
  \<open> FAIL TEXT(\<open>Fail to transform\<close> X \<open>to\<close> T)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action to T\<close>
  unfolding Action_Tag_def FAIL_def by blast

lemma [\<phi>reason default 1]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action NToA
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. y = y' \<and> P @action to U\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 5000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<s>\<u>\<b>\<j> x'. x' = x @action to T\<close>
  unfolding Action_Tag_def by simp


subsubsection \<open>Special Forms\<close>

lemma [\<phi>reason 1000]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Ua \<s>\<u>\<b>\<j> y. ra y @action to T)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Ub \<s>\<u>\<b>\<j> y. rb y @action to T)
\<Longrightarrow> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> If C Ua Ub \<s>\<u>\<b>\<j> y. (if C then ra y else rb y) @action to T\<close>
  unfolding Action_Tag_def Premise_def
  by (cases C; simp)

lemma [\<phi>reason 1000]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> x \<Ztypecolon> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Ua \<s>\<u>\<b>\<j> y. ra y @action to T)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> x \<Ztypecolon> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Ub \<s>\<u>\<b>\<j> y. rb y @action to T)
\<Longrightarrow> x \<Ztypecolon> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> If C Ua Ub \<s>\<u>\<b>\<j> y. (if C then ra y else rb y) @action to T\<close>
  unfolding Action_Tag_def Premise_def
  by (cases C; simp)


lemma [\<phi>reason 1000 for \<open>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to _\<close>]:
  \<open> () \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to T
\<Longrightarrow> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to T \<close>
  by simp


subsubsection \<open>No Change\<close>

consts \<A>NO_CHANGE :: \<open>('a,'b) \<phi>\<close> ("\<n>\<o>-\<c>\<h>\<a>\<n>\<g>\<e>")

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<s>\<u>\<b>\<j> x'. x' = x @action to \<n>\<o>-\<c>\<h>\<a>\<n>\<g>\<e> \<close>
  unfolding Action_Tag_def by simp


subsubsection \<open>Pattern\<close>

lemma \<A>_strip_traverse:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> A) \<close>
  unfolding Action_Tag_def .

lemma \<A>_pattern_meet:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to A'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to (\<p>\<a>\<t>\<t>\<e>\<r>\<n> pat \<Rightarrow> A) \<close>
  unfolding Action_Tag_def .

lemma \<A>_pattern_not_meet:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to \<n>\<o>-\<c>\<h>\<a>\<n>\<g>\<e>
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to \<A> \<close>
  unfolding Action_Tag_def .

lemma \<A>_pattern_meet_this:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to A'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to (\<p>\<a>\<t>\<t>\<e>\<r>\<n> pat \<Rightarrow> A \<o>\<r>\<e>\<l>\<s>\<e> others) \<close>
  unfolding Action_Tag_def .

lemma \<A>_pattern_meet_that:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to that
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action to (this \<o>\<r>\<e>\<l>\<s>\<e> that) \<close>
  unfolding Action_Tag_def .


\<phi>reasoner_ML \<A>pattern 10000
    ( \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (\<p>\<a>\<t>\<t>\<e>\<r>\<n> _ \<Rightarrow> _)\<close>
    | \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (\<p>\<a>\<t>\<t>\<e>\<r>\<n> _ \<Rightarrow> _ \<o>\<r>\<e>\<l>\<s>\<e> _)\<close>
    | \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> _ \<Rightarrow> _)\<close>
    | \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> _ \<Rightarrow> _ \<o>\<r>\<e>\<l>\<s>\<e> _)\<close> ) =
\<open>fn (_, (ctxt, sequent)) => Seq.make (fn () =>
  let fun parse_patterns (Const(\<^const_name>\<open>synt_orelse\<close>, _) $ X $ Y)
            = parse_patterns X @ parse_patterns Y
        | parse_patterns (Const(\<^const_name>\<open>\<A>pattern\<close>, _) $ Pat $ Y) = [(Pat, Y)]
        | parse_patterns _ = []
      val _ (*Trueprop*) $ (_ (*Action_Tag*)
            $ (_ (*Transformation*) $ (_ (*\<phi>Type*) $ _ $ T) $ _ $ _)
            $ (_ (*to*) $ A)) = Thm.major_prem_of sequent
      val (is_traverse, A') = case A of Const(\<^const_name>\<open>\<A>traverse\<close>, _) $ A' => (true, A')
                                      | A' => (false, A')
      val pats = parse_patterns A'
      val len = length pats
      val thy = Proof_Context.theory_of ctxt

      fun meet_pattern A (i,len) th =
        if i = 0
        then let val rule = (if i = len - 1 then @{thm' \<A>_pattern_meet} else @{thm' \<A>_pattern_meet_this})
                         |> Drule.infer_instantiate ctxt [(("A'",0), A)]
              in rule RS th
             end
        else meet_pattern A (i-1,len-1) (@{thm' \<A>_pattern_meet_that} RS th)
      fun meet_pattern' A i th =
        meet_pattern A (i,len) (if is_traverse then @{thm' \<A>_strip_traverse} RS th else th)

      fun bad_pattern pat = error ("Bad Pattern: " ^ Syntax.string_of_term ctxt pat)
      fun cannot_shortcut (Abs (_, _, X)) = cannot_shortcut X
        | cannot_shortcut tm =
           (case Term.strip_comb tm of (Const (h, _), args) => (
                    exists (fn (pat, _) =>
                      case Term.head_of pat
                        of Const(N, _) => if N = h then Pattern.matches thy (pat, tm) else false
                         | Free _ => false
                         | _ => bad_pattern pat) pats)
                    orelse exists cannot_shortcut args
               | (Free (N, _), args) => (
                    exists (fn (pat, _) =>
                      case Term.head_of pat
                        of Const(N, _) => false
                         | Free(N', _) => if N = N' then Pattern.matches thy (pat, tm) else false
                         | _ => bad_pattern pat) pats)
               | (_, args) => exists cannot_shortcut args)

   in case get_index (fn (pat,residue) =>
        let val subst = Pattern.match thy (pat, T) (Vartab.empty, Vartab.empty)
         in SOME (Envir.subst_term subst residue)
        end handle Pattern.MATCH => NONE) pats
   of NONE => if cannot_shortcut T then NONE
              else (SOME ((ctxt, @{thm' ToA_trivial} RS sequent), Seq.empty)
                 handle THM _ =>
                    SOME ((ctxt, @{thm' \<A>_pattern_not_meet} RS sequent), Seq.empty))
    | SOME (i, A) => SOME ((ctxt, meet_pattern' (Thm.cterm_of ctxt A) i sequent), Seq.empty)
  end
)\<close>

(* TODO:
hide_fact \<A>_strip_traverse \<A>_pattern_meet \<A>_pattern_meet_this \<A>_pattern_meet_that *)



subsubsection \<open>Product\<close>

(* \<open>to\<close> is for single \<phi>-type item!

lemma prod_transform_to1:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action to T
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action to U
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action to (T \<^emph> U)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_frame implies_right_frame transformation_trans)

lemma prod_transform_to2:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action to U
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action to T
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action to (T \<^emph> U)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_frame implies_right_frame transformation_trans)

declare [[\<phi>reason 1200 prod_transform_to1 prod_transform_to2
      for \<open>?A * ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (?T \<^emph> ?U)\<close>]]

hide_fact prod_transform_to1 prod_transform_to2

lemma [\<phi>reason 1100]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action to T
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action to T
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action to T\<close>
  unfolding Action_Tag_def
  by (meson implies_left_frame implies_right_frame transformation_trans)
*)

text \<open>By default, the To-Transformation does not recognize \<open>to (A \<^emph> B \<^emph> C)\<close> as a request to
permute for instance \<open>C \<^emph> B \<^emph> A\<close> to it. Instead, it recognizes the request as transform
\<open>C\<close> to \<open>A\<close>, \<open>B\<close> to \<open>B\<close>, and \<open>C\<close> to \<open>A\<close> successively. If you want to make the \<open>A \<^emph> B \<^emph> C\<close> as a whole
so that the system can do the permutation, write it as \<open>to (id (A \<^emph> B \<^emph> C))\<close>.\<close>

lemma Prod_ToTransform[\<phi>reason 1200]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' @action to A
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' @action to B
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') @action to (A \<^emph> B)\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)

lemma Prod_ToTransform_rev:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' @action to B
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' @action to A
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') @action to (A \<^emph> B)\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)

lemma [\<phi>reason 1210]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Target)
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Target)
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Target)\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)

(* Is this still required?

lemma [\<phi>reason 1210 for \<open>_ \<Ztypecolon> _ \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to ( _ \<f>\<o>\<r> _ \<^emph> _) \<close>]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' \<w>\<i>\<t>\<h> P @action to (T' \<f>\<o>\<r> T)
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' \<w>\<i>\<t>\<h> Q @action to (U' \<f>\<o>\<r> U)
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') \<w>\<i>\<t>\<h> P \<and> Q
    @action to (T' \<^emph> U' \<f>\<o>\<r> T \<^emph> U)\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)
*)

subsubsection \<open>To Itself\<close>

declare [[\<phi>reason_default_pattern
    \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. _) \<w>\<i>\<t>\<h> _ @action to Itself\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to Itself\<close> (200)
      \<comment> \<open>Here we varify the type of the \<open>Itself\<close> \<close>
]]

lemma [\<phi>reason default 2]:
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v \<Ztypecolon> (Itself :: ('v,'v) \<phi>) \<s>\<u>\<b>\<j> v. v \<Turnstile> (x \<Ztypecolon> T) @action to (Itself :: ('v,'v) \<phi>)\<close>
  unfolding Action_Tag_def Transformation_def
  by simp

lemma [\<phi>reason 1200]:
  \<open>x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v \<Ztypecolon> (Itself :: ('v,'v) \<phi>) \<s>\<u>\<b>\<j> v. v = x @action to (Itself :: ('v,'v) \<phi>)\<close>
  unfolding Action_Tag_def Transformation_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> x. ra x @action to (Itself :: ('c,'c) \<phi>)
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> x. rb x @action to (Itself :: ('c,'c) \<phi>)
\<Longrightarrow> x \<Ztypecolon> T \<^emph> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (Itself :: ('c::sep_magma,'c) \<phi>) \<s>\<u>\<b>\<j> x.
                    (\<exists>b a. x = b * a \<and> b ## a \<and> rb b \<and> ra a) @action to (Itself :: ('c,'c) \<phi>) \<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)

paragraph \<open>Special Forms\<close>

lemma [\<phi>reason 1000]:
  \<open> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y::'b::one) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. y = 1 @action to (Itself :: ('b, 'b) \<phi>) \<close>
  unfolding Action_Tag_def Transformation_def Identity_Element\<^sub>E_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> x \<Ztypecolon> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'a) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ra y @action to (Itself :: ('a,'a) \<phi>))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> x \<Ztypecolon> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rb y @action to (Itself :: ('a,'a) \<phi>))
\<Longrightarrow> x \<Ztypecolon> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (if C then ra y else rb y) @action to (Itself :: ('a,'a) \<phi>)\<close>
  unfolding Action_Tag_def Transformation_def Premise_def
  by simp

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v \<Ztypecolon> Itself \<s>\<u>\<b>\<j> v. True @action to Itself\<close>
  unfolding Action_Tag_def Transformation_def
  by simp


subsubsection \<open>The \<open>to\<close> application\<close>

lemma to_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> T
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<w>\<i>\<t>\<h> P @action to T
\<Longrightarrow> Ya \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>_apply_simplication
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Do_def Action_Tag_def Transformation_def
  by simp


subsection \<open>As\<close>

lemma as_\<phi>app:
  " \<p>\<a>\<r>\<a>\<m> (y \<Ztypecolon> U)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<s>\<u>\<b>\<j> y'. P y' @action to U
\<Longrightarrow> Object_Equiv U eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>y'. P y' \<longrightarrow> eq y' y)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U "
  unfolding Premise_def Action_Tag_def Object_Equiv_def Transformation_def
  by simp blast



subsection \<open>Case Analysis\<close>

consts \<A>case :: action

subsubsection \<open>Framework\<close>

declare [[
  \<phi>reason_default_pattern
      \<open> ?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action \<A>case \<close> \<Rightarrow> \<open> ?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action \<A>case \<close>   (100)
  and \<open> ?X \<s>\<h>\<i>\<f>\<t>\<s> _ @action \<A>case \<close> \<Rightarrow> \<open> ?X \<s>\<h>\<i>\<f>\<t>\<s> _ @action \<A>case \<close>   (100)
  and \<open> ?X @action \<A>case \<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Malformed \<A>case rule\<close> (?X @action \<A>case))\<close> (0)
]]

lemma "_cases_app_rule_":
  \<open>Call_Action (\<A>_view_shift_or_imp \<A>case)\<close> ..

ML_file \<open>library/tools/induct_analysis.ML\<close>

hide_fact "_cases_app_rule_"

\<phi>processor case_analysis 5000 (\<open>_\<close>) \<open> IDECP_Induct_Analysis.case_analysis_processor \<close>


subsubsection \<open>Case Rules\<close>

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<s>\<h>\<i>\<f>\<t>\<s> Y
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Y
\<Longrightarrow> B + A \<s>\<h>\<i>\<f>\<t>\<s> Y @action \<A>case\<close>
  unfolding Argument_def Action_Tag_def
  using \<phi>CASE_VS by fastforce

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y
\<Longrightarrow> B + A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>case\<close>
  unfolding Argument_def Action_Tag_def
  using \<phi>CASE_IMP by fastforce

lemma [\<phi>reason 1000]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<s>\<h>\<i>\<f>\<t>\<s> Ya)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> \<not> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Yb)
\<Longrightarrow> If P Ya Yb \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action invoke_branch_convergence
\<Longrightarrow> If P A B \<s>\<h>\<i>\<f>\<t>\<s> Y @action \<A>case\<close>
  unfolding Argument_def Action_Tag_def Premise_def
  apply (cases P; simp)
  using \<phi>view_trans view_shift_by_implication apply fastforce
  using View_Shift_def view_shift_by_implication by force

lemma [\<phi>reason 1000]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> \<not> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb)
\<Longrightarrow> \<^bold>d\<^bold>o If P Ya Yb \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action invoke_branch_convergence
\<Longrightarrow> If P A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>case\<close>
  unfolding Argument_def Action_Tag_def Premise_def
  apply (cases P; simp)
  using transformation_trans apply fastforce
  using transformation_trans by fastforce

lemma [\<phi>reason default 0]:
  \<open> FAIL TEXT(\<open>Don't know how to case-split\<close> X)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>case\<close>
  unfolding FAIL_def
  by blast


(*lemma [\<phi>reason 1000]:
  \<open> \<p>\<a>\<r>\<a>\<m> P
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PA)
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PB
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_VS . *)


subsection \<open>Open \& Make Abstraction\<close>


subsubsection \<open>Open Abstraction\<close>

consts RAW :: \<open>('a,'b) \<phi>\<close>

lemma open_abstraction_\<phi>app:
  \<open> Friendly_Help TEXT(\<open>Just tell me which \<phi>-type you want to open.\<close> \<newline>
      \<open>Input a lambda abstraction e.g. \<open>\<lambda>x. List (Box x)\<close> as a pattern where the lambda variable is the \<phi>-type you want to destruct.\<close>
      \<open>I will match\<close> T \<open>with the pattern.\<close> \<newline>
      \<open>You can also use an underscore to denote the target \<phi>-type in this pattern so you don't need to write a lambda abstraction, e.g. \<open>List (Box _)\<close>\<close>)
\<Longrightarrow> \<p>\<a>\<r>\<a>\<m> target
\<Longrightarrow> \<^bold>d\<^bold>o x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transform_to (target RAW)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Do_def Action_Tag_def .

ML \<open>
structure Gen_Open_Abstraction_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>gen_open_abstraction_simps\<close>
  val comment = "Simplification rules used when generating open-abstraction rules"
  val attribute = NONE
)
\<close>

setup \<open>Context.theory_map (Gen_Open_Abstraction_SS.map (fn ctxt =>
          ctxt addsimprocs [\<^simproc>\<open>defined_Ex\<close>, \<^simproc>\<open>defined_All\<close>, \<^simproc>\<open>NO_MATCH\<close>]
               addsimps @{thms' HOL.simp_thms}))\<close>

lemma \<comment>\<open>fallback\<close>
  [\<phi>reason default 2 for \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to RAW\<close>]:
  \<open> FAIL TEXT(\<open>Fail to destruct \<phi>-type\<close> T)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action to RAW \<close>
  unfolding FAIL_def
  by blast

subsubsection \<open>Make Abstraction\<close>

definition MAKE :: \<open>('a,'b) \<phi> \<Rightarrow> ('a,'b) \<phi>\<close> where \<open>MAKE X \<equiv> X\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason !59]:
  \<open> FAIL TEXT(\<open>Don't know how to make the abstraction\<close> Y) 
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE U \<w>\<i>\<t>\<h> P\<close>
  unfolding FAIL_def
  by blast

lemma [\<phi>reason !59]: \<comment> \<open>Exactly higher than the entry point of Structural Extract\<close>
  \<open> FAIL TEXT(\<open>Don't know how to make the abstraction\<close> Y) 
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding FAIL_def
  by blast

lemma \<comment>\<open>fallback\<close>
  [\<phi>reason default 2 for \<open> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> MAKE _ \<w>\<i>\<t>\<h> _ \<close>]:
  \<open> FAIL TEXT(\<open>Fail to construct \<phi>-type\<close> U)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE U \<w>\<i>\<t>\<h> P \<close>
  unfolding FAIL_def
  by blast

lemma \<comment>\<open>fallback\<close>
  [\<phi>reason default 3 for \<open> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> MAKE _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _ \<close>]:
  \<open> FAIL TEXT(\<open>Fail to construct \<phi>-type\<close> U)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding FAIL_def
  by blast

setup \<open>let
  fun pass_check _ data = if #2 (#2 data) <= 59
                          then error "The priority of a MAKE rule must be greater than 59!"
                          else data
in Context.theory_map (
      Phi_Reasoner.add_pass (\<^const_name>\<open>MAKE\<close>, \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> MAKE _ \<w>\<i>\<t>\<h> _\<close>, pass_check)
   #> Phi_Reasoner.add_pass (\<^const_name>\<open>MAKE\<close> ^ "'R", \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> MAKE _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>, pass_check))
end\<close>


(*
subsection \<open>Construct \& Destruct \<open>\<phi>\<close>-Type by Definition\<close>

consts \<A>_construct\<phi> :: \<open>'a BI \<Rightarrow> action\<close>
       (*\<A>_destruct\<phi>  :: \<open>('a,'b) \<phi> \<Rightarrow> action\<close>*)

declare [[ \<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi> ?S\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi> ?S\<close>    (100)
  (*and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_destruct\<phi> ?T\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_destruct\<phi> ?T\<close>    (100)*)
]]

(*
lemma destruct\<phi>_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> T'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> D \<w>\<i>\<t>\<h> P @action \<A>_destruct\<phi> T'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> D \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def .*)

consts \<A>_construct\<phi>_NToA :: \<open>'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> action\<close>

lemma [\<phi>reason 1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi>_NToA _ _\<close>]:
  \<open> ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_NToA x T\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1100 for \<open>?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi>_NToA _ _\<close>]:
  \<open> ((X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi> (x \<Ztypecolon> T)
&&&   S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action NToA))
||| ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_NToA x T\<close>
  unfolding Action_Tag_def Do_def atomize_conj atomize_Branch
  using transformation_trans by fastforce

lemma [\<phi>reason 1110 for \<open>(?S::'a::sep_magma BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi>_NToA _ _\<close>]:
  \<open> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi> (x \<Ztypecolon> T)
&&&  S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if single then X else X \<r>\<e>\<m>\<a>\<i>\<n>\<s> S') \<w>\<i>\<t>\<h> P @action NToA)
||| ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if single then x \<Ztypecolon> T else x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> S') \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_NToA x T\<close>
  for S :: \<open>'a::sep_magma BI\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def Do_def atomize_conj atomize_Branch
  apply (cases single; simp)
  using transformation_trans apply fastforce
  using implies_left_frame transformation_trans by fastforce

lemma construct\<phi>_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> (x \<Ztypecolon> T)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_NToA x T
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def Do_def .

consts mode_\<phi>defs :: \<open>action\<close>

abbreviation Unfold_\<phi>Defs :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] _ : _" [1000,10] 9)
  where "Unfold_\<phi>Defs \<equiv> Simplify mode_\<phi>defs"

lemma [\<phi>reason 10 for \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_destruct\<phi> _\<close>]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] D: T x
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> D @action \<A>_destruct\<phi> T\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by simp

lemma [\<phi>reason 10]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] X: T x
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T @action \<A>_construct\<phi> (x \<Ztypecolon> T)\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by simp


ML \<open>
structure PhiDef_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>\<phi>defs\<close>
  val comment = "Rules to expand definitions of \<phi>-Type"
)\<close>

\<phi>reasoner_ML Unfold_\<phi>Defs 1000 (\<open>Unfold_\<phi>Defs ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) PhiDef_SS.get')\<close>

declare prod.case[\<phi>defs]
*)


subsection \<open>Split\<close>

consts \<A>split :: \<open>('a,'b) \<phi>\<close> ("\<s>\<p>\<l>\<i>\<t>")
       (*TODO: remove me? \<A>\<T>split_step :: \<open>action\<close> *)

text \<open>Syntax:

\<^item> \<^term>\<open>to (List (\<s>\<p>\<l>\<i>\<t> \<^emph> other))\<close> splits for instance \<^term>\<open>List ((A \<^emph> B) \<^emph> other)\<close> into
  \<^term>\<open>List (A \<^emph> other)\<close> and \<^term>\<open>List (B \<^emph> other)\<close>, leaving the \<^term>\<open>other\<close> unchanged.

\<^item> \<^term>\<open>to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> pat \<Rightarrow> \<s>\<p>\<l>\<i>\<t>)\<close> splits any sub-\<phi>type matching the pattern

\<close>

definition \<phi>Auto_Prod (infixr "\<^emph>\<^sub>\<A>" 70)
    where [assertion_simps]: "\<phi>Auto_Prod \<equiv> \<phi>Prod"
  \<comment> \<open>The production operator that will expand by the system automatically\<close>


subsubsection \<open>Reasoning\<close>

lemma [\<phi>reason 1210 for \<open>_ \<Ztypecolon> _ \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to \<s>\<p>\<l>\<i>\<t>\<close>]:
  \<open> x \<Ztypecolon> T \<^emph> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<^emph>\<^sub>\<A> U \<s>\<u>\<b>\<j> x'. x' = x @action to \<s>\<p>\<l>\<i>\<t> \<close>
  unfolding Action_Tag_def Transformation_def \<phi>Auto_Prod_def
  by simp

lemma [\<phi>reason !10]:
  \<open> x \<Ztypecolon> T \<^emph>\<^sub>\<A> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<^emph> U \<s>\<u>\<b>\<j> x'. x' = x @action \<A>simp \<close>
  unfolding Action_Tag_def \<phi>Auto_Prod_def Transformation_def
  by simp

subsubsection \<open>Simplification\<close>

lemma [\<phi>reason 1000]:
  \<open> NO_MATCH (Ua \<^emph>\<^sub>\<A> Ub) U
\<Longrightarrow> x \<Ztypecolon> (Ta \<^emph>\<^sub>\<A> Tb) \<^emph> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Ta \<^emph> U) \<^emph>\<^sub>\<A> Tb \<s>\<u>\<b>\<j> y. y = ((fst (fst x), snd x), snd (fst x)) @action \<A>simp \<close>
  for U :: \<open>('c::sep_ab_semigroup,'a) \<phi>\<close>
  unfolding \<phi>Auto_Prod_def Action_Tag_def Transformation_def
  by (cases x; clarsimp;
      metis sep_disj_commuteI sep_disj_multD1 sep_disj_multI2 sep_mult_assoc sep_mult_commute) 

lemma [\<phi>reason 1000]:
  \<open> NO_MATCH (Ta \<^emph>\<^sub>\<A> Tb) T
\<Longrightarrow> x \<Ztypecolon> T \<^emph> (Ua \<^emph>\<^sub>\<A> Ub) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (T \<^emph> Ua) \<^emph>\<^sub>\<A> Ub \<s>\<u>\<b>\<j> y. y = ((fst x, fst (snd x)), snd (snd x)) @action \<A>simp \<close>
  for T :: \<open>('c::sep_semigroup,'a) \<phi>\<close>
  unfolding \<phi>Auto_Prod_def Action_Tag_def Transformation_def
  by (cases x; clarsimp; insert sep_disj_multD2 sep_disj_multI2 sep_mult_assoc; blast)

lemma [\<phi>reason 1020]:
  \<open> x \<Ztypecolon> (Ta \<^emph>\<^sub>\<A> Tb) \<^emph> (Ua \<^emph>\<^sub>\<A> Ub) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Ta \<^emph> Ua) \<^emph>\<^sub>\<A> (Tb \<^emph> Ub) \<s>\<u>\<b>\<j> y.
              y = ((fst (fst x), fst (snd x)), (snd (fst x), snd (snd x))) @action \<A>simp \<close>
  for Ta :: \<open>('c::sep_ab_semigroup,'a) \<phi>\<close>
  unfolding \<phi>Auto_Prod_def Action_Tag_def Transformation_def
  by (cases x; clarsimp; smt (verit, ccfv_threshold) sep_disj_commuteI sep_disj_multD1
                             sep_disj_multI1 sep_mult_assoc' sep_mult_commute)



subsection \<open>Duplicate \& Shrink\<close>

consts action_dup    :: \<open>action\<close>
       action_shrink :: \<open>action\<close>
       action_drop   :: \<open>action\<close>

lemma dup_\<phi>app:
  \<open>Call_Action (\<A>_transformation (\<A>_leading_item (\<A>_structural_1_2 action_dup)))\<close> ..

lemma shrink_\<phi>app:
  \<open>Call_Action (\<A>_transformation (multi_arity (\<A>_structural_2_1 action_shrink)))\<close> ..

lemma drop_\<phi>app:
  \<open>Call_Action (\<A>_view_shift_or_imp (multi_arity action_drop))\<close> ..

(*subsection \<open>Simplification as an Action\<close>

consts action_simplify :: \<open>action\<close>

lemma simplify_\<phi>app:
  \<open>PROP Call_Action (\<A>_transformation (\<A>_simple_MTF ))\<close> *)

subsection \<open>Transformation\<close>

consts find_source_object :: action

declare [[\<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _ find_source_object\<close> \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _ find_source_object\<close> (100) ]]

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>cannot find a source object\<close> x \<open>enabling transformation\<close> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<w>\<i>\<t>\<h> P))
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action find_source_object\<close>
  unfolding Action_Tag_def FAIL_def
  by blast


(*TODO: hide_fact ToA_trivial *)

end
