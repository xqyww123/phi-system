chapter \<open>Pre-built \<phi>-Types\<close>

theory Phi_Types
  imports Phi_Type_Algebra
begin

ML \<open>Phi_Conv.set_rules__type_form_to_ex_quantified [] ;
    Phi_Conv.set_rules__type_form_to_ex_quantified_single_var [] \<close>

section \<open>Basics\<close>
 
subsection \<open>Preliminary Sugars\<close>

consts \<phi>coercion :: \<open>('c1,'a) \<phi> \<Rightarrow> ('c2,'a) \<phi>\<close> ("\<coercion> _" [61] 60)
  \<comment> \<open>merely a syntax sugar to be overloaded.\<close>

(*reconsider this! may depreciate it!*)
text \<open>A semantic type is not always required to be annotated if it is known syntactically.
  We use syntax translation to achieve a sugar to do this.

This is a planning feature has not been implemented\<close>

syntax TY_of_\<phi> :: \<open>('a,'b) \<phi> \<Rightarrow> TY\<close> ("TY'_of'_\<phi>")



subsection \<open>Func\<close>

declare [[\<phi>trace_reasoning = 0]]
         
\<phi>type_def \<phi>Fun :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('c,'a) \<phi>\<close>
  where \<open>\<phi>Fun f x = (f x \<Ztypecolon> Itself)\<close>
  deriving \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = 1 \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> \<phi>Fun f) True\<close>
       and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = 1 \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> \<phi>Fun f)\<close>
       and Basic
       and Functionality
       (*d Open_Abstraction_Full*)

subsubsection \<open>Algebraic Properties\<close>

lemma [\<phi>reason add]:
  \<open> closed_homo_sep f
\<Longrightarrow> Object_Sep_Homo\<^sub>I (\<phi>Fun f) UNIV \<close>
  unfolding Object_Sep_Homo\<^sub>I_def Transformation_def
  by (clarsimp simp add: set_mult_expn closed_homo_sep_disj.sep_disj_homo
                         homo_sep_mult.homo_mult closed_homo_sep_def homo_sep_def)

lemma [\<phi>reason add]:
  \<open> homo_sep f
\<Longrightarrow> Object_Sep_Homo\<^sub>E (\<phi>Fun f)\<close>
  unfolding Object_Sep_Homo\<^sub>E_def Transformation_def
  by (clarsimp simp add: set_mult_expn homo_sep_disj_def
                         homo_sep_mult.homo_mult homo_sep_def)



subsection \<open>Embedding Subjection into Type\<close>

declare [[\<phi>trace_reasoning = 2]]
 
\<phi>type_def SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<s>\<u>\<b>\<j>" 25)
  where [embed_into_\<phi>type]: \<open> (T \<phi>\<s>\<u>\<b>\<j> P) = (\<lambda>x. x \<Ztypecolon> T \<s>\<u>\<b>\<j> P) \<close>
  deriving Basic
       and \<open>(\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> Functionality T Q) \<Longrightarrow> Functionality (T \<phi>\<s>\<u>\<b>\<j> P) Q\<close>
       and Open_Abstraction_Full
       and \<open>(\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P) \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> Q) (Q \<and> P)\<close>
       and \<open>Identity_Element\<^sub>E (x \<Ztypecolon> T) \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P) \<close>
       and Functional_Transformation_Functor
       and Separation_Homo

translations "TY_of_\<phi> (T \<phi>\<s>\<u>\<b>\<j> P)" \<rightharpoonup> "TY_of_\<phi> T"


subsubsection \<open>Rules\<close>

paragraph \<open>Simplification Rules\<close>

declare SubjectionTY.unfold [\<phi>programming_simps, assertion_simps]

lemma \<phi>\<s>\<u>\<b>\<j>_\<phi>\<s>\<u>\<b>\<j>[embed_into_\<phi>type, simp]:
  \<open>(T \<phi>\<s>\<u>\<b>\<j> P \<phi>\<s>\<u>\<b>\<j> Q) = (T \<phi>\<s>\<u>\<b>\<j> P \<and> Q)\<close>
  by (rule \<phi>Type_eqI; clarsimp)


subsubsection \<open>Algebraic Properties\<close>

text \<open>Here we construct two inner transformations from \<open>a \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P\<close> to \<open>a \<Ztypecolon> T\<close> and another reversely.
  It is essentially an identity transformation from \<open>a\<close> to \<open>a\<close> itself.
  The constraints checks 1. if the identity transformation is supported (a very weak requirement),
        2. the container is always non-empty so that an independent assertion \<open>P\<close> bound at the element
           type is valid globally (this is a necessary condition).  \<close>


lemma \<phi>\<s>\<u>\<b>\<j>_Homo[\<phi>reason_template [assertion_simps]]:
  \<open> Transformation_Functor Fa Fa D R mapper
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a. a \<in> D x \<and> P \<longrightarrow> a \<in> R x) \<and> (\<forall>y. mapper (\<lambda>a b. a = b \<and> P) x y \<longrightarrow> x = y \<and> P)
\<Longrightarrow> (x \<Ztypecolon> Fa (T \<phi>\<s>\<u>\<b>\<j> P)) \<equiv> (x \<Ztypecolon> Fa T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Transformation_Functor_def Transformation_def atomize_eq Premise_def BI_eq_iff
  apply (clarsimp; rule)
  subgoal premises prems for p
    by (insert prems(1)[THEN spec[where x=\<open>T \<phi>\<s>\<u>\<b>\<j> P\<close>], THEN spec[where x=T], THEN spec[where x=x],
                           THEN spec[where x=\<open>\<lambda>a b. a = b \<and> P\<close>], simplified]
               prems(2-4),
        clarsimp,
        blast)
  subgoal premises prems for p
    by (insert prems(1)[THEN spec[where x=\<open>T\<close>], THEN spec[where x=\<open>T \<phi>\<s>\<u>\<b>\<j> P\<close>], THEN spec[where x=x],
                           THEN spec[where x=\<open>\<lambda>a b. a = b\<close>], simplified]
               prems(2-4),
        clarsimp,
        blast) .

text \<open>The above rule is interesting but essentially useless as it is replaced by the following rule.
  The To-Transformation already enters into the elements by transformation functor.\<close>

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x \<and> P @action \<A>simp\<close>
  unfolding Transformation_Functor_def Transformation_def Action_Tag_def
  by simp


subsection \<open>Dependent Sum Type\<close>

text \<open>Transformation functor requires inner elements to be transformed into some fixed \<phi>-type
  independently with the element. It seems to be a limitation. For example, we want to transform
  a list of unknown bit-length numbers \<open>l \<Ztypecolon> List T\<close> where \<open>x \<Ztypecolon> T \<equiv> (x \<Ztypecolon> \<nat>[b] \<s>\<u>\<b>\<j> b. x < 2^b)\<close>
  into a set of all lists of such numbers \<open>{l | ? } \<Ztypecolon> List \<nat>[?]\<close> where the question marks denote
  the terms cannot be expressed yet now.

  Such transformation can be expressed by \<^emph>\<open>Dependent Sum Type\<close> \<open>\<Sigma>\<close> and \<^emph>\<open>Set Abstraction\<close> \<open>LooseState\<close> \<close>
                  
\<phi>type_def \<phi>Dependent_Sum :: \<open>('c \<Rightarrow> ('a,'b) \<phi>) \<Rightarrow> ('a, 'c \<times> 'b) \<phi>\<close> ("\<Sigma> _" [26] 26)
  where \<open>cx \<Ztypecolon> \<phi>Dependent_Sum T \<equiv> (snd cx) \<Ztypecolon> T (fst cx)\<close>
   
  deriving Abstract_Domain
    and    \<open>(\<And>A. Object_Equiv (T A) (eq A))
        \<Longrightarrow> Object_Equiv (\<Sigma> T) (\<lambda>x y. fst y = fst x \<and> eq (fst x) (snd x) (snd y))\<close>
    and \<open>Object_Equiv (\<Sigma> (\<lambda>x. \<circle>)) (\<lambda>_ _. True) \<close>
    and    \<open>Identity_Element\<^sub>I (u \<Ztypecolon> T c) P
        \<Longrightarrow> Identity_Element\<^sub>I ((c, u) \<Ztypecolon> \<Sigma> T) P \<close>
    and    \<open>Identity_Element\<^sub>E (u \<Ztypecolon> T c)
        \<Longrightarrow> Identity_Element\<^sub>E ((c, u) \<Ztypecolon> \<Sigma> T) \<close>
    and Functionality
  (*and    \<open>Is_Functional (u \<Ztypecolon> T c)
        \<Longrightarrow> Is_Functional ((c, u) \<Ztypecolon> \<Sigma> T)\<close> *)
    and   \<open>(\<And>a (x::?'b \<times> ?'a). a \<Ztypecolon> T (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Itself \<s>\<u>\<b>\<j> b. r a b @action to Itself)
        \<Longrightarrow> \<forall>(x::?'b \<times> ?'a). x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>b. r (snd x) b \<and> y = b) @action to Itself \<close>



notation \<phi>Dependent_Sum (binder "\<Sigma> " 22)

declare SubjectionTY_def[embed_into_\<phi>type del]
declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def Set_Abstraction :: \<open>('a,'b) \<phi> \<Rightarrow> ('a, 'b set) \<phi>\<close> ("\<S> _" [26] 26)
  where [embed_into_\<phi>type]: \<open>s \<Ztypecolon> \<S> T \<equiv> (x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s)\<close>
  deriving \<open> Abstract_Domain T P \<Longrightarrow> Abstract_Domain (\<S> T) (\<lambda>s. \<exists>x\<in>s. P x) \<close>
       and \<open> Abstract_Domain\<^sub>L T P \<Longrightarrow> Abstract_Domain\<^sub>L (\<S> T) (\<lambda>s. \<exists>x\<in>s. P x) \<close>
       and \<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<S> T) (\<lambda>Sx Sy. \<forall>x \<in> Sx. \<exists>y \<in> Sy. eq x y) \<close>
       and \<open> Object_Equiv (\<S> \<circle>) (\<lambda>Sx Sy. Sx \<noteq> {} \<longrightarrow> Sy \<noteq> {}) \<close>
       and Identity_Element
       and Open_Abstraction_Full
       and \<open>Transformation_Functor Set_Abstraction Set_Abstraction (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>g Sx Sy. Sy = {y. \<exists>x\<in>Sx. g x y})\<close>
       and \<open>Functional_Transformation_Functor Set_Abstraction Set_Abstraction
                      (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>g Sx Sy. Sy = {y. \<exists>x\<in>Sx. g x y}) True
                      (\<lambda>_ _ _. True) (\<lambda>f P X. { f x |x. x \<in> X \<and> P x})\<close>

text \<open>Read it as 'the abstract object is certain element in the set'

Together with the \<^const>\<open>SubjectionTY\<close>, \<^const>\<open>\<phi>Dependent_Sum\<close> and \<^const>\<open>Set_Abstraction\<close> embed
  BI connective \<open>\<and>\<close> (\<^const>\<open>Subjection\<close>) and \<open>\<exists>\<close> (\<^const>\<open>ExSet\<close>) into \<phi>-types. The embedding of \<open>\<exists>\<close>
  is in an algebraic way having good properties like the \<Sigma>-Homomorphism and \<S>-Homomorphism introduced below.

The system reduces the three \<phi>-types actively just like how it reduces BI \<open>\<exists>\<close> and \<open>\<and>\<close>.
Any pure facts in the conjunctions are extracted and stored, and existentially quantified variables are fixed.
This reduction is reversible (meaning loosing no information).

User should define their own \<phi>-types wrapping \<open>\<S>\<close> if they do not want this reduction.
However, a specific fixed variable is generally easier to use than a certain element in a set.

\<open>\<Sigma>\<close>-type usually cannot be reduced because there is no non-trivial homomorphism
\<open>x \<Ztypecolon> F(\<Sigma> T) \<longleftrightarrow> f(x) \<Ztypecolon> \<Sigma>(F T)\<close> that moves a \<open>\<Sigma>\<close> out from a type operator \<open>F\<close>, unless
all the first projection of the elements of \<open>x\<close> are equal. However,
the reasoning about \<open>\<Sigma>\<close> has no problem because the \<open>x\<close> is given, so the parameters of the type i.e.,
the first projections of the elements of \<open>x\<close> are known.
We can apply \<open>\<Sigma>\<^sub>E\<close> and \<open>\<Sigma>\<^sub>I\<close> in the element transformation of \<open>x\<close> by \<open>F\<close>'s transformation functor property,
and the generated proof obligations about \<open>x\<close> are able to specify the type parameter of \<open>T\<close>,
e.g., if all the first projection of the elements of \<open>x\<close> are unchanged throughout the transformation, the
  type parameter of \<open>T\<close> is unchanged).
\<open>x \<Ztypecolon> \<Sigma> T \<longrightarrow> \<pi>\<^sub>2(x) \<Ztypecolon> T (\<pi>\<^sub>1 x)     (\<Sigma>\<^sub>E)\<close>
\<open>x \<Ztypecolon> T(c) \<longrightarrow> (c,x) \<Ztypecolon> \<Sigma> T        (\<Sigma>\<^sub>I)\<close>

\<open>\<S>\<close> type has homomorphism, and it is entailed in Transformation Functor.

\<close>

declare SubjectionTY_def[embed_into_\<phi>type add]
        Set_Abstraction_def[embed_into_\<phi>type del]

subsubsection \<open>Rules\<close>

paragraph \<open>Simplifications\<close>

declare \<phi>Dependent_Sum.unfold [embed_into_\<phi>type, \<phi>programming_base_simps, assertion_simps, simp]

lemma Set_Abstraction_single[embed_into_\<phi>type]:
  \<open>{x} \<Ztypecolon> \<S> T \<equiv> x \<Ztypecolon> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma Set_Abstraction_unfold_defined:
  \<open> {x. x = y \<and> P} \<Ztypecolon> \<S> T \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> P \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma Set_Abstraction_unfold_Ex:
  \<open> {x. \<exists>a. P x a} \<Ztypecolon> \<S> T \<equiv> {x. P x a} \<Ztypecolon> \<S> T \<s>\<u>\<b>\<j> a. \<top> \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp blast

lemma Set_Abstraction_unfold':
  \<open> NO_MATCH {a} s
\<Longrightarrow> NO_MATCH {x. x = y'\<and> P'} s
\<Longrightarrow> NO_MATCH {x. \<exists>a. P'' x a} s
\<Longrightarrow> (s \<Ztypecolon> \<S> T) = (x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s)\<close>
  using Set_Abstraction.unfold .

lemmas [\<phi>programming_base_simps, assertion_simps, simp] =
  Set_Abstraction_single
  Set_Abstraction_unfold_defined
  Set_Abstraction_unfold_Ex
  Set_Abstraction_unfold'


lemma \<phi>\<s>\<u>\<b>\<j>_over_\<S>[\<phi>programming_simps]:
  \<open>\<S> (T \<phi>\<s>\<u>\<b>\<j> P) \<equiv> (\<S> T) \<phi>\<s>\<u>\<b>\<j> P\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI, simp, blast)

lemma \<phi>\<s>\<u>\<b>\<j>_over_\<Sigma>[\<phi>programming_simps]:
  \<open>\<Sigma> x. (T x \<phi>\<s>\<u>\<b>\<j> P) \<equiv> (\<Sigma> T) \<phi>\<s>\<u>\<b>\<j> P\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI, simp)

lemma [embed_into_\<phi>type]:
  \<open> NO_MATCH (\<lambda>_. T') T
\<Longrightarrow> f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { (x, f x) |x. P x } \<Ztypecolon> \<S> \<Sigma> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open> f x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { f x |x. P x } \<Ztypecolon> \<S> T \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open>x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> x \<in> s \<s>\<u>\<b>\<j> x. \<top> \<equiv> s \<Ztypecolon> \<S> T \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open> NO_MATCH (\<lambda>_. T') T
\<Longrightarrow> {x. P c x} \<Ztypecolon> \<S> (T c) \<s>\<u>\<b>\<j> c. \<top> \<equiv> {x. \<exists>c y. x = (c, y) \<and> P c y} \<Ztypecolon> \<S> \<Sigma> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma [embed_into_\<phi>type]:
  \<open> {x. P c x} \<Ztypecolon> \<S> T \<s>\<u>\<b>\<j> c. \<top> \<equiv> {x. \<exists>c. P c x} \<Ztypecolon> \<S> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

paragraph \<open>Conversion Setup\<close>

lemma pure_type_to_ex_quantified_form_3:
  \<open> Collect P \<Ztypecolon> \<S> T \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. P y \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

ML \<open>Phi_Conv.set_rules__type_form_to_ex_quantified
      @{thms' Set_Abstraction_unfold_Ex Set_Abstraction_unfold_defined
              SubjectionTY.unfold} ;
    Phi_Conv.set_rules__type_form_to_ex_quantified_single_var
      @{thms' Set_Abstraction_unfold_Ex pure_type_to_ex_quantified_form_3
              SubjectionTY.unfold} \<close>


paragraph \<open>ToA Reasoning\<close>

declare \<phi>Dependent_Sum.intro_reasoning(1)
        [where x=\<open>(a,b)\<close> for a b, simplified,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.intro_reasoning(2)
        [where x=\<open>(a,b)\<close> for a b, simplified,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.elim_reasoning[\<phi>reason 1000]

declare Set_Abstraction.intro_reasoning  [\<phi>reason 60 (*TODO 60*)]
        Set_Abstraction.elim_reasoning(1)[\<phi>reason 1000]

lemma [\<phi>reason 2800]:
  \<open> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> fst x \<Longrightarrow> (a, snd x) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE )
\<Longrightarrow> x \<Ztypecolon> (\<S> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  unfolding Action_Tag_def Premise_def Transformation_def
  by (cases x; clarsimp; blast)

lemma [\<phi>reason 2800]:
  \<open> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> fst x \<Longrightarrow> (a, snd x) \<Ztypecolon> \<black_circle> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi )
\<Longrightarrow> x \<Ztypecolon> \<black_circle> (\<S> T) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Action_Tag_def Premise_def Transformation_def
  by (cases x; clarsimp; blast)


subsubsection \<open>\<Sigma>-Homomorphism\<close>

definition \<open>Trivial_\<Sigma> Fa Fb D s m \<longleftrightarrow> (\<forall>T x. D (s x) x \<longrightarrow> (x \<Ztypecolon> Fa (\<Sigma> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> m x \<Ztypecolon> Fb (T (s x))))\<close>
  \<comment> \<open>There is only trivial homomorphism where all the first projection of the element are equal\<close>

lemma apply_Trivial_\<Sigma>:
  \<open> Trivial_\<Sigma> Fa Fb D s m
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (s x) x
\<Longrightarrow> x \<Ztypecolon> Fa (\<Sigma> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> m x \<Ztypecolon> Fb (T (s x))\<close>
  unfolding Trivial_\<Sigma>_def Premise_def
  by blast

text \<open>In this trivial homomorphism, the first project of all elements are equal.

This homomorphism can give us a simplification rule that strips the inner \<open>\<Sigma>\<close>. However,
the first project of all elements are equal, this is not a usual situation, so this simplification
is invoked manually by \<open>to \<s>\<t>\<r>\<i>\<p>-\<Sigma>\<close>
\<close>

consts \<A>strip_\<Sigma> :: \<open>('a,'b) \<phi>\<close> ("\<s>\<t>\<r>\<i>\<p>-\<Sigma>")

definition \<phi>Auto_\<Sigma> ("\<Sigma>\<^sub>\<A> _" [26] 26)
  where [assertion_simps]: "\<phi>Auto_\<Sigma> \<equiv> \<phi>Dependent_Sum"

notation \<phi>Auto_\<Sigma> (binder "\<Sigma>\<^sub>\<A> " 22)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> \<Sigma>\<^sub>\<A> T \<s>\<u>\<b>\<j> x'. x' = x @action to \<s>\<t>\<r>\<i>\<p>-\<Sigma> \<close>
  unfolding Action_Tag_def \<phi>Auto_\<Sigma>_def
  by simp

lemma [\<phi>reason !10]: \<comment> \<open>fallback if fails to strip \<Sigma> by simplification\<close>
  \<open> x \<Ztypecolon> \<Sigma>\<^sub>\<A> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> \<Sigma> T \<s>\<u>\<b>\<j> x'. x' = x @action \<A>simp \<close>
  unfolding Action_Tag_def \<phi>Auto_\<Sigma>_def
  by simp


paragraph \<open>Deriver\<close>

lemma \<phi>TA_SgH_rule:
  \<open> (\<And>T y x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s x = y \<Longrightarrow> (Ant @action \<phi>TA_ANT) \<longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D y x \<longrightarrow>
        (x \<Ztypecolon> Fa (\<Sigma>\<^sub>\<A> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, m x) \<Ztypecolon> \<Sigma>\<^sub>\<A> c. Fb (T c)) @action \<phi>TA_ind_target \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Trivial_\<Sigma> Fa Fb D s m\<close>
  unfolding Trivial_\<Sigma>_def Premise_def Action_Tag_def \<phi>Auto_\<Sigma>_def
  by simp

lemma \<phi>TA_SgH_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> DD \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U) @action \<phi>TA_ind_target \<A>)
 \<equiv> (Ant \<Longrightarrow> DD \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<s>\<u>\<b>\<j> y'. y' = y @action \<A>) \<close>
  unfolding Action_Tag_def atomize_imp
  by simp

lemma \<phi>TA_SgH_rewr_C:
  \<open> Trueprop (Ant \<longrightarrow> DD \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) @action \<phi>TA_ind_target \<A>)
 \<equiv> (Ant \<Longrightarrow> DD \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_SgH_T_intro:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T c' \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> c = c'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T c \<w>\<i>\<t>\<h> P \<close>
  unfolding Premise_def by simp

lemma \<phi>TA_SgH_T_intro':
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T c' \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> c = c'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T c \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P \<close>
  unfolding Premise_def by simp

ML_file \<open>library/phi_type_algebra/sigma_single_point.ML\<close>

\<phi>property_deriver Trivial_\<Sigma> 130 for ( \<open>Trivial_\<Sigma> _ _ _ _ _\<close> )
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Algebra_Derivers.sigma_trivial_homomorphism \<close>

hide_fact \<phi>TA_SgH_T_intro' \<phi>TA_SgH_T_intro \<phi>TA_SgH_rewr_C \<phi>TA_SgH_rewr_IH \<phi>TA_SgH_rule




subsubsection \<open>\<S>-Homomorphism\<close>

text \<open>The homomorphism of \<open>\<S>\<close> type is entailed in the transformation functor directly.\<close>

lemma \<S>_Homo\<^sub>E:
  \<open> Transformation_Functor Fa Fb D R mapper
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D s \<and> b \<in> a \<longrightarrow> b \<in> R s)
\<Longrightarrow> s \<Ztypecolon> Fa (\<S> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb T \<s>\<u>\<b>\<j> y. mapper (\<lambda>S x. x \<in> S) s y\<close>
  unfolding Transformation_Functor_def Transformation_def Premise_def
  apply clarsimp
  subgoal premises prems for v
    by (insert prems(1)[THEN spec[where x=\<open>\<S> T\<close>], THEN spec[where x=\<open>T\<close>],
                        THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>S x. x \<in> S\<close>],
                        simplified]
               prems(2,3),
        clarsimp) .

lemma \<S>_Homo\<^sub>I:
  \<open> Transformation_Functor Fa Fb D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D s \<longrightarrow> {a} \<in> R s)
\<Longrightarrow> s \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<s>\<u>\<b>\<j> s'. mapper (\<lambda>a b. b = {a}) s s' \<close>
  unfolding Action_Tag_def Transformation_Functor_def Premise_def
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=T], THEN spec[where x=\<open>\<S> T\<close>], THEN spec[where x=s],
                        THEN spec[where x=\<open>\<lambda>a b. b = {a}\<close>], simplified]
               prems(2),
        clarsimp) .

text \<open>The above rules are interesting but essentially useless as it is replaced by the following rule.\<close>

lemma [\<phi>reason 1000]:
  \<open>s \<Ztypecolon> \<S> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s @action \<A>simp\<close>
  unfolding Action_Tag_def Transformation_def
  by simp



subsection \<open>Vertical Composition\<close>

\<phi>type_def \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 30)
  where \<open>\<phi>Composition T U x = (y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<Turnstile> (x \<Ztypecolon> U))\<close>
  deriving Functional_Transformation_Functor

text \<open>
  We do not use deriver here.
  It is too basic and our reasoner can barely do little about \<phi>-types embedded in a
  satisfaction statement because it as a pure proposition loses the type structure to guide our
  reasoner. As a consequence, almost every property of the \<phi>-type has to be proven manually.

  For this reason, user should use \<open>(T \<Zcomp> U)\<close> instead of a raw satisfaction statement \<open>x \<Turnstile> X\<close>.
  The only meaningful interpretation of the satisfaction statement that we can imagine, is for
  vertical composition of abstractions. Therefore, \<open>(T \<Zcomp> U)\<close> should be able to replace any usage
  of satisfaction statement.
\<close>

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain U A
\<Longrightarrow> Abstract_Domain T B
\<Longrightarrow> Abstract_Domain (T \<Zcomp> U) (\<lambda>x. A x \<and> Ex B) \<close>
  unfolding Inhabited_def Action_Tag_def Abstract_Domain_def
  by simp blast

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain\<^sub>L U A
\<Longrightarrow> Abstract_Domain\<^sub>L T B
\<Longrightarrow> Abstract_Domain\<^sub>L (T \<Zcomp> U) (\<lambda>x. A x \<and> All B) \<close>
  unfolding Inhabited_def Action_Tag_def Abstract_Domain\<^sub>L_def
  by clarsimp blast

text \<open>The space between the upper bound and the lower bound is inevitable as we lost the exact value
  of the middle-level object in this vertical composition.\<close>

lemma [\<phi>reason 1000]:
  \<open> Functionality U P\<^sub>U
\<Longrightarrow> Functionality T P\<^sub>T
\<Longrightarrow> Functionality (T \<Zcomp> U) (\<lambda>x. P\<^sub>U x \<and> (\<forall>m. m \<Turnstile> (x \<Ztypecolon> U) \<longrightarrow> P\<^sub>T m)) \<close>
  unfolding Functionality_def Premise_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rU x y @action to (Itself :: ('b,'b) \<phi>))
\<Longrightarrow> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'c) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rT x y @action to (Itself :: ('c,'c) \<phi>))
\<Longrightarrow> x \<Ztypecolon> T \<Zcomp> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>m. rT m y \<and> rU x m) @action to (Itself :: ('c,'c) \<phi>)\<close>
  unfolding Transformation_def Action_Tag_def
  by clarsimp  blast

   
lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>I (1 \<Ztypecolon> B) P \<and> Identity_Element\<^sub>I (x \<Ztypecolon> T) Q \<or>\<^sub>c\<^sub>u\<^sub>t (\<forall>x. Identity_Element\<^sub>I (x \<Ztypecolon> B) P) \<and> Q = True
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> B \<Zcomp> T) (P \<and> Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Orelse_shortcut_def
  by simp blast
     
lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>E (1 \<Ztypecolon> B)
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T)
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> B \<Zcomp> T)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by simp blast
 
lemma [\<phi>reason 1000]:
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv (B \<Zcomp> T) eq \<close>
  unfolding Object_Equiv_def Transformation_def
  by clarsimp blast

let_\<phi>type \<phi>Composition deriving SE_Trim_Empty


(*
lemma [\<phi>reason 1200]:
  \<open> y \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE U \<w>\<i>\<t>\<h> P
\<Longrightarrow> y \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE (T \<Zcomp> U) \<w>\<i>\<t>\<h> P\<close>
  \<medium_left_bracket> premises Y[unfolded Transformation_def Itself_expn, simplified, useful]
    construct\<phi> \<open>x \<Ztypecolon> T \<Zcomp> U\<close> \<medium_right_bracket> .
*)


subsubsection \<open>Algebraic Properties\<close>

lemma \<phi>Composition_Separation_Homo\<^sub>I[\<phi>reason 1000]:
  \<open> Object_Sep_Homo\<^sub>I B UNIV
\<Longrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>_ _ _. True) UNIV (\<lambda>x. x)\<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
  by (clarsimp, insert times_set_I, blast)

lemma (*The above rule is reversible. requiring the sep homo domain being the univ is already the weakest.*)
  \<open> S \<noteq> {}
\<Longrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>_ _ _. True) S (\<lambda>x. x)
\<Longrightarrow> Object_Sep_Homo\<^sub>I B UNIV \<close>
  unfolding Separation_Homo\<^sub>I_def Object_Sep_Homo\<^sub>I_def Transformation_def
  apply (clarsimp simp add: set_mult_expn)
  apply (simp add: \<phi>Type_def)
  subgoal premises prems for x y u v
    by (insert prems(2)[THEN spec[where x=\<open>\<lambda>_. {y}\<close>], THEN spec[where x=\<open>\<lambda>_. {x}\<close>], simplified]
               prems(1,3-5),
        auto simp add: Satisfaction_def) .

  
lemma \<phi>Composition_separatio_functor_unzip[\<phi>reason 1000]:
  \<open> Object_Sep_Homo\<^sub>E B
\<Longrightarrow> Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x)\<close>
  for B :: \<open>('d::sep_magma,'e::sep_magma) \<phi>\<close>
  unfolding Separation_Homo\<^sub>E_def Transformation_def Object_Sep_Homo\<^sub>E_def
  by (clarsimp simp add: set_mult_expn; blast)

lemma (*The above rule is reversible*)
  \<open> Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x) \<Longrightarrow> Object_Sep_Homo\<^sub>E B \<close>
  unfolding Separation_Homo\<^sub>E_def Object_Sep_Homo\<^sub>E_def Transformation_def
  apply (clarsimp simp add: set_mult_expn)
  apply (simp add: \<phi>Type_def Satisfaction_def)
  subgoal premises prems for x y v
    by (insert prems(1)[THEN spec[where x=\<open>\<lambda>_. {y}\<close>], THEN spec[where x=\<open>\<lambda>_. {x}\<close>], simplified]
               prems(2-3), blast) .

(*
lemma
  \<open> Semimodule_LDistr_Homo\<^sub>O\<^sub>Z B Ds Dx' zz
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z  (\<lambda>s. (\<Zcomp>) (B s)) Ds Dx z \<close>
*)



(* subsection \<open>Embedding Universal Quantification\<close>

\<phi>type_def \<phi>Type_univ_quant :: \<open>('c \<Rightarrow> ('a, 'b) \<phi>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b)\<phi>\<close> ("\<forall>\<^sub>\<phi> _" [10] 10)
  where \<open>\<phi>Type_univ_quant T = (\<lambda>x. \<forall>\<^sub>B\<^sub>Ic. x c \<Ztypecolon> T c)\<close>

lemma \<phi>Type_univ_quant_expn[\<phi>expns]:
  \<open>p \<in> (f \<Ztypecolon> (\<forall>\<^sub>\<phi> T)) \<longleftrightarrow> (\<forall>x. p \<in> (f x \<Ztypecolon> T x))\<close>
  unfolding \<phi>Type_univ_quant_def \<phi>Type_def by clarsimp
*)


subsection \<open>Embedding Additive Disjunction\<close>

subsubsection \<open>Preliminary Settings\<close>

term case_sum

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 1020]:
  \<open> A a \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> case_sum A B (Inl a) \<i>\<m>\<p>\<l>\<i>\<e>\<s> P\<close>
  by simp

lemma [\<phi>reason 1020]:
  \<open> B b \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> case_sum A B (Inr b) \<i>\<m>\<p>\<l>\<i>\<e>\<s> P\<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> A a \<i>\<m>\<p>\<l>\<i>\<e>\<s> P a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> B b \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q b)
\<Longrightarrow> case_sum A B x \<i>\<m>\<p>\<l>\<i>\<e>\<s> case_sum P Q x \<close>
  by (cases x; simp)



subsubsection \<open>\<phi>-Type Embedding of Multiplicative Finite Quantification\<close>

definition \<phi>Mul_Quant :: \<open>'i set \<Rightarrow> ('i \<Rightarrow> ('c::sep_algebra, 'x) \<phi>) \<Rightarrow> ('c::sep_algebra, 'i \<Rightarrow> 'x) \<phi>\<close> ("\<big_ast>\<^sup>\<phi>")
  where \<open>\<big_ast>\<^sup>\<phi> I T = (\<lambda>x. \<big_ast>i\<in>I. x i \<Ztypecolon> T i)\<close>

syntax
  "_\<phi>Mul_Quant" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> logic \<Rightarrow> logic"  ("(2\<big_ast>[_/\<in>_]/ _)" [0, 51, 1000] 1000)
  "_\<phi>Mul_Quant_print" :: "pttrn \<Rightarrow> pttrn \<Rightarrow> 'x \<Rightarrow> 'a set \<Rightarrow> 'T \<Rightarrow> logic"
translations
  "x \<Ztypecolon> \<big_ast>[i\<in>I] T" => "CONST \<phi>Type (\<lambda>i. x) (CONST \<phi>Mul_Quant I (\<lambda>i. T))"
  "x \<Ztypecolon> \<big_ast>[i\<in>I] T" <= "CONST \<phi>Type (\<lambda>i. x) (CONST \<phi>Mul_Quant I (\<lambda>j. T))"

print_translation \<open>[
  (\<^syntax_const>\<open>_\<phi>Mul_Quant_print\<close>, (fn ctxt =>fn L => hd (@{print} L)))
]\<close>


subsubsection \<open>Separation Extraction\<close>

term insert

lemma
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> I \<Longrightarrow> (fst x i, fst wr) \<Ztypecolon> T i \<^emph> Wi \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Y \<^emph> Ri)
\<Longrightarrow> (fst x, snd x) \<Ztypecolon> \<big_ast>\<^sup>\<phi> (Set.remove i I) T \<^emph> Ws \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> wr \<Ztypecolon> Wi \<^emph> Rs
\<Longrightarrow> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd wr) \<Ztypecolon> Y \<^emph> (Ri \<^emph> Rs) \<w>\<i>\<t>\<h> P\<close>
  sorry
  (*\<medium_left_bracket> premises I and S
    *)

lemma
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> J = I
\<Longrightarrow> (\<And>i\<in>J. (fst x i, snd x i) \<Ztypecolon> T i \<^emph> W i \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y i \<Ztypecolon> Y i \<^emph> R i)
\<Longrightarrow> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T \<^emph> \<big_ast>\<^sup>\<phi> J W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst o y, fst x, snd o y) \<Ztypecolon> \<big_ast>\<^sup>\<phi> J Y \<^emph> (\<big_ast>\<^sup>\<phi> (I-J) T \<^emph> \<big_ast>\<^sup>\<phi> J R) \<w>\<i>\<t>\<h> P\<close>
  sorry

lemma
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> J \<subseteq> I
\<Longrightarrow> (\<And>i\<in>J. (fst x i, snd x i) \<Ztypecolon> T i \<^emph> W i \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y i \<Ztypecolon> Y i \<^emph> R i)
\<Longrightarrow> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T \<^emph> \<big_ast>\<^sup>\<phi> J W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst o y, fst x, snd o y) \<Ztypecolon> \<big_ast>\<^sup>\<phi> J Y \<^emph> (\<big_ast>\<^sup>\<phi> (I-J) T \<^emph> \<big_ast>\<^sup>\<phi> J R) \<w>\<i>\<t>\<h> P\<close>
  sorry


(* TODO!
subsubsection \<open>Addition of Algebraic Data Type\<close>

declare [[\<phi>trace_reasoning = 3]]
           
\<phi>type_def \<phi>ADT_Add :: \<open>('c,'x) \<phi> \<Rightarrow> ('c, 'y) \<phi> \<Rightarrow> ('c, 'x + 'y) \<phi>\<close> (infixl "+\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T +\<^sub>\<phi> U) = (\<lambda>xy. case xy of Inl x \<Rightarrow> x \<Ztypecolon> T | Inr y \<Rightarrow> y \<Ztypecolon> U)\<close>
  deriving Implication
       and \<open>Object_Equiv T eq\<^sub>T \<Longrightarrow> Object_Equiv U eq\<^sub>U \<Longrightarrow> Object_Equiv (T +\<^sub>\<phi> U) (rel_sum eq\<^sub>T eq\<^sub>U)\<close>

term \<open>Object_Equiv T eq\<^sub>T \<Longrightarrow> Object_Equiv U eq\<^sub>U \<Longrightarrow> Object_Equiv (T +\<^sub>\<phi> U) (rel_sum eq\<^sub>T eq\<^sub>U)\<close>

thm old.sum.simps

term \<open>(fst x \<Ztypecolon> T) + (snd x \<Ztypecolon> U)\<close>
*)


subsection \<open>Embedding Additive Disjunction\<close>

declare [[\<phi>trace_reasoning = 0]]
    
\<phi>type_def \<phi>Union :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<or>\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T \<or>\<^sub>\<phi> U) = (\<lambda>x. (fst x \<Ztypecolon> T) + (snd x \<Ztypecolon> U))\<close>
  deriving \<open>  Abstract_Domain A Pa
          \<Longrightarrow> Abstract_Domain B Pb
          \<Longrightarrow> Abstract_Domain (A \<or>\<^sub>\<phi> B) (\<lambda>(a,b). Pa a \<or> Pb b) \<close>
       and \<open>  Abstract_Domain\<^sub>L A Pa
          \<Longrightarrow> Abstract_Domain\<^sub>L B Pb
          \<Longrightarrow> Abstract_Domain\<^sub>L (A \<or>\<^sub>\<phi> B) (\<lambda>(a,b). Pa a \<or> Pb b) \<close>
       and \<open>  Object_Equiv T eqa
          \<Longrightarrow> Object_Equiv U eqb
          \<Longrightarrow> Object_Equiv (T \<or>\<^sub>\<phi> U) (\<lambda>(a1,b1) (a2,b2). eqa a1 a2 \<and> eqb b1 b2)\<close>
       and \<open>  Identity_Element\<^sub>I (1 \<Ztypecolon> T) P
          \<Longrightarrow> Identity_Element\<^sub>I (1 \<Ztypecolon> U) Q
          \<Longrightarrow> Identity_Element\<^sub>I (1 \<Ztypecolon> T \<or>\<^sub>\<phi> U) (P \<or> Q)\<close>
       and \<open>  Identity_Element\<^sub>E (1 \<Ztypecolon> T) \<or> Identity_Element\<^sub>E (1 \<Ztypecolon> U)
          \<Longrightarrow> Identity_Element\<^sub>E (1 \<Ztypecolon> T \<or>\<^sub>\<phi> U) \<close>

subsubsection \<open>Configurations\<close>

declare \<phi>Union_def[embed_into_\<phi>type del]

lemma [embed_into_\<phi>type]:
  \<open>(x \<Ztypecolon> T) + (y \<Ztypecolon> U) \<equiv> (x,y) \<Ztypecolon> T \<or>\<^sub>\<phi> U\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

let_\<phi>type \<phi>Union deriving \<open>Object_Equiv (\<circle> \<or>\<^sub>\<phi> \<circle>) (\<lambda>_ _. True)\<close>


subsection \<open>Embedding Additive Conjunction\<close>
     
\<phi>type_def \<phi>Inter :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<and>\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T \<and>\<^sub>\<phi> U) = (\<lambda>x. (fst x \<Ztypecolon> T) \<and>\<^sub>B\<^sub>I (snd x \<Ztypecolon> U))\<close>
  deriving \<open>  Abstract_Domain T P
          \<Longrightarrow> Abstract_Domain U Q
          \<Longrightarrow> Abstract_Domain (T \<and>\<^sub>\<phi> U) (\<lambda>(x,y). P x \<and> Q y)\<close>
       (*and \<open>  Abstract_Domain\<^sub>L T P
          \<Longrightarrow> Abstract_Domain\<^sub>L U Q
          \<Longrightarrow> Abstract_Domain\<^sub>L (T \<and>\<^sub>\<phi> U) (\<lambda>(x,y). P x \<and> Q y)\<close>
         The lower bound of (T \<and>\<^sub>\<phi> U) is not derivable as there is no sufficiency reasoning for additive conjunction *)
       and \<open>  Object_Equiv T eqa
          \<Longrightarrow> Object_Equiv U eqb
          \<Longrightarrow> Object_Equiv (T \<and>\<^sub>\<phi> U) (\<lambda>(a1,b1) (a2,b2). eqa a1 a2 \<and> eqb b1 b2)\<close>
       and \<open>  Identity_Element\<^sub>I (1 \<Ztypecolon> T) P \<or> Identity_Element\<^sub>I (1 \<Ztypecolon> U) Q
          \<Longrightarrow> Identity_Element\<^sub>I (1 \<Ztypecolon> T \<and>\<^sub>\<phi> U) (P \<or> Q)\<close>
       and \<open>  Identity_Element\<^sub>E (1 \<Ztypecolon> T)
          \<Longrightarrow> Identity_Element\<^sub>E (1 \<Ztypecolon> U)
          \<Longrightarrow> Identity_Element\<^sub>E (1 \<Ztypecolon> T \<and>\<^sub>\<phi> U)\<close>
       and Functional_Transformation_Functor
     (*DO NOT REMOVE, I'm thinking if we really should support so much additive conjunction
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = A' \<Longrightarrow>
              Transformation_Functor ((\<and>\<^sub>\<phi>) A) ((\<and>\<^sub>\<phi>) A') Basic_BNFs.snds (\<lambda>_. UNIV) (rel_prod (=))\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B' \<Longrightarrow>
              Transformation_Functor (\<lambda>A. A \<and>\<^sub>\<phi> B) (\<lambda>A. A \<and>\<^sub>\<phi> B') Basic_BNFs.fsts (\<lambda>_. UNIV) (\<lambda>r. rel_prod r (=))\<close>
       and \<open>Functional_Transformation_Functor ((\<and>\<^sub>\<phi>) A) ((\<and>\<^sub>\<phi>) A') Basic_BNFs.snds (\<lambda>_. UNIV)
                                              (rel_prod (=)) (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = A') (pred_prod (\<lambda>a. True)) (map_prod (\<lambda>a. a))\<close>
       and \<open>Functional_Transformation_Functor (\<lambda>A. A \<and>\<^sub>\<phi> B) (\<lambda>A. A \<and>\<^sub>\<phi> B') Basic_BNFs.fsts
                                              (\<lambda>_. UNIV) (\<lambda>r. rel_prod r (=)) (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B') (\<lambda>p. pred_prod p (\<lambda>a. True)) (\<lambda>f. map_prod f (\<lambda>a. a))\<close> *)


subsubsection \<open>Rules\<close>

declare \<phi>Inter_def[embed_into_\<phi>type del]

lemma \<phi>Inter_embedding[embed_into_\<phi>type]:
  \<open>(x \<Ztypecolon> T) \<and>\<^sub>B\<^sub>I (y \<Ztypecolon> U) \<equiv> (x, y) \<Ztypecolon> T \<and>\<^sub>\<phi> U\<close>
  unfolding atomize_eq BI_eq_iff
  by simp

lemma [\<phi>reason 1000]:
  \<open> fst x \<Ztypecolon> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ra y @action to Itself
\<Longrightarrow> snd x \<Ztypecolon> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rb y @action to Itself
\<Longrightarrow> x \<Ztypecolon> A \<and>\<^sub>\<phi> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ra y \<and> rb y @action to Itself \<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp


subsection \<open>Vertical Composition of Function\<close>

text \<open>It is a more specific form than \<open>\<phi>Fun f \<Zcomp> T\<close> whose automation rules are more general.\<close>

declare [[\<phi>trace_reasoning = 0]]
            
\<phi>type_def \<phi>Fun' :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close> (infixl "\<Zcomp>\<^sub>f" 30)
  where \<open>\<phi>Fun' f T = (\<phi>Fun f \<Zcomp> T)\<close>
  deriving Basic
       and \<open> homo_one f \<and> Identity_Element\<^sub>I (x \<Ztypecolon> T) P \<or>\<^sub>c\<^sub>u\<^sub>t constant_1 f \<and> P = True \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> \<phi>Fun' f T) P \<close>
       and \<open> homo_one f \<and> Identity_Element\<^sub>E (x \<Ztypecolon> T) \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> \<phi>Fun' f T) \<close>
       and Functionality
       and Functional_Transformation_Functor
       and Trivial_\<Sigma>
       and Open_Abstraction_Full
       and \<open>homo_sep \<psi> \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL TEXT(\<open>Fail to derive \<close>) \<Longrightarrow> Separation_Homo\<^sub>E (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<lambda>x. x)\<close>

term \<open> homo_one f \<and> Identity_Element\<^sub>I (x \<Ztypecolon> T) P \<or>\<^sub>c\<^sub>u\<^sub>t constant_1 f \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> \<phi>Fun' f T) P \<close>

text \<open>The following rule is more general than \<open>\<phi>Fun f \<Zcomp> T\<close> as it in addition supports non-closed homomorphism.\<close>

declare [[\<phi>trace_reasoning = 1]]
 
lemma \<phi>Fun'_Separation_Homo\<^sub>I[\<phi>reason 1000]:
  \<open> homo_sep \<psi> \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL TEXT(\<open>Fail to derive the separation homomorphism of\<close> \<psi>)
\<Longrightarrow> closed_homo_sep_disj \<psi> \<and> Prem = (\<lambda>T U xy. True)
    \<or>\<^sub>c\<^sub>u\<^sub>t Prem = (\<lambda>T U xy. Separation_Disj \<psi> (snd xy \<Ztypecolon> U) (fst xy \<Ztypecolon> T))
    \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL TEXT(\<open>Fail to derive the separation homomorphism of\<close> \<psi>)
\<Longrightarrow> Separation_Homo\<^sub>I (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) Prem UNIV (\<lambda>x. x) \<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
            Separation_Disj_def closed_homo_sep_def homo_sep_def closed_homo_sep_disj_def
            homo_sep_mult_def homo_sep_disj_def Orelse_shortcut_def TRACE_FAIL_def
  by (clarsimp; metis (no_types, lifting) fst_conv snd_conv)

lemma Semimodule_Identity_by_function [\<phi>reason 1000]:
  \<open> module_scalar_identity \<psi>
\<Longrightarrow> Semimodule_Identity (\<lambda>a. (\<Zcomp>\<^sub>f) (scalar_mult \<psi> a)) T \<close>
  unfolding Semimodule_Identity_def module_scalar_identity_def scalar_mult_def
  by (rule \<phi>Type_eqI; clarsimp; metis)

lemma Semimodule_Scalar_Assoc_by_function[\<phi>reason 1000]:
  \<open> module_scalar_assoc \<psi> Ds
\<Longrightarrow> Semimodule_Scalar_Assoc (\<lambda>a. (\<Zcomp>\<^sub>f) (scalar_mult \<psi> a)) T Ds \<close>
  unfolding module_scalar_assoc_def Semimodule_Scalar_Assoc_def scalar_mult_def
  by (clarify; rule \<phi>Type_eqI; clarsimp; metis)

lemma Semimodule_LDistr_Homo\<^sub>Z_by_function[\<phi>reason 1000]:
  \<open> module_L_distr \<psi> Ds
\<Longrightarrow> Functionality T Dx
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> Abstract_Domain T D\<^sub>T
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z (\<lambda>a. (\<Zcomp>\<^sub>f) (scalar_mult \<psi> a)) T Ds
                            (\<lambda>s t (x,y). (D\<^sub>T x \<longrightarrow> eq x y \<and> Dx y) \<or> (D\<^sub>T y \<longrightarrow> eq y x \<and> Dx x))
                            (\<lambda>_ _. fst)\<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_def Transformation_def module_L_distr_def Is_Functional_def
            Object_Equiv_def Functionality_def Abstract_Domain_def Action_Tag_def Inhabited_def
            scalar_mult_def
  by clarsimp metis
  

text \<open>The domain of abstract objects constrains to ensure the two middle-level objects
  (namely, the concrete objects of \<open>T\<close> and the abstract objects of \<open>\<psi>\<close>) are identical so that
  we can apply the right distributive law \<open>smult (s + t) a = smult s a * smult t a\<close> of module,
  which requires the group objects \<open>a\<close> at the two sides of \<open>*\<close> to be identical.

  To this requirement, the instantiated domains above is the weakest.
\<close>

lemma \<comment> \<open>The instantiated domains above is the weakest upto using the \<open>module_L_distr \<psi> Ds\<close>,
          i.e., \<open>smult (s + t) a = smult s a * smult t a\<close>, when the \<open>Dx\<close>, \<open>eq\<close>, and \<open>D\<^sub>T\<close> are the weakest. \<close>
  \<open> (\<forall>x. p x \<longleftrightarrow> (\<forall>u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> u = v))
\<Longrightarrow> (\<forall>x y. eq x y \<longleftrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T))
\<Longrightarrow> (D\<^sub>Tx \<longleftrightarrow> (\<exists>u. u \<Turnstile> (x \<Ztypecolon> T))) \<and> (D\<^sub>Ty \<longleftrightarrow> (\<exists>u. u \<Turnstile> (y \<Ztypecolon> T)))
\<Longrightarrow> (\<forall>u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (y \<Ztypecolon> T) \<longrightarrow> u = v) \<longrightarrow> ((D\<^sub>Tx \<longrightarrow> eq x y \<and> p y) \<or> (D\<^sub>Ty \<longrightarrow> eq y x \<and> p x)) \<close>
  unfolding Transformation_def
  by auto metis
  




subsubsection \<open>Configuration\<close>

setup \<open>Context.theory_map (Phi_Type_Algebra.Defining_Phi_Type.add 12 (fn phi => fn thy =>
  let exception Found of term * term
      fun find (X as Const(\<^const_name>\<open>\<phi>Composition\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Fun\<close>, _) $ f) $ T)
            = raise Found (X, Const(\<^const_name>\<open>\<phi>Fun'\<close>, dummyT) $ f $ T)
        | find (A $ B) = (find A; find B)
        | find (Abs (_, _, X)) = find X
        | find _ = ()

      open Pretty
      val _ = List.app (find o Thm.prop_of) (#equations phi)
              handle Found (X,Y) => Phi_Reasoner.warn_pretty thy 0 (fn () =>
                  paragraph (text "We have noticed you are using" @ [brk 1,
                      Context.cases Syntax.pretty_term_global Syntax.pretty_term thy X, brk 1] @
                      text "instead of a more specific \<phi>-type" @ [brk 1,
                      Context.cases Syntax.pretty_term_global Syntax.pretty_term thy Y, str ".", brk 1] @
                      text "We highly recommend the later form which replaces the former totally and\
                           \ have more general automation on separation homomorphism." ))
   in thy
  end))\<close>


subsection \<open>Multiplicative Finite Product\<close>

(*TODO*)
lemma
  \<open> (\<And>x \<in> S. A x \<i>\<m>\<p>\<l>\<i>\<e>\<s> P x)
\<Longrightarrow> finite S
\<Longrightarrow> prod A S \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<forall>x \<in> S. P x)\<close>
  unfolding Action_Tag_def meta_Ball_def Inhabited_def Premise_def
  apply clarsimp
  by (metis Satisfaction_def Zero_expn ex_in_conv prod_zero)
  
  thm comm_monoid_mult_class.prod.remove


section \<open>Structural Connectives\<close>

subsection \<open>List Item \& Empty List\<close>

subsubsection \<open>List Item\<close>

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def List_Item :: \<open>('v, 'a) \<phi> \<Rightarrow> ('v list, 'a) \<phi>\<close>
  where \<open>List_Item T \<equiv> (\<lambda>v. [v]) \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functionality
       and Open_Abstraction_Full
       and Functional_Transformation_Functor
       and Trivial_\<Sigma>


lemma \<comment> \<open>A example for how to represent list of multi-elements\<close>
  \<open> v1 \<Turnstile> (x1 \<Ztypecolon> T1)
\<Longrightarrow> v2 \<Turnstile> (x2 \<Ztypecolon> T2)
\<Longrightarrow> [v1,v2] \<Turnstile> ((x1, x2) \<Ztypecolon> (List_Item T1 \<^emph> List_Item T2))\<close>
  by (simp add: times_list_def,
      rule exI[where x=\<open>[v2]\<close>],
      rule exI[where x=\<open>[v1]\<close>],
      simp)


subsubsection \<open>Empty List\<close>

declare [[\<phi>trace_reasoning = 0]]
  
\<phi>type_def Empty_List :: \<open>('v list, unit) \<phi>\<close>
  where \<open>Empty_List = (\<lambda>x. [] \<Ztypecolon> Itself)\<close>
  deriving Basic
       and Functionality
       and Open_Abstraction_Full
       and Identity_Element



subsection \<open>Empty Type of Free Objects\<close>

(*
declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>None_freeobj :: \<open>('v::one, 'x) \<phi>\<close> ("\<circle>\<^sub>\<x>")
  where \<open> x \<Ztypecolon> \<circle>\<^sub>\<x> \<equiv> 1 \<close>
  deriving Basic
       and \<open> Identity_Element\<^sub>I (x \<Ztypecolon> \<circle>\<^sub>\<x>) True \<close>
       and \<open> Identity_Element\<^sub>E (x \<Ztypecolon> \<circle>\<^sub>\<x>) \<close>
       and Open_Abstraction_Full

declare \<phi>None_freeobj.intro_reasoning[\<phi>reason 1000]
        \<phi>None_freeobj.elim_reasoning[\<phi>reason 1000]
*)
subsubsection \<open>Special Rules\<close>

lemma [\<phi>reason !10]:
  \<open>x \<Ztypecolon> \<circle>\<^sub>\<x> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<circle>\<^sub>\<x> \<s>\<u>\<b>\<j> y. True @action to \<n>\<o>-\<c>\<h>\<a>\<n>\<g>\<e>\<close>
  unfolding Action_Tag_def Transformation_def
  by simp



subsection \<open>Optional\<close>

(*
\<phi>type_def \<phi>Optional :: \<open>('c,'x) \<phi> \<Rightarrow> bool \<Rightarrow> ('c::one,'x) \<phi>\<close> (infix "?\<^sub>\<phi>" 55)
  where \<open> T ?\<^sub>\<phi> C \<equiv> if C then T else \<circle>\<^sub>\<x> \<close>
  deriving Object_Equiv
       and Identity_Element
       and \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Is_Functional (x \<Ztypecolon> T)) \<Longrightarrow> Is_Functional (x \<Ztypecolon> T ?\<^sub>\<phi> C) \<close>
       and \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r y @action to Itself)
          \<Longrightarrow> x \<Ztypecolon> T ?\<^sub>\<phi> C \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. C \<longrightarrow> r y @action to Itself\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C = C'
          \<Longrightarrow> Transformation_Functor (\<lambda>T. T ?\<^sub>\<phi> C) (\<lambda>T. T ?\<^sub>\<phi> C') (\<lambda>a. {a}) (\<lambda>_. UNIV) (\<lambda>r. if C then r else (=)) \<close>
       and \<open> Functional_Transformation_Functor (\<lambda>T. T ?\<^sub>\<phi> C) (\<lambda>T. T ?\<^sub>\<phi> C') (\<lambda>a. {a}) (\<lambda>_. UNIV)
                                    (\<lambda>r. if C then r else (=)) (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C = C')
                                    (\<lambda>P. if C then P else (\<lambda>_. True)) (\<lambda>f. if C then f else (\<lambda>x. x))\<close>


subsubsection \<open>Simplification\<close>

lemma [simp]:
  \<open>x \<Ztypecolon> T ?\<^sub>\<phi> True \<equiv> x \<Ztypecolon> T\<close>
  unfolding atomize_eq BI_eq_iff
  by simp

lemma [simp]:
  \<open>1 \<Ztypecolon> T ?\<^sub>\<phi> False \<equiv> 1\<close>
  unfolding atomize_eq BI_eq_iff
  by simp
*)


subsection \<open>Mapping\<close>

declare [[\<phi>trace_reasoning = 1]]

\<phi>type_def \<phi>Mapping :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> ('av \<Rightarrow> 'bv, 'a \<Rightarrow> 'b) \<phi>\<close> (infixr "\<Rrightarrow>" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>f \<Ztypecolon> T \<Rrightarrow> U \<equiv> g \<Ztypecolon> Itself \<s>\<u>\<b>\<j> g. (\<forall>v x. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> g v \<Turnstile> (f x \<Ztypecolon> U))\<close>

text \<open>Again it is a form requiring satisfaction operator, so our deriver is very limited on this.\<close>

thm \<phi>Mapping.expansion

lemma [\<phi>inhabitance_rule 1000]:
  \<open> (\<And>x. St x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T)
\<Longrightarrow> (\<And>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> Ct x)
\<Longrightarrow> (\<And>x. Ct x \<Longrightarrow> f x \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> Cu x )
\<Longrightarrow> f \<Ztypecolon> T \<Rrightarrow> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<forall>x. St x \<longrightarrow> Ct x \<and> Cu x) \<close>
  unfolding Inhabited_def Action_Tag_def
  apply clarsimp
  apply blast .
  




subsection \<open>Point on a Mapping\<close>

subsubsection \<open>By Key\<close>

thm list_all2_lengthD
  
declare [[ML_print_depth = 1000, \<phi>trace_reasoning = 1]]
declare [[\<phi>trace_reasoning = 0]]
                                                                                  
\<phi>type_def List  :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List T) = (x \<Ztypecolon> T\<heavy_comma> l \<Ztypecolon> List T)\<close>
  deriving Separation_Monoid
       and Trivial_\<Sigma>
       and SE_Trim_Empty

\<phi>type_def List3 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List3 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List3 T) = (x \<Ztypecolon> List T\<heavy_comma> l \<Ztypecolon> List3 T)\<close>
  deriving Separation_Monoid
       and SE_Trim_Empty
       and Trivial_\<Sigma>

(* BOSS:
\<phi>type_def List2 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List2 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List2 T) = (prod (\<lambda>x. x \<Ztypecolon> T) (set x)\<heavy_comma> l \<Ztypecolon> List2 T)\<close>
*)
 
declare [[\<phi>trace_reasoning = 0]]
       
\<phi>type_def rounded_Nat :: \<open>nat \<Rightarrow> (nat,nat) \<phi>\<close>
  where \<open>(x \<Ztypecolon> rounded_Nat m) = (x mod m \<Ztypecolon> Itself)\<close>
  deriving Basic
  

(*
lemma [\<phi>reason 10000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P\<close>
  sorry  *)
 declare [[\<phi>trace_reasoning = 0]]

   
\<phi>type_def \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 75)
  where \<open>\<phi>MapAt k T = (fun_upd 1 k \<Zcomp>\<^sub>f T)\<close>
  deriving Separation_Monoid
       and Open_Abstraction_Full
       and Functionality
       and Trivial_\<Sigma>


(*
TESTING
definition \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 60)
  where \<open>\<phi>MapAt key T x = { 1(key := v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>MapAt_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> key \<^bold>\<rightarrow> T) \<longleftrightarrow> (\<exists>v. p = 1(key := v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>MapAt_def \<phi>Type_def by simp

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> field \<^bold>\<rightarrow> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Conversions\<close>

lemma \<phi>MapAt_\<phi>Prod:
  \<open>k \<^bold>\<rightarrow> (T \<^emph> U) = (k \<^bold>\<rightarrow> T) \<^emph> (k \<^bold>\<rightarrow> U)\<close>
  for T :: \<open>('a::sep_magma_1,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1))
  by (metis fun_1upd_homo_right1)
 
lemma \<phi>MapAt_\<phi>None:
  \<open>k \<^bold>\<rightarrow> \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

(*
lemma \<phi>MapAt_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> k \<^bold>\<rightarrow> T) = (x' \<Ztypecolon> k \<^bold>\<rightarrow> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>MapAt_simp_cong ("(x \<Ztypecolon> k \<^bold>\<rightarrow> T)") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>MapAt_simp_cong} ctxt)
\<close> *)

paragraph \<open>Implication \& Action rules\<close>

lemma \<phi>MapAt_cast:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma (*[\<phi>reason 1000]: TESTING*)
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P\<close>
  using \<phi>MapAt_cast by (simp add: Premise_def)

(*lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .*)

(* TESTING
lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action to (k' \<^bold>\<rightarrow> Z) \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action to Z \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .*)

(*lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> k' \<^bold>\<rightarrow> Z) \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow> U \<w>\<i>\<t>\<h> P @action as Z \<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow> (T \<phi>\<s>\<u>\<b>\<j> P)) = (k \<^bold>\<rightarrow> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)
*)

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> k = k'
\<Longrightarrow> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> 1(k := v) \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> k' \<^bold>\<rightarrow> T \<w>\<i>\<t>\<h> P\<close>
  by (clarsimp simp add: \<phi>expns Transformation_def, blast)

lemma [\<phi>reason 1200]:
  \<open> Is_Functional (x \<Ztypecolon> T)
\<Longrightarrow> Is_Functional (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  by (clarsimp simp add: \<phi>expns Is_Functional_def, blast)

paragraph \<open>Algebraic Properties\<close>

lemma \<phi>MapAt_transformation_functor(*[\<phi>reason 1100]*):
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'
\<Longrightarrow> Transformation_Functor ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k') (\<lambda>x. x) (\<lambda>x. x)\<close>
  unfolding Transformation_Functor_def Premise_def
  by (simp add: \<phi>MapAt_cast)

interpretation \<phi>MapAt: Transformation_Functor_L \<open>(\<^bold>\<rightarrow>) k\<close> \<open>(\<^bold>\<rightarrow>) k'\<close> \<open>(\<lambda>x. x)\<close> \<open>(\<lambda>x. x)\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'\<close>
  by (standard, rule \<phi>MapAt_transformation_functor)

lemma \<phi>MapAt_separation_functor[\<phi>reason 1100]:
  \<open>Separation_Functor ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) T U\<close>
  for T :: \<open>('a::sep_magma_1,'b) \<phi>\<close>
  unfolding Separation_Functor_def \<phi>MapAt_\<phi>Prod ..

lemma \<phi>MapAt_void_functor[\<phi>reason add]:
  \<open>Unit_Functor ((\<^bold>\<rightarrow>) k)\<close>
  unfolding Unit_Functor_def Transformation_def
  by (clarsimp simp add: \<phi>expns; metis fun_1upd1)

interpretation Union_Functor \<open>(\<^bold>\<rightarrow>) k\<close> \<open>(\<^bold>\<rightarrow>) k\<close>
  by (standard; rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

*)

subsubsection \<open>By List of Keys\<close>

(*
definition \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 60)
  where [\<phi>defs, \<phi>expns]: \<open>\<phi>MapAt_L k T = (\<phi>Fun (push_map k) \<Zcomp> T)\<close>

interpretation \<phi>MapAt_L: Transformation_Functor_L \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close> \<open>(\<^bold>\<rightarrow>\<^sub>@) k'\<close> \<open>(\<lambda>x. x)\<close> \<open>(\<lambda>x. x)\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k = k'\<close>
  by (standard, unfold \<phi>MapAt_L_def, \<phi>reason)

lemma \<phi>MapAt_L_separation_functor[\<phi>reason add]:
  \<open>Separation_Functor ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) T U\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_magma_1,'b) \<phi>\<close>
  unfolding \<phi>MapAt_L_def by \<phi>reason

lemma \<phi>MapAt_L_void_functor[\<phi>reason 1100]:
  \<open>Unit_Functor ((\<^bold>\<rightarrow>\<^sub>@) k)\<close>
  unfolding \<phi>MapAt_L_def
  by \<phi>reason *)
      
\<phi>type_def \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 75)
  where \<open>\<phi>MapAt_L k T = (scalar_mult push_map k \<Zcomp>\<^sub>f T)\<close>
  deriving Separation_Monoid
       and Open_Abstraction_Full
       and Functionality
       and Trivial_\<Sigma>
       and Semimodule_Scalar_Assoc
       and Semimodule_Identity

abbreviation \<phi>MapAt_L1 :: \<open>'key \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>#" 75)
  where \<open>\<phi>MapAt_L1 key \<equiv> \<phi>MapAt_L [key]\<close>

abbreviation \<phi>MapAt_Lnil :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>[\<^sub>]" 75)
  where \<open>\<phi>MapAt_Lnil key T \<equiv> \<phi>MapAt_L [key] (\<phi>MapAt [] T)\<close>

paragraph \<open>Simplification\<close>

lemma \<phi>MapAt_L_At:
  \<open>(ks \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) = (ks \<^bold>\<rightarrow> T)\<close>
  by (rule \<phi>Type_eqI; simp add: scalar_mult_def; metis append_self_conv push_map_unit)


paragraph \<open>Implication \& Action Rules\<close>


(* TESTING
lemma [\<phi>reason 1020]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P\<close>
  using \<phi>MapAt_L_cast by (simp add: Premise_def)*)

lemma [\<phi>reason 1017]:
  \<open> \<g>\<u>\<a>\<r>\<d>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> length k < length k'
&&& \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k @ kd = k'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def \<r>Guard_def conjunction_imp Premise_def
  apply clarsimp
  using push_map_push_map by blast

lemma [\<phi>reason 1013]:
  \<open> \<g>\<u>\<a>\<r>\<d>
    \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> length k' < length k
&&& \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k @ kd = k'
\<Longrightarrow> x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def \<r>Guard_def conjunction_imp Premise_def
  by (clarsimp)

(* TESTING
lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U \<w>\<i>\<t>\<h> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def using \<phi>MapAt_L_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow>\<^sub>@ (T \<phi>\<s>\<u>\<b>\<j> P)) = (k \<^bold>\<rightarrow>\<^sub>@ T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)
*)

paragraph \<open>Algebraic Properties\<close>
 

lemma \<phi>MapAt_L_left_seminearring_functor[\<phi>reason 1100]:
  \<open>Semimodule_Scalar_Assoc (\<^bold>\<rightarrow>\<^sub>@) T UNIV\<close>
  unfolding Semimodule_Scalar_Assoc_def
  by (clarsimp simp add: \<phi>MapAt_L_\<phi>MapAt_L times_list_def)

(*
lemma \<phi>MapAt_L_void_functor[\<phi>reason add]:
  \<open>Unit_Functor ((\<^bold>\<rightarrow>\<^sub>@) k)\<close>
  unfolding Unit_Functor_def Transformation_def
  by (clarsimp simp add: \<phi>expns; metis fun_1upd1)

interpretation \<phi>MapAt_L: Union_Functor \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close> \<open>(\<^bold>\<rightarrow>\<^sub>@) k\<close>
  by (standard; rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1000]:
  \<open>Type_Variant_of_the_Same_Type_Operator ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k)\<close>
  unfolding Type_Variant_of_the_Same_Type_Operator_def ..
*)






subsection \<open>Permission Sharing\<close>

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def \<phi>Share :: \<open>rat \<Rightarrow> ('c::share,'a) \<phi> \<Rightarrow> ('c, 'a) \<phi>\<close> (infixr "\<odiv>" 75)
  where \<open>\<phi>Share n T = (scalar_mult share n \<Zcomp>\<^sub>f T \<phi>\<s>\<u>\<b>\<j> 0 < n)\<close>
  deriving Separation_Monoid
       and \<open>Identity_Element\<^sub>E (1 \<Ztypecolon> (T::('c::share_one,'a::one) \<phi>)) \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<Longrightarrow> Identity_Element\<^sub>E (1 \<Ztypecolon> n \<odiv> T)\<close>
       and Functionality
       and Open_Abstraction_Full
       and Trivial_\<Sigma>
       and SE_Trim_Empty
       and Semimodule_Scalar_Assoc
       and Semimodule_Identity

thm \<phi>Share.\<phi>None
thm \<phi>Share.scalar_assoc
thm \<phi>Share.scalar_identity
thm \<phi>Share.Semimodule_Scalar_Assoc


subparagraph \<open>Auxiliary Tag\<close>

(*TODO: rename this to partial which is a syntactic const, \<^term>\<open>partial \<odiv> T\<close>, and translate it during
  the parsing time*)


definition half :: \<open>rat \<Rightarrow> rat\<close> where [iff]: \<open>half x = x\<close>

text \<open>Many read-only applicable rules require only non-zero permissions.
  It is reflected as arbitrary schematic variable in the rule, like
    \<^schematic_prop>\<open> x \<Ztypecolon> ?n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z\<close>.
  As arbitrary schematic variable, the reasoner may by mistake instantiate it to be the total
  permission. It is not the optimal, and it is better to only assign a half of the permission
    and to leave the remain half to be used potentially later.
  For example, if a rule requires twice the same resource,
    \<^schematic_prop>\<open> (x \<Ztypecolon> ?n \<odiv> T) * (x \<Ztypecolon> ?m \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z\<close>.
  The best solution is to assign ?n by a half of the current permission and then assign ?m
    the half of the remaining half.

  Unfortunately, the reasoner can hardly be configured to apply this conservative policy, because
  schematic variables have a semantics of accepting any instantiation and there are many short-cut
  reasoning rule trying to solve greedily a local problem by unification.

  An approach is, if a rule may request a same object by twice, add the tag \<^term>\<open>half\<close> on its
    permission to tell explicitly the reasoner to only assign it a half of the permission.
    \<^schematic_prop>\<open> (x \<Ztypecolon> half ?n \<odiv> T) * (x \<Ztypecolon> half ?m \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Z\<close>.
\<close>

subsubsection \<open>Simplification Rules\<close>

lemma \<phi>Share_share:
  \<open> 0 < n \<and> 0 < m
\<Longrightarrow> Sep_Functional (x \<Ztypecolon> T)
\<Longrightarrow> Sep_Reflexive (x \<Ztypecolon> T)
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) * (x \<Ztypecolon> m \<odiv> T) = (x \<Ztypecolon> (n + m) \<odiv> T) \<close>
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  unfolding BI_eq_iff Sep_Functional_def Sep_Reflexive_def
  apply (clarify; rule; clarsimp)
  using share_sep_left_distrib_0 apply blas
  by (metis share_sep_disj_left share_sep_disj_right share_sep_left_distrib_0

lemma \<phi>Share_\<phi>MapAt[assertion_simps]:
  \<open>n \<odiv> k \<^bold>\<rightarrow> T = k \<^bold>\<rightarrow> n \<odiv> T\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  by (rule \<phi>Type_eqI; clarsimp; rule; clarsimp;
      metis share_fun_updt share_right_one

lemma \<phi>Share_\<phi>MapAt_Lassertion_simps[]:
  \<open>n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T = k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp; rule)
  apply (clarsimp simp add: share_push_map) apply blast
  apply (clarsimp simp add: share_push_map[symmetric]) by blast

lemma \<phi>Share_\<phi>Prod[assertion_simps]:
  \<open>n \<odiv> (T \<^emph> U) = (n \<odiv> T) \<^emph> (n \<odiv> U)\<close>
  for T :: \<open>('a::share_nun_semimodule, 'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp; rule; clarsimp)
  apply (metis share_sep_disj_left share_sep_disj_right share_sep_right_distrib_0)
  using share_sep_right_distrib_0 by blast

lemma \<phi>Share_\<phi>None[simp, assertion_simps]:
  \<open>0 < n \<Longrightarrow> n \<odiv> \<circle> = (\<circle> :: ('a::share_one,unit) \<phi>)\<close>
  by (rule \<phi>Type_eqI; clarsimp)

(*
lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> ?n \<odiv> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action (?Act::?'b::simplification action)\<close>]:
  \<open>x \<Ztypecolon> n \<odiv> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>) @action Act\<close>
  for Act :: \<open>'b::simplification action\<close>
  unfolding Transformation_def Action_Tag_def
  by (simp add: \<phi>expns) *)


paragraph \<open>Implication \& Action Rules\<close>



lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> (m * n) \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> x \<Ztypecolon> n \<odiv> m \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (m * n) \<odiv> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> m \<odiv> T \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow> n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> k \<^bold>\<rightarrow> n \<odiv> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow> T \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<odiv> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> k \<^bold>\<rightarrow>\<^sub>@ T \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (n \<odiv> T) \<^emph> (n \<odiv> U) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> n \<odiv> (T \<^emph> U) \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> (n \<odiv> T) \<^emph> (n \<odiv> U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> (T \<^emph> U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .


paragraph \<open>Action Rules\<close>

lemma [\<phi>reason 1200]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<odiv> U) \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

(* TESTING
lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<odiv> U) \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n' = n
\<Longrightarrow> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<odiv> U) \<w>\<i>\<t>\<h> P @action to (n' \<odiv> Z)\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<odiv> U) \<w>\<i>\<t>\<h> P @action as Z\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation .

lemma [\<phi>reason 1100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> n' = n
\<Longrightarrow> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U) \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> n \<odiv> U) \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> n' \<odiv> Z)\<close>
  unfolding Action_Tag_def using \<phi>Share_transformation . *)


paragraph \<open>Simplifications\<close>

lemma [simp]:
  \<open>(n \<odiv> ExTyp T) = (\<exists>\<phi> c. n \<odiv> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(n \<odiv> (T \<phi>\<s>\<u>\<b>\<j> P)) = (n \<odiv> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

(*
lemma \<phi>Share_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) = (x' \<Ztypecolon> n \<odiv> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Share_simp_cong ("x \<Ztypecolon> n \<odiv> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>Share_simp_cong} ctxt)
\<close>*)


subparagraph \<open>Permission\<close>

lemma share_split_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> (x \<Ztypecolon> (n+m) \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> n \<odiv> T) * (x \<Ztypecolon> m \<odiv> T)\<close>
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share Premise_def)

lemma share_merge_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> (x \<Ztypecolon> n \<odiv> T) * (x \<Ztypecolon> m \<odiv> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> (n+m) \<odiv> T)\<close>
  for T :: \<open>('a::share_nun_semimodule,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share Premise_def)

paragraph \<open>Algebraic Properties\<close>

lemma \<phi>Share_left_seminearring_functor[\<phi>reason add]:
  \<open>Semimodule_Scalar_Assoc (\<odiv>) T {0<..1}\<close>
  unfolding Semimodule_Scalar_Assoc_def
  by clarsimp

(*
lemma \<phi>Share_void_functor[\<phi>reason add]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n
\<Longrightarrow> Unit_Functor ((\<odiv>) n :: ('a::share_one, 'b) \<phi> \<Rightarrow> ('a, 'b) \<phi>)\<close>
  unfolding Unit_Functor_def Transformation_def Premise_def
  by (clarsimp simp add: \<phi>Share_expn, insert share_right_one, blast)*)
 
interpretation \<phi>Share: Functional_Transformation_Functor
    \<open>(\<odiv>) n\<close> \<open>(\<odiv>) n'\<close> \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> n = n'\<close> \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard, clarsimp simp add: Transformation_Functor_def Transformation_def ExSet_expn Premise_def
      Subjection_expn \<phi>Share_expn; blast)

interpretation \<phi>Share: Sep_Homo_Type_Functor_L
    \<open>(\<odiv>) n :: ('a::share_nun_semimodule, 'b) \<phi> \<Rightarrow> _\<close> \<open>(\<odiv>) n\<close> \<open>(\<odiv>) n\<close> True
  by ((standard; rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp),
      (insert share_sep_right_distrib_0, blast)[1],
      metis share_sep_disj_left share_sep_disj_right share_sep_right_distrib_0)

lemma [\<phi>reason add]:
  \<open> Semimodule_LDistr_Homo\<^sub>Z ((\<odiv>) :: _ \<Rightarrow> ('a::share_nun_semimodule,'b) \<phi> \<Rightarrow> _)
        {n. 0 < n}
        (\<lambda>T x. \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> T) \<and> Object_Equiv T eq \<and> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd x) (fst x)))
        (\<lambda>_ _. fst) \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_def \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: Transformation_def \<phi>Prod_expn Object_Equiv_def \<phi>Share_expn Premise_def;
      metis share_sep_left_distrib_0)

lemma [\<phi>reason add]:
  \<open> Semimodule_LDistr_Homo\<^sub>Z_rev ((\<odiv>) :: _ \<Rightarrow> ('a::share_nun_semimodule,'b) \<phi> \<Rightarrow> _)
        {n. 0 < n}
        (\<lambda>T x. \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> T) \<and> Object_Equiv T eq \<and> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd x) (fst x)))
        (\<lambda>_ _. fst) \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_rev_def \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: Transformation_def \<phi>Prod_expn Object_Equiv_def \<phi>Share_expn Premise_def;
      metis add.commute share_sep_left_distrib_0)

lemma [\<phi>reason add]:
  \<open> Semimodule_LDistr_Homo\<^sub>U ((\<odiv>) :: _ \<Rightarrow> ('a::share_nun_semimodule,'b) \<phi> \<Rightarrow> _)
        {n. 0 < n}
        (\<lambda>T x. \<phi>Sep_Disj_Inj (x \<Ztypecolon> T))
        (\<lambda>_ _ x. (x,x)) \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>U_def \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: Transformation_def \<phi>Prod_expn Object_Equiv_def \<phi>Share_expn;
      metis share_sep_disj_left share_sep_disj_right share_sep_left_distrib_0)











(* subsection \<open>Down Lifting\<close> (*depreciated*)

definition DownLift :: "('a, 'b) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<phi>" (infixl "<down-lift>" 80)
  where "DownLift N g x = (g x \<Ztypecolon> N)"

lemma DownLift_expn[simp]: " p \<in> (x \<Ztypecolon> N <down-lift> g) \<longleftrightarrow> p \<in> (g x \<Ztypecolon> N) "
  unfolding DownLift_def \<phi>Type_def by simp

lemma [elim!,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> N <down-lift> g) \<Longrightarrow> (Inhabited (g x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

(* lemma [\<phi>cast_overload E]: " x \<Ztypecolon> N <down-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g x \<Ztypecolon> N" unfolding Transformation_def by simp *)
lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> g x = x' \<Longrightarrow> x \<Ztypecolon> N <down-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> N" unfolding Transformation_def by (simp add: \<phi>expns)

(* lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> (g y = x) \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <down-lift> g"
  unfolding Intro_def Transformation_def by (simp add: \<phi>expns) blast
lemma [\<phi>reason, \<phi>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <down-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g y \<Ztypecolon> M"
  unfolding Dest_def Transformation_def by (simp add: \<phi>expns) *)

lemma [\<phi>reason]: " x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y1 \<Ztypecolon> M \<w>\<i>\<t>\<h> P \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y1 = g y  \<Longrightarrow> x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <down-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns)
lemma "\<down>lift_\<phi>app": "\<p>\<a>\<r>\<a>\<m> g \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> g y = x \<Longrightarrow> x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> N <down-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns)



subsection \<open>Up Lifting\<close> (*depreciated*)

definition UpLift :: "('a, 'c) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<phi>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> p \<in> (y \<Ztypecolon> N))}"

lemma UpLift_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <up-lift> f) \<longleftrightarrow> (\<exists>y. (f y = x) \<and> p \<in> (y \<Ztypecolon> N))"
  unfolding UpLift_def \<phi>Type_def by auto

lemma UpLift_inhabited[elim,\<phi>inhabitance_rule]:
  "Inhabited (x \<Ztypecolon> N <up-lift> f) \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> Inhabited (y \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma "\<up>lift_\<phi>app":
  "\<p>\<a>\<r>\<a>\<m> g \<Longrightarrow> \<p>\<a>\<r>\<a>\<m> y \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <up-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns) blast
(* lemma [\<phi>overload D]: "x \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists> \<Ztypecolon> M) "
  unfolding Transformation_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason]: "\<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x \<Longrightarrow> \<i>\<n>\<^bold>t\<^bold>r\<^bold>o x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M <up-lift> g"
  unfolding Intro_def Transformation_def by (simp add: \<phi>expns) blast *)

lemma [\<phi>reason 130]:
  "x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> M' \<w>\<i>\<t>\<h> P \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y = g x' \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> M' <up-lift> g"
  unfolding Transformation_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 20]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> N \<w>\<i>\<t>\<h> P x)
\<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> N \<w>\<i>\<t>\<h> (\<exists>x. y = g x \<and> P x)"
  unfolding Transformation_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 150]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' x \<Ztypecolon> M' x \<w>\<i>\<t>\<h> P x)
    \<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>*x. y' x \<Ztypecolon> M' x) \<w>\<i>\<t>\<h> (\<exists>x. y = g x \<and> P x)"
  unfolding Transformation_def by (simp add: \<phi>expns) blast

(* lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <up-lift> g \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<exists>* x. (x \<Ztypecolon> M) \<and>\<^sup>s g x = y)"
  unfolding Dest_def Transformation_def by (simp add: \<phi>expns) blast *)

lemma "x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> N <up-lift> f" unfolding Transformation_def by (simp add: \<phi>expns) blast
lemma "x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> N <up-lift> f" unfolding Transformation_def by (simp add: \<phi>expns) blast

(* lemma "\<phi>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<phi>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<phi>Equal_def by (auto 0 6) *)
*)

section \<open>Semantics Related\<close>

subsection \<open>Value\<close>

subsubsection \<open>Syntax to fetch the latest n-th Val\<close>

(*
setup \<open>let open Ast Phi_Syntax
  fun strip_constrain (Const ("_constrain", _) $ x $ _) = strip_constrain x
    | strip_constrain (Const ("_type_constraint_", _) $ x) = strip_constrain x
    | strip_constrain x = x

  fun name_of_Val (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ v $ _ ))
        = SOME v
    | name_of_Val _ = NONE

  fun get_val ctxt ind =
    let
      val values = Thm.prop_of (Phi_Envir.the_construction ctxt)
                  |> dest_CurrentConstruction |> #4
                  |> strip_separations |> rev
                  |> map_filter name_of_Val
    in if ind < length values
       then List.nth (values, ind)
       else error ("Referring a value that does not exists.")
    end

  fun has_get_val (Const (\<^const_name>\<open>\<phi>__get_val\<close>, _)) = true
    | has_get_val (A $ B) = has_get_val A orelse has_get_val B
    | has_get_val (Abs (_,_,X)) = has_get_val X
    | has_get_val _ = false
  fun map_get_val ctxt (Const (\<^const_name>\<open>\<phi>__get_val\<close>, _) $ X)
        = get_val ctxt (Value.parse_nat (Term.term_name (strip_constrain X)))
    | map_get_val ctxt (A $ B) = map_get_val ctxt A $ map_get_val ctxt B
    | map_get_val ctxt (Abs (name,ty,X)) = Abs (name,ty, map_get_val ctxt X)
    | map_get_val ctxt x = x
 in Context.theory_map (Syntax_Phases.term_check ~10 "\<phi>valiable" (fn ctxt =>
      map (fn x => if has_get_val x then map_get_val ctxt x else x)))
end\<close> *)


subsection \<open>Semantic Type Annotation\<close>

paragraph \<open>Annotation for Single One\<close>
(* TODO!
definition Of_Type :: \<open>(VAL,'a) \<phi> \<Rightarrow> TY \<Rightarrow> (VAL,'a) \<phi>\<close> (infix "<of-type>" 23)
  where \<open>(T <of-type> TY) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> Well_Type TY)\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-type> TY) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> p \<in> Well_Type TY\<close>
  unfolding Of_Type_def \<phi>Type_def by (simp add: \<phi>expns)

lemma [elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-type> TY) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> T <of-type> TY) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> T <of-type> TY) TY\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

lemma [\<phi>reason 100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U <of-type> TY \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def \<phi>SemType_def by (simp add: \<phi>expns) blas


paragraph \<open>Annotation for a List\<close>

definition Of_Types :: \<open>(VAL list,'a) \<phi> \<Rightarrow> TY list \<Rightarrow> (VAL list,'a) \<phi>\<close> (infix "<of-types>" 23)
  where \<open>(T <of-types> TYs) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> {p. list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs})\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-types> TYs) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs\<close>
  unfolding Of_Types_def \<phi>Type_def by (simp add: \<phi>expns)

lemma [elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-types> TYs) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> T <of-types> TYs) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast
*)



subsection \<open>Morphism of Separation Homomorphism\<close>

declare [[\<phi>trace_reasoning = 3]]

\<phi>type_def \<phi>sep_homo :: \<open>('a::sep_magma \<Rightarrow> 'c::sep_magma) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close>
  where \<open>\<phi>sep_homo \<psi> T = (\<phi>Fun \<psi> \<Zcomp> T \<phi>\<s>\<u>\<b>\<j> homo_sep \<psi>)\<close>
  deriving Implication
       (*and Is_Functional
       and Open_Abstraction_Full*)

lemma [\<phi>reason add]:
  \<open> Object_Sep_Homo\<^sub>I (\<phi>sep_homo \<psi>) {(y,x). \<psi> x ## \<psi> y \<longrightarrow> x ## y} \<close>
  unfolding Object_Sep_Homo\<^sub>I_def Transformation_def
  by (clarsimp simp add: homo_sep_def homo_sep_mult_def homo_sep_disj_def)

lemma \<phi>Composition_Separation_Homo\<^sub>I'[\<phi>reason 1200]:
  \<open> Separation_Homo\<^sub>I ((\<Zcomp>) (\<phi>sep_homo \<psi>)) ((\<Zcomp>) (\<phi>sep_homo \<psi>)) ((\<Zcomp>) (\<phi>sep_homo \<psi>))
                     (\<lambda>T U xy. Separation_Disj \<psi> (snd xy \<Ztypecolon> U) (fst xy \<Ztypecolon> T))
                     UNIV (\<lambda>x. x)\<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
            Separation_Disj_def
  by (clarsimp; metis homo_sep_def homo_sep_mult_def)
  


lemma \<phi>sep_homo_Prod:
  \<open> (\<phi>sep_homo \<psi> \<Zcomp> (T \<^emph> U)) = (\<phi>sep_homo \<psi> \<Zcomp> T) \<^emph> (\<phi>sep_homo \<psi> \<Zcomp> U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add:; rule; clarsimp)
  using homo_sep.axioms(1) homo_sep.axioms(2) homo_sep_disj_def homo_sep_mult_def apply blast


  

lemma
  \<open> (x \<Ztypecolon> \<phi>sep_homo_morph \<psi>) * (y \<Ztypecolon> \<phi>sep_homo_morph \<psi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> \<phi>sep_homo_morph \<psi> \<w>\<i>\<t>\<h> x ## y
\<Longrightarrow> x ## y\<close>
  unfolding Transformation_def
  apply (clarsimp simp add: homo_sep_def)

lemma [\<phi>reason add]:
  \<open> Object_Sep_Homo\<^sub>E (\<phi>sep_homo_morph \<psi>) \<close>
  unfolding Object_Sep_Homo\<^sub>E_def Transformation_def
  by (clarsimp simp add: homo_sep_def homo_sep_mult_def homo_sep_disj_def)

term \<open>Object_Equiv (\<phi>sep_homo_morph \<psi>) (\<lambda>x y. \<psi> x = \<psi> y)\<close>

\<phi>type_def \<phi>sep_homo :: \<open>('a::sep_magma \<Rightarrow> 'b::sep_magma) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi>sep_homo \<psi> T = (\<lambda>x. x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T \<s>\<u>\<b>\<j> homo_sep \<psi>)\<close>
  deriving (*Basic
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>sep_homo \<psi> T) eq \<close>
       and \<open>Object_Equiv (\<phi>sep_homo T \<circle>) (\<lambda>_ _. True)\<close>
       and Functional_Transformation_Functor
       and*) Separation_Homo\<^sub>E

thm \<phi>sep_homo.unfold

term \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>sep_homo \<psi> T) eq \<close>
term \<open>Object_Equiv (\<phi>sep_homo T \<circle>) (\<lambda>_ _. True)\<close>



section \<open>Permission \& Share\<close>

subsection \<open>Share \& Option\<close>

subsubsection \<open>Definition of Properties\<close>

definition \<phi>Sep_Disj :: \<open>('a::sep_magma,'b1) \<phi> \<Rightarrow> ('a,'b2) \<phi> \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj T U \<longleftrightarrow> (\<forall>x y u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (y \<Ztypecolon> U) \<longrightarrow> (\<exists>u' v'. u' \<Turnstile> (x \<Ztypecolon> T) \<and> v' \<Turnstile> (y \<Ztypecolon> U) \<and> u' ## v'))\<close>

definition \<phi>Sep_Disj_Inj :: \<open>'a::share_nun_semimodule set \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj_Inj S \<longleftrightarrow> (\<forall>u v. u \<Turnstile> S \<and> v \<Turnstile> S \<and> u ## v \<longrightarrow> u = v) \<and> (\<forall>u. u \<Turnstile> S \<longrightarrow> u ## u)\<close>

subsubsection \<open>The \<phi>-Type of Separation Homomorphism\<close>





subsubsection \<open>Insertion Functor\<close>

declare share_orthogonal_homo_pointwise[\<phi>reason 1200]
        share_orthogonal_homo_to_share[\<phi>reason 1200]

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def \<phi>insertion :: \<open>('a::sep_monoid \<Rightarrow> 'b::sep_monoid) \<Rightarrow> 'a set \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi>insertion \<psi> D T = (\<lambda>x. x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T \<s>\<u>\<b>\<j> sep_orthogonal_monoid \<psi> D)\<close>
  deriving Basic
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>insertion \<psi> D T) eq\<close>
       and Object_Equiv\<^sub>O
       (*and Transformation_Functor*)
       

term \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<phi>insertion \<psi> D T) eq\<close>

abbreviation (in sep_orthogonal_monoid) \<open>\<phi> \<equiv> \<phi>insertion \<psi> D\<close>

lemma (in sep_orthogonal_monoid) [\<phi>expns]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<Turnstile> (x \<Ztypecolon> T))\<close>
  by (simp add: sep_orthogonal_monoid_axioms)

paragraph \<open>Implication\<close>
(*
lemma \<phi>insertion_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<phi>insertion \<psi> D T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>insertion \<psi> D U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp; blast) *)

paragraph \<open>Action\<close>

paragraph \<open>Simplification\<close>
(*
lemma [simp]:
  \<open>(\<phi>insertion \<psi> D (ExTyp T)) = (\<exists>\<phi> c. \<phi>insertion \<psi> D (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi>insertion \<psi> D (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<phi>insertion \<psi> D T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)
*)

(*
lemma \<phi>insertion_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi>insertion \<psi> T) = (x' \<Ztypecolon> \<phi>insertion \<psi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>insertion_simp_cong ("x \<Ztypecolon> \<phi>insertion \<psi> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>insertion_simp_cong} ctxt)
\<close>
*)

lemma \<phi>insertion_Prod:
  \<open> \<phi>Sep_Disj U T
\<Longrightarrow> \<phi>insertion f D (T \<^emph> U) = (\<phi>insertion f D T) \<^emph> (\<phi>insertion f D U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>Sep_Disj_def; rule; clarsimp)
  apply (metis homo_sep_def homo_sep_disj_def homo_sep_mult_def sep_orthogonal_1_def sep_orthogonal_def sep_orthogonal_monoid_def)
  
  



lemma \<phi>insertion_\<phi>None:
  assumes prem: \<open>sep_orthogonal_monoid \<psi> D\<close>
  shows \<open>\<phi>insertion \<psi> D \<circle> = \<circle>\<close>
proof -
  interpret sep_orthogonal_monoid \<psi> using prem .
  show \<open>\<phi> \<circle> = \<circle>\<close>
    by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns sep_orthogonal_monoid_axioms)
qed

(* lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> \<phi>insertion ?\<psi> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P @action (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> \<phi>insertion \<psi> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> @action Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Transformation_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  using inj_at_1_def share_orthogonal_homo'.axioms(5) by blast *)

lemma \<phi>insertion_MapAt:
  \<open>\<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow> T) = (k \<^bold>\<rightarrow> \<phi>insertion f D T)\<close>
proof (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>MapAt_def
            sep_orthogonal_monoid_pointwise_eq; rule; clarsimp)
  fix x :: 'a and va :: 'd
  assume \<open>sep_orthogonal_monoid f D\<close>
  then interpret sep_orthogonal_monoid f .
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> 1(k := va) = 1(k := v) \<and> (\<exists>va. v = f va \<and> va \<in> (x \<Ztypecolon> T))\<close> by fastforce
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. 1(k := f va) = f \<circ> v \<and> (\<exists>va. v = 1(k := va) \<and> va \<in> (x \<Ztypecolon> T))\<close>
    by (metis \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> 1(k := va) = 1(k := v) \<and> (\<exists>va. v = f va \<and> va \<in> (x \<Ztypecolon> T))\<close> comp_def fun_upd_same)
qed

lemma \<phi>insertion_MapAt_L:
  \<open>\<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow>\<^sub>@ T) = (k \<^bold>\<rightarrow>\<^sub>@ \<phi>insertion ((o) f) (pointwise_set D) T)\<close>
proof (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns
            sep_orthogonal_monoid_pointwise_eq; rule; clarsimp)
  fix x :: 'a and va :: \<open>'b list \<Rightarrow> 'd\<close>
  assume \<open>sep_orthogonal_monoid f D\<close>
  then interpret sep_orthogonal_monoid f .
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. f \<circ> k \<tribullet>\<^sub>m va = k \<tribullet>\<^sub>m v \<and> (\<exists>va. v = f \<circ> va \<and> va \<in> (x \<Ztypecolon> T))\<close>
    using homo_one_axioms push_map_homo by blast
  show \<open>va \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<exists>v. k \<tribullet>\<^sub>m (f \<circ> va) = f \<circ> v \<and> (\<exists>va. v = k \<tribullet>\<^sub>m va \<and> va \<in> (x \<Ztypecolon> T))\<close>
    by (metis homo_one_axioms push_map_homo)
qed    


lemma \<phi>insertion_Prod_imply:
  \<open>x \<Ztypecolon> \<phi>insertion f D (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<phi>insertion f D T) \<^emph> (\<phi>insertion f D U)\<close>
  unfolding Transformation_def
  apply (cases x; clarsimp simp add: \<phi>expns)
  by (metis homo_sep_def homo_sep_disj_def homo_sep_mult_def sep_orthogonal.axioms(1) sep_orthogonal_1.axioms sep_orthogonal_monoid.axioms share_orthogonal_homo.axioms(1)


thm share_orthogonal_homo.axioms(1)



subsubsection \<open>\<phi>-Some\<close>



abbreviation \<phi>Share_Some ("\<fish_eye> _" [91] 90)
  where \<open>\<phi>Share_Some T \<equiv> \<phi>insertion to_share UNIV (\<phi>Some T)\<close>

abbreviation \<phi>Share_Some_L ("\<fish_eye>\<^sub>L _" [91] 90)
  where \<open>\<phi>Share_Some_L T \<equiv> [] \<^bold>\<rightarrow> \<phi>insertion to_share UNIV (\<phi>Some T)\<close>

\<phi>adhoc_overloading \<phi>coercion \<phi>Some \<phi>Share_Some \<phi>Share_Some_L



lemma \<phi>Some_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Some T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> \<phi>Some T) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>Some_expn)


paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>Some_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 1070]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (\<black_circle> Z) \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

(* TODO:: fix me!!!
lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P @action to Itself
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Some x' \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P @action to Itself \<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns) *)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z) \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> \<black_circle> Z) \<close>
  unfolding Action_Tag_def using \<phi>Some_cast .


lemma [simp]:
  \<open>(\<black_circle> ExTyp T) = (\<exists>\<phi> c. \<black_circle> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<black_circle> (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<black_circle> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

(*lemma \<phi>Some_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<black_circle> T) = (x' \<Ztypecolon> \<black_circle> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Some_simp_cong ("x \<Ztypecolon> \<black_circle> T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>Some_simp_cong} ctxt)
\<close>*)

lemma [\<phi>reason 1200]:
  \<open> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> Some v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v' \<Ztypecolon> \<black_circle> T \<w>\<i>\<t>\<h> P\<close>
  by (clarsimp simp add: \<phi>expns Transformation_def)

lemma [\<phi>reason 1200]:
  \<open> Is_Functional (x \<Ztypecolon> T)
\<Longrightarrow> Is_Functional (x \<Ztypecolon> \<black_circle> T)\<close>
  by (clarsimp simp add: \<phi>expns Is_Functional_def)

paragraph \<open>Algebraic Properties\<close>

interpretation \<phi>Some: Functional_Transformation_Functor \<phi>Some \<phi>Some
      \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> True \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard, clarsimp simp add: Transformation_Functor_def Transformation_def ExSet_expn
      Subjection_expn \<phi>Some_expn; blast)

interpretation \<phi>Some: Sep_Homo_Type_Functor_L \<phi>Some \<phi>Some \<phi>Some True
  by (standard, rule \<phi>Type_eqI, clarsimp simp add: \<phi>Prod_expn \<phi>Some_expn, force)


subsubsection \<open>\<phi>Sep_Disj\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj X Y
\<Longrightarrow> \<phi>Sep_Disj X (m \<odiv> Y)\<close>
  for X :: \<open>('a::share_sep_disj,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj Y X
\<Longrightarrow> \<phi>Sep_Disj (m \<odiv> Y) X\<close>
  for X :: \<open>('a::share_sep_disj,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj X \<phi>None\<close>
  for X :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj \<phi>None X\<close>
  for X :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k1 \<noteq> k2
||| \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>Sep_Disj (k1 \<^bold>\<rightarrow> T) (k2 \<^bold>\<rightarrow> U)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def atomize_Branch
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)+

lemma [\<phi>reason 1200]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k1 \<noteq> k2
||| \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>Sep_Disj (k1 \<^bold>\<rightarrow>\<^sub># T) (k2 \<^bold>\<rightarrow>\<^sub># U)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def atomize_Branch
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def push_map_def)+


lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj X A
\<Longrightarrow> \<phi>Sep_Disj X B
\<Longrightarrow> \<phi>Sep_Disj X (A \<^emph> B) \<close>
  for X :: \<open>('a::sep_disj_distrib, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)

lemma [\<phi>reason 1300]:
  \<open> \<phi>Sep_Disj X Z
\<Longrightarrow> \<phi>Sep_Disj Y Z
\<Longrightarrow> \<phi>Sep_Disj (X \<^emph> Y) Z \<close>
  for X :: \<open>('a::sep_disj_distrib, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)


subsubsection \<open>\<phi>Sep_Disj_Inj\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> n \<odiv> T)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Inj_\<phi>MapAt[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Inj_\<phi>MapAt_L[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: \<phi>expns)
  using push_map_sep_disj by blast

lemma \<phi>Sep_Disj_Inj_Prod[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (y \<Ztypecolon> U)
\<Longrightarrow> \<phi>Sep_Disj_Inj ((x,y) \<Ztypecolon> T \<^emph> U)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  apply (clarsimp simp add: )
  by (metis sep_refl_mult_I sep_disj_multD1 sep_disj_multD2)

lemma [\<phi>reason 1190]:
  \<open> \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (snd x \<Ztypecolon> U)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> T \<^emph> U)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (cases x; clarsimp simp add: \<phi>expns; metis sep_refl_mult_I sep_disj_multD1 sep_disj_multD2)


lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion f D T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow> T)) \<close>
  by (subst \<phi>insertion_MapAt; rule \<phi>Sep_Disj_Inj_\<phi>MapAt)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion ((o) f) (pointwise_set D) T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion ((o) f) (pointwise_set D) (k \<^bold>\<rightarrow>\<^sub>@ T)) \<close>
  by (subst \<phi>insertion_MapAt_L; rule \<phi>Sep_Disj_Inj_\<phi>MapAt_L)

lemma [\<phi>reason 1190]:
  \<open> \<phi>Sep_Disj_Inj (fst x \<Ztypecolon> \<phi>insertion f D T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (snd x \<Ztypecolon> \<phi>insertion f D U)
\<Longrightarrow> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion f D (T \<^emph> U)) \<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (cases x; simp; smt (verit) Transformation_def \<phi>Sep_Disj_Inj_Prod \<phi>Sep_Disj_Inj_def \<phi>insertion_Prod_imply)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion f D T)
\<Longrightarrow> \<phi>Sep_Disj_Inj (y \<Ztypecolon> \<phi>insertion f D U)
\<Longrightarrow> \<phi>Sep_Disj_Inj ((x,y) \<Ztypecolon> \<phi>insertion f D (T \<^emph> U)) \<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (smt (verit) Transformation_def \<phi>Sep_Disj_Inj_Prod \<phi>Sep_Disj_Inj_def \<phi>insertion_Prod_imply)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion to_share D (\<phi>Some T))\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>insertion to_share D \<phi>None)\<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Inj (x \<Ztypecolon> \<phi>None :: 'a::share_semimodule set) \<close>
  unfolding \<phi>Sep_Disj_Inj_def
  by (clarsimp simp add: \<phi>expns)


subsection \<open>Agreement\<close>

definition Agreement :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T agree option, 'x) \<phi>\<close>
  where \<open>Agreement T x = { Some (agree v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma Agreement_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Agreement T) \<longleftrightarrow> (\<exists>v. p = Some (agree v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Agreement_def by simp

lemma Agreement_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> Agreement T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C
\<Longrightarrow> Inhabited (x \<Ztypecolon> Agreement T) \<longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: Agreement_expns)

lemma Agreement_times:
  \<open>(w \<Ztypecolon> Agreement W) * (x \<Ztypecolon> Agreement T) = ((w,x) \<Ztypecolon> Agreement (W \<inter>\<^sub>\<phi> T))\<close>
  unfolding set_eq_iff
  apply (clarsimp simp add: \<phi>expns; rule; clarsimp)
  subgoal for v
    by (rule exI[where x=\<open>Some (agree v)\<close>]; rule exI[where x=\<open>Some (agree v)\<close>]; simp) .

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>Agreement (T \<phi>\<s>\<u>\<b>\<j> P) = (Agreement T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>Agreement (ExTyp T) = (\<exists>\<phi>c. Agreement (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

paragraph \<open>Rule\<close>

lemma Agreement_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma Agreement_dup[
  \<phi>reason 1200 for \<open>?x \<Ztypecolon> Agreement ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?U \<w>\<i>\<t>\<h> ?P @action action_dup\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>?x \<Ztypecolon> Agreement ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<w>\<i>\<t>\<h> ?P\<close>
]:
  \<open> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) @action action_dup\<close>
  unfolding Transformation_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for v by (rule exI[where x=\<open>Some (agree v)\<close>]; rule exI[where x=\<open>Some (agree v)\<close>]; simp) .

lemma Agreement_shrink[
  \<phi>reason 1200 for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?U \<w>\<i>\<t>\<h> ?P @action action_shrink\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x \<Ztypecolon> Agreement ?T \<w>\<i>\<t>\<h> ?P\<close>
]:
  \<open> (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Agreement T @action action_shrink \<close>
  unfolding Transformation_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)


lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (Agreement Z)\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action as Z\<close>
  unfolding Action_Tag_def using Agreement_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Agreement T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Agreement U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Agreement Z)\<close>
  unfolding Action_Tag_def using Agreement_cast .


subsection \<open>Nosep\<close>

definition Nosep :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T nosep, 'x) \<phi>\<close>
  where \<open>Nosep T x = nosep ` (x \<Ztypecolon> T)\<close>

term \<open>\<lambda>T. \<fish_eye> Nosep T\<close>

\<phi>adhoc_overloading \<phi>coercion \<open>\<lambda>T. \<black_circle> Nosep T\<close> \<open>\<lambda>T. \<fish_eye> Nosep T\<close> (* \<open>\<lambda>T. \<fish_eye>\<^sub>L Nosep T\<close> *)

(*TODO: give a configure flag to control this sugar*)
translations
  "\<coercion> T" <= "\<fish_eye> CONST Nosep T"

lemma Nosep_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Nosep T) \<longleftrightarrow> (\<exists>v. p = nosep v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Nosep_def by blast

lemma Nosep_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> Nosep T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (x \<Ztypecolon> T) \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> Inhabited (x \<Ztypecolon> Nosep T) \<longrightarrow> C @action \<A>EIF\<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp add: Nosep_expns)


paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>Nosep (T \<phi>\<s>\<u>\<b>\<j> P) = (Nosep T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>Nosep (ExTyp T) = (\<exists>\<phi>c. Nosep (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)


paragraph \<open>Rule\<close>

lemma Nosep_cast[\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (Nosep Z)\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as Z
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P @action as Z\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Nosep U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Nosep Z)\<close>
  unfolding Action_Tag_def using Nosep_cast .

lemma [\<phi>reason 1200 for \<open>_ \<Ztypecolon> Nosep _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Itself \<w>\<i>\<t>\<h> _\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Nosep T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> nosep y \<Ztypecolon> Itself \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def 
  by (clarsimp simp add: Nosep_expns Itself_expn)


section \<open>Specifc Structures\<close>

subsection \<open>Potentially Uninitialized Structure\<close>

datatype 'V uninit = initialized 'V | uninitialized

instantiation uninit :: (nonsepable_semigroup) nonsepable_semigroup begin
definition \<open>sep_disj_uninit (x::'a uninit) (y::'a uninit) \<longleftrightarrow> False\<close>
instance apply standard unfolding sep_disj_uninit_def by simp_all
end

paragraph \<open>Definition\<close>

text \<open>\<phi>MayInit T relates a value with T if the value is initialized; or if not, it relates the zero
  value of that type with T.\<close>

definition \<phi>MayInit :: \<open>TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (VAL uninit, 'x) \<phi>\<close>
  where \<open>\<phi>MayInit TY T x = ({uninitialized} \<s>\<u>\<b>\<j> (\<exists>z. Zero TY = Some z \<and> z \<in> (x \<Ztypecolon> T))) + initialized ` (x \<Ztypecolon> T <of-type> TY)\<close>

(* abbreviation \<phi>Share_Some_Init ("\<fish_eye>\<lbrakk>_\<rbrakk> _" [0, 91] 90)
  where \<open>\<phi>Share_Some_Init TY T \<equiv> \<fish_eye> \<phi>MayInit TY T\<close> *)

lemma \<phi>MayInit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>MayInit TY T) \<longleftrightarrow> (p = uninitialized \<and> (\<exists>z. Zero TY = Some z \<and> z \<in> (x \<Ztypecolon> T)) \<or> (\<exists>v. p = initialized v \<and> v \<in> (x \<Ztypecolon> T <of-type> TY)))\<close>
  unfolding \<phi>Type_def \<phi>MayInit_def by (simp add: \<phi>expns, blast)

(*
lemma \<phi>MayInit_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>MayInit TY T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast) *)

paragraph \<open>Conversions\<close>

lemma [simp]:
  \<open>\<phi>MayInit TY (T \<phi>\<s>\<u>\<b>\<j> P) = (\<phi>MayInit TY T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>\<phi>MayInit TY (ExTyp T) = (\<exists>\<phi> c. \<phi>MayInit TY (T c))\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

paragraph \<open>Rules\<close>

(*TODO: improve this*)
lemma \<phi>MayInit_cast[\<phi>reason for \<open>?x \<Ztypecolon> \<phi>MayInit ?TY ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<phi>MayInit ?TY' ?U \<w>\<i>\<t>\<h> ?P\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<w>\<i>\<t>\<h> P @action \<A>_structural Act\<close>
  unfolding Action_Tag_def using \<phi>MayInit_cast .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> \<phi>MayInit TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>MayInit TY U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z\<close>
  unfolding Action_Tag_def Transformation_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)


definition \<phi>Uninit :: \<open>('v uninit, unit) \<phi>\<close>
  where \<open>\<phi>Uninit x = {uninitialized}\<close>

lemma \<phi>Uninit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Uninit) \<longleftrightarrow> p = uninitialized\<close>
  unfolding \<phi>Type_def \<phi>Uninit_def by simp

(* TODO
lemma \<phi>Uninit_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Uninit) \<Longrightarrow> C \<Longrightarrow> C\<close> . *)


section \<open>Misc.\<close>

subsection \<open>Forward Simulation\<close>

definition \<phi>F_simulation
    :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> (('av \<times> 'bv) set, ('a \<times> 'b) set) \<phi>\<close> (infixr "\<Rrightarrow>\<^sub>r" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow>\<^sub>r U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>u y. (v,u) \<in> g \<and> (x,y) \<in> f \<and> u \<in> (y \<Ztypecolon> U)) })\<close>

end
