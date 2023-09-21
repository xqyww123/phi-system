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
  opening  extract_premises_in_local_inverse
  deriving \<open>Identity_Elements\<^sub>E (\<phi>Fun f) (\<lambda>x. f x = 1)\<close>
       and \<open>Identity_Elements\<^sub>I (\<phi>Fun f) (\<lambda>x. f x = 1) (\<lambda>_. True)\<close>
       and Basic
       and Functionality
       and Abstraction_to_Raw


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

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<s>\<u>\<b>\<j>" 25)
  where [embed_into_\<phi>type]: \<open> (T \<phi>\<s>\<u>\<b>\<j> P) = (\<lambda>x. x \<Ztypecolon> T \<s>\<u>\<b>\<j> P) \<close>
  deriving Basic
       and \<open>(\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Functionality T Q) \<Longrightarrow> Functionality (T \<phi>\<s>\<u>\<b>\<j> P) (\<lambda>x. P \<longrightarrow> Q x)\<close>
       and \<open>(\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Carrier_Set T Q) \<Longrightarrow> Carrier_Set (T \<phi>\<s>\<u>\<b>\<j> P) (\<lambda>x. P \<longrightarrow> Q x)\<close>
       and \<open>(\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<Longrightarrow> Identity_Elements\<^sub>I T D P) \<Longrightarrow> Identity_Elements\<^sub>I (T \<phi>\<s>\<u>\<b>\<j> Q) (\<lambda>x. Q \<longrightarrow> D x) (\<lambda>x. Q \<and> P x)\<close>
       and \<open>Identity_Elements\<^sub>E T D \<Longrightarrow> Identity_Elements\<^sub>E (T \<phi>\<s>\<u>\<b>\<j> P) (\<lambda>x. P \<and> D x) \<close>
       and Separation_Monoid
       and Abstraction_to_Raw

translations "TY_of_\<phi> (T \<phi>\<s>\<u>\<b>\<j> P)" \<rightharpoonup> "TY_of_\<phi> T"

subsubsection \<open>Rules\<close>

paragraph \<open>Simplification Rules\<close>

declare SubjectionTY.unfold [\<phi>programming_simps, assertion_simps]

lemma \<phi>\<s>\<u>\<b>\<j>_\<phi>\<s>\<u>\<b>\<j>[embed_into_\<phi>type, simp]:
  \<open>(T \<phi>\<s>\<u>\<b>\<j> P \<phi>\<s>\<u>\<b>\<j> Q) = (T \<phi>\<s>\<u>\<b>\<j> P \<and> Q)\<close>
  by (rule \<phi>Type_eqI; clarsimp)


subsubsection \<open>Transformation Setup\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> P) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by clarsimp

lemma [\<phi>reason %ToA_red]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> P) \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by (cases x; cases C; clarsimp; blast)

lemma [\<phi>reason %ToA_red]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by clarsimp

lemma [\<phi>reason %ToA_red]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph>[C] U) \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> P) \<^emph>[C] U \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by clarsimp

subsubsection \<open>Algebraic Properties\<close>

text \<open>Here we construct two inner transformations from \<open>a \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P\<close> to \<open>a \<Ztypecolon> T\<close> and another reversely.
  It is essentially an identity transformation from \<open>a\<close> to \<open>a\<close> itself.
  The constraints checks 1. if the identity transformation is supported (a very weak requirement),
        2. the container is always non-empty so that an independent assertion \<open>P\<close> bound at the element
           type is valid globally (this is a necessary condition).  \<close>


lemma \<phi>\<s>\<u>\<b>\<j>_Homo[\<phi>reason_template name Fa.\<phi>subj [assertion_simps]]:
  \<open> Transformation_Functor Fa Fa (T \<phi>\<s>\<u>\<b>\<j> P) T D R mapper
\<Longrightarrow> Transformation_Functor Fa Fa T (T \<phi>\<s>\<u>\<b>\<j> P) D R mapper
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a. a \<in> D x \<and> P \<longrightarrow> a \<in> R x) \<and> (\<forall>y. mapper (\<lambda>a b. a = b \<and> P) x y \<longrightarrow> x = y \<and> P)
\<Longrightarrow> (x \<Ztypecolon> Fa (T \<phi>\<s>\<u>\<b>\<j> P)) = (x \<Ztypecolon> Fa T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Transformation_Functor_def Transformation_def atomize_eq Premise_def BI_eq_iff
  apply (clarsimp; rule)
  subgoal premises prems for p
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>a b. a = b \<and> P\<close>], simplified]
               prems(3-5),
        clarsimp,
        blast)
  subgoal premises prems for p
    by (insert prems(2)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>a b. a = b\<close>], simplified]
               prems(3-5),
        clarsimp,
        blast) .

text \<open>The above rule is interesting but essentially useless as it is replaced by the following rule.
  The To-Transformation already enters into the elements by transformation functor.\<close>

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x \<and> P @action \<A>simp\<close>
  unfolding Transformation_Functor_def Transformation_def Action_Tag_def
  by simp

subsubsection \<open>Guessing Antecedents\<close>

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Property PC False (x \<Ztypecolon> T) a c C
\<Longrightarrow> Guess_Property PC False (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P) a ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P) \<and>\<^sub>\<r> c) C\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Property PC True (x \<Ztypecolon> T) a c C
\<Longrightarrow> Guess_Property PC True (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P) ((\<p>\<r>\<e>\<m>\<i>\<s>\<e> P) \<and>\<^sub>\<r> a) c C\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Property PC undefined (x \<Ztypecolon> T) a c C
\<Longrightarrow> Guess_Property PC undefined (x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P) a c C\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x) U Ds Dx zi ants conds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x \<phi>\<s>\<u>\<b>\<j> P s x) U
                            Ds (\<lambda>s t (x,y). P s x \<and> P t y \<longrightarrow> Dx s t (x,y)) zi ants conds \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x) U Ds Dx zi ants conds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. f s x \<Ztypecolon> T' s T x \<phi>\<s>\<u>\<b>\<j> P s x) U
                              Ds (\<lambda>s t xy. P (s + t) xy \<longrightarrow> Dx s t xy) zi ants conds \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

paragraph \<open>Commutativity between Tyoprs\<close>

subparagraph \<open>\<open>Guess_Tyops_Commute\<^sub>I\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P) G_def' T
                        (\<lambda>x. P \<longrightarrow> D x) r ants ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P) \<and>\<^sub>\<r> conds) \<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P x) G_def' T
                        (\<lambda>x. P x \<longrightarrow> D x) r ants conds \<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P' T x) T D r ants conds \<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P') T D r ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P') \<and>\<^sub>\<r> ants) conds \<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

subparagraph \<open>\<open>Guess_Tyops_Commute\<^sub>E\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute\<^sub>E F F' G G' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>E F F' G G' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P) G_def' T
                        (\<lambda>x. P \<longrightarrow> D x) r ants ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P) \<and>\<^sub>\<r> conds) \<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>E F F' G G' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>E F F' G G' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P x) G_def' T D r ants conds \<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>E F F' G G' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>E F F' G G' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P' T x) T D r ants conds \<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute\<^sub>E F F' G G' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>E F F' G G' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P') T D r ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P') \<and>\<^sub>\<r> ants) conds \<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..


subsection \<open>Dependent Sum Type \& Abstraction of Set\<close>

text \<open>Transformation functor requires inner elements to be transformed into some fixed \<phi>-type
  independently with the element. It seems to be a limitation. For example, we want to transform
  a list of unknown bit-length numbers \<open>l \<Ztypecolon> List \<nat>\<^sub>f\<^sub>r\<^sub>e\<^sub>e\<close> where \<open>x \<Ztypecolon> \<nat>\<^sub>f\<^sub>r\<^sub>e\<^sub>e \<equiv> (x \<Ztypecolon> \<nat>[b] \<s>\<u>\<b>\<j> b. x < 2^b)\<close>
  into a set of all lists of such numbers \<open>{l | ? } \<Ztypecolon> List \<nat>[?]\<close> where the question marks denote
  the terms cannot be expressed yet now.

  Such transformation can be expressed by \<^emph>\<open>Dependent Sum Type\<close> \<open>\<Sigma>\<close> and \<^emph>\<open>Set Abstraction\<close> \<open>LooseState\<close> \<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>Dependent_Sum :: \<open>('c \<Rightarrow> ('a,'b) \<phi>) \<Rightarrow> ('a, 'c \<times> 'b) \<phi>\<close> ("\<Sigma>")
  where \<open>cx \<Ztypecolon> \<Sigma> T \<equiv> (snd cx) \<Ztypecolon> T (fst cx)\<close>
  deriving \<open>(\<And>A. Object_Equiv (T A) (eq A))
        \<Longrightarrow> Object_Equiv (\<Sigma> T) (\<lambda>x y. fst y = fst x \<and> eq (fst x) (snd x) (snd y))\<close>
    and \<open>Object_Equiv (\<Sigma> (\<lambda>x. \<circle>)) (\<lambda>_ _. True) \<close>
    and    \<open>(\<And>c. Identity_Elements\<^sub>I (T c) (D c) (P c))
        \<Longrightarrow> Identity_Elements\<^sub>I (\<Sigma> T) (\<lambda>(c,u). D c u) (\<lambda>(c,u). P c u)\<close>
    and    \<open>(\<And>c. Identity_Elements\<^sub>E (T c) (D c))
        \<Longrightarrow> Identity_Elements\<^sub>E (\<Sigma> T) (\<lambda>(c,u). D c u) \<close>
    and Functionality
    and   \<open>(\<And>a (x::?'b \<times> ?'a). a \<Ztypecolon> T (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Itself \<s>\<u>\<b>\<j> b. r a b @action to Itself)
        \<Longrightarrow> \<forall>(x::?'b \<times> ?'a). x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>b. r (snd x) b \<and> y = b) @action to Itself \<close>
    and Abstraction_to_Raw

notation \<phi>Dependent_Sum (binder "\<Sigma> " 22)

text \<open>Though \<^term>\<open>\<Sigma> T\<close> is not a transformation functor not a separation homomoprhism
  as the element \<phi>-type \<open>T\<close> is parameterized,
  there can be properties very akin to them, see the section \<open>Pseudo properties of \<Sigma>\<close> below.\<close>


declare SubjectionTY_def[embed_into_\<phi>type del]

declare [[\<phi>trace_reasoning = 0]]
  
\<phi>type_def Set_Abstraction :: \<open>('a,'b) \<phi> \<Rightarrow> ('a, 'b set) \<phi>\<close> ("\<S>")
  where [embed_into_\<phi>type]: \<open>s \<Ztypecolon> \<S> T \<equiv> (x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s)\<close>
  deriving \<open> Identity_Elements\<^sub>E T D
         \<Longrightarrow> Identity_Elements\<^sub>E (\<S> T) (\<lambda>S. Bex S D) \<close>
       and \<open> Identity_Elements\<^sub>I T D P
         \<Longrightarrow> Identity_Elements\<^sub>I (\<S> T) (\<lambda>S. Ball S D) (\<lambda>S. Bex S P)\<close>
       and \<open> Abstract_Domain T P \<Longrightarrow> Abstract_Domain (\<S> T) (\<lambda>s. \<exists>x\<in>s. P x) \<close>
       and \<open> Abstract_Domain\<^sub>L T P \<Longrightarrow> Abstract_Domain\<^sub>L (\<S> T) (\<lambda>s. \<exists>x\<in>s. P x) \<close>
       and \<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<S> T) (\<lambda>Sx Sy. \<forall>x \<in> Sx. \<exists>y \<in> Sy. eq x y) \<close>
       (*and \<open> Object_Equiv (\<S> \<circle>) (\<lambda>Sx Sy. Sx \<noteq> {} \<longrightarrow> Sy \<noteq> {}) \<close>
                  \<comment> \<open>An example for which it is a non-symmetric reachability relation\<close>*)
       and Separation_Monoid
       and \<open>Transformation_Functor \<S> \<S> T U (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>g Sx Sy. Sy = {y. \<exists>x\<in>Sx. g x y})\<close>
       and \<open>Functional_Transformation_Functor Set_Abstraction Set_Abstraction T U
                      (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>_ _ _. True) (\<lambda>f P X. { f x |x. x \<in> X \<and> P x })\<close>
       and \<open>Separation_Homo\<^sub>I \<S> \<S> \<S> T U UNIV (\<lambda>x. case x of (A, B) \<Rightarrow> A \<times> B)\<close>
       and Open_Abstraction_to_Raw
       and \<open>c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {x} \<Ztypecolon> \<S> T \<close>

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
\<Longrightarrow> f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { (x, f x) |x. P x } \<Ztypecolon> \<S> (\<Sigma> T)\<close>
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
\<Longrightarrow> {x. P c x} \<Ztypecolon> \<S> (T c) \<s>\<u>\<b>\<j> c. \<top> \<equiv> {x. \<exists>c y. x = (c, y) \<and> P c y} \<Ztypecolon> \<S> (\<Sigma> T)\<close>
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

declare [[\<phi>trace_reasoning = 1]]

declare \<phi>Dependent_Sum.intro_reasoning(1)
        [where x=\<open>(a,b)\<close> for a b, simplified apfst_conv apsnd_conv fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.intro_reasoning(2)
        [where x=\<open>(a,b)\<close> for a b, simplified apfst_conv apsnd_conv fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((_, _), _) \<Ztypecolon> \<Sigma> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.intro_reasoning\<^sub>R
        [where x=\<open>(a,b)\<close> for a b, simplified fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> ]

        \<phi>Dependent_Sum.elim_reasoning[\<phi>reason 1000]
        \<phi>Dependent_Sum.elim_reasoning(1)
        [where x=\<open>(a,b)\<close> for a b, simplified fst_conv snd_conv,
         \<phi>reason 1010 for \<open>(_, _) \<Ztypecolon> \<Sigma> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]

        \<phi>Dependent_Sum.elim_reasoning(2)
        [where x=\<open>((a,b),w)\<close> for a b w, simplified apfst_conv fst_conv snd_conv,
         \<phi>reason 1010 for \<open>((_,_),_) \<Ztypecolon> \<Sigma> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]

thm Set_Abstraction.intro_reasoning\<^sub>R
thm Set_Abstraction.intro_reasoning
thm Set_Abstraction.elim_reasoning

text \<open>Type-level \<open>Set_Abstraction.intro_reasoning\<close> is not activated as the reasoning uses
  transformation functor.

  see Set_Abstraction.intro_reasoning

NG! TODO!\<close>

thm Set_Abstraction.intro_reasoning(1)  [\<phi>reason 60]
        Set_Abstraction.elim_reasoning(1)[\<phi>reason 1000]

(*TODO!!!*)

lemma [\<phi>reason 2800]:
  \<open> (\<And>a \<in> fst x. (a, snd x) \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P )
\<Longrightarrow> x \<Ztypecolon> (\<S> T) \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def Premise_def Transformation_def meta_Ball_def
  by (cases x; cases C; clarsimp; blast)


subsubsection \<open>Pseudo properties of \<Sigma>\<close>

text \<open>Any non-constantly parameterized \<phi>-types are represented by \<open>\<Sigma>\<close>. Therefore,
  \<open>\<Sigma>\<close> is the only parameterized \<phi>-type for which we need to configure its reasoning rules manually.\<close>

text \<open>The following properties are nice but essentially useless for reasoning as we have registered
  the intro- and elim-rules for \<open>\<Sigma>\<close> destructing any \<open>\<Sigma>\<close> occurring in the reasoning.
  So, the properties below are just listed for aesthetics of math.
\<close>

lemma \<Sigma>_pseudo_Transformation_Functor:
  \<open> (\<And>a c. a \<Ztypecolon> T c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U c' \<s>\<u>\<b>\<j> b c'. g (c,a) (c',b))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> U \<s>\<u>\<b>\<j> y. g x y \<close>
  unfolding Transformation_def
  by (cases x; clarsimp; blast)

lemma \<Sigma>_pseudo_Separation_Homo\<^sub>I:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst (fst x) = fst (snd x)
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<^emph> \<Sigma> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst (fst x), (snd (fst x), snd (snd x))) \<Ztypecolon> \<Sigma> c. (T c \<^emph> U c) \<close>
  unfolding Transformation_def Premise_def
  by clarsimp

lemma \<Sigma>_pseudo_Separation_Homo\<^sub>E:
  \<open> x \<Ztypecolon> \<Sigma> c. (T c \<^emph> U c) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst x, fst (snd x)), (fst x, snd (snd x))) \<Ztypecolon> \<Sigma> T \<^emph> \<Sigma> U \<close>
  unfolding Transformation_def Premise_def
  by clarsimp

lemma \<Sigma>_fundef_cong[fundef_cong]:
  \<comment> \<open>The rule fails to be derived due to the absence of the standard
      Transformation Functor property\<close>
  \<open> x = y
\<Longrightarrow> (F (fst y) (snd y) = G (fst y) (snd y))
\<Longrightarrow> \<Sigma> F x = \<Sigma> G y \<close>
  unfolding \<phi>Dependent_Sum_def \<phi>Type_def
  by simp

(*TODO: reasoning rules based on the above pseudo properties*)


subsubsection \<open>\<Sigma>-Homomorphism\<close>



lemma [\<phi>reason_template name F.\<Sigma>\<^sub>I[]]:
  \<open> Functional_Transformation_Functor F F' (T (fst x)) (\<Sigma> T) D R pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D (snd x) \<longrightarrow> (fst x, a) \<in> R (snd x))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> c. F (T c) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fm (\<lambda>a. (fst x, a)) (\<lambda>_. True) (snd x) \<Ztypecolon> F' (\<Sigma> T)\<close>
  unfolding Functional_Transformation_Functor_def Premise_def
  apply clarsimp
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=\<open>snd x\<close>], THEN spec[where x=\<open>\<lambda>a. (fst x, a)\<close>],
                        THEN spec[where x=\<open>\<lambda>_. True\<close>], simplified]
               prems(2-),
        clarsimp simp add: transformation_weaken) .

lemma [\<phi>reason_template name F.\<Sigma>\<^sub>E[]]:
  \<open> (\<And>c. Functional_Transformation_Functor F F' (\<Sigma> T) (T c) D (R c) (pm c) (fm c))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. fst a = c \<and> snd a \<in> R c x )
\<Longrightarrow> x \<Ztypecolon> F (\<Sigma> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fm c snd (\<lambda>_. True) x \<Ztypecolon> F' (T c) \<w>\<i>\<t>\<h> pm c snd (\<lambda>_. True) x \<close>
  unfolding Premise_def Functional_Transformation_Functor_def
  by clarsimp force

lemma [\<phi>reason_template name F.\<Sigma>_rewr[]]:
  \<open> (\<And>c. Functional_Transformation_Functor F F' (\<Sigma> T) (T c) D (R c) (pm c) (fm c))
\<Longrightarrow> Functional_Transformation_Functor F' F (T c) (\<Sigma> T) D' R' pm' fm'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. c = fst a \<and> snd a \<in> R c x ) \<and>
           (\<forall>a. a \<in> D' (fm c snd (\<lambda>_. True) x) \<longrightarrow> (c, a) \<in> R' (fm c snd (\<lambda>_. True) x))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fm' (\<lambda>a. (c, a)) (\<lambda>_. True) (fm c snd (\<lambda>_. True) x) = x
\<Longrightarrow> (x \<Ztypecolon> F (\<Sigma> T)) = (fm c snd (\<lambda>_. True) x \<Ztypecolon> F' (T c))\<close>
  unfolding Functional_Transformation_Functor_def Premise_def
  apply (clarsimp simp del: split_paired_All; rule assertion_eq_intro)

  subgoal premises prems
    by (insert prems(1)[of c, THEN spec[where x=x], THEN spec[where x=snd], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-) ;
        clarsimp simp add: transformation_weaken;
        metis fst_conv snd_eqD transformation_weaken)

  subgoal premises prems
    by (insert prems(2)[THEN spec[where x=\<open>fm c snd (\<lambda>_. True) x\<close>], THEN spec[where x=\<open>\<lambda>a. (c, a)\<close>],
                        THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-),
        clarsimp simp add: transformation_weaken) .




(*

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
        (x \<Ztypecolon> Fa (\<Sigma>\<^sub>\<A> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, m x) \<Ztypecolon> \<Sigma> c. Fb (T c)) @action \<phi>TA_ind_target \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
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


*)

subsubsection \<open>\<S>-Homomorphism\<close>

text \<open>The homomorphism of \<open>\<S>\<close> type is entailed in the transformation functor directly.\<close>

lemma \<S>_Homo\<^sub>E [\<phi>reason_template name Fa.\<S>\<^sub>E []]:
  \<open> Transformation_Functor Fa Fb (\<S> T) T D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D s \<and> b \<in> a \<longrightarrow> b \<in> R s)
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> s' : Collect (mapper (\<lambda>S x. x \<in> S) s)) @action \<A>_template_reason
\<Longrightarrow> s \<Ztypecolon> Fa (\<S> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> \<S> (Fb T)\<close>
  unfolding Transformation_Functor_def Transformation_def Premise_def Action_Tag_def Simplify_def
  by clarsimp

text \<open>Does the reverse transformation exists?. The commutativity between \<open>F\<close> and \<open>\<S>\<close> gonna be a problem.\<close>



(* TODO: meta analysis, and commutativity of \<open>\<S>\<close>

lemma \<S>_Homo\<^sub>I [\<phi>reason_template name \<S>\<^sub>I []]:

lemma
  \<open> Transformation_Functor Fa Fb T (\<S> T) D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D s \<longrightarrow> {a} \<in> R s)
\<Longrightarrow> s \<Ztypecolon> \<S> (Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<s>\<u>\<b>\<j> s'. mapper (\<lambda>a b. b = {a}) s s' \<close>
  unfolding Action_Tag_def Functional_Transformation_Functor_def Premise_def
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>a. {a}\<close>], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2) ;
        clarsimp simp add: transformation_weaken) .

(*the reverse map cannot be derived using TF.*)

lemma
  \<open> (\<And>a \<in> fst x. a \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U ...)
\<Longrightarrow> x \<Ztypecolon> \<S> T \<^emph>[Cw] \<S> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] \<S> R \<close>

lemma \<S>_Homo\<^sub>I [\<phi>reason_template name \<S>\<^sub>I []]:
  \<open> Functional_Transformation_Functor Fa Fb T (\<S> T) D R pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<exists>f. \<forall>x \<in> s. s' = fm f (\<lambda>_. True) x \<and> (\<forall>a \<in> D x. f a \<in> R x))
\<Longrightarrow> s \<Ztypecolon> \<S> (Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<close>
  unfolding Action_Tag_def Transformation_Functor_def Premise_def
  apply clarsimp
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>a b. b = {a}\<close>], simplified]
               prems(2),
        clarsimp) .
*)

lemma \<S>_Homo\<^sub>I [\<phi>reason_template name Fa.\<S>\<^sub>I []]:
  \<open> Functional_Transformation_Functor Fa Fb T (\<S> T) D R pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D s \<longrightarrow> {a} \<in> R s)
\<Longrightarrow> s \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fm (\<lambda>x. {x}) (\<lambda>_. True) s \<Ztypecolon> Fb (\<S> T)\<close>
  unfolding Action_Tag_def Functional_Transformation_Functor_def Premise_def
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>a. {a}\<close>], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2) ;
        clarsimp simp add: transformation_weaken) .

(*
lemma \<S>_Homo\<^sub>I [\<phi>reason_template name \<S>\<^sub>I []]:
  \<open> Transformation_Functor Fa Fb T (\<S> T) D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D s \<longrightarrow> {a} \<in> R s)
\<Longrightarrow> s \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> Fb (\<S> T) \<s>\<u>\<b>\<j> s'. mapper (\<lambda>a b. b = {a}) s s' \<close>
  unfolding Action_Tag_def Transformation_Functor_def Premise_def
  subgoal premises prems
    by (insert prems(1)[THEN spec[where x=s], THEN spec[where x=\<open>\<lambda>a b. b = {a}\<close>], simplified]
               prems(2),
        clarsimp) .
*)


text \<open>The above rules are interesting but essentially useless as it is replaced by the following rule,
  which eliminates any \<open>\<S>\<close> in a ready sequent of CoP.

mmm but what if during the separation extraction when a \<open>\<S>\<close> is generated by some previous reasoning?

The above rules are still useful in giving the commutativity between \<open>F\<close> and \<open>\<S>\<close>.
\<close>

lemma [\<phi>reason 1000]:
  \<open>s \<Ztypecolon> \<S> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s @action \<A>simp\<close>
  unfolding Action_Tag_def Transformation_def
  by simp


 
subsection \<open>Vertical Composition\<close>
 
\<phi>type_def \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 30)
  where \<open>\<phi>Composition T U x = (y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<Turnstile> (x \<Ztypecolon> U))\<close>
  deriving Carrier_Set

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
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B'
\<Longrightarrow> Transformation_Functor ((\<Zcomp>) B) ((\<Zcomp>) B') T U (\<lambda>x. {x}) (\<lambda>_. UNIV) (\<lambda>r. r)\<close>
  unfolding Transformation_Functor_def Transformation_def \<r>Guard_def Premise_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> B = B'
\<Longrightarrow> Functional_Transformation_Functor ((\<Zcomp>) B) ((\<Zcomp>) B') T U (\<lambda>x. {x}) (\<lambda>_. UNIV) (\<lambda>_ P. P) (\<lambda>f _. f)\<close>
  unfolding Functional_Transformation_Functor_def Transformation_def \<r>Guard_def Premise_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rU x y @action to (Itself :: ('b,'b) \<phi>))
\<Longrightarrow> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'c) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rT x y @action to (Itself :: ('c,'c) \<phi>))
\<Longrightarrow> x \<Ztypecolon> T \<Zcomp> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>m. rT m y \<and> rU x m) @action to (Itself :: ('c,'c) \<phi>)\<close>
  unfolding Transformation_def Action_Tag_def
  by clarsimp  blast

lemma [\<phi>reason 1000]:
  \<open> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> m \<Ztypecolon> T
\<Longrightarrow> m \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U
\<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<Zcomp> U \<close>
  unfolding Action_Tag_def Transformation_def Premise_def
  by clarsimp blast
   
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

(*TODO: let_\<phi>type \<phi>Composition deriving SE_Trim_Empty*)



lemma \<Psi>_comp:
  \<open> \<Psi>[\<psi>] (x \<Ztypecolon> T) = (x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T) \<close>
  unfolding BI_eq_iff
  by clarsimp

(* TODO
(*   C ----> T ---> U
     \<down>\<delta>  \<subseteq>   | \<delta>\<^sub>T   | \<delta>\<^sub>U
    D(c) \<leftarrow>-- \<leftarrow>----
 *)
lemma
  \<open> Domainoid_Homo\<^sub>L \<delta> U d
\<Longrightarrow> Domainoid_Homo\<^sub>L \<delta> (T \<Zcomp> U) d \<close>
*)

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
\<Longrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U UNIV (\<lambda>x. x)\<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
  by (clarsimp, insert times_set_I, blast)

lemma (*The above rule is reversible. requiring the sep homo domain being the univ is already the weakest.*)
  \<open> S \<noteq> {}
\<Longrightarrow> \<forall>T U. Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U S (\<lambda>x. x)
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
\<Longrightarrow> Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U (\<lambda>x. x)\<close>
  for B :: \<open>('d::sep_magma,'e::sep_magma) \<phi>\<close>
  unfolding Separation_Homo\<^sub>E_def Transformation_def Object_Sep_Homo\<^sub>E_def
  by (clarsimp simp add: set_mult_expn; blast)

lemma (*The above rule is reversible*)
  \<open> \<forall>T U. Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U (\<lambda>x. x) \<Longrightarrow> Object_Sep_Homo\<^sub>E B \<close>
  unfolding Separation_Homo\<^sub>E_def Object_Sep_Homo\<^sub>E_def Transformation_def
  apply (clarsimp simp add: set_mult_expn)
  apply (simp add: \<phi>Type_def Satisfaction_def)
  subgoal premises prems for x y v
    by (insert prems(1)[THEN spec[where x=\<open>\<lambda>_. {y}\<close>], THEN spec[where x=\<open>\<lambda>_. {x}\<close>], simplified]
               prems(2-3), blast) .



(* subsection \<open>Embedding Universal Quantification\<close>

\<phi>type_def \<phi>Type_univ_quant :: \<open>('c \<Rightarrow> ('a, 'b) \<phi>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b)\<phi>\<close> ("\<forall>\<^sub>\<phi> _" [10] 10)
  where \<open>\<phi>Type_univ_quant T = (\<lambda>x. \<forall>\<^sub>B\<^sub>Ic. x c \<Ztypecolon> T c)\<close>

lemma \<phi>Type_univ_quant_expn[\<phi>expns]:
  \<open>p \<in> (f \<Ztypecolon> (\<forall>\<^sub>\<phi> T)) \<longleftrightarrow> (\<forall>x. p \<in> (f x \<Ztypecolon> T x))\<close>
  unfolding \<phi>Type_univ_quant_def \<phi>Type_def by clarsimp
*)


subsection \<open>Additive Disjunction\<close>

subsubsection \<open>Preliminary Settings\<close>

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


subsection \<open>Finite Multiplicative Quantification\<close>



declare [[\<phi>trace_reasoning = 0]]

text \<open>The type parameter \<open>T\<close> is not paramterized by the quantified variable. It is not a restriction
  as we have \<open>\<Sigma>\<close>. Instead, only when \<open>T\<close> is not parameterized, \<open>\<big_ast>\<^sup>\<phi> I T\<close> forms a semimodule.\<close>

\<phi>type_def \<phi>Mul_Quant :: \<open>'i set \<Rightarrow> ('c::sep_algebra, 'x) \<phi> \<Rightarrow> ('c::sep_algebra, 'i \<Rightarrow> 'x) \<phi>\<close> ("\<big_ast>\<^sup>\<phi>")
  where [embed_into_\<phi>type]: \<open>\<big_ast>\<^sup>\<phi> I T = (\<lambda>x. \<big_ast>i\<in>I. x i \<Ztypecolon> T)\<close>
  deriving Basic
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (\<big_ast>\<^sup>\<phi> I T) (\<lambda>x. \<forall>i \<in> I. P (x i)) \<close>
       (*and Abstract_Domain\<^sub>L (*TODO*)*)
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J \<Longrightarrow> Transformation_Functor (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> J) T U (\<lambda>x. x ` I) (\<lambda>_. UNIV) (\<lambda>g x y. \<forall>i\<in>I. g (x i) (y i))\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J \<Longrightarrow> Functional_Transformation_Functor (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> J) T U (\<lambda>x. x ` I) (\<lambda>_. UNIV) (\<lambda>_ P x. \<forall>i\<in>I. P (x i)) (\<lambda>f _. (o) f)\<close>
       and \<open>Identity_Elements\<^sub>I T D P
        \<Longrightarrow> Identity_Elements\<^sub>I (\<big_ast>\<^sup>\<phi> I T) (\<lambda>f. \<forall>i\<in>I. D (f i)) (\<lambda>f. \<forall>i\<in>I. P (f i))\<close>
       and \<open>Identity_Elements\<^sub>E T D
        \<Longrightarrow> Identity_Elements\<^sub>E (\<big_ast>\<^sup>\<phi> I T) (\<lambda>f. finite I \<and> (\<forall>i\<in>I. D (f i))) \<close>
       and Separation_Monoid
       and \<open>Functionality T P \<Longrightarrow> Functionality (\<big_ast>\<^sup>\<phi> I T) (\<lambda>x. (\<forall>i \<in> I. P (x i)))\<close>
       and Semimodule_NonDistr
       and Closed_Semimodule_Zero


subsubsection \<open>Syntax\<close>

nonterminal "dom_idx"

syntax
  "_one_dom" :: \<open>pttrns \<Rightarrow> 'a set \<Rightarrow> dom_idx\<close> ("_/\<in>_" [0,51] 50)
  "_more_dom":: \<open>dom_idx \<Rightarrow> dom_idx \<Rightarrow> dom_idx\<close> ("_,/ _" [49, 50] 49)
  "_\<phi>Mul_Quant" :: "dom_idx \<Rightarrow> logic \<Rightarrow> logic"  ("(2\<big_ast>[_]/ _)" [49, 1000] 1000)
  "_\<phi>Mul_Quant_mid" :: "dom_idx \<Rightarrow> logic \<Rightarrow> logic"

translations
  "CONST \<phi>Type x (_\<phi>Mul_Quant (_one_dom i I) T)" == "CONST \<phi>Type (\<lambda>i. x) (CONST \<phi>Mul_Quant I T)"
  "CONST \<phi>Type x (_\<phi>Mul_Quant (_more_dom d (_one_dom i I)) T)" == "CONST \<phi>Type (\<lambda>i. x) (_\<phi>Mul_Quant d (CONST \<phi>Mul_Quant I T))"


subsubsection \<open>Configure\<close>

lemma \<phi>Mul_Quant_induct:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> finite I
\<Longrightarrow> (\<And>T x. P {} T x)
\<Longrightarrow> (\<And>I T x i. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> finite I \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<notin> I \<Longrightarrow> P I T x \<Longrightarrow> P (insert i I) T x)
\<Longrightarrow> P I T x\<close>
  unfolding Premise_def
  subgoal premises prems
    by (insert prems(2-);
        induct rule: finite_induct[OF prems(1)]; clarsimp) .

setup \<open>Context.theory_map (
  Phi_Type_Algebra.override_ind_rule (\<^const_name>\<open>\<phi>Mul_Quant\<close>, @{thm' \<phi>Mul_Quant_induct}))\<close>

subsubsection \<open>Supplementary Algebraic Properties\<close>

text \<open>Instead of deriving the Scalar Distributivity automatically, we give them manually, as the scalar
  distribution of the assertion-level \<open>\<big_ast>\<close> is not activated in the reasoning system by default
  (it is too aggressive to enable it).\<close>

lemma \<phi>Mul_Quant_SDistr_Homo\<^sub>Z[\<phi>reason 1000]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z \<big_ast>\<^sup>\<phi> T (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ D\<^sub>g (f,g). f \<oplus>\<^sub>f[D\<^sub>g] g) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def dom_of_add_set_def
  by (clarsimp simp add: \<phi>Prod_expn' \<phi>Mul_Quant.unfold sep_quant_scalar_distr;
      smt (verit) Mul_Quant_def Transformation_def disjoint_iff plus_set_in_iff prod.cong)

lemma \<phi>Mul_Quant_SDistr_Homo\<^sub>U[\<phi>reason 1000]:
  \<open> Semimodule_SDistr_Homo\<^sub>U \<big_ast>\<^sup>\<phi> T (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ f. (f ,f)) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_def dom_of_add_set_def
  by (clarsimp simp add: \<phi>Mul_Quant.unfold \<phi>Prod_expn' sep_quant_scalar_distr)


subsubsection \<open>Supplementary Rewrites\<close>

thm \<phi>Mul_Quant.scalar_zero
thm \<phi>Mul_Quant.scalar_one

lemma \<phi>Mul_Quant_insert:
  \<open> k \<notin> I
\<Longrightarrow> (x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T) = ((x k, x) \<Ztypecolon> T \<^emph> \<big_ast>\<^sup>\<phi> I T) \<close>
  unfolding \<phi>Mul_Quant.unfold \<phi>Prod_expn'
  by (clarsimp simp add: sep_quant_insert)

subsubsection \<open>Supplementary Transformations\<close>

paragraph \<open>Reduction for individually inserted elements\<close>

lemma [\<phi>reason %ToA_derived_red-10]: \<comment>\<open>The priority must be lower than the derived \<open> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> {x} T\<close>\<close>
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T) * (x k \<Ztypecolon> T) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Mul_Quant.unfold \<r>Guard_def Premise_def
  by (clarsimp simp add: sep_quant_insert)

lemma [\<phi>reason %ToA_derived_red-10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T) * (x k \<Ztypecolon> T) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Mul_Quant.unfold \<r>Guard_def Premise_def
  by (clarsimp simp add: sep_quant_insert)

lemma [\<phi>reason %ToA_derived_red-10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst (\<lambda>f. (f k, f)) x \<Ztypecolon> (T \<^emph> \<big_ast>\<^sup>\<phi> I T) \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> (insert k I) T \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding \<r>Guard_def Premise_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn' \<phi>Mul_Quant_insert)


(* The proof cannot continue as it requires the \<phi>-type commutativity \<open>x \<Ztypecolon> \<black_circle> \<big_ast>\<^sup>\<phi> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> \<black_circle> T\<close>
   The commutativity between \<phi>-type operators! It should be a meta deriver...

lemma
  \<open> \<g>\<u>\<a>\<r>\<d> NO_MATCH {e} I
\<Longrightarrow> (fst x i, fst wr) \<Ztypecolon> T \<^emph>[Cwi] Wi \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Y \<^emph>[Cri] Ri \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> I \<comment> \<open>The domain of the \<open>\<big_ast>\<close> must be known during reasoning time\<close>
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> J : Set.remove i I
\<Longrightarrow> if Cwi then (fst x, snd x) \<Ztypecolon> \<big_ast>\<^sup>\<phi> J T \<^emph>[Cw] Ws \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> wr \<Ztypecolon> Wi \<^emph>[Crj] Rs \<w>\<i>\<t>\<h> Q \<and>\<^sub>\<r>
                (((snd y, snd wr) \<Ztypecolon> \<half_blkcirc>[Cri] Ri \<^emph> \<half_blkcirc>[Crj] Rs) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>merge)
           else (Cw, Ws) = (False, \<top>\<^sub>\<phi>) \<and>\<^sub>\<r>
                (((snd y, fst x) \<Ztypecolon> \<half_blkcirc>[Cri] Ri \<^emph> \<half_blkcirc>[True] \<big_ast>\<^sup>\<phi> J T) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>merge)
\<Longrightarrow> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T \<^emph>[Cw] Ws \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> Y \<^emph>[Cr] R \<w>\<i>\<t>\<h> Q \<and> P\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_MATCH_def Ant_Seq_def
  apply (cases Cwi; simp add: cond_prod_transformation_rewr;
         simp add: Cond_\<phi>Prod_expn_\<phi>Some \<phi>Prod_expn' \<phi>Prod_expn'')

  \<medium_left_bracket> premises Tr1 and I and J[] and Tr2
    have [simp]: \<open>I = insert i J\<close> using I J by force
    have th1[simp]: \<open>i \<notin> J\<close> using J by fastforce ;; ;;

    simplify (\<phi>Prod_expn'', \<phi>Mul_Quant_insert)

thm \<phi>Mul_Quant_insert
thm Tr2
*)



subsection \<open>Sum Type\<close>

declare [[\<phi>trace_reasoning = 0]]


lemma [simp]:
  \<open>pred_sum = case_sum\<close>
  using pred_sum_eq_case_sum by blast


(*TODO: finish me!*)

\<phi>type_def \<phi>Sum :: \<open>('c,'x) \<phi> \<Rightarrow> ('c, 'y) \<phi> \<Rightarrow> ('c, 'x + 'y) \<phi>\<close> (infixl "+\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T +\<^sub>\<phi> U) = (\<lambda>xy. case xy of Inl x \<Rightarrow> x \<Ztypecolon> T | Inr y \<Rightarrow> y \<Ztypecolon> U)\<close>
  opening extracting_Identity_Element
  deriving \<open>Object_Equiv T eq\<^sub>T \<Longrightarrow> Object_Equiv U eq\<^sub>U \<Longrightarrow> Object_Equiv (T +\<^sub>\<phi> U) (rel_sum eq\<^sub>T eq\<^sub>U)\<close>
       and \<open>Abstract_Domain T P
        \<Longrightarrow> Abstract_Domain U Q
        \<Longrightarrow> Abstract_Domain (T +\<^sub>\<phi> U) (pred_sum P Q) \<close>
       and \<open>Carrier_Set T P
        \<Longrightarrow> Carrier_Set U Q
        \<Longrightarrow> Carrier_Set (T +\<^sub>\<phi> U) (pred_sum P Q)\<close>
       and Identity_Elements
       and Transformation_Functor
       and Commutativity_Deriver\<^sub>E_rev


subsubsection \<open>Rewrites\<close>

lemma \<phi>Sum_red[simp]:
  \<open>(Inl a \<Ztypecolon> T +\<^sub>\<phi> U) = (a \<Ztypecolon> T)\<close>
  \<open>(Inr b \<Ztypecolon> T +\<^sub>\<phi> U) = (b \<Ztypecolon> U)\<close>
  unfolding \<phi>Sum.unfold
  by simp_all

(* TODO: if so, we can totally replace \<open>\<or>\<^sub>\<phi>\<close> by \<open>+\<^sub>\<phi>\<close>
(*TODO: reduce \<open>(x \<Ztypecolon> T) + (y \<Ztypecolon> U) + (z \<Ztypecolon> Z) \<equiv> {Inl ({Inl x} + {Inr y})} + {Inr z} \<Ztypecolon> \<S> (\<S> (T +\<^sub>\<phi> U) +\<^sub>\<phi> Z)
                                           \<equiv> {Inl (Inl x)} + {Inl (Inr y)} + {Inr z} \<Ztypecolon> \<S> T +\<^sub>\<phi> \<S> U +\<^sub>\<phi> \<S> Z\<close>*)
lemma [embed_into_\<phi>type]:
  \<open> ((x \<Ztypecolon> T) + (y \<Ztypecolon> U)) = ({Inl x} + {Inr y} \<Ztypecolon> \<S> (T +\<^sub>\<phi> U)) \<close>
  unfolding BI_eq_iff
  by (clarsimp simp add: split_sum_ex)

term \<open>{Inl ({Inl x} + {Inr y})} + {Inr z} \<Ztypecolon> \<S> (\<S> (T +\<^sub>\<phi> U) +\<^sub>\<phi> Z)\<close>

*)

subsubsection \<open>Transformations\<close>

\<phi>reasoner_group ToA_splitting_\<phi>Sum = (%ToA_splitting-20, [%ToA_splitting-20, %ToA_splitting-19])
                                      for (\<open>x \<Ztypecolon> T +\<^sub>\<phi> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close>, \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T +\<^sub>\<phi> U\<close>)
                                       in ToA_splitting and < ToA_splitting_If
  \<open>ToA splitting \<open>\<phi>Sum\<close>\<close>

declare \<phi>Sum.intro_reasoning(1)[\<phi>reason %ToA_splitting_\<phi>Sum]
        \<phi>Sum.elim_reasoning (1)[\<phi>reason %ToA_splitting_\<phi>Sum]

lemma [\<phi>reason %ToA_splitting_\<phi>Sum+1 for \<open>(_, _) \<Ztypecolon> (_ +\<^sub>\<phi> _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (case x of Inl a \<Rightarrow> (a, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>a a] W\<^sub>a a | Inr b \<Rightarrow> (b, w\<^sub>b b) \<Ztypecolon> U \<^emph>[C\<^sub>b b] W\<^sub>b b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x, case_sum w\<^sub>a w\<^sub>b x) \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[case_sum C\<^sub>a C\<^sub>b x] case_sum W\<^sub>a W\<^sub>b x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by (cases x; auto simp add: \<phi>Prod_expn' Cond_\<phi>Prod_expn)

lemma [\<phi>reason %ToA_splitting_\<phi>Sum]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> snd x = case_sum w\<^sub>a w\<^sub>b (fst x) \<Longrightarrow>
      (case fst x of Inl a \<Rightarrow> (a, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>a a] W\<^sub>a a | Inr b \<Rightarrow> (b, w\<^sub>b b) \<Ztypecolon> U \<^emph>[C\<^sub>b b] W\<^sub>b b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> snd x = case_sum w\<^sub>a w\<^sub>b (fst x)
\<Longrightarrow> x \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[case_sum C\<^sub>a C\<^sub>b (fst x)] case_sum W\<^sub>a W\<^sub>b (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Premise_def
  by (cases x; case_tac a; auto simp add: \<phi>Prod_expn' Cond_\<phi>Prod_expn)

lemma [\<phi>reason %ToA_splitting_\<phi>Sum]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (case fst y of Inl a \<Rightarrow> (a, snd y) \<Ztypecolon> T \<^emph>[C] R | Inr b \<Rightarrow> (b, snd y) \<Ztypecolon> U \<^emph>[C] R) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  by (cases y; case_tac a; cases C; simp add: \<phi>Prod_expn')


subsubsection \<open>Rule\<close>

declare [[\<phi>trace_reasoning = 1]]
 
lemma \<phi>Sum_Comm\<^sub>I_temlpate [\<phi>reason_template name F.\<phi>Sum_Comm\<^sub>I[]]:
  \<open> Functional_Transformation_Functor F\<^sub>T F T (T +\<^sub>\<phi> U) D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F U (T +\<^sub>\<phi> U) D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D : (\<lambda>x. case x of Inl u \<Rightarrow> (\<forall>a \<in> D\<^sub>T u. Inl a \<in> R\<^sub>T u)
                              | Inr v \<Rightarrow> (\<forall>b \<in> D\<^sub>U v. Inr b \<in> R\<^sub>U v))) @action \<A>_template_reason
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r : (embedded_func (case_sum (fm\<^sub>T Inl (\<lambda>_. True)) (fm\<^sub>U Inr (\<lambda>_. True)))
                                (pred_sum (pm\<^sub>T Inl (\<lambda>_. True)) (pm\<^sub>U Inr (\<lambda>_. True))))) @action \<A>_template_reason
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F\<^sub>T F\<^sub>U (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U D r \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Functional_Transformation_Functor_def Premise_def
            Action_Tag_def Simplify_def
  by (clarify; case_tac x; clarsimp)

(*
setup \<open>Context.theory_map (Phi_Type_Template_Properties.Template_Inst_SS_Post_Merging.add 100
  (fn _ => Config.put Simplifier.simp_trace true))\<close>

declare [[simp_trace_depth_limit = 10]]*)

lemma \<phi>Sum_Comm\<^sub>E_temlpate [\<phi>reason_template name F.\<phi>Sum_Comm\<^sub>E'[]]:
  \<open> Functional_Transformation_Functor F F'\<^sub>T (T +\<^sub>\<phi> U) T D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F F'\<^sub>U (T +\<^sub>\<phi> U) U D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x a. a \<in> D\<^sub>T x \<and> isl a \<longrightarrow> projl a \<in> R\<^sub>T x) \<and>
           (\<forall>x a. a \<in> D\<^sub>U x \<and> \<not> isl a \<longrightarrow> projr a \<in> R\<^sub>U x)
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] D : (\<lambda>x. (\<forall>a \<in> D\<^sub>T x. isl a) \<or> (\<forall>b \<in> D\<^sub>U x. \<not> isl b))) @action \<A>_template_reason
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] r : (embedded_func (\<lambda>x. if (\<forall>a \<in> D\<^sub>T x. isl a)
                                    then Inl (fm\<^sub>T projl (\<lambda>_. True) x)
                                    else Inr (fm\<^sub>U projr (\<lambda>_. True) x))
                               (\<lambda>x. if (\<forall>a \<in> D\<^sub>T x. isl a)
                                    then pm\<^sub>T projl (\<lambda>_. True) x
                                    else pm\<^sub>U projr (\<lambda>_. True) x))) @action \<A>_template_reason
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U D r \<close>
  unfolding Functional_Transformation_Functor_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Simplify_def Action_Tag_def
  apply (clarify; case_tac \<open>Ball (D\<^sub>T x) isl\<close>; auto)
  subgoal premises prems for x
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=projl], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems (3-),
        clarsimp simp add: Transformation_def split_sum_all Ball_def)
  subgoal premises prems for x
    by (insert prems(2)[THEN spec[where x=x], THEN spec[where x=projr], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-),
        clarsimp simp add: Transformation_def split_sum_all Ball_def) .



(*lemma \<phi>Sum_Comm\<^sub>E [\<phi>reason %\<phi>type_algebra_prop_cut]:
  \<open> Functional_Transformation_Functor F\<^sub>T F T (T +\<^sub>\<phi> U) D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F U (T +\<^sub>\<phi> U) D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F\<^sub>T F\<^sub>U \<phi>Sum \<phi>Sum T U
                   (\<lambda>x. case x of Inl u \<Rightarrow> (\<forall>a \<in> D\<^sub>T u. Inl a \<in> R\<^sub>T u)
                                | Inr v \<Rightarrow> (\<forall>b \<in> D\<^sub>U v. Inr b \<in> R\<^sub>U v))
                   (embedded_func (case_sum (fm\<^sub>T Inl (\<lambda>_. True)) (fm\<^sub>U Inr (\<lambda>_. True)))
                                  (pred_sum (pm\<^sub>T Inl (\<lambda>_. True)) (pm\<^sub>U Inr (\<lambda>_. True)))) \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Functional_Transformation_Functor_def Premise_def
  by (clarify; case_tac x; clarsimp)*)

lemma \<phi>Sum_Comm\<^sub>E [\<phi>reason %\<phi>type_algebra_prop_cut]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Transformation_def
  by (clarsimp simp add: split_sum_all)


subsection \<open>Additive Disjunction\<close>

text \<open>Depreciated! Use \<open>\<phi>Sum\<close> instead!\<close>

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
       and \<open>Identity_Elements\<^sub>I T D\<^sub>T P\<^sub>T
        \<Longrightarrow> Identity_Elements\<^sub>I U D\<^sub>U P\<^sub>U
        \<Longrightarrow> Identity_Elements\<^sub>I (T \<or>\<^sub>\<phi> U) (\<lambda>(x,y). D\<^sub>T x \<and> D\<^sub>U y) (\<lambda>(x,y). P\<^sub>T x \<or> P\<^sub>U y) \<close>
       and Identity_Elements
       and \<open> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T) \<and> y = undefined \<or>\<^sub>c\<^sub>u\<^sub>t
             (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U) \<and> x = undefined
          \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> T \<or>\<^sub>\<phi> U \<close>


(*       and \<open>\<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> P c \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x = f c @action to T)
        \<Longrightarrow> \<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> Q c \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U \<s>\<u>\<b>\<j> x. x = g c @action to U)
        \<Longrightarrow> \<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> P c \<or> Q c \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<or>\<^sub>\<phi> U \<s>\<u>\<b>\<j> y. y = (f c, g c) @action to (T \<or>\<^sub>\<phi> U))\<close>*)


subsubsection \<open>Configurations\<close>

declare \<phi>Union_def[embed_into_\<phi>type del]

lemma [embed_into_\<phi>type]:
  \<open>(x \<Ztypecolon> T) + (y \<Ztypecolon> U) \<equiv> (x,y) \<Ztypecolon> T \<or>\<^sub>\<phi> U\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp
 
let_\<phi>type \<phi>Union deriving \<open>Object_Equiv (\<circle> \<or>\<^sub>\<phi> \<circle>) (\<lambda>_ _. True)\<close>



subsection \<open>Embedding Additive Conjunction\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>Inter :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<and>\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T \<and>\<^sub>\<phi> U) = (\<lambda>x. (fst x \<Ztypecolon> T) \<and>\<^sub>B\<^sub>I (snd x \<Ztypecolon> U))\<close>
  deriving Basic
       and \<open>  Abstract_Domain T P
          \<Longrightarrow> Abstract_Domain U Q
          \<Longrightarrow> Abstract_Domain (T \<and>\<^sub>\<phi> U) (\<lambda>(x,y). P x \<and> Q y)\<close>
       (*and \<open>  Abstract_Domain\<^sub>L T P
          \<Longrightarrow> Abstract_Domain\<^sub>L U Q
          \<Longrightarrow> Abstract_Domain\<^sub>L (T \<and>\<^sub>\<phi> U) (\<lambda>(x,y). P x \<and> Q y)\<close>
         The lower bound of (T \<and>\<^sub>\<phi> U) is not derivable as there is no sufficiency reasoning for additive conjunction *)
       and \<open>  Object_Equiv T eqa
          \<Longrightarrow> Object_Equiv U eqb
          \<Longrightarrow> Object_Equiv (T \<and>\<^sub>\<phi> U) (\<lambda>(a1,b1) (a2,b2). eqa a1 a2 \<and> eqb b1 b2)\<close>
       and Identity_Elements
       and Functional_Transformation_Functor
       and (*Make_Abstraction_from_Raw (*TODO:simplification*)*)
          \<open> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> T \<and>\<^sub>\<phi> U \<close>

     (*DO NOT REMOVE, they are right but I'm thinking if we really should support so much additive conjunction
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


(* Commutativity of \<open>\<and>\<^sub>\<phi>\<close> cannot be derived simply from transformation functor. *)

lemma \<phi>Inter_comm\<^sub>E:
  \<open> Functional_Transformation_Functor F F\<^sub>T (T \<and>\<^sub>\<phi> U) T D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F F\<^sub>U (T \<and>\<^sub>\<phi> U) U D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F\<^sub>T F\<^sub>U \<phi>Inter \<phi>Inter T U
                     (\<lambda>x. (\<forall>a \<in> D\<^sub>T x. fst a \<in> R\<^sub>T x) \<and> (\<forall>a \<in> D\<^sub>U x. snd a \<in> R\<^sub>U x))
                     (embedded_func (\<lambda>x. (fm\<^sub>T fst (\<lambda>_. True) x, fm\<^sub>U snd (\<lambda>_. True) x))
                                    (\<lambda>x. pm\<^sub>T fst (\<lambda>_. True) x \<and> pm\<^sub>U snd (\<lambda>_. True) x))\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Functional_Transformation_Functor_def Premise_def
  apply clarify
  subgoal premises prems for x
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=fst], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2)[THEN spec[where x=x], THEN spec[where x=snd], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-);
        clarsimp simp add: Transformation_def) .



subsection \<open>Vertical Composition of Function\<close>

text \<open>It is a more specific form than \<open>\<phi>Fun f \<Zcomp> T\<close> whose automation rules are more general.\<close>

declare [[\<phi>trace_reasoning = 0]]

lemma [simp]: (*TODO: move me*)
  \<open>(case x of Inl x \<Rightarrow> Inl x | Inr x \<Rightarrow> Inr x) = x\<close>
  by (cases x; simp)

\<phi>type_def \<phi>Fun' :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close> (infixr "\<Zcomp>\<^sub>f" 30)
  where \<open>\<phi>Fun' f T = (\<phi>Fun f \<Zcomp> T)\<close>
  opening extract_premises_in_Carrier_Set
  deriving Basic
       and \<open> homo_one f \<and> Identity_Element\<^sub>I (x \<Ztypecolon> T) P \<or>\<^sub>c\<^sub>u\<^sub>t constant_1 f \<and> P = True \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> \<phi>Fun' f T) P \<close>
       and \<open> homo_one f \<and> Identity_Element\<^sub>E (x \<Ztypecolon> T) \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> \<phi>Fun' f T) \<close>
       and Functionality
       and Functional_Transformation_Functor
       (*and Trivial_\<Sigma>*)
       and \<open>homo_sep \<psi> \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL TEXT(\<open>Fail to derive \<close>) \<Longrightarrow> Separation_Homo\<^sub>E (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) T U (\<lambda>x. x)\<close>
       and \<open>homo_mul_carrier f \<Longrightarrow> Carrier_Set U P \<Longrightarrow> Carrier_Set (f \<Zcomp>\<^sub>f U) P \<close>
       and Abstraction_to_Raw
       and Commutativity_Deriver 
       and \<phi>Sum.Comm\<^sub>E

thm \<phi>Fun'.\<phi>Sum_Comm\<^sub>E

lemmas \<phi>Fun'_\<phi>Sum_comm_rewr = Comm_Tyops_Rewr\<^sub>2_temlpate[OF \<phi>Fun'.\<phi>Sum_Comm\<^sub>E \<phi>Fun'.\<phi>Sum_Comm\<^sub>I, simplified]


subsubsection \<open>Reasoning Rules\<close>

text \<open>The following rule is more general than \<open>\<phi>Fun f \<Zcomp> T\<close> as it in addition supports non-closed homomorphism.\<close>

declare [[\<phi>trace_reasoning = 2]]

lemma \<phi>Fun'_Separation_Homo\<^sub>I[\<phi>reason 1000]:
  \<open> homo_sep \<psi> \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL TEXT(\<open>Fail to derive the separation homomorphism of\<close> \<psi>)
\<Longrightarrow> closed_homo_sep_disj \<psi> \<and>\<^sub>\<r> Dx = UNIV \<or>\<^sub>c\<^sub>u\<^sub>t
    Separation_Disj\<^sub>\<phi> \<psi> Dx U T \<or>\<^sub>c\<^sub>u\<^sub>t
    TRACE_FAIL TEXT(\<open>Fail to derive the separation homomorphism of\<close> \<psi>)
\<Longrightarrow> Separation_Homo\<^sub>I (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) T U Dx (\<lambda>x. x) \<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
            Separation_Disj\<^sub>\<phi>_def Separation_Disj_def closed_homo_sep_def
            homo_sep_def closed_homo_sep_disj_def Ant_Seq_def
            homo_sep_mult_def homo_sep_disj_def Orelse_shortcut_def TRACE_FAIL_def
  by (clarsimp simp add: Ball_def; metis)

lemma \<phi>Fun'_Scalar_Assoc\<^sub>I:
  \<open> Semimodule_Scalar_Assoc\<^sub>I \<phi>Fun' \<phi>Fun' \<phi>Fun' T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (o) (\<lambda>_ _ x. x) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Transformation_def
  by clarsimp blast

lemma \<phi>Fun'_Scalar_Assoc\<^sub>E:
  \<open> Semimodule_Scalar_Assoc\<^sub>E \<phi>Fun' \<phi>Fun' \<phi>Fun' T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (o) (\<lambda>_ _ x. x) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Transformation_def
  by clarsimp blast

text \<open>Though \<open>\<phi>Fun'\<close> comprises an associative semimodule, we don not activate it in the reasoning
  system because its associative reduction is not expected in usual reasoning.
  Instead, we manually instantiate useful properties.\<close>

lemmas \<phi>Fun'_scalar_assoc = scalar_assoc_template[OF \<phi>Fun'_Scalar_Assoc\<^sub>I \<phi>Fun'_Scalar_Assoc\<^sub>E, simplified]

lemma (*TODO!*)
  \<open> fun_commute \<psi> \<phi> \<psi>' \<phi>'
\<Longrightarrow> (\<psi> \<Zcomp>\<^sub>f \<phi> \<Zcomp>\<^sub>f T) = (\<phi>' \<Zcomp>\<^sub>f \<psi>' \<Zcomp>\<^sub>f T)\<close>
  unfolding fun_commute_def
  by (simp add: \<phi>Fun'_scalar_assoc)

lemma \<phi>Fun'_comm[\<phi>reason %\<phi>type_algebra_properties]:
  \<open> fun_commute \<psi> \<phi> \<psi>' \<phi>'
\<Longrightarrow> Tyops_Commute (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>') (\<phi>Fun' \<phi>) (\<phi>Fun' \<phi>') T
                  (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))\<close>
  unfolding Tyops_Commute_def fun_commute_def
  by (simp add: \<phi>Fun'_scalar_assoc)


subsubsection \<open>Guessing Property\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute g f g' f'
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) (fun_commute g f g' f') True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute f g f' g'
\<Longrightarrow> Guess_Tyops_Commute\<^sub>E ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') G G' (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True\<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>E ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') G G' (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) (fun_commute f g f' g') True\<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..
  


(*TODO: move!*)

lemma
  \<open> inj \<psi>
\<Longrightarrow> x \<Ztypecolon> (\<psi> \<Zcomp>\<^sub>f T) \<and>\<^sub>\<phi> (\<psi> \<Zcomp>\<^sub>f U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<psi> \<Zcomp>\<^sub>f (T \<and>\<^sub>\<phi> U) \<close>
  unfolding Transformation_def inj_def
  by clarsimp blast


lemma \<comment> \<open>The above rule is reversible (for universally quantified x, T, U)\<close>
  \<open>(\<And>T U x. x \<Ztypecolon> (\<psi> \<Zcomp>\<^sub>f T) \<and>\<^sub>\<phi> (\<psi> \<Zcomp>\<^sub>f U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<psi> \<Zcomp>\<^sub>f (T \<and>\<^sub>\<phi> U)) \<Longrightarrow> inj \<psi>\<close>
  unfolding Transformation_def inj_def
  apply clarsimp
  subgoal premises prems for x y
    by (insert prems(1)[of _ \<open>\<lambda>_. {x}\<close> _ \<open>\<lambda>_. {y}\<close>]
               prems(2-),
        clarsimp simp add: \<phi>Type_def Satisfaction_def) .

lemma
  \<open> x \<Ztypecolon> \<psi> \<Zcomp>\<^sub>f (T +\<^sub>\<phi> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<psi> \<Zcomp>\<^sub>f T) +\<^sub>\<phi> (\<psi> \<Zcomp>\<^sub>f U) \<close>
  unfolding Transformation_def
  by (cases x; clarsimp)

(*
lemma
  \<open> fun_commute \<psi> \<phi>' \<psi>' \<phi>
\<Longrightarrow> (\<And>x. \<Psi>[\<psi>'] (x \<Ztypecolon> T) = (f x \<Ztypecolon> U))
\<Longrightarrow> \<Psi>[\<psi>] (x \<Ztypecolon> \<phi> \<Zcomp>\<^sub>f T) = (f x \<Ztypecolon> \<phi>' \<Zcomp>\<^sub>f U) \<close>
  unfolding \<phi>Fun'_def \<Psi>_comp
  apply (clarsimp simp add: fun_commute_def[unfolded fun_eq_iff, simplified])


lemma
  \<open> 
\<Longrightarrow> Domainoid_Homo\<^sub>U \<delta> (\<psi> \<Zcomp> T) dm' \<close>
*)




subsection \<open>Vertical Composition of Scalar Multiplication\<close>

declare [[\<phi>trace_reasoning = 0 ]]

\<phi>type_def \<phi>ScalarMul :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 's \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close> ("\<s>\<c>\<a>\<l>\<a>\<r>[_] _ \<Zcomp> _" [31,31,30] 30)
  where \<open>\<phi>ScalarMul f s T = (scalar_mult f s \<Zcomp>\<^sub>f T)\<close>
  deriving Basic
       and \<open> homo_one (f s) \<and> Identity_Element\<^sub>I (x \<Ztypecolon> T) P \<or>\<^sub>c\<^sub>u\<^sub>t constant_1 (f s) \<and> P = True
         \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) P \<close>
       and \<open> homo_one (f s)
         \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T)
         \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) \<close>
       and Functionality
       and Functional_Transformation_Functor
       (*and Trivial_\<Sigma>*)
       and Abstraction_to_Raw
       and \<open> homo_sep (scalar_mult \<psi> s) \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL TEXT(\<open>Fail to derive the separation homomorphism of\<close> (\<psi> s))
         \<Longrightarrow> closed_homo_sep_disj (scalar_mult \<psi> s) \<or>\<^sub>c\<^sub>u\<^sub>t
             Separation_Disj\<^sub>\<phi> (scalar_mult \<psi> s) Dx U T \<or>\<^sub>c\<^sub>u\<^sub>t
             TRACE_FAIL TEXT(\<open>Fail to derive the separation homomorphism of\<close> (\<psi> s))
         \<Longrightarrow> Separation_Homo\<^sub>I (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) T U Dx (\<lambda>x. x)\<close>
       and \<open> homo_sep (\<psi> s) \<or>\<^sub>c\<^sub>u\<^sub>t TRACE_FAIL TEXT(\<open>Fail to derive \<close>)
         \<Longrightarrow> Separation_Homo\<^sub>E (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) T U (\<lambda>x. x) \<close>
       and \<open> homo_mul_carrier (f s) \<Longrightarrow> Carrier_Set U P \<Longrightarrow> Carrier_Set (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> U) P \<close>
       and \<phi>Fun'.Comm
       and Commutativity_Deriver
       and \<phi>Sum.Comm\<^sub>E



subsubsection \<open>Reasoning Rules\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma Semimodule_Identity_by_function [\<phi>reason 1000]:
  \<open> module_scalar_identity \<psi>
\<Longrightarrow> Semimodule_Identity\<^sub>E (\<phi>ScalarMul \<psi>) T 1 (\<lambda>_. True) (\<lambda>x. x) \<close>
  unfolding Semimodule_Identity\<^sub>E_def module_scalar_identity_def scalar_mult_def BI_eq_iff
  by clarsimp

lemma Semimodule_Scalar_Assoc\<^sub>I_by_function[\<phi>reason 1000]:
  \<open> module_scalar_assoc \<psi> Ds
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) T Ds Ds (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) \<close>
  unfolding module_scalar_assoc_def Semimodule_Scalar_Assoc\<^sub>I_def scalar_mult_def Transformation_def
  by (clarsimp; blast)

lemma Semimodule_Scalar_Assoc\<^sub>E_by_function[\<phi>reason 1000]:
  \<open> module_scalar_assoc \<psi> Ds
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) T Ds Ds (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) \<close>
  unfolding module_scalar_assoc_def Semimodule_Scalar_Assoc\<^sub>E_def scalar_mult_def Transformation_def
  by clarsimp metis

declare [[\<phi>trace_reasoning = 0]]

lemma Semimodule_SDistr_Homo\<^sub>Z_by_function[\<phi>reason 1000]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Functionality T Dx
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> Abstract_Domain T D\<^sub>T
\<Longrightarrow> Carrier_Set T D\<^sub>C
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z (\<phi>ScalarMul \<psi>) T Ds
                            (\<lambda>s t (x,y). (D\<^sub>T x \<longrightarrow> D\<^sub>T y \<longrightarrow> eq x y \<and> Dx y \<and> D\<^sub>C y \<or> eq y x \<and> Dx x \<and> D\<^sub>C x))
                            (\<lambda>_ _. fst) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Transformation_def module_S_distr_def Is_Functional_def
            Object_Equiv_def Functionality_def Abstract_Domain_def Action_Tag_def Inhabited_def
            scalar_mult_def Carrier_Set_def Within_Carrier_Set_def
  by (clarsimp, metis)

text \<open>The domain of abstract objects constrains to ensure the two middle-level objects
  (namely, the concrete objects of \<open>T\<close> and the abstract objects of \<open>\<psi>\<close>) are identical so that
  we can apply the right distributive law \<open>smult (s + t) a = smult s a * smult t a\<close> of module,
  which requires the group objects \<open>a\<close> at the two sides of \<open>*\<close> to be identical.

  To this requirement, the instantiated domains above is the weakest.
\<close>

lemma \<comment> \<open>The instantiated domains above is the weakest upto using the \<open>module_S_distr \<psi> Ds\<close>,
          i.e., \<open>smult (s + t) a = smult s a * smult t a\<close>, when the \<open>Dx\<close>, \<open>eq\<close>, and \<open>D\<^sub>T\<close> are the weakest. \<close>
  \<open> (\<forall>x. p x \<longleftrightarrow> (\<forall>u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> u = v))
\<Longrightarrow> (\<forall>x y. eq x y \<longleftrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T))
\<Longrightarrow> (D\<^sub>Tx \<longleftrightarrow> (\<exists>u. u \<Turnstile> (x \<Ztypecolon> T))) \<and> (D\<^sub>Ty \<longleftrightarrow> (\<exists>u. u \<Turnstile> (y \<Ztypecolon> T)))
\<Longrightarrow> (\<forall>u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (y \<Ztypecolon> T) \<longrightarrow> u = v) \<longrightarrow> ((D\<^sub>Tx \<longrightarrow> eq x y \<and> p y) \<or> (D\<^sub>Ty \<longrightarrow> eq y x \<and> p x)) \<close>
  unfolding Transformation_def
  by auto metis
    
lemma Semimodule_SDistr_Homo\<^sub>U_by_function[\<phi>reason 1000]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Functionality T Dx
\<Longrightarrow> Abstract_Domain T D\<^sub>T
\<Longrightarrow> Carrier_Set T D\<^sub>C
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U (\<phi>ScalarMul \<psi>) T Ds
                            (\<lambda>s t x. D\<^sub>T x \<longrightarrow> Dx x \<and> D\<^sub>C x)
                            (\<lambda>_ _ x. (x,x))\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_def Transformation_def module_S_distr_def Is_Functional_def
            Object_Equiv_def Functionality_def Abstract_Domain_def Action_Tag_def Inhabited_def
            scalar_mult_def Carrier_Set_def Within_Carrier_Set_def
  by (clarsimp, metis)


subsubsection \<open>Commutativity\<close>

paragraph \<open>Guessing Property\<close>

text \<open>TODO: deriving the guessing rules\<close>

subparagraph \<open>\<open>\<phi>ScalarMul\<close> to \<open>\<phi>ScalarMul\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute (scalar_mult g t) (scalar_mult f s) (scalar_mult g' t') (scalar_mult f' s')
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g] t \<Zcomp> U) (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g'] t' \<Zcomp> U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         True True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g] t \<Zcomp> U) (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g'] t' \<Zcomp> U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         (fun_commute (scalar_mult g t) (scalar_mult f s) (scalar_mult g' t') (scalar_mult f' s')) True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute (scalar_mult f s) (scalar_mult g t) (scalar_mult f' s') (scalar_mult g' t')
\<Longrightarrow> Guess_Tyops_Commute\<^sub>E (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') G G' (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g] t \<Zcomp> U) (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g'] t' \<Zcomp> U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         True True\<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>E (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') G G' (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g] t \<Zcomp> U) (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g'] t' \<Zcomp> U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         (fun_commute (scalar_mult f s) (scalar_mult g t) (scalar_mult f' s') (scalar_mult g' t')) True\<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

subparagraph \<open>\<open>\<phi>ScalarMul\<close> to \<open>\<phi>Fun\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute g (scalar_mult f s) g' (scalar_mult f' s')
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         True True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         (fun_commute g (scalar_mult f s) g' (scalar_mult f' s')) True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute (scalar_mult f s) g (scalar_mult f' s') g'
\<Longrightarrow> Guess_Tyops_Commute\<^sub>E (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') G G' (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         True True\<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>E (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') G G' (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         (fun_commute (scalar_mult f s) g (scalar_mult f' s') g') True\<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..

subparagraph \<open>\<open>\<phi>Fun'\<close> to \<open>\<phi>ScalarMul\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute (scalar_mult g s) f (scalar_mult g' s') f'
\<Longrightarrow> Guess_Tyops_Commute\<^sub>I G G' ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g] s \<Zcomp> U) (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g'] s' \<Zcomp> U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         True True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>I G G' ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g] s \<Zcomp> U) (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g'] s' \<Zcomp> U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         (fun_commute (scalar_mult g s) f (scalar_mult g' s') f') True\<close>
  unfolding Guess_Tyops_Commute\<^sub>I_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute\<^sub>E ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') G G' (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g] s \<Zcomp> U) (\<lambda>U x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[g'] s' \<Zcomp> U) T
                         (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))
                         (fun_commute f (scalar_mult g s) f' (scalar_mult g' s')) True\<close>
  unfolding Guess_Tyops_Commute\<^sub>E_def ..


paragraph \<open>Deriving the Commutativity with Itself\<close>

let_\<phi>type \<phi>ScalarMul deriving \<phi>ScalarMul.Comm\<^sub>I


subsubsection \<open>Guessing Antecedents\<close>

lemma [\<phi>reason %\<phi>TA_guesser for \<open>Guess_Zip_of_Semimodule _ _ _ _ _ (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?\<psi>] s \<Zcomp> T) _ _ _ _ _ _ \<close>]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[\<psi>] s \<Zcomp> T) T Ds
                            (\<lambda>s t (x,y). (D\<^sub>T x \<longrightarrow> D\<^sub>T y \<longrightarrow> eq x y \<and> Dx y \<and> D\<^sub>C y \<or> eq y x \<and> Dx x \<and> D\<^sub>C x))
                            (\<lambda>_ _. fst)
                            (Functionality T Dx \<and>\<^sub>\<r> Object_Equiv T eq \<and>\<^sub>\<r> Abstract_Domain T D\<^sub>T \<and>\<^sub>\<r> Carrier_Set T D\<^sub>C)
                            True \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser for \<open>Guess_Unzip_of_Semimodule _ _ _ _ _ (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?\<psi>] s \<Zcomp> T) _ _ _ _ _ _ \<close>]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F (\<lambda>s T x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[\<psi>] s \<Zcomp> T) T Ds
                            (\<lambda>s t x. D\<^sub>T x \<longrightarrow> Dx x \<and> D\<^sub>C x)
                            (\<lambda>_ _ x. (x,x))
                            (Functionality T Dx \<and>\<^sub>\<r> Abstract_Domain T D\<^sub>T \<and>\<^sub>\<r> Carrier_Set T D\<^sub>C)
                            True \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..


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
       and Functional_Transformation_Functor
       (*and Trivial_\<Sigma>*)
       and Abstraction_to_Raw
       and \<phi>Sum.Comm\<^sub>E


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
       and Identity_Element
       and Abstraction_to_Raw


subsection \<open>Empty Type of Free Objects\<close>

(*
declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>None_freeobj :: \<open>('v::one, 'x) \<phi>\<close> ("\<circle>\<^sub>\<x>")
  where \<open> x \<Ztypecolon> \<circle>\<^sub>\<x> \<equiv> 1 \<close>
  deriving Basic
       and \<open> Identity_Element\<^sub>I (x \<Ztypecolon> \<circle>\<^sub>\<x>) True \<close>
       and \<open> Identity_Element\<^sub>E (x \<Ztypecolon> \<circle>\<^sub>\<x>) \<close>
       and Open_Abstraction_to_Raw

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
  deriving (*TODO!*)

text \<open>Again it is a form requiring satisfaction operator, and derivers are very limited on this.\<close>

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

declare [[\<phi>trace_reasoning = 0]]

   
\<phi>type_def List  :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List T) = (x \<Ztypecolon> T\<heavy_comma> l \<Ztypecolon> List T)\<close>
  deriving Separation_Monoid


declare [[\<phi>trace_reasoning = 3]]
   
                          
\<phi>type_def List\<^sub>S  :: \<open>nat \<Rightarrow> (fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List\<^sub>S n T) = (Void \<s>\<u>\<b>\<j> n = 0)\<close>
      | \<open>(x # l \<Ztypecolon> List\<^sub>S n T) = (x \<Ztypecolon> T\<heavy_comma> l \<Ztypecolon> List\<^sub>S (n - 1) T \<s>\<u>\<b>\<j> n = length l + 1)\<close>
      deriving \<open>Identity_Element\<^sub>I ([] \<Ztypecolon> List\<^sub>S n T) (n = 0)\<close>
           and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> n = 0 \<Longrightarrow> Identity_Element\<^sub>E ([] \<Ztypecolon> List\<^sub>S n T)\<close>
           and \<open>Identity_Element\<^sub>I (l \<Ztypecolon> List\<^sub>S n \<circle>) (n = length l)\<close>
           and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> n = length l \<Longrightarrow> Identity_Element\<^sub>E (l \<Ztypecolon> List\<^sub>S n \<circle>)\<close>
           and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (List\<^sub>S n T) (\<lambda>l. list_all P l \<and> n = length l) \<close>
           (*and Object_Equiv\<^sub>O*)
          (*and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (List\<^sub>S n T) (list_all2 eq)\<close>*)
term \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (List\<^sub>S n T) (\<lambda>l. list_all P l \<and> n = length l) \<close>

term \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> n = length l \<Longrightarrow> Identity_Element\<^sub>E (l \<Ztypecolon> List\<^sub>S n \<circle>)\<close>

term \<open>Identity_Element\<^sub>I (l \<Ztypecolon> List\<^sub>S n \<circle>) (n = length l)\<close>

term \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (List\<^sub>S n T) (list_all2 eq)\<close>


(*(*\<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (List\<^sub>S n T) (\<lambda>l. list_all P l \<and> n = length l)\<close>
      and*) Object_Equiv\<^sub>O*)

term \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (List\<^sub>S n T) (\<lambda>l. list_all P l \<and> n = length l)\<close>


(*setup \<open>Config.put_global Phi_Reasoner_solve_obligation_and_no_defer 3\<close>*)











       
       (*and \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 List List List (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>x. Ball (set x) isl \<or> (\<forall>b\<in>set x. \<not> isl b))
                            (embedded_func (\<lambda>x. if Ball (set x) isl then Inl (map projl x) else Inr (map projr x)) (list_all (\<lambda>_. True)))\<close>*)
(*Separation_Monoid*)
       (*and Trivial_\<Sigma>*)
       (*and SE_Trim_Empty*)

(*TODO: FIX ME!

  declare if_split_eq1[simp]
  deriving \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 List List List (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>x. Ball (set x) isl \<or> (\<forall>b\<in>set x. \<not> isl b))
 (embedded_func (\<lambda>x. if Ball (set x) isl then Inl (map projl x) else Inr (map projr x)) (list_all (\<lambda>_. True)))\<close>
  (*For some reason, the deriving fails here due to loosing certain conditions during the reasoning I believe,
    but I cannot figure it out now. I will lieave this and go back when I have time.*)
*)

thm List.\<phi>Sum_Comm\<^sub>E'

term \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 List List List (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>x. Ball (set x) isl \<or> (\<forall>b\<in>set x. \<not> isl b))
 (embedded_func (\<lambda>x. if Ball (set x) isl then Inl (map projl x) else Inr (map projr x)) (list_all (\<lambda>_. True)))\<close>

thm List.\<Sigma>\<^sub>E
thm List.\<Sigma>_rewr
thm List.functional_transformation

\<phi>type_def List3 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List3 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List3 T) = (x \<Ztypecolon> List T\<heavy_comma> l \<Ztypecolon> List3 T)\<close>
  deriving Separation_Monoid
       (*and SE_Trim_Empty*)
       (*and Trivial_\<Sigma>*)

thm List3.\<Sigma>\<^sub>E
thm List3.\<Sigma>_rewr
thm list.cases

    

(* BOSS:
\<phi>type_def List2 :: \<open>(fiction,'a) \<phi> \<Rightarrow> (fiction, 'a list list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> List2 T) = Void\<close>
      | \<open>(x # l \<Ztypecolon> List2 T) = (prod (\<lambda>x. x \<Ztypecolon> T) (set x)\<heavy_comma> l \<Ztypecolon> List2 T)\<close>
*)
 
declare [[\<phi>trace_reasoning = 0]]
       
\<phi>type_def rounded_Nat :: \<open>nat \<Rightarrow> (nat,nat) \<phi>\<close>
  where \<open>(x \<Ztypecolon> rounded_Nat m) = (x mod m \<Ztypecolon> Itself)\<close>
  deriving Basic
       and Make_Abstraction_from_Raw


declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 75)
  where \<open>\<phi>MapAt k T = (fun_upd 1 k \<Zcomp>\<^sub>f T)\<close>
  deriving Separation_Monoid
       and Functionality
       and Abstraction_to_Raw
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm

thm \<phi>MapAt.\<Sigma>_rewr

subsubsection \<open>By List of Keys\<close>

declare [[\<phi>trace_reasoning = 1]]
         
\<phi>type_def \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 75)
  where \<open>\<phi>MapAt_L k T = (\<s>\<c>\<a>\<l>\<a>\<r>[push_map] k \<Zcomp> T)\<close>
  deriving Separation_Monoid
       and Functionality
       (*and Trivial_\<Sigma>*)
       and Semimodule_NonDistr_no0
       and Abstraction_to_Raw

thm \<phi>MapAt_L.\<Sigma>\<^sub>E
thm \<phi>MapAt_L.\<Sigma>_rewr

abbreviation \<phi>MapAt_L1 :: \<open>'key \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>#" 75)
  where \<open>\<phi>MapAt_L1 key \<equiv> \<phi>MapAt_L [key]\<close>

abbreviation \<phi>MapAt_Lnil :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>[\<^sub>]" 75)
  where \<open>\<phi>MapAt_Lnil key T \<equiv> \<phi>MapAt_L [key] (\<phi>MapAt [] T)\<close>

paragraph \<open>Simplification\<close>

lemma \<phi>MapAt_L_At:
  \<open>(ks \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) = (ks \<^bold>\<rightarrow> T)\<close>
  by (rule \<phi>Type_eqI; simp add: scalar_mult_def; metis append_self_conv push_map_unit)


paragraph \<open>Implication \& Action Rules\<close>


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



subsection \<open>Permission Sharing\<close>

declare [[\<phi>trace_reasoning = 0 ]]

text \<open>TODO: Perhaps we need a class for all homomorphic-morphism-based \<phi>-types.\<close>

   
\<phi>type_def \<phi>Share :: \<open>rat \<Rightarrow> ('c::share,'a) \<phi> \<Rightarrow> ('c, 'a) \<phi>\<close> (infixr "\<odiv>" 75)
  where \<open>\<phi>Share n T = (\<s>\<c>\<a>\<l>\<a>\<r>[share] n \<Zcomp> T \<phi>\<s>\<u>\<b>\<j> 0 < n)\<close>
  deriving Separation_Monoid
       and Functionality
       (*and SE_Trim_Empty*)
       and Semimodule_no0
       and \<open>(\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> Carrier_Set T P) \<Longrightarrow> Carrier_Set (n \<odiv> T) (\<lambda>x. 0 < n \<longrightarrow> P x)\<close>
       and Abstraction_to_Raw
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm
       and \<phi>MapAt.Comm

thm \<phi>Share.\<Sigma>_rewr
thm \<phi>Fun'.\<phi>Fun'.comm_rewr
thm \<phi>MapAt.\<phi>Share.comm_rewr

declare [[\<phi>trace_reasoning = 3]]

thm \<phi>Share.Identity_Element\<^sub>I
thm \<phi>Share.unfold_sdistr (*TODO: reduce identical antecedents*)
thm \<phi>Share.\<phi>Prod
thm \<phi>Share.\<phi>None
thm \<phi>Share.scalar_assoc
thm \<phi>Share.scalar_one
thm \<phi>Share.Semimodule_Scalar_Assoc\<^sub>E


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

(*TODO:
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
*)

thm \<phi>Share.\<phi>None


(*
lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> ?n \<odiv> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action (?Act::?'b::simplification action)\<close>]:
  \<open>x \<Ztypecolon> n \<odiv> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>) @action Act\<close>
  for Act :: \<open>'b::simplification action\<close>
  unfolding Transformation_def Action_Tag_def
  by (simp add: \<phi>expns) *)


paragraph \<open>Implication \& Action Rules\<close>


(* TODO:
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
*)


paragraph \<open>Simplifications\<close>

(* TODO:
lemma [simp]:
  \<open>(n \<odiv> ExTyp T) = (\<exists>\<phi> c. n \<odiv> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)
*)

thm \<phi>Share.\<S>\<^sub>E
thm \<phi>Share.\<S>\<^sub>I
thm \<phi>Share.\<phi>subj
thm \<phi>Share.simp_cong




section \<open>Semantics Related\<close>

subsection \<open>Value\<close>

subsubsection \<open>Syntax to fetch the latest n-th Val\<close>

(*where I moved it? the function seems still useful*)

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



(* not need any more
subsection \<open>Morphism of Separation Homomorphism\<close>

declare [[\<phi>trace_reasoning = 3]]

\<phi>type_def \<phi>sep_homo :: \<open>('a::sep_magma \<Rightarrow> 'c::sep_magma) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close>
  where \<open>\<phi>sep_homo \<psi> T = (\<phi>Fun \<psi> \<Zcomp> T \<phi>\<s>\<u>\<b>\<j> homo_sep \<psi>)\<close>
  deriving Implication
       (*and Is_Functional
       and Open_Abstraction_to_Raw*)

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
  using homo_sep.axioms(1) homo_sep.axioms(2) homo_sep_disj_def homo_sep_mult_def apply blas


  

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

*)

section \<open>Permission \& Share\<close>

subsection \<open>Share \& Option\<close>

(* replaced by domainoid
subsubsection \<open>Definition of Properties\<close>

definition \<phi>Sep_Disj :: \<open>('a::sep_magma,'b1) \<phi> \<Rightarrow> ('a,'b2) \<phi> \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj T U \<longleftrightarrow> (\<forall>x y u v. u \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (y \<Ztypecolon> U) \<longrightarrow> (\<exists>u' v'. u' \<Turnstile> (x \<Ztypecolon> T) \<and> v' \<Turnstile> (y \<Ztypecolon> U) \<and> u' ## v'))\<close>

definition \<phi>Sep_Disj_Inj :: \<open>'a::share_nun_semimodule set \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj_Inj S \<longleftrightarrow> (\<forall>u v. u \<Turnstile> S \<and> v \<Turnstile> S \<and> u ## v \<longrightarrow> u = v) \<and> (\<forall>u. u \<Turnstile> S \<longrightarrow> u ## u)\<close>

subsubsection \<open>The \<phi>-Type of Separation Homomorphism\<close>
*)


thm share_orthogonal_homo_to_share

(* not need
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
*)


subsection \<open>To-Share\<close>

declare [[\<phi>trace_reasoning = 3]]

\<phi>type_def To_Share
  where \<open>To_Share T \<equiv> (to_share \<Zcomp>\<^sub>f T)\<close>
  deriving (*Basic
       and Functional_Transformation_Functor
       and Identity_Element
       and*) Separation_Homo\<^sub>E


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

instantiation uninit :: (discrete_semigroup) discrete_semigroup begin
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
