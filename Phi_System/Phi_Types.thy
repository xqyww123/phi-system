chapter \<open>Pre-built \<phi>-Types\<close>

theory Phi_Types
  imports Phi_Type "List-Index.List_Index"
begin

section \<open>Preliminary\<close>

consts \<phi>coercion :: \<open>('c1,'a) \<phi> \<Rightarrow> ('c2,'a) \<phi>\<close> ("\<coercion> _" [61] 60)
  \<comment> \<open>merely a syntax sugar to be overloaded.\<close>

ML \<open>Phi_Conv.set_rules__type_form_to_ex_quantified [] ;
    Phi_Conv.set_rules__type_form_to_ex_quantified_single_var [] \<close>

section \<open>Basics\<close>

subsection \<open>Itself\<close> \<comment> \<open>together with the vertical composition forms the only primitives in the algbera of \<phi>-Types\<close>

lemma Itself_is_primitive: \<open>x \<Ztypecolon> Itself \<equiv> x \<Ztypecolon> Itself\<close> .

ML \<open>(Thm.transfer \<^theory> @{thm' Itself_is_primitive})\<close>

local_setup \<open>
  Phi_Type.add_type {no_auto=true}
        (\<^binding>\<open>Itself\<close>, \<^pattern>\<open>Itself\<close>, Phi_Type.DIRECT_DEF (Thm.transfer \<^theory> @{thm' Itself_is_primitive}),
         \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>

text \<open>No deriver is available on \<open>Itself\<close>, and they will trap in infinite loops because the fake
  definition \<open>Itself_is_primitive\<close> given to the deriving engine is infinitely recursive.\<close>


subsection \<open>Embedding of Empty\<close>

lemma \<phi>None_def': \<open> (x \<Ztypecolon> \<circle>) = (1 \<Ztypecolon> Itself) \<close>
  by (simp add: BI_eq_iff)

local_setup \<open>
  Phi_Type.add_type {no_auto=false}
      (\<^binding>\<open>\<phi>None\<close>, \<^pattern>\<open>\<phi>None\<close>, Phi_Type.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>None_def'}),
       \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>

declare [[\<phi>trace_reasoning = 0]]

let_\<phi>type \<phi>None
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and Identity_Elements
       and Abstraction_to_Raw
       and \<open>1 \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?xa \<Ztypecolon> \<circle>\<close>


subsection \<open>Embedding of \<open>\<top>\<close>\<close>

local_setup \<open>
  Phi_Type.add_type {no_auto=false}
      (\<^binding>\<open>\<phi>Any\<close>, \<^pattern>\<open>\<phi>Any::(?'c, ?'x) \<phi>\<close>, Phi_Type.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>Any_def}),
       \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>

let_\<phi>type \<phi>Any
  deriving Basic
       and Abstract_Domain\<^sub>L


subsection \<open>Embedding of \<open>\<bottom>\<close>\<close>

declare \<phi>Bot_def[embed_into_\<phi>type]

local_setup \<open>
  Phi_Type.add_type {no_auto=false}
        (\<^binding>\<open>\<phi>Bot\<close>, \<^pattern>\<open>\<phi>Bot::(?'c,?'a) \<phi>\<close>, Phi_Type.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>Bot_def}),
         \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>
 
let_\<phi>type \<phi>Bot
  deriving Basic
       and \<open>Abstract_Domain \<bottom>\<^sub>\<phi> (\<lambda>x. False)\<close>
       and \<open>Abstract_Domain\<^sub>L \<bottom>\<^sub>\<phi> (\<lambda>x. False)\<close>
       and Functionality
       and Carrier_Set


subsection \<open>\<phi>Prod\<close>

local_setup \<open>
  Phi_Type.add_type {no_auto=false}
        (\<^binding>\<open>\<phi>Prod\<close>, \<^pattern>\<open>\<phi>Prod::(?'c::sep_magma,?'a\<^sub>1) \<phi> \<Rightarrow> (?'c,?'a\<^sub>2) \<phi> \<Rightarrow> (?'c,?'a\<^sub>1 \<times> ?'a\<^sub>2) \<phi>\<close>,
         Phi_Type.DIRECT_DEF (Thm.transfer \<^theory>
            @{lemma' \<open>(x \<Ztypecolon> T \<^emph> U) = (fst x \<Ztypecolon> T) * (snd x \<Ztypecolon> U)\<close>
                      for T :: \<open>('c::sep_magma,'a\<^sub>1) \<phi>\<close> and U :: \<open>('c::sep_magma,'a\<^sub>2) \<phi>\<close>
                  by (simp add: \<phi>Prod_expn'')}),
         \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>

declare [[\<phi>trace_reasoning = 0]]

let_\<phi>type \<phi>Prod
  deriving Basic
       and Functional_Transformation_Functor
       and Functionality
       and \<open>  Object_Equiv T er
          \<Longrightarrow> Object_Equiv U eq
          \<Longrightarrow> Object_Equiv (T \<^emph> U) (\<lambda>x y. er (fst x) (fst y) \<and> eq (snd x) (snd y))\<close>

subsection \<open>Func\<close>
 
\<phi>type_def \<phi>Fun :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('c,'a) \<phi>\<close>
  where \<open>\<phi>Fun f x = (f x \<Ztypecolon> Itself)\<close>
  deriving \<open>Identity_Elements\<^sub>E (\<phi>Fun f) (\<lambda>x. f x = 1)\<close>
       and \<open>Identity_Elements\<^sub>I (\<phi>Fun f) (\<lambda>x. f x = 1) (\<lambda>_. True)\<close>
       and Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and Abstraction_to_Raw
       and \<open>?f ?xa \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?xa \<Ztypecolon> \<phi>Fun ?f\<close>



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


subsection \<open>Embedding of Subjection\<close>

\<phi>type_def SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<s>\<u>\<b>\<j>" 25)
  where [embed_into_\<phi>type]: \<open> (T \<phi>\<s>\<u>\<b>\<j> P) = (\<lambda>x. x \<Ztypecolon> T \<s>\<u>\<b>\<j> P) \<close>
  deriving Sep_Functor_1
       and Abstract_Domain\<^sub>L
       and Functionality
       and Carrier_Set


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
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> x \<Ztypecolon> T \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> P) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def \<phi>Prod'_def
  by (cases x; clarsimp; blast)

lemma [\<phi>reason %ToA_red]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q \<close>
  unfolding Transformation_def
  by clarsimp

lemma [\<phi>reason %ToA_red]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<OTast> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> Q)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<phi>\<s>\<u>\<b>\<j> Q) \<OTast> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def Premise_def \<phi>Prod'_def
  by clarsimp

subsubsection \<open>Algebraic Properties\<close>

text \<open>Here we construct two inner transformations from \<open>a \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P\<close> to \<open>a \<Ztypecolon> T\<close> and another reversely.
  It is essentially an identity transformation from \<open>a\<close> to \<open>a\<close> itself.
  The constraints checks 1. if the identity transformation is supported (a very weak requirement),
        2. the container is always non-empty so that an independent assertion \<open>P\<close> bound at the element
           type is valid globally (this is a necessary condition).  \<close>

lemma \<phi>\<s>\<u>\<b>\<j>_Homo[\<phi>reason_template name Fa.\<phi>subj [assertion_simps]]:
  \<open> Functional_Transformation_Functor Fa Fa (T \<phi>\<s>\<u>\<b>\<j> P) T D R pm fm
\<Longrightarrow> Functional_Transformation_Functor Fa Fa T (T \<phi>\<s>\<u>\<b>\<j> P) D R pm fm
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a. a \<in> D x \<longrightarrow> a \<in> R x) \<and> (fm (\<lambda>x. x) (\<lambda>_. P) x = x \<and> pm (\<lambda>x. x) (\<lambda>_. P) x = P)
\<Longrightarrow> (x \<Ztypecolon> Fa (T \<phi>\<s>\<u>\<b>\<j> P)) = (x \<Ztypecolon> Fa T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Functional_Transformation_Functor_def Transformation_def atomize_eq Premise_def BI_eq_iff
  apply (clarsimp; rule)
  subgoal premises prems for p
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp)
  subgoal premises prems for p
    by (insert prems(2)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp) .

lemma \<phi>\<s>\<u>\<b>\<j>_Homo_ty[\<phi>reason_template name Fa.\<phi>subj_ty [assertion_simps]]:
  \<open> Functional_Transformation_Functor Fa Fa (T \<phi>\<s>\<u>\<b>\<j> P) T D R pm fm
\<Longrightarrow> Functional_Transformation_Functor Fa Fa T (T \<phi>\<s>\<u>\<b>\<j> P) D R pm fm
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a x. a \<in> D x \<longrightarrow> a \<in> R x) \<and> (\<forall>x. fm (\<lambda>x. x) (\<lambda>_. P) x = x \<and> pm (\<lambda>x. x) (\<lambda>_. P) x = P)
\<Longrightarrow> Fa (T \<phi>\<s>\<u>\<b>\<j> P) = (Fa T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  unfolding Functional_Transformation_Functor_def atomize_eq Premise_def BI_eq_iff
  apply (rule \<phi>Type_eqI_Tr; clarsimp simp add: Transformation_def)
  subgoal premises prems for x v
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp,
        blast)
  subgoal premises prems for x v
    by (insert prems(2)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>x. x\<close>], THEN spec[where x=\<open>\<lambda>_. P\<close>]]
               prems(3-),
        clarsimp) .

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x \<and> P @tag \<A>_transitive_simp\<close>
  unfolding Transformation_Functor_def Transformation_def Action_Tag_def
  by simp

paragraph \<open>Commutativity\<close>

lemma [\<phi>reason_template name G.\<phi>\<s>\<u>\<b>\<j>\<^sub>E]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor G G' T (T \<phi>\<s>\<u>\<b>\<j> P) D R pm fm
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D' : (\<lambda>x. \<forall>a \<in> D x. a \<in> R x) @tag \<A>_template_reason undefined
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' : embedded_func (fm (\<lambda>x. x) (\<lambda>_. True)) (\<lambda>_. True) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P) G G' T D' r' \<close>
  unfolding Action_Tag_def Simplify_def \<r>Guard_def
            Functional_Transformation_Functor_def Transformation_def Tyops_Commute_def
  by clarsimp

lemma [\<phi>reason_template name F.\<phi>\<s>\<u>\<b>\<j>\<^sub>I]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F F' (T \<phi>\<s>\<u>\<b>\<j> P) T D R pm fm
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D' : (\<lambda>x. (\<forall>a \<in> D x. a \<in> R x) \<and> (pm (\<lambda>x. x) (\<lambda>_. P) x \<longrightarrow> P)) @tag \<A>_template_reason undefined
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' : embedded_func (fm (\<lambda>x. x) (\<lambda>_. P)) (\<lambda>_. True) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute F F' (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P) (\<lambda>T. T \<phi>\<s>\<u>\<b>\<j> P) T D' r' \<close>
  unfolding Action_Tag_def Simplify_def \<r>Guard_def
            Functional_Transformation_Functor_def Transformation_def Tyops_Commute_def
  by clarsimp


subsubsection \<open>Guessing Antecedents\<close>

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Property PC False T' (\<lambda>x. f x \<Ztypecolon> T x) a p c
\<Longrightarrow> Guess_Property PC False T' (\<lambda>x. f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x) a p (\<lambda>x. P x \<and> c x)\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Property PC True T' (\<lambda>x. f x \<Ztypecolon> T x) a p c
\<Longrightarrow> Guess_Property PC True T' (\<lambda>x. f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x) a (\<lambda>x. P x \<and> p x) c\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Zip_of_Semimodule TS TC TA F (\<lambda>s x. f s x \<Ztypecolon> T' s x) Ds Dx zi ants conds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA F (\<lambda>s x. f s x \<Ztypecolon> T' s x \<phi>\<s>\<u>\<b>\<j> P s x)
                            Ds (\<lambda>s t (x,y). P s x \<and> P t y \<longrightarrow> Dx s t (x,y)) zi ants conds \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason default %\<phi>TA_guesser]:
  \<open> Guess_Unzip_of_Semimodule TS TC TA F (\<lambda>s x. f s x \<Ztypecolon> T' s x) Ds Dx zi ants conds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA F (\<lambda>s x. f s x \<Ztypecolon> T' s x \<phi>\<s>\<u>\<b>\<j> P s x)
                              Ds (\<lambda>s t xy. P (s + t) xy \<longrightarrow> Dx s t xy) zi ants conds \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

paragraph \<open>Commutativity between Tyoprs\<close>

subparagraph \<open>\<open>Guess_Tyops_Commute\<^sub>I\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P) G_def' uF uF' T
                        (\<lambda>x. P \<longrightarrow> D x) r ants (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<and>\<^sub>\<r> conds) \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P x) G_def' uF uF' T
                        (\<lambda>x. P x \<longrightarrow> D x) r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P' T x) uF uF' T D r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P') uF uF' T D r (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P' \<and>\<^sub>\<r> ants) conds \<close>
  unfolding Guess_Tyops_Commute_def ..

subparagraph \<open>\<open>Guess_Tyops_Commute\<^sub>E\<close>\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P) G_def' T
                        (\<lambda>x. P \<longrightarrow> D x) r ants (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<and>\<^sub>\<r> conds) \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T) G_def' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' (\<lambda>T x. g x \<Ztypecolon> G_def T \<phi>\<s>\<u>\<b>\<j> P x) G_def' T D r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P' T x) T D r ants conds \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T) T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' G_def (\<lambda>T x. g' x \<Ztypecolon> G_def' T \<phi>\<s>\<u>\<b>\<j> P') T D r (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P' \<and>\<^sub>\<r> ants) conds \<close>
  unfolding Guess_Tyops_Commute_def ..


subsection \<open>Dependent Sum Type\<close>

\<phi>type_def \<phi>Dependent_Sum :: \<open>('c \<Rightarrow> ('a,'b) \<phi>) \<Rightarrow> ('a, 'c \<times> 'b) \<phi>\<close> ("\<Sigma>")
  where \<open>cx \<Ztypecolon> \<Sigma> T \<equiv> (snd cx) \<Ztypecolon> T (fst cx)\<close>
  deriving Basic
    and \<open> (\<And>A. Object_Equiv (T A) (eq A))
      \<Longrightarrow> Object_Equiv (\<Sigma> T) (\<lambda>x y. fst y = fst x \<and> eq (fst x) (snd x) (snd y))\<close>
    and \<open>(\<And>A. Abstract_Domain (T A) (P A)) \<Longrightarrow> Abstract_Domain (\<Sigma> T) (\<lambda>x. P (fst x) (snd x))\<close>
    and \<open>(\<And>A. Abstract_Domain\<^sub>L (T A) (P A)) \<Longrightarrow> Abstract_Domain\<^sub>L (\<Sigma> T) (\<lambda>x. P (fst x) (snd x))\<close>
    and Identity_Elements
    and \<open>(\<And>i. Functionality (T i) (P i)) \<Longrightarrow> Functionality (\<Sigma> T) (\<lambda>x. P (fst x) (snd x))\<close>
    and \<open>(\<And>p. Carrier_Set (T p) (P p)) \<Longrightarrow> Carrier_Set (\<Sigma> T) (\<lambda>x. P (fst x) (snd x)) \<close> \<comment> \<open>Gusser fails to
                    realize the predicate \<open>P\<close> can also be parameterized, which is a specific feature of the dependent sum\<close>
    and Abstraction_to_Raw
    and \<open>(\<And>a c. a \<Ztypecolon> T c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Itself \<s>\<u>\<b>\<j> b. r a b c @tag to Itself)
      \<Longrightarrow> \<forall>(x::?'b \<times> ?'a). x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>b. r (snd x) b (fst x) \<and> y = b) @tag to Itself \<close>
    and \<open>(\<And>A. c A \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y A \<Ztypecolon> T A)
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (y a = x)
      \<Longrightarrow> c a \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (a,x) \<Ztypecolon> \<Sigma> T \<close>

notation \<phi>Dependent_Sum (binder "\<Sigma> " 22)


subsubsection \<open>Properties Failed to be Derived\<close>

lemma \<phi>Dependent_Sum_TF[\<phi>type_property \<phi>Dependent_Sum Transformation_Functor]:
  \<open>Transformation_Functor\<^sub>\<Lambda> \<Sigma> \<Sigma> T U (\<lambda>p x. if fst x = p then {snd x} else {}) (\<lambda>_ _. UNIV)
                                    (\<lambda>r x. rel_prod (=) (r (fst x)) x)\<close>
  unfolding Transformation_Functor\<^sub>\<Lambda>_def Transformation_def
  by clarsimp
 
context begin

lemma \<phi>Dependent_Sum_SH\<^sub>I[\<phi>type_property \<phi>Dependent_Sum Separation_Homo\<^sub>I]:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>I \<Sigma> \<Sigma> \<Sigma> T U {x. fst (fst x) = fst (snd x)} (\<lambda>x. (fst (fst x), (snd (fst x), snd (snd x)))) \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_def Transformation_def
  by clarsimp

lemma \<phi>Dependent_Sum_SH\<^sub>E[\<phi>type_property \<phi>Dependent_Sum Separation_Homo\<^sub>E]:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>E \<Sigma> \<Sigma> \<Sigma> T U (\<lambda>x. ((fst x, fst (snd x)), (fst x, snd (snd x)))) \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_def Transformation_def
  by clarsimp

let_\<phi>type \<phi>Dependent_Sum
  deriving \<open>Functional_Transformation_Functor\<^sub>\<Lambda> \<Sigma> \<Sigma> T U (\<lambda>p x. if fst x = p then {snd x} else {}) (\<lambda>_ _. UNIV)
                                                        (\<lambda>f P. case_prod P)
                                                        (\<lambda>f P x. apsnd (f (fst x)) x)\<close>

end

subsubsection \<open>Rewrites\<close>

declare \<phi>Dependent_Sum.unfold [embed_into_\<phi>type, \<phi>programming_base_simps, assertion_simps, simp]

lemma \<phi>\<s>\<u>\<b>\<j>_over_\<Sigma>[\<phi>programming_simps]:
  \<open>\<Sigma> x. (T x \<phi>\<s>\<u>\<b>\<j> P) \<equiv> (\<Sigma> T) \<phi>\<s>\<u>\<b>\<j> P\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI, simp)

subsubsection \<open>ToA Reasoning\<close>

lemma [\<phi>reason add]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @clean
\<Longrightarrow> (a, x) \<Ztypecolon> \<Sigma> (\<lambda>_. T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @clean \<close> 
  by simp

lemma [\<phi>reason add]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U @clean
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (a,y) \<Ztypecolon> \<Sigma> (\<lambda>_. U) @clean \<close>
  by simp

lemma [\<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<OTast> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>
                        \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((_, _), _) \<Ztypecolon> \<Sigma> _ \<OTast> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T a \<OTast> R a \<w>\<i>\<t>\<h> P @tag \<T>\<P>'
\<Longrightarrow> (a, snd y) \<Ztypecolon> \<Sigma> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> r' \<Ztypecolon> R' @clean
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((a, fst y), r') \<Ztypecolon> \<Sigma> T \<OTast> R' \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Transformation_def Action_Tag_def \<phi>Prod'_def
  by clarsimp blast

lemma [\<phi>reason 1100 for \<open>_ \<Ztypecolon> \<Sigma> _ \<OTast> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>]:
  \<open> PROP Reduce_HO_trivial_variable (Trueprop (
      (snd (fst x), snd (snd x)) \<Ztypecolon> T (fst (fst x)) \<OTast> W (fst (fst x)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>'))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst (snd x) = fst (fst x)
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<OTast> \<Sigma> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>'\<close>
  unfolding Premise_def Transformation_def Reduce_HO_trivial_variable_def Action_Tag_def \<phi>Prod'_def
  by clarsimp

(*


lemma [\<phi>reason 1010 for \<open>((_,_),_) \<Ztypecolon> \<Sigma> _ \<OTast> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>]:
  \<open> PROP Reduce_HO_trivial_variable (Trueprop (
      (b, snd w) \<Ztypecolon> T a \<OTast> W a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>'))
\<Longrightarrow> w' \<Ztypecolon> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<Sigma> W @clean
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst w = a
\<Longrightarrow> ((a, b), w') \<Ztypecolon> \<Sigma> T \<OTast> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Premise_def Transformation_def Reduce_HO_trivial_variable_def Action_Tag_def \<phi>Prod'_def
  by clarsimp blast
*)

declare [[\<phi>chk_source_val = false]]

declare \<phi>Dependent_Sum.intro_reasoning(1)
        [where x=\<open>(a,b)\<close> for a b, simplified apfst_conv apsnd_conv fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>]

        \<phi>Dependent_Sum.intro_reasoning\<^sub>R
        [where x=\<open>(a,b)\<close> for a b, simplified fst_conv snd_conv,
         \<phi>reason 1000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_, _) \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>
                          \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<Ztypecolon> \<Sigma> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>
                       \<comment> \<open>There are no contextual bound vars only parameterizing the objects,
                           so the rules are safe.\<close>
        ]

        \<phi>Dependent_Sum.elim_reasoning(1)[\<phi>reason 1000 for \<open>_ \<Ztypecolon> \<Sigma> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P> \<close>]
        \<phi>Dependent_Sum.elim_reasoning(1)
        [where x=\<open>(a,b)\<close> for a b, simplified fst_conv snd_conv,
         \<phi>reason 1010 for \<open>(_, _) \<Ztypecolon> \<Sigma> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>]

declare [[\<phi>chk_source_val]]



subsubsection \<open>Quasi Functor Properties\<close>

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

lemma \<Sigma>_pseudo_Functional_Transformation_Functor:
  \<open> snd x \<Ztypecolon> T (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U c \<w>\<i>\<t>\<h> P 
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (c,y) \<Ztypecolon> \<Sigma> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def
  by (cases x; clarsimp)

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



paragraph \<open>Manual Instantiation of Reasoning Rules\<close>

lemma \<Sigma>_simp_cong[\<phi>simp_cong]:
  \<open> x \<Ztypecolon> T c\<^sub>x \<equiv> y \<Ztypecolon> U c\<^sub>y
\<Longrightarrow> (c\<^sub>x,x) \<Ztypecolon> \<Sigma> T \<equiv> (c\<^sub>y,y) \<Ztypecolon> \<Sigma> U \<close>
  by clarsimp

subparagraph \<open>To-Transformation\<close>

text \<open>To-Transformation is still type-directed and the target type \<open>U\<close> is inferred according to the
  instruction of the annotation \<open>to \<T>\<close>. In case of \<open>\<Sigma>\<close>, the thing is \<open>to (\<Sigma> c. \<T> c)\<close> does not fix
  the parameter of \<open>\<T>\<close> because the parameter \<open>c\<close> is from object, and the parameter cannot be left unknown
  to expect some instantiation in the later reasoning because \<open>U\<close> is also unknown having to be inferred,
  causing higher order unknowns \<open>U c\<close> which are undecidable and usually not uniquely determined.
  More annotations have to be given from user.
  We invent syntax \<open>\<Sigma> c. \<T> c \<p>\<a>\<r>\<a>\<m>: f\<close> to annotate the target parameter by a function \<open>f\<close> over the
  source object, supporting dynamic choice of the parameter.
\<close>

definition Param_Annot :: \<open>'a::{} \<Rightarrow> 'p::{} \<Rightarrow> 'a::{}\<close> (infix "\<p>\<a>\<r>\<a>\<m>:" 60)
  where \<open>x \<p>\<a>\<r>\<a>\<m>: p \<equiv> x\<close>

lemma [\<phi>reason %To_ToA_cut+20]:
  \<open> WARNING TEXT(\<open>The parameter of the \<open>\<Sigma>\<close> type is not annotated. To prevent higher-order unknowns,\<close>
                 \<open>we assume the parameter is unchanged throughout the To-Transformation.\<close>)
\<Longrightarrow> PROP Reduce_HO_trivial_variable (Trueprop (
        snd x \<Ztypecolon> T (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U (fst x) \<s>\<u>\<b>\<j> b. g b @tag to (Z (fst x))))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> U \<s>\<u>\<b>\<j> y. fst y = fst x \<and> g (snd y) @tag to (\<Sigma> Z) \<close>
  unfolding Action_Tag_def Transformation_def Reduce_HO_trivial_variable_def
  by clarsimp

lemma \<Sigma>_To_Transformation[\<phi>reason %To_ToA_cut+30]:
  \<open> PROP Reduce_HO_trivial_variable (Trueprop (
        snd x \<Ztypecolon> T (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U (f x) \<s>\<u>\<b>\<j> b. g b @tag to (Z (f x))))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> U \<s>\<u>\<b>\<j> y. fst y = f x \<and> g (snd y) @tag to (\<Sigma> Z \<p>\<a>\<r>\<a>\<m>: f) \<close>
  unfolding Action_Tag_def Transformation_def Reduce_HO_trivial_variable_def
  by clarsimp

lemma \<Sigma>_To_Transformation_fuzzy[\<phi>reason %To_ToA_cut+10]:
  \<open> NO_MATCH TYPE('c\<^sub>a\<^sub>a) TYPE('c) 
\<Longrightarrow> PROP Reduce_HO_trivial_variable (Trueprop (
        snd x \<Ztypecolon> T (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U (fst x) \<s>\<u>\<b>\<j> b. g b @tag to Z))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> U \<s>\<u>\<b>\<j> y. fst y = fst x \<and> g (snd y) @tag to Z \<close>
  for T :: \<open>('p \<Rightarrow> ('c,'a) \<phi>)\<close> and Z :: \<open>('c\<^sub>a\<^sub>a, 'a\<^sub>a\<^sub>a) \<phi>\<close>
  unfolding Action_Tag_def Transformation_def Reduce_HO_trivial_variable_def
  by clarsimp

lemma \<Sigma>_to_traverse[\<phi>reason default %To_ToA_cut+20]:
  \<open> PROP Reduce_HO_trivial_variable (Trueprop (
        snd x \<Ztypecolon> T (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U (fst x) \<s>\<u>\<b>\<j> b. g b @tag to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z)))
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> U \<s>\<u>\<b>\<j> y. fst y = fst x \<and> g (snd y) @tag to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z) \<close>
  unfolding Action_Tag_def Transformation_def Reduce_HO_trivial_variable_def
  by clarsimp

lemma \<Sigma>_\<A>simp[\<phi>transformation_based_simp default %\<phi>simp_derived_Tr_functor no trigger]:
  \<open> (\<And>c. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> fst x = c \<Longrightarrow> snd x \<Ztypecolon> T c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U c \<s>\<u>\<b>\<j> b. g c b @tag \<A>simp)
      \<comment> \<open>I don't know how to be right. This part causes a lot of HO problems\<close>
\<Longrightarrow> x \<Ztypecolon> \<Sigma> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> U \<s>\<u>\<b>\<j> y. fst y = fst x \<and> g (fst x) (snd y) @tag \<A>_transitive_simp \<close>
  unfolding Action_Tag_def Transformation_def Reduce_HO_trivial_variable_def
  by clarsimp

lemma \<Sigma>_\<A>simp_sep_homo[\<phi>reason %\<phi>simp_cut]:
  \<open> x \<Ztypecolon> \<Sigma> c. T\<^sub>L c \<^emph>\<^sub>\<A> T\<^sub>R c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<Sigma> T\<^sub>L \<^emph>\<^sub>\<A> \<Sigma> T\<^sub>R \<s>\<u>\<b>\<j> y. y = ((fst x, fst (snd x)), (fst x, snd (snd x))) @tag \<A>simp\<close>
  unfolding Action_Tag_def Transformation_def Bubbling_def
  by clarsimp






subsubsection \<open>\<Sigma>-Homomorphism (Commutativity over \<Sigma>)\<close>

lemma [\<phi>reason_template name G.\<Sigma>\<^sub>E[no_atp]]:
  \<open> (\<And>p. Functional_Transformation_Functor G G' (T p) (\<Sigma> T) (D p) (R p) (pm p) (fm p))
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D' : (\<lambda>x. \<forall>a. a \<in> D (fst x) (snd x) \<longrightarrow> (fst x, a) \<in> R (fst x) (snd x)) @tag \<A>_template_reason undefined
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' : embedded_func (\<lambda>x. fm (fst x) (\<lambda>a. ((fst x), a)) (\<lambda>_. True) (snd x)) (\<lambda>_. True) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute\<^sub>\<Lambda>\<^sub>E \<Sigma> \<Sigma> G G' T D' r' \<close>
  unfolding Functional_Transformation_Functor_def Simplify_def Action_Tag_def
            Tyops_Commute\<^sub>\<Lambda>\<^sub>E_def Transformation_def
  by clarsimp

lemma [\<phi>reason_template name F.\<Sigma>\<^sub>I[no_atp]]:
  \<open> (\<And>c. Functional_Transformation_Functor F F' (\<Sigma> T) (T c) D (R c) (pm c) (fm c))
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D' : (\<lambda>x. \<forall>a \<in> D x. fst a = c x \<and> snd a \<in> R (c x) x) @tag \<A>_template_reason undefined
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' : embedded_func (\<lambda>x. (c x, fm (c x) snd (\<lambda>_. True) x))
                              (\<lambda>x. pm (c x) snd (\<lambda>_. True) x) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' \<Sigma> \<Sigma> T D' r' \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>I_def Functional_Transformation_Functor_def Simplify_def Action_Tag_def
  by clarsimp force


subsection \<open>Nondeterministic Abstraction\<close>

text \<open>Transformation functor requires inner elements to be transformed into some fixed \<phi>-type
  independently with the element. It seems to be a limitation. For example, we want to transform
  a list of numbers whose bit-length is unknown \<open>l \<Ztypecolon> List \<nat>\<^sub>f\<^sub>r\<^sub>e\<^sub>e\<close> where \<open>x \<Ztypecolon> \<nat>\<^sub>f\<^sub>r\<^sub>e\<^sub>e \<equiv> (x \<Ztypecolon> \<nat>[b] \<s>\<u>\<b>\<j> b. x < 2^b)\<close>
  into a set of all lists of such numbers \<open>{l | ? } \<Ztypecolon> List \<nat>[?]\<close> where the question marks denote
  the terms cannot be expressed yet now.

  Such transformation can be expressed by \<^emph>\<open>Dependent Sum Type\<close> \<open>\<Sigma>\<close> and \<^emph>\<open>Set Abstraction\<close> \<open>LooseState\<close> \<close>

declare SubjectionTY_def[embed_into_\<phi>type del] \<comment> \<open>replaced by \<open>Set_Abst\<close>\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Set_Abst :: \<open>('a,'b) \<phi> \<Rightarrow> ('a, 'b set) \<phi>\<close> ("\<S>")
  where [embed_into_\<phi>type]: \<open>s \<Ztypecolon> \<S> T \<equiv> (x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s)\<close>
   
 deriving Sep_Functor_1 \<comment> \<open>Its Object_Equiv is an example for non-symmetric reachability relation\<close>
      and Abstract_Domain\<^sub>L
      and \<open>Transformation_Functor \<S> \<S> T U (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>g Sx Sy. Sy = {y. \<exists>x\<in>Sx. g x y})\<close>
      and \<open>Functional_Transformation_Functor Set_Abst Set_Abst T U
                     (\<lambda>x. x) (\<lambda>_. UNIV) (\<lambda>_ _ _. True) (\<lambda>f P X. { f x |x. x \<in> X \<and> P x })\<close>
      and \<open>Separation_Homo\<^sub>I \<S> \<S> \<S> T U UNIV (\<lambda>x. case x of (A, B) \<Rightarrow> A \<times> B)\<close>
      and Carrier_Set
      and Open_Abstraction_to_Raw
      and \<open>c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {x} \<Ztypecolon> \<S> T \<close>
      and \<open>(\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @tag to Itself)
        \<Longrightarrow> \<forall>s. (s \<Ztypecolon> \<S> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>x. r x y \<and> x \<in> s) @tag to Itself)\<close>


text \<open>Read it as 'the abstract object is certain element in the set'

Together with the \<^const>\<open>SubjectionTY\<close>, \<^const>\<open>\<phi>Dependent_Sum\<close> and \<^const>\<open>Set_Abst\<close> embed
  BI connective \<open>\<and>\<close> (\<^const>\<open>Subjection\<close>) and \<open>\<exists>\<close> (\<^const>\<open>ExBI\<close>) into \<phi>-types. The embedding of \<open>\<exists>\<close>
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
        Set_Abst_def[embed_into_\<phi>type del]

subsubsection \<open>Rules\<close>

paragraph \<open>Simplifications\<close>

lemma Set_Abst_single[embed_into_\<phi>type]:
  \<open>{x} \<Ztypecolon> \<S> T \<equiv> x \<Ztypecolon> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma Set_Abst_unfold_defined:
  \<open> {x. x = y \<and> P} \<Ztypecolon> \<S> T \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> P \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

lemma Set_Abst_unfold_Ex:
  \<open> {x. \<exists>a. P x a} \<Ztypecolon> \<S> T \<equiv> {x. P x a} \<Ztypecolon> \<S> T \<s>\<u>\<b>\<j> a. \<top> \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp blast

lemma Set_Abst_unfold':
  \<open> NO_MATCH {a} s
\<Longrightarrow> NO_MATCH {x. x = y'\<and> P'} s
\<Longrightarrow> NO_MATCH {x. \<exists>a. P'' x a} s
\<Longrightarrow> (s \<Ztypecolon> \<S> T) = (x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s)\<close>
  using Set_Abst.unfold .

lemmas [\<phi>programming_base_simps, assertion_simps, simp] =
  Set_Abst_single
  Set_Abst_unfold_defined
  Set_Abst_unfold_Ex
  Set_Abst_unfold'

lemma \<phi>\<s>\<u>\<b>\<j>_over_\<S>[\<phi>programming_simps]:
  \<open>\<S> (T \<phi>\<s>\<u>\<b>\<j> P) \<equiv> (\<S> T) \<phi>\<s>\<u>\<b>\<j> P\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI, simp, blast)

lemma [embed_into_\<phi>type]:
  \<open> (\<Sigma> c. T c) \<phi>\<s>\<u>\<b>\<j> P \<equiv> (\<Sigma> c. T c \<phi>\<s>\<u>\<b>\<j> P) \<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI; clarsimp)

ML \<open>
val BI_Ex_embed_P = Simplifier.make_simproc \<^context> "BI_Ex_embed" {
  lhss = [\<^pattern>\<open>Collect _ \<Ztypecolon> \<S> _ \<phi>\<s>\<u>\<b>\<j> _\<close>],
  proc = fn _ => fn ctxt => fn ctm =>
    SOME ((Conv.rewr_conv @{lemma' \<open> {x. f x} \<Ztypecolon> \<S> T \<phi>\<s>\<u>\<b>\<j> P \<equiv> {x. f x \<and> P} \<Ztypecolon> \<S> T \<close>
                               by (clarsimp simp: atomize_eq BI_eq_iff, blast)}
           then_conv Conv.arg1_conv (Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) =>
        let fun conv ctxt =
                        Conv.rewr_conv @{lemma' \<open>(\<exists>x. Q x) \<and> P \<equiv> \<exists>x. Q x \<and> P\<close>
                                            by (unfold atomize_eq, blast)}
              then_conv Conv.arg_conv (Conv.abs_conv (conv o snd) ctxt)
              else_conv Conv.rewr_conv @{lemma' \<open>(Q \<and> R) \<and> P \<equiv> Q \<and> R \<and> P\<close>
                                            by (unfold atomize_eq, blast)}
              then_conv Conv.arg_conv (conv ctxt)
              else_conv Conv.all_conv
         in conv ctxt
        end) ctxt))) ctm)
}

val BI_Ex_embed_proc = Simplifier.make_simproc \<^context> "BI_Ex_embed" {
  lhss = [\<^pattern>\<open>_ \<Ztypecolon> _ \<s>\<u>\<b>\<j> x. \<top>\<close>],
  proc = fn _ => fn ctxt => fn ctm =>
    case Thm.term_of ctm
      of Const(\<^const_name>\<open>ExBI\<close>, _) $ Abs (_, _, Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) => (
          case T
            of Const(\<^const_name>\<open>SubjectionTY\<close>, _) $ T $ P => (
                  case P
                    of Const(\<^const_name>\<open>Set.member\<close>, _) $ Bound 0 $ _ =>
                        SOME (Conv.rewr_conv
                           (@{print} @{lemma' \<open>x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> x \<in> s \<s>\<u>\<b>\<j> x. \<top> \<equiv> s \<Ztypecolon> \<S> T\<close> for T s
                                by (clarsimp simp: atomize_eq BI_eq_iff) }) ctm)
                     | _ =>
                        if Term.is_dependent T
                        then SOME (Conv.rewr_conv
                                @{lemma' \<open>f x \<Ztypecolon> T x \<phi>\<s>\<u>\<b>\<j> P x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { (x, f x) |x. P x } \<Ztypecolon> \<S> (\<Sigma> x. T x)\<close> for f T P
                                     by (clarsimp simp: atomize_eq BI_eq_iff) } ctm)
                        else SOME (Conv.rewr_conv
                                @{lemma' \<open>f x \<Ztypecolon> T \<phi>\<s>\<u>\<b>\<j> P x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { f x |x. P x } \<Ztypecolon> \<S> T\<close> for f T P
                                     by (clarsimp simp: atomize_eq BI_eq_iff) } ctm))
             | Const(\<^const_name>\<open>Set_Abst\<close>, _) $ T => (
                  if Term.is_dependent T
                  then let fun conv ctxt ctmx =
                                  ( Conv.rewr_conv @{lemma' \<open> (\<exists>y. EQ y \<and> (\<exists>x. P x y)) \<equiv> \<exists>x y. EQ y \<and> P x y \<close> for EQ P
                                                        by (clarsimp simp: atomize_eq, blast)}
                          then_conv Conv.arg_conv (Conv.abs_conv (conv o snd) ctxt)
                          else_conv Conv.rewr_conv @{lemma' \<open> (\<exists>y. x = (c, y) \<and> y = y' \<and> P y) \<equiv> x = (c, y') \<and> P y' \<close> for x c P y'
                                                        by (clarsimp simp: atomize_eq)}
                          else_conv Conv.rewr_conv @{lemma' \<open> (\<exists>y. x = (c, y) \<and> y = y') \<equiv> x = (c, y') \<close> for x c y'
                                                        by (clarsimp simp: atomize_eq)} ) ctmx
                    in SOME ((
                          Conv.rewr_conv @{lemma' \<open> {x. P c x} \<Ztypecolon> \<S> (T c) \<s>\<u>\<b>\<j> c. \<top> \<equiv> {(c, y) |c y. P c y} \<Ztypecolon> \<S> (\<Sigma> T) \<close> for P T
                                              by (clarsimp simp: atomize_eq BI_eq_iff) }
                          then_conv Conv.arg1_conv (Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) =>
                                        Conv.arg_conv (Conv.abs_conv (conv o snd) ctxt)) ctxt))
                          ) ctm)
                   end
                  else SOME (Conv.rewr_conv
                          @{lemma' \<open> {x. P c x} \<Ztypecolon> \<S> T \<s>\<u>\<b>\<j> c. \<top> \<equiv> {x. \<exists>c. P c x} \<Ztypecolon> \<S> T \<close> for P T
                               by (clarsimp simp: atomize_eq BI_eq_iff) } ctm))
             | _ => if Term.is_dependent T
                    then SOME (Conv.rewr_conv @{lemma' \<open>f x \<Ztypecolon> T x \<s>\<u>\<b>\<j> x. \<top> \<equiv> { (x, f x) |x. True } \<Ztypecolon> \<S> (\<Sigma> x. T x)\<close> for f T
                                                   by (clarsimp simp: atomize_eq BI_eq_iff)} ctm)
                    else SOME (Conv.rewr_conv @{lemma' \<open>f x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. \<top> \<equiv> { f x |x. True } \<Ztypecolon> \<S> T\<close> for f T
                                                   by (clarsimp simp: atomize_eq BI_eq_iff)} ctm) 
           )
       | _ => NONE
}
\<close>

setup \<open>Context.theory_map (Phi_Conv.Embed_into_Phi_Type.map (fn ctxt =>
  ctxt addsimprocs [BI_Ex_embed_P, BI_Ex_embed_proc])
)\<close>


paragraph \<open>Conversion Setup\<close>

lemma pure_type_to_ex_quantified_form_3:
  \<open> Collect P \<Ztypecolon> \<S> T \<equiv> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. P y \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

ML \<open>Phi_Conv.set_rules__type_form_to_ex_quantified
      @{thms' Set_Abst_unfold_Ex Set_Abst_unfold_defined
              SubjectionTY.unfold} ;
    Phi_Conv.set_rules__type_form_to_ex_quantified_single_var
      @{thms' Set_Abst_unfold_Ex pure_type_to_ex_quantified_form_3
              SubjectionTY.unfold} \<close>


paragraph \<open>ToA Reasoning\<close>

lemma [\<phi>reason 2800]:
  \<open> (\<And>a \<in> fst x. (a, snd x) \<Ztypecolon> T \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P )
\<Longrightarrow> x \<Ztypecolon> (\<S> T) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def Premise_def Transformation_def meta_Ball_def \<phi>Prod'_def
  by (cases x; clarsimp; blast)


subsubsection \<open>\<S>-Homomorphism (Commutativity over \<S>)\<close>

text \<open>The homomorphism of \<open>\<S>\<close> type is entailed in the transformation functor directly.\<close>

lemma \<S>_Homo\<^sub>E: (*deprecated*)
  \<open> Transformation_Functor Fa Fb (\<S> T) T D R mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D s \<and> b \<in> a \<longrightarrow> b \<in> R s)
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> s' : Collect (mapper (\<lambda>S x. x \<in> S) s)) @tag \<A>_template_reason undefined
\<Longrightarrow> s \<Ztypecolon> Fa (\<S> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> s' \<Ztypecolon> \<S> (Fb T)\<close>
  unfolding Transformation_Functor_def Transformation_def Premise_def Action_Tag_def Simplify_def
  by clarsimp

lemma [\<phi>reason_template name G.\<S>\<^sub>I [no_atp]]:
  \<open> Transformation_Functor G G' (\<S> T) T D R mapper
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D' : (\<lambda>s. \<forall>a. a \<in> D s \<longrightarrow> a \<subseteq> R s) @tag \<A>_template_reason undefined
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' : embedded_func (\<lambda>s. Collect (mapper (\<lambda>S x. x \<in> S) s)) (\<lambda>_. True) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute G G' \<S> \<S> T D' r'\<close>
  unfolding Tyops_Commute_def
            Transformation_Functor_def Transformation_def Premise_def Action_Tag_def Simplify_def
  by (clarsimp simp add: subset_iff Ball_def; smt (verit, ccfv_threshold))

text \<open>Does the reverse transformation exist?. The commutativity between \<open>F\<close> and \<open>\<S>\<close> gonna be a problem.\<close>
  
lemma [\<phi>reason_template name F.\<S>\<^sub>E [no_atp]]:
  \<open> Functional_Transformation_Functor F F' T (\<S> T) D R pm fm
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D' : (\<lambda>s. (\<forall>x \<in> s. \<forall>a \<in> D x. f s x a \<in> R x \<and> a \<in> f s x a) \<and>
                     (\<forall>x \<in> s. fm (f s x) (\<lambda>_. True) x = g s)) @tag \<A>_template_reason undefined
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' : embedded_func g (\<lambda>_. True) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute \<S> \<S> F F' T D' r' \<close>
  unfolding Functional_Transformation_Functor_def Tyops_Commute_def Transformation_def
            Action_Tag_def Simplify_def
  apply clarsimp
  subgoal premises prems for s v x
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>f s x\<close>], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2-),
        clarsimp,
        blast) .


text \<open>The above rules are interesting but essentially useless as it is replaced by the following rule,
  which eliminates any \<open>\<S>\<close> in a ready sequent of CoP.

mmm but what if during the separation extraction when a \<open>\<S>\<close> is generated by some previous reasoning?

The above rules are still useful in giving the commutativity between \<open>F\<close> and \<open>\<S>\<close>.
\<close>

lemma [\<phi>reason 1000]:
  \<open>s \<Ztypecolon> \<S> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. x \<in> s @tag \<A>_transitive_simp\<close>
  unfolding Action_Tag_def Transformation_def
  by simp


 
subsection \<open>Vertical Composition\<close>


\<phi>type_def \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 30)
  where \<open>\<phi>Composition T U x = (y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y \<Turnstile> (x \<Ztypecolon> U))\<close>
  deriving \<open>Carrier_Set T P \<Longrightarrow> Carrier_Set (T \<Zcomp> U) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> U) \<longrightarrow> P v)\<close>

declare \<phi>Composition.expansion[unfolded \<phi>Type_def, iff]

lemma \<phi>Composition_assoc:
  \<open>((I1 \<Zcomp> I2) \<Zcomp> I3) = (I1 \<Zcomp> (I2 \<Zcomp> I3))\<close>
  by (rule \<phi>Type_eqI, simp , blast)

lemma interp_comp_homo_one[simp]:
  \<open>homo_one Ia \<Longrightarrow> homo_one Ib \<Longrightarrow> homo_one (Ia \<Zcomp> Ib)\<close>
  unfolding homo_one_def by (simp add: BI_eq_iff)

lemma Itself_comp[simp]:
  \<open>(Itself \<Zcomp> I) = I\<close> \<open>(I \<Zcomp> Itself) = I\<close>
  by (simp add: BI_eq_iff fun_eq_iff)+

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

subsubsection \<open>Algebraic Properties\<close>

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain U A
\<Longrightarrow> Abstract_Domain T B
\<Longrightarrow> Abstract_Domain (T \<Zcomp> U) (\<lambda>x. A x \<and> Ex B) \<close>
  unfolding Satisfiable_def Action_Tag_def Abstract_Domain_def \<r>EIF_def
  by simp blast

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain\<^sub>L U A
\<Longrightarrow> Abstract_Domain\<^sub>L T B
\<Longrightarrow> Abstract_Domain\<^sub>L (T \<Zcomp> U) (\<lambda>x. A x \<and> All B) \<close>
  unfolding Satisfiable_def Action_Tag_def Abstract_Domain\<^sub>L_def \<r>ESC_def
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
  \<open> (\<And>x. x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rU x y @tag to (Itself :: ('b,'b) \<phi>))
\<Longrightarrow> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y :: 'c) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rT x y @tag to (Itself :: ('c,'c) \<phi>))
\<Longrightarrow> x \<Ztypecolon> T \<Zcomp> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. (\<exists>m. rT m y \<and> rU x m) @tag to (Itself :: ('c,'c) \<phi>)\<close>
  unfolding Transformation_def Action_Tag_def
  by clarsimp  blast

lemma [\<phi>reason 1000]:
  \<open> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> m \<Ztypecolon> T
\<Longrightarrow> m \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U
\<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<Zcomp> U \<close>
  unfolding Action_Tag_def Transformation_def Premise_def
  by clarsimp blast

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>I B D\<^sub>B P\<^sub>B
\<Longrightarrow> Identity_Elements\<^sub>I (B \<Zcomp> T) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> D\<^sub>B v) (\<lambda>x. (\<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> P\<^sub>B v) \<and> Satisfiable (x \<Ztypecolon> T))\<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Transformation_def Orelse_shortcut_def
            Satisfiable_def
  by clarsimp blast

(*TODO: analysis of completeness*)

lemma [\<phi>reason 1000]:
  \<open> Identity_Elements\<^sub>E B D\<^sub>B
\<Longrightarrow> Identity_Elements\<^sub>E (B \<Zcomp> T) (\<lambda>x. \<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> D\<^sub>B v) \<close>
  unfolding Identity_Element\<^sub>E_def Identity_Elements\<^sub>E_def Transformation_def
  by clarsimp blast
 
lemma [\<phi>reason 1000]:
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv (B \<Zcomp> T) eq \<close>
  unfolding Object_Equiv_def Transformation_def
  by clarsimp blast

lemma \<Psi>_comp:
  \<open> \<Psi>[\<psi>] (x \<Ztypecolon> T) = (x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T) \<close>
  unfolding BI_eq_iff
  by clarsimp


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
    by (insert prems(2)[THEN spec[where x=\<open>\<lambda>_. Itself x\<close>], THEN spec[where x=\<open>\<lambda>_. Itself y\<close>], simplified]
               prems(1,3-5),
        auto) .
  
lemma \<phi>Composition_separatio_functor_unzip[\<phi>reason 1000]:
  \<open> Object_Sep_Homo\<^sub>E B
\<Longrightarrow> Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U (\<lambda>x. x)\<close>
  for B :: \<open>('d::sep_magma_1,'e::sep_magma) \<phi>\<close>
  unfolding Separation_Homo\<^sub>E_def Transformation_def Object_Sep_Homo\<^sub>E_def
  by (clarsimp simp add: set_mult_expn; blast)

lemma (*The above rule is reversible*)
  \<open> \<forall>T U. Separation_Homo\<^sub>E ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) T U (\<lambda>x. x) \<Longrightarrow> Object_Sep_Homo\<^sub>E B \<close>
  unfolding Separation_Homo\<^sub>E_def Object_Sep_Homo\<^sub>E_def Transformation_def
  apply (clarsimp simp add: set_mult_expn)
  apply (simp add: \<phi>Type_def)
  subgoal premises prems for x y v
    by (insert prems(1)[THEN spec[where x=\<open>\<lambda>_. Itself x\<close>], THEN spec[where x=\<open>\<lambda>_. Itself y\<close>], simplified]
               prems(2-3), metis Itself_expn' Satisfaction_def) .





subsection \<open>Finite Multiplicative Quantification\<close>
  
text \<open>The type parameter \<open>T\<close> is not paramterized by the quantified variable. It is not a restriction
  as we have \<open>\<Sigma>\<close>. Instead, only when \<open>T\<close> is not parameterized, \<open>\<big_ast>\<^sup>\<phi> I T\<close> forms a semimodule.\<close>

\<phi>type_def \<phi>Mul_Quant :: \<open>'i set \<Rightarrow> ('c::sep_algebra, 'x) \<phi> \<Rightarrow> ('c::sep_algebra, 'i \<Rightarrow> 'x) \<phi>\<close> ("\<big_ast>\<^sup>\<phi>\<^sub>0")
  where [embed_into_\<phi>type]: \<open>\<big_ast>\<^sup>\<phi>\<^sub>0 I T = (\<lambda>x. \<big_ast>i\<in>I. x i \<Ztypecolon> T)\<close>
  deriving Basic
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (\<big_ast>\<^sup>\<phi>\<^sub>0 I T) (\<lambda>x. \<forall>i \<in> I. P (x i)) \<close>
       (*and Abstract_Domain\<^sub>L (*TODO*)*)
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J \<Longrightarrow> Transformation_Functor (\<big_ast>\<^sup>\<phi>\<^sub>0 I) (\<big_ast>\<^sup>\<phi>\<^sub>0 J) T U (\<lambda>x. x ` I) (\<lambda>_. UNIV) (\<lambda>g x y. \<forall>i\<in>I. g (x i) (y i))\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J \<Longrightarrow> Functional_Transformation_Functor (\<big_ast>\<^sup>\<phi>\<^sub>0 I) (\<big_ast>\<^sup>\<phi>\<^sub>0 J) T U (\<lambda>x. x ` I) (\<lambda>_. UNIV) (\<lambda>_ P x. \<forall>i\<in>I. P (x i)) (\<lambda>f _. (o) f)\<close>
       and Sep_Functor_1
       and Functionality
       and Semimodule_Scalar_Assoc
       and Semimodule_One
       and Closed_Semimodule_Zero
       and Carrier_Set


subsubsection \<open>Syntax\<close>

nonterminal "dom_idx"

syntax
  "_one_dom" :: \<open>pttrns \<Rightarrow> 'a set \<Rightarrow> dom_idx\<close> ("_/\<in>_" [0,51] 50)
  "_more_dom":: \<open>dom_idx \<Rightarrow> dom_idx \<Rightarrow> dom_idx\<close> ("_,/ _" [49, 50] 49)
  "_\<phi>Mul_Quant\<^sub>0" :: "dom_idx \<Rightarrow> logic \<Rightarrow> logic"  ("(2\<big_ast>\<^sub>0[_]/ _)" [49, 1000] 1000)

translations
  "CONST \<phi>Type x (_\<phi>Mul_Quant\<^sub>0 (_one_dom i I) T)" == "CONST \<phi>Type (\<lambda>i. x) (CONST \<phi>Mul_Quant I T)"
  "CONST \<phi>Type x (_\<phi>Mul_Quant\<^sub>0 (_more_dom d (_one_dom i I)) T)" == "CONST \<phi>Type (\<lambda>i. x) (_\<phi>Mul_Quant\<^sub>0 d (CONST \<phi>Mul_Quant I T))"


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
  Phi_Type.override_ind_rule (\<^pattern>\<open>\<phi>Mul_Quant\<close>, @{thm' \<phi>Mul_Quant_induct}))\<close>


subsubsection \<open>Algebraic Properties\<close>

text \<open>We cannot derive the Scalar Distributivity automatically, because the scalar
  distribution of the assertion-level \<open>\<big_ast>\<close> is not activated in the reasoning system by default
  (it is too aggressive to enable it, I believe).\<close>

lemma \<phi>Mul_Quant_SDistr_Homo\<^sub>Z[\<phi>reason 1000]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z (\<lambda>I. \<big_ast>\<^sup>\<phi>\<^sub>0 I T) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ D\<^sub>g (f,g). f \<oplus>\<^sub>f[D\<^sub>g] g) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def dom_of_add_set_def
  by (clarsimp simp add: \<phi>Prod_expn' \<phi>Mul_Quant.unfold sep_quant_scalar_distr;
      smt (verit) Mul_Quant_def Transformation_def disjoint_iff plus_set_in_iff prod.cong)

lemma \<phi>Mul_Quant_SDistr_Homo\<^sub>S[\<phi>reason 1000]:
  \<open> Semimodule_SDistr_Homo\<^sub>S (\<lambda>I. \<big_ast>\<^sup>\<phi>\<^sub>0 I T) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ f. (f ,f)) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def dom_of_add_set_def
  by (clarsimp simp add: \<phi>Mul_Quant.unfold \<phi>Prod_expn' sep_quant_scalar_distr)


subsubsection \<open>Rewrites\<close>

lemma \<phi>Mul_Quant_insert:
  \<open> k \<notin> I
\<Longrightarrow> (x \<Ztypecolon> \<big_ast>\<^sup>\<phi>\<^sub>0 (insert k I) T) = ((x k, x) \<Ztypecolon> T \<^emph> \<big_ast>\<^sup>\<phi>\<^sub>0 I T) \<close>
  unfolding \<phi>Mul_Quant.unfold \<phi>Prod_expn'
  by (clarsimp simp add: sep_quant_insert)

subsubsection \<open>Transformations\<close>

paragraph \<open>Reduction for individually inserted elements\<close>

lemma [\<phi>reason %ToA_derived_red-10]: \<comment>\<open>The priority must be lower than the derived \<open> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> {x} T\<close>\<close>
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x k \<Ztypecolon> T) * (x \<Ztypecolon> \<big_ast>\<^sup>\<phi>\<^sub>0 I T) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi>\<^sub>0 (insert k I) T \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Mul_Quant.unfold \<r>Guard_def Premise_def
  by (clarsimp simp add: sep_quant_insert)

lemma [\<phi>reason %ToA_derived_red-10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x k \<Ztypecolon> T) * (x \<Ztypecolon> \<big_ast>\<^sup>\<phi>\<^sub>0 I T) \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi>\<^sub>0 (insert k I) T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Mul_Quant.unfold \<r>Guard_def Premise_def
  by (clarsimp simp add: sep_quant_insert)

lemma [\<phi>reason %ToA_derived_red-10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k \<notin> I
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst (\<lambda>f. (f k, f)) x \<Ztypecolon> (T \<^emph> \<big_ast>\<^sup>\<phi>\<^sub>0 I T) \<OTast> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<big_ast>\<^sup>\<phi>\<^sub>0 (insert k I) T \<OTast> R \<w>\<i>\<t>\<h> P \<close>
  unfolding \<r>Guard_def Premise_def \<phi>Prod'_def
  by (cases x; clarsimp simp add: \<phi>Prod_expn' \<phi>Mul_Quant_insert)



subsection \<open>Sum Type\<close>

lemma pred_sum_is_case_sum[simp]:
  \<open>pred_sum = case_sum\<close>
  using pred_sum_eq_case_sum by blast

declare [[\<phi>trace_reasoning = 0]]
 
\<phi>type_def \<phi>Sum :: \<open>('c,'x) \<phi> \<Rightarrow> ('c, 'y) \<phi> \<Rightarrow> ('c, 'x + 'y) \<phi>\<close> (infixl "+\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T +\<^sub>\<phi> U) = (\<lambda>xy. case xy of Inl x \<Rightarrow> x \<Ztypecolon> T | Inr y \<Rightarrow> y \<Ztypecolon> U)\<close>
  deriving \<open>Object_Equiv T eq\<^sub>T \<Longrightarrow> Object_Equiv U eq\<^sub>U \<Longrightarrow> Object_Equiv (T +\<^sub>\<phi> U) (rel_sum eq\<^sub>T eq\<^sub>U)\<close>
       and Abstract_Domain
       and \<open>Abstract_Domain\<^sub>L T T\<^sub>D
        \<Longrightarrow> Abstract_Domain\<^sub>L U U\<^sub>D
        \<Longrightarrow> Abstract_Domain\<^sub>L (T +\<^sub>\<phi> U) (case_sum T\<^sub>D U\<^sub>D)\<close> (*simplification fails to transform the result into the ideal form*)
       and \<open>Carrier_Set T P
        \<Longrightarrow> Carrier_Set U Q
        \<Longrightarrow> Carrier_Set (T +\<^sub>\<phi> U) (pred_sum P Q)\<close> (*simplification fails*)
       and Identity_Elements
       and \<open>Identity_Elements\<^sub>E T T\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E U U\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E (T +\<^sub>\<phi> U) (case_sum T\<^sub>D U\<^sub>D) \<close> (*The inference works, but the result is not in an ideal form,
                                                            so we give the annotation manually*)
       and \<open>Identity_Elements\<^sub>I T T\<^sub>D T\<^sub>P
        \<Longrightarrow> Identity_Elements\<^sub>I U U\<^sub>D U\<^sub>P 
        \<Longrightarrow> Identity_Elements\<^sub>I (T +\<^sub>\<phi> U) (case_sum T\<^sub>D U\<^sub>D) (case_sum T\<^sub>P U\<^sub>P) \<close> (*The inference works*)
       and Functional_Transformation_Functor



subsubsection \<open>Rewrites\<close>

lemma \<phi>Sum_red[simp]:
  \<open>(Inl a \<Ztypecolon> T +\<^sub>\<phi> U) = (a \<Ztypecolon> T)\<close>
  \<open>(Inr b \<Ztypecolon> T +\<^sub>\<phi> U) = (b \<Ztypecolon> U)\<close>
  unfolding \<phi>Sum.unfold
  by simp_all


subsubsection \<open>Transformations\<close>

\<phi>reasoner_group ToA_splitting_\<phi>Sum = (%ToA_splitting-20, [%ToA_splitting-20, %ToA_splitting-19])
                                      for (\<open>x \<Ztypecolon> T +\<^sub>\<phi> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close>, \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T +\<^sub>\<phi> U\<close>)
                                       in ToA_splitting and < ToA_splitting_If
  \<open>ToA splitting \<open>\<phi>Sum\<close>\<close>

declare \<phi>Sum.intro_reasoning(1)[\<phi>reason %ToA_splitting_\<phi>Sum]
        \<phi>Sum.elim_reasoning (1)[\<phi>reason %ToA_splitting_\<phi>Sum]

(*
lemma [\<phi>reason %ToA_splitting_\<phi>Sum+1 for \<open>(_, _) \<Ztypecolon> (_ +\<^sub>\<phi> _) \<OTast> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>]:
  \<open> (case x of Inl a \<Rightarrow> (a, w\<^sub>a a) \<Ztypecolon> T \<OTast> W\<^sub>a a | Inr b \<Rightarrow> (b, w\<^sub>b b) \<Ztypecolon> U \<OTast> W\<^sub>b b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>'
\<Longrightarrow> (x, case_sum w\<^sub>a w\<^sub>b x) \<Ztypecolon> (T +\<^sub>\<phi> U) \<OTast> case_sum W\<^sub>a W\<^sub>b x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding \<phi>Prod'_def
  by (cases x; auto simp add: \<phi>Prod_expn' )
*)

(*TODO: special process!*)
lemma [\<phi>reason %ToA_splitting_\<phi>Sum]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> snd x = case_sum w\<^sub>a w\<^sub>b (fst x) \<Longrightarrow>
      (case fst x of Inl a \<Rightarrow> (a, w\<^sub>a a) \<Ztypecolon> T \<OTast> W\<^sub>a a | Inr b \<Rightarrow> (b, w\<^sub>b b) \<Ztypecolon> U \<OTast> W\<^sub>b b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> snd x = case_sum w\<^sub>a w\<^sub>b (fst x)
\<Longrightarrow> x \<Ztypecolon> (T +\<^sub>\<phi> U) \<OTast> case_sum W\<^sub>a W\<^sub>b (fst x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @tag \<T>\<P>'\<close>
  unfolding Premise_def \<phi>Prod'_def
  by (cases x; case_tac a; auto simp add: \<phi>Prod_expn')

lemma [\<phi>reason %ToA_splitting_\<phi>Sum]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (case fst y of Inl a \<Rightarrow> (a, snd y) \<Ztypecolon> T \<OTast> R | Inr b \<Rightarrow> (b, snd y) \<Ztypecolon> U \<OTast> R) \<w>\<i>\<t>\<h> P @tag \<T>\<P>'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (T +\<^sub>\<phi> U) \<OTast> R \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding \<phi>Prod'_def
  by (cases y; case_tac a; simp add: \<phi>Prod_expn')


subsubsection \<open>Rule\<close>

lemma [\<phi>reason_template name F.\<phi>Sum\<^sub>E[no_atp]]:
  \<open> Functional_Transformation_Functor F\<^sub>T F T (T +\<^sub>\<phi> U) D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F\<^sub>U F U (T +\<^sub>\<phi> U) D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D : (\<lambda>x. case x of Inl u \<Rightarrow> (\<forall>a \<in> D\<^sub>T u. Inl a \<in> R\<^sub>T u)
                             | Inr v \<Rightarrow> (\<forall>b \<in> D\<^sub>U v. Inr b \<in> R\<^sub>U v))) @tag \<A>_template_reason undefined
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r : (embedded_func (case_sum (fm\<^sub>T Inl (\<lambda>_. True)) (fm\<^sub>U Inr (\<lambda>_. True)))
                               (pred_sum (pm\<^sub>T Inl (\<lambda>_. True)) (pm\<^sub>U Inr (\<lambda>_. True))))) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F\<^sub>T F\<^sub>U (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U D r \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Functional_Transformation_Functor_def Premise_def
            Action_Tag_def Simplify_def
  by (clarify; case_tac x; clarsimp)

lemma [\<phi>reason_template name F.\<phi>Sum\<^sub>I[no_atp]]:
  \<open> Functional_Transformation_Functor F F'\<^sub>T (T +\<^sub>\<phi> U) T D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F F'\<^sub>U (T +\<^sub>\<phi> U) U D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x a. a \<in> D\<^sub>T x \<and> isl a \<longrightarrow> projl a \<in> R\<^sub>T x) \<and>
           (\<forall>x a. a \<in> D\<^sub>U x \<and> \<not> isl a \<longrightarrow> projr a \<in> R\<^sub>U x)
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] D : (\<lambda>x. (\<forall>a \<in> D\<^sub>T x. isl a) \<or> (\<forall>b \<in> D\<^sub>U x. \<not> isl b))) @tag \<A>_template_reason undefined
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] r : (embedded_func (\<lambda>x. if (\<forall>a \<in> D\<^sub>T x. isl a)
                                    then Inl (fm\<^sub>T projl (\<lambda>_. True) x)
                                    else Inr (fm\<^sub>U projr (\<lambda>_. True) x))
                               (\<lambda>x. if (\<forall>a \<in> D\<^sub>T x. isl a)
                                    then pm\<^sub>T projl (\<lambda>_. True) x
                                    else pm\<^sub>U projr (\<lambda>_. True) x))) @tag \<A>_template_reason undefined
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

 
lemma \<phi>Composition_\<phi>Sum_Comm [\<phi>reason %\<phi>TA_property]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (+\<^sub>\<phi>) (+\<^sub>\<phi>) T U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Transformation_def
  by (clarsimp simp add: split_sum_all)


subsection \<open>Additive Disjunction\<close>

text \<open>Depreciated! Use \<open>\<phi>Sum\<close> instead!\<close>
 
\<phi>type_def \<phi>Union :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<or>\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T \<or>\<^sub>\<phi> U) = (\<lambda>x. (fst x \<Ztypecolon> T) + (snd x \<Ztypecolon> U))\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Identity_Elements
       and \<open>(c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T) \<and> y = unspec \<or>\<^sub>c\<^sub>u\<^sub>t
            (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U) \<and> x = unspec
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> T \<or>\<^sub>\<phi> U \<close>


subsubsection \<open>Configurations\<close>

declare \<phi>Union_def[embed_into_\<phi>type del]

lemma [embed_into_\<phi>type]:
  \<open>(x \<Ztypecolon> T) + (y \<Ztypecolon> U) \<equiv> (x,y) \<Ztypecolon> T \<or>\<^sub>\<phi> U\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp
 
let_\<phi>type \<phi>Union deriving \<open>Object_Equiv (\<circle> \<or>\<^sub>\<phi> \<circle>) (\<lambda>_ _. True)\<close>



subsection \<open>Embedding Additive Conjunction\<close>

(* declare False_def[symmetric, simp] *)

\<phi>type_def \<phi>Inter :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<and>\<^sub>\<phi>" 70)
  where [embed_into_\<phi>type]: \<open>(T \<and>\<^sub>\<phi> U) = (\<lambda>x. (fst x \<Ztypecolon> T) \<sqinter> (snd x \<Ztypecolon> U))\<close>
  deriving Basic
       and Object_Equiv
       and Identity_Elements
       and Functional_Transformation_Functor
       and \<open> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U
        \<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> T \<and>\<^sub>\<phi> U \<close>
       and Functionality
       and Commutativity_Deriver\<^sub>E
       and \<open> Identity_Elements\<^sub>I ?T ?T\<^sub>D ?T\<^sub>P \<Longrightarrow>
             Identity_Elements\<^sub>I ?U ?U\<^sub>D ?U\<^sub>P \<Longrightarrow> Identity_Elements\<^sub>I (?T \<and>\<^sub>\<phi> ?U) (\<lambda>x. ?U\<^sub>D (snd x) \<or> ?T\<^sub>D (fst x)) (\<lambda>x. ?U\<^sub>P (snd x) \<or> ?T\<^sub>P (fst x))   \<close>


subsubsection \<open>Rules\<close>

declare \<phi>Inter_def[embed_into_\<phi>type del]

lemma \<phi>Inter_embedding[embed_into_\<phi>type]:
  \<open>(x \<Ztypecolon> T) \<sqinter> (y \<Ztypecolon> U) \<equiv> (x, y) \<Ztypecolon> T \<and>\<^sub>\<phi> U\<close>
  unfolding atomize_eq BI_eq_iff
  by simp

lemma [\<phi>reason 1000]:
  \<open> fst x \<Ztypecolon> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ra y @tag to Itself
\<Longrightarrow> snd x \<Ztypecolon> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. rb y @tag to Itself
\<Longrightarrow> x \<Ztypecolon> A \<and>\<^sub>\<phi> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ra y \<and> rb y @tag to Itself \<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp

(*TODO: transformation rules for \<open>\<and>\<^sub>\<phi>\<close>*)

lemma [\<phi>reason_template name F.\<phi>Inter\<^sub>I[no_atp]]:
  \<open> Functional_Transformation_Functor F F\<^sub>T (T \<and>\<^sub>\<phi> U) T D\<^sub>T R\<^sub>T pm\<^sub>T fm\<^sub>T
\<Longrightarrow> Functional_Transformation_Functor F F\<^sub>U (T \<and>\<^sub>\<phi> U) U D\<^sub>U R\<^sub>U pm\<^sub>U fm\<^sub>U
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] D : (\<lambda>x. (\<forall>a \<in> D\<^sub>T x. fst a \<in> R\<^sub>T x) \<and> (\<forall>a \<in> D\<^sub>U x. snd a \<in> R\<^sub>U x))) @tag \<A>_template_reason undefined
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] r : (embedded_func (\<lambda>x. (fm\<^sub>T fst (\<lambda>_. True) x, fm\<^sub>U snd (\<lambda>_. True) x))
                                                (\<lambda>x. pm\<^sub>T fst (\<lambda>_. True) x \<and> pm\<^sub>U snd (\<lambda>_. True) x))) @tag \<A>_template_reason undefined
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F\<^sub>T F\<^sub>U (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U D r\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Functional_Transformation_Functor_def Premise_def
            Simplify_def Action_Tag_def
  apply clarify
  subgoal premises prems for x
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=fst], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(2)[THEN spec[where x=x], THEN spec[where x=snd], THEN spec[where x=\<open>\<lambda>_. True\<close>]]
               prems(3-);
        clarsimp simp add: Transformation_def) .

lemma \<phi>Composition_\<phi>Inter_Comm [\<phi>reason %\<phi>TA_property]:
  \<open> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U
                    (\<lambda>(a,b). \<forall>u v c. u \<Turnstile> (a \<Ztypecolon> T) \<and> v \<Turnstile> (b \<Ztypecolon> U) \<and> c \<Turnstile> (u \<Ztypecolon> B) \<and> c \<Turnstile> (v \<Ztypecolon> B) \<longrightarrow>
                            (\<exists>w. c \<Turnstile> (w \<Ztypecolon> B) \<and> w \<Turnstile> (a \<Ztypecolon> T) \<and> w \<Turnstile> (b \<Ztypecolon> U)))
                    (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Transformation_def
  by clarsimp


subsection \<open>Vertical Composition of Function\<close>


text \<open>It is a more specific form than \<open>\<phi>Fun f \<Zcomp> T\<close> on which automation rules (particularly the Sep_Homo)
  can be given more generally.\<close>

\<phi>reasoner_group
      identity_elements_of_\<phi>Fun = (100, [100, 140]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
                                                     in identity_element and > derived_identity_element \<open>\<close>
  and carrier_set_of_\<phi>Fun = (60, [60,70]) for \<open>Carrier_Set _ _\<close>
                            in carrier_set and > derived_carrier_set and < carrier_set_cut \<open>\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>Fun' :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close> (infixr "\<Zcomp>\<^sub>f" 30)
  where \<open>\<phi>Fun' f T = (\<phi>Fun f \<Zcomp> T)\<close>
  opening extracting_Carrier_Set_sat
          extract_mul_carrier
          Identity_Element_sat
  deriving Basic
       and Abstract_Domain\<^sub>L
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 f
         \<Longrightarrow> Identity_Elements\<^sub>I (f \<Zcomp>\<^sub>f T) (\<lambda>_. True) (\<lambda>x. Satisfiable (x \<Ztypecolon> T)) \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one f
         \<Longrightarrow> Identity_Elements\<^sub>I T D P
         \<Longrightarrow> Identity_Elements\<^sub>I (f \<Zcomp>\<^sub>f T) D P \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>I (f \<Zcomp>\<^sub>f T) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> f v = 1) (\<lambda>x. Satisfiable (x \<Ztypecolon> T))\<close>
           (%identity_elements_of_\<phi>Fun)
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 f
         \<Longrightarrow> Identity_Elements\<^sub>E (f \<Zcomp>\<^sub>f T) (\<lambda>x. Satisfiable (x \<Ztypecolon> T)) \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one f
         \<Longrightarrow> Identity_Elements\<^sub>E T D
         \<Longrightarrow> Identity_Elements\<^sub>E (f \<Zcomp>\<^sub>f T) D \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>E (f \<Zcomp>\<^sub>f T) (\<lambda>x. \<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> f v = 1) \<close>
           (%identity_elements_of_\<phi>Fun)
       and Functionality
       and Functional_Transformation_Functor
       and \<open>homo_sep \<psi> \<Longrightarrow> Separation_Homo\<^sub>E (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) T U (\<lambda>x. x)\<close>
       and \<open>\<g>\<u>\<a>\<r>\<d> homo_mul_carrier f
        \<Longrightarrow> Carrier_Set U P
        \<Longrightarrow> Carrier_Set (f \<Zcomp>\<^sub>f U) P \<close> \<comment> \<open>Guesser fails. It is
                            still too hard for our guesser to infer \<open>homo_mul_carrier f\<close>\<close>
           (%carrier_set_of_\<phi>Fun+10)
       and \<open>\<g>\<u>\<a>\<r>\<d> constantly_inside_carrier f
        \<Longrightarrow> Carrier_Set (f \<Zcomp>\<^sub>f U) P\<close>
           (%carrier_set_of_\<phi>Fun)
       and Commutativity_Deriver
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> f\<^sub>1 = f\<^sub>2 \<and> f\<^sub>1 = f\<^sub>3
         \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] inj f\<^sub>1
         \<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ((\<Zcomp>\<^sub>f) f\<^sub>1) ((\<Zcomp>\<^sub>f) f\<^sub>2) ((\<Zcomp>\<^sub>f) f\<^sub>3) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))\<close>

       and \<open> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::('c2,'c2) \<phi>) \<s>\<u>\<b>\<j> y. r x y @tag to (Itself::('c2,'c2) \<phi>))
         \<Longrightarrow> \<forall>x'. x' \<Ztypecolon> f \<Zcomp>\<^sub>f T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::('c,'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = f x \<and> r x' x) @tag to (Itself::('c,'c) \<phi>)  \<close>
       and \<open> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<Longrightarrow> f c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> f \<Zcomp>\<^sub>f T  \<close>


declare \<phi>Fun'.\<phi>Sum\<^sub>I[\<phi>reason add]
        \<phi>Fun'.\<phi>Sum\<^sub>E[\<phi>reason add]
        \<phi>Fun'.\<phi>Inter\<^sub>I[\<phi>reason add]

subsubsection \<open>Reasoning Rules\<close>

text \<open>The following rule is more general than \<open>\<phi>Fun f \<Zcomp> T\<close> as it in addition supports non-closed homomorphism.\<close>

lemma \<phi>Fun'_Separation_Homo\<^sub>I[\<phi>reason 1000]:
  \<open> homo_sep \<psi>
\<Longrightarrow> closed_homo_sep \<psi> \<and>\<^sub>\<r> Dx = UNIV \<or>\<^sub>c\<^sub>u\<^sub>t
    Separation_Disj\<^sub>\<phi> \<psi> Dx T U
\<Longrightarrow> Separation_Homo\<^sub>I (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>) T U Dx (\<lambda>x. x) \<close>
  unfolding Separation_Homo\<^sub>I_def Transformation_def Object_Sep_Homo\<^sub>I_def
            Separation_Disj\<^sub>\<phi>_def Separation_Disj\<^sub>\<psi>_def closed_homo_sep_def
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

lemma \<phi>Fun'_comm[\<phi>reason %\<phi>TA_commutativity]:
  \<open> fun_commute \<psi> \<phi> \<psi>' \<phi>'
\<Longrightarrow> Tyops_Commute (\<phi>Fun' \<psi>) (\<phi>Fun' \<psi>') (\<phi>Fun' \<phi>) (\<phi>Fun' \<phi>') T
                  (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))\<close>
  unfolding Tyops_Commute_def fun_commute_def
  by (simp add: \<phi>Fun'_scalar_assoc)


subsubsection \<open>Guessing Property\<close>

lemma [\<phi>reason %guess_tyop_commute+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> fun_commute g f g' f'
\<Longrightarrow> Guess_Tyops_Commute both G G' F F'
                        (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) (\<lambda>T x. x \<Ztypecolon> f \<Zcomp>\<^sub>f T) (\<lambda>T x. x \<Ztypecolon> f' \<Zcomp>\<^sub>f T) T
                        (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True\<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute]:
  \<open> Guess_Tyops_Commute both G G' F F'
                        (\<lambda>U x. x \<Ztypecolon> g \<Zcomp>\<^sub>f U) (\<lambda>U x. x \<Ztypecolon> g' \<Zcomp>\<^sub>f U) (\<lambda>T x. x \<Ztypecolon> f \<Zcomp>\<^sub>f T) (\<lambda>T x. x \<Ztypecolon> f' \<Zcomp>\<^sub>f T) T
                        (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) (fun_commute g f g' f') True\<close>
  unfolding Guess_Tyops_Commute_def ..


subsubsection \<open>Meta Analysis\<close>

lemma \<comment> \<open>The rule of \<open>\<phi>Fun'.\<phi>Inter_Comm\<^sub>I\<close> is reversible (for universally quantified x, T, U)\<close>
  \<open>(\<And>T U x. x \<Ztypecolon> (\<psi> \<Zcomp>\<^sub>f T) \<and>\<^sub>\<phi> (\<psi> \<Zcomp>\<^sub>f U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<psi> \<Zcomp>\<^sub>f (T \<and>\<^sub>\<phi> U)) \<Longrightarrow> inj \<psi>\<close>
  unfolding Transformation_def inj_def
  apply clarsimp
  subgoal premises prems for x y
    by (insert prems(1)[of _ \<open>\<lambda>_. Itself x\<close> _ \<open>\<lambda>_. Itself y\<close>]
               prems(2-),
        clarsimp simp add: \<phi>Type_def) .



subsection \<open>Injection into Unital Algebra\<close>

lemma \<phi>Some_def': \<open> \<black_circle> T = (Some \<Zcomp>\<^sub>f T) \<close>
  by (rule \<phi>Type_eqI_BI; simp add: BI_eq_iff)

local_setup \<open>
  Phi_Type.add_type {no_auto=false}
        (\<^binding>\<open>\<phi>Some\<close>, \<^pattern>\<open>\<phi>Some\<close>, Phi_Type.DIRECT_DEF (Thm.transfer \<^theory> @{thm' \<phi>Some_def'}),
         \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>
  \<comment> \<open>Setup an alternative definition in the language of \<phi>-types so that we can apply
      derivers over these bootstrap \<phi>-types\<close>

let_\<phi>type \<phi>Some
  deriving Sep_Functor_1
       and Abstract_Domain\<^sub>L
       and Carrier_Set
       and Functionality
       and \<open>Identity_Elements\<^sub>I (\<black_circle> T) (\<lambda>_. False) (\<lambda>_. False)\<close>
       and \<open>Identity_Elements\<^sub>E (\<black_circle> T) (\<lambda>_. False)\<close>
       and \<open>c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<Longrightarrow> Some c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> T\<close>
       and \<open> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::('c, 'c) \<phi>) \<s>\<u>\<b>\<j> y. r x y @tag to (Itself::('c, 'c) \<phi>))
         \<Longrightarrow> \<forall>x'. x' \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::('c option, 'c option) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = Some x \<and> r x' x) @tag to (Itself::('c option, 'c option) \<phi>) \<close>


text \<open>For technical reasons, the \<open>\<phi>Some\<close> is defined and used before the setup of the derivation system.
  Therefore some of its rules are handcrafted. However, the rules could all be derived automatically
  if the derivation was ready. To show this, below we re-define the \<open>\<phi>Some\<close> using another name \<open>\<phi>Some'\<close>,
  and we show all rules and properties are indeed derived automatically.\<close>

\<phi>type_def \<phi>Some' :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close>
  where \<open>\<phi>Some' T \<equiv> Some \<Zcomp>\<^sub>f T\<close>
  deriving Sep_Functor
       and Abstract_Domain\<^sub>L
       and Carrier_Set
       and Functionality
       and \<open>Identity_Elements\<^sub>I (\<phi>Some' T) (\<lambda>_. False) (\<lambda>_. False)\<close>
       and \<open>Identity_Elements\<^sub>E (\<phi>Some' T) (\<lambda>_. False)\<close>




subsection \<open>Domainoid\<close>
   
\<phi>type_def Domainoid ("\<DD>[_]" [4] 1000)
    where \<open>\<DD>[\<delta>] T \<equiv> \<delta> \<Zcomp>\<^sub>f T \<phi>\<s>\<u>\<b>\<j> closed_homo_sep \<delta>\<close>
  \<comment> \<open>\<open>\<Psi>[\<psi>] (x \<Ztypecolon> T) \<equiv> x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T\<close>, therefore \<open>\<phi>Fun \<psi> \<Zcomp> T\<close> is always an exact solution for
      evaluating \<open>\<Psi>[\<psi>] (x \<Ztypecolon> T)\<close>. However, in the case of domainoid extraction, this is not a
      final expression directly giving the domainoids of resources. We want a direct expression
      even if just an upper or lower approximation. Due to this, here
      we introduce a differentiated syntax to emphasize the intention of extracting domainoid,
      on which specific reasoning procedures can be given to reduce the expression further.\<close>
 deriving Sep_Functor
      and Abstract_Domain\<^sub>L
      and \<open> constant_1 \<delta> \<and>\<^sub>\<r> (D,P) = (\<lambda>_. True, \<lambda>_. True) \<or>\<^sub>c\<^sub>u\<^sub>t
            homo_one \<delta> \<and>\<^sub>\<r> Identity_Elements\<^sub>I T D P
        \<Longrightarrow> Identity_Elements\<^sub>I (\<DD>[\<delta>] T) D P \<close>

      and \<open> closed_homo_sep \<delta>
        \<Longrightarrow> constant_1 \<delta> \<and>\<^sub>\<r> Abstract_Domain\<^sub>L T D \<or>\<^sub>c\<^sub>u\<^sub>t
            homo_one \<delta> \<and>\<^sub>\<r> Identity_Elements\<^sub>E T D
        \<Longrightarrow> Identity_Elements\<^sub>E (\<DD>[\<delta>] T) D \<close>

      and Commutativity_Deriver
      and \<open> comm_domainoid_mapper_rev TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' f f'
        \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>'] ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

      and \<open> comm_domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' f f'
        \<Longrightarrow> Tyops_Commute ((\<Zcomp>\<^sub>f) f) ((\<Zcomp>\<^sub>f) f') \<DD>[\<delta>] \<DD>[\<delta>'] T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>


subsubsection \<open>Basic Rules\<close>

lemma WS_domainoid:
  \<open> closed_homo_sep \<delta>
\<Longrightarrow> \<Psi>[domainoid_tag \<delta>] (x \<Ztypecolon> T) = (x \<Ztypecolon> \<DD>[\<delta>] T) \<close>
  unfolding Domainoid.unfold BI_eq_iff domainoid_tag_def
  by clarsimp


subsubsection \<open>Approximating Domainoid\<close>

declare [[\<phi>reason_default_pattern \<open>_ \<le> (_ \<Ztypecolon> \<DD>[?d] ?T)\<close> \<Rightarrow> \<open>?var \<le> (_ \<Ztypecolon> \<DD>[?d] ?T)\<close> (300)
                              and \<open>(_ \<Ztypecolon> \<DD>[?d] ?T) \<le> _\<close> \<Rightarrow> \<open>(_ \<Ztypecolon> \<DD>[?d] ?T) \<le> ?var\<close> (300) ]]

lemma [\<phi>reason %BI_approx_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> closed_homo_sep \<delta>
\<Longrightarrow> A' \<le> (x \<Ztypecolon> \<DD>[\<delta>] T)
\<Longrightarrow> A' \<le> \<Psi>[domainoid_tag \<delta>] (x \<Ztypecolon> T) \<close>
  unfolding Premise_def
  by (simp add: WS_domainoid)

lemma [\<phi>reason %BI_approx_cut]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> closed_homo_sep \<delta>
\<Longrightarrow> (x \<Ztypecolon> \<DD>[\<delta>] T) \<le> A'
\<Longrightarrow> \<Psi>[domainoid_tag \<delta>] (x \<Ztypecolon> T) \<le> A' \<close>
  unfolding Premise_def
  by (simp add: WS_domainoid)

lemma [\<phi>reason %BI_approx_success]:
  \<open> (x \<Ztypecolon> \<DD>[(\<lambda>_. d)] T) \<le> (d \<Ztypecolon> Itself) \<close>
  unfolding BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason %BI_approx_success]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Satisfiable (x \<Ztypecolon> T)
\<Longrightarrow> (d \<Ztypecolon> Itself) \<le> (x \<Ztypecolon> \<DD>[(\<lambda>_. d)] T) \<close>
  for T :: \<open>('c::discrete_semigroup,'a) \<phi>\<close>
  and d :: \<open>'d::discrete_semigroup\<close>
  unfolding BI_sub_transformation Transformation_def Premise_def Satisfiable_def
  by clarsimp

lemma [\<phi>reason %BI_approx_success]:
  \<open> (x \<Ztypecolon> \<DD>[(\<lambda>d. d)] T) \<le> (x \<Ztypecolon> T) \<close>
  unfolding BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason %BI_approx_success]:
  \<open> (x \<Ztypecolon> T) \<le> (x \<Ztypecolon> \<DD>[(\<lambda>d. d)] T) \<close>
  unfolding BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason_template %BI_approx_derived]:
  \<open> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>'] G G' T D (embedded_func f P)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> (f x \<Ztypecolon> G' (\<DD>[\<delta>'] T)) \<le> A'
\<Longrightarrow> (x \<Ztypecolon> \<DD>[\<delta>] (G T)) \<le> A' \<close>
  unfolding Premise_def Tyops_Commute_def BI_sub_transformation Transformation_def
  by clarsimp

lemma [\<phi>reason_template %BI_approx_derived]:
  \<open> Tyops_Commute G' G \<DD>[\<delta>'] \<DD>[\<delta>] T D (embedded_func f P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> f x = y \<and> D x
\<Longrightarrow> A' \<le> (x \<Ztypecolon> G' (\<DD>[\<delta>'] T))
\<Longrightarrow> A' \<le> (y \<Ztypecolon> \<DD>[\<delta>] (G T)) \<close>
  unfolding Premise_def Tyops_Commute_def BI_sub_transformation Transformation_def
  by clarsimp blast


paragraph \<open>Guess the Forms\<close>

lemma [\<phi>reason %guess_tyop_commute for \<open>Guess_Tyops_Commute False \<DD>[_] ?var _ ?var_F' _ _ _ _ _ _ _ _ _\<close> ]:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>'
\<Longrightarrow> Guess_Tyops_Commute False \<DD>[\<delta>] \<DD>[\<delta>'] F F' uG uG' uF uF' T D r a c
\<Longrightarrow> Guess_Tyops_Commute False \<DD>[\<delta>] \<DD>[\<delta>'] F F' uG uG' uF uF' T D r a c \<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute for \<open>Guess_Tyops_Commute True _ ?var_F' \<DD>[_] ?var _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>'
\<Longrightarrow> Guess_Tyops_Commute True F F' \<DD>[\<delta>] \<DD>[\<delta>'] uG uG' uF uF' T D r a c
\<Longrightarrow> Guess_Tyops_Commute True F F' \<DD>[\<delta>] \<DD>[\<delta>'] uG uG' uF uF' T D r a c \<close>
  unfolding Guess_Tyops_Commute_def ..


subsubsection \<open>Application \label{phi-types/Domainoid/App}\<close>
  
lemma [\<phi>reason %abstract_domain]:
  \<open> Abstract_Domain\<^sub>L T D\<^sub>T
\<Longrightarrow> Abstract_Domain\<^sub>L U D\<^sub>U
\<Longrightarrow> domainoid TYPE('c::sep_magma) \<delta>
\<Longrightarrow> (\<And>x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (closed_homo_sep \<delta> \<and> Satisfiable (x \<Ztypecolon> T)) \<Longrightarrow> (f x \<Ztypecolon> T') \<le> (x \<Ztypecolon> \<DD>[\<delta>] T))
          \<comment>\<open>expand \<open>\<Psi>[d] A, \<Psi>[d] B\<close> to a simpler (but should still strong) upper approximation\<close>
\<Longrightarrow> (\<And>y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (closed_homo_sep \<delta> \<and> Satisfiable (y \<Ztypecolon> U)) \<Longrightarrow> (g y \<Ztypecolon> U') \<le> (y \<Ztypecolon> \<DD>[\<delta>] U))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x y. D\<^sub>T x \<and> D\<^sub>U y \<longrightarrow> (\<exists>a b. a \<Turnstile> (f x \<Ztypecolon> T') \<and> b \<Turnstile> (g y \<Ztypecolon> U') \<and> a ## b))
\<Longrightarrow> Abstract_Domain\<^sub>L (T \<^emph> U) (\<lambda>(x,y). D\<^sub>T x \<and> D\<^sub>U y)\<close>
  unfolding Satisfiable_def BI_sub_iff Premise_def Action_Tag_def domainoid_def domainoid_tag_def
            Abstract_Domain\<^sub>L_def \<r>ESC_def
  apply (clarsimp simp add: closed_homo_sep_def closed_homo_sep_disj_def)
  by metis



subsection \<open>Vertical Composition of Scalar Multiplication\<close>


\<phi>type_def \<phi>ScalarMul :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 's \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close> ("\<s>\<c>\<a>\<l>\<a>\<r>[_] _ \<Zcomp> _" [31,31,30] 30)
  where \<open>\<phi>ScalarMul f s T = (scalar_mult f s \<Zcomp>\<^sub>f T)\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 (f s)
         \<Longrightarrow> Identity_Elements\<^sub>I T D P
         \<Longrightarrow> Identity_Elements\<^sub>I (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) D P \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one (f s)
         \<Longrightarrow> Identity_Elements\<^sub>I T D P
         \<Longrightarrow> Identity_Elements\<^sub>I (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) D P \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>I (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) (\<lambda>x. \<forall>v. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> f s v = 1) (\<lambda>x. Satisfiable (x \<Ztypecolon> T))\<close>
           (%identity_elements_of_\<phi>Fun)
       and \<open> \<g>\<u>\<a>\<r>\<d> constant_1 (f s)
         \<Longrightarrow> Identity_Elements\<^sub>E (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) (\<lambda>x. Satisfiable (x \<Ztypecolon> T)) \<close>
           (%identity_elements_of_\<phi>Fun+40)
       and \<open> \<g>\<u>\<a>\<r>\<d> homo_one (f s)
         \<Longrightarrow> Identity_Elements\<^sub>E T D
         \<Longrightarrow> Identity_Elements\<^sub>E (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) D \<close>
           (%identity_elements_of_\<phi>Fun+20)
       and \<open> Identity_Elements\<^sub>E (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T) (\<lambda>x. \<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> f s v = 1) \<close>
           (%identity_elements_of_\<phi>Fun)
       and Functionality
       and Functional_Transformation_Functor
       and \<open> homo_sep (scalar_mult \<psi> s)
         \<Longrightarrow> closed_homo_sep (scalar_mult \<psi> s) \<or>\<^sub>c\<^sub>u\<^sub>t
             Separation_Disj\<^sub>\<phi> (scalar_mult \<psi> s) Dx T U
         \<Longrightarrow> Separation_Homo\<^sub>I (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) T U Dx (\<lambda>x. x)\<close>
       and \<open> homo_sep (\<psi> s)
         \<Longrightarrow> Separation_Homo\<^sub>E (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) (\<phi>ScalarMul \<psi> s) T U (\<lambda>x. x) \<close>
       and \<open> homo_mul_carrier (f s) \<Longrightarrow> Carrier_Set U P \<Longrightarrow> Carrier_Set (\<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> U) P \<close>
       and \<phi>Fun'.Comm
       and Commutativity_Deriver
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] inj (f s)
         \<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 (\<phi>ScalarMul f s) (\<phi>ScalarMul f s) (\<phi>ScalarMul f s) (\<and>\<^sub>\<phi>) (\<and>\<^sub>\<phi>) T U
                             (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True))\<close>

       and \<open> comm_domainoid_mapper TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' (scalar_mult f s) (scalar_mult f' s')
        \<Longrightarrow> Tyops_Commute (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') \<DD>[\<delta>] \<DD>[\<delta>'] T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

       and \<open> comm_domainoid_mapper_rev TYPE('c\<^sub>1::sep_magma) TYPE('c\<^sub>2::sep_magma) \<delta> \<delta>' (scalar_mult f s) (scalar_mult f' s')
        \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>'] (\<phi>ScalarMul f s) (\<phi>ScalarMul f' s') T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

       and \<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> scalar_mult ?f ?s ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T \<close>
       and \<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c2,?'c2) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @tag to (Itself::(?'c2,?'c2) \<phi>))
         \<Longrightarrow> \<forall>x'. x' \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c,?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = ?f ?s x \<and> ?r x' x) @tag to (Itself::(?'c,?'c) \<phi>) \<close>


declare [[\<phi>ToA_assoc_normalization \<open>\<s>\<c>\<a>\<l>\<a>\<r>[?f] ?s \<Zcomp> \<s>\<c>\<a>\<l>\<a>\<r>[?f] ?t \<Zcomp> ?T\<close> (100)]]



subsubsection \<open>Reasoning Rules\<close>

lemma Semimodule_One\<^sub>I_by_function [\<phi>reason 1000]:
  \<open> module_scalar_identity \<psi>
\<Longrightarrow> Semimodule_One\<^sub>I (\<lambda>s. \<phi>ScalarMul \<psi> s T) T 1 (\<lambda>_. True) (\<lambda>x. x) (\<lambda>_. True) \<close>
  unfolding Semimodule_One\<^sub>I_def module_scalar_identity_def scalar_mult_def BI_eq_iff
            Transformation_def
  by clarsimp

lemma Semimodule_One\<^sub>E_by_function [\<phi>reason 1000]:
  \<open> module_scalar_identity \<psi>
\<Longrightarrow> Semimodule_One\<^sub>E (\<lambda>s. \<phi>ScalarMul \<psi> s T) T 1 (\<lambda>_. True) (\<lambda>x. x) (\<lambda>_. True) \<close>
  unfolding Semimodule_One\<^sub>E_def module_scalar_identity_def scalar_mult_def BI_eq_iff
            Transformation_def
  by clarsimp

lemma Semimodule_Scalar_Assoc\<^sub>I_by_function[\<phi>reason 1000]:
  \<open> module_scalar_assoc \<psi> Ds
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) T Ds Ds (\<lambda>_ _ _. True) (*) (\<lambda>_ _ x. x) \<close>
  unfolding module_scalar_assoc_def Semimodule_Scalar_Assoc\<^sub>I_def scalar_mult_def Transformation_def
  by (clarsimp; blast)

lemma Semimodule_Scalar_Assoc\<^sub>E_by_function[\<phi>reason 1000]:
  \<open> module_scalar_assoc \<psi> Ds
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) (\<phi>ScalarMul \<psi>) T Ds Ds (\<lambda>_ _ _. True) (*) (\<lambda>_ _ x. x) \<close>
  unfolding module_scalar_assoc_def Semimodule_Scalar_Assoc\<^sub>E_def scalar_mult_def Transformation_def
  by clarsimp metis

lemma Semimodule_SDistr_Homo\<^sub>Z_by_function[\<phi>reason 1000]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Functionality T Dx
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> Carrier_Set T D\<^sub>C
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z (\<lambda>s. \<phi>ScalarMul \<psi> s T) Ds
                            (\<lambda>s t (x,y). (eq x y \<and> Dx y \<and> D\<^sub>C y \<or> eq y x \<and> Dx x \<and> D\<^sub>C x))
                            (\<lambda>_ _. fst) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Transformation_def module_S_distr_def Is_Functional_def
            Object_Equiv_def Functionality_def Abstract_Domain_def Action_Tag_def Satisfiable_def
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
 
lemma Semimodule_SDistr_Homo\<^sub>S_by_function[\<phi>reason 1000]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Carrier_Set T D\<^sub>C
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S (\<lambda>s. \<phi>ScalarMul \<psi> s T) Ds
                            (\<lambda>s t x. Dx x \<and> D\<^sub>C x)
                            (\<lambda>_ _ x. (x,x))\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def Transformation_def module_S_distr_def Is_Functional_def
            Object_Equiv_def Functionality_def Action_Tag_def Satisfiable_def
            scalar_mult_def Carrier_Set_def Within_Carrier_Set_def
  by (clarsimp, metis)


subsubsection \<open>Commutativity\<close>

paragraph \<open>Guessing Property\<close>

declare Guess_Tyops_Commute_by_unfolding
        [where A=\<open>\<lambda>T x. (x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[f] s \<Zcomp> T)\<close> for f s,
         OF \<phi>ScalarMul.unfold,
         \<phi>reason %guess_tyop_commute]

paragraph \<open>Deriving the Commutativity with Itself\<close>

declare [[\<phi>trace_reasoning = 0]]

let_\<phi>type \<phi>ScalarMul deriving \<phi>ScalarMul.Comm\<^sub>I


subsubsection \<open>Guessing Antecedents\<close>

lemma [\<phi>reason %\<phi>TA_guesser for \<open>Guess_Zip_of_Semimodule _ _ _ _ (\<lambda>s x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?\<psi>] s \<Zcomp> ?T) _ _ _ _ _ \<close>]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA F (\<lambda>s x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[\<psi>] s \<Zcomp> T) Ds
                            (\<lambda>s t (x,y). (eq x y \<and> Dx y \<and> D\<^sub>C y \<or> eq y x \<and> Dx x \<and> D\<^sub>C x))
                            (\<lambda>_ _. fst)
                            (Functionality T Dx \<and>\<^sub>\<r> Object_Equiv T eq \<and>\<^sub>\<r> Carrier_Set T D\<^sub>C)
                            True \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser for \<open>Guess_Unzip_of_Semimodule _ _ _ _ (\<lambda>s x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[?\<psi>] s \<Zcomp> ?T) _ _ _ _ _ \<close>]:
  \<open> module_S_distr \<psi> Ds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA F (\<lambda>s x. x \<Ztypecolon> \<s>\<c>\<a>\<l>\<a>\<r>[\<psi>] s \<Zcomp> T) Ds
                            (\<lambda>s t x. Dx x \<and> D\<^sub>C x)
                            (\<lambda>_ _ x. (x,x))
                            (Functionality T Dx \<and>\<^sub>\<r> Carrier_Set T D\<^sub>C)
                            True \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..


subsubsection \<open>Configuration\<close>

setup \<open>Context.theory_map (Phi_Type.Defining_Phi_Type.add 12 (fn phi => fn thy =>
  let exception Found of term * term
      fun find (X as Const(\<^const_name>\<open>\<phi>Composition\<close>, _) $ (Const(\<^const_name>\<open>\<phi>Fun\<close>, _) $ f) $ T)
            = raise Found (X, Const(\<^const_name>\<open>\<phi>Fun'\<close>, dummyT) $ f $ T)
        | find (A $ B) = (find A; find B)
        | find (Abs (_, _, X)) = find X
        | find _ = ()

      open Pretty
      val _ = List.app (find o Thm.prop_of) (#equations phi)
              handle Found (X,Y) => Phi_Reasoner.warn_pretty (Context.Proof thy) 0 (fn () =>
                  paragraph (text "We have noticed you are using" @ [brk 1,
                      Syntax.pretty_term thy X, brk 1] @
                      text "instead of a more specific \<phi>-type" @ [brk 1,
                      Syntax.pretty_term thy Y, str ".", brk 1] @
                      text "We highly recommend the later form which replaces the former totally and\
                           \ have more general automation on separation homomorphism." ))
   in thy
  end))\<close>


section \<open>Structural Connectives\<close>

subsection \<open>List Item \& Empty List\<close>

subsubsection \<open>List Item\<close>

\<phi>type_def List_Item :: \<open>('v, 'a) \<phi> \<Rightarrow> ('v list, 'a) \<phi>\<close>
  where \<open>List_Item T \<equiv> (\<lambda>v. [v]) \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and Functional_Transformation_Functor
       and Carrier_Set
       and \<phi>Inter.Comm\<^sub>E


lemma \<comment> \<open>A example for how to represent list of multi-elements\<close>
  \<open> v1 \<Turnstile> (x1 \<Ztypecolon> T1)
\<Longrightarrow> v2 \<Turnstile> (x2 \<Ztypecolon> T2)
\<Longrightarrow> [v1,v2] \<Turnstile> ((x1, x2) \<Ztypecolon> (List_Item T1 \<^emph> List_Item T2))\<close>
  by (simp add: times_list_def,
      rule exI[where x=\<open>[v1]\<close>],
      rule exI[where x=\<open>[v2]\<close>],
      simp)


subsubsection \<open>Empty List\<close>
     
\<phi>type_def Empty_List :: \<open>('v list, unit) \<phi>\<close>
  where \<open>Empty_List = (\<lambda>x. [] \<Ztypecolon> Itself)\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and Identity_Elements
       and Abstraction_to_Raw


subsection \<open>Option Abstraction of Unital Algebra\<close>


   
\<phi>type_def \<phi>Option :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x option) \<phi>\<close> ("\<half_blkcirc> _" [91] 90)
  where \<open>\<half_blkcirc> T = (\<lambda>x. if x = None then 1 else the x \<Ztypecolon> \<black_circle> T)\<close>
  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (\<half_blkcirc> T) (pred_option P) \<close>
       and \<open>Abstract_Domain\<^sub>L T P \<Longrightarrow> Abstract_Domain\<^sub>L (\<half_blkcirc> T) (pred_option P) \<close>
       and \<open>Functionality T P \<Longrightarrow> Functionality (\<half_blkcirc> T) (case_option True P)\<close>
       and \<open>Identity_Elements\<^sub>I (\<half_blkcirc> T) (\<lambda>x. x = None) (\<lambda>a. True)\<close>
       and \<open>Identity_Elements\<^sub>E (\<half_blkcirc> T) (\<lambda>x. x = None)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<half_blkcirc> T) (rel_option eq)\<close>
       and \<open>Transformation_Functor \<phi>Option \<phi>Option T U set_option (\<lambda>_. UNIV) rel_option \<close>
       and \<open>Functional_Transformation_Functor \<phi>Option \<phi>Option T U set_option (\<lambda>_. UNIV) (\<lambda>_. pred_option) (\<lambda>f _. map_option f)\<close>

lemma [\<phi>reason %ToA_cut]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Some y \<Ztypecolon> \<half_blkcirc> U \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Option.unfold 
  \<medium_left_bracket> premises [\<phi>reason add] \<medium_right_bracket> .

lemma [\<phi>reason %ToA_cut]:
  \<open> x \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> None \<Ztypecolon> \<half_blkcirc> T \<close>
  unfolding \<phi>Option.unfold 
  \<medium_left_bracket> \<medium_right_bracket> .

lemma [\<phi>reason %ToA_cut]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<noteq> None
\<Longrightarrow> the x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Option.unfold 
  \<medium_left_bracket> premises [\<phi>reason add] \<medium_right_bracket> certified by auto_sledgehammer .

lemma [\<phi>reason %ToA_cut]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x = None
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> () \<Ztypecolon> \<circle> \<close>
  unfolding \<phi>Option.unfold 
  \<medium_left_bracket> \<medium_right_bracket> .

(*
term \<open>Separation_Homo\<^sub>I \<phi>Option \<phi>Option \<phi>Option T U UNIV \<close>
term \<open>rel_option r\<close>
term set_option
term \<open>Transformation_Functor \<phi>Option \<phi>Option T U set_option (\<lambda>_. UNIV) rel_option \<close>
term \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (\<half_blkcirc> T) (rel_option eq)\<close>
term \<open>Identity_Elements\<^sub>E (\<half_blkcirc> T) (\<lambda>x. x = None)\<close>
*)





subsection \<open>Point on a Mapping\<close>

subsubsection \<open>By Key\<close>
    
\<phi>type_def \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 75)
  where \<open>\<phi>MapAt k T = (fun_upd 1 k \<Zcomp>\<^sub>f T)\<close>
  deriving Sep_Functor_1
       and Abstract_Domain\<^sub>L
       and Functionality
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm
       and \<phi>Inter.Comm\<^sub>E
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) \<DD>[\<delta>] \<DD>[(\<circ>) \<delta>] Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute \<DD>[(\<circ>) \<delta>] \<DD>[\<delta>] ((\<^bold>\<rightarrow>) k) ((\<^bold>\<rightarrow>) k) Ta (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>

       and \<open>?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> 1(?k := ?c) \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?k \<^bold>\<rightarrow> ?T\<close>
       and \<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'c::one,?'c) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @tag to (Itself::(?'c,?'c) \<phi>))
         \<Longrightarrow> \<forall>x'. x' \<Ztypecolon> ?k \<^bold>\<rightarrow> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'a \<Rightarrow> ?'c, ?'a \<Rightarrow> ?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = 1(?k := x) \<and> ?r x' x) @tag to (Itself::(?'a \<Rightarrow> ?'c, ?'a \<Rightarrow> ?'c) \<phi>)\<close>


\<phi>adhoc_overloading \<phi>coercion \<open>\<lambda>T. [] \<^bold>\<rightarrow> T\<close>


subsubsection \<open>By List of Keys\<close>

\<phi>type_def \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 75)
  where \<open>\<phi>MapAt_L k T = (\<s>\<c>\<a>\<l>\<a>\<r>[push_map] k \<Zcomp> T)\<close>
  deriving Sep_Functor_1
       and Abstract_Domain\<^sub>L
       and Functionality
       and Semimodule_NonDistr_no0
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm
       and \<phi>Inter.Comm\<^sub>E
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute \<DD>[(o) \<delta>] \<DD>[(o) \<delta>] ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) T (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
       and \<open>homo_one \<delta>
        \<Longrightarrow> Tyops_Commute ((\<^bold>\<rightarrow>\<^sub>@) k) ((\<^bold>\<rightarrow>\<^sub>@) k) \<DD>[(o) \<delta>] \<DD>[(o) \<delta>] T (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
       and \<open> ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T \<Longrightarrow> scalar_mult (\<tribullet>\<^sub>m) ?k ?c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?T  \<close>
       and \<open> (\<And>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'a list \<Rightarrow> ?'c::one, ?'a list \<Rightarrow> ?'c) \<phi>) \<s>\<u>\<b>\<j> y. ?r x y @tag to (Itself::(?'a list \<Rightarrow> ?'c, ?'a list \<Rightarrow> ?'c) \<phi>))
        \<Longrightarrow> \<forall>x'. x' \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (Itself::(?'a list \<Rightarrow> ?'c, ?'a list \<Rightarrow> ?'c) \<phi>) \<s>\<u>\<b>\<j> y. (\<exists>x. y = ?k \<tribullet>\<^sub>m x \<and> ?r x' x) @tag to (Itself::(?'a list \<Rightarrow> ?'c, ?'a list \<Rightarrow> ?'c) \<phi>) \<close>


declare [[\<phi>ToA_assoc_normalization \<open>?k\<^sub>1 \<^bold>\<rightarrow>\<^sub>@ ?k\<^sub>2 \<^bold>\<rightarrow>\<^sub>@ ?T\<close> (100)]]


abbreviation \<phi>MapAt_L1 :: \<open>'key \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>#" 75)
  where \<open>\<phi>MapAt_L1 key \<equiv> \<phi>MapAt_L [key]\<close>

abbreviation \<phi>MapAt_Lnil :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>[\<^sub>]" 75)
  where \<open>\<phi>MapAt_Lnil key T \<equiv> \<phi>MapAt_L [key] (\<phi>MapAt [] T)\<close>



subsection \<open>Permission Sharing\<close>

\<phi>type_def \<phi>Share :: \<open>rat \<Rightarrow> ('c::share,'a) \<phi> \<Rightarrow> ('c, 'a) \<phi>\<close> (infixr "\<odiv>" 75)
  where \<open>\<phi>Share n T = (\<s>\<c>\<a>\<l>\<a>\<r>[share] n \<Zcomp> T \<phi>\<s>\<u>\<b>\<j> 0 < n)\<close>
  deriving Sep_Functor_1
       and Abstract_Domain\<^sub>L
       and Functionality

       and Semimodule_no0
       and \<open>Functionality (T::('c::share_semimodule, 'x) \<phi>) Dx
        \<Longrightarrow> Carrier_Set T D\<^sub>C
        \<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S (\<lambda>\<s>. \<s> \<odiv> T) ((<) 0) (\<lambda>s t xy. 0 < s + t \<longrightarrow> Dx xy \<and> D\<^sub>C xy) (\<lambda>_ _ x. (x, x))\<close>

       and Carrier_Set
       and Commutativity_Deriver
       and \<phi>Fun'.Comm
       and \<phi>ScalarMul.Comm
       and \<phi>MapAt.Comm
       and \<phi>MapAt_L.Comm

       and \<open>homo_share \<delta>
        \<Longrightarrow> Tyops_Commute ((\<odiv>) n) ((\<odiv>) n) \<DD>[\<delta>] \<DD>[\<delta>] T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>
       and \<open>homo_share \<delta>
        \<Longrightarrow> Tyops_Commute \<DD>[\<delta>] \<DD>[\<delta>] ((\<odiv>) n) ((\<odiv>) n) T (\<lambda>x. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close>


declare [[\<phi>ToA_assoc_normalization \<open>?n \<odiv> ?m \<odiv> ?T\<close> (100)]]

declare \<phi>Share.\<Sigma>\<^sub>I[where c=fst, simplified, \<phi>reason add]
        \<phi>Share.\<Sigma>\<^sub>E[\<phi>reason add]

        \<phi>Share.\<S>\<^sub>E[where g=\<open>\<lambda>x. x\<close> and f=\<open>\<lambda>s _ _. s\<close>, unfolded Ball_def, simplified, \<phi>reason add]
        \<phi>Share.\<S>\<^sub>I[\<phi>reason add]

declare \<phi>Dependent_Sum.\<phi>Share.rewr[where n=n and na=n for n, OF \<r>Guard_I, OF Premise_I, OF HOL.refl,
                                   simp, assertion_simps]
        Set_Abst.\<phi>Share.rewr      [where n=n and na=n for n, OF \<r>Guard_I, OF Premise_I, OF HOL.refl,
                                   simp, assertion_simps]
        \<phi>Share.\<phi>Prod              [symmetric, assertion_simps]

declare [[\<phi>ToA_swap_normalization \<open>(\<odiv>) ?n\<close> into \<dots> (100)]]



subsection \<open>Injection from partial map to permissioned partial map\<close>

\<phi>type_def To_Share
  where \<open>To_Share T \<equiv> (to_share \<Zcomp>\<^sub>f T)\<close>
  deriving Sep_Functor_1
       and Abstract_Domain\<^sub>L
       and \<open>Separation_Homo\<^sub>E (To_Share :: ('c::discrete_semigroup option,'a) \<phi> \<Rightarrow> ('c share option,'a) \<phi>) To_Share To_Share T U (\<lambda>x. x) \<close>
       and \<open>Separation_Disj\<^sub>\<phi> to_share Dx T U
        \<Longrightarrow> Separation_Homo\<^sub>I (To_Share :: ('c::discrete_semigroup option,'a) \<phi> \<Rightarrow> ('c share option,'a) \<phi>) To_Share To_Share T U Dx (\<lambda>x. x) \<close>
       and Functionality
       and Carrier_Set

declare To_Share.\<Sigma>\<^sub>I[where c=fst, simplified, \<phi>reason add]
        To_Share.\<Sigma>\<^sub>E[\<phi>reason add]




subsubsection \<open>Syntax\<close>

abbreviation \<phi>Share_Some ("\<fish_eye> _" [91] 90)
  where \<open>\<phi>Share_Some T \<equiv> To_Share (\<phi>Some T)\<close>

abbreviation \<phi>Share_Some_L ("\<fish_eye>\<^sub>L _" [91] 90)
  where \<open>\<phi>Share_Some_L T \<equiv> [] \<^bold>\<rightarrow> To_Share (\<phi>Some T)\<close>

\<phi>adhoc_overloading \<phi>coercion \<phi>Some \<phi>Share_Some \<phi>Share_Some_L


subsection \<open>Injection into Discrete Algebra\<close>
  
\<phi>type_def Discrete :: \<open>('c, 'a) \<phi> \<Rightarrow> ('c discrete, 'a) \<phi>\<close>
  where \<open>Discrete T = (discrete \<Zcomp>\<^sub>f T)\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and \<open>Carrier_Set (Discrete T) (\<lambda>_. True)\<close>
       and Functionality 
       and Functional_Transformation_Functor

\<phi>adhoc_overloading \<phi>coercion \<open>\<lambda>T. \<black_circle> Discrete T\<close> \<open>\<lambda>T. \<fish_eye> Discrete T\<close> \<open>\<lambda>T. \<fish_eye>\<^sub>L Discrete T\<close>

translations
  "\<coercion> T" <= "\<fish_eye> CONST Discrete T"


section \<open>Derivatives\<close>

subsection \<open>Parameterized FMQ\<close>

\<phi>type_def \<phi>Mul_Quant\<^sub>\<Lambda> :: \<open>'i set \<Rightarrow> ('i \<Rightarrow> ('c::sep_algebra, 'x) \<phi>) \<Rightarrow> ('c::sep_algebra, 'i \<Rightarrow> 'x) \<phi>\<close> ("\<big_ast>\<^sup>\<phi>")
  where \<open>x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T \<equiv> (i, x i) \<Ztypecolon> \<big_ast>\<^sub>0[i\<in>I] (\<Sigma> T)\<close>
  deriving \<open>(\<And>p. Object_Equiv (T p) (eq p))
        \<Longrightarrow> Object_Equiv (\<big_ast>\<^sup>\<phi> I T) (\<lambda>x y. \<forall>i \<in> I. eq i (x i) (y i))\<close>
       and \<open>(\<And>i. Carrier_Set (T i) (P i)) \<Longrightarrow> Carrier_Set (\<big_ast>\<^sup>\<phi> I T) (\<lambda>x. \<forall>i \<in> I. P i (x i)) \<close>
                \<comment> \<open>the guesser fails to realize the \<open>P\<close> can be parameterized, which is a specific
                    feature of \<open>\<phi>Mul_Quant\<^sub>\<Lambda>\<close>\<close>
       and \<open>(\<And>i. Functionality (T i) (P i)) \<Longrightarrow> Functionality (\<big_ast>\<^sup>\<phi> I T) (\<lambda>x. \<forall>i \<in> I. P i (x i)) \<close>
       and \<open> (\<And>i. Abstract_Domain (T i) (P i))
        \<Longrightarrow> Abstract_Domain (\<big_ast>\<^sup>\<phi> I T) (\<lambda>x. \<forall>i\<in>I. P i (x i)) \<close>  
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J
        \<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> J) T U (\<lambda>p x. x ` I) (\<lambda>_ _. UNIV) (\<lambda>g x y. \<forall>i\<in>I. g i (x i) (y i)) \<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J
        \<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> J) T U (\<lambda>p x. x ` I) (\<lambda>_ _. UNIV)
                                         (\<lambda>_ P x. \<forall>i\<in>I. P i (x i)) (\<lambda>f _ x i. f i (x i))\<close>
           \<comment> \<open>Gusser is not supported on most of the properties of quantifier \<phi>-types\<close>
       and Sep_Functor_1
       and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> I) T U UNIV zip_fun\<close>
       and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> I) (\<big_ast>\<^sup>\<phi> I) T U unzip_fun\<close>
       and Semimodule_NonAssoc 
       and \<open>Semimodule_One\<^sub>I (\<lambda>I. \<big_ast>\<^sup>\<phi> I T) (T i) {i} (\<lambda>_. True) (\<lambda>x _. x) (\<lambda>_. True)\<close>
       and \<open>Semimodule_One\<^sub>E (\<lambda>I. \<big_ast>\<^sup>\<phi> I T) (T i) {i} (\<lambda>_. True) (\<lambda>f. f i) (\<lambda>_. True)\<close>
       and \<open>Semimodule_SDistr_Homo\<^sub>Z (\<lambda>I. \<big_ast>\<^sup>\<phi> I T) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ D\<^sub>g (f,g). f \<oplus>\<^sub>f[D\<^sub>g] g)\<close>
       and \<open>Semimodule_SDistr_Homo\<^sub>S (\<lambda>I. \<big_ast>\<^sup>\<phi> I T) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ f. (f ,f))\<close>
       and \<open>Semimodule_Zero (\<lambda>I. \<big_ast>\<^sup>\<phi> I T) {}\<close>
       and \<open>Closed_Semimodule_Zero (\<lambda>I. \<big_ast>\<^sup>\<phi> I T) {}\<close>

lemma \<phi>Mul_Quant\<^sub>\<Lambda>_cong[cong]:
  \<open> (\<And>i. i \<in> I \<Longrightarrow> T i = U i)
\<Longrightarrow> \<big_ast>\<^sup>\<phi> I T = \<big_ast>\<^sup>\<phi> I U \<close>
  by (rule \<phi>Type_eqI; auto simp: Mul_Quant_def; smt (verit) prod.cong)


subsubsection \<open>Syntax\<close>

syntax
  "_\<phi>Mul_Quant"  :: "dom_idx \<Rightarrow> logic \<Rightarrow> logic"  ("(2\<big_ast>[_]/ _)" [49, 1000] 1000)

consts "\<phi>Mul_Quant'" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"

(*
print_ast_translation \<open> let open Ast
  fun append (Appl L) x = Appl (L @ [x])
    | append X x = Appl [X, x]
in [(\<^const_syntax>\<open>\<phi>Type\<close>, fn ctxt =>
  fn [Appl [Constant \<^syntax_const>\<open>_abs\<close>,
            Appl [Constant \<^syntax_const>\<open>_constrain\<close>, Appl [Constant \<^syntax_const>\<open>_bound\<close>, Variable vi], _],
            fx],
      Appl [Constant \<^const_syntax>\<open>\<phi>Mul_Quant\<^sub>\<Lambda>\<close>, Dom,
            Appl [Constant \<^syntax_const>\<open>_abs\<close>,
                  vjb as Appl [Constant \<^syntax_const>\<open>_constrain\<close>, Appl [Constant \<^syntax_const>\<open>_bound\<close>, Variable vj], _],
                  fT]]]
    => let fun subst (Variable v) = if v = vi then SOME (Variable vj) else NONE
             | subst (Appl L) =
                  let fun mapL [] = NONE
                        | mapL (x::L) = case (subst x, mapL L)
                                          of (SOME x', SOME L') => SOME (x'::L')
                                           | (SOME x', NONE) => SOME (x'::L)
                                           | (NONE, SOME L') => SOME (x::L')
                                           | (NONE, NONE) => NONE
                   in Option.map Appl (mapL L)
                  end
             | subst _ = NONE
           val fx' = if vi = vj then fx else the_default fx (subst fx)
        in Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>,
                 fx',
                 Appl [Constant \<^syntax_const>\<open>_\<phi>Mul_Quant\<close>,
                       Appl [Constant \<^syntax_const>\<open>_one_dom\<close>, vjb, Dom],
                       fT]]
       end
   | [Appl [Constant \<^syntax_const>\<open>_abs\<close>,
            vxb as Appl [Constant \<^syntax_const>\<open>_constrain\<close>, Appl [Constant \<^syntax_const>\<open>_bound\<close>, Variable vi], _],
            fx],
      Appl [Constant \<^const_syntax>\<open>\<phi>Mul_Quant\<^sub>\<Lambda>\<close>, Dom, T]]
    => Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, fx,
             Appl [Constant \<^syntax_const>\<open>_\<phi>Mul_Quant\<close>,
                   Appl [Constant \<^syntax_const>\<open>_one_dom\<close>, vxb, Dom], append T vxb]]
   | [x,
      Appl [Constant \<^const_syntax>\<open>\<phi>Mul_Quant\<^sub>\<Lambda>\<close>, Dom,
            Appl [Constant \<^syntax_const>\<open>_abs\<close>,
                  vjb as Appl [Constant \<^syntax_const>\<open>_constrain\<close>, Appl [Constant \<^syntax_const>\<open>_bound\<close>, Variable vj], _],
                  fT]]]
    => Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, append x vjb,
             Appl [Constant \<^syntax_const>\<open>_\<phi>Mul_Quant\<close>,
                   Appl [Constant \<^syntax_const>\<open>_one_dom\<close>, vjb, Dom],
                   fT]]
)] end \<close>
*)

translations
  "CONST \<phi>Type x (_\<phi>Mul_Quant (_one_dom i I) T)" => "CONST \<phi>Type (\<lambda>i. x) (CONST \<phi>Mul_Quant\<^sub>\<Lambda> I (\<lambda>i. T))"


subsubsection \<open>Reasoning\<close>

declare [[\<phi>trace_reasoning = 2]]

lemma \<phi>Mul_Quant\<^sub>\<Lambda>_wrap_module_src:
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> I \<longrightarrow> ((fst x, w) \<Ztypecolon> T \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U i \<OTast> R \<w>\<i>\<t>\<h> P @tag \<T>\<P>'))
       \<and>\<^sub>\<r> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> I
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y' i = fst y \<and> (\<forall>i \<in> I - {i}. y'' i = y' i)
\<Longrightarrow> snd x \<Ztypecolon> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (w, y'') \<Ztypecolon> W \<^emph> \<big_ast>\<^sup>\<phi> (I - {i}) U @clean
\<Longrightarrow> x \<Ztypecolon> T \<OTast> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y', snd y) \<Ztypecolon> \<big_ast>\<^sup>\<phi> I U \<OTast> R \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Action_Tag_def \<r>Guard_def Ant_Seq_imp \<phi>Prod'_def 
  apply (simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric])
  \<medium_left_bracket> premises Tr and _ and _ and C
    C Tr
  \<medium_right_bracket> .

lemma \<phi>Mul_Quant\<^sub>\<Lambda>_wrap_module_tgt:
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i \<in> I \<longrightarrow> ((fst x i, snd x) \<Ztypecolon> T i \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<OTast> R \<w>\<i>\<t>\<h> P @tag \<T>\<P>'))
                      \<comment> \<open>BUG!: must exclude trivial success!\<close>
       \<and>\<^sub>\<r> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] i \<in> I
\<Longrightarrow> (snd y, fst x) \<Ztypecolon> R \<^emph> \<big_ast>\<^sup>\<phi> (I - {i}) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> r \<Ztypecolon> R' @clean
\<Longrightarrow> x \<Ztypecolon> \<big_ast>\<^sup>\<phi> I T \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> U \<OTast> R' \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Action_Tag_def \<r>Guard_def Ant_Seq_imp \<phi>Prod'_def
  \<medium_left_bracket> premises Tr and _ and C
    Tr C
  \<medium_right_bracket> .


declare \<phi>Mul_Quant\<^sub>\<Lambda>.wrap_module_src[\<phi>reason del]
        \<phi>Mul_Quant\<^sub>\<Lambda>.wrap_module_tgt[\<phi>reason del]

declare \<phi>Mul_Quant\<^sub>\<Lambda>_wrap_module_src[\<phi>reason default %derived_SE_inj_to_module]
        \<phi>Mul_Quant\<^sub>\<Lambda>_wrap_module_tgt[\<phi>reason default %derived_SE_inj_to_module]

hide_fact \<phi>Mul_Quant\<^sub>\<Lambda>.wrap_module_src
          \<phi>Mul_Quant\<^sub>\<Lambda>.wrap_module_tgt



subsection \<open>From FMQ\<close>

subsubsection \<open>Interval in Length Representation\<close>

context begin

private lemma list_all2_single_length_1[simp]:
  \<open>list_all2 (=) [hd x] x \<longleftrightarrow> length x = Suc 0\<close>
  by (metis append_eq_conv_conj length_Suc_conv list.sel(1) list.size(3) list_all2_eq take0)

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def \<phi>Mul_Quant_LenIv :: \<open> nat len_intvl
                              \<Rightarrow> (nat \<Rightarrow> ('c::sep_algebra, 'x) \<phi>)
                              \<Rightarrow> ('c::sep_algebra, 'x list) \<phi>\<close> ("\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi>")
  where \<open>l \<Ztypecolon> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T \<equiv> (\<lambda>i. l ! (i - Len_Intvl.start iv)) \<Ztypecolon> \<big_ast>\<^sup>\<phi> (Len_Intvl.set iv) T \<s>\<u>\<b>\<j> length l = len_intvl.len iv\<close>
  deriving Sep_Functor_1
       and Semimodule_NonAssoc 
       and \<open>(\<And>i. Carrier_Set (T i) (P i))
        \<Longrightarrow> Carrier_Set (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>l. \<forall>i < Len_Intvl.len iv. P (Len_Intvl.start iv + i) (l ! i)) \<close>  
       and \<open>(\<And>i. Abstract_Domain (T i) (P i))
        \<Longrightarrow> Abstract_Domain (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>x. length x = len_intvl.len iv \<and>
                                             (\<forall>i < Len_Intvl.len iv. P (Len_Intvl.start iv + i) (x ! i))) \<close> \<comment> \<open>simplification is not satisfiable\<close>
       and \<open>(\<And>i. Object_Equiv (T i) (eq i))
        \<Longrightarrow> Object_Equiv (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>x y. length x = length y \<and> 
                                             (\<forall>i < Len_Intvl.len iv. eq (Len_Intvl.start iv + i) (x ! i) (y ! i)))\<close>
       and \<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> iv = iv'
        \<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv') T U (\<lambda>_. set) (\<lambda>_ x. UNIV)
                                    (\<lambda>r x y. length x = length y \<and> (\<forall>i < Len_Intvl.len iv. r (Len_Intvl.start iv + i) (x ! i) (y ! i))) \<close>
           (tactic: auto ; subgoal' for r l cc \<open>rule exI[where x=\<open>map cc [len_intvl.start iv' ..< len_intvl.start iv'+len_intvl.len iv']\<close>]\<close> )
       and \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> iv = iv'
        \<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv') T U (\<lambda>_. set) (\<lambda>_ x. UNIV)
                                               (\<lambda>f P x. \<forall>i < len_intvl.len iv. P (len_intvl.start iv + i) (x ! i))
                                               (\<lambda>f P. map_index (\<lambda>i. f (len_intvl.start iv + i))) \<close>
       and \<open>(\<And>i. Identity_Elements\<^sub>I (T i) (T\<^sub>D i) (T\<^sub>P i))
        \<Longrightarrow> Identity_Elements\<^sub>I (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T)
                               (\<lambda>x. \<forall>i < Len_Intvl.len iv. T\<^sub>D (len_intvl.start iv + i) (x ! i))
                               (\<lambda>x. length x = len_intvl.len iv \<and> (\<forall>i<len_intvl.len iv. T\<^sub>P (len_intvl.start iv + i) (x ! i))) \<close>
       and \<open>(\<And>i. Identity_Elements\<^sub>E (T i) (T\<^sub>D i))
        \<Longrightarrow> Identity_Elements\<^sub>E (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>x. length x = len_intvl.len iv \<and>
                                                (\<forall>i < len_intvl.len iv. T\<^sub>D (len_intvl.start iv + i) (x ! i))) \<close>
       and \<open>(\<And>i. Functionality (T i) (P i))
        \<Longrightarrow> Functionality (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>x. \<forall>i < len_intvl.len iv. P (len_intvl.start iv + i) (x ! i))\<close>
       and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) T U {(x, y). length x = length y} (case_prod zip)\<close>
       and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) (\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv) T U list.unzip\<close>
       and \<open> Semimodule_Zero (\<lambda>iv. \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) \<lbrakk>i : 0\<rwpar> \<close>
       and \<open> Semimodule_One\<^sub>I (\<lambda>iv. \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (T i) \<lbrakk>i : 1\<rwpar> (\<lambda>_. True) (\<lambda>x. [x]) (\<lambda>_. True) \<close>
       and \<open> Semimodule_One\<^sub>E (\<lambda>iv. \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (T i) \<lbrakk>i : 1\<rwpar> (\<lambda>l. length l = 1) hd (\<lambda>_. True) \<close>
       and \<open> Semimodule_SDistr_Homo\<^sub>S (\<lambda>iv. \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>_. True)
                                     (\<lambda>s t x. len_intvl.len s + len_intvl.len t = length x)
                                     (\<lambda>s t x. (take (len_intvl.len s) x, drop (len_intvl.len s) x)) \<close>
       and \<open> Semimodule_SDistr_Homo\<^sub>Z (\<lambda>iv. \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T) (\<lambda>_. True)
                                     (\<lambda>s t (x,y). len_intvl.len s = length x \<and> len_intvl.len t = length y) (\<lambda>s t (x,y). x @ y) \<close>

declare list_all2_single_length_1[simp del]

end

translations "\<big_ast> \<lbrakk>i:len\<rwpar> T" == "\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> \<lbrakk>i:len\<rwpar> T"

text \<open>TODO: \<phi>Mul_Quant_LenIv.ToA_mapper_sep, requires ToA_mapper_template_\<Lambda> x\<close>

paragraph \<open>Reasoning\<close>

lemma \<phi>Mul_Quant_LenIv_wrap_module_src:
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> y' ! (i - len_intvl.start iv) = fst y \<and> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv
          \<longrightarrow> ((fst x, w) \<Ztypecolon> T \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U i \<OTast> R i \<w>\<i>\<t>\<h> P @tag \<T>\<P>'))
       \<and>\<^sub>\<r> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> length y' = len_intvl.len iv \<and> y' ! (i - len_intvl.start iv) = fst y
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (j, len, j', len') : (len_intvl.start iv, i - len_intvl.start iv,
                                 i + 1, len_intvl.start iv + len_intvl.len iv - i - 1)
\<Longrightarrow> snd x \<Ztypecolon> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (w, take len y', drop (len+1) y') \<Ztypecolon> W \<^emph> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> \<lbrakk>j:len\<rwpar> U \<^emph> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> \<lbrakk>j':len'\<rwpar> U @clean
\<Longrightarrow> x \<Ztypecolon> T \<OTast> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y', snd y) \<Ztypecolon> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv U \<OTast> R i \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Action_Tag_def \<r>Guard_def Ant_Seq_imp \<phi>Prod'_def
  \<medium_left_bracket> premises Tr and _ and _ and _ and C[]
    C
    Tr
  \<medium_right_bracket> certified by (insert \<phi>, auto simp add: nth_append nth_Cons'; auto_sledgehammer) .

lemma \<phi>Mul_Quant_LenIv_wrap_module_tgt:
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv
          \<longrightarrow> ((fst x ! (i - len_intvl.start iv), snd x) \<Ztypecolon> T i \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<OTast> R \<w>\<i>\<t>\<h> P @tag \<T>\<P>'))
       \<and>\<^sub>\<r> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (j, len, j', len') : (len_intvl.start iv, i - len_intvl.start iv,
                                 i + 1, len_intvl.start iv + len_intvl.len iv - i - 1)
\<Longrightarrow> (snd y, take len (fst x), drop (len+1) (fst x)) \<Ztypecolon> R \<^emph> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> \<lbrakk>j:len\<rwpar> T \<^emph> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> \<lbrakk>j':len'\<rwpar> T
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> r \<Ztypecolon> R' @clean
\<Longrightarrow> x \<Ztypecolon> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv T \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> U \<OTast> R' \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Action_Tag_def \<r>Guard_def Ant_Seq_imp Simplify_def \<phi>Prod'_def
  \<medium_left_bracket> premises Tr and _ and _  and C
    note hd_drop_conv_nth[simp] \<phi>Some_\<phi>Prod[symmetric, simp] \<phi>Prod_expn'[simp]
    \<semicolon> Tr
      unfold One_nat_def
      C
  \<medium_right_bracket> .

declare \<phi>Mul_Quant_LenIv.wrap_module_src[\<phi>reason del]
        \<phi>Mul_Quant_LenIv.wrap_module_tgt[\<phi>reason del]

declare \<phi>Mul_Quant_LenIv_wrap_module_src[\<phi>reason default %derived_SE_inj_to_module]
        \<phi>Mul_Quant_LenIv_wrap_module_tgt[\<phi>reason default %derived_SE_inj_to_module]

hide_fact \<phi>Mul_Quant_LenIv.wrap_module_src
          \<phi>Mul_Quant_LenIv.wrap_module_tgt



subsubsection \<open>Array of Tree Nodes\<close>

lemma [\<phi>reason add]:
  \<open>separatable_module_zip True d a b c
                          (\<lambda>d _ x. (take (len_intvl.len d) x, drop (len_intvl.len d) x))
                          (\<lambda>_ _ (x,y). x @ y)
                          (\<lambda>b _ x. (take (len_intvl.len b) x, drop (len_intvl.len b) x))
                          (\<lambda>_ _ (x,y). x @ y)
                          (\<lambda>(x\<^sub>d,x\<^sub>a) (y\<^sub>b,y\<^sub>c). length x\<^sub>d = len_intvl.len d) (map f) (map f\<^sub>c)
                          (map f)
                          (\<lambda>x. map f (take (len_intvl.len b - len_intvl.len d) x) @ map f\<^sub>c (drop (len_intvl.len b - len_intvl.len d) x)) \<close>
  for d :: \<open>nat len_intvl\<close>
  unfolding separatable_module_zip_def
  by (clarsimp dest!: dabc_equation__len_intvl_D)

lemma [\<phi>reason add]:
  \<open>separatable_module_zip False d a b c
                          (\<lambda>d _ x. (take (len_intvl.len d) x, drop (len_intvl.len d) x))
                          (\<lambda>_ _ (x,y). x @ y)
                          (\<lambda>b _ x. (take (len_intvl.len b) x, drop (len_intvl.len b) x))
                          (\<lambda>_ _ (x,y). x @ y)
                          (\<lambda>(x\<^sub>d,x\<^sub>a) (y\<^sub>b,y\<^sub>c). length x\<^sub>d = len_intvl.len d)
                          (map f) (map f\<^sub>c)
                          (\<lambda>x. map f (take (len_intvl.len b) x) @ map f\<^sub>c (drop (len_intvl.len b) x)) (map f\<^sub>c) \<close>
  for d :: \<open>nat len_intvl\<close>
  unfolding separatable_module_zip_def
  by (clarsimp dest!: dabc_equation__len_intvl_D)


\<phi>type_def \<phi>Mul_Quant_Tree :: \<open>(nat \<Rightarrow> 'k) \<Rightarrow> nat len_intvl \<Rightarrow> ('k list \<Rightarrow> 'c, 'a) \<phi> \<Rightarrow> ('k list \<Rightarrow> 'c::sep_algebra, 'a list) \<phi> \<close> ("\<big_ast>\<^sub>\<bbbT>")
  where \<open>l \<Ztypecolon> \<phi>Mul_Quant_Tree f iv T \<equiv> l \<Ztypecolon> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv (\<lambda>i. f i \<^bold>\<rightarrow>\<^sub># T)\<close>
  deriving Sep_Functor_1
       and \<open>Abstract_Domain T P
        \<Longrightarrow> Abstract_Domain (\<phi>Mul_Quant_Tree f iv T) (\<lambda>x. length x = len_intvl.len iv \<and> list_all P x) \<close>
       and \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (\<phi>Mul_Quant_Tree f iv T) (list_all2 eq) \<close>
       and \<open>Identity_Elements\<^sub>I T T\<^sub>D T\<^sub>P
        \<Longrightarrow> Identity_Elements\<^sub>I (\<phi>Mul_Quant_Tree f iv T) (list_all T\<^sub>D) (\<lambda>x. length x = len_intvl.len iv \<and> list_all T\<^sub>P x) \<close>
       and \<open>Identity_Elements\<^sub>E T T\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E (\<phi>Mul_Quant_Tree f iv T) (\<lambda>x. length x = len_intvl.len iv \<and> list_all T\<^sub>D x) \<close>

term 1

declare [[\<phi>trace_reasoning = 3]]

let_\<phi>type  \<phi>Mul_Quant_Tree
  deriving Semimodule_SDistr_Homo\<^sub>S

term 1
       and Semimodule_NonAssoc
       
       and \<open>Semimodule_One\<^sub>I (\<lambda>iv. \<phi>Mul_Quant_Tree f iv T) (f j \<^bold>\<rightarrow>\<^sub># T) \<lbrakk>j:1\<rwpar> (\<lambda>_. True) (\<lambda>x. [x]) (\<lambda>_. True)\<close>
       and \<open>Semimodule_One\<^sub>E (\<lambda>iv. \<phi>Mul_Quant_Tree f iv T) (f j \<^bold>\<rightarrow>\<^sub># T) \<lbrakk>j:1\<rwpar> (\<lambda>l. length l = 1) hd (\<lambda>_. True)\<close>


\<phi>reasoner_group \<phi>Mul_Quant_Tree_wrap_module
              = (25, [25,26]) < derived_SE_inj_to_module
  \<open>Supplemantary wrappers injecting into module\<close>

lemma \<phi>Mul_Quant_Tree_wrap_module_src[\<phi>reason default %\<phi>Mul_Quant_Tree_wrap_module]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv
       \<and>\<^sub>\<r> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> y' ! (i - len_intvl.start iv) = fst y
            \<longrightarrow> (?\<^sub>Z[C\<^sub>W] (\<lambda>x. x) (\<lambda>f. f) (fst x, w) \<Ztypecolon> ks \<^bold>\<rightarrow>\<^sub>@ T \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<OTast> R \<w>\<i>\<t>\<h> P @tag \<T>\<P>'))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> length y' = len_intvl.len iv \<and> y' ! (i - len_intvl.start iv) = fst y
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (j, len, j', len') : (len_intvl.start iv, i - len_intvl.start iv,
                                 i + 1, len_intvl.start iv + len_intvl.len iv - i - 1)
\<Longrightarrow> ((snd x) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W'] W') = (
        (w, take len y', drop (len+1) y') \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] (f i \<^bold>\<rightarrow>\<^sub># W) \<^emph> \<half_blkcirc>[True] (\<phi>Mul_Quant_Tree f \<lbrakk>j:len\<rwpar> U) \<^emph> \<half_blkcirc>[True] (\<phi>Mul_Quant_Tree f \<lbrakk>j':len'\<rwpar> U)) @tag \<A>merge
\<Longrightarrow> x \<Ztypecolon> (f i # ks) \<^bold>\<rightarrow>\<^sub>@ T \<OTast> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y', snd (?\<^sub>U\<^sub>Z[C\<^sub>R] (\<lambda>x. x) (\<lambda>f. f) y)) \<Ztypecolon> \<phi>Mul_Quant_Tree f iv U \<OTast> f i \<^bold>\<rightarrow>\<^sub># R \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Action_Tag_def \<r>Guard_def Ant_Seq_imp \<phi>Prod'_def
  apply (simp add: cond_prod_transformation_rewr,
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises _ and Tr and _ and _ and []
    note Tr' = Tr[folded \<phi>Prod_expn' Cond_\<phi>Prod_expn_\<phi>Some,
                  unfolded \<phi>Some_transformation_strip prod.collapse]
    note t1 = \<phi>MapAt_L.scalar_partial_functor[
          unfolded Action_Tag_def,
          where t'=\<open>[]\<close> and s=\<open>[f i]\<close>, simplified,
          OF _ Tr'[THEN mp], unfolded times_list_def append_Cons append_Nil,
          simplified cond_prod_transformation_rewr,
          unfolded \<phi>Prod_expn' \<phi>Prod_expn'' Cond_\<phi>Prod_expn_\<phi>Some
                   times_list_def append_Cons append_Nil append_Nil2] ;;
    t1
  \<medium_right_bracket> certified by auto_sledgehammer .


lemma \<phi>Mul_Quant_Tree_wrap_module_tgt[\<phi>reason default %\<phi>Mul_Quant_Tree_wrap_module+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv
       \<and>\<^sub>\<r> (?\<^sub>Z[C\<^sub>W] (\<lambda>x. x) (\<lambda>f. f) (apfst (\<lambda>x. x ! (i - len_intvl.start iv)) x) \<Ztypecolon> T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> ks \<^bold>\<rightarrow>\<^sub>@ U \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P @tag \<T>\<P>')
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (j, len, j', len') : (len_intvl.start iv, i - len_intvl.start iv,
                                 i + 1, len_intvl.start iv + len_intvl.len iv - i - 1)
\<Longrightarrow> ((snd (?\<^sub>U\<^sub>Z[C\<^sub>R] (\<lambda>x. x) (\<lambda>f. f) y), take len (fst x), drop (len+1) (fst x))
      \<Ztypecolon> \<half_blkcirc>[C\<^sub>R] (f i \<^bold>\<rightarrow>\<^sub># R) \<^emph> \<half_blkcirc>[True] (\<phi>Mul_Quant_Tree f \<lbrakk>j:len\<rwpar> T) \<^emph> \<half_blkcirc>[True] (\<phi>Mul_Quant_Tree f \<lbrakk>j':len'\<rwpar> T))
      = (r \<Ztypecolon> \<half_blkcirc>[C\<^sub>R'] R') @tag \<A>merge
\<Longrightarrow> x \<Ztypecolon> \<phi>Mul_Quant_Tree f iv T \<^emph>[C\<^sub>W] f i \<^bold>\<rightarrow>\<^sub># W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> (f i # ks) \<^bold>\<rightarrow>\<^sub>@ U \<^emph>[C\<^sub>R'] R' \<w>\<i>\<t>\<h> P @tag \<T>\<P>' \<close>
  unfolding Action_Tag_def \<r>Guard_def Ant_Seq_imp
  apply (simp add: cond_prod_transformation_rewr,
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises _ and Tr and _ and A[]
    note Tr' = Tr[folded \<phi>Prod_expn' Cond_\<phi>Prod_expn_\<phi>Some,
                  unfolded \<phi>Some_transformation_strip prod.collapse]
    note t1 = \<phi>MapAt_L.scalar_partial_functor[
          unfolded Action_Tag_def,
          where t=\<open>[]\<close> and s=\<open>[f i]\<close> and s'=\<open>[f i]\<close>, simplified,
          OF Tr', unfolded times_list_def append_Cons append_Nil append_Nil2,
          simplified cond_prod_transformation_rewr,
          unfolded \<phi>Prod_expn' \<phi>Prod_expn'' Cond_\<phi>Prod_expn_\<phi>Some
                   times_list_def append_Cons append_Nil append_Nil2] ;;
    t1 certified by auto_sledgehammer \<semicolon>
     A 
  \<medium_right_bracket> .


lemma [\<phi>reason default %\<phi>mapToA_derived_module_SDistri
           for \<open>\<m>\<a>\<p> _ : (?fa ?j # _ # _) \<^bold>\<rightarrow>\<^sub>@ _ \<^emph>[_] _ \<mapsto> (?fa ?j # _ # _) \<^bold>\<rightarrow>\<^sub>@ _ \<^emph>[_] _
                \<o>\<v>\<e>\<r> _ : \<big_ast>\<^sub>\<bbbT> ?fa ?a _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
                \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a' = a \<and>\<^sub>\<r> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d \<lbrakk>j : 1\<rwpar> d\<epsilon> c a
\<Longrightarrow> module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C C\<^sub>c C\<^sub>d c \<lbrakk>j : 1\<rwpar> d\<epsilon> d
      (\<lambda>s t x. (take (len_intvl.len s) x, drop (len_intvl.len s) x)) (\<lambda>s t (x,y). x @ y) hd
      (\<lambda>x. [x]) (\<lambda>l. length l = 1) (\<lambda>_. True) (\<lambda>s t x. length x = len_intvl.len s + len_intvl.len t)
      (\<lambda>s t (x, y). length x = len_intvl.len s \<and> length y = len_intvl.len t) D\<^sub>G f\<^sub>c f f\<^sub>d f' getter
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : fa j \<^bold>\<rightarrow>\<^sub># ks \<^bold>\<rightarrow>\<^sub>@ U \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G \<mapsto> fa j \<^bold>\<rightarrow>\<^sub># ks' \<^bold>\<rightarrow>\<^sub>@ U' \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : fa j \<^bold>\<rightarrow>\<^sub># T \<^emph>[C\<^sub>W] W \<mapsto> fa j \<^bold>\<rightarrow>\<^sub># T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x, w). case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)) ` D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>G (fst x))
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G \<^emph> \<half_blkcirc>[C\<^sub>d] \<big_ast>\<^sub>\<bbbT> fa d T \<^emph> \<half_blkcirc>[C\<^sub>c] \<big_ast>\<^sub>\<bbbT> fa c T @tag \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G' \<^emph> \<half_blkcirc>[C\<^sub>d] \<big_ast>\<^sub>\<bbbT> fa d T' \<^emph> \<half_blkcirc>[C\<^sub>c] \<big_ast>\<^sub>\<bbbT> fa c T' @tag \<A>merge
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c : (fa j # ks) \<^bold>\<rightarrow>\<^sub>@ U \<^emph>[C\<^sub>R] R \<mapsto> (fa j # ks') \<^bold>\<rightarrow>\<^sub>@ U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : \<big_ast>\<^sub>\<bbbT> fa a T \<^emph>[C\<^sub>W] W \<mapsto> \<big_ast>\<^sub>\<bbbT> fa a' T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>(x, w). case getter x of (x\<^sub>d, x\<^sub>b, x\<^sub>c) \<Rightarrow> case h (x\<^sub>b, w) of (y, r) \<Rightarrow> (y, r, x\<^sub>d, x\<^sub>c))
         \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>(y, r, x\<^sub>d, x\<^sub>c). case s (y, r) of (x\<^sub>b, x) \<Rightarrow> (?\<^sub>j\<^sub>R C\<^sub>c (\<lambda>(x,y). x @ y) (?\<^sub>j\<^sub>L C\<^sub>d (\<lambda>(x,y). x @ y) (x\<^sub>d, [x\<^sub>b]), x\<^sub>c), x))
    \<i>\<n> D\<close>
  unfolding \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks]
            \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks'] times_list_def
            append_Cons[where x=\<open>(fa j)\<close>] List.append.append_Nil

  using \<phi>Mul_Quant_Tree.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>\<epsilon>\<^sub>c
        [where U=\<open>ks \<^bold>\<rightarrow>\<^sub>@ U\<close> and fa=fa and j=j and Ua=\<open>ks' \<^bold>\<rightarrow>\<^sub>@ U'\<close>,
         unfolded \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks]
                  \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks'] times_list_def
                  append_Cons[where x=\<open>(fa j)\<close>] List.append.append_Nil] .

(*
thm \<phi>Mul_Quant_Tree.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>\<epsilon>
        [where U=\<open>ks \<^bold>\<rightarrow>\<^sub>@ U\<close> and fa=fa and j=j and Ua=\<open>ks' \<^bold>\<rightarrow>\<^sub>@ U'\<close>,
         unfolded \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks]
                  \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks']
                  times_list_def[where a=ks] times_list_def[where a=ks']
                  append_Cons[where x=\<open>(fa j)\<close>] List.append.append_Nil]

lemma [\<phi>reason default %\<phi>mapToA_derived_module_SDistri
           for \<open>\<m>\<a>\<p> _ : (?fa ?j # _ # _) \<^bold>\<rightarrow>\<^sub>@ _ \<^emph>[_] _ \<mapsto> (?fa ?j # _ # _) \<^bold>\<rightarrow>\<^sub>@ _ \<^emph>[_] _
                \<o>\<v>\<e>\<r> _ : \<big_ast>\<^sub>\<bbbT> ?fa ?a _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
                \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _ \<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a' = a \<and>\<^sub>\<r> equation\<^sub>2\<^sub>1 d \<lbrakk>j : 1\<rwpar> a
\<Longrightarrow> module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L \<lbrakk>j : Suc 0\<rwpar> d
     (\<lambda>s t x. (take (len_intvl.len s) x, drop (len_intvl.len s) x))
     (\<lambda>s t (x,y). x @ y) hd (\<lambda>x. [x])
     (\<lambda>l. length l = Suc 0) (\<lambda>_. True)
     (\<lambda>s t x. length x = len_intvl.len s + len_intvl.len t)
     (\<lambda>s t (x,y). length x = len_intvl.len s \<and> length y = len_intvl.len t) D\<^sub>G f f\<^sub>d f' getter
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : fa j \<^bold>\<rightarrow>\<^sub># ks \<^bold>\<rightarrow>\<^sub>@ U \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G \<mapsto> fa j \<^bold>\<rightarrow>\<^sub># ks' \<^bold>\<rightarrow>\<^sub>@ U' \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : fa j \<^bold>\<rightarrow>\<^sub># T \<^emph>[C\<^sub>W] W \<mapsto> fa j \<^bold>\<rightarrow>\<^sub># T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x, w). case getter x of (x\<^sub>d, x\<^sub>b) \<Rightarrow> (x\<^sub>b, w)) ` D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>G (fst x))
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R  = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G  \<^emph> \<half_blkcirc>[True] \<big_ast>\<^sub>\<bbbT> fa d T  @tag \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G' \<^emph> \<half_blkcirc>[True] \<big_ast>\<^sub>\<bbbT> fa d T' @tag \<A>merge
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d : (fa j # ks) \<^bold>\<rightarrow>\<^sub>@ U \<^emph>[C\<^sub>R] R \<mapsto> (fa j # ks') \<^bold>\<rightarrow>\<^sub>@ U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : \<big_ast>\<^sub>\<bbbT> fa a T \<^emph>[C\<^sub>W] W \<mapsto> \<big_ast>\<^sub>\<bbbT> fa a' T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>(x, w). case getter x of (x\<^sub>d, x\<^sub>b) \<Rightarrow> case h (x\<^sub>b, w) of (y, r) \<Rightarrow> (y, r, x\<^sub>d))
         \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>(y, r, x\<^sub>d). case s (y, r) of (x\<^sub>b, x) \<Rightarrow> (x\<^sub>d @ [x\<^sub>b], x))
    \<i>\<n> D \<close>

  unfolding \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks]
            \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks'] times_list_def
            append_Cons[where x=\<open>(fa j)\<close>] List.append.append_Nil

  using \<phi>Mul_Quant_Tree.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>\<epsilon>
        [where U=\<open>ks \<^bold>\<rightarrow>\<^sub>@ U\<close> and fa=fa and j=j and Ua=\<open>ks' \<^bold>\<rightarrow>\<^sub>@ U'\<close>,
         unfolded \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks]
                  \<phi>MapAt_L.scalar_assoc[where s=\<open>[fa j]\<close> and t=ks'] times_list_def
                  append_Cons[where x=\<open>(fa j)\<close>] List.append.append_Nil] .
*)

end
