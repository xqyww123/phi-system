section \<open>An Implementation of \<phi>-Bunched Implications\<close>

text \<open>It also contains a simplified BI specialized for only necessary constructs required
  by \<^emph>\<open>Multi-Term Form\<close>.

\<^descr> \<^emph>\<open>Multi-Term Form\<close> is the canonical form in the reasoning of \<phi>-System, which demonstrates
  abstractions directly and clearly in a localized way. It is characterized by form,
\[ \<open>\<exists>a. (x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<^emph> \<cdots> x\<^sub>n \<Ztypecolon> T\<^sub>n) \<and> P\<close> \]
where \<open>P\<close> is a pure proposition only containing free variables occurring in \<open>x\<^sub>1,\<cdots>,x\<^sub>n,a\<close>.
It relates the concrete resource to a set of abstract objects \<open>{(x\<^sub>1,\<cdots>,x\<^sub>n) |a. P}\<close> if
  \<^emph>\<open>variables \<open>a\<close> are not free in \<open>T\<^sub>1,\<cdots>,T\<^sub>n\<close>\<close>.
All specifications in \<phi>-System are in Multi-Term Form. It is so pervasive that we use a set-like
notation to denote them,
\[ \<open>(x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<^emph> \<cdots> x\<^sub>n \<Ztypecolon> T\<^sub>n \<s>\<u>\<b>\<j> a. P)\<close> \]
Readers may read it as a set,
\[ \<open>{ x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<^emph> \<cdots> x\<^sub>n \<Ztypecolon> T\<^sub>n |a. P }\<close> \]

\<^descr> \<^emph>\<open>Simple Multi-Term Form\<close> is a MTF where there is no existential quantification and the attached
  \<open>P\<close> is trivial \<open>True\<close>, viz., it is characterized by
  \[ \<open>x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> \<cdots> \<^emph> x\<^sub>n \<Ztypecolon> T\<^sub>n\<close> \]
\<close>

text \<open>
Specifically, in this minimal specialized BI:

  \<^item> It does not have a general additive conjunction (\<open>\<and>\<close>) that connects any BI assertions,
    but only the one (\<open>A \<s>\<u>\<b>\<j> P\<close>) connects a BI assertion \<open>A\<close> and a pure assertion \<open>P\<close>,
    because it is exactly what at most the MTF requires.

  \<^item> Implication does not occur in assertions (of \<phi>-SL), but it represents transformations of
    abstraction so has a significant role in reasoning (rules).
    We emphasize this transformation by assigning the implication with notation
    \<open>A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<triangleq> A \<longrightarrow> B \<and> P\<close>, where \<open>P\<close> is a pure assertion.
    The \<open>P\<close> helps to capture the information (in abstract domain) lost in the
    weakening of this implication.
    Currying implications like \<open>A \<longrightarrow> B \<longrightarrow> C\<close> are never used in \<phi>-BI.

  \<^item> Optionally we have universal quantification. It can be used to quantify free variables
    if for any reason free variables are inadmissible. The universal quantifier is typically
    not necessary in \<phi>-BI and \<phi>-SL, where we use free variables directly. However, in some
    situation, like when we consider transitions of resource states and we want a transition
    relation for each procedure, we need a single universally quantified assertion,
    instead of a family of assertions indexed by free variables.

  \<^item> The use of a implication represents a transformation of abstraction.
    Therefore, implications are never curried or nested, always in form \<open>X \<longrightarrow> Y \<and> P\<close>
    where \<open>X, Y\<close> are MTF and \<open>P\<close> is a pure proposition.
    We denote them by notation \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>.

  \<^item> It only has multiplicative conjunctions, specialized additive conjunction described above,
    existential quantification, and optionally universal quantification,
    which are all the MTF requires,
    plus implications that only occur in reasoning rules.
    Any other things, should be some specific \<phi>-Types expressing their meaning
    specifically and particularly.
\<close>

theory Phi_BI
  imports "Phi_Logic_Programming_Reasoner.Phi_Logic_Programming_Reasoner" Phi_Preliminary
  abbrevs "<:>" = "\<Ztypecolon>"
      and "<trans>" = "\<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>"
      and "<transforms>" = "\<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>"
      and "<with>"  = "\<w>\<i>\<t>\<h>"
      and "<subj>" = "\<s>\<u>\<b>\<j>"
      and "<when>" = "\<w>\<h>\<e>\<n>"
      and "<remains>" = "\<r>\<e>\<m>\<a>\<i>\<n>\<s>"
begin

type_synonym 'a BI = \<open>'a set\<close>

subsection \<open>Satisfaction\<close>

definition Satisfaction :: \<open>'a \<Rightarrow> 'a BI \<Rightarrow> bool\<close> (infix "\<Turnstile>" 50) where \<open>(\<Turnstile>) = (\<in>)\<close>

lemma BI_eq_iff:
  \<open>S = S' \<longleftrightarrow> (\<forall>u. u \<Turnstile> S \<longleftrightarrow> u \<Turnstile> S')\<close>
  unfolding Satisfaction_def set_eq_iff ..

lemma sep_conj_expn[simp, \<phi>expns]:
  \<open>uv \<Turnstile> (S * T) \<longleftrightarrow> (\<exists>u v. uv = u * v \<and> u \<Turnstile> S \<and> v \<Turnstile> T \<and> u ## v)\<close>
  unfolding Satisfaction_def
  using set_mult_expn .

lemma Subjection_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (S \<s>\<u>\<b>\<j> P) \<longleftrightarrow> p \<Turnstile> S \<and> P\<close>
  unfolding Satisfaction_def using Subjection_expn_set .

lemma ExSet_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (ExSet S) \<longleftrightarrow> (\<exists>x. p \<Turnstile> S x)\<close>
  unfolding Satisfaction_def using ExSet_expn_set .

lemma Bottom_expn[iff, \<phi>expns]:
  \<open>\<not> (p \<Turnstile> {})\<close>
  unfolding Satisfaction_def by simp

lemma Zero_expn[iff, \<phi>expns]:
  \<open>\<not> (p \<Turnstile> 0)\<close>
  unfolding Satisfaction_def by simp

lemma One_expn[iff, \<phi>expns]:
  \<open>v \<Turnstile> 1 \<longleftrightarrow> v = 1\<close>
  unfolding Satisfaction_def by simp

lemma Top_expn[iff, \<phi>expns]:
  \<open>v \<Turnstile> top\<close>
  unfolding Satisfaction_def by simp


subsection \<open>BI order\<close>

lemma BI_sub_iff:
  \<open> S \<le> S' \<longleftrightarrow> (\<forall>u. u \<Turnstile> S \<longrightarrow> u \<Turnstile> S') \<close>
  unfolding Satisfaction_def subset_iff ..

declare [[\<phi>reason_default_pattern
    \<open> ?S \<le> ?S' \<close> \<Rightarrow> \<open> ?S \<le> ?S' \<close> \<open> ?var_S \<le> ?S' \<close> \<open> ?S \<le> ?var_S' \<close> (100) ]]

declare order.refl[\<phi>reason for \<open>?X \<le> ?X\<close> (10000)
                               \<open>?var \<le> _\<close> (1)
                               \<open>_ \<le> ?var\<close> (1) ]


subsection \<open>\<phi>-Type\<close>

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete BI "

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a BI" (infix "\<Ztypecolon>" 20) where " x \<Ztypecolon> T \<equiv> T x"

text \<open>Convention of name:

In \<open>x \<Ztypecolon> T\<close>, we refer to \<open>x\<close> as the \<^emph>\<open>object\<close> or the \<^emph>\<open>\<phi>-type term\<close> and \<open>T\<close> as the \<^emph>\<open>\<phi>-type\<close>.
For convenience, when the context is unambiguous, we also call the entire \<open>x \<Ztypecolon> T\<close> as '\<phi>-type',
but as \<^emph>\<open>\<phi>-type assertion\<close> to be precise.
\<close>

lemma \<phi>Type_eqI:
  \<open>(\<forall>x p. p \<Turnstile> (x \<Ztypecolon> a) \<longleftrightarrow> p \<Turnstile> (x \<Ztypecolon> b)) \<Longrightarrow> a = b\<close>
  unfolding \<phi>Type_def Satisfaction_def by blast

ML_file \<open>library/tools/simp_congruence.ML\<close>

subsection \<open>Inhabitance\<close>

definition Inhabited :: " 'a BI \<Rightarrow> bool " where  "Inhabited S = (\<exists>p. p \<Turnstile> S)"

abbreviation Inhabitance_Implication :: \<open>'a BI \<Rightarrow> bool \<Rightarrow> bool\<close> (infix "\<i>\<m>\<p>\<l>\<i>\<e>\<s>" 10)
  where \<open>S \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<equiv> Inhabited S \<longrightarrow> P @action \<A>EIF\<close>
  \<comment> \<open>P is weaker than S. We want to get a simpler P and as strong as possible. \<close>

abbreviation Sufficient_Inhabitance :: \<open>bool \<Rightarrow> 'a BI \<Rightarrow> bool\<close> (infix "\<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>" 10)
  where \<open>P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> S \<equiv> P \<longrightarrow> Inhabited S @action \<A>ESC\<close>
  \<comment> \<open>P is stronger than S. We want to get a simpler P and as weak as possible. \<close>

declare [[
  \<phi>reason_default_pattern \<open>Inhabited ?X \<longrightarrow> _\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>bad form\<close>)\<close> (100)
                      and \<open>_ \<longrightarrow> Inhabited ?X\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>bad form\<close>)\<close> (100)
]]

ML_file \<open>library/tools/inhabited_rule.ML\<close>

lemma Inhabited_I:
  \<open>x \<Turnstile> S \<Longrightarrow> Inhabited S\<close>
  unfolding Inhabited_def ..

lemma Inhabited_fallback_True:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> True \<close>
  unfolding Action_Tag_def by blast

lemma Suf_Inhabited_fallback_True:
  \<open> False \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> X \<close>
  unfolding Action_Tag_def by blast

\<phi>reasoner_ML Inhabited_fallback default 2 (\<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.mode_generate_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Inhabited_fallback_True} RS sequent), Seq.empty)
)\<close>

\<phi>reasoner_ML Suf_Inhabited_fallback default 2 (\<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.mode_generate_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Suf_Inhabited_fallback_True} RS sequent), Seq.empty)
)\<close>

lemma [\<phi>reason 1000]:
  \<open> P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P
\<Longrightarrow> Inhabited A\<close>
  unfolding Action_Tag_def Premise_def
  by blast

subsubsection \<open>Inhabitance of \<phi>-Type\<close>

lemma typing_inhabited: "p \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (x \<Ztypecolon> T)"
  unfolding Inhabited_def \<phi>Type_def by blast

definition Abstract_Domain :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Abstract_Domain T d \<longleftrightarrow> (\<forall>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> d x)\<close>
  \<comment> \<open>Upper Bound\<close>

definition Abstract_Domain\<^sub>L :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Abstract_Domain\<^sub>L T d \<longleftrightarrow> (\<forall>x. d x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T)\<close>
  \<comment> \<open>Lower Bound\<close>

declare [[\<phi>reason_default_pattern \<open>Abstract_Domain ?T _\<close> \<Rightarrow> \<open>Abstract_Domain ?T _\<close> (100)
                              and \<open>Abstract_Domain\<^sub>L ?T _\<close> \<Rightarrow> \<open>Abstract_Domain\<^sub>L ?T _\<close> (100) ]]

lemma [\<phi>reason default 10]:
  \<open> Abstract_Domain T D
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> D x\<close>
  unfolding Abstract_Domain_def Action_Tag_def
  by blast

lemma [\<phi>reason default 10]:
  \<open> Abstract_Domain\<^sub>L T D
\<Longrightarrow> D x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T\<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def
  by blast

lemma [\<phi>reason default 1]:
  \<open> Abstract_Domain T (\<lambda>_. True) \<close>
  unfolding Abstract_Domain_def Action_Tag_def
  by simp

lemma [\<phi>reason default 1]:
  \<open> Abstract_Domain\<^sub>L T (\<lambda>_. False) \<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def
  by simp

declare [[
  \<phi>reason_default_pattern_ML \<open>?x \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close> \<Rightarrow> \<open>
    fn ctxt => fn tm as (_ (*Trueprop*) $ (_ (*Action_Tag*) $ ( _ (*imp*) $ (
                            _ (*Inhabited*) $ (_ (*\<phi>Type*) $ x $ _)) $ _) $ _)) =>
      if is_Var x orelse not (Context_Position.is_visible_generic ctxt)
      then NONE
      else error (let open Pretty in string_of (chunks [
            para "Malformed Implication Rule: in \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close> the x must be a schematic variable. But given",
            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
          ]) end)\<close> (1000),

  \<phi>reason_default_pattern_ML \<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> _ \<Ztypecolon> _\<close> \<Rightarrow> \<open>
    fn ctxt => fn tm as (_ (*Trueprop*) $ (_ (*Action_Tag*) $ ( _ (*imp*) $ _ $ (
                            _ (*Inhabited*) $ (_ (*\<phi>Type*) $ x $ _))) $ _)) =>
      if is_Var x orelse not (Context_Position.is_visible_generic ctxt)
      then NONE
      else error (let open Pretty in string_of (chunks [
            para "Malformed Sufficiency Rule: in \<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T\<close> the x must be a schematic variable. But given",
            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
          ]) end)\<close> (1000)
]]


subsubsection \<open>The Variant of Inhabitance for Separation Carrier\<close>

definition Inhabited\<^sub>M\<^sub>C :: " 'a::sep_carrier BI \<Rightarrow> bool " where  "Inhabited\<^sub>M\<^sub>C S = (\<exists>p. p \<Turnstile> S \<and> mul_carrier p)"

abbreviation Inhabitance_Implication\<^sub>M\<^sub>C :: \<open>'a::sep_carrier BI \<Rightarrow> bool \<Rightarrow> bool\<close> (infix "\<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C" 10)
  where \<open>S \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C P \<equiv> Inhabited\<^sub>M\<^sub>C S \<longrightarrow> P @action \<A>EIF\<close>
  \<comment> \<open>P is weaker than S. We want to get a simpler P and as strong as possible. \<close>

abbreviation Sufficient_Inhabitance\<^sub>M\<^sub>C :: \<open>bool \<Rightarrow> 'a::sep_carrier BI \<Rightarrow> bool\<close> (infix "\<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C" 10)
  where \<open>P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C S \<equiv> P \<longrightarrow> Inhabited\<^sub>M\<^sub>C S @action \<A>ESC\<close>
  \<comment> \<open>P is stronger than S. We want to get a simpler P and as weak as possible. \<close>

lemma Inhabited\<^sub>M\<^sub>C_fallback_True:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C True \<close>
  unfolding Action_Tag_def by blast

lemma Suf\<^sub>M\<^sub>C_Inhabited_fallback_True:
  \<open> False \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C X \<close>
  unfolding Action_Tag_def by blast

\<phi>reasoner_ML Inhabited_fallback\<^sub>M\<^sub>C default 2 (\<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.mode_generate_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Inhabited\<^sub>M\<^sub>C_fallback_True} RS sequent), Seq.empty)
)\<close>

\<phi>reasoner_ML Suf_Inhabited_fallback\<^sub>M\<^sub>C default 2 (\<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.mode_generate_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Suf\<^sub>M\<^sub>C_Inhabited_fallback_True} RS sequent), Seq.empty)
)\<close>

lemma [\<phi>reason 1000]:
  \<open> P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C A
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P
\<Longrightarrow> Inhabited\<^sub>M\<^sub>C A\<close>
  unfolding Action_Tag_def Premise_def
  by blast


subsubsection \<open>The Separation Carrier Variant for \<phi>-Type\<close>

definition Abstract_Domain\<^sub>M\<^sub>C :: \<open>('c::sep_carrier,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Abstract_Domain\<^sub>M\<^sub>C T d \<longleftrightarrow> (\<forall>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C d x)\<close>
  \<comment> \<open>Upper Bound\<close>

definition Abstract_Domain\<^sub>M\<^sub>C\<^sub>L :: \<open>('c::sep_carrier,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Abstract_Domain\<^sub>M\<^sub>C\<^sub>L T d \<longleftrightarrow> (\<forall>x. d x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C x \<Ztypecolon> T)\<close>
  \<comment> \<open>Lower Bound\<close>

declare [[\<phi>reason_default_pattern \<open>Abstract_Domain\<^sub>M\<^sub>C ?T _\<close> \<Rightarrow> \<open>Abstract_Domain\<^sub>M\<^sub>C ?T _\<close> (100)
                              and \<open>Abstract_Domain\<^sub>M\<^sub>C\<^sub>L ?T _\<close> \<Rightarrow> \<open>Abstract_Domain\<^sub>M\<^sub>C\<^sub>L ?T _\<close> (100) ]]

lemma [\<phi>reason default 10]:
  \<open> Abstract_Domain\<^sub>M\<^sub>C T D
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C D x\<close>
  unfolding Abstract_Domain\<^sub>M\<^sub>C_def Action_Tag_def
  by blast

lemma [\<phi>reason default 10]:
  \<open> Abstract_Domain\<^sub>M\<^sub>C\<^sub>L T D
\<Longrightarrow> D x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C x \<Ztypecolon> T\<close>
  unfolding Abstract_Domain\<^sub>M\<^sub>C\<^sub>L_def Action_Tag_def
  by blast

lemma [\<phi>reason default 1]:
  \<open> Abstract_Domain\<^sub>M\<^sub>C T (\<lambda>_. True) \<close>
  unfolding Abstract_Domain\<^sub>M\<^sub>C_def Action_Tag_def
  by simp

lemma [\<phi>reason default 1]:
  \<open> Abstract_Domain\<^sub>M\<^sub>C\<^sub>L T (\<lambda>_. False) \<close>
  unfolding Abstract_Domain\<^sub>M\<^sub>C\<^sub>L_def Action_Tag_def
  by simp

declare [[
  \<phi>reason_default_pattern_ML \<open>?x \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C _\<close> \<Rightarrow> \<open>
    fn ctxt => fn tm as (_ (*Trueprop*) $ (_ (*Action_Tag*) $ ( _ (*imp*) $ (
                            _ (*Inhabited\<^sub>M\<^sub>C*) $ (_ (*\<phi>Type*) $ x $ _)) $ _) $ _)) =>
      if is_Var x orelse not (Context_Position.is_visible_generic ctxt)
      then NONE
      else error (let open Pretty in string_of (chunks [
            para "Malformed Implication Rule: in \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C _\<close> the x must be a schematic variable. But given",
            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
          ]) end)\<close> (1000),

  \<phi>reason_default_pattern_ML \<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C _ \<Ztypecolon> _\<close> \<Rightarrow> \<open>
    fn ctxt => fn tm as (_ (*Trueprop*) $ (_ (*Action_Tag*) $ ( _ (*imp*) $ _ $ (
                            _ (*Inhabited\<^sub>M\<^sub>C*) $ (_ (*\<phi>Type*) $ x $ _))) $ _)) =>
      if is_Var x orelse not (Context_Position.is_visible_generic ctxt)
      then NONE
      else error (let open Pretty in string_of (chunks [
            para "Malformed Sufficiency Rule: in \<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C x \<Ztypecolon> T\<close> the x must be a schematic variable. But given",
            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
          ]) end)\<close> (1000)
]]


(*
lemma Membership_E_Inhabitance:
  \<open> x \<Turnstile> S
\<Longrightarrow> Inhabited S \<longrightarrow> C
\<Longrightarrow> C\<close>
  unfolding Inhabited_def by blast
*)


subsection \<open>Transformation of Abstraction\<close>

text \<open>The only meaningful implication \<open>\<longrightarrow>\<close> under the interpretation of \<phi> data refinement\<close>

definition Transformation :: " 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool \<Rightarrow> bool " ("(2_)/ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (2_)/ \<w>\<i>\<t>\<h> (2_)" [13,13,13] 12)
  where "(A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) \<longleftrightarrow> (\<forall>v. v \<Turnstile> A \<longrightarrow> v \<Turnstile> B \<and> P)"

abbreviation SimpleTransformation :: " 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool " ("(2_)/ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (2_)" [13,13] 12)
  where \<open>SimpleTransformation T U \<equiv> Transformation T U True\<close>

text \<open>
Transformation \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. f x y\<close> and its dual \<open>y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. g x y\<close>
constitute a classical Galios connection \<open>(f,g)\<close>. However, our method does not apply the Galios
connection directly as our method is synthetic (we do not analysis the relation between
concrete sets and abstract sets once after defining a \<phi>-type,
but do deductions by means of transformation rules).
Comparing to analytic methods (the classical methods for data refinement), synthetic methods based
on a higher abstraction simplify representations and give more chances for automation (by means of an inference system),
and in addition, can be combined in program logics more natively.
\<close>

subsubsection \<open>Rules\<close>

lemma \<phi>Type_eqI_Tr:
  \<open> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U)
\<Longrightarrow> (\<And>x. x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T)
\<Longrightarrow> T = U\<close>
  unfolding \<phi>Type_def Transformation_def Satisfaction_def
  by auto

lemma transformation_refl[simp]:
  "A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A" unfolding Transformation_def by fast

lemma transformation_trans:
  "A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> (P \<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C \<w>\<i>\<t>\<h> P \<and> Q"
  unfolding Transformation_def Premise_def by auto

lemma mk_intro_transformation:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def
  by simp

lemma mk_elim_transformation:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def
  by simp blast

lemma transformation_weaken:
  \<open> P \<longrightarrow> P'
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P'\<close>
  unfolding Transformation_def by simp

lemma transformation_intro_inhab:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> Inhabited A \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def Inhabited_def Satisfaction_def
  by blast

lemma assertion_eq_intro:
  \<open> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Q
\<Longrightarrow> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> P
\<Longrightarrow> P = Q\<close>
  unfolding Transformation_def BI_eq_iff by blast


subsubsection \<open>Transformation between \<close>

text \<open>There are two kinds of transformation rule

\<^item> cast-rule: \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> U \<w>\<i>\<t>\<h> P(x)\<close> binding on pattern \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> U \<w>\<i>\<t>\<h> _\<close>,
  which specifies how to transform a given \<phi>-type \<open>x \<Ztypecolon> T\<close> into the target type \<open>U\<close> and what is the
  resulted abstract object with yielding any auxiliary pure facts \<open>P(x)\<close>.

\<^item> intro-rule: \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g(y) \<Ztypecolon> U' \<w>\<i>\<t>\<h> P \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<and> Q(y)\<close> binding on
  pattern \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> _\<close>, which specifies how to construct \<open>y \<Ztypecolon> U\<close> by construction
  from \<open>g(y) \<Ztypecolon> U'\<close>.
    
\<^item> elim-rule: \<open>g(x) \<Ztypecolon> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> Q(x)\<close> binding on
  pattern \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>, which specifies how to destruct \<open>x \<Ztypecolon> T\<close> in sense of opening
  its encapsulated abstraction to then deduce whatever we want.

(*TODO: revise the text below!!!*)
Among the rules generated from \<open>\<phi>type_def\<close>, only the cast-rules are registered and activated.
Case-rule is point to point (from a specific type to another specific) so it is safe.
The intro-rule and the elim-rule reduce the abstraction level.
They cause the reasoning reduces to a lower level of abstraction.
Users can always activate the rules at their discretion.

Intro-rule and elim-rule can always be applied manually. It doesn't burden the user even a little because
the rules are used only when opening and closing an abstraction, in the case that should only happens
when building an interface or an internal operation of a data structure, where users can
write the intro-rule and the elim-rule at the beginning and the end of the program without thinking a bit.
\<close>

text \<open>In reasoning, the \<open>P\<close> in any goal is always an OUT-argument.\<close>

ML \<open>val phi_allow_source_object_to_be_not_variable =
          Config.declare_bool ("phi_allow_source_object_to_be_not_variable", \<^here>) (K false)\<close>

ML_file \<open>library/syntax/transformation.ML\<close>

declare [[
  (*a general checker warns if the abstract object of the source is not a variable*)
  \<phi>reason_default_pattern_ML \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>fn ctxt =>
    fn tm as (Trueprop $ (Transformation $ (PhiTyp $ x $ _) $ _ $ _)) => (
      if not (is_Var (Term.head_of x)) andalso
         Context_Position.is_visible_generic ctxt andalso
         not (Config.get_generic ctxt phi_allow_source_object_to_be_not_variable)
      then warning (let open Pretty in string_of (chunks [
              para "The abstract object of the source of a transformation rule should be a variable.\n",
              Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
            ]) end)
      else () ;
      NONE
  )\<close> (1000),

  \<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> (10)
  and \<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> (501) (*TODO: Auto_Transform_Hint*)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> (500)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _\<close> (20)
]]

subsubsection \<open>Transformations with Remainders and Future Target\<close>

text \<open>Upon above, we present in addition two extension forms providing partial transformations
  where a part of the source object may transform to only a part of the target object, leaving some
  remainder of the source and some unsolved target part.

\<^enum> \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> U\<close>, the usual one-\<phi>type-to-one-\<phi>type transformation.
\<^enum> \<open>x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close> or alternatively
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cr] R(x)\<close>, the transformation with remainders
\<^enum> \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close>, with both remainders and unsolved target parts.

where \<open>Cw, Cr\<close> are boolean conditions deciding if the remainder and respectively the unsolved aims
are presented.
The forms constitute a lattice where the reasoning of the bottom reduce to the top.

Note \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close> is not admissible though it is syntactically valid.
As it is entailed by the more general \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close>, and more
important, the pattern of \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<dots>\<close> also covers that of \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _\<close> when \<open>T\<close>
is variable, meaning inefficiency in selecting rule during reasoning, we dismiss \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<dots>\<close>
for the sake of reasoning performance and reducing the total number of reasoning rules.

In this way, designers of \<phi>-types only require to provide two forms of rules,
\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close> and \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R\<close>
\<close>

definition REMAINS :: \<open> 'a::sep_magma BI \<Rightarrow> bool \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<close> ("_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _" [14,10,14] 13)
  where \<open>(X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<equiv> if C then R * X else X\<close>
  \<comment> \<open>The \<open>C\<close> should be a variable sending to the later reasoning which decides if the transformation
      results in some remainders. Or, exceptionally, \<open>C\<close> can be constant \<open>True\<close> for unital algebras
      and the later reasoning sets the remainder to \<open>1\<close> if it does not really results in remainders.

      It means, every reasoning procedure should prepare two versions, the one for variable \<open>C\<close>
      and another for the \<open>C\<close> of constant \<open>True\<close>.

      A reasoning procedure can at any time if on a unital algebra, set a variable \<open>C\<close> to \<open>True\<close>
      and turns the reasoning into the unital mode.\<close>

definition \<phi>Prod :: " ('concrete::sep_magma, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b). B b * A a)"

definition Cond_\<phi>Prod :: \<open> ('v,'x) \<phi> \<Rightarrow> bool \<Rightarrow> ('v,'y) \<phi> \<Rightarrow> ('v::sep_magma,'x \<times> 'y) \<phi> \<close> ("_ \<^emph>[_] _" [71,40,70] 70)
    \<comment> \<open>\<phi>Type embedding of conditional remainder\<close>
  where \<open>(T \<^emph>[C] U) \<equiv> if C then T \<^emph> U else (\<lambda>x. fst x \<Ztypecolon> T)\<close>

lemma REMAINS_simp[simp]:
  \<open>X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<equiv> R * X\<close>
  \<open>X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] R \<equiv> X\<close>
  unfolding REMAINS_def
  by simp_all

text \<open>In reasoning, the \<open>P,R,W\<close> in any goal are always OUT-arguments.\<close>

declare [[
  \<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> (11)

  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> (20)
  and \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?C] ?R \<w>\<i>\<t>\<h> ?P\<close> \<Rightarrow>
          \<open>WARNING TEXT(\<open>Transformations between single \<phi>-types with remainders should use\<close>
                        (x \<Ztypecolon> ?T \<^emph>[False] Top \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (?y, some_r) \<Ztypecolon> ?U \<^emph>[?C] some_R \<w>\<i>\<t>\<h> ?P)
                        \<open>instead of the given\<close>
                        (?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?C] ?R \<w>\<i>\<t>\<h> ?P))\<close>
          \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> (21)

  and \<open>_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> (30)
  and \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[?Cr] ?R \<w>\<i>\<t>\<h> ?P\<close> \<Rightarrow>
          \<open>ERROR TEXT(\<open>Not admissible form. Please use\<close>
                      (x \<Ztypecolon> ?T \<^emph>[False] Top \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[?Cr] ?R \<w>\<i>\<t>\<h> ?P)
                      \<open>instead of the given\<close>
                      (?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[?Cr] ?R \<w>\<i>\<t>\<h> ?P))\<close> (25)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[?C] ?R \<w>\<i>\<t>\<h> ?P\<close> \<Rightarrow>
          \<open>ERROR TEXT((U \<^emph>[C] R) \<open>should only be used in transformations between single \<phi>-types. You should use\<close>
                        (?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst ?y) \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?C] snd ?y \<Ztypecolon> ?R \<w>\<i>\<t>\<h> ?P)
                        \<open>instead of the given\<close>
                        (?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[?C] ?R \<w>\<i>\<t>\<h> ?P))\<close> (24)
  and \<open> Attempt_Fallback ( _ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _ ) \<close> \<Rightarrow>
      \<open> Attempt_Fallback ( _ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _ ) \<close>   (30)

  and \<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> (511) (*TODO: Auto_Transform_Hint*)
  and \<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> (511) (*TODO: Auto_Transform_Hint*)
  and \<open>?x \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?x \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> (510)
]]

lemma REMAINS_expn[\<phi>expns]:
  \<open> p \<Turnstile> (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<longleftrightarrow> (if C then p \<Turnstile> R * A else p \<Turnstile> A) \<close>
  unfolding REMAINS_def
  by simp

paragraph \<open>Fallback\<close>

text \<open>Clearly, on any commutative algebra any transformations having remainders and future targets
  have a trivial fallback, that does nothing but leaving all to the future target

  \<open> x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> U \<^emph>[True] T \<close>

  By default, such rule is not activated as it really does nothing, and clients have a way
  to know if the reasoning fails. However, if such fallback is expected, one can use reasoning goal
  \<open> Try Cs (x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R) \<close>
  in which boolean condition \<open>Cs\<close> returns whether the reasoning really ever made some changes.
 \<close>

lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph>[True] X) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Attempt_Fallback_def Cond_\<phi>Prod_def \<phi>Prod_def \<phi>Type_def Transformation_def
  by (cases x; simp add: mult.commute)

lemma [\<phi>reason default 2]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> Attempt_Fallback ((x,y) \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph>[True] X) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Attempt_Fallback_def Cond_\<phi>Prod_def \<phi>Prod_def \<phi>Type_def Transformation_def
  by (simp add: mult.commute)

(* TODO!
lemma [\<phi>reason default 2]:
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph>[True] X \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Attempt_Fallback_def
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')
*)

subsubsection \<open>Inhabitance Reasoning - Part II\<close>

(*TODO: move me!!*)

lemma [\<phi>reason 1100]:
  \<open> Generate_Implication_Reasoning (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) (Inhabited X) (Inhabited Y) \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Inhabited_def by blast

lemma [\<phi>reason 1000]:
  \<open> Generate_Implication_Reasoning (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) (Inhabited X) (Inhabited Y \<and> P) \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Inhabited_def by blast



subsection \<open>Bottom\<close>

text \<open>Despite of semantically \<open>0 = \<bottom>\<close> where syntactically \<open>\<bottom> \<equiv> {}\<close>, but there is not syntactically
  \<open>0 \<equiv> {}\<close>. We prefer to use \<open>0\<close> instead of the more usual \<open>\<bottom>\<close> for the sake of forming
  a semiring together with \<open>1 \<equiv> emp\<close>, \<open>*\<close>, \<open>+ \<equiv> \<or>\<^sub>B\<^sub>I\<close>, to leverage the existing automation of semiring.\<close>

abbreviation Bottom ("\<bottom>\<^sub>B\<^sub>I") where \<open>Bottom \<equiv> (0::'a::sep_magma BI)\<close>
abbreviation Bottom_abs ("\<bottom>\<^sub>\<lambda>") where \<open>Bottom_abs \<equiv> (0 :: 'b \<Rightarrow> 'a::sep_magma BI)\<close>


lemma zero_implies_any[\<phi>reason 2000, simp]:
  \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close>
  unfolding Transformation_def zero_set_def Satisfaction_def by simp

lemma BI_bot_ord [\<phi>reason for \<open>0 \<le> _\<close> (1000)]:
  \<open>0 \<le> Any\<close>
  for Any :: \<open>'a BI\<close>
  by (simp add: zero_set_def)

declare bot_least [\<phi>reason for \<open>bot \<le> _\<close> (1000)]


subsection \<open>Top\<close>

notation top ("\<top>")

declare top_greatest [\<phi>reason for \<open>_ \<le> \<top>\<close> (1000)]


subsection \<open>Additive Disjunction\<close>

text \<open>Is the \<^term>\<open>(+) :: 'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> directly\<close>

lemma Disjunction_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (A + B) \<longleftrightarrow> p \<Turnstile> A \<or> p \<Turnstile> B\<close>
  unfolding Satisfaction_def by simp

lemma [\<phi>inhabitance_rule 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> B
\<Longrightarrow> X + Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<or> B\<close>
  unfolding Action_Tag_def Inhabited_def
  by simp blast

lemma [\<phi>reason 1000]:
  \<open> A \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> X
\<Longrightarrow> B \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> Y
\<Longrightarrow> A \<or> B \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> X + Y\<close>
  unfolding Action_Tag_def Inhabited_def
  by simp blast

text \<open>The above two rules are reversible.\<close>

lemma set_plus_inhabited[elim!]:
  \<open>Inhabited (S + T) \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by (simp, blast)

lemma implies_union:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X + Y \<w>\<i>\<t>\<h> P\<close>
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X + Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by simp_all

declare add_mono[\<phi>reason 1000]
  

subsection \<open>Additive Conjunction\<close>


definition Additive_Conj :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> (infix "\<and>\<^sub>B\<^sub>I" 35)
  where \<open>Additive_Conj = (\<inter>)\<close>

lemma Additive_Conj_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (A \<and>\<^sub>B\<^sub>I B) \<longleftrightarrow> p \<Turnstile> A \<and> p \<Turnstile> B\<close>
  unfolding Satisfaction_def Additive_Conj_def by simp

lemma additive_conj_inhabited_E[elim!]:
  \<open>Inhabited (A \<and>\<^sub>B\<^sub>I B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by simp blast

lemma [\<phi>reason 1000]:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q
\<Longrightarrow> A \<and>\<^sub>B\<^sub>I B \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> Q\<close>
  unfolding Action_Tag_def
  by blast

lemma
  \<open> P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A
\<Longrightarrow> Q \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> B
\<Longrightarrow> P \<and> Q \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A \<and>\<^sub>B\<^sub>I B\<close>
  unfolding Action_Tag_def Inhabited_def
  oops

text \<open>There is no sufficiency reasoning for additive conjunction, because the sufficient condition
  of \<open>A \<and>\<^sub>B\<^sub>I B\<close> cannot be reasoned separately (by considering \<open>A\<close> and \<open>B\<close> separately).\<close>



subsubsection \<open>Subjection: Conjunction to a Pure Fact\<close>

text \<open>This is the only widely used additive conjunction under the interpretation of the \<phi> data refinement\<close>

paragraph \<open>Rules\<close>

lemma Subjection_inhabited_E[elim!]:
  \<open>Inhabited (S \<s>\<u>\<b>\<j> P) \<Longrightarrow> (Inhabited S \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> C
\<Longrightarrow> S \<s>\<u>\<b>\<j> P \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> C \<close>
  unfolding Inhabited_def Action_Tag_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> C \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> S
\<Longrightarrow> P \<and> C \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> S \<s>\<u>\<b>\<j> P \<close>
  unfolding Inhabited_def Action_Tag_def
  by simp 

lemma Subjection_imp_I:
  \<open> P
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> Q
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q\<close>
  unfolding Transformation_def by simp

lemma Subjection_ord[\<phi>reason 1000]:
  \<open> S \<le> S'
\<Longrightarrow> (S \<s>\<u>\<b>\<j> P) \<le> (S' \<s>\<u>\<b>\<j> P) \<close>
  unfolding BI_sub_iff
  by clarsimp


paragraph \<open>Simplification\<close>

lemma Subjection_cong[cong]:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<s>\<u>\<b>\<j> P) \<equiv> (S' \<s>\<u>\<b>\<j> P')\<close>
  unfolding atomize_eq BI_eq_iff by (simp, blast)

lemma Subjection_imp_simp[simp]:
  \<open> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q) \<longleftrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<and> Q) \<close>
  unfolding Transformation_def by simp

lemma Subjection_True [simp, \<phi>programming_base_simps]:
  \<open>(T \<s>\<u>\<b>\<j> True) = T\<close>
  unfolding BI_eq_iff by simp

lemma Subjection_Flase[simp, \<phi>programming_base_simps]:
  \<open>(T \<s>\<u>\<b>\<j> False) = 0\<close>
  unfolding BI_eq_iff by simp

lemma Subjection_Subjection[simp, \<phi>programming_base_simps]:
  \<open>(S \<s>\<u>\<b>\<j> P \<s>\<u>\<b>\<j> Q) = (S \<s>\<u>\<b>\<j> P \<and> Q)\<close>
  unfolding BI_eq_iff
  by simp

lemma Subjection_Zero[simp, \<phi>programming_base_simps]:
  \<open>(0 \<s>\<u>\<b>\<j> P) = 0\<close>
  unfolding BI_eq_iff
  by simp

lemma Subjection_transformation:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P
\<Longrightarrow> S \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (simp; blast)

lemma Subjection_transformation_expn:
  \<open> (A \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) \<longleftrightarrow> (Q \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P))\<close>
  unfolding Transformation_def by (simp; blast)

(* lemma (in \<phi>empty) [simp]: "(VAL (S \<s>\<u>\<b>\<j> P)) = (VAL S \<s>\<u>\<b>\<j> P)" by (simp add: \<phi>expns set_eq_iff) blast
lemma (in \<phi>empty) [simp]: "(OBJ (S \<s>\<u>\<b>\<j> P)) = (OBJ S \<s>\<u>\<b>\<j> P)" by (simp add: \<phi>expns set_eq_iff) *)

subparagraph \<open>With Additive Conjunction\<close>

lemma Subjection_addconj[simp]:
  \<open>(A \<s>\<u>\<b>\<j> P) \<and>\<^sub>B\<^sub>I B \<equiv> (A \<and>\<^sub>B\<^sub>I B) \<s>\<u>\<b>\<j> P\<close>
  \<open>B \<and>\<^sub>B\<^sub>I (A \<s>\<u>\<b>\<j> P) \<equiv> (B \<and>\<^sub>B\<^sub>I A) \<s>\<u>\<b>\<j> P\<close>
  unfolding atomize_eq BI_eq_iff
  by (clarsimp; blast)+

subparagraph \<open>With Additive Disjunction\<close>

lemma Subjection_plus_distrib:
  \<open>(A + B \<s>\<u>\<b>\<j> P) = (A \<s>\<u>\<b>\<j> P) + (B \<s>\<u>\<b>\<j> P)\<close>
  unfolding BI_eq_iff
  by simp blast

subparagraph \<open>With Multiplicative Conjunction\<close>

lemma Subjection_times[simp]:
  \<open>(S \<s>\<u>\<b>\<j> P) * T = (S * T \<s>\<u>\<b>\<j> P)\<close>
  \<open>T * (S \<s>\<u>\<b>\<j> P) = (T * S \<s>\<u>\<b>\<j> P)\<close>
  unfolding BI_eq_iff
  by (simp, blast)+

(*subsection \<open>Disjunction\<close>*)

(* Just similarly not needed

subsubsection \<open>Embedding of disjunction in \<phi>-Type\<close>

definition \<phi>Plus :: " ('concrete, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^bold>+" 55)
  where "A \<^bold>+ B = (\<lambda>(a,b). B b + A a)"

lemma \<phi>Plus_expn[\<phi>expns]:
  "c \<in> ((a,b) \<Ztypecolon> A \<^bold>+ B) \<longleftrightarrow> c \<in> (b \<Ztypecolon> B) \<or> c \<in> (a \<Ztypecolon> A)"
  unfolding \<phi>Plus_def \<phi>Type_def by simp

lemma \<phi>Plus_expn':
  \<open>((a,b) \<Ztypecolon> A \<^bold>+ B) = (b \<Ztypecolon> B) + (a \<Ztypecolon> A)\<close>
  unfolding set_eq_iff by (simp add: \<phi>Plus_expn)
*)





subsection \<open>Multiplicative Conjunction\<close>

text \<open>Is the \<^term>\<open>(*) :: ('a::sep_magma) BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> directly\<close>

lemma set_mult_inhabited[elim!]:
  \<open>Inhabited (S * T) \<Longrightarrow> (Inhabited S \<Longrightarrow> Inhabited T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by (simp, blast)

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> B
\<Longrightarrow> X * Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<and> B\<close>
  unfolding Action_Tag_def
  using set_mult_inhabited by blast

lemma
  \<open> A \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> X
\<Longrightarrow> B \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> Y
\<Longrightarrow> A \<and> B \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> X * Y\<close>
  unfolding Action_Tag_def Inhabited_def
  apply clarsimp
  oops

text \<open>There is no sufficiency reasoning for multiplicative conjunction, because if we reason A and B
  separately, we loose the constraint about A and B are separatable, A ## B..\<close>


lemma eq_left_frame:
  \<open> A = B \<Longrightarrow> R * A = R * B \<close>
  by simp

lemma eq_right_frame:
  \<open> A = B \<Longrightarrow> A * R = B * R \<close>
  by simp

lemma implies_left_frame:
  "U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> R * U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * U \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma implies_right_frame:
  "U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> U' * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U * R \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma implies_bi_frame:
  " R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> L' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> L \<w>\<i>\<t>\<h> Q
\<Longrightarrow> L' * R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> L * R \<w>\<i>\<t>\<h> P \<and> Q "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast


subsection \<open>Multiplicative Finite Quantification\<close>

definition Mul_Quant :: \<open>('a \<Rightarrow> 'b::sep_algebra BI) \<Rightarrow> 'a set \<Rightarrow> 'b BI\<close> ("\<big_ast>")
  where \<open>Mul_Quant A S \<equiv> (prod A S \<s>\<u>\<b>\<j> finite S)\<close>

syntax
  "_Mul_Quant" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(2\<big_ast>(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<big_ast>i\<in>A. b" == "CONST Mul_Quant (\<lambda>i. b) A"

syntax
  "_qMul_Quant" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<big_ast>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<big_ast>x|P. t" => "CONST Mul_Quant (\<lambda>x. t) {x. P}"

subsubsection \<open>Rules\<close>

lemma [\<phi>reason 1000]:
  \<open> (\<And>i\<in>S. A i \<i>\<m>\<p>\<l>\<i>\<e>\<s> P i)
\<Longrightarrow> (\<big_ast>i\<in>S. A i) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<forall>i\<in>S. P i)\<close>
  unfolding Mul_Quant_def Action_Tag_def Inhabited_def meta_Ball_def Premise_def
  by (clarsimp; metis Satisfaction_def ex_in_conv prod_zero zero_set_iff)

lemma Mul_Quant_ord:
  \<open> (\<And>i\<in>S. A i \<le> A' i)
\<Longrightarrow> (\<big_ast>i\<in>S. A i) \<le> (\<big_ast>i\<in>S. A' i) \<close>
  unfolding atomize_Ball
proof -
  { assume \<open>finite S\<close>
    have \<open>(\<forall>i\<in>S. A i \<le> A' i) \<longrightarrow> (\<Prod>i\<in>S. A i) \<le> (\<Prod>i\<in>S. A' i)\<close>
      by (induct rule: finite_induct[OF \<open>finite S\<close>];
          clarsimp simp add: BI_sub_iff;
          blast)
  }
  moreover assume \<open>\<forall>i\<in>S. A i \<le> A' i\<close>
  ultimately show ?thesis
  unfolding Mul_Quant_def
  by (metis (full_types) BI_bot_ord Subjection_Flase Subjection_True)
qed

lemma finite_prod_subjection:
  \<open>finite I \<Longrightarrow> (\<Prod>i\<in>I. A i \<s>\<u>\<b>\<j> P i) = ((\<Prod>i\<in>I. A i) \<s>\<u>\<b>\<j> (\<forall>i\<in>I. P i))\<close>
  unfolding BI_eq_iff
proof (clarify; rule; clarsimp)
  fix u
  assume \<open>finite I\<close>
  have \<open>u \<Turnstile> (\<Prod>i\<in>I. A i \<s>\<u>\<b>\<j> P i) \<longrightarrow> u \<Turnstile> prod A I \<and> (\<forall>x\<in>I. P x)\<close>
    by (induct arbitrary: u rule: finite_induct[OF \<open>finite I\<close>]; simp; blast)
  moreover assume \<open>u \<Turnstile> (\<Prod>i\<in>I. A i \<s>\<u>\<b>\<j> P i)\<close>
  ultimately show \<open>u \<Turnstile> prod A I \<and> (\<forall>x\<in>I. P x)\<close>
    by blast
qed 

lemma sep_quant_subjection:
  \<open>(\<big_ast>i\<in>I. A i \<s>\<u>\<b>\<j> P i) = ((\<big_ast>i\<in>I. A i) \<s>\<u>\<b>\<j> (\<forall>i\<in>I. P i))\<close>
  unfolding BI_eq_iff
  by (clarify; rule; clarsimp simp add: Mul_Quant_def finite_prod_subjection)

lemma sep_quant_contract:
  \<open>(\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) = ((\<big_ast>ij \<in> I \<times> J. case_prod A ij) \<s>\<u>\<b>\<j> finite I)\<close>
  unfolding BI_eq_iff Mul_Quant_def
  by (clarsimp; rule;
      clarsimp simp add: finite_prod_subjection ex_in_conv finite_cartesian_product_iff;
      cases \<open>I = {}\<close>; cases \<open>J = {}\<close>; simp add: prod.cartesian_product)
  thm prod.cartesian_product

subsection \<open>Existential Quantification\<close>

lemma ExSet_inhabited_E[elim!]:
  \<open>Inhabited (ExSet S) \<Longrightarrow> (\<And>x. Inhabited (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by simp blast

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. S x \<i>\<m>\<p>\<l>\<i>\<e>\<s> C x)
\<Longrightarrow> ExSet S \<i>\<m>\<p>\<l>\<i>\<e>\<s> Ex C \<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp; blast)

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. C x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> S x)
\<Longrightarrow> Ex C \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> ExSet S \<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp; blast)

lemma ExSet_ord[\<phi>reason 1000]:
  \<open> (\<And>c. S c \<le> S' c)
\<Longrightarrow> ExSet S \<le> ExSet S' \<close>
  unfolding BI_sub_iff
  by simp blast

subsubsection \<open>Syntax\<close>

syntax
  "_SetcomprNu" :: "'a \<Rightarrow> pttrns \<Rightarrow> bool \<Rightarrow> 'a BI"  ("_ \<s>\<u>\<b>\<j>/ _./ _" [14,0,15] 14)

parse_translation \<open>[
  (\<^syntax_const>\<open>_SetcomprNu\<close>, fn ctxt => fn [X,idts,P] =>
  let fun subst l Bs (Free v) =
            let val i = find_index (fn v' => v = v') Bs
             in if i = ~1 then Free v else Bound (i+l)
            end
        | subst l Bs (A $ B) = subst l Bs A $ subst l Bs B
        | subst l Bs (Abs(N,T,X)) = Abs(N,T, subst (l+1) Bs X)
        | subst l Bs X = X
      fun trans_one (Bs,C) (Const(\<^syntax_const>\<open>_unit\<close>, _))
            = Abs ("", \<^Type>\<open>unit\<close>, C [])
        | trans_one (Bs,C) (Const(\<^const_syntax>\<open>Pair\<close>, _)
                                $ (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free (A, T) $ Ac)
                                $ B)
            = Const(\<^const_syntax>\<open>case_prod\<close>, dummyT) $ (
                Const(\<^syntax_const>\<open>_constrainAbs\<close>, dummyT)
                  $ Abs (A, T, trans_one ((A,T)::Bs, C) B)
                  $ Ac
              )
        | trans_one (Bs,C) (Const(\<^const_syntax>\<open>Pair\<close>, _)
                                $ (Const (\<^syntax_const>\<open>_constrain\<close>, _)
                                      $ (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free (A, T) $ T') $ Ac)
                                $ B)
            = Const(\<^const_syntax>\<open>case_prod\<close>, dummyT) $ (
                Const(\<^syntax_const>\<open>_constrainAbs\<close>, dummyT)
                  $ (Const(\<^syntax_const>\<open>_constrainAbs\<close>, dummyT)
                      $ Abs (A, T, trans_one ((A,T)::Bs, C) B)
                      $ T')
                  $ Ac
              )
        | trans_one (Bs,C) (Const(\<^const_syntax>\<open>Pair\<close>, _)
                                $ Const (\<^syntax_const>\<open>_unit\<close>, _)
                                $ B)
            = Const(\<^const_syntax>\<open>case_prod\<close>, dummyT) $ (
                Const(\<^syntax_const>\<open>_constrainAbs\<close>, dummyT)
                  $ Abs ("", dummyT, trans_one (Bs, C) B)
                  $ Const(\<^type_syntax>\<open>unit\<close>, dummyT)
              )
        | trans_one (Bs,C) (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free (A, T) $ Ac)
            = Const(\<^syntax_const>\<open>_constrainAbs\<close>, dummyT)
                  $ Abs (A, T, C ((A,T)::Bs))
                  $ Ac
      fun trans (Const (\<^syntax_const>\<open>_pttrns\<close>, _) $ A $ B) Bs
            = Const (\<^const_syntax>\<open>ExSet\<close>, dummyT) $ trans_one (Bs,trans B) A
        | trans B Bs
            = Const (\<^const_syntax>\<open>ExSet\<close>, dummyT) $ trans_one (Bs, (fn Bs =>
                case P of(* Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free ("True",_) $ _
                            => subst 0 Bs X
                        |*) Const (\<^const_syntax>\<open>top\<close>, _)
                            => subst 0 Bs X
                        | _ => Const (\<^const_syntax>\<open>Subjection\<close>, dummyT) $ subst 0 Bs X $ subst 0 Bs P
              )) B
   in trans idts [] end)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>ExSet\<close>, fn ctxt => fn [X] =>
    let fun subst l Bs (Bound i)
              = if l <= i andalso i-l <= length Bs then List.nth(Bs, i-l) else Bound i
          | subst l Bs (Abs (N,T,X)) = Abs (N,T, subst (l+1) Bs X)
          | subst l Bs (A $ B) = subst l Bs A $ subst l Bs B
          | subst l Bs X = X
        fun trans (Vs,Bs) (Const(\<^const_syntax>\<open>case_prod\<close>, _) $ Abs (A,T,X))
              = if T = \<^Type>\<open>unit\<close> andalso A = ""
                then trans (Const(\<^syntax_const>\<open>_unit\<close>, dummyT) :: Vs, Bs) X
                else let val bound = Const(\<^syntax_const>\<open>_bound\<close>, dummyT) $ Free(A,T)
                      in trans (bound::Vs, bound::Bs) X
                     end
          | trans (Vs,Bs) (Abs(A,T, Const(\<^const_syntax>\<open>ExSet\<close>, _) $ X))
              = let val bound = Const(\<^syntax_const>\<open>_bound\<close>, dummyT) $ Free(A,T)
                    val var = fold (fn v => fn v' => Const(\<^const_syntax>\<open>Pair\<close>,dummyT) $ v $ v')
                                    Vs bound
                    val (X',idts',P') = trans ([], bound :: Bs) X
                 in (X', Const(\<^syntax_const>\<open>_pttrns\<close>, dummyT) $ var $ idts', P')
                end
          | trans (Vs,Bs0) (Abs(A,T,B))
              = let val bound = Const(\<^syntax_const>\<open>_bound\<close>, dummyT) $ Free(A,T)
                    val v' = if T = \<^Type>\<open>unit\<close> andalso A = ""
                             then Const(\<^syntax_const>\<open>_unit\<close>, dummyT)
                             else bound
                    val var = fold (fn v => fn v' => Const(\<^const_syntax>\<open>Pair\<close>,dummyT) $ v $ v')
                                    Vs v'
                    val Bs = bound :: Bs0
                    val (X,P) = case B of Const(\<^const_syntax>\<open>Subjection\<close>, _) $ X $ P => (X,P)
                                        | _ => (B, Const(\<^const_syntax>\<open>top\<close>, dummyT))
                 in (subst 0 Bs X, var, subst 0 Bs P)
                end
        val (X',idts',P') = trans ([],[]) X
     in Const(\<^syntax_const>\<open>_SetcomprNu\<close>, dummyT) $ X' $ idts' $ P' end)
]\<close>


subsubsection \<open>Semantic Explanation\<close>

text \<open>Semantically, an existential quantification in BI actually represents union of resources
  matching the existentially quantified assertion, as shown by the following lemma.\<close>

lemma " Union { S x |x. P x } = (S x \<s>\<u>\<b>\<j> x. P x) "
  by (simp add: set_eq_iff ExSet_def Subjection_def) blast

subsubsection \<open>Simplifications\<close>

lemma ExSet_pair: "ExSet T = (\<exists>*a b. T (a,b))"
  unfolding BI_eq_iff by clarsimp

lemma ExSet_simps[simp, \<phi>programming_base_simps]:
  \<open>ExSet 0 = 0\<close>
  \<open>ExSet (\<lambda>_. T) = T\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> x = y) = (F y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> y = x) = (F y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> x = y \<and> P x) = (F y \<s>\<u>\<b>\<j> P y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> y = x \<and> P x) = (F y \<s>\<u>\<b>\<j> P y)\<close>
  \<open>(ExSet X \<s>\<u>\<b>\<j> PP) = (ExSet (\<lambda>c. X c \<s>\<u>\<b>\<j> PP))\<close>
(*  \<open>(\<exists>* x. x = t \<and> P x) = P t\<close>
"\<And>P. (\<exists>x. x = t \<and> P x) = P t"
    "\<And>P. (\<exists>x. t = x \<and> P x) = P t"*)
  unfolding BI_eq_iff by simp_all

lemma Ex_transformation_expn:
  \<open>((\<exists>*x. A x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) \<longleftrightarrow> (\<forall>x. A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P)\<close>
  unfolding Transformation_def ExSet_expn
  by blast

paragraph \<open>With Multiplicative Conjunction\<close>

lemma ExSet_times_left [simp, \<phi>programming_base_simps]:
  "(ExSet T * R) = (\<exists>* c. T c * R )"
  by (simp add: BI_eq_iff, blast)

lemma ExSet_times_right[simp, \<phi>programming_base_simps]:
  "(L * ExSet T) = (\<exists>* c. L * T c)"
  by (simp add: BI_eq_iff, blast)

paragraph \<open>With Additive Conjunction\<close>

lemma ExSet_adconj:
  \<open>A \<and>\<^sub>B\<^sub>I (\<exists>*c. B c) \<equiv> \<exists>*c. A \<and>\<^sub>B\<^sub>I B c\<close>
  \<open>(\<exists>*c. B c) \<and>\<^sub>B\<^sub>I A \<equiv> \<exists>*c. B c \<and>\<^sub>B\<^sub>I A\<close>
  unfolding atomize_eq BI_eq_iff
  by simp+

paragraph \<open>With Additive Disjunction\<close>

lemma ExSet_addisj:
  \<open>A + (\<exists>*c. B c) \<equiv> \<exists>*c. A + B c\<close>
  \<open>(\<exists>*c. B c) + A \<equiv> \<exists>*c. B c + A\<close>
  unfolding atomize_eq BI_eq_iff
  by simp+


subsubsection \<open>Rules\<close>

lemma ExSet_transformation:
  \<open>(\<And>x. S x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' x \<w>\<i>\<t>\<h> P)
\<Longrightarrow> ExSet S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet S' \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp, blast)

lemma ExSet_transformation_I:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' x \<w>\<i>\<t>\<h> P
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (ExSet S') \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp, blast)

lemma ExSet_transformation_I_R:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (ExSet S') \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by (cases C; clarsimp, blast)


lemma ExSet_additive_disj:
  \<open>(\<exists>*x. A x + B x) = ExSet A + ExSet B\<close>
  \<open>ExSet (A + B) = ExSet A + ExSet B\<close>
  unfolding BI_eq_iff by (simp_all add: plus_fun) blast+

ML_file \<open>library/tools/simproc_ExSet_expand_quantifier.ML\<close>



subsection \<open>Universal Quantification\<close>

definition AllSet :: \<open>('a \<Rightarrow> 'b BI) \<Rightarrow> 'b BI\<close> (binder "\<forall>\<^sub>B\<^sub>I" 10)
  where \<open>AllSet X = {y. \<forall>x. y \<in> X x}\<close>

lemma AllSet_expn[simp, \<phi>expns]:
  \<open>p \<Turnstile> (\<forall>\<^sub>B\<^sub>Ix. B x) \<longleftrightarrow> (\<forall>x. p \<Turnstile> B x)\<close>
  unfolding AllSet_def Satisfaction_def by simp

lemma AllSet_subset:
  \<open>A \<subseteq> (\<forall>\<^sub>B\<^sub>I x. B x) \<longleftrightarrow> (\<forall>x. A \<subseteq> B x)\<close>
  unfolding AllSet_def subset_iff by (rule; clarsimp; blast)

lemma AllSet_refl:
  \<open>(\<And>x. refl (B x))
\<Longrightarrow> refl (\<forall>\<^sub>B\<^sub>I x. B x)\<close>
  unfolding AllSet_def
  by (simp add: refl_on_def)

lemma AllSet_trans:
  \<open>(\<And>x. trans (B x))
\<Longrightarrow> trans (\<forall>\<^sub>B\<^sub>I x. B x)\<close>
  unfolding AllSet_def
  by (smt (verit) mem_Collect_eq transD transI)

lemma [elim!]:
  \<open>Inhabited (AllSet S) \<Longrightarrow> (Inhabited (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by clarsimp blast

lemma [\<phi>inhabitance_rule 1000]:
  \<open> S x \<i>\<m>\<p>\<l>\<i>\<e>\<s> C
\<Longrightarrow> AllSet S \<i>\<m>\<p>\<l>\<i>\<e>\<s> C \<close>
  unfolding Action_Tag_def
  by clarsimp blast



subsection \<open>Basic \<phi>-Types \& Embedding of Logic Connectives\<close>

subsubsection \<open>Identity \<phi>-Type\<close>

definition Itself :: " ('a,'a) \<phi> " where "Itself x = {x}"

lemma Itself_expn[\<phi>expns, iff]:
  "p \<Turnstile> (x \<Ztypecolon> Itself) \<longleftrightarrow> p = x"
  unfolding \<phi>Type_def Itself_def Satisfaction_def by auto

lemma Itself_inhabited_E[elim!]:
  \<open> Inhabited (x \<Ztypecolon> Itself) \<Longrightarrow> C \<Longrightarrow> C \<close> .

lemma Itself_inhabited[\<phi>reason 1000, simp, intro!]:
  \<open> Inhabited (x \<Ztypecolon> Itself) \<close>
  unfolding Inhabited_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain Itself (\<lambda>_. True) \<close>
  unfolding Abstract_Domain_def
  using Inhabited_fallback_True by blast

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain\<^sub>M\<^sub>C Itself mul_carrier \<close>
  unfolding Abstract_Domain\<^sub>M\<^sub>C_def Action_Tag_def Inhabited\<^sub>M\<^sub>C_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain\<^sub>L Itself (\<lambda>_. True) \<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def Inhabited_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> Abstract_Domain\<^sub>M\<^sub>C\<^sub>L Itself mul_carrier \<close>
  unfolding Abstract_Domain\<^sub>M\<^sub>C\<^sub>L_def Action_Tag_def Inhabited\<^sub>M\<^sub>C_def
  by simp

lemma Itself_E[\<phi>reason default 10]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<close>
  unfolding Transformation_def Premise_def by simp

text \<open>The Itself introduction rule cannot be written in such \<exists>free-ToA form but in To-Transformation form.\<close>

lemma satisfication_encoding:
  \<open> (x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<w>\<i>\<t>\<h> P) \<longleftrightarrow> x \<Turnstile> (y \<Ztypecolon> T) \<and> P \<close>
  unfolding Transformation_def by simp


subsubsection \<open>Embedding of \<open>\<top>\<close>\<close>

definition \<phi>Any :: \<open>('x, unit) \<phi>\<close> ("\<top>\<^sub>\<phi>")
  where \<open>\<top>\<^sub>\<phi> = (\<lambda>_. UNIV)\<close>

setup \<open>Sign.mandatory_path "\<phi>Any"\<close>

lemma unfold:
  \<open>(x \<Ztypecolon> \<top>\<^sub>\<phi>) = UNIV\<close>
  unfolding \<phi>Any_def \<phi>Type_def ..

lemma expansion[simp]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<top>\<^sub>\<phi>) \<longleftrightarrow> True\<close>
  unfolding \<phi>Any.unfold
  by simp

setup \<open>Sign.parent_path\<close>

lemma [\<phi>reason 1000]:
  \<open>x \<Ztypecolon> \<top>\<^sub>\<phi> \<i>\<m>\<p>\<l>\<i>\<e>\<s> True\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1000]:
  \<open>True \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> \<top>\<^sub>\<phi>\<close>
  unfolding Action_Tag_def Inhabited_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> UNIV \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P\<close>
  unfolding \<phi>Any.unfold
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> UNIV \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<top>\<^sub>\<phi> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding \<phi>Any.unfold
  by simp


subsubsection \<open>Embedding of Empty\<close>

definition \<phi>None :: \<open>('v::one, unit) \<phi>\<close> ("\<circle>")
  where \<open>\<phi>None = (\<lambda>x. { 1 }) \<close>

lemma \<phi>None_expn[\<phi>expns, simp]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<phi>None) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>None_def \<phi>Type_def Satisfaction_def
  by simp

lemma \<phi>None_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>None) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>None_itself_is_one[simp]:
  \<open>(any \<Ztypecolon> \<phi>None) = 1\<close>
  unfolding BI_eq_iff by simp

(*
lemma [\<phi>reason 1200]:
  \<open>any \<Ztypecolon> \<phi>None \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<Ztypecolon> Itself\<close>
  unfolding Transformation_def by simp *)

(*subsubsection \<open>Insertion into Unital Algebra\<close>

definition \<phi>Option_Insertion :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x option) \<phi>\<close> ("\<half_blkcirc> _" [91] 90)
  where \<open>\<half_blkcirc> T = (\<lambda>x. case x of Some x' \<Rightarrow> { Some v |v. v \<in> (x' \<Ztypecolon> T) } | None \<Rightarrow> { None })\<close>

lemma \<phi>Option_Insertion_expn[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x' \<Ztypecolon> \<half_blkcirc> T) \<longleftrightarrow> (case x' of None \<Rightarrow> p = None
                                 | Some x \<Rightarrow> \<exists>v. p = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T)) \<close>
  unfolding \<phi>Option_Insertion_def \<phi>Type_def Satisfaction_def
  by (cases x'; clarsimp)+

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P x)
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> pred_option P x\<close>
  unfolding Action_Tag_def Inhabited_def
  by (cases x; clarsimp)

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. P x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T)
\<Longrightarrow> pred_option P x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> \<half_blkcirc> T\<close>
  unfolding Action_Tag_def Inhabited_def
  by (cases x; clarsimp)
*)

subsubsection \<open>Embedding of Separation Conjunction\<close>

lemma \<phi>Prod_expn[\<phi>expns, simp]:
  "concrete \<Turnstile> (x \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>cb ca. concrete = cb * ca \<and> cb \<Turnstile> (snd x \<Ztypecolon> B) \<and> ca \<Turnstile> (fst x \<Ztypecolon> A) \<and> cb ## ca)"
  unfolding \<phi>Prod_def \<phi>Type_def by (cases x; simp)

lemma \<phi>Prod_expn':
  \<open>((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)\<close>
  unfolding BI_eq_iff by (simp add: set_mult_expn)

lemma \<phi>Prod_expn'':
  \<open> NO_MATCH (xx,yy) x
\<Longrightarrow> (x \<Ztypecolon> A \<^emph> B) = (snd x \<Ztypecolon> B) * (fst x \<Ztypecolon> A)\<close>
  unfolding BI_eq_iff by (cases x; simp add: set_mult_expn)

bundle \<phi>Prod_expn = \<phi>Prod_expn'[simp] \<phi>Prod_expn''[simp]

lemma [\<phi>reason 1000]:
  \<open> fst x \<Ztypecolon> T1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> C1
\<Longrightarrow> snd x \<Ztypecolon> T2 \<i>\<m>\<p>\<l>\<i>\<e>\<s> C2
\<Longrightarrow> x \<Ztypecolon> T1 \<^emph> T2 \<i>\<m>\<p>\<l>\<i>\<e>\<s> C1 \<and> C2\<close>
  unfolding Inhabited_def Action_Tag_def
  by (cases x; simp, blast)

lemma \<phi>Prod_\<phi>None:
  \<open>((x',y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'a::sep_magma_1 BI)\<close>
  \<open>((x,y') \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'b::sep_magma_1 BI)\<close>
  unfolding BI_eq_iff
  by (simp_all add: set_mult_expn)

lemma destruct_\<phi>Prod_\<phi>app: (*TODO: merge this into general destruction*)
  \<open>x \<Ztypecolon> T \<^emph> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x \<Ztypecolon> U) * (fst x \<Ztypecolon> T)\<close>
  by (cases x; simp add: Transformation_def set_mult_expn)

lemma \<phi>Prod_transformation:
  " x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> N' \<w>\<i>\<t>\<h> Pa
\<Longrightarrow> y \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> M' \<w>\<i>\<t>\<h> Pb
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x',y') \<Ztypecolon> N' \<^emph> M' \<w>\<i>\<t>\<h> Pa \<and> Pb"
  unfolding Transformation_def by simp blast
  (*The rule is not added into the \<phi>-LPR because such product is solved by Structural Extract*)

lemma [\<phi>reason 1000]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x \<Ztypecolon> M) * (fst x \<Ztypecolon> N) \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> N \<^emph> M \<w>\<i>\<t>\<h> P"
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1001 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_,_) \<Ztypecolon> _ \<^emph> _ \<w>\<i>\<t>\<h> _\<close> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> _ \<^emph> _ \<w>\<i>\<t>\<h> _\<close>]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> M) * (x \<Ztypecolon> N) \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> N \<^emph> M \<w>\<i>\<t>\<h> P"
  by (simp add: \<phi>Prod_expn')


subsubsection \<open>Type-level Remainders\<close>

lemma Cond_\<phi>Prod_expn:
  \<open> (x \<Ztypecolon> T \<^emph>[C] U) = (if C then (x \<Ztypecolon> T \<^emph> U) else (fst x \<Ztypecolon> T)) \<close>
  unfolding Cond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

lemma Cond_\<phi>Prod_expn'[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> T \<^emph>[C] U) = (if C then p \<Turnstile> (x \<Ztypecolon> T \<^emph> U) else p \<Turnstile> (fst x \<Ztypecolon> T)) \<close>
  unfolding Cond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

lemma Cond_\<phi>Prod_expn_const[simp]:
  \<open>T \<^emph>[True] U \<equiv> T \<^emph> U\<close>
  \<open>x \<Ztypecolon> T \<^emph>[False] U \<equiv> fst x \<Ztypecolon> T\<close>
  by (simp_all add: Cond_\<phi>Prod_def \<phi>Type_def)

lemma [\<phi>reason 1000]:
  \<open> fst x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> snd x \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[C] U \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> (C \<longrightarrow> Q) \<close>
  unfolding Action_Tag_def Inhabited_def
  by (cases C; clarsimp; blast)


subsubsection \<open>Insertion into Unital Algebra\<close>

definition \<phi>Some :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<black_circle> _" [91] 90)
  where \<open>\<black_circle> T = (\<lambda>x. { Some v |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma \<phi>Some_expn[simp, \<phi>expns]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<black_circle> T) \<longleftrightarrow> (\<exists>v. p = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>Some_def Satisfaction_def
  by simp

lemma \<phi>Some_\<phi>Prod:
  \<open> \<black_circle> T \<^emph> \<black_circle> U = \<black_circle> (T \<^emph> U) \<close>
  by (rule \<phi>Type_eqI; clarsimp; force)

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<close>
  unfolding Action_Tag_def Inhabited_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T
\<Longrightarrow> P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> \<black_circle> T \<close>
  unfolding Action_Tag_def Inhabited_def
  by clarsimp

lemma \<phi>Some_transformation_strip:
  \<open> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P \<equiv> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<close>
  unfolding atomize_eq Transformation_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Some_transformation_strip .

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<^emph>[Cw] \<black_circle> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph>[Cr] \<black_circle> R \<w>\<i>\<t>\<h> P\<close>
  by (cases Cw; cases Cr; simp add: \<phi>Some_\<phi>Prod \<phi>Some_transformation_strip)

lemma \<phi>Some_eq_term_strip:
  \<open> (x \<Ztypecolon> \<black_circle> T) = (y \<Ztypecolon> \<black_circle> U) \<equiv> (x \<Ztypecolon> T) = (y \<Ztypecolon> U) \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp blast



subsection \<open>Equivalence of Objects\<close>

definition Object_Equiv :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Object_Equiv T eq \<longleftrightarrow> (\<forall>x y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T))\<close>

declare [[
  \<phi>reason_default_pattern \<open>Object_Equiv ?T _\<close> \<Rightarrow> \<open>Object_Equiv ?T _\<close> (100),
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Object_Equiv _ _\<close>
]]

subsubsection \<open>Reasoning Rules\<close>

lemma Object_Equiv_fallback[\<phi>reason default 1]:
  \<open>Object_Equiv T (=)\<close>
  unfolding Object_Equiv_def by simp


(*
lemma [\<phi>reason 800 for \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> _\<close>]:
  " Object_Equiv T eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T"
  unfolding Object_Equiv_def Transformation_def Premise_def by clarsimp*)

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv \<top>\<^sub>\<phi> (\<lambda>_ _. True) \<close>
  unfolding Object_Equiv_def Transformation_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv \<circle> (\<lambda>_ _. True) \<close>
  unfolding Object_Equiv_def Transformation_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv (\<black_circle> T) eq \<close>
  unfolding Object_Equiv_def Transformation_def
  by simp blast

lemma [\<phi>reason 1000]:
  \<open> (\<And>a. Object_Equiv (\<lambda>x. S x a) (R a))
\<Longrightarrow> Object_Equiv (\<lambda>x. ExSet (S x)) (\<lambda>x y. \<forall>a. R a x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp; blast)

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv S R
\<Longrightarrow> Object_Equiv (\<lambda>x. S x \<s>\<u>\<b>\<j> P x) (\<lambda>x y. P x \<longrightarrow> R x y \<and> P y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. S1 x \<and>\<^sub>B\<^sub>I S2 x) (\<lambda>x y. R1 x y \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. S1 x + S2 x) (\<lambda>x y. R1 x y \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

(* lemma
  \<open> (\<And>x. Object_Equiv (R x) (T x))
\<Longrightarrow> Object_Equiv (\<lambda>x y. T y = T x \<and> R x (f x) (f y)) (\<lambda>x. f x \<Ztypecolon> T x)\<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp *)

lemma [\<phi>reason 1000]:
  \<open> (\<And>a. Object_Equiv (\<lambda>x. S x a) (R a))
\<Longrightarrow> Object_Equiv (\<lambda>x. AllSet (S x)) (\<lambda>x y. \<forall>a. R a x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp simp add: AllSet_expn; blast)

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. S1 x * S2 x) (\<lambda> x y. R1 x y \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp simp add: set_mult_expn; blast)

lemma [\<phi>reason 1000]:
  \<open> Object_Equiv T\<^sub>a Eq\<^sub>a
\<Longrightarrow> Object_Equiv T\<^sub>b Eq\<^sub>b
\<Longrightarrow> Object_Equiv (T\<^sub>a \<^emph> T\<^sub>b) (\<lambda>(x\<^sub>a, x\<^sub>b) (y\<^sub>a, y\<^sub>b). Eq\<^sub>a x\<^sub>a y\<^sub>a \<and> Eq\<^sub>b x\<^sub>b y\<^sub>b) \<close>
  unfolding Object_Equiv_def Transformation_def
  by (clarsimp simp add: set_mult_expn; blast)

(*
lemma
  \<open> (\<And>x y. Rx x y \<longleftrightarrow> (S1 x * S2 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S1 y * S2 y))
\<Longrightarrow> (\<And>x y. R1 x y \<longleftrightarrow> (S1 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S1 y))
\<Longrightarrow> (\<And>x y. R2 x y \<longleftrightarrow> (S2 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S2 y))
\<Longrightarrow> (\<And>x y. Rx x y \<Longrightarrow> R1 x y \<or> R2 x y)\<close>
  unfolding Transformation_def
  apply (auto simp add: set_mult_expn)*)

lemma
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. {p. p \<Turnstile> S1 x \<longrightarrow> p \<Turnstile> S2 x}) (\<lambda>x y. R1 y x \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp simp add: Satisfaction_def)

lemma [\<phi>reason 1000]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Object_Equiv A Ea)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Object_Equiv B Eb)
\<Longrightarrow> Object_Equiv (if C then A else B) (if C then Ea else Eb) \<close>
  unfolding Premise_def
  by (cases C; simp)

(*
lemma
  \<open> (\<And>x y. Rx x y \<longleftrightarrow> ({p. p \<in> S1 x \<longrightarrow> p \<in> S2 x} \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {p. p \<in> S1 y \<longrightarrow> p \<in> S2 y}))
\<Longrightarrow> (\<And>x y. R1 x y \<longleftrightarrow> (S1 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S1 y))
\<Longrightarrow> (\<And>x y. R2 x y \<longleftrightarrow> (S2 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S2 y))
\<Longrightarrow> (\<And>x y. Rx x y \<Longrightarrow> R1 y x \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  apply (auto simp add: AllSet_expn)*)

(*
lemma
  \<open> (\<And>x y. Rx x y \<longleftrightarrow> (S1 x \<union> S2 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S1 y \<inter> S2 y))
\<Longrightarrow> (\<And>x y. R1 x y \<longleftrightarrow> (S1 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S1 y))
\<Longrightarrow> (\<And>x y. R2 x y \<longleftrightarrow> (S2 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S2 y))
\<Longrightarrow> (\<And>x y. Rx x y \<Longrightarrow> R1 x y \<and> R2 x y)\<close>
  unfolding Transformation_def
  apply (auto simp add: Subjection_expn) *)

lemma Object_Equiv_Mul_Quant[\<phi>reason 1000]:
  \<open> (\<And>i\<in>S. Object_Equiv (\<lambda>x. A x i) (eq i))
\<Longrightarrow> Object_Equiv (\<lambda>x. \<big_ast>i\<in>S. A x i) (\<lambda>x y. \<forall>i. eq i x y)\<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
            meta_Ball_def Premise_def Mul_Quant_def
  proof (clarsimp, unfold Satisfaction_def)
    fix x y v
    assume prems: \<open>(\<And>x. x \<in> S \<Longrightarrow> \<forall>xa y. eq x xa y \<longrightarrow> (\<forall>v. v \<in> A xa x \<longrightarrow> v \<in> A y x))\<close>
                  \<open>\<forall>i. eq i x y\<close>
                  \<open>v \<in> prod (A x) S\<close>
       and \<open>finite S\<close>
    show \<open>v \<in> prod (A y) S\<close>
      by (insert prems;
          induct arbitrary: x y v rule: finite_induct[OF \<open>finite S\<close>];
          clarsimp simp add: set_mult_expn;
          metis)
  qed

subsection \<open>Reasoning Settings\<close>

ML_file \<open>library/syntax/Phi_Syntax0.ML\<close>


subsubsection \<open>The Lattice of the Partial Transformations\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason default 1]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def by blast

lemma [\<phi>reason default 2]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, undefined) \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason default 1]:
  \<open> (x, undefined) \<Ztypecolon> T \<^emph>[False] Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yr \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst yr \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] snd yr \<Ztypecolon> R \<w>\<i>\<t>\<h> P \<close>
  by (cases C; clarsimp simp add: \<phi>Some_transformation_strip \<phi>Prod_expn'')

lemma ToA_by_Equiv_Class
      [\<phi>reason default 5 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>
                         except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y  \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> Object_Equiv U eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def by clarsimp

lemma ToA_by_Equiv_Class'
      [\<phi>reason default 5 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                         except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y  \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Object_Equiv U eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def REMAINS_def
  by (cases C; clarsimp; meson Transformation_def implies_left_frame)

text \<open>Convention: Any meaningful transformation rules should be of priority greater than 5
  (the of \<open>ToA_by_Equiv_Class\<close>)

TODO: move me!\<close>


subsubsection \<open>Reflexive Transformation\<close>

paragraph \<open>When the target and the source are either alpha-equivalent or unified\<close>

text \<open>Applying reflexive transformation on alpha-equivalent couples of source and target is safe,
so be applied of high priority.
In contrast, unification by reflexive transformation is aggressive. Therefore, they are applied
only when no other rules are applicable.\<close>

declare [[\<phi>trace_reasoning = 1]]

(*TODO: Auto_Transform_Hint*)

declare transformation_refl [\<phi>reason 4000 for \<open>?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<w>\<i>\<t>\<h> _\<close>
                                              \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?T \<w>\<i>\<t>\<h> _\<close>,
                             \<phi>reason default 3 for \<open>?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A' \<w>\<i>\<t>\<h> _\<close>]
                                     \<comment> \<open>the priority 3 is lower than ToA_by_Equiv_Class and higher than any fallback\<close>

lemma transformation_refl_assigning_remainder [\<phi>reason 4000 for \<open>_ * ?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _ \<close>
                                                                \<open>_ * (_ \<Ztypecolon> ?T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>,
                                               \<phi>reason default 3 for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open>R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R\<close>
  unfolding REMAINS_def
  by simp

lemma transformation_refl_with_remainder [\<phi>reason 4000 for \<open>?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                                           \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>,
                                          \<phi>reason default 3 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open>A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top>\<close>
  unfolding REMAINS_def
  by simp

lemma transformation_refl_assigning_W [\<phi>reason 4000,
                                       \<phi>reason default 3 for \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open>x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x, undefined) \<Ztypecolon> (T \<^emph> U) \<^emph>[False] \<top>\<^sub>\<phi>\<close>
  by simp

lemma transformation_refl_assigning_R [\<phi>reason 4000,
                                       \<phi>reason default 3 for \<open>_ \<Ztypecolon> (_ \<^emph> _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open>x \<Ztypecolon> (T \<^emph> U) \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst x \<Ztypecolon> T \<^emph>[True] U\<close>
  by simp

lemma transformation_refl_with_WR [\<phi>reason 4001,
                                   \<phi>reason default 4 for \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
        \<comment> \<open>Higher than \<open>transformation_refl\<close> to set the condition variable Cr\<close>
  \<open>x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi>\<close>
  by simp


paragraph \<open>When the target is a schematic variable\<close>

ML \<open>
(* (\<And>x. X x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> P) where ?Y is a variable.
   When X contains some quantified variables \<open>x\<close> that do not parameterize ?Y, the procedure
   existentially quantifies X, and assign \<open>\<exists>x. X x\<close> to ?Y.
   cannot work on \<open>_ \<^emph>[_] _\<close> (*TODO*)
 *)
fun apply_refl_by_unifying (refl, exintro', Gx, Gy) ctxt thm =
  let val (vs, _, goal) = Phi_Help.leading_antecedent (Thm.prop_of thm)
      val N = length vs
      val (X0,Y0,_) = Phi_Syntax.dest_transformation goal
      val (X, Y) = (Gx X0, Gy Y0)
      val (Var V, args) = strip_comb Y
      val bnos = map_filter (fn Bound i => SOME i | _ => NONE) args
      val bads = subtract (op =) bnos (Term.loose_bnos X)
   in if null bads
   then Phi_Reasoner.single_RS refl ctxt thm
   else case exintro'
     of NONE => Seq.empty
      | SOME exintro => let
      val N_bads = length bads
      val N_bnos = length bnos
      val (argTys, \<^Type>\<open>set \<open>TY\<close>\<close>) = Term.strip_type (snd V)
      val insts' = List.tabulate (N, fn i =>
            let val bi = find_index (fn k => k = i) bads
                val ci = find_index (fn k => k = i) bnos
             in if bi <> ~1
                then Bound (N_bads - 1 - bi)
                else if ci <> ~1
                then Bound (N_bads + N_bnos - 1 - ci)
                else Term.dummy (*not occur*)
            end)
      val Y'1 = subst_bounds (insts', X)
      val Y'2 = fold (fn j => fn TM =>
                  let val (name,T) = List.nth (vs, N-1-j)
                   in \<^Const>\<open>ExSet \<open>T\<close> \<open>TY\<close>\<close> $ Abs (name, T, TM)
                  end) bads Y'1
      val Y'3 = fold (fn (_, Bound j) => (fn TM =>
                            let val (name,T) = List.nth (vs, N-1-j)
                             in Abs (name, T, TM)
                            end)
                       | (ty, _) => (fn TM => Abs ("_", ty, TM))
                     ) (argTys ~~ args) Y'2
   in Thm.instantiate (TVars.empty, Vars.make [(V, Thm.cterm_of ctxt Y'3)]) thm
   |> funpow N_bads (fn th => exintro RS th)
   |> Phi_Reasoner.single_RS refl ctxt
   handle THM _ => Seq.empty
  end
  end
\<close>

\<phi>reasoner_ML transformation_refl_var 3900 (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm transformation_refl}, SOME @{thm ExSet_transformation_I}, I, I
      ) ctxt thm) \<close>

\<phi>reasoner_ML transformation_refl_var_R 3900 (\<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm transformation_refl_assigning_remainder}, SOME @{thm ExSet_transformation_I_R},
          (fn R $ A => A), (fn _ (*REMAINS*) $ A $ _ $ _ => A)
      ) ctxt thm) \<close>

\<phi>reasoner_ML transformation_refl_var_R' 3901 (\<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _ \<w>\<i>\<t>\<h> _\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm transformation_refl_with_remainder}, SOME @{thm ExSet_transformation_I_R},
          I, (fn _ (*REMAINS*) $ A $ _ $ _ => A)
      ) ctxt thm) \<close>

text \<open>Here, we assign the semantics of schematic variables occurring in targets and sources to be,
  a wild-card for any single separation item.\<close>

declare transformation_refl_assigning_W [\<phi>reason 3900 for \<open>_ \<Ztypecolon> ?var \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph> _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]
        transformation_refl_assigning_R [\<phi>reason 3900 for \<open>_ \<Ztypecolon> (_ \<^emph> _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?var \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]
        transformation_refl_with_WR [\<phi>reason 3901 for \<open>_ \<Ztypecolon> ?var \<^emph>[False] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                                      \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?var \<^emph>[False] _ \<w>\<i>\<t>\<h> _\<close>]
(*
lemma [\<phi>reason 4100 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?var_U \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                        \<open>_ \<Ztypecolon> ?var_T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                    except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[False] _ \<w>\<i>\<t>\<h> _\<close>
                           \<open>_ \<Ztypecolon> _ \<^emph>[False] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> ERROR TEXT(\<open>Unable to reason the transformation where the target (or the source) has more than one variable assertions\<close>
               (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P)
               \<open>It usually means somewhere in the reasoning system is wrong\<close>)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<close>
  unfolding ERROR_def
  by blast
*)

text \<open>
TODO: move me!

NToA procedure addresses the transformation between any-to-many \<phi>-type items.
  Separation Extraction addresses that from many to one \<phi>-type item.
  The \<phi>-type themselves should provide the rules for one-to-one transformations, as they are primitive.
  Transformation Functor presented later provides an automation for this.

  However, a small supplementary is one-to-one with remainders.
  For unital algebras, the issue is easy as we can always force yielding remainders.
  For non-semigroups, after a reasoning branch splitting the cases for having remainder or not,
  the issue reduces immediately.
  For associative but non-unital algebras, a bit of work is required. 

\<close>

end