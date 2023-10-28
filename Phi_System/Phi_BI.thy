(*TODO: lift it to a chapter*)
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
  imports "Phi_Logic_Programming_Reasoner.PLPR" Phi_Preliminary
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

subsubsection \<open>Basic Rules\<close>

lemma BI_eq_iff:
  \<open>S = S' \<longleftrightarrow> (\<forall>u. u \<Turnstile> S \<longleftrightarrow> u \<Turnstile> S')\<close>
  unfolding Satisfaction_def set_eq_iff ..

subsubsection \<open>Basic Rewrites\<close>

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

subsubsection \<open>Reasoning Configuration\<close>

\<phi>reasoner_group extract_pure_sat = (%extract_pure+40, [%extract_pure+40, %extract_pure+70])
                                    for (\<open>_ \<longrightarrow> _ @action \<A>EIF\<close>, \<open>_ \<longrightarrow> _ @action \<A>ESC\<close>)
                                     in extract_pure_all and > extract_pure
  \<open>Rules extracting BI properties down to Satisfaction\<close>

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

definition Inhabited :: " 'a BI \<Rightarrow> bool "
  where "Inhabited S = (\<exists>p. p \<Turnstile> S)"
  \<comment> \<open>\<open>Inhabited S\<close> should be always an atom in the view of ATPs.

      The fallback of extracting implied pure facts returns the original \<open>Inhabited T\<close> unchanged,
      \<open>P \<i>\<m>\<p>\<l>\<i>\<e>\<s> Inhabited P\<close> where \<open>Inhabited P\<close> should be regarded as an atom.\<close>


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

\<phi>reasoner_group extract_pure_phity = (10, [10,10]) for (\<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P\<close>, \<open>P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T\<close>)
  > extract_pure_fallback and < extract_pure
  \<open>Entry points towards \<open>Abstract_Domain\<close> and \<open>Abstract_Domain\<^sub>L\<close> \<close>

subsubsection \<open>Basic Rules\<close>

lemma Inhabited_I:
  \<open>x \<Turnstile> S \<Longrightarrow> Inhabited S\<close>
  unfolding Inhabited_def ..

lemma Inhabited_fallback:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Inhabited X \<close>
  unfolding Action_Tag_def by blast

lemma Suf_Inhabited_fallback:
  \<open> Inhabited X \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> X \<close>
  unfolding Action_Tag_def by blast

\<phi>reasoner_ML Inhabited_fallback default 2 (\<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.is_generating_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Inhabited_fallback} RS sequent), Seq.empty)
)\<close>

\<phi>reasoner_ML Suf_Inhabited_fallback default 2 (\<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.is_generating_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Suf_Inhabited_fallback} RS sequent), Seq.empty)
)\<close>

lemma [\<phi>reason 1000]:
  \<open> P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P
\<Longrightarrow> Inhabited A\<close>
  unfolding Action_Tag_def Premise_def
  by blast

paragraph \<open>Sum Type\<close>

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

\<phi>reasoner_group abstract_domain_all = (1000, [1, 2000]) for (\<open>Abstract_Domain T d\<close>, \<open>Abstract_Domain\<^sub>L T d\<close>)
    \<open>All reasoning rules giving \<open>Abstract_Domain\<close> or \<open>Abstract_Domain\<^sub>L\<close>\<close>
 and abstract_domain = (1000, [1000, 1000]) for (\<open>Abstract_Domain T d\<close>, \<open>Abstract_Domain\<^sub>L T d\<close>)
                                             in abstract_domain_all
    \<open>Normal reasoning rules for \<open>Abstract_Domain\<close>, \<open>Abstract_Domain\<^sub>L\<close>\<close>
 and abstract_domain_fallback = (1, [1,1]) for (\<open>Abstract_Domain T d\<close>, \<open>Abstract_Domain\<^sub>L T d\<close>) < abstract_domain
                                            in abstract_domain_all
    \<open>Fallbacks reasoning rules for \<open>Abstract_Domain\<close>, \<open>Abstract_Domain\<^sub>L\<close> \<close>
 and derived_abstract_domain = (60, [50,70]) for (\<open>Abstract_Domain T d\<close>, \<open>Abstract_Domain\<^sub>L T d\<close>)
                                              in abstract_domain_all and < abstract_domain
    \<open>Automatically derived rules\<close>



paragraph \<open>Extracting Pure Facts\<close>

lemma Inhabitance_Implication_\<A>EIF [\<phi>reason %extract_pure]:
  \<open> A' \<longrightarrow> Inhabited A @action \<A>ESC
\<Longrightarrow> (A \<i>\<m>\<p>\<l>\<i>\<e>\<s> P) \<longrightarrow> (A' \<longrightarrow> P) @action \<A>EIF\<close>
  unfolding Action_Tag_def
  by blast

lemma Inhabitance_Implication_\<A>EIF_Sat:
  \<open>(A \<i>\<m>\<p>\<l>\<i>\<e>\<s> P) \<longrightarrow> ((\<exists>v. v \<Turnstile> A) \<longrightarrow> P) @action \<A>EIF\<close>
  unfolding Action_Tag_def Inhabited_def
  by blast

lemma Inhabitance_Implication_\<A>ESC[\<phi>reason %extract_pure]:
  \<open> Inhabited A \<longrightarrow> A' @action \<A>EIF
\<Longrightarrow> (A' \<longrightarrow> P) \<longrightarrow> (A \<i>\<m>\<p>\<l>\<i>\<e>\<s> P) @action \<A>ESC\<close>
  unfolding Action_Tag_def
  by blast

lemma Inhabitance_Implication_\<A>ESC_Sat:
  \<open>((\<exists>v. v \<Turnstile> A) \<longrightarrow> P) \<longrightarrow> (A \<i>\<m>\<p>\<l>\<i>\<e>\<s> P) @action \<A>ESC\<close>
  unfolding Action_Tag_def Inhabited_def
  by blast

lemma Sufficient_Inhabitance_\<A>EIF[\<phi>reason %extract_pure]:
  \<open> Inhabited A \<longrightarrow> A' @action \<A>EIF
\<Longrightarrow> (P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A) \<longrightarrow> (P \<longrightarrow> A') @action \<A>EIF\<close>
  unfolding Action_Tag_def
  by blast

lemma Sufficient_Inhabitance_\<A>EIF_Sat:
  \<open>(P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A) \<longrightarrow> (P \<longrightarrow> (\<exists>v. v \<Turnstile> A)) @action \<A>EIF\<close>
  unfolding Action_Tag_def Inhabited_def
  by blast

lemma Sufficient_Inhabitance_\<A>ESC[\<phi>reason %extract_pure]:
  \<open> A' \<longrightarrow> Inhabited A @action \<A>EIF
\<Longrightarrow> (P \<longrightarrow> A') \<longrightarrow> (P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A) @action \<A>ESC\<close>
  unfolding Action_Tag_def
  by blast

lemma Sufficient_Inhabitance_\<A>ESC_Sat:
  \<open>(P \<longrightarrow> (\<exists>v. v \<Turnstile> A)) \<longrightarrow> (P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A) @action \<A>ESC\<close>
  unfolding Action_Tag_def Inhabited_def
  by blast

bundle extracting_Inhabitance_Implication_sat =
          Inhabitance_Implication_\<A>EIF_Sat [\<phi>reason %extract_pure_sat]
          Inhabitance_Implication_\<A>ESC_Sat [\<phi>reason %extract_pure_sat]
bundle extracting_Sufficient_Inhabitance_sat =
          Sufficient_Inhabitance_\<A>EIF_Sat [\<phi>reason %extract_pure_sat]
          Sufficient_Inhabitance_\<A>ESC_Sat [\<phi>reason %extract_pure_sat]
bundle extracting_Inhabitance_sat begin
  unbundle extracting_Inhabitance_Implication_sat extracting_Sufficient_Inhabitance_sat
end

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. ((x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> D x) \<longrightarrow> P x @action \<A>EIF)
\<Longrightarrow> Abstract_Domain T D \<longrightarrow> (All P) @action \<A>EIF \<close>
  unfolding Abstract_Domain_def Action_Tag_def
  by blast

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. P x \<longrightarrow> ((x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> D x) @action \<A>ESC)
\<Longrightarrow> All P \<longrightarrow> Abstract_Domain T D @action \<A>ESC \<close>
  unfolding Abstract_Domain_def Action_Tag_def
  by blast

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. (D x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> (x \<Ztypecolon> T)) \<longrightarrow> P x @action \<A>EIF)
\<Longrightarrow> Abstract_Domain\<^sub>L T D \<longrightarrow> (All P) @action \<A>EIF \<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def
  by blast

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. P x \<longrightarrow> (D x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> (x \<Ztypecolon> T)) @action \<A>ESC)
\<Longrightarrow> All P \<longrightarrow> Abstract_Domain\<^sub>L T D @action \<A>ESC \<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def
  by blast


paragraph \<open>Basic Rules\<close>

lemma [\<phi>reason default %extract_pure_phity]:
  \<open> Abstract_Domain T D
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> D x\<close>
  unfolding Abstract_Domain_def Action_Tag_def
  by blast

lemma [\<phi>reason default %extract_pure_phity]:
  \<open> Abstract_Domain\<^sub>L T D
\<Longrightarrow> D x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> T\<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def
  by blast

paragraph \<open>Fallback\<close>

lemma [\<phi>reason default %abstract_domain_fallback]:
  \<open> Abstract_Domain T (\<lambda>x. Inhabited (x \<Ztypecolon> T)) \<close>
  unfolding Abstract_Domain_def Action_Tag_def
  by simp

lemma [\<phi>reason default %abstract_domain_fallback]:
  \<open> Abstract_Domain\<^sub>L T (\<lambda>x. Inhabited (x \<Ztypecolon> T)) \<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def
  by simp

paragraph \<open>Configuration\<close>

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

setup \<open> PLPR_Template_Properties.add_property_kinds [
  \<^pattern_prop>\<open>Abstract_Domain _ _\<close>, \<^pattern_prop>\<open>Abstract_Domain\<^sub>L _ _\<close>
]\<close>

paragraph \<open>Template Instantiation\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma Inhabited_rewr_template[\<phi>reason_template name T.inh_rewr [simp]]:
  \<open> Abstract_Domain T D @action \<A>_template_reason
\<Longrightarrow> Abstract_Domain\<^sub>L T D' @action \<A>_template_reason
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>x. D' x = D x) @action \<A>_template_reason
\<Longrightarrow> Inhabited (x \<Ztypecolon> T) \<equiv> D x \<close>
  unfolding Action_Tag_def Abstract_Domain_def Abstract_Domain\<^sub>L_def Premise_def
  by (clarsimp, smt (verit, best))


(*
(*depreciate!*)
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
  if Config.get ctxt Phi_Reasoners.is_generating_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Inhabited\<^sub>M\<^sub>C_fallback_True} RS sequent), Seq.empty)
)\<close>

\<phi>reasoner_ML Suf_Inhabited_fallback\<^sub>M\<^sub>C default 2 (\<open>_ \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>\<^sub>M\<^sub>C _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.is_generating_extraction_rule
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
*)

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
  \<comment> \<open>Implementation notes: It is safe to unfold Transformation but unsafe to unfold Satisfaction.
      Transformation is always based on Satisfaction but in future when we upgrade our logic onto
      impredicativeness, the definition of Satisfaction will be changed.
      Satisfaction is the bottom abstraction layer.\<close>

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

text \<open>The name of transformation is good in sense of corresponding to categorical natural transformation.
  If we consider the state transition of a program as a category \<open>\<C>\<close>, two \<phi>-types \<open>T\<close> and \<open>U\<close> form
  functors over \<open>\<C>\<close>, and the transformation between \<open>T\<close> and \<open>U\<close> is the natural transformation between
  the two functors. \<close>

text \<open>TODO: move me
Our method simplifies program verification by lifting it onto an abstract domain.
However, it is hard to universally define what are abstract and what are not.
In a transformation \<open>x \<Ztypecolon> T \<longrightarrow> f(x) \<Ztypecolon> U\<close>, the abstract map \<open>f\<close> can have various expressions and
may fall back to concrete level such as \<open>f(x) = @y(x \<Ztypecolon> T \<longrightarrow> y \<Ztypecolon> U)\<close> (\<open>@\<close> is Hilbert choice operator)
which is always a trivial solution of \<open>f\<close>.


The criterion about what expression of \<open>f\<close> is considered abstract can be given by user.
The abstract maps (\<open>f\<close>) occurring in their annotations or given properties are assumed abstract.
In addition, if the abstract objects \<open>x\<close> are defined algebraically using Bounded Natural Functor,
the implied operators including mapper, relator, predicator, etc. are also considered abstract.
The range is unfixed and may extended if reasonable.

When we say we lift the verification onto an abstract domain, precisely we mean the proof obligation
extracted by our reasoning is a boolean assertion consisting of only the abstract operators as above
plus boolean connectives and other basic primitives like projections of product type.
It basically means the reasoning is made by composition of the rules giving abstraction, and the
extracted proof obligation is a composition of the abstract operators given in the rules.
\<close>


subsubsection \<open>Rules\<close>

lemma \<phi>Type_eqI_Tr:
  \<open> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U)
\<Longrightarrow> (\<And>x. x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T)
\<Longrightarrow> T = U\<close>
  unfolding \<phi>Type_def Transformation_def Satisfaction_def
  by auto

lemma \<phi>Type_eqI_BI:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (x \<Ztypecolon> U))
\<Longrightarrow> T = U \<close>
  unfolding \<phi>Type_def fun_eq_iff
  by blast

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

lemma BI_eq_ToA:
  \<open> P = Q \<longleftrightarrow> (P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Q) \<and> (Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> P) \<close>
  unfolding BI_eq_iff Transformation_def
  by blast

lemma BI_sub_transformation:
  \<open> S \<le> S' \<longleftrightarrow> (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S') \<close>
  unfolding Transformation_def Satisfaction_def subset_iff
  by blast

lemma BI_sub_iff:
  \<open> S \<le> S' \<longleftrightarrow> (\<forall>u. u \<Turnstile> S \<longrightarrow> u \<Turnstile> S') \<close>
  unfolding Satisfaction_def subset_iff ..

lemma transformation_protector:
  \<open>A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<equiv> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P\<close> .

subsubsection \<open>Basic Transformation Form\<close>

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

subsubsection \<open>Separation Extraction - Transformations with Remainders and Subsequent Targets\<close>

text \<open>Upon above, we present in addition two extension forms providing partial transformations
  where a part of the source object may transform to only a part of the target object, leaving some
  remainder of the source and some unsolved target part for later reasoning.

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

abbreviation ALWAYS_REMAINS :: \<open> 'a::sep_magma BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<close> (infix "\<r>\<e>\<m>\<a>\<i>\<n>\<s>" 13)
  where \<open>(X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R) \<equiv> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R\<close>

definition \<phi>Prod :: " ('concrete::sep_magma, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b). B b * A a)"

definition Cond_\<phi>Prod :: \<open> ('v,'x) \<phi> \<Rightarrow> bool \<Rightarrow> ('v,'y) \<phi> \<Rightarrow> ('v::sep_magma,'x \<times> 'y) \<phi> \<close> ("_ \<^emph>[_] _" [71,40,70] 70)
    \<comment> \<open>\<phi>Type embedding of conditional remainder\<close>
  where \<open>(T \<^emph>[C] U) \<equiv> if C then T \<^emph> U else (\<lambda>x. fst x \<Ztypecolon> T)\<close>

lemma \<phi>Prod_expn[\<phi>expns, simp]:
  "concrete \<Turnstile> (x \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>cb ca. concrete = cb * ca \<and> cb \<Turnstile> (snd x \<Ztypecolon> B) \<and> ca \<Turnstile> (fst x \<Ztypecolon> A) \<and> cb ## ca)"
  unfolding \<phi>Prod_def \<phi>Type_def by (cases x; simp)

lemma Cond_\<phi>Prod_expn'[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> T \<^emph>[C] U) = (if C then p \<Turnstile> (x \<Ztypecolon> T \<^emph> U) else p \<Turnstile> (fst x \<Ztypecolon> T)) \<close>
  unfolding Cond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

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

  and \<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> (511) (*TODO: Auto_Transform_Hint*)
  and \<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> (511) (*TODO: Auto_Transform_Hint*)
  and \<open>?x \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?x \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> (510)
]]

lemma REMAINS_expn[\<phi>expns]:
  \<open> p \<Turnstile> (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<longleftrightarrow> (if C then p \<Turnstile> R * A else p \<Turnstile> A) \<close>
  unfolding REMAINS_def
  by simp

subsubsection \<open>Allocation of Priorities\<close>

\<phi>reasoner_group
  ToA_all         = (100, [0, 4999]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                    \<open>Rules of transformation\<close>
  ToA_bottom      = (0, [0, 13]) in ToA_all
                    \<open>System transformation rules, of the lowest priority\<close>
  ToA             = (100, [14, 4999]) in ToA_all > ToA_bottom
                    \<open>User rules for transformation\<close>
  ToA_bk          = (100, [14, 999]) in ToA
                    \<open>Backtracking rules\<close>
  ToA_cut         = (1000, [1000, 1399]) in ToA
                    \<open>Deterministic transformation rules without backtracking, meaning the reasoning
                     on the specified cases is definite and no branching.\<close>
  ToA_splitting_target = (1500, [1500,1501]) > ToA_cut in ToA
                    \<open>split the separation sequent in the target part and reason the tranformation for
                     each separated item one by one.\<close>
  ToA_splitting     = (1600, [1550,1699]) > ToA_splitting_target in ToA
                    \<open>Transformation rules splitting the reasoning goal into more subgoals\<close>
  ToA_assertion_cut = (1700, [1700,1899]) > ToA_splitting in ToA
                    \<open>Deterministic transformation rules between unsplitted assertions.\<close>
  ToA_normalizing = (2000, [1950, 2399]) > ToA_assertion_cut in ToA
                    \<open>Rules normalizing the transformation problem. A normalization rule should neither
                     branch nor yield new subgoal, i.e., always from onetransformation to another
                     transformaiton. If it branches, see %ToA_branches; if yields new assertions,
                     see %ToA_assertion_cut\<close>
  ToA_fixes_quant = (2400, [2400, 2409]) > ToA_normalizing in ToA
                    \<open>Transformation rules fixing quantified variables.\<close>
  ToA_red         = (2500, [2500, 2549]) > ToA_fixes_quant in ToA
                    \<open>Transformation rules reducing literal or trivial cases.\<close>
  ToA_success     = (3000, [2960, 3499])
                    \<open>Transformation rules that are shortcuts leading to success on special cases\<close>
  ToA_assigning_var = (4100, [4100, 4110]) in ToA
                    \<open>Tranformation rules assigning variable targets or sources, of the highest priority
                     as occurrences of schematic variables are usually not considered in the subsequent
                     normal process of the reasoning, and may cause unexpected exception in them.\<close>
  ToA_refl        = (4000, [3990, 4019]) in ToA
                    \<open>Reflexive tranformation rules\<close>
  ToA_splitting_source = (50, [50,50]) for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> < ToA_cut in ToA
                    \<open>split the separation sequent in the source part and reason the tranformation for
                     each separated item one by one.\<close>
  ToA_weak        = (20, [20,24]) for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA < default
                    \<open>Weak transformation rules giving some reasoning support temporarily and expecting to be orverride\<close>
  ToA_derived     = (50, [25,79]) for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA < default and > ToA_weak
                    \<open>Automatically derived transformations. Many substructures are contained in this large range.\<close>
  ToA_derived_red = (150, [130,170]) for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> > ToA_derived > default in ToA
                    \<open>Automatically derived transformation reductions.\<close>
  ToA_weak_red    = (120, [120,129]) for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> < ToA_derived_red in ToA
                    \<open>Weak reduction rules giving some reasoning support temporarily and expecting to be orverride\<close>


paragraph \<open>Bottom Groups\<close>

\<phi>reasoner_group
  ToA_falling_latice = (1, [0,4]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA_bottom
                    \<open>Fallbacks of transformation rules\<close>
  ToA_unified_refl = (5, [5,6]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA_bottom and > ToA_falling_latice
                     \<open>Reflexive tranformation rules with unification, of a low priority because
                      unification is aggresive.\<close>
  ToA_varify_target_object = (7, [7,7]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA_bottom and > ToA_unified_refl
                    \<open>Varifies the fixed target object, using Object_Equiv\<close>
  ToA_inst_qunat  = (8, [8,8]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA_bottom and > ToA_varify_target_object
                    \<open>Transformation rules instantiating quantified variables. It is unsafe unless
                     all fixable variables are fixed. If any variable is fixed later than the instantiation,
                     the instantiated schematic variable cannot caputure the later fixed variable.\<close>
  ToA_branches    = (10, [9,13]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA_bottom and > ToA_inst_qunat
                    \<open>Branching transformation rules.\<close>


paragraph \<open>Fallback\<close>

text \<open>There are two trivial solutions for such problem.

  On commutative algebra, a transformation can do nothing but simply return the source to the remainder
  and demand subsequent transformation to the target. Such transformation is of the lowest priority
  serving as a fallback of the ordinary reasoning.

  \<open> x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> U \<^emph>[True] T \<close>

  Another trivial solution is on unital algebras, where a transformation can assign the target object
  to the identity element of the type so the source term directly go to the remainder.

  \<open> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (one, fst x) \<Ztypecolon> U \<^emph>[True] T \<close> where \<open>one \<Ztypecolon> U \<equiv> emp\<close>

  This is the fallback rule for unital algebras that are non-commutative, and in this case when
  all transformations from T to U fail, assigning \<open>U\<close> to identity element is the only available search
  branch so the fallback is safe. For commutative algebra, the previous fallback is applied.
  When \<open>U\<close> is kept swapping and all source terms are passed, the still remaining \<open>U\<close> is assigned
  with the identity element, so the case of \<open>one \<Ztypecolon> U \<equiv> emp\<close> is still covered.



(*Implementation note:

  By default, such rule is not activated as it really does nothing, and clients have a way
  to know if the reasoning fails. However, if such fallback is expected, one can use reasoning goal
  \<open> Try Cs (x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R) \<close>
  in which boolean condition \<open>Cs\<close> returns whether the reasoning really ever made some changes.*)
 \<close>


text \<open>Rules are given in \<section>\<open>Reasoning/Basic Transformation Rules/Fallback\<close>\<close>


subsubsection \<open>Extracting Pure Facts Implies Inside\<close>

text \<open>This is used in \<phi>-derivers, particularly in induction when\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> P\<^sub>A \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> P\<^sub>B
\<Longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) \<longrightarrow> (P\<^sub>A \<longrightarrow> P\<^sub>B \<and> P) @action \<A>EIF \<close>
  unfolding Action_Tag_def Inhabited_def Transformation_def
  by clarsimp

ML \<open>
fun extracting_elim_or_intro_ToA is_intro ctxt sequent =
  let val target = fst (HOLogic.dest_imp (PLPR_Syntax.dest_action_of \<^const_name>\<open>\<A>EIF\<close>
                          (HOLogic.dest_Trueprop (Thm.major_prem_of sequent))))
      fun get_concl (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = get_concl X
        | get_concl X = X
      val concl = get_concl target
      fun get_V (A, B) = if is_intro then A else B
      val (A, B, Var p) = Phi_Syntax.dest_transformation (fst (HOLogic.dest_imp target))
      val Var v = get_V (A, B)

      fun parse_P (Var p) = p 
        | parse_P (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ Var p $ _) = p

   in case try Phi_Syntax.dest_transformation concl
   of SOME (A', B', P') => if get_V (A', B') = Var v andalso p = parse_P P'
      then SOME ((ctxt, @{lemma' \<open> S \<longrightarrow> C @action \<A>EIF
                              \<Longrightarrow> ((A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A) \<longrightarrow> S) \<longrightarrow> C @action \<A>EIF\<close>
                             by simp}
                          RS sequent), Seq.empty)
      else NONE
  end
\<close>

\<phi>reasoner_ML Transformation\<^sub>I_\<A>EIF' %extract_pure+10 (\<open>((?var \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> ?var_P) \<longrightarrow> _) \<longrightarrow> _ @action \<A>EIF\<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () => extracting_elim_or_intro_ToA true ctxt sequent)
\<close>

\<phi>reasoner_ML Transformation\<^sub>E_\<A>EIF' %extract_pure+10 (\<open>((_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var \<w>\<i>\<t>\<h> ?var_P) \<longrightarrow> _) \<longrightarrow> _ @action \<A>EIF\<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () => extracting_elim_or_intro_ToA false ctxt sequent)
\<close>


(*TODO*)
lemma ToA_EIF_sat:
  \<open> (\<And>v. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> vA v : v \<Turnstile> A)
\<Longrightarrow> (\<And>v. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> vB v : v \<Turnstile> B)
\<Longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) \<longrightarrow> (\<forall>v. vA v \<longrightarrow> vB v \<and> P) @action \<A>EIF \<close>
  unfolding Action_Tag_def Inhabited_def Transformation_def Simplify_def
  by clarsimp

lemma ToA_ESC_sat:
  \<open> (\<And>v. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> vA v : v \<Turnstile> A)
\<Longrightarrow> (\<And>v. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> vB v : v \<Turnstile> B)
\<Longrightarrow> (\<forall>v. vA v \<longrightarrow> vB v \<and> P) \<longrightarrow>   (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) @action \<A>ESC \<close>
  unfolding Action_Tag_def Inhabited_def Transformation_def Simplify_def
  by clarsimp

bundle ToA_extract_pure_sat = ToA_EIF_sat[\<phi>reason %extract_pure_sat]
                              ToA_ESC_sat[\<phi>reason %extract_pure_sat]


subsubsection \<open>Reasoning Configure\<close>

ML_file \<open>library/tools/helper_reasoners.ML\<close>

paragraph \<open>Auxiliary Tools\<close>

definition May_Assign :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>May_Assign _ _ \<equiv> True\<close>

\<phi>reasoner_group may_assign__all = (100, [1,2000]) for \<open>May_Assign var val\<close> \<open>\<close>
  and may_assign_success = (2000, [2000,2000]) in may_assign__all \<open>\<close>
  and may_assign_red = (1500, [1500, 1530]) in may_assign__all \<open>\<close>
  and may_assign_fallback = (1, [1,1]) in may_assign__all \<open>\<close>

lemma [\<phi>reason %may_assign_success for \<open>May_Assign _ _\<close>]:
  \<open> May_Assign z z \<close>
  unfolding May_Assign_def ..

lemma [\<phi>reason %may_assign_fallback]:
  \<open>May_Assign x y \<close>
  unfolding May_Assign_def ..

lemma [\<phi>reason %may_assign_red]:
  \<open> May_Assign y z
\<Longrightarrow> May_Assign (snd (x,y)) z \<close>
  unfolding May_Assign_def ..



paragraph \<open>Inhabitance Reasoning - Part II\<close>

(*TODO: move me!!*)

lemma [\<phi>reason 1000]:
  \<open> Generate_Implication_Reasoning (Inhabited X \<longrightarrow> Y) (Inhabited X) Y \<close>
  unfolding Generate_Implication_Reasoning_def
  ..

lemma [\<phi>reason 1100]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> Generate_Implication_Reasoning (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) (Inhabited X) P \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Inhabited_def Action_Tag_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q
\<Longrightarrow> Generate_Implication_Reasoning (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) (Inhabited X) (Q \<and> P) \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Inhabited_def Action_Tag_def
  by blast

declare [[\<phi>trace_reasoning = 1]]


subsection \<open>Top\<close>

notation top ("\<top>")

subsubsection \<open>Rewrites\<close>

lemma Top_Inhabited[simp]:
  \<open>Inhabited \<top> \<longleftrightarrow> True\<close>
  unfolding Inhabited_def
  by clarsimp

subsubsection \<open>Transformation Rules\<close>

declare [[\<phi>trace_reasoning = 1]]

\<phi>reasoner_group ToA_top = (%ToA_success, [%ToA_success-1, %ToA_success+1]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> \<w>\<i>\<t>\<h> _\<close>
                          \<open>Transformation rules handling \<top>\<close>

text \<open>The target part is assumed having no schematic variable, so it is safe to do such shortcuts
      comparing with the bottom-in-source.\<close>

lemma [\<phi>reason %ToA_top]:
  \<open>Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top>\<close>
  unfolding Transformation_def by blast

lemma [\<phi>reason %ToA_top]:
  \<open>Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top>\<close>
  unfolding Transformation_def
  by simp

lemma [\<phi>reason %ToA_top]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B * \<top>
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B * \<top> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top>\<close>
  by simp

lemma [\<phi>reason %ToA_top-1 for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _\<close>]:
      \<comment> \<open>the case when the remainder is forced\<close>
  \<open> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top>
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R\<close>
  by simp

lemma [\<phi>reason %ToA_top-1 for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<top> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _\<close>]:
      \<comment> \<open>the case when the remainder is forced. Non-semigroup algebra is covered by what??? TODO!\<close>
  \<open> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * C * \<top>
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C * \<top> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R\<close>
  for A :: \<open>'a :: sep_semigroup BI\<close>
  by (simp add: mult.assoc)

(*The following procedure only supports commutative semigroup*)
 
lemma [\<phi>reason %ToA_top+1 if \<open>fn (ctxt,sequent) =>
          case Thm.major_prem_of sequent
            of _ (*Trueprop*) $ (_ (*transformation*) $ _ $ (_ (*times*) $ R $ _) $ _)
               => let fun chk (Const(\<^const_name>\<open>times\<close>, _) $ X $ Const(\<^const_name>\<open>top\<close>, _)) = chk X
                        | chk (Const(\<^const_name>\<open>top\<close>, _)) = false
                        | chk _ = true
                   in chk R
                  end\<close>]:
  \<open> Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> * R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  for Any :: \<open>'a::sep_ab_semigroup BI\<close>
  by (simp add: mult.commute)

(*when we reach here, it means R all consists of \<top>, so that we can eliminate them one-by-one,
  until the last one which can be done by \<open>Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top>\<close> directly.
  Again we assume and only consider commutative semigroup*)

lemma [\<phi>reason %ToA_top]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  for A :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding Transformation_def
  by clarsimp blast

lemma [\<phi>reason %ToA_top-1]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  for A :: \<open>'a::sep_algebra BI\<close>
  unfolding Transformation_def
  by clarsimp (metis mult_1_class.mult_1_right sep_magma_1_left)

lemma [\<phi>reason %fail]:
  \<open> FAIL TEXT(\<open>Sorry, currently we do not support solving \<open>R * \<top>\<close> problems on non-monoidal and non-commutative group.\<close>)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def FAIL_def
  by blast



subsection \<open>Bottom\<close>

text \<open>Despite of semantically \<open>0 = \<bottom>\<close> where syntactically \<open>\<bottom> \<equiv> {}\<close>, but there is not syntactically
  \<open>0 \<equiv> {}\<close>. We prefer to use \<open>0\<close> instead of the more usual \<open>\<bottom>\<close> for the sake of forming
  a semiring together with \<open>1 \<equiv> emp\<close>, \<open>*\<close>, \<open>+ \<equiv> \<or>\<^sub>B\<^sub>I\<close>, to leverage the existing automation of semiring.\<close>

abbreviation Bottom ("\<bottom>\<^sub>B\<^sub>I") where \<open>Bottom \<equiv> (0::'a::sep_magma BI)\<close>
abbreviation Bottom_abs ("\<bottom>\<^sub>\<lambda>") where \<open>Bottom_abs \<equiv> (0 :: 'b \<Rightarrow> 'a::sep_magma BI)\<close>

lemma bot_eq_BI_bot:
  \<open>bot = \<bottom>\<^sub>B\<^sub>I\<close>
  unfolding zero_set_def ..

lemma zero_implies_any[simp]:
  \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close>
  unfolding Transformation_def zero_set_def Satisfaction_def by simp

subsubsection \<open>Rewrites\<close>

lemma Bot_Inhabited[simp]:
  \<open> Inhabited 0 \<longleftrightarrow> False \<close>
  unfolding Inhabited_def
  by clarsimp

subsubsection \<open>Transformation Rules\<close>

\<phi>reasoner_group ToA_bot = (%ToA_cut+5, [%ToA_cut, %ToA_cut+10]) for \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
   \<open>Transformation rules when the source assertion is 0.
    The rule is not of a highest priority because the target may contain schematic variables,
    and the usual reasoning procedure is still required to unfold the target connective-by-connective
    to ensure every variables inside is instantiated.\<close>

declare zero_implies_any[\<phi>reason %ToA_cut for \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                                              \<open>?var \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]

lemma [\<phi>reason %ToA_bot for \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _ \<close>
                            \<open>?var \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _ \<close> ]:
  \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Any] 0\<close>
  using zero_implies_any .

paragraph \<open>Reductions\<close>

lemma [\<phi>reason %ToA_red for \<open>_ * 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                            \<open>_ * ?var \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X
\<Longrightarrow> R * 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>0 * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                            \<open>?var * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X
\<Longrightarrow> 0 * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ + 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                            \<open>_ + ?var \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y + 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>0 + _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                            \<open>?var + _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> 0 + Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ + 0 \<w>\<i>\<t>\<h> _\<close>
                            \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ + ?var \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X + 0 \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 + _ \<w>\<i>\<t>\<h> _\<close>
                            \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var + _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 + X \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ + 0 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                            \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ + ?var \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X + 0 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 + _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                            \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var + _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 + X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> 0 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> R * 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * 0 x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 0 * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> 0 x * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp


subsection \<open>Unit\<close>

subsubsection \<open>Properties\<close>

lemma [\<phi>reason %extract_pure]:
  \<open>1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> True\<close>
  unfolding Action_Tag_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> True \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> 1 \<close>
  unfolding Action_Tag_def Inhabited_def
  by simp

lemma Emp_Inhabited[simp]:
  \<open> Inhabited 1 \<longleftrightarrow> True \<close>
  unfolding Inhabited_def
  by clarsimp

subsubsection \<open>Transformation Rules\<close>

lemma [\<phi>reason %ToA_success]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

lemma [\<phi>reason %ToA_red]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * 1 \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right .

lemma [\<phi>reason %ToA_red]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right .

lemma [\<phi>reason %ToA_red]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right .


subsection \<open>Additive Disjunction\<close>

text \<open>Is the \<^term>\<open>(+) :: 'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> directly\<close>

subsubsection \<open>Basic Rules\<close>

lemma Disjunction_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (A + B) \<longleftrightarrow> p \<Turnstile> A \<or> p \<Turnstile> B\<close>
  unfolding Satisfaction_def by simp

lemma Add_Disj_Inhabited[simp]:
  \<open> Inhabited (A + B) \<longleftrightarrow> Inhabited A \<or> Inhabited B \<close>
  unfolding Inhabited_def
  by clarsimp blast

lemma [\<phi>reason %cutting]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> B
\<Longrightarrow> X + Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<or> B\<close>
  unfolding Action_Tag_def Inhabited_def
  by simp blast

lemma [\<phi>reason %cutting]:
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


subsubsection \<open>Transformation Rules\<close>

paragraph \<open>In Source\<close>

lemma [\<phi>reason %ToA_splitting]:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A + B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (simp add: Transformation_def)

lemma [\<phi>reason %ToA_splitting]:
  \<open> R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1
\<Longrightarrow> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P2
\<Longrightarrow> R * (A + B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (simp add: Transformation_def distrib_left) blast

lemma [\<phi>reason %ToA_splitting+10]:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RB \<w>\<i>\<t>\<h> P1
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A + B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA + RB \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (cases C; simp add: Transformation_def; meson)

lemma [\<phi>reason %ToA_splitting+10]:
  \<open> R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RB \<w>\<i>\<t>\<h> P1
\<Longrightarrow> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA \<w>\<i>\<t>\<h> P2
\<Longrightarrow> R * (A + B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA + RB \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (cases C; simp add: Transformation_def; blast)


paragraph \<open>In Target\<close>

lemma ToA_disj_target_A:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<w>\<i>\<t>\<h> P\<close>
  unfolding plus_set_def
  by (metis implies_union(1) plus_set_def)

lemma ToA_disj_target_B:
  \<open>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<w>\<i>\<t>\<h> P\<close>
  by (simp add: Transformation_def)

declare [[\<phi>reason ! %ToA_branches ToA_disj_target_A ToA_disj_target_B for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A + ?B \<w>\<i>\<t>\<h> ?P\<close>]]

hide_fact ToA_disj_target_A ToA_disj_target_B

lemma ToA_disj_target_A':
  \<open>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def
  by (cases C; simp add: distrib_left; blast)

lemma ToA_disj_target_B':
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def
  by (cases C; simp add: distrib_left; blast)

declare [[\<phi>reason ! %ToA_branches ToA_disj_target_A' ToA_disj_target_B'
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A + ?B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]]

hide_fact ToA_disj_target_A' ToA_disj_target_B'



subsection \<open>Existential Quantification\<close>

lemma ExSet_inhabited_E[elim!]:
  \<open>Inhabited (ExSet S) \<Longrightarrow> (\<And>x. Inhabited (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by simp blast

lemma [\<phi>reason %cutting]:
  \<open> (\<And>x. S x \<i>\<m>\<p>\<l>\<i>\<e>\<s> C x)
\<Longrightarrow> ExSet S \<i>\<m>\<p>\<l>\<i>\<e>\<s> Ex C \<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp; blast)

lemma [\<phi>reason %cutting]:
  \<open> (\<And>x. C x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> S x)
\<Longrightarrow> Ex C \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> ExSet S \<close>
  unfolding Inhabited_def Action_Tag_def
  by (simp; blast)

lemma ExSet_Inhabited[simp]:
  \<open> Inhabited (ExSet S) \<longleftrightarrow> (\<exists>x. Inhabited (S x)) \<close>
  unfolding Inhabited_def
  by clarsimp blast


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
  \<open>(ExSet X \<s>\<u>\<b>\<j> PP) = (ExSet (\<lambda>c. X c \<s>\<u>\<b>\<j> PP))\<close>
  \<open>(F' y \<s>\<u>\<b>\<j> y. embedded_func f' P' x' y) = (F' (f' x') \<s>\<u>\<b>\<j> P' x')\<close>
(*  \<open>(\<exists>* x. x = t \<and> P x) = P t\<close>
"\<And>P. (\<exists>x. x = t \<and> P x) = P t"
    "\<And>P. (\<exists>x. t = x \<and> P x) = P t"*)
  unfolding BI_eq_iff embedded_func_def
  by simp_all

lemma ExSet_simps_ex[simp, \<phi>programming_base_simps]:
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> x = y) = (F y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> y = x) = (F y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> x = y \<and> P x) = (F y \<s>\<u>\<b>\<j> P y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> y = x \<and> P x) = (F y \<s>\<u>\<b>\<j> P y)\<close>
  unfolding BI_eq_iff
  by simp_all

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


paragraph \<open>With Additive Disjunction\<close>

lemma ExSet_addisj:
  \<open>A + (\<exists>*c. B c) \<equiv> \<exists>*c. A + B c\<close>
  \<open>(\<exists>*c. B c) + A \<equiv> \<exists>*c. B c + A\<close>
  unfolding atomize_eq BI_eq_iff
  by simp+


subsubsection \<open>Transformation Rules\<close>

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


subsubsection \<open>ToA Reasoning\<close>

lemma [\<phi>reason %ToA_fixes_quant]:
  "(\<And>x.  T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P x)
\<Longrightarrow> ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> Ex P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason %ToA_fixes_quant+5]:
  "(\<And>x.  T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R x \<w>\<i>\<t>\<h> P x)
\<Longrightarrow> ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] ExSet R \<w>\<i>\<t>\<h> Ex P"
  unfolding Transformation_def REMAINS_def by (cases C; simp; blast)

lemma [\<phi>reason %ToA_fixes_quant]:
  "(\<And>x.  W * T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P x)
\<Longrightarrow> W * ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> Ex P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason %ToA_fixes_quant+5]:
  "(\<And>x.  W * T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R x \<w>\<i>\<t>\<h> P x)
\<Longrightarrow> W * ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] ExSet R \<w>\<i>\<t>\<h> Ex P"
  unfolding Transformation_def by (cases C; simp; fastforce)

text \<open>Continued in \ref{supp-ex-conj}\<close>


subsection \<open>Additive Conjunction\<close>

definition Additive_Conj :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> (infix "\<and>\<^sub>B\<^sub>I" 35)
  where \<open>Additive_Conj = (\<inter>)\<close>

subsubsection \<open>Basic Rules\<close>

lemma Additive_Conj_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (A \<and>\<^sub>B\<^sub>I B) \<longleftrightarrow> p \<Turnstile> A \<and> p \<Turnstile> B\<close>
  unfolding Satisfaction_def Additive_Conj_def by simp

lemma additive_conj_inhabited_E[elim!]:
  \<open>Inhabited (A \<and>\<^sub>B\<^sub>I B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by simp blast

lemma [\<phi>reason %cutting]:
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


subsubsection \<open>Simplification\<close>

paragraph \<open>With ExSet\<close>

lemma ExSet_adconj:
  \<open>A \<and>\<^sub>B\<^sub>I (\<exists>*c. B c) \<equiv> \<exists>*c. A \<and>\<^sub>B\<^sub>I B c\<close>
  \<open>(\<exists>*c. B c) \<and>\<^sub>B\<^sub>I A \<equiv> \<exists>*c. B c \<and>\<^sub>B\<^sub>I A\<close>
  unfolding atomize_eq BI_eq_iff
  by simp+


subsubsection \<open>Transformation Rules\<close>

text \<open>Non-pure Additive Conjunction (excludes those are used in pure propositions), is rarely used under our
  refinement interpretation of BI assertions, because we can hardly imagine when and why an object
  has to be specified by two abstractions that cannot transform to each other (if they can,
  it is enough to use any one of them with a strong constraint over the abstraction, and transform it
  to the other when needed). We believe those abstractions if exist are specific enough to be preferably
  expressed by a specific \<phi>-type equipped with ad-hoc reasoning rules.

  To support additive conjunction, it brings enormous branches in the reasoning so affects the
  reasoning performance. Before applying the rules introduced previously, we can add the following
  rules which are also attempted subsequently in order and applied whenever possible.
  \<open>X \<longrightarrow> A \<Longrightarrow> X \<longrightarrow> B \<Longrightarrow> X \<longrightarrow> A \<and> B\<close> generates two subgoals.
  \<open>(A \<longrightarrow> Y) \<or> (B \<longrightarrow> Y) \<Longrightarrow> A \<and> B \<longrightarrow> Y\<close> branches the reasoning. Specially, when \<open>Y \<equiv> \<exists>x. P x\<close> is an
  existential quantification containing non-pure additive conjunction (e.g. \<open>P x \<equiv> C x \<and> D x\<close>),
  the priority of eliminating \<open>\<and>\<close> or instantiating \<open>\<exists>\<close> is significant.
  We attempt the both priorities by a search branch.
(*  If we instantiate first, the instantiation is forced to be identical in the two branches.
  If we eliminate \<open>\<and>\<close> first, the \<open>P\<close> can be too strong *)
  This rule is irreversible and we recall our hypothesis that \<phi>-types between the conjunction are
  considered disjoint, i.e., we only consider \<open>(x \<Ztypecolon> T) \<and> (y \<Ztypecolon> U) \<longrightarrow> Y\<close> when
  either \<open>x \<Ztypecolon> T \<longrightarrow> Y\<close> or \<open>y \<Ztypecolon> U \<longrightarrow> Y\<close>.
\<close>

lemma [\<phi>reason %ToA_splitting]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P1
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P2
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<and>\<^sub>B\<^sub>I B \<w>\<i>\<t>\<h> P1 \<and> P2 \<close>
  unfolding Transformation_def
  by simp

lemma NToA_conj_src_A:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<and>\<^sub>B\<^sub>I B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def
  by simp blast

lemma NToA_conj_src_B:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<and>\<^sub>B\<^sub>I B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def
  by simp blast

text \<open>Continued in \ref{supp-ex-conj}\<close>


subsection \<open>Subjection: Conjunction to a Pure Fact\<close>

text \<open>This is the only widely used additive conjunction under the interpretation of the \<phi> data refinement\<close>

subsubsection \<open>Basic Rules\<close>

lemma Subjection_inhabited_E[elim!]:
  \<open>Inhabited (S \<s>\<u>\<b>\<j> P) \<Longrightarrow> (Inhabited S \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by simp

lemma [\<phi>reason %cutting]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> C)
\<Longrightarrow> S \<s>\<u>\<b>\<j> P \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> C \<close>
  unfolding Inhabited_def Action_Tag_def Premise_def
  by simp

lemma [\<phi>reason %cutting]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> C \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> S)
\<Longrightarrow> P \<and> C \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> S \<s>\<u>\<b>\<j> P \<close>
  unfolding Inhabited_def Action_Tag_def Premise_def
  by simp 

lemma Subjection_imp_I:
  \<open> P
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> Q
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q\<close>
  unfolding Transformation_def by simp


subsubsection \<open>Simplification\<close>

lemma Subjection_cong[cong]:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<s>\<u>\<b>\<j> P) \<equiv> (S' \<s>\<u>\<b>\<j> P')\<close>
  unfolding atomize_eq BI_eq_iff by (simp, blast)

lemma Subjection_eq:
  \<open>(A \<s>\<u>\<b>\<j> P) = (A' \<s>\<u>\<b>\<j> P) \<longleftrightarrow> (P \<longrightarrow> A = A')\<close>
  unfolding BI_eq_iff
  by clarsimp blast

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

lemma Subjection_transformation_rewr:
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

subsubsection \<open>Transformation Rules\<close>

\<phi>reasoner_group ToA_subj = (%ToA_assertion_cut, [%ToA_assertion_cut, %ToA_assertion_cut+20]) for \<open>T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P\<close>
  \<open>Transformation rules handling \<open>Subjection\<close>\<close>

lemma [\<phi>reason %ToA_subj]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> Q)
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Premise_def
  by simp

lemma [\<phi>reason %ToA_red]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> True \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def by simp

lemma [\<phi>reason %ToA_subj]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> Q)
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> Q \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Premise_def
  by simp

lemma [\<phi>reason %ToA_red]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> True \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def by simp

lemma [\<phi>reason %ToA_subj+10]: (*THINK: add Q in P, is good or not?*)
  "\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<longrightarrow> (T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P )
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason %ToA_subj+20]:
  "\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<longrightarrow> (T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason %ToA_subj+10]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<longrightarrow> (W * T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P )
\<Longrightarrow> W * (T \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason %ToA_subj+20]:
  "\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<longrightarrow> (W * T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> W * (T \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast



subsection \<open>Multiplicative Conjunction\<close>

text \<open>Is the \<^term>\<open>(*) :: ('a::sep_magma) BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> directly\<close>

lemma set_mult_inhabited[elim!]:
  \<open>Inhabited (S * T) \<Longrightarrow> (Inhabited S \<Longrightarrow> Inhabited T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by (simp, blast)

lemma [\<phi>reason %cutting]:
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

lemma transformation_left_frame:
  "U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> R * U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * U \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma transformation_right_frame:
  "U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> U' * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U * R \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma transformation_bi_frame:
  " R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> L' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> L \<w>\<i>\<t>\<h> Q
\<Longrightarrow> L' * R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> L * R \<w>\<i>\<t>\<h> P \<and> Q "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast


subsection \<open>Finite Multiplicative Quantification (FMQ)\<close>

definition Mul_Quant :: \<open>('a \<Rightarrow> 'b::sep_algebra BI) \<Rightarrow> 'a set \<Rightarrow> 'b BI\<close> ("\<big_ast>")
  where \<open>Mul_Quant A S \<equiv> (prod A S \<s>\<u>\<b>\<j> finite S)\<close>

text \<open>Finite Multiplicative Quantification \<open>\<big_ast>i\<in>I. A\<^sub>i\<close> is inductively applying separation conjunction
  over a finite family \<open>{A\<^sub>i}\<close> of assertions indexed by \<open>i\<in>I\<close>, e.g., \<open>(\<big_ast>i\<in>I. A\<^sub>i) = A\<^sub>1 * A\<^sub>2 * \<dots> * A\<^sub>n\<close> for
  \<open>I = {1,2,\<dots>,n}\<close>\<close>

syntax
  "_Mul_Quant" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(2\<big_ast>(_/\<in>_)./ _)" [0, 51, 14] 14)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<big_ast>i\<in>A. b" == "CONST Mul_Quant (\<lambda>i. b) A"

syntax
  "_qMul_Quant" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<big_ast>_ | (_)./ _)" [0, 0, 14] 14)
translations
  "\<big_ast>x|P. t" => "CONST Mul_Quant (\<lambda>x. t) {x. P}"


subsubsection \<open>Rewrites\<close>

lemma sep_quant_sing[simp]:
  \<open>\<big_ast> A {i} = A i\<close>
  unfolding Mul_Quant_def
  by simp

lemma sep_quant_empty[simp]:
  \<open>\<big_ast> A {} = 1\<close>
  unfolding Mul_Quant_def
  by simp

lemma sep_quant_insert:
  \<open>i \<notin> I \<Longrightarrow> \<big_ast> A (insert i I) = \<big_ast> A I * A i\<close>
  unfolding Mul_Quant_def
  by (clarsimp simp add: Subjection_eq mult.commute)

lemma sep_quant_reindex:
  \<open> inj_on f I
\<Longrightarrow> \<big_ast>i\<in>f`I. A i \<equiv> \<big_ast>i\<in>I. A (f i)\<close>
  unfolding Mul_Quant_def BI_eq_iff atomize_eq
  by (clarsimp; rule; clarsimp simp add: finite_image_iff prod.reindex_cong)

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

lemma sep_quant_ExSet:
  \<open>(\<big_ast>i\<in>I. \<exists>*j. A i j) = (\<exists>*j. \<big_ast>i\<in>I. A i (j i))\<close>
proof -
  have t1: \<open>\<And>u. finite I \<Longrightarrow> u \<Turnstile> (\<Prod>i\<in>I. ExSet (A i)) \<longleftrightarrow> (\<exists>x. u \<Turnstile> (\<Prod>i\<in>I. A i (x i)))\<close> (is \<open>\<And>u. _ \<Longrightarrow> ?goal u\<close>)
  proof -
    fix u
    assume \<open>finite I\<close>
    show \<open>?goal u\<close>
      apply (induct arbitrary: u rule: finite_induct[OF \<open>finite I\<close>]; clarsimp)
      apply (rule; clarsimp)
      subgoal for x F xa ua v xb
        by (rule exI[where x=\<open>\<lambda>i. if i = x then xa else xb i\<close>], rule exI[where x=ua], rule exI[where x=v],
            simp, smt (verit) prod.cong)
      by blast
  qed
  show ?thesis
    unfolding BI_eq_iff Mul_Quant_def
    by (clarsimp; rule; clarsimp simp add: t1)
qed

lemma sep_quant_swap:
  \<open>\<lbrakk> finite I; finite J \<rbrakk> \<Longrightarrow>(\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) = (\<big_ast>j\<in>J. \<big_ast>i\<in>I. A i j)\<close>
  unfolding BI_eq_iff Mul_Quant_def
  by (clarsimp; metis prod.swap)

lemma sep_quant_scalar_assoc:
  \<open>(\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) = ((\<big_ast>(i,j) \<in> I \<times> J. A i j) \<s>\<u>\<b>\<j> finite I)\<close>
  unfolding BI_eq_iff Mul_Quant_def
  by (clarsimp; rule;
      clarsimp simp add: finite_prod_subjection ex_in_conv finite_cartesian_product_iff;
      cases \<open>I = {}\<close>; cases \<open>J = {}\<close>; simp add: prod.cartesian_product)

lemma sep_quant_sep:
  \<open>(\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) = (\<big_ast>i\<in>I. A i * B i)\<close>
  unfolding BI_eq_iff Mul_Quant_def
  proof (clarsimp; rule; clarify)
    fix u ua v
    assume \<open>finite I\<close>
    show \<open>ua \<Turnstile> prod A I \<Longrightarrow> v \<Turnstile> prod B I \<Longrightarrow> ua ## v \<Longrightarrow> ua * v \<Turnstile> (\<Prod>i\<in>I. A i * B i)\<close>
      by (induct arbitrary: v u ua rule: finite_induct[OF \<open>finite I\<close>] ; clarsimp ;
          smt (verit, best) sep_disj_commuteI sep_disj_multD1 sep_disj_multI1 sep_mult_assoc sep_mult_commute)
  next
    fix u
    assume \<open>finite I\<close>
    show \<open>u \<Turnstile> (\<Prod>i\<in>I. A i * B i) \<Longrightarrow> \<exists>ua v. u = ua * v \<and> ua \<Turnstile> prod A I \<and> v \<Turnstile> prod B I \<and> ua ## v\<close>
      by (induct arbitrary: u rule: finite_induct[OF \<open>finite I\<close>] ; clarsimp ;
          smt (verit) sep_disj_commuteI sep_disj_multD1 sep_disj_multI1 sep_mult_assoc sep_mult_commute)
qed

lemma sep_quant_merge_additive_disj:
  \<open>(\<big_ast>i\<in>I. A i) + (\<big_ast>i\<in>I. B i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. A i + B i)\<close>
  \<comment> \<open>but not held reversely\<close>
unfolding Transformation_def Mul_Quant_def
proof (clarsimp; rule; clarsimp)
  fix v
  assume \<open>finite I\<close>
  show \<open>v \<Turnstile> prod A I \<Longrightarrow> v \<Turnstile> (\<Prod>i\<in>I. A i + B i)\<close>
    by (induct arbitrary: v rule: finite_induct[OF \<open>finite I\<close>]; clarsimp; blast)
next
  fix v
  assume \<open>finite I\<close>
  show \<open>v \<Turnstile> prod B I \<Longrightarrow> v \<Turnstile> (\<Prod>i\<in>I. A i + B i)\<close>
    by (induct arbitrary: v rule: finite_induct[OF \<open>finite I\<close>]; clarsimp; blast)
qed

lemma sep_quant_scalar_distr:
  \<open>I \<inter> J = {} \<Longrightarrow> (\<big_ast>i\<in>I. A i) * (\<big_ast>j\<in>J. B j) = (\<big_ast>k\<in>I + J. (if k \<in> J then B k else A k))\<close> (*TODO: syntax priority!*)
  unfolding Mul_Quant_def plus_set_def Subjection_times Subjection_Subjection
  by (clarsimp simp add: Subjection_eq,
      smt (verit) disjoint_iff prod.cong prod.union_disjoint)


subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %cutting]:
  \<open> (\<And>i\<in>S. A i \<i>\<m>\<p>\<l>\<i>\<e>\<s> P i)
\<Longrightarrow> (\<big_ast>i\<in>S. A i) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (\<forall>i\<in>S. P i) \<close>
  unfolding Mul_Quant_def Action_Tag_def Inhabited_def meta_Ball_def Premise_def
  by (clarsimp; metis Satisfaction_def ex_in_conv prod_zero zero_set_iff)


subsubsection \<open>Transformation\<close>

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (\<big_ast>i\<in>{x}. A i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (\<big_ast>i\<in>{}. A i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> R * A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (\<big_ast>i\<in>{x}. A i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (\<big_ast>i\<in>{}. A i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A x \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>{x}. A i) \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>{}. A i) \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>{x}. A i) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>{}. A i) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp


paragraph \<open>Weak Normalization\<close>

text \<open>Source side is normalized by merging separations together
        \<open>(\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<longrightarrow> (\<big_ast>i\<in>I. A i * B i)\<close>
  while the target side is normalized by splitting sep-quants into small separations
        \<open>(\<big_ast>i\<in>I. A i * B i) \<longrightarrow> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i)\<close>.
  It is because our reasoning strategy is splitting the target side first and scanning the source
    side \<phi>-type-by-type for each separated individual \<open>\<phi>\<close>-type items.
  The first step works in assertion form while the second step is between \<phi>-types.
  The \<open>\<big_ast>\<close> is in assertion level, so the target side has to be split before the first step.
  Before the second step, for each individual target item \<open>(\<big_ast>i\<in>I. x \<Ztypecolon> T)\<close> we shall apply
    \<open>sep_quant_transformation\<close> to strip off the outer \<open>\<big_ast>\<close> in order to enter inside into \<phi>-type level
    so that the second step can continue.
  This \<open>sep_quant_transformation\<close> may fail and if it fails, there is no way to enter the second step
    \<^emph>\<open>in this unfinished reasoning mechanism right now\<close>.

  Later after the type embedding of \<open>\<big_ast>\<close> is completed, the reasoning of \<open>\<big_ast>\<close> will be forwarded to the
  type embedding which provides full power of competence on that level.
\<close>

lemma [\<phi>reason %ToA_weak_red]:
  \<open> (\<big_ast>i\<in>I. A i * B i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding sep_quant_sep
  by simp

lemma [\<phi>reason %ToA_weak_red]:
  \<open> R * (\<big_ast>i\<in>I. A i * B i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding sep_quant_sep[symmetric]
  by (simp add: mult.assoc)

lemma [\<phi>reason %ToA_weak_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. A i * B i) \<w>\<i>\<t>\<h> P \<close>
  unfolding sep_quant_sep
  by simp

lemma [\<phi>reason %ToA_weak_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) * R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. A i * B i) * R \<w>\<i>\<t>\<h> P \<close>
  unfolding sep_quant_sep
  by simp

lemma [\<phi>reason %ToA_weak_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. A i * B i) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding sep_quant_sep
  by simp




paragraph \<open>Transformation Functor\<close>

lemma sep_quant_transformation[\<phi>reason %ToA_cut]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J
\<Longrightarrow> (\<And>i\<in>I. A i \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B i \<w>\<i>\<t>\<h> P i)
\<Longrightarrow> (\<big_ast>i\<in>I. A i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>J. B i) \<w>\<i>\<t>\<h> (\<forall>i\<in>I. P i) \<close>
  unfolding Transformation_def Mul_Quant_def meta_Ball_def Premise_def \<r>Guard_def
  proof clarsimp
    fix v
    assume \<open>finite J\<close>
    show \<open> (\<And>x. x \<in> J \<Longrightarrow> \<forall>v. v \<Turnstile> A x \<longrightarrow> v \<Turnstile> B x \<and> P x)
        \<Longrightarrow> v \<Turnstile> prod A J \<Longrightarrow> v \<Turnstile> prod B J \<and> (\<forall>x\<in>J. P x) \<close> 
      by (induct arbitrary: v rule: finite_induct[OF \<open>finite J\<close>]; clarsimp; blast)
  qed

lemma [\<phi>reason %ToA_cut]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> I = J
\<Longrightarrow> (\<And>i\<in>J. A i \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B i \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R i \<w>\<i>\<t>\<h> P i)
\<Longrightarrow> (\<big_ast>i\<in>I. A i) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>J. B i) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] (\<big_ast>i\<in>J. R i) \<w>\<i>\<t>\<h> (\<forall>i\<in>J. P i) \<close>
  unfolding REMAINS_def Premise_def \<r>Guard_def
  by (cases C; simp add: sep_quant_sep sep_quant_transformation)


paragraph \<open>Scalar Associative\<close>

lemma [\<phi>reason %ToA_normalizing]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> finite I \<Longrightarrow> (\<big_ast>(i,j) \<in> I \<times> J. A i j) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P)
\<Longrightarrow> (\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def Subjection_transformation_rewr
  by simp

lemma [\<phi>reason %ToA_normalizing]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> finite I \<Longrightarrow> R * (\<big_ast>(i,j) \<in> I \<times> J. A i j) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P)
\<Longrightarrow> R * (\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def Subjection_transformation_rewr Subjection_times
  by simp

lemma [\<phi>reason %ToA_normalizing]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>(i,j) \<in> I \<times> J. B i j) \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> finite I
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. \<big_ast>j\<in>J. B i j) \<w>\<i>\<t>\<h> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def
  by simp

lemma [\<phi>reason %ToA_normalizing]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>(i,j) \<in> I \<times> J. B i j) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> finite I
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<big_ast>i\<in>I. \<big_ast>j\<in>J. B i j) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def
  by simp





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


subsection \<open>Supplementary Connective\<close>

subsubsection \<open>World Shift\<close> \<comment> \<open>Functional refinement in assertion-level, functional counterpart of \<open>\<Zcomp>\<close>\<close>

definition World_Shift :: \<open>('c \<Rightarrow> 'd) \<Rightarrow> 'c BI \<Rightarrow> 'd BI\<close> ("\<Psi>[_]" [10] 1000)
  where \<open>(\<Psi>[\<psi>] S) = {\<psi> u |u. u \<Turnstile> S}\<close>
  \<comment> \<open>applying a function \<open>\<psi>\<close> (usually a homomorphism) to the concrete objects (namely Kripke world)
      characterized by an assertion.\<close>

text \<open>Some thinking, what if we extend \<open>\<psi>\<close> to be a relation instead of a function? Then \<open>\<Psi>[\<psi>]\<close>
  actually becomes the assertion-level counterpart of the \<phi>-type \<open>\<Zcomp>\<close>. However, the difficulty is
  I cannot find the relational extension of closed homomorphism that gives us distributivity over
  \<open>*\<close> like \<open>\<Psi>_Multiplicative_Conj\<close>.\<close>

lemma World_Shift_expn[\<phi>expns, simp]:
  \<open>p \<Turnstile> \<Psi>[\<psi>] S \<longleftrightarrow> (\<exists>u. p = \<psi> u \<and> u \<Turnstile> S)\<close>
  unfolding World_Shift_def Satisfaction_def
  by clarsimp

lemma World_Shift_expn'[\<phi>expns, simp]:
  \<open>p \<in> \<Psi>[\<psi>] S \<longleftrightarrow> (\<exists>u. p = \<psi> u \<and> u \<Turnstile> S)\<close>
  unfolding World_Shift_def Satisfaction_def
  by clarsimp

text \<open>The motivation of such modality is it is used later in Domainoid Extraction\<close>

paragraph \<open>Rewrites \& Transformations\<close>

lemma \<Psi>_1:
  \<open> homo_one \<psi>
\<Longrightarrow> \<Psi>[\<psi>] 1 = 1 \<close>
  unfolding BI_eq_iff homo_one_def
  by simp

lemma \<Psi>_0:
  \<open> \<Psi>[\<psi>] 0 = 0 \<close>
  unfolding BI_eq_iff
  by clarsimp

lemma
  \<open> \<Psi>[\<psi>] (A \<and>\<^sub>B\<^sub>I B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (\<Psi>[\<psi>] A \<and>\<^sub>B\<^sub>I \<Psi>[\<psi>] B) \<close>
  unfolding Transformation_def
  by (clarsimp; blast)

lemma \<Psi>_Multiplicative_Conj:
  \<open> closed_homo_sep \<psi>
\<Longrightarrow> \<Psi>[\<psi>] (A * B) = \<Psi>[\<psi>] A * \<Psi>[\<psi>] B\<close>
  unfolding BI_eq_iff
  by (clarsimp simp add: closed_homo_sep_def closed_homo_sep_disj_def homo_sep_def
                         homo_sep_mult_def; rule; clarsimp; metis)

lemma \<Psi>_Mul_Quant:
  \<open> closed_homo_sep \<psi>
\<Longrightarrow> homo_one \<psi>
\<Longrightarrow> \<Psi>[\<psi>] (\<big_ast>i\<in>S. A i) = (\<big_ast>i\<in>S. \<Psi>[\<psi>] (A i)) \<close>
proof -
  assume \<open>closed_homo_sep \<psi>\<close> and \<open>homo_one \<psi>\<close>
  { assume \<open>finite S\<close>
    have \<open>\<Psi>[\<psi>] (\<Prod>i\<in>S. A i) = (\<Prod>i\<in>S. \<Psi>[\<psi>] (A i))\<close>
      by (induct rule: finite_induct[OF \<open>finite S\<close>];
          simp add: \<Psi>_1 \<open>closed_homo_sep \<psi>\<close> \<open>homo_one \<psi>\<close> \<Psi>_Multiplicative_Conj)
  }
  then show \<open>\<Psi>[\<psi>] (\<big_ast>i\<in>S. A i) = (\<big_ast>i\<in>S. \<Psi>[\<psi>] (A i))\<close>
    unfolding Mul_Quant_def
    by (smt (verit, best) Subjection_Flase Subjection_True \<Psi>_0)
qed

lemma \<Psi>_Additive_Disj:
  \<open>\<Psi>[d] (A + B) = \<Psi>[d] A + \<Psi>[d] B\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)

lemma \<Psi>_ExSet:
  \<open>\<Psi>[d] (ExSet S) = (\<exists>*c. \<Psi>[d] (S c))\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)

lemma \<Psi>_Subjection:
  \<open>\<Psi>[d] (S \<s>\<u>\<b>\<j> P) = (\<Psi>[d] S \<s>\<u>\<b>\<j> P)\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)


section \<open>Basic \<phi>-Types \& Embedding of Logic Connectives\<close>

subsection \<open>Identity \<phi>-Type\<close>

definition Itself :: " ('a,'a) \<phi> " where "Itself x = {x}"

lemma Itself_expn[\<phi>expns, iff]:
  "p \<Turnstile> (x \<Ztypecolon> Itself) \<longleftrightarrow> p = x"
  unfolding \<phi>Type_def Itself_def Satisfaction_def by auto

lemma Itself_inhabited_E[elim!]:
  \<open> Inhabited (x \<Ztypecolon> Itself) \<Longrightarrow> C \<Longrightarrow> C \<close> .

lemma Itself_inhabited[\<phi>reason %cutting, simp, intro!]:
  \<open> Inhabited (x \<Ztypecolon> Itself) \<close>
  unfolding Inhabited_def
  by blast

lemma [\<phi>reason %cutting]:
  \<open> Abstract_Domain Itself (\<lambda>_. True) \<close>
  unfolding Abstract_Domain_def Action_Tag_def Inhabited_def
  by clarsimp
 
lemma [\<phi>reason %abstract_domain]:
  \<open> Abstract_Domain\<^sub>L Itself (\<lambda>_. True) \<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def Inhabited_def
  by simp

lemma Itself_E:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<close>
  unfolding Transformation_def Premise_def by simp

text \<open>The introduction rule of Itself cannot be written in such \<exists>free-ToA form but in To-Transformation form.\<close>

lemma satisfication_encoding:
  \<open> (x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<w>\<i>\<t>\<h> P) \<longleftrightarrow> x \<Turnstile> (y \<Ztypecolon> T) \<and> P \<close>
  unfolding Transformation_def by simp


subsubsection \<open>Construction from Raw Abstraction represented by Itself \<close>
  \<comment> \<open>is a sort of reasoning process useful later in making initial Hoare triples from semantic raw
      representation (which are represented by Itself, i.e., no abstraction).\<close>

\<phi>reasoner_group abstract_from_raw = (100, [14, 1399]) for \<open>v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<close>
      > ToA_bottom and < ToA_splitting_target
      \<open>Rules constructing abstraction from raw representations\<close>
  and abstract_from_raw_cut = (1000, [1000, 1030]) for \<open>v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<close> in abstract_from_raw
      \<open>Cutting rules constructing abstraction from raw representations\<close>
  and derived_abstract_from_raw = (70, [60,80]) for \<open>v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<close>
                                                 in abstract_from_raw and < abstract_from_raw_cut
      \<open>Derived rules\<close>

declare [[\<phi>reason_default_pattern
      \<open> _ \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow> \<open> _ \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T \<w>\<i>\<t>\<h> _ \<close> (1120)
  and \<open> _ \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow> \<open> _ \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<w>\<i>\<t>\<h> _ \<close> (1110)
  and \<open> _ \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow> \<open>_\<close> (1100)
]]

declare Itself_E[\<phi>reason default %ToA_falling_latice]

lemma [\<phi>reason default %ToA_falling_latice+1 except \<open>?var \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c = c' \<Longrightarrow> c' \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> c = c'
\<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<close>
  unfolding Premise_def
  by simp

lemma [\<phi>reason %abstract_from_raw_cut]:
  \<open> c\<^sub>a \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A
\<Longrightarrow> c\<^sub>b \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> c\<^sub>a ## c\<^sub>b
\<Longrightarrow> (c\<^sub>a * c\<^sub>b) \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A * B\<close>
  unfolding Transformation_def Premise_def
  by (clarsimp; blast)

subsection \<open>Embedding of \<open>\<top>\<close>\<close>

definition \<phi>Any :: \<open>('c, 'x) \<phi>\<close> ("\<top>\<^sub>\<phi>") where \<open>\<top>\<^sub>\<phi> = (\<lambda>_. UNIV)\<close>

setup \<open>Sign.mandatory_path "\<phi>Any"\<close>

lemma unfold:
  \<open>(x \<Ztypecolon> \<top>\<^sub>\<phi>) = UNIV\<close>
  unfolding \<phi>Any_def \<phi>Type_def ..

lemma expansion[simp]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<top>\<^sub>\<phi>) \<longleftrightarrow> True\<close>
  unfolding \<phi>Any.unfold
  by simp

setup \<open>Sign.parent_path\<close>

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %extract_pure]:
  \<open>x \<Ztypecolon> \<top>\<^sub>\<phi> \<i>\<m>\<p>\<l>\<i>\<e>\<s> True\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open>True \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> \<top>\<^sub>\<phi>\<close>
  unfolding Action_Tag_def Inhabited_def
  by simp

subsubsection \<open>Transformation Rules\<close>

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P\<close>
  unfolding \<phi>Any.unfold
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<top>\<^sub>\<phi> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding \<phi>Any.unfold
  by simp

paragraph \<open>Separation Extraction\<close>

text \<open>In ToA, the \<open>\<top>\<^sub>\<phi>\<close> behaviors like a wildcard that can absorb an undetermined number of \<phi>-type items,
  and which \<phi>-type items are absorbed cannot be determined just from the type information. Therefore,
  we require explicit annotations to be given to give the range of the absorption of \<open>\<top>\<^sub>\<phi>\<close>.

TODO: make such annotation syntax.
\<close>

lemma [\<phi>reason %ToA_top+1]:
  \<open> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((), undefined) \<Ztypecolon> \<top>\<^sub>\<phi> \<^emph>[False] \<top>\<^sub>\<phi> \<close>
  unfolding Transformation_def
  by clarsimp

(*
lemma [\<phi>reason %ToA_top]:
  \<open>x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (undefined, snd x) \<Ztypecolon> \<top>\<^sub>\<phi> \<^emph>[C] W \<close>
  unfolding Transformation_def
  by clarsimp blast*)

subsection \<open>Embedding of \<open>\<bottom>\<close>\<close>

definition \<phi>Bot :: \<open>('c,'a) \<phi>\<close> ("\<bottom>\<^sub>\<phi>") where \<open>\<bottom>\<^sub>\<phi> = (\<lambda>_. 0)\<close>

setup \<open>Sign.mandatory_path "\<phi>Bot"\<close>

lemma unfold:
  \<open>(x \<Ztypecolon> \<bottom>\<^sub>\<phi>) = 0\<close>
  unfolding \<phi>Bot_def \<phi>Type_def ..

lemma expansion[simp]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<bottom>\<^sub>\<phi>) \<longleftrightarrow> False\<close>
  unfolding \<phi>Bot.unfold
  by simp

setup \<open>Sign.parent_path\<close>

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %extract_pure]:
  \<open>x \<Ztypecolon> \<bottom>\<^sub>\<phi> \<i>\<m>\<p>\<l>\<i>\<e>\<s> False \<close>
  unfolding Action_Tag_def \<phi>Bot.unfold Inhabited_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open>False \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> \<bottom>\<^sub>\<phi>\<close>
  unfolding Action_Tag_def \<phi>Bot.unfold Inhabited_def
  by simp

subsubsection \<open>Transformation Rules\<close>

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<bottom>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding \<phi>Bot.unfold
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> W * 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> W * (x \<Ztypecolon> \<bottom>\<^sub>\<phi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding \<phi>Bot.unfold
  by simp

paragraph \<open>Separation Extraction\<close>

(*TODO: more think!*)

lemma [\<phi>reason %ToA_top]:
  \<open> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> \<bottom>\<^sub>\<phi> \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (any, undefined) \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<close>
  unfolding Transformation_def
  by clarsimp


subsection \<open>Embedding of Separation Conjunction\<close>

lemma \<phi>Prod_expn':
  \<open>((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)\<close>
  unfolding BI_eq_iff by (simp add: set_mult_expn)

lemma \<phi>Prod_expn'':
  \<open> NO_MATCH (xx,yy) x
\<Longrightarrow> (x \<Ztypecolon> A \<^emph> B) = (snd x \<Ztypecolon> B) * (fst x \<Ztypecolon> A)\<close>
  unfolding BI_eq_iff by (cases x; simp add: set_mult_expn)

bundle \<phi>Prod_expn = \<phi>Prod_expn'[simp] \<phi>Prod_expn''[simp]

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> fst x \<Ztypecolon> T1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> C1
\<Longrightarrow> snd x \<Ztypecolon> T2 \<i>\<m>\<p>\<l>\<i>\<e>\<s> C2
\<Longrightarrow> x \<Ztypecolon> T1 \<^emph> T2 \<i>\<m>\<p>\<l>\<i>\<e>\<s> C1 \<and> C2\<close>
  unfolding Inhabited_def Action_Tag_def
  by (cases x; simp, blast)

paragraph \<open>Frame Rules\<close>

lemma transformation_right_frame_ty:
  \<open>(\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a = fst x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(a) \<Ztypecolon> U \<w>\<i>\<t>\<h> P(a))
\<Longrightarrow> x \<Ztypecolon> T \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f x \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P(fst x) \<close>
  unfolding Transformation_def
  by (cases x; clarsimp; blast)

lemma transformation_left_frame_ty:
  \<open>(\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a = snd x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(a) \<Ztypecolon> U \<w>\<i>\<t>\<h> P(a))
\<Longrightarrow> x \<Ztypecolon> R \<^emph> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apsnd f x \<Ztypecolon> R \<^emph> U \<w>\<i>\<t>\<h> P(snd x) \<close>
  unfolding Transformation_def
  by (cases x; clarsimp; blast)

subsubsection \<open>Abstract Domain\<close>

text \<open>The upper bound of the abstraction domain is simple.\<close>
(*
lemma \<comment> \<open>will be derived later\<close>:
  \<open> Abstract_Domain T D\<^sub>T
\<Longrightarrow> Abstract_Domain U D\<^sub>U
\<Longrightarrow> Abstract_Domain (T \<^emph> U) (\<lambda>(x,y). D\<^sub>T x \<and> D\<^sub>U y) \<close>
  unfolding Abstract_Domain_def Action_Tag_def Inhabited_def
  by (clarsimp, blast)
*)

text \<open>However, the lower bound is non-trivial, in which case we have to show the separation combination
  is compatible between the two \<phi>-types. The compatibility is encoded by predicate \<open>Separation_Disj\<close>
  and \<open>Separation_Disj\<^sub>\<phi>\<close> which are solved by means of the domainoid introduced later.
  So the rules are given until \cref{phi-types/Domainoid/App}.
\<close>


subsubsection \<open>Transformation Rules\<close>

lemma destruct_\<phi>Prod_\<phi>app: (*TODO: merge this into general destruction*)
  \<open>x \<Ztypecolon> T \<^emph> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x \<Ztypecolon> U) * (fst x \<Ztypecolon> T)\<close>
  by (cases x; simp add: Transformation_def set_mult_expn)

lemma \<phi>Prod_transformation:
  " x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> N' \<w>\<i>\<t>\<h> Pa
\<Longrightarrow> y \<Ztypecolon> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> M' \<w>\<i>\<t>\<h> Pb
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x',y') \<Ztypecolon> N' \<^emph> M' \<w>\<i>\<t>\<h> Pa \<and> Pb"
  unfolding Transformation_def by simp blast
  (*The rule is not added into the \<phi>-LPR because such product is solved by Structural Extract*)

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x \<Ztypecolon> M) * (fst x \<Ztypecolon> N) \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> N \<^emph> M \<w>\<i>\<t>\<h> P"
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason %ToA_red+1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_,_) \<Ztypecolon> _ \<^emph> _ \<w>\<i>\<t>\<h> _\<close>
                              \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> _ \<^emph> _ \<w>\<i>\<t>\<h> _\<close>]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> M) * (x \<Ztypecolon> N) \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x,y) \<Ztypecolon> N \<^emph> M \<w>\<i>\<t>\<h> P"
  by (simp add: \<phi>Prod_expn')

text \<open>The reductions on source are not enabled as they may break the form of original source assertion\<close>

paragraph \<open>Separation Extraction\<close>

text \<open>see \<section>\<open>Technical \<phi>-Types required in Reasoning Transformation/Separation Extraction of \<open>\<phi>\<close>Prod\<close>\<close>

lemma Structural_Extract_\<phi>Prod_a [\<phi>reason %ToA_cut except \<open>(_ :: ?'a::sep_semigroup set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
      \<comment> \<open>merely the rule for non-semigroup algebras.
          for others, see \<section>\<open>Technical \<phi>-Types required in Reasoning Transformation/Separation Extraction of \<open>\<phi>\<close>Prod\<close>\<close>
  \<open> fst a \<Ztypecolon> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> a \<Ztypecolon> A \<^emph>[True] X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((b, snd a), undefined) \<Ztypecolon> (Y \<^emph> X) \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp blast


subsection \<open>Embedding of Conditioned Separation Conjunction\<close>

lemma Cond_\<phi>Prod_expn:
  \<open> (x \<Ztypecolon> T \<^emph>[C] U) = (if C then (x \<Ztypecolon> T \<^emph> U) else (fst x \<Ztypecolon> T)) \<close>
  unfolding Cond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

lemma Cond_\<phi>Prod_expn_const[simp]:
  \<open>T \<^emph>[True] U \<equiv> T \<^emph> U\<close>
  \<open>x \<Ztypecolon> T \<^emph>[False] U \<equiv> fst x \<Ztypecolon> T\<close>
  by (simp_all add: Cond_\<phi>Prod_def \<phi>Type_def)

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> fst x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> snd x \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q)
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[C] U \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> (C \<longrightarrow> Q) \<close>
  unfolding Action_Tag_def Inhabited_def
  by (cases C; clarsimp; blast)

paragraph \<open>Frame Rules\<close>

lemma transformation_right_frame_conditioned_ty:
  \<open>(\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a = fst x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(a) \<Ztypecolon> U \<w>\<i>\<t>\<h> P(a))
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[C] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f x \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P(fst x) \<close>
  unfolding Transformation_def
  by (cases C; cases x; clarsimp; blast)

lemma transformation_left_frame_conditioned_ty:
  \<open>(\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a = snd x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(a) \<Ztypecolon> U \<w>\<i>\<t>\<h> P(a))
\<Longrightarrow> x \<Ztypecolon> R \<^emph>[C] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apsnd f x \<Ztypecolon> R \<^emph>[C] U \<w>\<i>\<t>\<h> C \<longrightarrow> P(snd x) \<close>
  unfolding Transformation_def
  by (cases C; cases x; clarsimp; blast)


subsubsection \<open>Transformation Rules\<close>

text \<open>see \<section>\<open>Reasoning/Supplementary Transformations/Type-embedding of Conditioned Remains\<close>\<close>

subsection \<open>Embedding of Empty\<close>

definition \<phi>None :: \<open>('v::one, unit) \<phi>\<close> ("\<circle>")
  where \<open>\<phi>None = (\<lambda>x. { 1 }) \<close>

lemma \<phi>None_expn[\<phi>expns, simp]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<phi>None) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>None_def \<phi>Type_def Satisfaction_def
  by simp

lemma \<phi>None_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>None) \<Longrightarrow> C \<Longrightarrow> C\<close> .

subsubsection \<open>Rewrites\<close>

lemma \<phi>None_itself_is_one[simp]:
  \<open>(any \<Ztypecolon> \<phi>None) = 1\<close>
  unfolding BI_eq_iff by simp

lemma \<phi>Prod_\<phi>None:
  \<open>((x',y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'a::sep_magma_1 BI)\<close>
  \<open>((x,y') \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'b::sep_magma_1 BI)\<close>
  unfolding BI_eq_iff
  by (simp_all add: set_mult_expn)


subsubsection \<open>Transformation Rules\<close>

lemma [\<phi>reason %ToA_red]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * (any \<Ztypecolon> \<circle>) \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right \<phi>None_itself_is_one .

lemma [\<phi>reason %ToA_red]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * (any \<Ztypecolon> \<circle>) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right \<phi>None_itself_is_one .

lemma [\<phi>reason %ToA_red]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (any \<Ztypecolon> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right \<phi>None_itself_is_one .

lemma [\<phi>reason %ToA_success]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> any \<Ztypecolon> \<circle> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

lemma [\<phi>reason %ToA_success+1]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> () \<Ztypecolon> \<circle> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

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

subsection \<open>Injection into Unital Algebra\<close>

definition \<phi>Some :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<black_circle> _" [91] 90)
  where \<open>\<black_circle> T = (\<lambda>x. { Some v |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma \<phi>Some_expn[simp, \<phi>expns]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<black_circle> T) \<longleftrightarrow> (\<exists>v. p = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>Some_def Satisfaction_def
  by simp

subsubsection \<open>Rewrites\<close>

lemma \<phi>Some_\<phi>Prod:
  \<open> \<black_circle> T \<^emph> \<black_circle> U = \<black_circle> (T \<^emph> U) \<close>
  by (rule \<phi>Type_eqI; clarsimp; force)

lemma \<phi>Some_eq_term_strip:
  \<open> (x \<Ztypecolon> \<black_circle> T) = (y \<Ztypecolon> \<black_circle> U) \<equiv> (x \<Ztypecolon> T) = (y \<Ztypecolon> U) \<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp blast


subsubsection \<open>Transformation Rules\<close>

lemma \<phi>Some_transformation_strip:
  \<open> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P \<equiv> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<close>
  unfolding atomize_eq Transformation_def
  by clarsimp blast

lemma [\<phi>reason %ToA_cut]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P \<close>
  unfolding \<phi>Some_transformation_strip .

lemma [\<phi>reason %ToA_cut]:
  \<open> x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<^emph>[Cw] \<black_circle> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph>[Cr] \<black_circle> R \<w>\<i>\<t>\<h> P\<close>
  by (cases Cw; cases Cr; simp add: \<phi>Some_\<phi>Prod \<phi>Some_transformation_strip)


subsection \<open>Technical \<phi>-Types required in Reasoning Transformation\<close>

subsubsection \<open>Variant of Empty \<phi>-Type for Arbitrary Abstract Objects\<close>

definition \<phi>None_freeobj :: \<open>('v::one, 'x) \<phi>\<close> ("\<circle>\<^sub>\<x>") where \<open>\<circle>\<^sub>\<x> = (\<lambda>x. 1)\<close>

lemma \<phi>None_freeobj_expn[\<phi>expns, simp]:
  \<open> (x \<Ztypecolon> \<circle>\<^sub>\<x>) = 1\<close>
  unfolding \<phi>Type_def \<phi>None_freeobj_def
  by simp

lemma \<phi>Some_\<phi>None_freeobj:
  \<open> x \<Ztypecolon> T \<^emph> \<circle>\<^sub>\<x> \<equiv> fst x \<Ztypecolon> T\<close>
  \<open> y \<Ztypecolon> \<circle>\<^sub>\<x> \<^emph> T \<equiv> snd y \<Ztypecolon> T\<close>
  \<open> x' \<Ztypecolon> \<circle>\<^sub>\<x> \<^emph> (\<circle>\<^sub>\<x> :: ('v::sep_magma_1, 'x) \<phi>) \<equiv> 1\<close>
  for T :: \<open>'b \<Rightarrow> 'a::sep_magma_1 set\<close>
  unfolding atomize_eq BI_eq_iff
  by ((rule \<phi>Type_eqI)?; clarsimp)+


subsubsection \<open>Conditional Insertion into Unital Algebra\<close>

consts \<A>merge :: action

text \<open>This section we give an equivalent representation \<open>\<black_circle> T \<^emph> \<half_blkcirc>[C] R\<close> of the conditioned separation \<^term>\<open>T \<^emph>[C] R\<close>.
  \<open>\<half_blkcirc>\<close> is convenient to specify element-wise existence, and makes it easy to merge two conditioned remainders

  \<open> (fst a, wy) \<Ztypecolon> A \<^emph>[Cy] WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph>[Cb] B \<w>\<i>\<t>\<h> P1 
\<Longrightarrow> (snd b, wx) \<Ztypecolon> \<half_blkcirc>[Cb] B \<^emph> \<half_blkcirc>[Cx] WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> \<black_circle> X \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P2
\<Longrightarrow> (snd a \<Ztypecolon> \<half_blkcirc>[Cw] W) = ((wy, wx) \<Ztypecolon> \<half_blkcirc>[Cy] WY \<^emph> \<half_blkcirc>[Cx] WX) @action \<A>merge
\<Longrightarrow> a \<Ztypecolon> A \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph>[Cr] R \<w>\<i>\<t>\<h> (P1 \<and> P2) \<close>

By \<open>\<half_blkcirc>\<close>, we can easily merge the two remainders of the transformation two-side. However, using \<open>T \<^emph>[C] U\<close>
is not as easy as this.
Nonetheless, \<open>T \<^emph>[C] R\<close> is suitable for the one-to-one transformation with remainders.
\<close>

definition \<phi>Cond_Unital_Ins :: \<open>bool \<Rightarrow> ('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<half_blkcirc>[_] _" [20,91] 90)
  \<comment> \<open>Conditional Unital Insertion\<close>
  where \<open>\<half_blkcirc>[C] T = (if C then \<black_circle> T else \<circle>\<^sub>\<x>)\<close>



paragraph \<open>Rewrites\<close>

lemma \<phi>Cond_Unital_Ins_unfold:
  \<open> \<half_blkcirc>[C] T = (if C then \<black_circle> T else \<circle>\<^sub>\<x>) \<close>
  unfolding \<phi>Type_def \<phi>Cond_Unital_Ins_def
  by clarsimp

lemma \<phi>Cond_Unital_Ins_unfold_simp[simp]:
  \<open> \<half_blkcirc>[True] T \<equiv> \<black_circle> T \<close>
  \<open> \<half_blkcirc>[False] T \<equiv> \<circle>\<^sub>\<x> \<close>
  unfolding \<phi>Cond_Unital_Ins_unfold
  by simp+

lemma \<phi>Cond_Unital_Ins_expn[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> \<half_blkcirc>[C] T) \<longleftrightarrow> (if C then (\<exists>v. p = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T)) else p = None) \<close>
  unfolding \<phi>Cond_Unital_Ins_unfold
  by clarsimp

lemma \<phi>Cond_Unital_Prod:
  \<open>\<half_blkcirc>[C] T \<^emph> \<half_blkcirc>[C] U \<equiv> \<half_blkcirc>[C] (T \<^emph> U)\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI; clarsimp; force)

lemma \<phi>Cond_Unital_trans_rewr:
  \<open> x \<Ztypecolon> \<half_blkcirc>[C] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[C] U \<w>\<i>\<t>\<h> C \<longrightarrow> P \<equiv> C \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P) \<close>
  unfolding atomize_eq Transformation_def
  by (cases C; clarsimp; blast)

lemma Cond_\<phi>Prod_expn_\<phi>Some:
  \<open>\<black_circle> (T \<^emph>[C] U) \<equiv> \<black_circle> T \<^emph> \<half_blkcirc>[C] U\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI; cases C; clarsimp; force)

lemma cond_prod_transformation_rewr:
  \<open> x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<w>\<i>\<t>\<h> P \<equiv> x \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> \<black_circle> U' \<w>\<i>\<t>\<h> P\<close>
  \<open> x' \<Ztypecolon> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P \<equiv> x' \<Ztypecolon> \<black_circle> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding atomize_eq
  by (cases C; clarsimp simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj \<phi>Some_transformation_strip)+


paragraph \<open>Reasoning Properties\<close>

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P x)
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[C] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> C \<longrightarrow> P x\<close>
  unfolding Action_Tag_def Inhabited_def
  by clarsimp blast


paragraph \<open>Transformations\<close>

lemma [\<phi>reason %ToA_cut]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Cx = Cy
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cy \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[Cx] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[Cy] U \<w>\<i>\<t>\<h> Cy \<longrightarrow> P\<close>
  unfolding Premise_def
  by (simp add: \<phi>Cond_Unital_trans_rewr)

lemma [\<phi>reason %ToA_cut]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Cx = Cy
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cy \<Longrightarrow> x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[Cx] T \<^emph>[Cw] \<half_blkcirc>[Cx] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[Cy] U \<^emph>[Cr] \<half_blkcirc>[Cy] R \<w>\<i>\<t>\<h> Cy \<longrightarrow> P\<close>
  unfolding Premise_def
  by (cases Cw; cases Cr; clarsimp simp add: \<phi>Cond_Unital_Prod \<phi>Cond_Unital_trans_rewr)

paragraph \<open>Normalization\<close>

subparagraph \<open>Source\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[True] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[False] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (x \<Ztypecolon> \<half_blkcirc>[True] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (x \<Ztypecolon> \<half_blkcirc>[False] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> x \<Ztypecolon> \<black_circle> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[True] T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_success]:
  \<open> x \<Ztypecolon> (\<half_blkcirc>[False] T \<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (U \<^emph>[False] \<top>\<^sub>\<phi>) \<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

subparagraph \<open>Target\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[True] U \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[False] U \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[True] U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[False] U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[True] U \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_success]:
  \<open> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (undefined, fst x) \<Ztypecolon> \<half_blkcirc>[False] U \<^emph>[True] T \<close>
  by (clarsimp simp add: \<phi>Some_\<phi>None_freeobj)

paragraph \<open>Simplification Protects\<close>

definition [simplification_protect]:
  \<open>\<A>merge_SP P \<equiv> P @action \<A>merge\<close>

lemma [cong]:
  \<open>\<A>merge_SP P \<equiv> \<A>merge_SP P\<close> .

paragraph \<open>Merging Conditioned \<phi>-Types\<close>

declare [[\<phi>reason_default_pattern
      \<open>(_ \<Ztypecolon> \<half_blkcirc>[_] _) = ((_,_) \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) @action \<A>merge\<close> \<Rightarrow>
      \<open>(_ \<Ztypecolon> \<half_blkcirc>[_] _) = (_ \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) @action \<A>merge\<close>   (100)
  and \<open>(_ \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) = (_ \<Ztypecolon> \<half_blkcirc>[_] _) @action \<A>merge\<close> \<Rightarrow>
      \<open>(_ \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) = (_ \<Ztypecolon> \<half_blkcirc>[_] _) @action \<A>merge\<close>   (100)
(*and \<open>_ = (if ?flag then _ else _) @action \<A>merge \<close> \<Rightarrow>
      \<open>_ = (if ?flag then _ else _) @action \<A>merge \<close>   (100)*)
(*  and \<open>?flag \<longrightarrow> _ @action \<A>merge\<close> \<Rightarrow>
      \<open>?flag \<longrightarrow> _ @action \<A>merge\<close>   (100)*)
  and \<open>?X @action \<A>merge\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed \<A>merge rule\<close> (?X @action \<A>merge))\<close> (0)
]]

\<phi>reasoner_group \<A>merge = (%cutting, [%cutting, %cutting+10]) for \<open>(_ \<Ztypecolon> \<half_blkcirc>[_] _) = _\<close>
  \<open>Rules merging multiple conditioned \<phi>types into one conditioned \<phi>type,
   always using the abstract object(s) given in the left hand side to assign the abstract object(s)
   in the right.\<close>

text \<open>Information is always given from left to right below.
      They accept arguments from LHS and assign the result to RHS\<close>

lemma [\<phi>reason %\<A>merge]: \<comment> \<open>contracts two sides respectively\<close>
  \<open>(x \<Ztypecolon> \<half_blkcirc>[True] (A \<^emph> B)) = ((fst x, snd x) \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[True] B) @action \<A>merge\<close>
  \<open>(a \<Ztypecolon> \<half_blkcirc>[True] A) = ((a, undefined) \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[False] B) @action \<A>merge\<close>
  \<open>(b \<Ztypecolon> \<half_blkcirc>[True] B) = ((undefined, b) \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[True] B) @action \<A>merge\<close>
  \<open>(c \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) = ((undefined, undefined) \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[False] B) @action \<A>merge\<close>
  unfolding Action_Tag_def BI_eq_iff
  by (clarsimp; force)+

lemma [\<phi>reason %\<A>merge]:
  \<open> (x \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[True] B) = (x \<Ztypecolon> \<half_blkcirc>[True] (A \<^emph> B)) @action \<A>merge \<close>
  \<open> (x \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[False] B) = (fst x \<Ztypecolon> \<half_blkcirc>[True] A) @action \<A>merge \<close>
  \<open> (x \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[True] B) = (snd x \<Ztypecolon> \<half_blkcirc>[True] B) @action \<A>merge \<close>
  \<open> (x \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[False] B) = (undefined \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>merge \<close>
  unfolding Action_Tag_def BI_eq_iff
  by (clarsimp; force)+

lemma [\<phi>reason %\<A>merge+10]:
  \<open> ((x,y) \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[False] B) = (x \<Ztypecolon> \<half_blkcirc>[True] A) @action \<A>merge \<close>
  \<open> ((x,y) \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[True] B) = (y \<Ztypecolon> \<half_blkcirc>[True] B) @action \<A>merge \<close>
  unfolding Action_Tag_def BI_eq_iff
  by (clarsimp; force)+


subsubsection \<open>Separation Extraction of \<open>\<phi>\<close>Prod\<close>

text \<open>Using the technical auxiliaries, we can give the separation extraction for \<open>\<phi>Prod\<close>\<close>

lemma Structural_Extract_\<phi>Prod_right_i[\<phi>reason %ToA_cut]:
  \<open> (fst a, wy) \<Ztypecolon> A \<^emph>[Cy] WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph>[Cb] B \<w>\<i>\<t>\<h> P1
\<Longrightarrow> if Cb then ((snd b, wx) \<Ztypecolon> B \<^emph>[Cx] WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<^emph>[Cr] R \<w>\<i>\<t>\<h> P2)
          else (Cx, Cr, WX, wx, P2) = (True, False, X, fst c, True)
\<Longrightarrow> (snd a \<Ztypecolon> \<half_blkcirc>[Cw] W) = ((wy, wx) \<Ztypecolon> \<half_blkcirc>[Cy] WY \<^emph> \<half_blkcirc>[Cx] WX) @action \<A>merge
\<Longrightarrow> a \<Ztypecolon> A \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph>[Cr] R \<w>\<i>\<t>\<h> (P1 \<and> P2) \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
  apply (cases Cb; simp add: cond_prod_transformation_rewr;
         clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  subgoal premises prems
    by (insert prems(1)[THEN transformation_left_frame, where R=\<open>wx \<Ztypecolon> \<half_blkcirc>[Cx] WX\<close>]
               prems(2)[THEN transformation_right_frame, where R=\<open>fst b \<Ztypecolon> \<black_circle> Y\<close>],
        simp add: mult.assoc transformation_trans)
  by (simp add: transformation_left_frame mult.assoc)

(* TODO!
lemma [\<phi>reason 1201]:
  \<open> Try S1 ((fst a, wy) \<Ztypecolon> \<black_circle> A \<^emph> \<half_blkcirc>[Cy] WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cb] B \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> Y' \<^emph> \<half_blkcirc>[Cb] B') (x'1 \<Ztypecolon> \<black_circle> A' \<^emph> \<half_blkcirc>[Cy] WY') \<and> P1 @action \<A>SEi )
\<Longrightarrow> Try S2 ((snd b, wx) \<Ztypecolon> \<half_blkcirc>[Cb] B \<^emph> \<half_blkcirc>[Cx] WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> \<black_circle> X \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'2 \<Ztypecolon> \<black_circle> X' \<^emph> \<half_blkcirc>[Cr] R') (x'2 \<Ztypecolon> \<half_blkcirc>[Cb] B' \<^emph> \<half_blkcirc>[Cx] WX') \<and> P2 @action \<A>SEi )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> (snd a \<Ztypecolon> \<half_blkcirc>[Cw] W) = ((wy, wx) \<Ztypecolon> \<half_blkcirc>[Cy] WY \<^emph> \<half_blkcirc>[Cx] WX) @action \<A>merge
\<Longrightarrow> a \<Ztypecolon> \<black_circle> A \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> \<black_circle> (Y \<^emph> X) \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'3 \<Ztypecolon> \<black_circle> (Y' \<^emph> X') \<^emph> \<half_blkcirc>[Cr] R') (x'3 \<Ztypecolon> \<black_circle> A' \<^emph> \<half_blkcirc>[Cw] W') \<and> P1 \<and> P2 @action \<A>SEi \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and A' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_right_i .*)

lemma Structural_Extract_\<phi>Prod_left_i [\<phi>reason %ToA_cut]:
  \<open> (fst (fst x), fst wr) \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yr \<Ztypecolon> Y \<^emph>[Cra] Rt \<w>\<i>\<t>\<h> P1
\<Longrightarrow> if Cw then ((snd (fst x), snd x) \<Ztypecolon> U \<^emph>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> wr \<Ztypecolon> W \<^emph>[Crb] Ru \<w>\<i>\<t>\<h> P2)
          else (Cw2, Crb, Ru, wr, P2) = (False, True, U, (undefined, snd (fst x)), True)
\<Longrightarrow> ((snd yr, snd wr) \<Ztypecolon> \<half_blkcirc>[Cra] Rt \<^emph> \<half_blkcirc>[Crb] Ru) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst yr, r) \<Ztypecolon> Y \<^emph>[Cr] R \<w>\<i>\<t>\<h> P1 \<and> P2 \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
  apply (cases Cw; simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  subgoal premises prems
    by (insert prems(1)[THEN transformation_left_frame, where R=\<open>snd wr \<Ztypecolon> \<half_blkcirc>[Crb] Ru\<close>]
               prems(2)[THEN transformation_right_frame, where R=\<open>fst (fst x) \<Ztypecolon> \<black_circle> T\<close>],
        simp add: mult.assoc[symmetric] prems(3)[symmetric],
        smt (z3) Transformation_def)
  by (metis (no_types, lifting) transformation_left_frame mult.assoc)


(* TODO
lemma [\<phi>reason 1201]:
  \<open> Try S1 ((fst (fst x), fst wr) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yr \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cra] Rt \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> Y' \<^emph> \<half_blkcirc>[Cra] Rt') (x'1 \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[Cw] W') \<and> P1 @action \<A>SEi )
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> wr \<Ztypecolon> \<half_blkcirc>[Cw] W \<^emph> \<half_blkcirc>[Crb] Ru \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'2 \<Ztypecolon> \<half_blkcirc>[Cw] W' \<^emph> \<half_blkcirc>[Crb] Ru') (x'2 \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[Cw2] W2') \<and> P2 @action \<A>SEi )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> ((snd yr, snd wr) \<Ztypecolon> \<half_blkcirc>[Cra] Rt \<^emph> \<half_blkcirc>[Crb] Ru) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> \<black_circle> (T \<^emph> U) \<^emph> \<half_blkcirc>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst yr, r) \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> Y' \<^emph> \<half_blkcirc>[Cr] R') (x'3 \<Ztypecolon> \<black_circle> (T' \<^emph> U') \<^emph> \<half_blkcirc>[Cw2] W2') \<and> P1 \<and> P2 @action \<A>SEi \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and T' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_left_i .
*)

section \<open>Basic \<phi>-Type Properties\<close>

text \<open>The two properties are essential for reasoning the general transformation including separation extraction.\<close>

subsection \<open>Identity Element I\&E\<close>

definition Identity_Element\<^sub>I :: \<open>'a::one BI \<Rightarrow> bool \<Rightarrow> bool\<close> where \<open>Identity_Element\<^sub>I S P \<longleftrightarrow> (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P)\<close>
definition Identity_Element\<^sub>E :: \<open>'a::one BI \<Rightarrow> bool\<close> where \<open>Identity_Element\<^sub>E S \<longleftrightarrow> (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S)\<close>

definition Identity_Elements\<^sub>I :: \<open>('c::one,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Identity_Elements\<^sub>I T D P \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x))\<close>

definition Identity_Elements\<^sub>E :: \<open>('c::one,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Identity_Elements\<^sub>E T D \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T))\<close>

declare [[ \<phi>reason_default_pattern
      \<open>Identity_Element\<^sub>I ?S _\<close> \<Rightarrow> \<open>Identity_Element\<^sub>I ?S _\<close> (100)
  and \<open>Identity_Element\<^sub>I (_ \<Ztypecolon> ?T) _\<close> \<Rightarrow> \<open>Identity_Element\<^sub>I (_ \<Ztypecolon> ?T) _\<close> (110)
  and \<open>Identity_Element\<^sub>E ?S\<close> \<Rightarrow> \<open>Identity_Element\<^sub>E ?S\<close> (100)
  and \<open>Identity_Element\<^sub>E (_ \<Ztypecolon> ?T)\<close> \<Rightarrow> \<open>Identity_Element\<^sub>E (_ \<Ztypecolon> ?T)\<close> (110)

  and \<open>Identity_Elements\<^sub>I ?T _ _\<close> \<Rightarrow> \<open>Identity_Elements\<^sub>I ?T _ _\<close> (100)
  and \<open>Identity_Elements\<^sub>E ?T _\<close> \<Rightarrow> \<open>Identity_Elements\<^sub>E ?T _\<close> (100)
]]

\<phi>reasoner_group identity_element = (100,[1,3000]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
    \<open>Reasoning rules deducing if the given assertion can transform to or be transformed from the
     assertion of identity element.\<close>
 and identity_element_fallback = (1,[1,1]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > fail
    \<open>Fallbacks of reasoning Identity_Element.\<close>
 and identity_element_\<phi> = (10, [10, 10]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
    \<open>Turning to \<open>Identity_Elements\<^sub>I\<close> and \<open>Identity_Elements\<^sub>E\<close>\<close>
 and derived_identity_element = (50, [50,50]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > identity_element_\<phi>
    \<open>Automatically derived Identity_Element rules\<close>
 and identity_element_cut = (1000, [1000,1029]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > derived_identity_element
    \<open>Cutting rules for Identity_Element\<close>
 and identity_element_red = (2500, [2500, 2530]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > identity_element_cut
    \<open>Literal Reduction\<close>
 and identity_element_ToA = (50, [50,51]) for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> in ToA
    \<open>Entry points from ToA to Identity_Element\<close>

subsubsection \<open>Extracting Pure Facts\<close>

paragraph \<open>Identity_Element\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> Q \<longrightarrow> Inhabited S @action \<A>ESC
\<Longrightarrow> Identity_Element\<^sub>I S P \<longrightarrow> (Q \<longrightarrow> P) @action \<A>EIF \<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def Transformation_def Inhabited_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> Inhabited S \<longrightarrow> P @action \<A>EIF
\<Longrightarrow> Identity_Element\<^sub>E S \<longrightarrow> P @action \<A>EIF \<close>
  unfolding Identity_Element\<^sub>E_def Action_Tag_def Transformation_def Inhabited_def
  by blast

lemma Identity_Element\<^sub>I_\<A>EIF_sat:
  \<open> Identity_Element\<^sub>I S P \<longrightarrow> (\<forall>v. v \<Turnstile> S \<longrightarrow> v = 1 \<and> P) @action \<A>EIF \<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def Transformation_def
  by blast

lemma Identity_Element\<^sub>I_\<A>ESC_sat:
  \<open> (\<forall>v. v \<Turnstile> S \<longrightarrow> v = 1 \<and> P) \<longrightarrow> Identity_Element\<^sub>I S P @action \<A>ESC \<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def Transformation_def
  by blast

lemma Identity_Element\<^sub>E_\<A>EIF_sat:
  \<open> Identity_Element\<^sub>E S \<longrightarrow> (1 \<Turnstile> S) @action \<A>EIF \<close>
  unfolding Identity_Element\<^sub>E_def Action_Tag_def Transformation_def
  by blast

lemma Identity_Element\<^sub>E_\<A>ESC_sat:
  \<open> (1 \<Turnstile> S) \<longrightarrow> Identity_Element\<^sub>E S @action \<A>ESC \<close>
  unfolding Identity_Element\<^sub>E_def Action_Tag_def Transformation_def
  by blast

bundle Identity_Element\<^sub>I_sat = Identity_Element\<^sub>I_\<A>EIF_sat [\<phi>reason %extract_pure_sat]
                               Identity_Element\<^sub>I_\<A>ESC_sat [\<phi>reason %extract_pure_sat]
bundle Identity_Element\<^sub>E_sat = Identity_Element\<^sub>E_\<A>EIF_sat [\<phi>reason %extract_pure_sat]
                               Identity_Element\<^sub>E_\<A>ESC_sat [\<phi>reason %extract_pure_sat]

bundle Identity_Element_sat begin
  unbundle Identity_Element\<^sub>I_sat Identity_Element\<^sub>E_sat
end


paragraph \<open>Identity_Elements\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x. Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x) \<longrightarrow> Q x @action \<A>EIF)
\<Longrightarrow> Identity_Elements\<^sub>I T D P \<longrightarrow> (\<forall>x. D x \<longrightarrow> Q x) @action \<A>EIF\<close>
  unfolding Action_Tag_def Identity_Elements\<^sub>I_def
  by clarsimp

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x. Identity_Element\<^sub>E (x \<Ztypecolon> T) \<longrightarrow> Q x @action \<A>EIF)
\<Longrightarrow> Identity_Elements\<^sub>E T D \<longrightarrow> (\<forall>x. D x \<longrightarrow> Q x) @action \<A>EIF\<close>
  unfolding Action_Tag_def Identity_Elements\<^sub>E_def
  by clarsimp



subsubsection \<open>Fallback\<close>

lemma [\<phi>reason default %identity_element_fallback]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False
\<Longrightarrow> Identity_Element\<^sub>I S False\<close>
  unfolding Premise_def
  by blast

lemma [\<phi>reason default %identity_element_fallback]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False
\<Longrightarrow> Identity_Element\<^sub>E S\<close>
  unfolding Premise_def
  by blast

lemma [\<phi>reason default %fail]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show\<close> (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1))
\<Longrightarrow> Identity_Element\<^sub>I S Any \<close>
  unfolding TRACE_FAIL_def
  by blast

lemma [\<phi>reason default %fail]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show\<close> (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S))
\<Longrightarrow> Identity_Element\<^sub>E S \<close>
  unfolding TRACE_FAIL_def
  by blast

lemma [\<phi>reason default %identity_element_fallback]:
  \<open> Identity_Elements\<^sub>I T (\<lambda>_. False) (\<lambda>_. True) \<close>
  unfolding Identity_Elements\<^sub>I_def
  by blast

lemma [\<phi>reason default %identity_element_fallback]:
  \<open> Identity_Elements\<^sub>E T (\<lambda>_. False) \<close>
  unfolding Identity_Elements\<^sub>E_def
  by blast



subsubsection \<open>Termination\<close>

lemma [\<phi>reason %identity_element_cut]:
  \<open>Identity_Element\<^sub>I 0 True\<close>
  unfolding Identity_Element\<^sub>I_def by simp

lemma [\<phi>reason %identity_element_cut for \<open>Identity_Element\<^sub>E 1\<close>
                                         \<open>Identity_Element\<^sub>E ?var\<close> ]:
  \<open>Identity_Element\<^sub>E 1\<close>
  unfolding Identity_Element\<^sub>E_def by simp

lemma [\<phi>reason %identity_element_cut for \<open>Identity_Element\<^sub>I 1 _\<close>
                                         \<open>Identity_Element\<^sub>I ?var _\<close> ]:
  \<open>Identity_Element\<^sub>I 1 True\<close>
  unfolding Identity_Element\<^sub>I_def by simp

lemma Identity_Element\<^sub>E_empty[\<phi>reason %identity_element_cut]:
  \<open>Identity_Element\<^sub>E (any \<Ztypecolon> \<circle>)\<close>
  unfolding Identity_Element\<^sub>E_def by simp

lemma Identity_Element\<^sub>I_empty[\<phi>reason %identity_element_cut]:
  \<open>Identity_Element\<^sub>I (any \<Ztypecolon> \<circle>) True\<close>
  unfolding Identity_Element\<^sub>I_def by simp

(*
lemma [\<phi>reason %identity_element_cut for \<open>Identity_Element\<^sub>I {_} _\<close> ]:
  \<open>Identity_Element\<^sub>I {1} True\<close>
  unfolding Identity_Element\<^sub>I_def one_set_def by simp

lemma [\<phi>reason %identity_element_cut for \<open>Identity_Element\<^sub>E {_}\<close>]:
  \<open>Identity_Element\<^sub>E {1}\<close>
  unfolding Identity_Element\<^sub>E_def one_set_def by simp
*)

subsubsection \<open>Special Forms\<close>

lemma [\<phi>reason %identity_element_red for \<open>Identity_Element\<^sub>I _ True\<close>]:
  \<open> Identity_Element\<^sub>I X Any
\<Longrightarrow> Identity_Element\<^sub>I X True \<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by simp

paragraph \<open>Conditioned Branch\<close>

subparagraph \<open>Reduction\<close>

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>I A P
\<Longrightarrow> Identity_Element\<^sub>I (If True A B) P \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>I B P
\<Longrightarrow> Identity_Element\<^sub>I (If False A B) P \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> Identity_Element\<^sub>E (If True A B) \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (If False A B) \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>I A D P
\<Longrightarrow> Identity_Elements\<^sub>I (If True A B) D P \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>I B D P
\<Longrightarrow> Identity_Elements\<^sub>I (If False A B) D P \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>E A D
\<Longrightarrow> Identity_Elements\<^sub>E (If True A B) D \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>E B D
\<Longrightarrow> Identity_Elements\<^sub>E (If False A B) D \<close>
  by simp


subparagraph \<open>Normalizing\<close>

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I (If C (x \<Ztypecolon> A) (x \<Ztypecolon> B)) P
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> If C A B) P\<close>
  by (cases C; simp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>E (If C (x \<Ztypecolon> A) (x \<Ztypecolon> B))
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> If C A B)\<close>
  by (cases C; simp)

subparagraph \<open>Case Split\<close>

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>  C \<Longrightarrow> Identity_Elements\<^sub>I A D\<^sub>A P\<^sub>A)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not>C \<Longrightarrow> Identity_Elements\<^sub>I B D\<^sub>B P\<^sub>B)
\<Longrightarrow> Identity_Elements\<^sub>I (If C A B) (if C then D\<^sub>A else D\<^sub>B) (if C then P\<^sub>A else P\<^sub>B) \<close>
  by (cases C; simp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>  C \<Longrightarrow> Identity_Elements\<^sub>E (If C A B) D\<^sub>A)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not>C \<Longrightarrow> Identity_Elements\<^sub>E (If C A B) D\<^sub>B)
\<Longrightarrow> Identity_Elements\<^sub>E (If C A B) (If C D\<^sub>A D\<^sub>B)\<close>
  by (cases C; simp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Element\<^sub>I A Pa)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Identity_Element\<^sub>I B Pb)
\<Longrightarrow> Identity_Element\<^sub>I (If C A B) (If C Pa Pb) \<close>
  by (cases C; simp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Element\<^sub>E A)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Identity_Element\<^sub>E B)
\<Longrightarrow> Identity_Element\<^sub>E (If C A B) \<close>
  by (cases C; simp)

paragraph \<open>Case Split of Sum Type\<close>

subparagraph \<open>Reduction\<close>

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>E (A a)
\<Longrightarrow> Identity_Element\<^sub>E (case_sum A B (Inl a)) \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>E (B b)
\<Longrightarrow> Identity_Element\<^sub>E (case_sum A B (Inr b)) \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>I (A a) P
\<Longrightarrow> Identity_Element\<^sub>I (case_sum A B (Inl a)) P \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Element\<^sub>I (B b) P
\<Longrightarrow> Identity_Element\<^sub>I (case_sum A B (Inr b)) P \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>E (A a) D
\<Longrightarrow> Identity_Elements\<^sub>E (case_sum A B (Inl a)) D \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>E (B b) D
\<Longrightarrow> Identity_Elements\<^sub>E (case_sum A B (Inr b)) D \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>I (A a) D P
\<Longrightarrow> Identity_Elements\<^sub>I (case_sum A B (Inl a)) D P \<close>
  by simp

lemma [\<phi>reason %identity_element_red]:
  \<open> Identity_Elements\<^sub>I (B b) D P
\<Longrightarrow> Identity_Elements\<^sub>I (case_sum A B (Inr b)) D P \<close>
  by simp

subparagraph \<open>Case Split\<close>

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> Identity_Element\<^sub>I (A a) (P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> Identity_Element\<^sub>I (B b) (Q b))
\<Longrightarrow> Identity_Element\<^sub>I (case_sum A B x) (pred_sum P Q x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> Identity_Element\<^sub>E (A a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> Identity_Element\<^sub>E (B b))
\<Longrightarrow> Identity_Element\<^sub>E (case_sum A B x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> Identity_Elements\<^sub>I (A a) (D\<^sub>A a) (P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> Identity_Elements\<^sub>I (B b) (D\<^sub>B b) (Q b))
\<Longrightarrow> Identity_Elements\<^sub>I (case_sum A B x) (case_sum D\<^sub>A D\<^sub>B x) (case_sum P Q x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> Identity_Elements\<^sub>E (A a) (D\<^sub>A a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> Identity_Elements\<^sub>E (B b) (D\<^sub>B b))
\<Longrightarrow> Identity_Elements\<^sub>E (case_sum A B x) (case_sum D\<^sub>A D\<^sub>B x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)



subsubsection \<open>ToA Entry Point\<close>

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P \<close>
  unfolding Identity_Element\<^sub>I_def .

lemma [\<phi>reason default ! %identity_element_ToA+1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<circle> \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> () \<Ztypecolon> \<circle> \<w>\<i>\<t>\<h> P \<close>
  unfolding Identity_Element\<^sub>I_def
  by simp

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> \<w>\<i>\<t>\<h> P \<close>
  unfolding Identity_Element\<^sub>I_def
  by simp

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<close>
  unfolding Identity_Element\<^sub>E_def .

lemma [\<phi>reason default ! %identity_element_ToA+1 for \<open>_ \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> () \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<close>
  unfolding Identity_Element\<^sub>E_def
  by simp

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> x \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<close>
  unfolding Identity_Element\<^sub>E_def
  by simp


subsubsection \<open>Logic Connectives \& Basic \<phi>-Types\<close>

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>I Itself (\<lambda>x. x = 1) (\<lambda>_. True) \<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Transformation_def
  by clarsimp

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>E Itself (\<lambda>x. x = 1) \<close>
  unfolding Identity_Element\<^sub>E_def Identity_Elements\<^sub>E_def Transformation_def
  by clarsimp

lemma [\<phi>reason no explorative backtrack %identity_element_\<phi>]:
  \<open> Identity_Elements\<^sub>I T D P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x) \<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Premise_def
  using transformation_trans by fastforce

lemma [\<phi>reason no explorative backtrack %identity_element_\<phi>]:
  \<open> Identity_Elements\<^sub>E T D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T) \<close>
  unfolding Identity_Element\<^sub>E_def Identity_Elements\<^sub>E_def Premise_def
  using transformation_trans by fastforce

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I A P1
\<Longrightarrow> Identity_Element\<^sub>I B P2
\<Longrightarrow> Identity_Element\<^sub>I (A + B) (P1 \<or> P2)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by simp

lemma (*The above rule is local complete*)
  \<open>Identity_Element\<^sub>I (A + B) P \<Longrightarrow> Identity_Element\<^sub>I A P \<and> Identity_Element\<^sub>I B P\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by clarsimp

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>E A \<or> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (A + B)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by clarsimp

lemma (*The above rule is not local complete*)
  \<open> Identity_Element\<^sub>E (A + B) \<Longrightarrow> Identity_Element\<^sub>E A \<and> Identity_Element\<^sub>E B\<close>
  oops

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I (A x) P
\<Longrightarrow> Identity_Element\<^sub>I (AllSet A) P\<close>
  unfolding Identity_Element\<^sub>I_def
  by (metis AllSet_expn Transformation_def)
(*The rule is not local complete*)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>x. Identity_Element\<^sub>E (A x))
\<Longrightarrow> Identity_Element\<^sub>E (AllSet A)\<close>
  unfolding Identity_Element\<^sub>E_def
  by (metis AllSet_expn Transformation_def)

lemma (*The above rule is local complete*)
  \<open> Identity_Element\<^sub>E (AllSet A) \<Longrightarrow> Identity_Element\<^sub>E (A x) \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by clarsimp

lemma [\<phi>reason %identity_element_cut]:
  \<open>(\<And>x. Identity_Element\<^sub>I (A x) (P x))
\<Longrightarrow> Identity_Element\<^sub>I (ExSet A) (Ex P)\<close>
  unfolding Identity_Element\<^sub>I_def
  by (metis ExSet_expn Transformation_def)

lemma (*The above rule is local complete*)
  \<open>Identity_Element\<^sub>I (ExSet A) P \<Longrightarrow> Identity_Element\<^sub>I (A x) P\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp; blast)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>E (A x)
\<Longrightarrow> Identity_Element\<^sub>E (ExSet A)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp; blast)

lemma (*The above rule is not local complete*)
  \<open>Identity_Element\<^sub>E (ExSet A) \<Longrightarrow> \<exists>x. Identity_Element\<^sub>E (A x)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def ExSet_expn
  by clarsimp

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Identity_Element\<^sub>I A Q)
\<Longrightarrow> Identity_Element\<^sub>I (A \<s>\<u>\<b>\<j> P) (P \<and> Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (simp; blast)

lemma
  \<open> Identity_Element\<^sub>I (A \<s>\<u>\<b>\<j> P) (P \<and> Q) \<Longrightarrow> (P \<Longrightarrow> Identity_Element\<^sub>I A Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Inhabited_def
  by (cases P; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P
\<Longrightarrow> Identity_Element\<^sub>E (A \<s>\<u>\<b>\<j> P)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def Premise_def
  by (clarsimp; blast)

lemma (*The above rule is local complete*)
  \<open> Identity_Element\<^sub>E (A \<s>\<u>\<b>\<j> P) \<Longrightarrow> P \<and> Identity_Element\<^sub>E A \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def Premise_def
  by (clarsimp; blast)

lemma [\<phi>reason %identity_element_cut]: 
  \<open> Identity_Element\<^sub>I A P
\<Longrightarrow> Identity_Element\<^sub>I B Q
\<Longrightarrow> Identity_Element\<^sub>I (A * B) (P \<and> Q) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp simp add: set_mult_expn, insert mult_1_class.mult_1_left; blast)
  (* It is not complete, example: algebra {e,a} where the sep conjunction is only defined
     on the unit, x ## y \<longleftrightarrow> x = e \<and> y = e.
     Let A = B = {e,a}, we have A * B = {e}. Both A B are not stateless but A * B is. *)

lemma [\<phi>reason %identity_element_cut]: 
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (A * B) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp, insert mult_1_class.mult_1_left sep_magma_1_left, blast)

lemma (*the above rule is not local complete*)
  \<open> Identity_Element\<^sub>E (A * B) \<Longrightarrow> Identity_Element\<^sub>E A \<and> Identity_Element\<^sub>E B \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  oops

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>I T D\<^sub>T P
\<Longrightarrow> Identity_Elements\<^sub>I U D\<^sub>U Q
\<Longrightarrow> Identity_Elements\<^sub>I (T \<^emph> U) (\<lambda>(x,y). D\<^sub>T x \<and> D\<^sub>U y) (\<lambda>(x,y). P x \<and> Q y)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def \<phi>Prod_expn' Transformation_def
  by (simp add: set_mult_expn, insert mult_1_class.mult_1_left, blast)

lemma [\<phi>reason %identity_element_cut]: 
  \<open> Identity_Elements\<^sub>E T D\<^sub>T
\<Longrightarrow> Identity_Elements\<^sub>E U D\<^sub>U
\<Longrightarrow> Identity_Elements\<^sub>E (T \<^emph> U) (\<lambda>(x,y). D\<^sub>T x \<and> D\<^sub>U y) \<close>
  for T :: \<open>'a \<Rightarrow> 'b::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>E_def Identity_Elements\<^sub>E_def Transformation_def
  by (clarsimp simp add: \<phi>Prod_expn', insert set_mult_expn, fastforce)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>I T D\<^sub>T P
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Elements\<^sub>I U D\<^sub>U Q)
\<Longrightarrow> Identity_Elements\<^sub>I (T \<^emph>[C] U) (\<lambda>(x,y). D\<^sub>T x \<and> (C \<longrightarrow> D\<^sub>U y)) (\<lambda>(x,y). P x \<and> (C \<longrightarrow> Q y)) \<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Transformation_def Premise_def
  by (cases C; clarsimp simp add: \<phi>Prod_expn'; insert mult_1_class.mult_1_right; blast)

lemma [\<phi>reason %identity_element_cut]: 
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Element\<^sub>E B)
\<Longrightarrow> Identity_Element\<^sub>E (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def REMAINS_def
  by (clarsimp, insert mult_1_class.mult_1_left sep_magma_1_left, blast)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I A P
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Element\<^sub>I B Q)
\<Longrightarrow> Identity_Element\<^sub>I (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) (P \<and> (C \<longrightarrow> Q)) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Premise_def REMAINS_def
  by (clarsimp, insert mult_1_class.mult_1_right, blast)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>E T D\<^sub>T
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Elements\<^sub>E U D\<^sub>U)
\<Longrightarrow> Identity_Elements\<^sub>E (T \<^emph>[C] U) (\<lambda>(x,y). D\<^sub>T x \<and> (C \<longrightarrow> D\<^sub>U y)) \<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding Identity_Element\<^sub>E_def Identity_Elements\<^sub>E_def Transformation_def Premise_def
  by (cases C; clarsimp simp add: \<phi>Prod_expn'; insert mult_1_class.mult_1_right sep_magma_1_left; blast)

lemma [\<phi>reason %identity_element_cut]: 
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (A \<and>\<^sub>B\<^sub>I B) \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp)

lemma (*the above rule is local complete*)
  \<open> Identity_Element\<^sub>E (A \<and>\<^sub>B\<^sub>I B) \<Longrightarrow> Identity_Element\<^sub>E A \<and> Identity_Element\<^sub>E B \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I A P \<or> Identity_Element\<^sub>I B Q
\<Longrightarrow> Identity_Element\<^sub>I (A \<and>\<^sub>B\<^sub>I B) (P \<or> Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp, blast)

lemma (*the above rule is not local complete*)
  \<open> Identity_Element\<^sub>I (A \<and>\<^sub>B\<^sub>I B) True \<Longrightarrow> Identity_Element\<^sub>I A True \<or> Identity_Element\<^sub>I B True \<close>
  oops
  (* Auto Quickcheck found a counterexample:
  A = {a\<^sub>3}
  B = {a\<^sub>1} *)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>i\<in>I. Identity_Element\<^sub>I (A i) (P i))
\<Longrightarrow> Identity_Element\<^sub>I (\<big_ast>i\<in>I. A i) (\<forall>i\<in>I. P i)\<close>
  unfolding Identity_Element\<^sub>I_def Mul_Quant_def Transformation_def meta_Ball_def Premise_def
proof clarsimp
  fix v
  assume prems: \<open>(\<And>i. i \<in> I \<Longrightarrow> \<forall>v. v \<Turnstile> A i \<longrightarrow> v = 1 \<and> P i)\<close>
                \<open>v \<Turnstile> prod A I\<close>
     and \<open>finite I\<close>
  show \<open>v = 1 \<and> (\<forall>x\<in>I. P x)\<close>
    by (insert prems; induct rule: finite_induct[OF \<open>finite I\<close>]; clarsimp; fastforce)
qed

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>i\<in>S. Identity_Element\<^sub>E (A i))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> finite S
\<Longrightarrow> Identity_Element\<^sub>E (\<big_ast>i\<in>S. A i) \<close>
  unfolding Identity_Element\<^sub>E_def Mul_Quant_def Transformation_def Premise_def meta_Ball_def
proof clarsimp
  fix v
  assume prems: \<open>(\<And>i. i \<in> S \<Longrightarrow> 1 \<Turnstile> A i)\<close>
     and \<open>finite S\<close>
  show \<open>1 \<Turnstile> prod A S\<close>
    by (insert prems;
        induct rule: finite_induct[OF \<open>finite S\<close>];
        clarsimp;
        (insert mult_1_class.mult_1_left sep_magma_1_right, blast))
qed

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>I (\<half_blkcirc>[C] T) (\<lambda>_. \<not> C) (\<lambda>_. True) \<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Transformation_def Premise_def
  by simp

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>E (\<half_blkcirc>[C] T) (\<lambda>_. \<not> C) \<close>
  unfolding Identity_Element\<^sub>E_def Identity_Elements\<^sub>E_def Transformation_def Premise_def
  by clarsimp



subsection \<open>Equivalence of Objects\<close>

definition Object_Equiv :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Object_Equiv T eq \<longleftrightarrow> (\<forall>x. eq x x) \<and> (\<forall>x y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T))\<close>

text \<open>\<phi>-Deriver usually derives the object reachability relation of \<phi>-type operators generally
  for any variable type operand, but the reachability can be wider on specific type operands, such
  as the reachability \<open>\<lambda>x y. True\<close> of \<open>List(\<circle>)\<close> versus the version \<open>\<lambda>x y. length x = length y\<close> instantiated
  from the general rule \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (List T) (list_rel eq)\<close> by substituting
  \<open>T\<close> for \<open>\<circle>\<close> and \<open>eq\<close> for \<open>(=)\<close>.

  These special `singular` cases are hard to be handled by \<phi>-type algebra who provides a general automation,
  thus demanding user rules for override. Even so, common singular cases can still be handled by ad-hoc
  optimization in the algorithm.

  Generally, when an instantiation of a type operand yields a trivial type relating empty concrete objects,
  a singular case can occur. Therefore, when we infer the reachability of a given type, we can first
  check if it is such a trivial type and if so we derive the wider relation by rule (see \<open>\<A>_singular_unit\<close>).
  In this way, the overall reasoning can still be powerful even when such common singular cases are not considered.


(paper)
\<close>

declare [[
  \<phi>reason_default_pattern \<open>Object_Equiv ?T _\<close> \<Rightarrow> \<open>Object_Equiv ?T _\<close> (100),
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Object_Equiv _ _\<close>
]]

\<phi>reasoner_group object_equiv = (100, [1, 3999]) for \<open>Object_Equiv T eq\<close>
    \<open>Reasoning rules giving the equivalence relation (though is actually a reachability
     relation) of objects of the given \<phi>-type.\<close>
 and object_equiv_cut = (%cutting, [%cutting, %cutting+10]) for \<open>Object_Equiv T eq\<close> in object_equiv
    \<open>Cutting rules for reasonig Object_Equiv\<close>
 and derived_object_equiv = (50, [50,50]) for \<open>Object_Equiv T eq\<close> in object_equiv and < object_equiv_cut
    \<open>Automatically derived rules for Object_Equiv\<close>
 and object_equiv_fallback = (1, [1,1]) for \<open>Object_Equiv T eq\<close> in object_equiv and < derived_object_equiv
    \<open>Fallback rules for reasonig Object_Equiv\<close>

subsubsection \<open>Variants\<close>

consts \<A>_singular_unit :: action

declare [[
  \<phi>reason_default_pattern \<open>Object_Equiv ?T _ @action \<A>_singular_unit\<close> \<Rightarrow>
                          \<open>Object_Equiv ?T _ @action \<A>_singular_unit\<close> (100)
]]

lemma [\<phi>reason %object_equiv_cut+1]:
  \<open> Identity_Elements\<^sub>I T D\<^sub>I P
\<Longrightarrow> Identity_Elements\<^sub>E T D\<^sub>E
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> Object_Equiv T (\<lambda>x y. eq x y \<or> D\<^sub>I x \<and> (P x \<longrightarrow> D\<^sub>E y)) @action \<A>_singular_unit \<close>
  unfolding Object_Equiv_def Identity_Elements\<^sub>E_def Identity_Elements\<^sub>I_def Action_Tag_def
            Transformation_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
  by clarsimp blast

lemma [\<phi>reason %object_equiv_cut]: \<comment> \<open>for non-unital algebras\<close>
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv T eq @action \<A>_singular_unit \<close>
  unfolding Action_Tag_def
  by clarsimp


subsubsection \<open>Its Role in ToA\<close>

lemma [\<phi>reason default %ToA_varify_target_object for \<open>(_::?'c::one BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>
                                              except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Object_Equiv U eq
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq y y' \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def Action_Tag_def Orelse_shortcut_def
            Identity_Elements\<^sub>E_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def
            Ant_Seq_def Premise_def
  by clarsimp

(*
(*TODO: re-enable!*)
lemma [\<phi>reason default %ToA_varify_target_object for \<open>(_::?'c::one BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>
                                              except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Identity_Elements\<^sub>E U D\<^sub>E
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] (D\<^sub>E y')) \<and>\<^sub>\<r> Identity_Element\<^sub>I X P \<or>\<^sub>c\<^sub>u\<^sub>t
    Identity_Elements\<^sub>I U D\<^sub>I P\<^sub>I \<and>\<^sub>\<r>
    Object_Equiv U eq \<and>\<^sub>\<r>
    (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq y y' \<or> D\<^sub>I y \<and> (P\<^sub>I y \<longrightarrow> D\<^sub>E y') \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P)) \<and>\<^sub>\<r>
    (\<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y' \<or> D\<^sub>I y \<and> (P\<^sub>I y \<longrightarrow> D\<^sub>E y'))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def Action_Tag_def Orelse_shortcut_def
            Identity_Elements\<^sub>E_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def
            Ant_Seq_def Premise_def
  by clarsimp blast
*)

lemma ToA_by_Equiv_Class
      [\<phi>reason default %ToA_varify_target_object for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>
                                              except \<open>(_::?'c::one BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>
                                                     \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> Object_Equiv U eq
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> eq_y_y' : eq y y'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq_y_y' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P) \<comment> \<open>the target object is always constrained even when
                                                     it can be variable\<close>
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq_y_y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def Action_Tag_def Simplify_def
  by clarsimp

lemma [\<phi>reason default %ToA_varify_target_object for \<open>(_::?'c::sep_magma_1 BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                              except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Object_Equiv U eq
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq y y' \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  for X :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Object_Equiv_def Transformation_def Premise_def REMAINS_def Action_Tag_def
            Identity_Elements\<^sub>E_def Identity_Elements\<^sub>I_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def
            Orelse_shortcut_def Ant_Seq_def
  by (cases C; clarsimp; metis mult_1_class.mult_1_right sep_magma_1_left)

(*
(*TODO: re-enable!*)
lemma [\<phi>reason default %ToA_varify_target_object for \<open>(_::?'c::sep_magma_1 BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                              except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Identity_Elements\<^sub>E U D\<^sub>E
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[NO_INST] (D\<^sub>E y')) \<and>\<^sub>\<r> (C,R,P) = (True,X,True) \<or>\<^sub>c\<^sub>u\<^sub>t
    Identity_Elements\<^sub>I U D\<^sub>I P\<^sub>I \<and>\<^sub>\<r>
    Object_Equiv U eq \<and>\<^sub>\<r>
    (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq y y' \<or> D\<^sub>I y \<and> (P\<^sub>I y \<longrightarrow> D\<^sub>E y') \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)) \<and>\<^sub>\<r>
    (\<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y' \<or> D\<^sub>I y \<and> (P\<^sub>I y \<longrightarrow> D\<^sub>E y'))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  for X :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Object_Equiv_def Transformation_def Premise_def REMAINS_def Action_Tag_def
            Identity_Elements\<^sub>E_def Identity_Elements\<^sub>I_def Identity_Element\<^sub>E_def Identity_Element\<^sub>I_def
            Orelse_shortcut_def Ant_Seq_def
  by (cases C; clarsimp; metis mult_1_class.mult_1_right sep_magma_1_left)
*)

lemma ToA_by_Equiv_Class'
      [\<phi>reason default %ToA_varify_target_object for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                              except \<open>(_::?'c::sep_magma_1 BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                                                     \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Object_Equiv U eq
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> eq_y_y' : eq y y'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq_y_y' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq_y_y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def REMAINS_def Action_Tag_def Simplify_def
  by (cases C; clarsimp; meson Transformation_def transformation_left_frame)


subsubsection \<open>Extracting Pure Facts\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq x y \<Longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T) \<longrightarrow> P x y @action \<A>EIF)
\<Longrightarrow> Object_Equiv T eq \<longrightarrow> (\<forall>x. eq x x) \<and> (\<forall>x y. eq x y \<longrightarrow> P x y) @action \<A>EIF\<close>
  unfolding Action_Tag_def Object_Equiv_def Premise_def Transformation_def
  by clarsimp

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq x y \<Longrightarrow> P x y \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T) @action \<A>ESC)
\<Longrightarrow> (\<forall>x. eq x x) \<and> (\<forall>x y. eq x y \<longrightarrow> P x y) \<longrightarrow> Object_Equiv T eq @action \<A>ESC\<close>
  unfolding Action_Tag_def Object_Equiv_def Premise_def Transformation_def
  by clarsimp


subsubsection \<open>Reasoning Rules\<close>

lemma Object_Equiv_fallback[\<phi>reason default %object_equiv_fallback]:
  \<open>Object_Equiv T (=)\<close>
  unfolding Object_Equiv_def by simp


(*
lemma [\<phi>reason 800 for \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> _\<close>]:
  " Object_Equiv T eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T"
  unfolding Object_Equiv_def Transformation_def Premise_def by clarsimp*)

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv \<circle> (\<lambda>_ _. True) \<close>
  unfolding Object_Equiv_def Transformation_def
  by simp

lemma [\<phi>reason %object_equiv_cut]:
  \<open> (\<And>a. Object_Equiv (\<lambda>x. S x a) (R a))
\<Longrightarrow> Object_Equiv (\<lambda>x. ExSet (S x)) (\<lambda>x y. \<forall>a. R a x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp; blast)

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv S R
\<Longrightarrow> Object_Equiv (\<lambda>x. S x \<s>\<u>\<b>\<j> P x) (\<lambda>x y. P x \<longrightarrow> R x y \<and> P y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. S1 x \<and>\<^sub>B\<^sub>I S2 x) (\<lambda>x y. R1 x y \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

lemma [\<phi>reason %object_equiv_cut]:
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

lemma [\<phi>reason %object_equiv_cut]:
  \<open> (\<And>a. Object_Equiv (\<lambda>x. S x a) (R a))
\<Longrightarrow> Object_Equiv (\<lambda>x. AllSet (S x)) (\<lambda>x y. \<forall>a. R a x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp simp add: AllSet_expn; blast)

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. S1 x * S2 x) (\<lambda> x y. R1 x y \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp simp add: set_mult_expn; blast)

(* \<comment> \<open>derived automatically later\<close>
lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv T\<^sub>a Eq\<^sub>a
\<Longrightarrow> Object_Equiv T\<^sub>b Eq\<^sub>b
\<Longrightarrow> Object_Equiv (T\<^sub>a \<^emph> T\<^sub>b) (\<lambda>(x\<^sub>a, x\<^sub>b) (y\<^sub>a, y\<^sub>b). Eq\<^sub>a x\<^sub>a y\<^sub>a \<and> Eq\<^sub>b x\<^sub>b y\<^sub>b) \<close>
  unfolding Object_Equiv_def Transformation_def
  by (clarsimp simp add: set_mult_expn; blast)
*)

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

lemma [\<phi>reason %object_equiv_cut]:
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


lemma Object_Equiv_Mul_Quant[\<phi>reason %object_equiv_cut]:
  \<open> (\<forall>i x. eq i x x)
\<Longrightarrow> (\<And>i\<in>S. Object_Equiv (\<lambda>x. A x i) (eq i))
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


section \<open>Reasoning\<close>

ML_file \<open>library/syntax/Phi_Syntax0.ML\<close>

subsubsection \<open>Falling Lattice of Transformations\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason default %ToA_falling_latice-1]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def by blast

lemma [\<phi>reason default %ToA_falling_latice+3]:
  \<open> \<g>\<u>\<a>\<r>\<d> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, undefined) \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P\<close>
  unfolding \<r>Guard_def
  by simp

lemma [\<phi>reason default %ToA_falling_latice+2]:
  \<open> x \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> prod.swap x \<Ztypecolon> Y \<^emph>[True] X \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Cond_\<phi>Prod_def \<phi>Prod_def \<phi>Type_def Transformation_def
  by (cases x; simp add: mult.commute)

lemma [\<phi>reason default %ToA_falling_latice+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> Push_Envir_Var prove_obligations_in_time True \<and>\<^sub>\<r>
         Identity_Element\<^sub>I (fst x \<Ztypecolon> T) P \<and>\<^sub>\<r>
         Pop_Envir_Var prove_obligations_in_time
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  \<comment> \<open>the transformation from T to U fails, and the algebra is non-commutative, nor any methods of a higher priority,
      so \<open>T\<close> or \<open>U\<close> can only be identity if the reasoning can continue\<close>
  unfolding \<r>Guard_def Ant_Seq_def Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp; fastforce)

lemma [\<phi>reason default %ToA_falling_latice]:
  \<open> Identity_Element\<^sub>E (one \<Ztypecolon> U)
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (one, fst x) \<Ztypecolon> U \<^emph>[True] T\<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding \<r>Guard_def Ant_Seq_def Identity_Element\<^sub>E_def Transformation_def Premise_def
  by (clarsimp; force)

(*
lemma [\<phi>reason default %ToA_falling_latice+2]:
  \<open> \<g>\<u>\<a>\<r>\<d> Push_Envir_Var prove_obligations_in_time True \<and>\<^sub>\<r>
         Identity_Element\<^sub>I (fst x \<Ztypecolon> T) P \<and>\<^sub>\<r>
         Pop_Envir_Var prove_obligations_in_time
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P\<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding \<r>Guard_def Ant_Seq_def Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp; fastforce)

lemma [\<phi>reason default %ToA_falling_latice+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> Push_Envir_Var prove_obligations_in_time True \<and>\<^sub>\<r>
         Identity_Element\<^sub>E (one \<Ztypecolon> U) \<and>\<^sub>\<r>
         Pop_Envir_Var prove_obligations_in_time \<and>\<^sub>\<r>
         (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[MODE_SAT] y = (one, fst x))
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[True] T\<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding \<r>Guard_def Ant_Seq_def Identity_Element\<^sub>E_def Transformation_def Premise_def
  by (clarsimp; force)
*)

(*
declare [[\<phi>reason default %ToA_falling_latice + 1
          ToA_falling_lattice_SE_1 ToA_falling_lattice_SE_2
          for \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]]*)


lemma [\<phi>reason default %ToA_falling_latice except \<open>(_ :: ?'a::sep_magma_1 BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (x, w) \<Ztypecolon> T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yr \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst yr \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] snd yr \<Ztypecolon> R \<w>\<i>\<t>\<h> P \<close>
  unfolding Premise_def Try_def
  by (cases C; clarsimp simp add: \<phi>Some_transformation_strip \<phi>Prod_expn'')

lemma [\<phi>reason default %ToA_falling_latice+1]:
  \<open> (x, w) \<Ztypecolon> T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yr \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> if C\<^sub>W then Identity_Element\<^sub>E (w \<Ztypecolon> W) else True
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst yr \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] snd yr \<Ztypecolon> R \<w>\<i>\<t>\<h> P \<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding Premise_def Identity_Element\<^sub>E_def Try_def
  by (cases C; cases C\<^sub>W; clarsimp simp add: \<phi>Some_transformation_strip \<phi>Prod_expn'' \<phi>Prod_expn';
      metis mk_elim_transformation mult_1_class.mult_1_left transformation_right_frame)

lemma [\<phi>reason %ToA_red for \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                         except \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
      \<comment> \<open>\<^prop>\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R\<close> is invalid when \<open>T \<noteq> (_ \<^emph>[_] _)\<close>. The rule corrects
          such mistake eagerly (though may affect the overall performance).\<close>
  \<open> (x, undefined) \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> Cw
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Premise_def
  by simp

subsubsection \<open>Reflexive Transformation\<close>

paragraph \<open>When the target and the source are either alpha-equivalent or unified\<close>

text \<open>Applying reflexive transformation on alpha-equivalent couples of source and target is safe,
so be applied of high priority.
In contrast, unification by reflexive transformation is aggressive. Therefore, they are applied
only when no other rules are applicable.\<close>

declare [[\<phi>trace_reasoning = 1]]

(*TODO: Auto_Transform_Hint*)

declare transformation_refl [\<phi>reason %ToA_refl for \<open>?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<w>\<i>\<t>\<h> _\<close>
                                                   \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?T \<w>\<i>\<t>\<h> _\<close>]

lemma [\<phi>reason default %ToA_unified_refl for \<open>?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A' \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = A'
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<close>
  unfolding Premise_def \<r>Guard_def
  by simp


lemma transformation_refl_assigning_remainder [\<phi>reason %ToA_assigning_var for \<open>_ * ?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _ \<close>
                                                                \<open>_ * (_ \<Ztypecolon> ?T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open>R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R\<close>
  unfolding REMAINS_def
  by simp

lemma [\<phi>reason default %ToA_unified_refl for \<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = A'
\<Longrightarrow> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R\<close>
  unfolding Premise_def REMAINS_def \<r>Guard_def
  by simp


lemma transformation_refl_with_remainder [\<phi>reason %ToA_assigning_var for \<open>?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                                           \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open>A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top>\<close>
  by simp

lemma [\<phi>reason default %ToA_unified_refl for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A = A'
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top>\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma transformation_refl_assigning_W [\<phi>reason %ToA_assigning_var]:
  \<open>x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x, undefined) \<Ztypecolon> (T \<^emph> U) \<^emph>[False] \<top>\<^sub>\<phi>\<close>
  by simp

lemma [\<phi>reason default %ToA_unified_refl for \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> T = T'
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[True] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x, undefined) \<Ztypecolon> (T' \<^emph> U) \<^emph>[False] \<top>\<^sub>\<phi> \<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma transformation_refl_assigning_R [\<phi>reason %ToA_assigning_var]:
  \<open> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst x \<Ztypecolon> T \<^emph>[True] U\<close>
  by simp

lemma [\<phi>reason default %ToA_unified_refl for \<open>_ \<Ztypecolon> (_ \<^emph> _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> T = T'
\<Longrightarrow> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst x \<Ztypecolon> T' \<^emph>[True] U\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma transformation_refl_with_WR [\<phi>reason %ToA_assigning_var+1]:
        \<comment> \<open>Higher than \<open>transformation_refl\<close> to set the condition variable Cr\<close>
  \<open> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi>\<close>
  by simp

lemma [\<phi>reason default %ToA_unified_refl+1 for \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> T = T'
\<Longrightarrow> May_Assign (snd x) undefined
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T' \<^emph>[False] \<top>\<^sub>\<phi>\<close>
  unfolding Premise_def \<r>Guard_def
  by simp


paragraph \<open>When the target is a schematic variable\<close>

text \<open>Schematic variables occurring in source are assigned with zeros, and is
  covered by \<section>\<open>Phi_BI/Bottom/Transformation_Rules\<close>\<close>

ML \<open>
(* (\<And>x. X x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> P) where ?Y is a variable.
   When X contains some quantified variables \<open>x\<close> that do not parameterize ?Y, the procedure
   existentially qualifies X, and assign \<open>\<exists>x. X x\<close> to ?Y.
   cannot work on \<open>_ \<^emph>[_] _\<close> (*TODO, but the thing is there is no type embedding of existence,
                                     unless we use \<Sigma> and \<S>, but... mmmmm.... well, a lot of work.*)
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

\<phi>reasoner_ML transformation_refl_var %ToA_assigning_var (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm transformation_refl}, SOME @{thm ExSet_transformation_I}, I, I
      ) ctxt thm) \<close>

\<phi>reasoner_ML transformation_refl_var_R %ToA_assigning_var (\<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm transformation_refl_assigning_remainder}, SOME @{thm ExSet_transformation_I_R},
          (fn R $ A => A), (fn _ (*REMAINS*) $ A $ _ $ _ => A)
      ) ctxt thm) \<close>

\<phi>reasoner_ML transformation_refl_var_R' %ToA_assigning_var+1 (\<open>_ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _ \<w>\<i>\<t>\<h> _\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm transformation_refl_with_remainder}, SOME @{thm ExSet_transformation_I_R},
          I, (fn _ (*REMAINS*) $ A $ _ $ _ => A)
      ) ctxt thm) \<close>

text \<open>Here, we assign the semantics of schematic variables occurring in targets and sources to be,
  a wild-card for any single separation item.\<close>

declare transformation_refl_assigning_W [\<phi>reason %ToA_assigning_var for \<open>_ \<Ztypecolon> ?var \<^emph>[True] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph> _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]
        transformation_refl_assigning_R [\<phi>reason %ToA_assigning_var for \<open>_ \<Ztypecolon> (_ \<^emph> _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?var \<^emph>[True] _ \<w>\<i>\<t>\<h> _\<close>]
        transformation_refl_with_WR [\<phi>reason %ToA_assigning_var+1 for \<open>_ \<Ztypecolon> ?var \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                                                      \<open>_ \<Ztypecolon> _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?var \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]
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

subsubsection \<open>Basic Transformation Rules\<close>

paragraph \<open>Plainize\<close>

lemma [\<phi>reason %ToA_normalizing]:
  " R * T1 * T2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (T1 * T2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason %ToA_normalizing]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * X1 * X2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * (X1 * X2) \<w>\<i>\<t>\<h> P"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason %ToA_normalizing]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X3 * X1 * X2 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X3 * (X1 * X2) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding mult.assoc[symmetric] .


paragraph \<open>Splitting Separation Assertion in Target\<close>

lemma [\<phi>reason %ToA_splitting_target except \<open>(_ :: ?'a::sep_magma_1 BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<w>\<i>\<t>\<h> P1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y * X \<w>\<i>\<t>\<h> P1 \<and> P2"
  unfolding Action_Tag_def REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def
  by (cases C\<^sub>R; clarsimp; force)

lemma [\<phi>reason %ToA_splitting_target]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<longrightarrow> (if C\<^sub>R then (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P2)
                            else Identity_Element\<^sub>E Y \<and>\<^sub>\<r> P2 = True))
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y * X \<w>\<i>\<t>\<h> P1 \<and> P2"
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def
            Identity_Element\<^sub>E_def Ant_Seq_def
  by (cases C\<^sub>R; clarsimp; force)

lemma [\<phi>reason %ToA_splitting_target except \<open>(_ :: ?'a::sep_semigroup BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R1 \<w>\<i>\<t>\<h> P1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<Longrightarrow> R1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y * X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P1 \<and> P2"
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def
  by (cases C; clarsimp; metis sep_disj_multD2 sep_disj_multI2 sep_mult_assoc')

lemma [\<phi>reason %ToA_splitting_target]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R1 \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<Longrightarrow> if C\<^sub>R then (R1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P2)
                          else Identity_Element\<^sub>E Y \<and>\<^sub>\<r> (P2, C, R') = (True, False, \<top>))
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y * X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P1 \<and> P2"
  for A :: \<open>'a::{sep_semigroup, sep_magma_1} BI\<close>
  unfolding REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def
            Identity_Element\<^sub>E_def Ant_Seq_def
  by ((cases C; cases C\<^sub>R; clarsimp),
      smt (verit, best) sep_disj_multD2 sep_disj_multI2 sep_mult_assoc,
      blast,
      metis mult_1_class.mult_1_left sep_magma_1_right)

lemma [\<phi>reason %ToA_splitting_target+1]:
  " A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R1 \<w>\<i>\<t>\<h> P1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<longrightarrow> (R1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y * X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<w>\<i>\<t>\<h> P1 \<and> P2"
  for A :: \<open>'a::{sep_semigroup, sep_magma_1} BI\<close>
  unfolding Premise_def
  by (simp, metis (no_types, lifting) mult.assoc transformation_right_frame transformation_trans)
  


subsection \<open>Normalization of Assertions\<close>

subsubsection \<open>Declaring Simpsets\<close>

consts assertion_simps :: \<open>mode \<Rightarrow> mode\<close>
       SOURCE :: mode
       TARGET :: mode

ML \<open>
structure Assertion_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>assertion_simps\<close>
  val comment = "Simplification rules normalizing an assertion. \
                       \It is applied before NToA process."
  val attribute = NONE
  val post_merging = I
)

val _ = Theory.setup (Context.theory_map (Assertion_SS.map (fn ctxt =>
      (ctxt addsimprocs [\<^simproc>\<open>NO_MATCH\<close>, \<^simproc>\<open>defined_Ex\<close>, \<^simproc>\<open>HOL.defined_All\<close>,
                         \<^simproc>\<open>defined_all\<close>, \<^simproc>\<open>defined_Collect\<close>, \<^simproc>\<open>Set.defined_All\<close>,
                         \<^simproc>\<open>Set.defined_Bex\<close>, \<^simproc>\<open>unit_eq\<close>, \<^simproc>\<open>case_prod_beta\<close>,
                         \<^simproc>\<open>case_prod_eta\<close>, \<^simproc>\<open>Collect_mem\<close>,
                         Phi_Conv.move_Ex_for_set_notation]
            addsimps @{thms' Sum_Type.sum.case HOL.simp_thms})
          (*|> Simplifier.add_cong @{thm' Subjection_cong}*)
    )))

structure Assertion_SS_Source = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>assertion_simps_source\<close>
  val comment = "Simp rules normalizing particularly source part of an assertion."
  val attribute = NONE
  val post_merging = I
)

val _ = Theory.setup (Context.theory_map (Assertion_SS_Source.map (fn ctxt =>
      ctxt addsimps @{thms' ExSet_simps_ex}
        |> Simplifier.add_cong @{thm' Subjection_cong}
    )))

structure Assertion_SS_Target = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>assertion_simps_target\<close>
  val comment = "Simp rules normalizing particularly target part of an assertion."
  val attribute = NONE
  val post_merging = I
)

\<close>

lemmas [assertion_simps] =
  (*algebras*)
  mult_zero_right[where 'a=\<open>'a::sep_magma BI\<close>] mult_zero_left[where 'a=\<open>'a::sep_magma BI\<close>]
  mult_1_right[where 'a=\<open>'a::sep_magma_1 BI\<close>]
  mult_1_left[where 'a=\<open>'a::sep_magma_1 BI\<close>]
  add_0_right[where 'a=\<open>'a::sep_magma BI\<close>] add_0_left[where 'a=\<open>'a::sep_magma BI\<close>]
  zero_fun zero_fun_def[symmetric, where 'b=\<open>'a::sep_magma BI\<close>]
  plus_fun[where 'a=\<open>'a::sep_magma BI\<close>]
  distrib_right[where 'a=\<open>'a::sep_semigroup BI\<close>]
  mult.assoc[symmetric, where 'a=\<open>'a::sep_semigroup BI\<close>]
  bot_eq_BI_bot

  (*BI connectives*)
  Subjection_Subjection Subjection_Zero Subjection_True Subjection_Flase
  Subjection_times Subjection_addconj

  ExSet_simps

  sep_quant_subjection sep_quant_ExSet

  \<phi>Prod_expn'' \<phi>Prod_expn'
  REMAINS_simp(2)
  HOL.if_True HOL.if_False

  \<phi>Bot.unfold \<phi>Any.unfold

lemmas [assertion_simps_source] =
  ExSet_times_left ExSet_times_right ExSet_adconj ExSet_addisj

  REMAINS_simp(1)

  sep_quant_sep

lemmas [assertion_simps_target] =
  sep_quant_sep[symmetric]

simproc_setup defined_ExSet ( \<open>ExSet A\<close> )
  = \<open>fn _ => fn ctxt => fn ctm =>
      case Thm.term_of ctm
        of Const(\<^const_name>\<open>ExSet\<close>, _) $ Abs (_, _, Const(\<^const_name>\<open>Subjection\<close>, _) $ assn $ P) =>
      let val Const(\<^const_name>\<open>ExSet\<close>, _) $ X = Thm.term_of ctm
          val chk_bound_only_objs = Phi_Syntax.forall_item_of_assertion (
                  fn (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T) => not (Term.is_dependent T)
                   | X => not (Term.is_dependent X)
                )
          val rule = case P
                       of Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _ =>
                            SOME @{thm' ExSet_simps_ex(1)}
                        | Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ Bound 0 =>
                            SOME @{thm' ExSet_simps_ex(2)}
                        | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ _) $ _ =>
                            SOME @{thm' ExSet_simps_ex(3)}
                        | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ Bound 0) $ _ =>
                            SOME @{thm' ExSet_simps_ex(4)}
                        | _ => NONE
       in if chk_bound_only_objs assn
       then Option.mapPartial (fn rule' => try (Conv.rewr_conv rule') ctm) rule
       else NONE
      end
        | _ => NONE\<close>

setup \<open>Context.theory_map (Assertion_SS.map (fn ctxt =>
    ctxt addsimprocs [@{simproc defined_ExSet}]))\<close>

lemmas [\<phi>programming_simps] = plus_fun[where 'a=\<open>'a::sep_magma BI\<close>]


subsubsection \<open>Reasoners\<close>

\<phi>reasoner_ML assertion_simp_source 1300
  (\<open>Simplify (assertion_simps SOURCE) ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Source.get' ctxt)) {fix_vars=false}) o snd\<close>

\<phi>reasoner_ML assertion_simp_target 1300
  (\<open>Simplify (assertion_simps TARGET) ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Target.get' ctxt)) {fix_vars=false}) o snd\<close>

\<phi>reasoner_ML assertion_simp 1200
  (\<open>Premise (assertion_simps _) _\<close> | \<open>Simplify (assertion_simps ?ANY) ?X' ?X\<close> )
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) Assertion_SS.get' {fix_vars=false}) o snd\<close>


subsubsection \<open>Normalized Transformation\<close>

consts NToA' :: \<open>bool \<comment> \<open>whether to reason deeper transformation for each desired \<phi>-type
                          by invoking more time-consuming reasoning process,
                          or just apply unification to match the desired.\<close>
              \<Rightarrow> mode\<close>
      \<comment> \<open>Normalized ToA reasoning, the usual ToA reasoning having simplification and other
          normalization at the beginning.\<close>

text \<open>The boolean flag indicates whether to reason the transformation of \<phi>-types in depth.
For \<open>X\<^sub>1 * \<cdots> * X\<^sub>n \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<^sub>1 * \<cdots> * Y\<^sub>m @action NToA' ?flag\<close>,

\<^item> If the flag is turned on, for every desired \<phi>-Type \<^term>\<open>Y\<^sub>i\<close>, the reasoner
  infers in depth whether some source \<phi>-Type \<^term>\<open>X\<^sub>j\<close> can be transformed into \<^term>\<open>Y\<^sub>i\<close>,
  by invoking any configured reasoning rules bound on the type of \<^term>\<open>Y\<^sub>i\<close>.

\<^item> If the flag is turned off, such in-depth inference is not applied, so the
  reasoning succeeds only if for every desired \<phi>-Type \<^term>\<open>Y\<^sub>i\<close> there is another
  \<^term>\<open>X\<^sub>j\<close> that unifies \<^term>\<open>Y\<^sub>i\<close>.

The the flag is turned off, obviously the performance can be improved a lot though
the reasoning is weaker.
\<close>

abbreviation \<open>NToA \<equiv> NToA' True\<close>

paragraph \<open>Major Implementation\<close>

subparagraph \<open>Short-cuts\<close>

lemma [\<phi>reason %ToA_refl for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P @action NToA' ?mode\<close>]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action NToA' mode\<close>
  unfolding Action_Tag_def using transformation_refl .

lemma [\<phi>reason %ToA_red for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<s>\<u>\<b>\<j> True \<w>\<i>\<t>\<h> ?P @action NToA' ?mode\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action NToA' mode
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> True \<w>\<i>\<t>\<h> P @action NToA' mode\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason %ToA_normalizing for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y @action NToA' _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Any @action NToA' deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action NToA' deep\<close>
  unfolding Action_Tag_def
  by (simp add: transformation_weaken)

subparagraph \<open>ML\<close>

consts ToA_flag_deep :: bool

lemma "_NToA_init_":
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Simplify_def Identity_Element\<^sub>I_def
  by simp

lemma "_NToA_init_having_Q_":
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Simplify_def Identity_Element\<^sub>I_def Inhabited_def Premise_def Transformation_def
  by clarsimp blast

ML \<open>val augment_ToA_by_implication = Attrib.setup_config_bool \<^binding>\<open>augment_ToA_by_implication\<close> (K false)\<close>

\<phi>reasoner_ML NToA_init 2000 (\<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?var_P @action NToA' _\<close>) = \<open>
fn (_, (ctxt0,sequent)) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ ( _ (*Action_Tag*) $ _ $ (Const(\<^const_name>\<open>NToA'\<close>, _) $ deep))
         = Thm.major_prem_of sequent
      val sequent = @{thm' Action_Tag_I} RS sequent

      val ctxt = Context.proof_map (PLPR_Env.push \<^const_name>\<open>ToA_flag_deep\<close> deep) ctxt0
      val sequent = Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
            let val src_ctxt = Assertion_SS_Source.enhance (Assertion_SS.equip ctxt)
                val target_ctxt = Assertion_SS_Target.enhance (Assertion_SS.equip ctxt)
             in Phi_Syntax.transformation_conv (Simplifier.rewrite src_ctxt)
                                               (Simplifier.rewrite target_ctxt)
                                               Conv.all_conv
            end) ctxt
          ) 1 sequent

      val rule = case (deep, Config.get ctxt0 augment_ToA_by_implication)
                   of (\<^Const>\<open>True\<close>, true) => @{thm "_NToA_init_having_Q_"}
                    | _ => @{thm "_NToA_init_"}
   in SOME ((ctxt, rule RS sequent), Seq.empty)
  end)
\<close>

hide_fact "_NToA_init_"

subsection \<open>Entry Point of Separation Extraction\<close>

text \<open>From \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close> to \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R\<close>\<close>

lemma enter_SEi:
  \<open> (x,w) \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P1
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h> P2) else (P2, Crr) = (True, False)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def REMAINS_def Simplify_def Try_def
  apply (cases Cw; cases Cr; cases Crr; cases y;
         simp add: \<phi>Some_\<phi>Prod \<phi>Some_transformation_strip \<phi>Prod_expn')

  subgoal premises prems for a b
    by (insert prems(2)[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
               prems(1)[THEN transformation_left_frame, where R=RR],
        simp add: mult.assoc transformation_trans)

  subgoal premises prems for a b
    by (insert prems(2)[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
               prems(1),
        simp add: mult.assoc transformation_trans)

  subgoal premises prems for a b
    by (insert prems(2)[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
               prems(1)[THEN transformation_left_frame, where R=RR],
        simp add: mult.assoc transformation_trans)

  subgoal premises prems for a b
    by (insert prems(2)[THEN transformation_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
               prems(1),
        simp add: mult.assoc transformation_trans)

  subgoal premises prems for a b
    by (insert prems(1)[THEN transformation_left_frame, where R=A],
        simp add: mult.assoc transformation_trans)

  subgoal premises prems for a b
    by (insert prems(1)[THEN transformation_left_frame, where R=A],
        simp add: mult.assoc transformation_trans) .

(* TODO: DO NOT REMOVE
lemma enter_SEi_TH:
  \<open> Try Cp ((x,w) \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'1 \<Ztypecolon> U' \<^emph>[Cr] R') (x'1 \<Ztypecolon> T' \<^emph>[Cw] W') \<and> P1)
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h>
                    Auto_Transform_Hint (y'2 \<Ztypecolon> W') A' \<and> P2)
          else (P2, Crr) = (True, False)
\<Longrightarrow> if Cw then ATH = (A' * (x'3 \<Ztypecolon> T')) else ATH = (x'3 \<Ztypecolon> T')
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'3 \<Ztypecolon> U) ATH \<and> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEi .*)

(* not used
lemma enter_SEa:
  \<open> C = True \<and>\<^sub>\<r> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P) \<and>\<^sub>\<r> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> Q) \<or>\<^sub>c\<^sub>u\<^sub>t 
    (C, y) = (False, fst y') \<and>\<^sub>\<r>
    ((x, w) \<Ztypecolon> T \<^emph>[True] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P) \<and>\<^sub>\<r>
    (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<and> Q \<close>
  unfolding Action_Tag_def Orelse_shortcut_def Ant_Seq_def
  by (cases C; simp add: \<phi>Some_\<phi>Prod \<phi>Some_transformation_strip;
      clarsimp simp add: Transformation_def; blast)

(*TODO:
lemma enter_SEa_TH:
  \<open> (C, ATH) = (True, x'2 \<Ztypecolon> T') \<and>\<^sub>\<r>
    (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> U') (x'2 \<Ztypecolon> T') \<and> P) \<and>\<^sub>\<r>
    (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> Q)
    \<or>\<^sub>c\<^sub>u\<^sub>t
    (C, ATH, y) = (False, A' * (x'2) \<Ztypecolon> T', fst y') \<and>\<^sub>\<r>
    ((x, w) \<Ztypecolon> T \<^emph>[True] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> U' \<^emph>[False] \<top>\<^sub>\<phi>) (x'1 \<Ztypecolon> T' \<^emph>[True] W') \<and> P) \<and>\<^sub>\<r>
    (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> W') A' \<and> Q)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'2 \<Ztypecolon> U') ATH \<and> P \<and> Q \<close>
  unfolding Action_Tag_def Orelse_shortcut_def Ant_Seq_def Auto_Transform_Hint_def
  by (cases C; simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj \<phi>Some_transformation_strip;
      clarsimp simp add: Transformation_def; blast)
*)
*)

lemma enter_SEbi\<^sub>1:
  \<open> (x, w) \<Ztypecolon> T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P1
\<Longrightarrow> if C\<^sub>R then Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
          else Q = True
\<Longrightarrow> if C\<^sub>W then A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
          else Identity_Element\<^sub>I A P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma_1 set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def Premise_def
            Transformation_def Try_def Ant_Seq_def
  by (cases C\<^sub>W; cases C\<^sub>R; clarsimp; fastforce)

lemma enter_SEbi:
  \<open> (x, w) \<Ztypecolon> T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P1
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<not> C\<^sub>R \<and> C\<^sub>W)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P2 \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def Premise_def
            Transformation_def Try_def Identity_Element\<^sub>E_def Ant_Seq_def
  by (cases C\<^sub>W; cases C\<^sub>R; clarsimp; blast)

(* TODO: DO NOT REMOVE
lemma enter_SEbi_TH:
  \<open> Try Cp ((x, w) \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> U') (x' \<Ztypecolon> T' \<^emph>[C] W') \<and> P1)
\<Longrightarrow> if Cr then Identity_Element\<^sub>I (snd y \<Ztypecolon> \<black_circle> R) Q else Q = True
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (w' \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> U') (A' * (x'' \<Ztypecolon> T')) \<and> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEbi .
*)

ML \<open>
fun SE_entry_point rules thy sequent =
  let val (_, Y, _) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      val ty = Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent)
      val rules = (if Sign.of_sort thy (ty, \<^sort>\<open>sep_magma_1\<close>) then #1 else #2) rules
      fun obj_is_var (Const(\<^const_name>\<open>times\<close>, _) $ _ $ X) = obj_is_var X
        | obj_is_var (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ _) = obj_is_var X
        | obj_is_var (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _) = is_Var (Term.head_of x)
      val rule = (if obj_is_var Y then fst else snd) rules
    (*TODO: val has_auto_hint =
        case P of Const(\<^const_name>\<open>conj\<close>, _) $ (Const(\<^const_name>\<open>Auto_Transform_Hint\<close>, _) $ _ $ _) $ _ => true
                | _ => false
      val rule = (if has_auto_hint then snd else fst) rules*)
   in rule RS sequent
  end

val SE_entry_point_normal = SE_entry_point (
      (@{thm' enter_SEi}, @{thm' ToA_by_Equiv_Class'[OF _ _ enter_SEi]}),
      (@{thm' enter_SEi}, @{thm' ToA_by_Equiv_Class'[OF _ _ enter_SEi]}))

val SE_entry_point_b = SE_entry_point (
      (@{thm' enter_SEbi\<^sub>1}, @{thm' ToA_by_Equiv_Class[OF _ _ enter_SEbi\<^sub>1]}),
      (@{thm' enter_SEbi}, @{thm' ToA_by_Equiv_Class[OF _ _ enter_SEbi]}))
\<close>


\<phi>reasoner_ML \<A>SE_Entry default %ToA_splitting_source (\<open>(_::?'a::sep_semigroup BI) * (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>)
= \<open>fn (_, (ctxt, sequent)) =>
  Seq.make (fn () =>
    let val thy = Proof_Context.theory_of ctxt
     in if Sign.of_sort thy (Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent), \<^sort>\<open>sep_magma\<close>)
        then SOME ((ctxt, SE_entry_point_normal thy sequent), Seq.empty)
        else (warning "The reasoner can barely do nothing for those even are not sep_magma" ;
              NONE)
    end)\<close>

lemma [\<phi>reason %ToA_splitting_source except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ :: ?'a :: sep_semigroup set) \<w>\<i>\<t>\<h> _\<close>]:
  " (C,P) = (True, P1 \<and> P2) \<and> (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P1) \<and> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P2)) \<or>\<^sub>c\<^sub>u\<^sub>t
    C = False \<and> (A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  unfolding Orelse_shortcut_def Transformation_def REMAINS_def Premise_def
  by clarsimp blast

\<phi>reasoner_ML \<A>SEb_Entry default %ToA_splitting_source (\<open>_ * (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (_, (ctxt, sequent)) =>
  Seq.make (fn () =>
    let val thy = Proof_Context.theory_of ctxt
     in if Sign.of_sort thy (Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent), \<^sort>\<open>sep_magma\<close>)
        then SOME ((ctxt, SE_entry_point_b thy sequent), Seq.empty)
        else (warning "The reasoner can barely do nothing for those even are not sep_magma" ;
              NONE)
    end)\<close>

lemma [\<phi>reason default %ToA_falling_latice]: \<comment> \<open>when X fails to match \<open>x \<Ztypecolon> T\<close>\<close>
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> if C\<^sub>R then R'' = (R' * X) else R'' = X
\<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R'' \<w>\<i>\<t>\<h> P \<close>
  for Y :: \<open>'c::sep_ab_semigroup BI\<close>
  by ((cases C\<^sub>R; clarsimp),
      smt (verit, best) mult.commute mult.left_commute transformation_right_frame,
      metis mult.commute transformation_left_frame)

(* TODO:
hide_fact enter_SEb enter_SEb_TH*)



subsection \<open>Supplementary Transformations\<close>

subsubsection \<open>Supplementary for Ex \& Conj \label{supp-ex-conj}\<close>

ML \<open>fun ToA_ex_intro_reasoning (ctxt,sequent) =
  let val (_, X'', _) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      fun parse (Const(\<^const_name>\<open>ExSet\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X) = (false, ty, X)
        | parse (Const(\<^const_name>\<open>REMAINS\<close>, _) $ (Const(\<^const_name>\<open>ExSet\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X) $ _ $ _)
            = (true, ty, X)
        | parse X = parse (Envir.beta_eta_contract X)
      val (has_focus, _, X'1) = parse X''
      val X = case X'1 of Abs (_, _, X) => X | X => Term.incr_boundvars 1 X $ Bound 0
      val ex_var_is_in_obj_only = Phi_Syntax.forall_item_of_assertion_blv (fn lv =>
                                    (fn (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) => not (Term.loose_bvar1 (T, lv))
                                      | A => not (Term.loose_bvar1 (A, lv))))
      val rule0 = if has_focus
                  then if ex_var_is_in_obj_only X
                  then @{thm' ExSet_transformation_I_R[where x=\<open>id c\<close> for c]}
                  else @{thm' ExSet_transformation_I_R}
                  else if ex_var_is_in_obj_only X
                  then @{thm' ExSet_transformation_I[where x=\<open>id c\<close> for c]}
                  else @{thm' ExSet_transformation_I}
   in SOME ((ctxt, rule0 RS sequent), Seq.empty)
  end\<close>

\<phi>reasoner_ML ToA_ex_intro default ! %ToA_inst_qunat (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet _ \<w>\<i>\<t>\<h> _\<close> | \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>fn stat => Seq.make (fn () => ToA_ex_intro_reasoning (snd stat))\<close>

(*diverges to 3 branches, left branch, right branch, and instantiating the Ex in the domain if any. *)
\<phi>reasoner_ML NToA_conj_src ! %ToA_branches  (\<open>_ \<and>\<^sub>B\<^sub>I _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val tail = (case Thm.major_prem_of sequent
                    of _ (*Trueprop*) $ (_ (*Transformation*) $ _ $ (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) $ _) =>
                            if Term.exists_Const (fn (\<^const_name>\<open>Additive_Conj\<close>, _) => true
                                                   | _ => false) X
                            then Seq.make (fn () => ToA_ex_intro_reasoning (ctxt,sequent))
                            else Seq.empty
                     | _ => Seq.empty)
   in SOME ((ctxt, @{thm' NToA_conj_src_A} RS sequent),
        Seq.make (fn () => SOME ((ctxt, @{thm' NToA_conj_src_B} RS sequent), tail)))
  end
  )\<close>


subsubsection \<open>Evaluations\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> (y,x) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> prod.swap (x,y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (f x, y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> apfst f (x,y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, f y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> apsnd f (x,y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> fst (x,y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> y \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> snd (x,y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, z) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (fst (x,y), z) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (y, z) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd (x,y), z) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, y) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x, fst (y, z)) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, z) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x, snd (y, z)) \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

subsubsection \<open>Let\<close>

lemma [\<phi>reason %ToA_red]:
  " T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> Let x T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Let_def .

lemma [\<phi>reason %ToA_red]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U x \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Let x U \<w>\<i>\<t>\<h> P"
  unfolding Let_def .

lemma [\<phi>reason %ToA_red]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Let x U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  unfolding Let_def .

subsubsection \<open>Case Prod\<close>

\<phi>reasoner_group ToA_red_caseprod =
  (%ToA_red, [%ToA_red, %ToA_red+10]) for (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod _ _ \<w>\<i>\<t>\<h> _\<close>, \<open>case_prod _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  \<open>Transformations reducing \<open>case_prod\<close>\<close>

lemma [\<phi>reason %ToA_red_caseprod+10]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f (x,y) \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason %ToA_red_caseprod+10]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f (x,y) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason %ToA_red_caseprod+10]:
  " A x y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> case_prod A (x,y) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason %ToA_red_caseprod]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f (fst xy) (snd xy) \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f xy \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def
  by (cases xy; simp)

lemma [\<phi>reason %ToA_red_caseprod]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f (fst xy) (snd xy) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f xy \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def
  by (cases xy; cases C; simp)

lemma [\<phi>reason %ToA_red_caseprod]:
  " A (fst xy) (snd xy) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> case_prod A xy \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P"
  by (cases xy; simp)


subsubsection \<open>Conditional Branch\<close>

paragraph \<open>Normalization\<close>

lemma [\<phi>reason %ToA_normalizing]:
  \<open> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by (cases C; simp)

text \<open>\<^term>\<open>x \<Ztypecolon> (If C T U) \<^emph>[C\<^sub>W] W\<close> is not reduced because the \<open>C\<^sub>W\<close> and \<open>W\<close> have to be specially assigned.\<close>

lemma [\<phi>reason %ToA_normalizing]: \<comment> \<open>\<open>W\<close> shouldn't contain schematic variable. Why a source can contain
                                      variable?\<close>
  \<open> If C (W * (x \<Ztypecolon> A)) (W * (x \<Ztypecolon> B)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> W * (x \<Ztypecolon> If C A B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by (cases C; simp)

lemma [\<phi>reason %ToA_normalizing]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> If C A B \<w>\<i>\<t>\<h> P\<close>
  by (cases C; simp)

paragraph \<open>Reduction for constant boolean condition\<close>

subparagraph \<open>Source\<close>

lemma NToA_cond_source_A[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> (if C then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> (if C then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_A_ty[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> (if C then T else U) \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B_ty[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> x \<Ztypecolon> U \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> (if C then T else U) \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)


subparagraph \<open>Target\<close>

lemma NToA_cond_target_A[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_B[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_A'[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_B'[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_A_ty[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (if C then T else U) \<^emph>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_B_ty[\<phi>reason %ToA_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (if C then T else U) \<^emph>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp


paragraph \<open>When the condition boolean is a variable\<close>

text \<open>The condition should be regarded as an output, and the reasoning process assigns which
the branch that it chooses to the output condition variable.\<close>

subparagraph \<open>Normalizing\<close>

lemma [\<phi>reason %ToA_red for \<open>If (id ?var) _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> If C T U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> If (id C) T U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<Ztypecolon> If (id ?var) _ _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> x \<Ztypecolon> If C T U \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> If (id C) T U \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If (id ?var) _ _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C A B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If (id C) A B \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (If (id ?var) _ _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (If C A B) \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (If (id C) A B) \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P \<close>
  by simp

subparagraph \<open>Source\<close>

text \<open>the \<open>id ?x\<close> here is the protector generated by instantiating existence in target.\<close>

declare [[\<phi>reason ! %ToA_branches NToA_cond_source_A NToA_cond_source_B
        for \<open>(if ?var_condition then ?A else ?B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P\<close>]]

hide_fact NToA_cond_source_A NToA_cond_source_B

declare [[\<phi>reason ! %ToA_branches NToA_cond_source_A_ty NToA_cond_source_B_ty
      for \<open>_ \<Ztypecolon> (if ?var then _ else _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]]

hide_fact NToA_cond_source_A_ty NToA_cond_source_B_ty


subparagraph \<open>Target\<close>

declare [[\<phi>reason ! %ToA_branches NToA_cond_target_A NToA_cond_target_B
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var_condition then ?A else ?B) \<w>\<i>\<t>\<h> ?P\<close> ]]

hide_fact NToA_cond_target_A NToA_cond_target_B

declare [[\<phi>reason ! %ToA_branches NToA_cond_target_B' NToA_cond_target_A'
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var_condition then ?A else ?B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> ?P\<close> ]]

hide_fact NToA_cond_target_A' NToA_cond_target_B'

declare [[\<phi>reason ! %ToA_branches NToA_cond_target_A_ty NToA_cond_target_B_ty
            for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (if ?var then _ else _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> ]]

hide_fact NToA_cond_target_A_ty NToA_cond_target_B_ty


paragraph \<open>Case Split\<close>

\<phi>reasoner_group ToA_splitting_If = (%ToA_splitting, [%ToA_splitting, %ToA_splitting+1])
                                   for (\<open>If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close>, \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C A B\<close>)
                                    in ToA_splitting
  \<open>ToA splitting \<open>If\<close> in either source or target, into two sub-goals.\<close>

subparagraph \<open>Source\<close>

lemma ToA_cond_branch_src:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma ToA_cond_branch_src_R:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

(*lemma ToA_cond_branch_src_R':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> P = False) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> Q = False) \<or>\<^sub>c\<^sub>u\<^sub>t (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)
*)

lemma [\<phi>reason %ToA_splitting_If]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> (x \<Ztypecolon> T\<^sub>a \<^emph>[C\<^sub>W\<^sub>a] W\<^sub>a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a \<Ztypecolon> U \<^emph>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> (x \<Ztypecolon> T\<^sub>b \<^emph>[C\<^sub>W\<^sub>b] W\<^sub>b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b \<Ztypecolon> U \<^emph>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> x \<Ztypecolon> (If C T\<^sub>a T\<^sub>b) \<^emph>[If C C\<^sub>W\<^sub>a C\<^sub>W\<^sub>b] (If C W\<^sub>a W\<^sub>b) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C y\<^sub>a y\<^sub>b \<Ztypecolon> U \<^emph>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  unfolding Try_def
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

ML \<open>
fun reasoner_ToA_conditioned_subgoals_If ctxt'N (vars,Y,RHS) =
  let val (C, Ya, Yb) = Phi_Help.dest_triop_c \<^const_name>\<open>If\<close> RHS
      val C_term = Thm.term_of C

      val Ya_s = map (fn ((N,i),ty) => Thm.var ((N,i+2), Thm.ctyp_of ctxt'N ty)) vars
      val Yb_s = map (fn ((N,i),ty) => Thm.var ((N,i+3), Thm.ctyp_of ctxt'N ty)) vars 
      val Y_s  = map2 (fn a => fn b =>
                   let val ty = Thm.typ_of_cterm a
                    in Thm.apply (Thm.apply (
                          Thm.apply (Thm.cterm_of ctxt'N \<^Const>\<open>If ty\<close>) C
                        ) a
                        ) b
                   end) Ya_s Yb_s
      val Ya' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Ya_s)) Y
      val Yb' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Yb_s)) Y
      fun mk_inst ctm Y =
        case Thm.term_of ctm
          of _ $ Free _ => mk_inst (Thm.dest_fun ctm) (Thm.lambda (Thm.dest_arg ctm) Y)
           | Var v => (v, Y)
           | _ => error "BUG: reasoner_ToA_conditioned_subgoals"
 
   in (Vars.make (mk_inst Ya Ya' :: mk_inst Yb Yb' :: (vars ~~ Y_s)), C_term)
  end
\<close>


lemma If_distrib_fx:
  \<open>(If C fa fb) (If C va vb) \<equiv> (If C (fa va) (fb vb))\<close>
  unfolding atomize_eq
  by (cases C; simp)

lemma If_distrib_arg:
  \<open>(If C fa fb) a \<equiv> (If C (fa a) (fb a))\<close>
  unfolding atomize_eq
  by (cases C; simp)

\<phi>reasoner_ML \<open>ML (If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> %ToA_splitting_If
             ( \<open>If _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
             | except \<open>If ?var _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
             | except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_branch_src}, @{thm' ToA_cond_branch_src_R},
          (true, @{thms' if_cancel[folded atomize_eq]}, @{thms' if_True if_False}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>


subparagraph \<open>Target\<close>

lemma [\<phi>reason %ToA_splitting_If except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma [\<phi>reason %ToA_splitting_If except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

(*
lemma [\<phi>reason %ToA_splitting_If+1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if _ then _ else _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _ \<w>\<i>\<t>\<h> _\<close>
                    except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)*)

lemma [\<phi>reason %ToA_splitting_If except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (if ?var then _ else _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a \<Ztypecolon> T \<^emph>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b \<Ztypecolon> U \<^emph>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then y\<^sub>a else y\<^sub>b) \<Ztypecolon> (if C then T else U) \<^emph>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  unfolding Try_def Premise_def Orelse_shortcut_def
  by (cases C; simp)


subsubsection \<open>Conditioned Remains\<close>

paragraph \<open>When the conditional boolean is fixed\<close>

\<phi>reasoner_group ToA_constant_remains = (50, [50,60]) for (\<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P\<close>)
                                                      in ToA \<open>\<close>

lemma [\<phi>reason default %ToA_constant_remains+1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] ?var \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Premise_def
  by simp

lemma [\<phi>reason default %ToA_constant_remains+2 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] (?var::?'c::sep_magma_1 BI) \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C\<^sub>R] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> if C\<^sub>R then R = R' else R = 1
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>'c :: sep_magma_1 BI\<close>
  by (cases C\<^sub>R; simp)

lemma [\<phi>reason default %ToA_constant_remains for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_normalizing for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top> \<w>\<i>\<t>\<h> P \<close>
  by simp


paragraph \<open>Reduction\<close>

subparagraph \<open>Source\<close>

lemma ToA_CR_src_A [\<phi>reason %ToA_red]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> R * Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def
  by simp

lemma ToA_CR_src_B [\<phi>reason %ToA_red+10 for \<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                                            \<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def
  by simp

lemma ToA_CR_src_A' [\<phi>reason %ToA_red]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A * (R * Y) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def
  by simp

lemma ToA_CR_src_B' [\<phi>reason %ToA_red+10 for \<open>_ * (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                                             \<open>_ * (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> A * Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def
  by simp


subparagraph \<open>Target\<close>

lemma ToA_CR_target_A [\<phi>reason %ToA_red]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P"
  unfolding \<r>Guard_def Premise_def
  by simp

lemma ToA_CR_target_B [\<phi>reason %ToA_red+10 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                               \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P"
  unfolding \<r>Guard_def Premise_def
  by simp


paragraph \<open>Case Split\<close>

subparagraph \<open>Source\<close>

lemma ToA_cond_remain_src:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<longrightarrow> (B * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)

lemma ToA_cond_remain_src_R:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<longrightarrow> (B * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)

(*
lemma ToA_cond_remain_src_R':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (B * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)
*)

lemma ToA_cond_remain_src_W:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<longrightarrow> (W * (B * A) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (W * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)

lemma ToA_cond_remain_src_WR:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<longrightarrow> (W * (B * A) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (W * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)

(*
lemma ToA_cond_remain_src_WR':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * (B * A) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)
*)


\<phi>reasoner_ML \<open>ML (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> %ToA_splitting (\<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_remain_src}, @{thm' ToA_cond_remain_src_R}, (*@{thm' ToA_cond_remain_src_R'},*)
          (true, @{thms' if_cancel[folded atomize_eq]}, @{thms' if_True if_False}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>

\<phi>reasoner_ML \<open>ML (W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> %ToA_splitting (\<open>_ * (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_remain_src_W}, @{thm' ToA_cond_remain_src_WR}, (*@{thm' ToA_cond_remain_src_WR'},*)
          (true, @{thms' if_cancel[folded atomize_eq]}, @{thms' if_True if_False}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>


subparagraph \<open>Target\<close>

(*TODO: reasoner_ToA_conditioned_subgoals*)
lemma [\<phi>reason %ToA_splitting except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[CCa] RRa \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[CCb] RRb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C CCa CCb] If C RRa RRb \<w>\<i>\<t>\<h> If C P Q\<close>
  unfolding Premise_def Ant_Seq_def Orelse_shortcut_def
  by (cases C; simp)

(*
lemma [\<phi>reason %ToA_splitting+1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _ \<w>\<i>\<t>\<h> _\<close>
                                except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RRa \<w>\<i>\<t>\<h> P)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RRb \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C RRa RRb \<w>\<i>\<t>\<h> If C P Q\<close>
  by (cases C; simp)*)

paragraph \<open>When the condition boolean is a variable\<close>

subparagraph \<open>Normalizing\<close>

lemma [\<phi>reason %ToA_red for \<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[id ?var] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[V] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[id V] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ * (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[id ?var] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[V] R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[id V] R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[id ?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[V] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[id V] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P \<close>
  by simp

subparagraph \<open>Source\<close>

declare [[\<phi>reason ! %ToA_branches ToA_CR_src_A ToA_CR_src_B
        for \<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]]

hide_fact ToA_CR_src_A ToA_CR_src_B

declare [[\<phi>reason ! %ToA_branches ToA_CR_src_A' ToA_CR_src_B'
        for \<open>_ * (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]]

hide_fact ToA_CR_src_A' ToA_CR_src_B'

subparagraph \<open>Target\<close>

declare [[\<phi>reason ! %ToA_branches ToA_CR_target_A ToA_CR_target_B
            for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> ]]

hide_fact ToA_CR_target_A ToA_CR_target_B



subsubsection \<open>Type-embedding of Conditioned Remains\<close>

paragraph \<open>Reduction\<close>

subparagraph \<open>Source\<close>

lemma ToA_CR\<phi>_src_A [\<phi>reason %ToA_red]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> CC
\<Longrightarrow> x \<Ztypecolon> (T1 \<^emph> T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> (T1 \<^emph>[CC] T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def
  by simp

lemma ToA_CR\<phi>_src_B [\<phi>reason %ToA_red+10 for \<open>_ \<Ztypecolon> (_ \<^emph>[False] _) \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                                             \<open>_ \<Ztypecolon> (_ \<^emph>[?var] _) \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> CC
\<Longrightarrow> (fst (fst x), snd x) \<Ztypecolon> T1 \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> (T1 \<^emph>[CC] T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def
  by simp

subparagraph \<open>Target\<close>

lemma ToA_CR\<phi>_target_A [\<phi>reason %ToA_red]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> CC
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> R) \<^emph>[C] R2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph>[CC] R) \<^emph>[C] R2 \<w>\<i>\<t>\<h> P"
  unfolding \<r>Guard_def Premise_def
  by simp

lemma ToA_CR\<phi>_target_B [\<phi>reason %ToA_red+10 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[False] _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                                 \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[?var] _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  " \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> CC
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[C] R2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst y, undefined), snd y) \<Ztypecolon> (U \<^emph>[CC] R) \<^emph>[C] R2 \<w>\<i>\<t>\<h> P"
  unfolding \<r>Guard_def Premise_def
  by (cases C; simp add: \<phi>Prod_expn' \<phi>Prod_expn'')

paragraph \<open>Case Split\<close>

subparagraph \<open>Source\<close>

lemma [\<phi>reason %ToA_splitting]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and>\<^sub>\<r> (y\<^sub>a,P,Cwa,W\<^sub>a,C\<^sub>R\<^sub>a,R\<^sub>a,y\<^sub>a) = (undefined, False, True, \<bottom>\<^sub>\<phi>, True, \<bottom>\<^sub>\<phi>, undefined)) \<or>\<^sub>c\<^sub>u\<^sub>t
                      (x \<Ztypecolon> (T1 \<^emph> T2) \<^emph>[Cwa] W\<^sub>a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a \<Ztypecolon> U \<^emph>[C\<^sub>R\<^sub>a] R\<^sub>a \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and>\<^sub>\<r> (y\<^sub>b,Q,Cwb,W\<^sub>b,C\<^sub>R\<^sub>b,R\<^sub>b,y\<^sub>b) = (undefined, False, True, \<bottom>\<^sub>\<phi>, True, \<bottom>\<^sub>\<phi>, undefined)) \<or>\<^sub>c\<^sub>u\<^sub>t
                      (apfst fst x \<Ztypecolon> T1 \<^emph>[Cwb] W\<^sub>b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b \<Ztypecolon> U \<^emph>[C\<^sub>R\<^sub>b] R\<^sub>b \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> x \<Ztypecolon> (T1 \<^emph>[C] T2) \<^emph>[If C Cwa Cwb] If C W\<^sub>a W\<^sub>b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C y\<^sub>a y\<^sub>b \<Ztypecolon> U \<^emph>[If C C\<^sub>R\<^sub>a C\<^sub>R\<^sub>b] If C R\<^sub>a R\<^sub>b \<w>\<i>\<t>\<h> If C P Q \<close>
  unfolding Orelse_shortcut_def Premise_def Ant_Seq_def
  by (cases C; simp ; cases Cwb; simp add: \<phi>Prod_expn'' \<phi>Prod_expn')


(*
lemma ToA_cond_septy_src:
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> P = False) \<or>\<^sub>c\<^sub>u\<^sub>t
                      (x \<Ztypecolon> (T1 \<^emph> T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> Q = False) \<or>\<^sub>c\<^sub>u\<^sub>t
                      ((fst (fst x), snd x) \<Ztypecolon> T1 \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> x \<Ztypecolon> (T1 \<^emph>[C] T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; cases Cw;
      simp add: Orelse_shortcut_def Premise_def \<phi>Prod_expn'' \<phi>Prod_expn')

lemma ToA_cond_septy_src_R:
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = (False,0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                      (x \<Ztypecolon> (T1 \<^emph> T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = (False,0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                      ((fst (fst x), snd x) \<Ztypecolon> T1 \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> x \<Ztypecolon> (T1 \<^emph>[C] T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; cases Cw;
      simp add: Orelse_shortcut_def Premise_def \<phi>Prod_expn'' \<phi>Prod_expn')

(*
lemma ToA_cond_septy_src_R':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                      (x \<Ztypecolon> (T1 \<^emph> T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                      ((fst (fst x), snd x) \<Ztypecolon> T1 \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> x \<Ztypecolon> (T1 \<^emph>[C] T2) \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; cases Cw;
      simp add: Orelse_shortcut_def Premise_def \<phi>Prod_expn'' \<phi>Prod_expn')
*)

\<phi>reasoner_ML \<open>ML (x \<Ztypecolon> (T1 \<^emph>[C] T2) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> %ToA_splitting (\<open>_ \<Ztypecolon> (_ \<^emph>[_] _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_septy_src}, @{thm' ToA_cond_septy_src_R}, (*@{thm' ToA_cond_septy_src_R'},*)
          (\<^const_name>\<open>If\<close>, 3, @{thms' if_cancel[folded atomize_eq]}, @{thms' If_distrib_fx if_distrib}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>
*)

subparagraph \<open>Target\<close>

lemma [\<phi>reason %ToA_splitting except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[?var] _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and>\<^sub>\<r> (y\<^sub>a,CCa,RRa,P) = (undefined,True,\<bottom>\<^sub>\<phi>,False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                     (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a \<Ztypecolon> (U \<^emph> R) \<^emph>[CCa] RRa \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and>\<^sub>\<r> (y\<^sub>b,CCb,RRb,Q) = (undefined,True,\<bottom>\<^sub>\<phi>,False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                     (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b \<Ztypecolon> U \<^emph>[CCb] RRb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then y\<^sub>a else apfst (\<lambda>x. (x, undefined)) y\<^sub>b) \<Ztypecolon> (U \<^emph>[C] R) \<^emph>[If C CCa CCb] If C RRa RRb \<w>\<i>\<t>\<h> If C P Q\<close>
  unfolding Ant_Seq_def Orelse_shortcut_def Premise_def
  by (cases C; simp; cases CCb; simp add: \<phi>Prod_expn' \<phi>Prod_expn'')

(*
lemma [\<phi>reason %ToA_splitting+1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<^emph>[True] _ \<w>\<i>\<t>\<h> _\<close>
                                except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[?var] _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ya \<Ztypecolon> (U \<^emph> R) \<^emph>[True] RRa \<w>\<i>\<t>\<h> P)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yb \<Ztypecolon> U \<^emph>[True] RRb \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then ya else ((fst yb, undefined), snd yb)) \<Ztypecolon> (U \<^emph>[C] R) \<^emph>[True] If C RRa RRb \<w>\<i>\<t>\<h> If C P Q\<close>
  by (cases C; simp add: \<phi>Prod_expn' \<phi>Prod_expn'')*)

paragraph \<open>When the condition boolean is a variable\<close>

subparagraph \<open>Source\<close>

declare [[\<phi>reason ! %ToA_branches ToA_CR\<phi>_src_A ToA_CR\<phi>_src_B
        for \<open>_ \<Ztypecolon> (_ \<^emph>[?var] _) \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]]

hide_fact ToA_CR\<phi>_src_A ToA_CR\<phi>_src_B

subparagraph \<open>Target\<close>

declare [[\<phi>reason ! %ToA_branches ToA_CR\<phi>_target_A ToA_CR\<phi>_target_B
            for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[?var] _) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close> ]]

hide_fact ToA_CR\<phi>_target_A ToA_CR\<phi>_target_B



subsubsection \<open>Case Sum\<close>

paragraph \<open>Reduction\<close>

subparagraph \<open>Target\<close>

lemma ToA_case_sum_target_L[\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A x \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inl x) \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma ToA_case_sum_target_L'[\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inl x) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma ToA_case_sum_target_L_ty[\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<^sub>a c \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> case_sum U\<^sub>a U\<^sub>b (Inl c) \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma ToA_case_sum_target_R[\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B x \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inr x) \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma ToA_case_sum_target_R'[\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inr x) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma ToA_case_sum_target_R_ty[\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<^sub>b c \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> case_sum U\<^sub>a U\<^sub>b (Inr c) \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]: \<comment> \<open>This form can occur when reducing \<open>y \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[C] R\<close>\<close>
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B x \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (fst (x, y)) \<w>\<i>\<t>\<h> P \<close>
  by simp


subparagraph \<open>Source\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> case_sum A B (Inl x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> case_sum A B (Inr x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> W * A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> W * case_sum A B (Inl x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> W * B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> W * case_sum A B (Inr x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]: \<comment> \<open>This form can occur when reducing \<open>x \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[C] W\<close>\<close>
  \<open> case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> case_sum A B (fst (x, y)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp


paragraph \<open>Case Split\<close>

subparagraph \<open>Target\<close>

lemma [\<phi>reason %ToA_splitting except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum _ _ ?var \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A a \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B b \<w>\<i>\<t>\<h> Q b)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp)

lemma [\<phi>reason %ToA_splitting except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum _ _ ?var \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def)

lemma [\<phi>reason %ToA_splitting+1 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (case_sum _ _ ?var) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> (xx, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a a \<Ztypecolon> U\<^sub>a a \<^emph>[C\<^sub>a a] R\<^sub>a a \<w>\<i>\<t>\<h> P\<^sub>a a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> (xx, w\<^sub>b b) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b b \<Ztypecolon> U\<^sub>b b \<^emph>[C\<^sub>b b] R\<^sub>b b \<w>\<i>\<t>\<h> P\<^sub>b b)
\<Longrightarrow> (xx, case_sum w\<^sub>a w\<^sub>b x) \<Ztypecolon> T \<^emph>[case_sum C\<^sub>W\<^sub>a C\<^sub>W\<^sub>b x] (case_sum W\<^sub>a W\<^sub>b x)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> (case_sum U\<^sub>a U\<^sub>b x) \<^emph>[case_sum C\<^sub>a C\<^sub>b x] (case_sum R\<^sub>a R\<^sub>b x) \<w>\<i>\<t>\<h> case_sum P\<^sub>a P\<^sub>b x \<close>
  unfolding Premise_def Try_def
  by (cases x; simp)


(*TODO: Type level case split on SE gonna be a disaster!
        Every type variables between the two branches have to be independent! but here, the R\<^sub>a and R\<^sub>b
        are forced having identical abstract type! The abstract type of R\<^sub>a and R\<^sub>b instead should be
        a sum type!
  TODO: the case split now is broken!
*)
(*
lemma (*TODO-0918*)
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> (xx, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a a \<Ztypecolon> U\<^sub>a a \<^emph>[C\<^sub>a a] R\<^sub>a a \<w>\<i>\<t>\<h> P\<^sub>a a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> (xx, w\<^sub>b b) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b b \<Ztypecolon> U\<^sub>b b \<^emph>[C\<^sub>b b] R\<^sub>b b \<w>\<i>\<t>\<h> P\<^sub>b b)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S\<^sub>a \<or> S\<^sub>b
\<Longrightarrow> (xx, case_sum (Inl o w\<^sub>a) (Inr o w\<^sub>b) x) \<Ztypecolon> T \<^emph>[case_sum C\<^sub>W\<^sub>a C\<^sub>W\<^sub>b x] (case_sum (Inl\<^sub>\<phi> W\<^sub>a) (Inr\<^sub>\<phi> W\<^sub>b) x)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> (case_sum U\<^sub>a U\<^sub>b x) \<^emph>[case_sum C\<^sub>a C\<^sub>b x] (case_sum R\<^sub>a R\<^sub>b x) \<w>\<i>\<t>\<h> case_sum P\<^sub>a P\<^sub>b x \<close>
  unfolding Premise_def Try_def
  sorry
*)

lemma [\<phi>reason %ToA_splitting except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (case_sum _ _ ?var) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> (fst xx, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a a \<Ztypecolon> U\<^sub>a a \<^emph>[C\<^sub>a a] R\<^sub>a a \<w>\<i>\<t>\<h> P\<^sub>a a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> (fst xx, w\<^sub>b b) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b b \<Ztypecolon> U\<^sub>b b \<^emph>[C\<^sub>b b] R\<^sub>b b \<w>\<i>\<t>\<h> P\<^sub>b b)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S\<^sub>a \<or> S\<^sub>b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> snd xx = case_sum w\<^sub>a w\<^sub>b x
\<Longrightarrow> xx \<Ztypecolon> T \<^emph>[case_sum C\<^sub>W\<^sub>a C\<^sub>W\<^sub>b x] (case_sum W\<^sub>a W\<^sub>b x)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> (case_sum U\<^sub>a U\<^sub>b x) \<^emph>[case_sum C\<^sub>a C\<^sub>b x] (case_sum R\<^sub>a R\<^sub>b x) \<w>\<i>\<t>\<h> case_sum P\<^sub>a P\<^sub>b x \<close>
  unfolding Premise_def Try_def
  by (cases x; cases xx; simp)

(*
lemma [\<phi>reason %ToA_splitting except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum _ _ ?var \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                                     \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum _ _ (id ?var) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra a \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb b \<w>\<i>\<t>\<h> Q b)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def)*)


subparagraph \<open>Source\<close>

lemma ToA_case_sum_src:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> P = (\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> Q = (\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

lemma ToA_case_sum_src_R:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = ((\<lambda>_. True),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = ((\<lambda>_. True),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

(*lemma ToA_case_sum_src_R':
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)*)

lemma [\<phi>reason %ToA_splitting for \<open>case_sum (\<lambda>_. _ \<Ztypecolon> _ \<^emph>[_] _) (\<lambda>_. _ \<Ztypecolon> _ \<^emph>[_] _) _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (y\<^sub>a,C\<^sub>W\<^sub>a,W\<^sub>a,Ca,Ra,P) = (undefined, (\<lambda>_. True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_. True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (x\<^sub>a a \<Ztypecolon> T\<^sub>a a \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a a \<Ztypecolon> U \<^emph>[Ca a] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (y\<^sub>b,C\<^sub>W\<^sub>b,W\<^sub>b,Cb,Rb,Q) = (undefined, (\<lambda>_.True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_.True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (x\<^sub>b b \<Ztypecolon> T\<^sub>b b \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b b \<Ztypecolon> U \<^emph>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> (case x of Inl a \<Rightarrow> x\<^sub>a a \<Ztypecolon> T\<^sub>a a \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a | Inr b \<Rightarrow> x\<^sub>b b \<Ztypecolon> T\<^sub>b b \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b)
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> U \<^emph>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  unfolding Try_def Simplify_def Premise_def Orelse_shortcut_def
  by (cases x; simp)

(*
lemma [\<phi>reason %ToA_splitting+1 for \<open>case_sum _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>a a \<Ztypecolon> U \<^emph>[True] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y\<^sub>b b \<Ztypecolon> U \<^emph>[True] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> U \<^emph>[True] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)*)

lemma ToA_case_sum_src_W:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> P = (\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> Q = (\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> W * case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

lemma ToA_case_sum_src_WR:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = ((\<lambda>_. True),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (W * A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = ((\<lambda>_. True),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (W * B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> W * case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

(*lemma ToA_case_sum_src_WR':
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> W * case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)
*)
lemma case_sum_degenerate:
  \<open>(case_sum (\<lambda>_. a) (\<lambda>_. a) x) \<equiv> a\<close>
  unfolding atomize_eq
  by (cases x; simp) 

lemma sum_case_distrib_fx:
  \<open>(case_sum fa fb x) (case_sum va vb x) \<equiv> (case_sum (\<lambda>x. fa x (va x)) (\<lambda>x. fb x (vb x)) x)\<close>
  unfolding atomize_eq
  by (cases x; simp)

lemma sum_case_distrib_arg:
  \<open>(case_sum fa fb x) a \<equiv> (case_sum (\<lambda>x. fa x a) (\<lambda>x. fb x a) x)\<close>
  unfolding atomize_eq
  by (cases x; simp)

ML \<open>
(*instantiates variables vs to \<open>case_sum va vb x\<close> for each*)
fun reasoner_ToA_conditioned_subgoals_sum ctxt'N (vars,Y,RHS) =
  let val (Ya, Yb, x) = Phi_Help.dest_triop_c \<^const_name>\<open>case_sum\<close> RHS
      val \<^Type>\<open>sum ta tb\<close> = Thm.typ_of_cterm x
      val ([Na,Nb], ctxt'N) = Variable.variant_fixes ["xa","xb"] ctxt'N
      val xa = Thm.cterm_of ctxt'N (Free (Na, ta))
      val xb = Thm.cterm_of ctxt'N (Free (Nb, tb))
      val x_term = Thm.term_of x

      val Ya_s = map (fn ((N,i),ty) => Thm.apply (Thm.var ((N,i+2), Thm.ctyp_of ctxt'N (ta --> ty))) xa) vars
      val Yb_s = map (fn ((N,i),ty) => Thm.apply (Thm.var ((N,i+3), Thm.ctyp_of ctxt'N (tb --> ty))) xb) vars 
      val Y_s  = map2 (fn a => fn b =>
                   let val ty = Thm.typ_of_cterm a
                    in Thm.apply (Thm.apply (Thm.apply (
                            Thm.cterm_of ctxt'N \<^Const>\<open>case_sum ta ty tb\<close>) (Thm.dest_fun a)
                        ) (Thm.dest_fun b)) x
                   end) Ya_s Yb_s
      val Ya' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Ya_s)) Y
             |> Thm.lambda xa
      val Yb' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Yb_s)) Y
             |> Thm.lambda xb
      fun mk_inst ctm Y =
        case Thm.term_of ctm
          of _ $ Free _ => mk_inst (Thm.dest_fun ctm) (Thm.lambda (Thm.dest_arg ctm) Y)
           | Var v => (v, Y)
           | _ => error "BUG: reasoner_ToA_conditioned_subgoals"

   in (Vars.make (mk_inst Ya Ya' :: mk_inst Yb Yb' :: (vars ~~ Y_s)), x_term)
  end
\<close>

\<phi>reasoner_ML \<open>ML (case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> %ToA_splitting
        ( \<open>case_sum _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
        | except \<open>case_sum _ _ ?var \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
        | except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_case_sum_src}, @{thm' ToA_case_sum_src_R}, (*@{thm' ToA_case_sum_src_R'},*)
          (true, @{thms' case_sum_degenerate}, @{thms' sum.case}),
          reasoner_ToA_conditioned_subgoals_sum, \<^context>) o snd\<close>

\<phi>reasoner_ML \<open>ML (W * case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> %ToA_splitting
        ( \<open>_ * case_sum _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
        | except \<open>_ * case_sum _ _ ?var \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
        | except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_case_sum_src_W}, @{thm' ToA_case_sum_src_WR}, (*@{thm' ToA_case_sum_src_WR'},*)
          (true, @{thms' case_sum_degenerate}, @{thms' sum.case}),
          reasoner_ToA_conditioned_subgoals_sum, \<^context>) o snd\<close>


paragraph \<open>When the sum type is a variable\<close>

subparagraph \<open>Normalizing\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B var \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (id var) \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B var \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (id var) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (case_sum A B var) \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (case_sum A B (id var)) \<^emph>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp

subparagraph \<open>Major Reasoning\<close>

declare [[
    \<phi>reason ! %ToA_branches ToA_case_sum_target_L ToA_case_sum_target_R
        for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum _ _ ?var \<w>\<i>\<t>\<h> _\<close>,
    \<phi>reason ! %ToA_branches ToA_case_sum_target_L' ToA_case_sum_target_R'
        for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum _ _ ?var \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>,
    \<phi>reason ! %ToA_branches ToA_case_sum_target_L_ty ToA_case_sum_target_R_ty
        for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (case_sum _ _ ?var) \<^emph>[_] _ \<w>\<i>\<t>\<h> _\<close>
]]

(*TODO: the source part!*)


subsection \<open>Helper Stuffs\<close>

method_setup represent_BI_pred_in_\<phi>Type = \<open>Args.term >> (fn X => fn ctxt => Method.METHOD (K (fn th =>
  let val T = Thm.cterm_of ctxt X
      val ty_a = Thm.ctyp_of_cterm T |> Thm.dest_ctyp0
      val ty_c = Thm.ctyp_of_cterm T |> Thm.dest_ctyp1 |> Thm.dest_ctyp0
   in case Thm.prop_of th
   of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
      Seq.single (Conv.gconv_rule (Conv.bottom_conv (fn _ => fn ctm =>
       case Thm.term_of ctm
         of X' $ _ => if X' aconv X
                      then Conv.rewr_conv \<^instantiate>\<open>T and x = \<open>Thm.dest_arg ctm\<close>
                                                        and 'c = ty_c and 'a = ty_a
                                                        in lemma \<open>T x \<equiv> x \<Ztypecolon> T\<close> for T :: \<open>('c,'a) \<phi>\<close>
                                                              by (simp add: \<phi>Type_def)\<close> ctm
                      else Conv.all_conv ctm
          | _ => Conv.all_conv ctm
      ) ctxt) 1 th)
    | _ => Seq.empty
  end
)))\<close>



end