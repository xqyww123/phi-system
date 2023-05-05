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
    \<open>A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P \<triangleq> A \<longrightarrow> B \<and> P\<close>, where \<open>P\<close> is a pure assertion.
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
    We denote them by notation \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>.

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
      and "<implies>" = "\<i>\<m>\<p>\<l>\<i>\<e>\<s>"
      and "<and>"  = "\<a>\<n>\<d>"
      and "<subj>" = "\<s>\<u>\<b>\<j>"
      and "<remains>" = "\<r>\<e>\<m>\<a>\<i>\<n>\<s>"
begin

subsection \<open>Bottom\<close>

abbreviation Bottom ("\<bottom>") where \<open>Bottom \<equiv> (0::'a::sep_magma set)\<close>
abbreviation Bottom_abs ("\<bottom>\<^sub>\<lambda>") where \<open>Bottom_abs \<equiv> (0 :: 'b \<Rightarrow> 'a::sep_magma set)\<close>

subsection \<open>\<phi>-Type\<close>

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete set "

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a set" (infix "\<Ztypecolon>" 20) where " (x \<Ztypecolon> T) = (T x)"

text \<open>The implementation represents BI assertions by sets simply, in shallow embedding manner.\<close>

lemma typing_inhabited: "p \<in> (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (x \<Ztypecolon> T)"
  unfolding Inhabited_def \<phi>Type_def by blast

lemma \<phi>Type_eqI:
  \<open>(\<forall>x p. p \<in> (x \<Ztypecolon> a) \<longleftrightarrow> p \<in> (x \<Ztypecolon> b)) \<Longrightarrow> a = b\<close>
  unfolding \<phi>Type_def by blast

ML_file \<open>library/tools/simp_congruence.ML\<close>

subsubsection \<open>Embedding of separation conjunction in \<phi>-Type\<close>

definition \<phi>Prod :: " ('concrete::sep_magma, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 55)
  where "A \<^emph> B = (\<lambda>(a,b). B b * A a)"

lemma \<phi>Prod_expn[\<phi>expns]:
  "concrete \<in> ((a,b) \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>cb ca. concrete = cb * ca \<and> cb \<in> (b \<Ztypecolon> B) \<and> ca \<in> (a \<Ztypecolon> A) \<and> cb ## ca)"
  unfolding \<phi>Prod_def \<phi>Type_def times_set_def by simp

lemma \<phi>Prod_expn':
  \<open>((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma \<phi>Prod_inhabited[elim!,\<phi>inhabitance_rule]:
  "Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<Longrightarrow> (Inhabited (x1 \<Ztypecolon> T1) \<Longrightarrow> Inhabited (x2 \<Ztypecolon> T2) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

lemma \<phi>Prod_split: "((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)"
  by (simp add: \<phi>expns set_eq_iff)



subsection \<open>Implication\<close>

definition Imply :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2_)/ \<i>\<m>\<p>\<l>\<i>\<e>\<s> (2_)/ \<a>\<n>\<d> (2_)" [13,13,13] 12)
  where "(A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P) \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P)"

abbreviation SimpleImply :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_)/ \<i>\<m>\<p>\<l>\<i>\<e>\<s> (2_)" [13,13] 12)
  where \<open>SimpleImply T U \<equiv> Imply T U True\<close>

declare [[\<phi>reason_default_pattern \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> _\<close> \<Rightarrow> \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> _\<close> (10)]]

text \<open>Semantics of antecedent \<^pattern_prop>\<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> ?P\<close>:
  Given the source \<^term>\<open>X\<close> and the target \<^term>\<open>Y\<close>, find a reasoning way to do the transformation,
  which may bring in additional pure facts \<^pattern_term>\<open>?P\<close> and generate proof obligations.\<close>

definition FOCUS_TAG :: " 'a \<Rightarrow> 'a "  ("\<blangle> _ \<brangle>") where [iff]: "\<blangle> x \<brangle> = x"

abbreviation Remains :: \<open> 'a::{sep_disj,times} set \<Rightarrow> 'a set \<Rightarrow> 'a set \<close> (infix "\<r>\<e>\<m>\<a>\<i>\<n>\<s>" 13)
  where \<open>(X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R) \<equiv> R * \<blangle> X \<brangle>\<close>

declare [[\<phi>reason_default_pattern
    \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<a>\<n>\<d> _\<close> \<Rightarrow> \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<a>\<n>\<d> _\<close> (20)
]]

text \<open>For antecedent \<^pattern_prop>\<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<a>\<n>\<d> _\<close>, the semantics is slightly different
  where it specifies extracting given \<^term>\<open>Y\<close> from given \<^term>\<open>X\<close> and leaving some \<^schematic_term>\<open>?R\<close>.\<close>

lemma \<phi>Type_eqI_imp:
  \<open> (\<And>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> U)
\<Longrightarrow> (\<And>x. x \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T)
\<Longrightarrow> T = U\<close>
  unfolding \<phi>Type_def Imply_def
  by auto

subsubsection \<open>Proof \& Reasoning Rules\<close>

lemma zero_implies_any[\<phi>reason 2000, simp]:
  \<open>0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X\<close>
  unfolding Imply_def zero_set_def by simp

lemma implies_refl[simp,
    \<phi>reason 4000 for \<open>?A \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?A \<a>\<n>\<d> ?P\<close>,
    \<phi>reason 900 for \<open>?A \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?B \<a>\<n>\<d> ?P\<close> \<comment> \<open>Unification can be aggressive.\<close>
]:
  "A \<i>\<m>\<p>\<l>\<i>\<e>\<s> A" unfolding Imply_def by fast

lemma implies_refl_ty[\<phi>reason 800 for \<open>?x \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?T' \<a>\<n>\<d> _\<close>]:
  "\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> T" unfolding Imply_def by fast



lemma implies_union:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X + Y \<a>\<n>\<d> P\<close>
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X + Y \<a>\<n>\<d> P\<close>
  unfolding Imply_def by simp_all

(* abbreviation SimpleSubty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _)" [2,14] 13)
  where "(A \<longmapsto> B) \<equiv> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> True)" *)
(* lemma SubtyE[elim]: "A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Imply_def Inhabited_def by (auto intro: Inhabited_subset)
lemma SubtyI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P" unfolding Imply_def Inhabited_def by auto *)


lemma implies_trans:
  "A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P
    \<Longrightarrow> (P \<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> C \<a>\<n>\<d> Q)
    \<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> C \<a>\<n>\<d> P \<and> Q"
  unfolding Imply_def by auto

lemma implies_weaken:
  \<open> P \<longrightarrow> P'
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P'\<close>
  unfolding Imply_def by simp

lemma implies_left_prod:
  "U' \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P \<Longrightarrow> R * U' \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * U \<a>\<n>\<d> P "
  unfolding Imply_def split_paired_All times_set_def by blast

lemma implies_right_prod:
  "U' \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P \<Longrightarrow> U' * R \<i>\<m>\<p>\<l>\<i>\<e>\<s> U * R \<a>\<n>\<d> P "
  unfolding Imply_def split_paired_All times_set_def by blast

lemma assertion_eq_intro:
  \<open> P \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q
\<Longrightarrow> Q \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> P = Q\<close>
  unfolding Imply_def by blast

subsubsection \<open>Inhabitance Reasoning - Part II\<close>

lemma [\<phi>reason 1100]:
  \<open>PROP Extract_Elimination_Rule (Trueprop (X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y)) (Inhabited X) (Inhabited Y) \<close>
  unfolding Extract_Elimination_Rule_def Imply_def Inhabited_def by blast

lemma [\<phi>reason 1000]:
  \<open>PROP Extract_Elimination_Rule (Trueprop (X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P)) (Inhabited X) (Inhabited Y \<and> P) \<close>
  unfolding Extract_Elimination_Rule_def Imply_def Inhabited_def by blast


subsection \<open>Specialized Additive Conjunction\<close>

declare Subjection_expn[\<phi>expns]

lemma Subjection_inhabited[elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (S \<s>\<u>\<b>\<j> P) \<Longrightarrow> (P \<Longrightarrow> Inhabited S \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: Subjection_expn)

lemma Subjection_cong[cong]:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<s>\<u>\<b>\<j> P) \<equiv> (S' \<s>\<u>\<b>\<j> P')\<close>
  unfolding atomize_eq set_eq_iff by (simp add: Subjection_expn, blast)

(* lemma [\<phi>reason 1000]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> T' \<a>\<n>\<d> P
\<Longrightarrow> (P \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Q)
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> T' \<s>\<u>\<b>\<j> Q \<a>\<n>\<d> P"
  unfolding Imply_def Premise_def by (simp add: Subjection_expn) *)

lemma Subjection_imp_I:
  \<open> P
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> Q
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<s>\<u>\<b>\<j> P \<a>\<n>\<d> Q\<close>
  unfolding Imply_def by (simp add: Subjection_expn)

lemma Subjection_True [simp, \<phi>programming_safe_simps]: "(T \<s>\<u>\<b>\<j> True) = T"
  unfolding set_eq_iff by (simp add: Subjection_expn)

lemma Subjection_Flase[simp, \<phi>programming_safe_simps]: \<open>(T \<s>\<u>\<b>\<j> False) = 0\<close>
  unfolding set_eq_iff by (simp add: Subjection_expn zero_set_def)

lemma Subjection_Subjection:
  \<open>(S \<s>\<u>\<b>\<j> P \<s>\<u>\<b>\<j> Q) = (S \<s>\<u>\<b>\<j> P \<and> Q)\<close>
  unfolding set_eq_iff
  by (simp add: Subjection_expn)

lemma Subjection_Zero[simp]:
  \<open>(0 \<s>\<u>\<b>\<j> P) = 0\<close>
  unfolding set_eq_iff
  by (simp add: Subjection_expn zero_set_def)

(* lemma (in \<phi>empty) [simp]: "(VAL (S \<s>\<u>\<b>\<j> P)) = (VAL S \<s>\<u>\<b>\<j> P)" by (simp add: \<phi>expns set_eq_iff) blast
lemma (in \<phi>empty) [simp]: "(OBJ (S \<s>\<u>\<b>\<j> P)) = (OBJ S \<s>\<u>\<b>\<j> P)" by (simp add: \<phi>expns set_eq_iff) *)

lemma Subjection_times[simp]:
  \<open>(S \<s>\<u>\<b>\<j> P) * T = (S * T \<s>\<u>\<b>\<j> P)\<close>
  \<open>T * (S \<s>\<u>\<b>\<j> P) = (T * S \<s>\<u>\<b>\<j> P)\<close>
  unfolding Subjection_def times_set_def set_eq_iff by blast+

lemma Subjection_plus:
  \<open>(A + B \<s>\<u>\<b>\<j> P) = (A \<s>\<u>\<b>\<j> P) + (B \<s>\<u>\<b>\<j> P)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns) blast

subsection \<open>Existential Quantification\<close>

declare ExSet_expn[\<phi>expns]

lemma ExSet_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (ExSet S) \<Longrightarrow> (\<And>x. Inhabited (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

syntax
  "_SetcomprNu" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<s>\<u>\<b>\<j>/ _./ _" [14,0,15] 14)

translations
  " X \<s>\<u>\<b>\<j> idts. P " \<rightleftharpoons> "\<exists>* idts. X \<s>\<u>\<b>\<j> P"
  " X \<s>\<u>\<b>\<j> idts. CONST True " \<rightleftharpoons> "\<exists>* idts. X"

text \<open>Semantically, an existential quantification in BI actually represents union of resources
  matching the existentially quantified assertion, as shown by the following lemma.\<close>

lemma " Union { S x |x. P x } = (S x \<s>\<u>\<b>\<j> x. P x) "
  by (simp add: set_eq_iff \<phi>expns) blast


lemma ExSet_pair: "ExSet T = (\<exists>*a b. T (a,b) )"
  unfolding set_eq_iff by (clarsimp simp add: \<phi>expns)

(* lemma (in \<phi>empty_sem) [simp]: "p \<in> \<S>  (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> \<S>  (T z) )" by (cases p, simp_all add: \<phi>expns set_eq_iff)
lemma (in \<phi>empty_sem) [simp]: "p \<in> !\<S> (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> !\<S> (T z) )" by (cases p, simp_all add: \<phi>expns set_eq_iff) *)
(* lemma (in \<phi>empty) [simp]: "(VAL ExSet T) = (\<exists>*c. VAL T c)" by (simp add: \<phi>expns set_eq_iff) blast
lemma (in \<phi>empty) [simp]: "(OBJ ExSet T) = (\<exists>*c. OBJ T c)" by (simp add: \<phi>expns set_eq_iff) *)

lemma ExSet_times_left [simp]: "(ExSet T * R) = (\<exists>* c. T c * R )" by (simp add: \<phi>expns set_eq_iff, blast)
lemma ExSet_times_right[simp]: "(L * ExSet T) = (\<exists>* c. L * T c)" by (simp add: \<phi>expns set_eq_iff) blast

lemma ExSet_simps[simp]:
  \<open>ExSet 0 = 0\<close>
  \<open>ExSet (\<lambda>_. T) = T\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> x = y) = (F y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> y = x) = (F y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> x = y \<and> P x) = (F y \<s>\<u>\<b>\<j> P y)\<close>
  \<open>(\<exists>* x. F x \<s>\<u>\<b>\<j> y = x \<and> P x) = (F y \<s>\<u>\<b>\<j> P y)\<close>
  \<open>(X b \<s>\<u>\<b>\<j> P b \<s>\<u>\<b>\<j> b. Q b) = (X b \<s>\<u>\<b>\<j> b. P b \<and> Q b)\<close>
  \<open>(X2 a b \<s>\<u>\<b>\<j> a. P2 a b \<s>\<u>\<b>\<j> b. Q b) = (X2 a b \<s>\<u>\<b>\<j> a b. P2 a b \<and> Q b)\<close>
  \<open>ExSet 0 = 0\<close>
(*  \<open>(\<exists>* x. x = t \<and> P x) = P t\<close>
"\<And>P. (\<exists>x. x = t \<and> P x) = P t"
    "\<And>P. (\<exists>x. t = x \<and> P x) = P t"*)
  unfolding set_eq_iff by (simp_all add: \<phi>expns) blast

declare ExSet_simps(1)[\<phi>programming_safe_simps]

(*lemma [\<phi>reason 200]: (*depreciated*)
   "(\<And>c. T c \<i>\<m>\<p>\<l>\<i>\<e>\<s> T' \<a>\<n>\<d> P c)
\<Longrightarrow> (ExSet T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> T' \<a>\<n>\<d> (\<exists>c. P c)"
  unfolding Imply_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason 300]:
  \<open>(\<And>c. S c \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> P)
\<Longrightarrow> (ExSet S) \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast) *)

lemma ExSet_imp_I:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' x \<a>\<n>\<d> P
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> (ExSet S') \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns, blast)

(*lemma [\<phi>reason 100 for \<open>?S \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?S' \<a>\<n>\<d> (Ex ?P)\<close>]:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> P x
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> (Ex P)\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns, blast) *)

lemma ExSet_plus:
  \<open>(\<exists>*x. A x + B x) = ExSet A + ExSet B\<close>
  \<open>ExSet (A + B) = ExSet A + ExSet B\<close>
  unfolding set_eq_iff by (simp_all add: \<phi>expns plus_fun) blast+

subsection \<open>Universal Quantification\<close>

definition AllSet :: \<open>('a \<Rightarrow> 'b set) \<Rightarrow> 'b set\<close> (binder "\<forall>\<^sup>S" 10)
  where \<open>AllSet X = {y. \<forall>x. y \<in> X x}\<close>

lemma AllSet_expn[\<phi>expns]:
  \<open>p \<in> (\<forall>\<^sup>Sx. B x) \<longleftrightarrow> (\<forall>x. p \<in> B x)\<close>
  unfolding AllSet_def by simp

lemma AllSet_subset:
  \<open>A \<subseteq> (\<forall>\<^sup>S x. B x) \<longleftrightarrow> (\<forall>x. A \<subseteq> B x)\<close>
  unfolding AllSet_def subset_iff by (rule; clarsimp; blast)

lemma AllSet_refl:
  \<open>(\<And>x. refl (B x))
\<Longrightarrow> refl (\<forall>\<^sup>S x. B x)\<close>
  unfolding AllSet_def
  by (simp add: refl_on_def)

lemma AllSet_trans:
  \<open>(\<And>x. trans (B x))
\<Longrightarrow> trans (\<forall>\<^sup>S x. B x)\<close>
  unfolding AllSet_def
  by (smt (verit) mem_Collect_eq transD transI)





end