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
\[ \<open>(x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<^emph> \<cdots> x\<^sub>n \<Ztypecolon> T\<^sub>n \<^bold>s\<^bold>u\<^bold>b\<^bold>j a. P)\<close> \]
Readers may read it as a set,
\[ \<open>{ x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<^emph> \<cdots> x\<^sub>n \<Ztypecolon> T\<^sub>n |a. P }\<close> \] 

\<^descr> \<^emph>\<open>Simple Multi-Term Form\<close> is a MTF where there is no existential quantification and the attached
  \<open>P\<close> is trivial \<open>True\<close>, viz., it is characterized by
  \[ \<open>x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> \<cdots> \<^emph> x\<^sub>n \<Ztypecolon> T\<^sub>n\<close> \]
\<close>

text \<open>
Specifically, in this minimal specialized BI:

  \<^item> It does not have a general additive conjunction (\<open>\<and>\<close>) that connects any BI assertions,
    but only the one (\<open>A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P\<close>) connects a BI assertion \<open>A\<close> and a pure assertion \<open>P\<close>,
    because it is exactly what at most the MTF requires.

  \<^item> Implication does not occur in assertions (of \<phi>-SL), but it represents transformations of
    abstraction so has a significant role in reasoning (rules).
    We emphasize this transformation by assigning the implication with notation
    \<open>A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P \<triangleq> A \<longrightarrow> B \<and> P\<close>, where \<open>P\<close> is a pure assertion.
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
    We denote them by notation \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close>.

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
      and "<implies>" = "\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s"
      and "<and>"  = "\<^bold>a\<^bold>n\<^bold>d"
      and "<subj>" = "\<^bold>s\<^bold>u\<^bold>b\<^bold>j"
begin

subsection \<open>Bottom\<close>

abbreviation Bottom ("\<bottom>") where \<open>Bottom \<equiv> (0::'a::sep_magma set)\<close>

subsection \<open>\<phi>-Type\<close>

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete set "

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a set" (infix "\<Ztypecolon>" 20) where " (x \<Ztypecolon> T) = (T x)"

lemma typing_inhabited: "p \<in> (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (x \<Ztypecolon> T)"
  unfolding Inhabited_def \<phi>Type_def by blast

lemma \<phi>Type_eqI:
  \<open>(\<forall>x p. p \<in> (x \<Ztypecolon> a) \<longleftrightarrow> p \<in> (x \<Ztypecolon> b)) \<Longrightarrow> a = b\<close>
  unfolding \<phi>Type_def by blast

ML_file \<open>library/tools/simp_congruence.ML\<close>

text \<open>The implementation represents BI assertions by sets simply, in shallow embedding manner.\<close>

subsection \<open>Implication\<close>

definition Imply :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2_)/ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (2_)/ \<^bold>a\<^bold>n\<^bold>d (2_)" [13,13,13] 12)
  where "(A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P) \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P)"

abbreviation SimpleImply :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_)/ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (2_)" [13,13] 12)
  where \<open>SimpleImply T U \<equiv> Imply T U True\<close>

declare [[\<phi>reason_default_pattern \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d _\<close> (10)]]

text \<open>Semantics of antecedent \<^pattern_prop>\<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>:
  Given the source \<^term>\<open>X\<close> and the target \<^term>\<open>Y\<close>, find a reasoning way to do the transformation,
  which may bring in additional pure facts \<^pattern_term>\<open>?P\<close> and generate proof obligations.\<close>

definition FOCUS_TAG :: " 'a \<Rightarrow> 'a "  ("\<blangle> _ \<brangle>") where [iff]: "\<blangle> x \<brangle> = x"

abbreviation Remains :: \<open> 'a::{sep_disj,times} set \<Rightarrow> 'a set \<Rightarrow> 'a set \<close> (infix "\<r>\<e>\<m>\<a>\<i>\<n>\<s>" 13)
  where \<open>(X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R) \<equiv> R * \<blangle> X \<brangle>\<close>

declare [[\<phi>reason_default_pattern
    \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<^bold>a\<^bold>n\<^bold>d _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<^bold>a\<^bold>n\<^bold>d _\<close> (20)
]]

text \<open>For antecedent \<^pattern_prop>\<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<^bold>a\<^bold>n\<^bold>d _\<close>, the semantics is slightly different
  where it specifies extracting given \<^term>\<open>Y\<close> from given \<^term>\<open>X\<close> and leaving some \<^schematic_term>\<open>?R\<close>.\<close>


subsubsection \<open>Proof \& Reasoning Rules\<close>

lemma zero_implies_any[\<phi>reason 2000, simp]:
  \<open>0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X\<close>
  unfolding Imply_def zero_set_def by simp

lemma implies_refl[simp,
    \<phi>reason 4000 for \<open>?A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?A \<^bold>a\<^bold>n\<^bold>d ?P\<close>,
    \<phi>reason 900 for \<open>?A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?B \<^bold>a\<^bold>n\<^bold>d ?P\<close> \<comment> \<open>Unification can be aggressive.\<close>
]:
  "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A" unfolding Imply_def by fast

lemma implies_refl_ty[\<phi>reason 800 for \<open>?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?T' \<^bold>a\<^bold>n\<^bold>d _\<close>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> T" unfolding Imply_def by fast



lemma implies_union:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X + Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X + Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by simp_all

(* abbreviation SimpleSubty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _)" [2,14] 13)
  where "(A \<longmapsto> B) \<equiv> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d True)" *)
(* lemma SubtyE[elim]: "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Imply_def Inhabited_def by (auto intro: Inhabited_subset)
lemma SubtyI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P" unfolding Imply_def Inhabited_def by auto *)


lemma implies_trans:
  "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
    \<Longrightarrow> (P \<Longrightarrow> B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s C \<^bold>a\<^bold>n\<^bold>d Q)
    \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s C \<^bold>a\<^bold>n\<^bold>d P \<and> Q"
  unfolding Imply_def by auto

lemma implies_weaken:
  \<open> P \<longrightarrow> P'
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P'\<close>
  unfolding Imply_def by simp

lemma implies_left_prod:
  "U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> R * U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * U \<^bold>a\<^bold>n\<^bold>d P "
  unfolding Imply_def split_paired_All times_set_def by blast

lemma implies_right_prod:
  "U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> U' * R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U * R \<^bold>a\<^bold>n\<^bold>d P "
  unfolding Imply_def split_paired_All times_set_def by blast

lemma assertion_eq_intro:
  \<open> P \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Q
\<Longrightarrow> Q \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s P
\<Longrightarrow> P = Q\<close>
  unfolding Imply_def by blast

subsubsection \<open>Inhabitance Reasoning - Part II\<close>

lemma [\<phi>reason 1100]:
  \<open>PROP Extract_Elimination_Rule (Trueprop (X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y)) (Inhabited X) (Inhabited Y) \<close>
  unfolding Extract_Elimination_Rule_def Imply_def Inhabited_def by blast

lemma [\<phi>reason 1000]:
  \<open>PROP Extract_Elimination_Rule (Trueprop (X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P)) (Inhabited X) (Inhabited Y \<and> P) \<close>
  unfolding Extract_Elimination_Rule_def Imply_def Inhabited_def by blast


subsection \<open>Specialized Additive Conjunction\<close>

definition Subjection :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<^bold>s\<^bold>u\<^bold>b\<^bold>j" 15)
  where " (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = {p. p \<in> T \<and> P}"

lemma Subjection_expn[\<phi>expns]:
  "p \<in> (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> p \<in> T \<and> P"
  unfolding Subjection_def by simp
 
lemma Subjection_inhabited[elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<Longrightarrow> (P \<Longrightarrow> Inhabited S \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: Subjection_expn)

lemma Subjection_cong[cong]:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<equiv> (S' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P')\<close>
  unfolding atomize_eq set_eq_iff by (simp add: Subjection_expn, blast)

(* lemma [\<phi>reason 1000]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q)
\<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Imply_def Premise_def by (simp add: Subjection_expn) *)

lemma Subjection_imp_I:
  \<open> P
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d Q
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<^bold>a\<^bold>n\<^bold>d Q\<close>
  unfolding Imply_def by (simp add: Subjection_expn)

lemma Subjection_True [simp]: "(T \<^bold>s\<^bold>u\<^bold>b\<^bold>j True) = T"
  unfolding set_eq_iff by (simp add: Subjection_expn)

lemma Subjection_Flase[simp]: \<open>(T \<^bold>s\<^bold>u\<^bold>b\<^bold>j False) = 0\<close>
  unfolding set_eq_iff by (simp add: Subjection_expn zero_set_def)

lemma Subjection_Subjection:
  \<open>(S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) = (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<and> Q)\<close>
  unfolding set_eq_iff
  by (simp add: Subjection_expn)

lemma Subjection_Zero[simp]:
  \<open>(0 \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = 0\<close>
  unfolding set_eq_iff
  by (simp add: Subjection_expn zero_set_def)

(* lemma (in \<phi>empty) [simp]: "(VAL (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (VAL S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)" by (simp add: \<phi>expns set_eq_iff) blast
lemma (in \<phi>empty) [simp]: "(OBJ (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (OBJ S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)" by (simp add: \<phi>expns set_eq_iff) *)

lemma Subjection_times[simp]:
  \<open>(S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) * T = (S * T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  \<open>T * (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (T * S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding Subjection_def times_set_def set_eq_iff by blast+

lemma Subjection_plus:
  \<open>(A + B \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) + (B \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns) blast

subsection \<open>Existential Quantification\<close>

definition ExSet :: " ('c \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "\<exists>*" 14)
  where "ExSet S = {p. (\<exists>c. p \<in> S c)}"
notation ExSet (binder "\<exists>\<^sup>s" 14)

lemma ExSet_expn[\<phi>expns]: "p \<in> ExSet S \<longleftrightarrow> (\<exists>c. p \<in> S c)" unfolding ExSet_def by simp

lemma ExSet_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (ExSet S) \<Longrightarrow> (\<And>x. Inhabited (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

syntax
  "_SetcomprNu" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<^bold>s\<^bold>u\<^bold>b\<^bold>j/ _./ _" [14,0,15] 14)

translations
  " X \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. P " \<rightleftharpoons> "\<exists>* idts. X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P"
  " X \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. CONST True " \<rightleftharpoons> "\<exists>* idts. X"

text \<open>Semantically, an existential quantification in BI actually represents union of resources
  matching the existentially quantified assertion, as shown by the following lemma.\<close>

lemma " Union { S x |x. P x } = (S x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x) "
  by (simp add: set_eq_iff \<phi>expns) blast


lemma ExSet_pair: "ExSet T = (\<exists>*c1 c2. T (c1,c2) )" by (auto simp add: \<phi>expns)

(* lemma (in \<phi>empty_sem) [simp]: "p \<in> \<S>  (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> \<S>  (T z) )" by (cases p, simp_all add: \<phi>expns set_eq_iff)
lemma (in \<phi>empty_sem) [simp]: "p \<in> !\<S> (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> !\<S> (T z) )" by (cases p, simp_all add: \<phi>expns set_eq_iff) *)
(* lemma (in \<phi>empty) [simp]: "(VAL ExSet T) = (\<exists>*c. VAL T c)" by (simp add: \<phi>expns set_eq_iff) blast
lemma (in \<phi>empty) [simp]: "(OBJ ExSet T) = (\<exists>*c. OBJ T c)" by (simp add: \<phi>expns set_eq_iff) *)

lemma ExSet_times_left [simp]: "(ExSet T * R) = (\<exists>* c. T c * R )" by (simp add: \<phi>expns set_eq_iff, blast)
lemma ExSet_times_right[simp]: "(L * ExSet T) = (\<exists>* c. L * T c)" by (simp add: \<phi>expns set_eq_iff) blast

lemma ExSet_simps[simp]:
  \<open>ExSet (\<lambda>_. T) = T\<close>
  \<open>(\<exists>* x. F x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x = y \<and> P x) = (F y \<^bold>s\<^bold>u\<^bold>b\<^bold>j P y)\<close>
  \<open>(X b \<^bold>s\<^bold>u\<^bold>b\<^bold>j P b \<^bold>s\<^bold>u\<^bold>b\<^bold>j b. Q b) = (X b \<^bold>s\<^bold>u\<^bold>b\<^bold>j b. P b \<and> Q b)\<close>
  \<open>(X2 a b \<^bold>s\<^bold>u\<^bold>b\<^bold>j a. P2 a b \<^bold>s\<^bold>u\<^bold>b\<^bold>j b. Q b) = (X2 a b \<^bold>s\<^bold>u\<^bold>b\<^bold>j a b. P2 a b \<and> Q b)\<close>
  unfolding set_eq_iff by (simp_all add: \<phi>expns) blast

(*lemma [\<phi>reason 200]: (*depreciated*)
   "(\<And>c. T c \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P c)
\<Longrightarrow> (ExSet T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d (\<exists>c. P c)"
  unfolding Imply_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason 300]:
  \<open>(\<And>c. S c \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d P)
\<Longrightarrow> (ExSet S) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast) *)

lemma ExSet_imp_I:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' x \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (ExSet S') \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns, blast)

(*lemma [\<phi>reason 100 for \<open>?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?S' \<^bold>a\<^bold>n\<^bold>d (Ex ?P)\<close>]:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d P x
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d (Ex P)\<close>
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