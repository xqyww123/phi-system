theory BI_for_Phi
  imports NoePreliminary
         "./Phi_Logic_Programming_Reasoner/Phi_Logic_Programming_Reasoner"
          Fictional_Algebra
  abbrevs "<implies>" = "\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s"
      and "<and>"  = "\<^bold>a\<^bold>n\<^bold>d"
      and "<subj>" = "\<^bold>s\<^bold>u\<^bold>b\<^bold>j"
begin

section \<open>An Implementation of Bunched Implications, Specialized for \<phi>-System\<close>

text \<open>Note, this is NOT \<phi>-BI logic but a partial implementation of the standard BI,
  just specialized for \<phi>-System in consideration of proof engineering.

  \<^item> It does not have a general additive conjunction that connects any BI assertions,
    but only the one connects a BI assertion and a pure assertion, because it is exactly
    what at most the canonical form of \<phi>-BI requires. Correspondingly, the proof engineering
    and automation never considers things other than this.
  \<^item> Implication does not occur in assertions (of \<phi>-SL), but, it has a significant role in
    reasoning (rules).
    These implications occurring in reasoning rules, have form in \<^term>\<open>A \<longrightarrow> B \<and> P\<close> where P is
    a pure assertion. This P (later in \<phi>-System) helps to catch the information (in abstract domain)
    lost in the weakening of this implication.
  \<^item> Optionally we have universal quantification. It can be used to quantify free variables
    if for any reason free variables are not advocated. The universal quantifier is typically
    not necessary in \<phi>-BI and \<phi>-SL, where we use free variables directly. However, in some
    situation, like when we consider transitions of resource states and we want a transition
    relation for each procedure, we need a single universally quantified assertion,
    instead of a family of assertions indexed by free variables.
  \<^item> We only have multiplicative conjunctions, specialized additive conjunction described above,
    existential quantification, and optionally universal quantification,
    because these are all the canonical form of \<phi>-BI requires
    (may plus implication that only occurs in reasoning rules).
    Any other things, should be some specific \<phi>-Types expressing their meaning
    specifically and particularly.

  Thus a simple name 'BI' is not suitable for this theory, because we do not want any
    conflict with another more general implementation of BI. The suffix 'for_Phi'
    ensures the name to be unique.\<close>

text \<open>The implementation represents BI assertions by sets simply, in shallow embedding manner.\<close>

subsection \<open>Implication\<close>

definition Imply :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2_/ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _/ \<^bold>a\<^bold>n\<^bold>d _)" [13,13,13] 12)
  where "(A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P) \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P)"

abbreviation SimpleImply :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_/ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _)" [13,13] 12)
  where \<open>SimpleImply T U \<equiv> Imply T U True\<close>


lemma zero_implies_any[\<phi>reason 2000 for \<open>0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X\<close>
  unfolding Imply_def zero_set_def by simp

lemma implies_refl[\<phi>reason 2000 for \<open>?A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?B \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A" unfolding Imply_def by fast

lemma implies_union[\<phi>reason 800]:
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
  unfolding Imply_def pair_forall times_set_def by blast

lemma implies_right_prod:
  "U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> U' * R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U * R \<^bold>a\<^bold>n\<^bold>d P "
  unfolding Imply_def pair_forall times_set_def by blast




subsection \<open>Specialized Additive Conjunction\<close>

definition Subjection :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<^bold>s\<^bold>u\<^bold>b\<^bold>j" 13)
  where " (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = {p. p \<in> T \<and> P}"

lemma Subjection_expn[\<phi>expns]:
  "p \<in> (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> p \<in> T \<and> P"
  unfolding Subjection_def by simp

lemma Subjection_inhabited[elim!,\<phi>reason_elim!]:
  \<open>Inhabited (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<Longrightarrow> (P \<Longrightarrow> Inhabited S \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Subjection_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> Inhabited S \<and> P\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Subjection_cong[cong]:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<equiv> (S' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P')\<close>
  unfolding atomize_eq set_eq_iff by (simp add: \<phi>expns, blast)

lemma [\<phi>reason]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q)
\<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Imply_def Premise_def by (simp add: \<phi>expns)

lemma Subjection_True [simp]: "(T \<^bold>s\<^bold>u\<^bold>b\<^bold>j True) = T"  unfolding set_eq_iff by (simp add: \<phi>expns)
lemma Subjection_Flase[simp]: \<open>(T \<^bold>s\<^bold>u\<^bold>b\<^bold>j False) = 0\<close> unfolding set_eq_iff by (simp add: \<phi>expns zero_set_def)

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


subsection \<open>Existential Quantification\<close>

definition ExSet :: " ('c \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "\<exists>*" 10)
  where "ExSet S = {p. (\<exists>c. p \<in> S c)}"
notation ExSet (binder "\<exists>\<^sup>s" 10)

lemma [\<phi>expns]: "p \<in> ExSet S \<longleftrightarrow> (\<exists>c. p \<in> S c)" unfolding ExSet_def by simp

lemma ExSet_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (ExSet S) \<Longrightarrow> (\<And>x. Inhabited (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

lemma ExSet_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited (ExSet S) \<longleftrightarrow> (\<exists>x. Inhabited (S x))\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

syntax
  "_SetcomprNu" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<^bold>s\<^bold>u\<^bold>b\<^bold>j/ _./ _" [3,0,4] 3)

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
lemma [simp]: "(ExSet T * R) = (\<exists>* c. T c * R )" by (simp add: \<phi>expns set_eq_iff) blast
lemma ExSet_times[simp]: "(L * ExSet T) = (\<exists>* c. L * T c)" by (simp add: \<phi>expns set_eq_iff) blast

lemma ExSet_const[simp]: \<open>ExSet (\<lambda>_. T) = T\<close> unfolding set_eq_iff by (simp add: \<phi>expns)
lemma [simp]: \<open>(\<exists>* x. F x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x = y \<and> P x) = (F y \<^bold>s\<^bold>u\<^bold>b\<^bold>j P y)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma ExSet_ExSet[simp]:
  \<open>(X a b \<^bold>s\<^bold>u\<^bold>b\<^bold>j a. P a b \<^bold>s\<^bold>u\<^bold>b\<^bold>j b. Q b) = (X a b \<^bold>s\<^bold>u\<^bold>b\<^bold>j a b. P a b \<and> Q b)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns, blast)

lemma ExSet_SubjSet[simp]:
  \<open>(X b \<^bold>s\<^bold>u\<^bold>b\<^bold>j P b \<^bold>s\<^bold>u\<^bold>b\<^bold>j b. Q b) = (X b \<^bold>s\<^bold>u\<^bold>b\<^bold>j b. P b \<and> Q b)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma [\<phi>reason 200]: (*depreciated*)
   "(\<And>c. T c \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P c)
\<Longrightarrow> (ExSet T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d (\<exists>c. P c)"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 300]:
  \<open>(\<And>c. S c \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d P)
\<Longrightarrow> (ExSet S) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma [\<phi>reason]:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' x \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (ExSet S') \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns, blast)

lemma [\<phi>reason]:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d P x
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d (Ex P)\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns, blast)


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