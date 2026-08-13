(*TODO: lift it to a chapter*)
chapter \<open>A Bunched Implications Equipped with Satisfaction\<close>

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
\[ \<open>(x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<^emph> \<cdots> x\<^sub>n \<Ztypecolon> T\<^sub>n \<subj> a. P)\<close> \]
Readers may read it as a set,
\[ \<open>{ x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> x\<^sub>2 \<Ztypecolon> T\<^sub>2 \<^emph> \<cdots> x\<^sub>n \<Ztypecolon> T\<^sub>n |a. P }\<close> \]

\<^descr> \<^emph>\<open>Simple Multi-Term Form\<close> is a MTF where there is no existential quantification and the attached
  \<open>P\<close> is trivial \<open>True\<close>, viz., it is characterized by
  \[ \<open>x\<^sub>1 \<Ztypecolon> T\<^sub>1 \<^emph> \<cdots> \<^emph> x\<^sub>n \<Ztypecolon> T\<^sub>n\<close> \]
\<close>

text \<open>
Specifically, in this minimal specialized BI:

  \<^item> It does not have a general additive conjunction (\<open>\<and>\<close>) that connects any BI assertions,
    but only the one (\<open>A \<subj> P\<close>) connects a BI assertion \<open>A\<close> and a pure assertion \<open>P\<close>,
    because it is exactly what at most the MTF requires.

  \<^item> Implication does not occur in assertions (of \<phi>-SL), but it represents transformations of
    abstraction so has a significant role in reasoning (rules).
    We emphasize this transformation by assigning the implication with notation
    \<open>A \<transforms> B \<with> P \<triangleq> A \<longrightarrow> B \<and> P\<close>, where \<open>P\<close> is a pure assertion.
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
    We denote them by notation \<open>X \<transforms> Y \<with> P\<close>.

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
      and "<trans>" = "\<transforms>"
      and "<transforms>" = "\<transforms>"
      and "<with>"  = "\<with>"
      and "<subj>" = "\<subj>"
      and "<when>" = "\<when>"
      and "<remains>" = "\<remains>"
      and "<get>" = "\<get>"
      and "<map>" = "\<m>\<a>\<p>"
      and "<by>" = "\<by>"
      and "<from>" = "\<from>"
      and "<remaining>" = "\<remaining>"
      and "<demanding>" = "\<demanding>"
      and "<to>" = "\<to>"
      and "<over>" = "\<over>"
      and "<subst>" = "\<subst>"
      and "<for>" = "\<for>"
      and "<TP>" = "\<T>\<P>"
begin

section \<open>Judgement\<close>

datatype 'a BI = BI (dest: \<open>'a set\<close>)
hide_const (open) dest

definition Satisfaction :: \<open>'a \<Rightarrow> 'a BI \<Rightarrow> bool\<close> (infix "\<Turnstile>" 50)
  where \<open>(x \<Turnstile> A) \<longleftrightarrow> (x \<in> BI.dest A)\<close>

lemma Satisfaction_BI_red[simp]:
  \<open> x \<Turnstile> BI S \<longleftrightarrow> x \<in> S \<close>
  unfolding Satisfaction_def by simp

lemma In_BI_dest[iff]:
  \<open> x \<in> BI.dest S \<longleftrightarrow> x \<Turnstile> S \<close>
  by (cases S; simp)

subsubsection \<open>Bootstrap Basics\<close>

lemma split_BI_all: \<open>(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P (BI x))\<close> by (metis BI.collapse) 
lemma split_BI_ex: \<open>(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. P (BI x))\<close> by (metis BI.collapse) 

lemma split_BI_meta_all:
  \<open>(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (BI x)) \<close>
proof
  fix x assume \<open>\<And>x. PROP P x\<close> then show \<open>PROP P (BI x)\<close> .
next
  fix x assume \<open>\<And>x. PROP P (BI x)\<close> from this[of \<open>BI.dest x\<close>] show \<open>PROP P x\<close> by simp
qed

subsection \<open>Algebraic Properties of BI\<close>

instantiation BI :: (type) zero begin
definition zero_BI where "zero_BI = BI {}"
instance ..
end

instantiation BI :: (one) one begin
definition "one_BI = BI {1::'a}"
instance ..
end

instantiation BI :: ("{sep_disj,times}") times begin
definition "times_BI P Q = BI { x * y | x y. x \<Turnstile> P \<and> y \<Turnstile> Q \<and> x ## y }"
instance ..
end

instance BI :: ("{sep_disj,times}") mult_zero 
  by (standard; simp add: zero_BI_def times_BI_def)

instance BI :: ("{sep_magma_1,no_inverse}") no_inverse
  by (standard; simp add: one_BI_def times_BI_def set_eq_iff split_BI_meta_all;
      metis (no_types, opaque_lifting) no_inverse sep_magma_1_left sep_magma_1_right)

instantiation BI :: (type) total_sep_disj begin
definition sep_disj_BI :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> bool\<close> where [simp]: \<open>sep_disj_BI _ _ = True\<close>
instance by (standard; simp)
end

instance BI :: (sep_magma) sep_magma ..

instance BI :: (sep_magma_1) sep_magma_1 proof
  fix x :: \<open>'a BI\<close>
  show \<open>1 * x = x\<close> by (cases x; simp add: one_BI_def times_BI_def)
  show \<open>x * 1 = x\<close> by (cases x; simp add: one_BI_def times_BI_def)
  show \<open>x ## 1\<close> by simp
  show \<open>1 ## x\<close> by simp
qed

instance BI :: (sep_no_inverse) sep_no_inverse
  by (standard, simp add: one_BI_def times_BI_def set_eq_iff split_BI_meta_all;
      metis (no_types, opaque_lifting) sep_magma_1_left sep_magma_1_right sep_no_inverse)

instance BI :: (sep_disj_distrib) sep_disj_distrib by (standard; simp)

instance BI :: (sep_semigroup) semigroup_mult
  apply (standard; clarsimp simp add: times_BI_def algebra_simps set_eq_iff; rule; clarsimp)
  using sep_disj_multD2 sep_disj_multI2 sep_mult_assoc apply blast
  by (metis sep_disj_multD1 sep_disj_multI1 sep_mult_assoc)

instance BI :: (sep_monoid) monoid_mult
  by standard simp_all

instance BI :: (sep_ab_semigroup) ab_semigroup_mult
  apply (standard; simp add: times_BI_def set_eq_iff)
  using sep_disj_commute sep_mult_commute by blast

instance BI :: (sep_algebra) comm_monoid_mult
  by (standard; simp_all add: one_set_def times_set_def)

instantiation BI :: (type) comm_monoid_add begin
definition \<open>plus_BI x y = BI (BI.dest x \<union> BI.dest y)\<close>
instance by standard (auto simp add: plus_BI_def zero_BI_def split_BI_meta_all)
end

instantiation BI :: (type) order begin
definition less_BI :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> bool\<close>
  where \<open>less_BI A B \<longleftrightarrow> BI.dest A < BI.dest B\<close>
definition less_eq_BI :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> bool\<close>
  where \<open>less_eq_BI A B \<longleftrightarrow> BI.dest A \<le> BI.dest B\<close>

lemma less_BI[simp]: \<open> BI A < BI B \<longleftrightarrow> A < B \<close> unfolding less_BI_def by simp
lemma less_eq_BI[simp]: \<open> BI A \<le> BI B \<longleftrightarrow> A \<le> B \<close> unfolding less_eq_BI_def by simp

lemma less_eq_BI_iff: \<open> A \<le> B \<longleftrightarrow> (\<forall>w. w \<Turnstile> A \<longrightarrow> w \<Turnstile> B) \<close>
  by (cases A; cases B; auto)

instance by (standard; simp add: split_BI_meta_all; blast)
end

instance BI :: (type) ordered_comm_monoid_add
  by standard (auto simp add: plus_BI_def zero_BI_def split_BI_meta_all)

lemma plus_BI_S_S [simp]: \<open>S + S = S\<close> for S :: \<open>'a BI\<close> by (simp add: plus_BI_def)

instance BI :: (sep_semigroup) ordered_semiring_0
  by standard (auto simp add: zero_BI_def plus_BI_def times_BI_def split_BI_meta_all)

instance BI :: (sep_monoid) semiring_1
  by standard (auto simp add: zero_BI_def one_BI_def plus_BI_def times_BI_def split_BI_meta_all)

instance BI :: (sep_ab_semigroup) ordered_comm_semiring
  by standard (auto simp add: zero_BI_def plus_BI_def times_BI_def split_BI_meta_all set_eq_iff)

instance BI :: (sep_algebra) comm_semiring_1
  by standard auto

instantiation BI :: (type) order_top begin
definition top_BI :: \<open>'a BI\<close> where \<open>top_BI = BI top\<close>
instance by (standard; simp add: top_BI_def split_BI_meta_all)
end

instantiation BI :: (type) order_bot begin
definition bot_BI :: \<open>'a BI\<close> where \<open>bot_BI = BI bot\<close>
instance by (standard; simp add: bot_BI_def split_BI_meta_all)
end

notation inf (infixl "\<sqinter>" 70)
     and sup (infixl "\<squnion>" 65)

instantiation BI :: (type) semilattice_inf begin
definition inf_BI :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close>
  where \<open>inf_BI A B = BI (BI.dest A \<inter> BI.dest B)\<close>

lemma inf_BI_red[simp]: \<open>BI A \<sqinter> BI B = BI (A \<sqinter> B)\<close> by (simp add: inf_BI_def)

instance by (standard; simp add: split_BI_meta_all)
end

instantiation BI :: (type) semilattice_sup begin
definition sup_BI :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close>
  where \<open>sup_BI A B = BI (BI.dest A \<union> BI.dest B)\<close>

lemma sup_BI_red[simp]: \<open>BI A \<squnion> BI B = BI (A \<squnion> B)\<close> by (simp add: sup_BI_def)

instance by (standard; simp add: split_BI_meta_all)
end

instance BI :: (type) lattice by standard

instantiation BI :: (type) complete_lattice begin

definition Inf_BI :: \<open>'a BI set \<Rightarrow> 'a BI\<close>
  where \<open>Inf_BI S = BI (Inf (BI.dest ` S))\<close>
definition Sup_BI :: \<open>'a BI set \<Rightarrow> 'a BI\<close>
  where \<open>Sup_BI S = BI (Sup (BI.dest ` S))\<close>

lemma Inf_BI_expn[iff]:
  \<open> w \<Turnstile> Inf S \<longleftrightarrow> (\<forall>A\<in>S. w \<Turnstile> A) \<close>
  unfolding Inf_BI_def by (auto simp: split_BI_meta_all)

lemma Sup_BI_expn[iff]:
  \<open> w \<Turnstile> Sup S \<longleftrightarrow> (\<exists>A\<in>S. w \<Turnstile> A) \<close>
  unfolding Sup_BI_def
  by (auto simp: split_BI_meta_all)

instance by (
      (standard; (simp add: split_BI_meta_all less_eq_BI_iff)?),
      meson Satisfaction_BI_red,
      metis BI.collapse Satisfaction_def,
      simp add: Inf_BI_def top_BI_def,
      simp add: Sup_BI_def bot_BI_def)
end

subsection \<open>Basics\<close>

subsubsection \<open>Basic Operations & Rules\<close>

lemma BI_eq_iff:
  \<open>S = S' \<longleftrightarrow> (\<forall>u. u \<Turnstile> S \<longleftrightarrow> u \<Turnstile> S')\<close>
  unfolding Satisfaction_def
  by (cases S, cases S', simp add: set_eq_iff)

definition I_image :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a BI \<Rightarrow> 'b BI\<close>  (infixr "`\<^sub>I" 90)
  where \<open> f `\<^sub>I A = BI (f ` BI.dest A) \<close>

lemma I_image_red[simp]:
  \<open> f `\<^sub>I BI A = BI (f ` A) \<close>
  unfolding I_image_def
  by simp

lemma I_image_expn[iff, \<phi>expns]:
  \<open> w \<Turnstile> f `\<^sub>I A \<longleftrightarrow> (\<exists>w'. w = f w' \<and> w' \<Turnstile> A) \<close>
  by (cases A; simp; blast)

subsubsection \<open>Basic Rewrites\<close>

lemma sep_conj_expn[simp, \<phi>expns]:
  \<open>uv \<Turnstile> (S * T) \<longleftrightarrow> (\<exists>u v. uv = u * v \<and> u \<Turnstile> S \<and> v \<Turnstile> T \<and> u ## v)\<close>
  unfolding Satisfaction_def times_BI_def
  by simp

definition Subjection :: " 'p BI \<Rightarrow> bool \<Rightarrow> 'p BI " (infixl "\<subj>" 15)
  where " (T \<subj> P) = BI {p. p \<Turnstile> T \<and> P}"

lemma Subjection_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (S \<subj> P) \<longleftrightarrow> p \<Turnstile> S \<and> P\<close>
  by (cases S; simp add: Subjection_def)

(*
lemma Subjection_Id_on:
  \<open>Id_on (S \<subj> P) = (Id_on S \<subj> P)\<close>
  by (auto simp add: Subjection_expn_set)
*)

lemma Subjection_image:
  \<open>f `\<^sub>I (S \<subj> P) = (f `\<^sub>I S \<subj> P)\<close>
  unfolding BI_eq_iff
  by simp blast

definition ExBI :: " ('x \<Rightarrow> 'c BI) \<Rightarrow> 'c BI" (binder "\<exists>*" 14)
  where "ExBI S = BI {p. (\<exists>c. p \<Turnstile> S c)}"

lemma ExBI_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (ExBI S) \<longleftrightarrow> (\<exists>x. p \<Turnstile> S x)\<close>
  by (simp add: ExBI_def)

lemma Zero_expn[iff, \<phi>expns]:
  \<open>\<not> (p \<Turnstile> 0)\<close>
  unfolding Satisfaction_def
  by (simp add: zero_BI_def)

lemma One_expn[iff, \<phi>expns]:
  \<open>v \<Turnstile> 1 \<longleftrightarrow> v = 1\<close>
  unfolding Satisfaction_def
  by (simp add: one_BI_def)

lemma Top_expn[iff, \<phi>expns]:
  \<open>v \<Turnstile> top\<close>
  unfolding Satisfaction_def
  by (simp add: top_BI_def)

subsubsection \<open>Lift\<close>

definition BI_lift :: \<open>'a set \<Rightarrow> 'a BI\<close>
  where \<open>BI_lift S = BI S\<close>

lemma BI_lift_expn[iff]:
  \<open> w \<Turnstile> BI_lift S \<longleftrightarrow> w \<in> S \<close>
  unfolding BI_lift_def by simp


subsection \<open>Reasoning Configuration\<close>

\<phi>reasoner_group extract_pure_sat = (%extract_pure+100, [%extract_pure+100, %extract_pure+130])
                                    for (\<open>\<r>EIF _ _\<close>, \<open>\<r>ESC _ _\<close>)
                                     in extract_pure_all and > extract_pure
  \<open>Rules extracting BI properties down to Satisfaction\<close>

section \<open>Connectives\<close>

subsection \<open>\<phi>-Type\<close>

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete BI "

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a BI" (infix "\<Ztypecolon>" 20) where " x \<Ztypecolon> T \<equiv> T x"

text \<open>Convention of name:

In \<open>x \<Ztypecolon> T\<close>, we refer to \<open>x\<close> as the \<^emph>\<open>object\<close> or the \<^emph>\<open>\<phi>-type term\<close> and \<open>T\<close> as the \<^emph>\<open>\<phi>-type\<close>.
For convenience, when the context is unambiguous, we also call the entire \<open>x \<Ztypecolon> T\<close> as '\<phi>-type',
but as \<^emph>\<open>\<phi>-type assertion\<close> to be precise.
\<close>

subsubsection \<open>Basic \& Auxiliary Rules\<close>

lemma \<phi>Type_eqI:
  \<open>(\<forall>x p. p \<Turnstile> (x \<Ztypecolon> a) \<longleftrightarrow> p \<Turnstile> (x \<Ztypecolon> b)) \<Longrightarrow> a = b\<close>
  unfolding \<phi>Type_def Satisfaction_def
  by (metis ext less_BI_def less_eq_BI_def order.order_iff_strict subset_iff subset_not_subset_eq)

lemma \<phi>Type_protect_type_cong:
  \<open> x \<equiv> x'
\<Longrightarrow> x \<Ztypecolon> T \<equiv> x' \<Ztypecolon> T\<close>
  by simp

setup \<open>Context.theory_map (PLPR_Rule_Gen.Rule_Gen_SS.map (
  Simplifier.add_cong @{thm' \<phi>Type_protect_type_cong}))\<close>

ML_file \<open>library/tools/simp_congruence.ML\<close>

subsection \<open>Inhabitance\<close>

definition Satisfiable :: " 'a BI \<Rightarrow> bool "
  where "Satisfiable S = (\<exists>p. p \<Turnstile> S)"
  \<comment> \<open>\<open>Satisfiable S\<close> should be always regarded as an atom in the view of ATPs.

      The fallback of extracting implied pure facts returns the original \<open>Satisfiable T\<close> unchanged,
      \<open>P \<implies> Satisfiable P\<close> where \<open>Satisfiable P\<close> should be regarded as an atom.\<close>

definition Inhabited
  where \<open>Inhabited T \<longleftrightarrow> (\<exists>x. Satisfiable (x \<Ztypecolon> T))\<close>


abbreviation Inhabitance_Implication :: \<open>'a BI \<Rightarrow> bool \<Rightarrow> bool\<close> (infix "\<implies>" 10)
  where \<open>S \<implies> P \<equiv> \<r>EIF (Satisfiable S) P \<close>
  \<comment> \<open>P is weaker than S. We want to get a simpler P and as strong as possible. \<close>

abbreviation Sufficient_Inhabitance :: \<open>bool \<Rightarrow> 'a BI \<Rightarrow> bool\<close> (infix "\<suffices>" 10)
  where \<open>P \<suffices> S \<equiv> \<r>ESC P (Satisfiable S) \<close>
  \<comment> \<open>P is stronger than S. We want to get a simpler P and as weak as possible. \<close>

declare [[
  \<phi>reason_default_pattern \<open>Satisfiable ?X \<longrightarrow> _\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>bad form\<close>)\<close> (100)
                      and \<open>_ \<longrightarrow> Satisfiable ?X\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>bad form\<close>)\<close> (100)
                      and \<open>Inhabited ?T\<close>  \<Rightarrow> \<open>Inhabited ?T\<close>      (100),
  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>Inhabited _\<close>  (%\<phi>attr)
]]

\<phi>reasoner_group extract_pure_phity = (10, [10,10]) for (\<open>x \<Ztypecolon> T \<implies> P\<close>, \<open>P \<suffices> x \<Ztypecolon> T\<close>)
  > extract_pure_fallback and < extract_pure
  \<open>Entry points towards \<open>Abstract_Domain\<close> and \<open>Abstract_Domain\<^sub>L\<close> \<close>

\<phi>reasoner_group inhabited_all = (100, [10, 3000]) for (\<open>Inhabited T\<close>) \<open>\<close>
  and inhabited = (1000, [1000, 1030]) in inhabited_all \<open>\<close>
  and inhabited_derived = (40, [30,50]) in inhabited_all and < inhabited \<open>\<close>
  and inhabited_default = (10, [10,20]) in inhabited_all and < inhabited_derived \<open>\<close>

subsubsection \<open>Basic Rules\<close>

lemma Satisfiable_I:
  \<open>x \<Turnstile> S \<Longrightarrow> Satisfiable S\<close>
  unfolding Satisfiable_def ..

lemma Satisfiable_fallback:
  \<open> X \<implies> Satisfiable X \<close>
  unfolding \<r>EIF_def by blast

lemma Suf_Satisfiable_fallback:
  \<open> Satisfiable X \<suffices> X \<close>
  unfolding \<r>ESC_def by blast

\<phi>reasoner_ML Satisfiable_fallback default 2 (\<open>_ \<implies> _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.is_generating_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Satisfiable_fallback} RS sequent), Seq.empty)
)\<close>

\<phi>reasoner_ML Suf_Satisfiable_fallback default 2 (\<open>_ \<suffices> _\<close>) =
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.is_generating_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Suf_Satisfiable_fallback} RS sequent), Seq.empty)
)\<close>

lemma [\<phi>reason 1000]:
  \<open> P \<suffices> A
\<Longrightarrow> \<premise> P
\<Longrightarrow> Satisfiable A\<close>
  unfolding \<r>ESC_def Premise_def
  by blast

lemma inhabited_type_EIF':
  \<open> \<r>EIF (Inhabited T) (\<exists>x. Satisfiable (x \<Ztypecolon> T)) \<close>
  unfolding Inhabited_def \<r>EIF_def
  by blast

bundle deriving_intabited_type = inhabited_type_EIF'[\<phi>reason default %extract_pure]



paragraph \<open>Sum Type\<close>

lemma [\<phi>reason 1020]:
  \<open> A a \<implies> P
\<Longrightarrow> case_sum A B (Inl a) \<implies> P\<close>
  by simp

lemma [\<phi>reason 1020]:
  \<open> B b \<implies> P
\<Longrightarrow> case_sum A B (Inr b) \<implies> P\<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> A a \<implies> P a)
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> B b \<implies> Q b)
\<Longrightarrow> case_sum A B x \<implies> case_sum P Q x \<close>
  by (cases x; simp)



subsection \<open>Abstract Domain\<close>

lemma typing_inhabited: "p \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> Satisfiable (x \<Ztypecolon> T)"
  unfolding Satisfiable_def \<phi>Type_def by blast

definition Abstract_Domain :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Abstract_Domain T d \<longleftrightarrow> (\<forall>x. x \<Ztypecolon> T \<implies> d x)\<close>
  \<comment> \<open>Upper Bound\<close>

definition Abstract_Domain\<^sub>L :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Abstract_Domain\<^sub>L T d \<longleftrightarrow> (\<forall>x. d x \<suffices> x \<Ztypecolon> T)\<close>
  \<comment> \<open>Lower Bound\<close>

declare [[
  \<phi>reason_default_pattern \<open>Abstract_Domain ?T _\<close> \<Rightarrow> \<open>Abstract_Domain ?T _\<close> (100)
                      and \<open>Abstract_Domain\<^sub>L ?T _\<close> \<Rightarrow> \<open>Abstract_Domain\<^sub>L ?T _\<close> (100),
  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>Abstract_Domain  _ _\<close>  (%\<phi>attr) ,
  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>Abstract_Domain\<^sub>L _ _\<close>  (%\<phi>attr)
]]

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

  and extract_implies = (%extract_pure+40, [%extract_pure+40, %extract_pure+70])
                       for (\<open>\<r>EIF (A \<implies> P) Q\<close>, \<open>\<r>ESC Q (A \<implies> P)\<close>,
                            \<open>\<r>EIF (A \<suffices> P) Q\<close>, \<open>\<r>ESC Q (A \<suffices> P)\<close>)
                       and > extract_pure and < extract_pure_sat \<open>\<close>


subsubsection \<open>Extracting Pure Facts\<close>

lemma Inhabitance_Implication_\<A>EIF [\<phi>reason %extract_implies]:
  \<open> \<r>ESC A' (Satisfiable A)
\<Longrightarrow> \<r>EIF (A \<implies> P) (A' \<longrightarrow> P) \<close>
  unfolding \<r>EIF_def \<r>ESC_def
  by blast

lemma Inhabitance_Implication_\<A>EIF_Sat:
  \<open> \<r>EIF (A \<implies> P) ((\<exists>v. v \<Turnstile> A) \<longrightarrow> P) \<close>
  unfolding \<r>EIF_def Satisfiable_def
  by blast

lemma Inhabitance_Implication_\<A>ESC[\<phi>reason %extract_implies]:
  \<open> \<r>EIF (Satisfiable A) A'
\<Longrightarrow> \<r>ESC (A' \<longrightarrow> P) (A \<implies> P) \<close>
  unfolding \<r>EIF_def \<r>ESC_def
  by blast

lemma Inhabitance_Implication_\<A>ESC_Sat:
  \<open> \<r>ESC ((\<exists>v. v \<Turnstile> A) \<longrightarrow> P) (A \<implies> P) \<close>
  unfolding \<r>ESC_def \<r>EIF_def Satisfiable_def
  by blast

lemma Sufficient_Inhabitance_\<A>EIF[\<phi>reason %extract_implies]:
  \<open> \<r>EIF (Satisfiable A) A'
\<Longrightarrow> \<r>EIF (P \<suffices> A) (P \<longrightarrow> A') \<close>
  unfolding \<r>EIF_def \<r>ESC_def
  by blast

lemma Sufficient_Inhabitance_\<A>EIF_Sat:
  \<open> \<r>EIF (P \<suffices> A) (P \<longrightarrow> (\<exists>v. v \<Turnstile> A)) \<close>
  unfolding \<r>EIF_def \<r>ESC_def Satisfiable_def
  by blast

lemma Sufficient_Inhabitance_\<A>ESC[\<phi>reason %extract_implies]:
  \<open> \<r>ESC A' (Satisfiable A)
\<Longrightarrow> \<r>ESC (P \<longrightarrow> A') (P \<suffices> A) \<close>
  unfolding \<r>EIF_def \<r>ESC_def
  by blast

lemma Sufficient_Inhabitance_\<A>ESC_Sat:
  \<open> \<r>ESC (P \<longrightarrow> (\<exists>v. v \<Turnstile> A)) (P \<suffices> A) \<close>
  unfolding \<r>ESC_def Satisfiable_def
  by blast

bundle extracting_Inhabitance_Implication_sat =
          Inhabitance_Implication_\<A>EIF_Sat [\<phi>reason %extract_pure_sat]
          Inhabitance_Implication_\<A>ESC_Sat [\<phi>reason %extract_pure_sat]
bundle extracting_Sufficient_Inhabitance_sat =
          Sufficient_Inhabitance_\<A>EIF_Sat [\<phi>reason %extract_pure_sat]
          Sufficient_Inhabitance_\<A>ESC_Sat [\<phi>reason %extract_pure_sat]
bundle extracting_Inhabitance_sat begin
  unbundle extracting_Inhabitance_Implication_sat and extracting_Sufficient_Inhabitance_sat
end

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. \<r>EIF ((x \<Ztypecolon> T) \<implies> D x) (P x))
\<Longrightarrow> \<r>EIF (Abstract_Domain T D) (All P) \<close>
  unfolding Abstract_Domain_def \<r>EIF_def
  by blast

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. \<r>ESC (P x) ((x \<Ztypecolon> T) \<implies> D x))
\<Longrightarrow> \<r>ESC (All P) (Abstract_Domain T D) \<close>
  unfolding Abstract_Domain_def \<r>ESC_def
  by blast

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. \<r>EIF (D x \<suffices> (x \<Ztypecolon> T)) (P x))
\<Longrightarrow> \<r>EIF (Abstract_Domain\<^sub>L T D) (All P) \<close>
  unfolding Abstract_Domain\<^sub>L_def \<r>EIF_def
  by blast

lemma [\<phi>reason %extract_pure_all]:
  \<open> (\<And>x. \<r>ESC (P x) (D x \<suffices> (x \<Ztypecolon> T)))
\<Longrightarrow> \<r>ESC (All P) (Abstract_Domain\<^sub>L T D) \<close>
  unfolding Abstract_Domain\<^sub>L_def \<r>ESC_def
  by blast


subsubsection \<open>Basic Rules\<close>

lemma Abstract_Domain_sub:
  \<open> (\<forall>x. D x \<longrightarrow> D' x)
\<Longrightarrow> Abstract_Domain T D
\<Longrightarrow> Abstract_Domain T D' \<close>
  unfolding Abstract_Domain_def \<r>EIF_def
  by auto

lemma Abstract_Domain\<^sub>L_sub:
  \<open> (\<forall>x. D' x \<longrightarrow> D x)
\<Longrightarrow> Abstract_Domain\<^sub>L T D
\<Longrightarrow> Abstract_Domain\<^sub>L T D' \<close>
  unfolding Abstract_Domain\<^sub>L_def \<r>ESC_def
  by auto

lemma [\<phi>reason default %extract_pure_phity]:
  \<open> Abstract_Domain T D
\<Longrightarrow> x \<Ztypecolon> T \<implies> D x\<close>
  unfolding Abstract_Domain_def Action_Tag_def
  by blast

lemma [\<phi>reason default %extract_pure_phity]:
  \<open> Abstract_Domain\<^sub>L T D
\<Longrightarrow> D x \<suffices> x \<Ztypecolon> T\<close>
  unfolding Abstract_Domain\<^sub>L_def Action_Tag_def
  by blast

lemma [\<phi>reason default %inhabited_default]:
  \<open> Abstract_Domain\<^sub>L T D
\<Longrightarrow> \<premise> (\<exists>x. D x)
\<Longrightarrow> Inhabited T \<close>
  unfolding Inhabited_def Abstract_Domain\<^sub>L_def Premise_def \<r>ESC_def
  by blast

subsubsection \<open>Fallback\<close>

lemma [\<phi>reason default %abstract_domain_fallback]:
  \<open> Abstract_Domain T (\<lambda>x. Satisfiable (x \<Ztypecolon> T)) \<close>
  unfolding Abstract_Domain_def \<r>EIF_def
  by simp

lemma [\<phi>reason default %abstract_domain_fallback]:
  \<open> Abstract_Domain\<^sub>L T (\<lambda>x. Satisfiable (x \<Ztypecolon> T)) \<close>
  unfolding Abstract_Domain\<^sub>L_def \<r>ESC_def
  by simp

subsubsection \<open>Configuration\<close>

declare [[
  \<phi>reason_default_pattern_ML \<open>?x \<Ztypecolon> ?T \<implies> _\<close> \<Rightarrow> \<open>
    fn ctxt => fn tm as (_ (*Trueprop*) $ (_ (*\<r>EIF*) $ (
                            _ (*Satisfiable*) $ (_ (*\<phi>Type*) $ x $ _)) $ _)) =>
      if is_Var x orelse not (Context_Position.is_visible_generic ctxt)
      then NONE
      else error (let open Pretty in string_of (chunks [
            para "Malformed Implication Rule: in \<open>x \<Ztypecolon> T \<implies> _\<close> the x must be a schematic variable. But given",
            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
          ]) end)\<close> (1000),

  \<phi>reason_default_pattern_ML \<open>_ \<suffices> _ \<Ztypecolon> _\<close> \<Rightarrow> \<open>
    fn ctxt => fn tm as (_ (*Trueprop*) $ (_ (*\<r>ESC*) $ _ $ (
                            _ (*Satisfiable*) $ (_ (*\<phi>Type*) $ x $ _)))) =>
      if is_Var x orelse not (Context_Position.is_visible_generic ctxt)
      then NONE
      else error (let open Pretty in string_of (chunks [
            para "Malformed Sufficiency Rule: in \<open>_ \<suffices> x \<Ztypecolon> T\<close> the x must be a schematic variable. But given",
            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt tm
          ]) end)\<close> (1000)
]]

setup \<open> PLPR_Template_Properties.add_property_kinds [
  \<^pattern_prop>\<open>Abstract_Domain _ _\<close>, \<^pattern_prop>\<open>Abstract_Domain\<^sub>L _ _\<close>
]\<close>

subsubsection \<open>Template Instantiation\<close>

lemma Satisfiable_rewr_template[\<phi>reason_template name T.inh_rewr [simp]]:
  \<open> Abstract_Domain T D
\<Longrightarrow> Abstract_Domain\<^sub>L T D'
\<Longrightarrow> \<condition> (\<forall>x. D' x = D x) @tag \<A>_template_reason None
\<Longrightarrow> Satisfiable (x \<Ztypecolon> T) \<equiv> D x \<close>
  unfolding \<r>EIF_def \<r>ESC_def Action_Tag_def Abstract_Domain_def Abstract_Domain\<^sub>L_def Premise_def
  by (clarsimp, smt (verit, best))


subsection \<open>Auxiliary Tag\<close>

definition \<phi>Tag :: \<open>mode \<Rightarrow> ('c,'x) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close>
  where \<open>\<phi>Tag mode T \<equiv> T\<close>

definition \<phi>TagA :: \<open>mode \<Rightarrow> 'c BI \<Rightarrow> 'c BI\<close>
  where \<open>\<phi>TagA mode T \<equiv> T\<close>


subsection \<open>Transformation of Abstraction\<close>

text \<open>The only meaningful implication \<open>\<longrightarrow>\<close> under the interpretation of \<phi> data refinement\<close>

definition Transformation :: " 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool \<Rightarrow> bool " ("(2_)/ \<transforms> (2_)/ \<with> (2_)" [13,13,13] 12)
  where "(A \<transforms> B \<with> P) \<longleftrightarrow> (\<forall>v. v \<Turnstile> A \<longrightarrow> v \<Turnstile> B \<and> P)"
  \<comment> \<open>Implementation notes: It is safe to unfold Transformation but unsafe to unfold Satisfaction.
      Transformation is always based on Satisfaction but in future when we upgrade our logic onto
      impredicativeness, the definition of Satisfaction will be changed.
      Satisfaction is the bottom abstraction layer.\<close>

abbreviation SimpleTransformation :: " 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool " ("(2_)/ \<transforms> (2_)" [13,13] 12)
  where \<open>SimpleTransformation T U \<equiv> Transformation T U True\<close>

text \<open>
Transformation \<open>x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<subj> y. f x y\<close> and its dual \<open>y \<Ztypecolon> U \<transforms> x \<Ztypecolon> T \<subj> x. g x y\<close>
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
  \<open> (\<And>x. x \<Ztypecolon> T \<transforms> x \<Ztypecolon> U)
\<Longrightarrow> (\<And>x. x \<Ztypecolon> U \<transforms> x \<Ztypecolon> T)
\<Longrightarrow> T = U\<close>
  unfolding \<phi>Type_def Transformation_def
  by auto (meson BI_eq_iff ext)

lemma \<phi>Type_eqI_BI:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (x \<Ztypecolon> U))
\<Longrightarrow> T = U \<close>
  unfolding \<phi>Type_def fun_eq_iff
  by blast

lemma transformation_refl[simp]:
  "A \<transforms> A" unfolding Transformation_def by fast

lemma transformation_trans:
  "A \<transforms> B \<with> P
\<Longrightarrow> (P \<Longrightarrow> B \<transforms> C \<with> Q)
\<Longrightarrow> A \<transforms> C \<with> P \<and> Q"
  unfolding Transformation_def Premise_def by auto

lemma mk_intro_transformation:
  \<open> A \<transforms> B
\<Longrightarrow> X \<transforms> A \<with> P
\<Longrightarrow> X \<transforms> B \<with> P \<close>
  unfolding Transformation_def
  by simp

lemma mk_elim_transformation:
  \<open> A \<transforms> B
\<Longrightarrow> B \<transforms> Y \<with> P
\<Longrightarrow> A \<transforms> Y \<with> P \<close>
  unfolding Transformation_def
  by simp blast

lemma transformation_weaken:
  \<open> P \<longrightarrow> P'
\<Longrightarrow> A \<transforms> B \<with> P
\<Longrightarrow> A \<transforms> B \<with> P'\<close>
  unfolding Transformation_def by simp

lemma transformation_intro_inhab:
  \<open> (\<premise> Satisfiable A \<Longrightarrow> A \<transforms> B \<with> P)
\<Longrightarrow> A \<transforms> B \<with> P \<close>
  unfolding Transformation_def Satisfiable_def Satisfaction_def
  by blast

lemma assertion_eq_intro:
  \<open> P \<transforms> Q
\<Longrightarrow> Q \<transforms> P
\<Longrightarrow> P = Q\<close>
  unfolding Transformation_def BI_eq_iff by blast

lemma BI_eq_ToA:
  \<open> P = Q \<longleftrightarrow> (P \<transforms> Q) \<and> (Q \<transforms> P) \<close>
  unfolding BI_eq_iff Transformation_def
  by blast

lemma BI_sub_transformation:
  \<open> S \<le> S' \<longleftrightarrow> (S \<transforms> S') \<close>
  unfolding Transformation_def Satisfaction_def subset_iff
  by (simp add: less_eq_BI_def subset_iff)

lemma BI_sub_iff:
  \<open> S \<le> S' \<longleftrightarrow> (\<forall>u. u \<Turnstile> S \<longrightarrow> u \<Turnstile> S') \<close>
  unfolding Satisfaction_def subset_iff
  by (meson less_eq_BI_def subset_eq)

lemma transformation_protector:
  \<open>A \<transforms> B \<with> P \<equiv> A \<transforms> B \<with> P\<close> .

subsubsection \<open>Forms of Reasoning\<close>

consts \<T>\<P>  :: action \<comment> \<open>Transformation Problem, x : T --> f(x) : U, or between assertions, can be abductive
                         but never bi-abductive.\<close>
       \<T>\<P>' :: action \<comment> \<open>Bi-abductive Transformation Problem with Remainders and Demands, x : T * W --> f(x) : U * R\<close>
       \<A>clean :: action

abbreviation \<A>clean' :: \<open>bool \<Rightarrow> bool\<close> ("_/ @clean" [9] 9)
  where \<open>P @clean \<equiv> P @tag \<A>clean\<close>

text \<open>There are two kinds of transformation rule

\<^item> cast-rule: \<open>x \<Ztypecolon> T \<transforms> f(x) \<Ztypecolon> U \<with> P(x)\<close> binding on pattern \<open>x \<Ztypecolon> T \<transforms> _ \<Ztypecolon> U \<with> _\<close>,
  which specifies how to transform a given \<phi>-type \<open>x \<Ztypecolon> T\<close> into the target type \<open>U\<close> and what is the
  resulted abstract object with yielding any auxiliary pure facts \<open>P(x)\<close>.

\<^item> intro-rule: \<open>X \<transforms> g(y) \<Ztypecolon> U' \<with> P \<Longrightarrow> X \<transforms> y \<Ztypecolon> U \<with> P \<and> Q(y)\<close> binding on
  pattern \<open>_ \<transforms> y \<Ztypecolon> U \<with> _\<close>, which specifies how to construct \<open>y \<Ztypecolon> U\<close> by construction
  from \<open>g(y) \<Ztypecolon> U'\<close>.
    
\<^item> elim-rule: \<open>g(x) \<Ztypecolon> T' \<transforms> Y \<with> P \<Longrightarrow> x \<Ztypecolon> T \<transforms> Y \<with> P \<and> Q(x)\<close> binding on
  pattern \<open>x \<Ztypecolon> T \<transforms> _ \<with> _\<close>, which specifies how to destruct \<open>x \<Ztypecolon> T\<close> in sense of opening
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


text \<open>Upon above, we present in addition two extension forms providing partial transformations
  where a part of the source object may transform to only a part of the target object, leaving some
  remainder of the source and some unsolved target part for later reasoning.

\<^enum> \<open>x \<Ztypecolon> T \<transforms> f(x) \<Ztypecolon> U\<close>, the usual one-\<phi>type-to-one-\<phi>type transformation.
\<^enum> \<open>x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<transforms> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close> or alternatively
  \<open>x \<Ztypecolon> T \<transforms> f(x) \<Ztypecolon> U \<remains>[Cr] R(x)\<close>, the transformation with remainders
\<^enum> \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<transforms> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close>, with both remainders and unsolved target parts.

where \<open>Cw, Cr\<close> are boolean conditions deciding if the remainder and respectively the unsolved aims
are presented.
The forms constitute a lattice where the reasoning of the bottom reduce to the top.

Note \<open>x \<Ztypecolon> T \<transforms> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close> is not admissible though it is syntactically valid.
As it is entailed by the more general \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<transforms> (f(x), r(x)) \<Ztypecolon> U \<^emph>[Cr] R\<close>, and more
important, the pattern of \<open>x \<Ztypecolon> T \<transforms> \<dots>\<close> also covers that of \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<transforms> _\<close> when \<open>T\<close>
is variable, meaning inefficiency in selecting rule during reasoning, we dismiss \<open>x \<Ztypecolon> T \<transforms> \<dots>\<close>
for the sake of reasoning performance and reducing the total number of reasoning rules.

In this way, designers of \<phi>-types only require to provide two forms of rules,
\<open>x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U\<close> and \<open>x \<Ztypecolon> T \<^emph>[Cw] W \<transforms> y \<Ztypecolon> U \<^emph>[Cr] R\<close>
\<close>

definition REMAINS :: \<open> 'a::sep_magma_1 BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<close> ("_ \<remains> _" [14,14] 13)
  where \<open>(X \<remains> R) \<equiv> X * R\<close>
  \<comment> \<open>The \<open>C\<close> should be a variable sending to the later reasoning which decides if the transformation
      results in some remainders. Or, exceptionally, \<open>C\<close> can be constant \<open>True\<close> for unital algebras
      and the later reasoning sets the remainder to \<open>1\<close> if it does not really results in remainders.

      It means, every reasoning procedure should prepare two versions, the one for variable \<open>C\<close>
      and another for the \<open>C\<close> of constant \<open>True\<close>.

      A reasoning procedure can at any time if on a unital algebra, set a variable \<open>C\<close> to \<open>True\<close>
      and turns the reasoning into the unital mode.\<close>

definition \<phi>Prod :: " ('concrete::sep_magma, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b). A a * B b)"

definition \<phi>Prod' :: " ('concrete::sep_magma_1, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<OTast>" 67)
  where "\<phi>Prod' = \<phi>Prod"

lemma \<phi>Prod_expn[\<phi>expns, simp]:
  "concrete \<Turnstile> (x \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>ca cb. concrete = ca * cb \<and> cb \<Turnstile> (snd x \<Ztypecolon> B) \<and> ca \<Turnstile> (fst x \<Ztypecolon> A) \<and> ca ## cb)"
  unfolding \<phi>Prod_def \<phi>Type_def by (cases x; simp) blast

definition \<phi>None :: \<open>('v::one, 'x) \<phi>\<close> ("\<circle>") where \<open>\<circle> = (\<lambda>x. 1)\<close>


text \<open>In reasoning, the \<open>P,R,W\<close> in any goal are always OUT-arguments.\<close>

ML \<open>val phi_allow_source_object_to_be_not_variable =
          Config.declare_bool ("phi_allow_source_object_to_be_not_variable", \<^here>) (K false)\<close>

ML_file \<open>library/syntax/transformation.ML\<close>

declare [[
  (*a general checker warns if the abstract object of the source is not a variable*)
  \<phi>reason_default_pattern_ML \<open>_ \<Ztypecolon> _ \<transforms> _ \<with> _\<close> \<Rightarrow> \<open>fn ctxt =>
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
      \<open>?X \<transforms> ?Y \<with> _\<close> \<Rightarrow> \<open>ERROR(TEXT(\<open>Transformation rules must be tagged by either of the following categories, \<T>\<P>, \<T>\<P>'\<close>))\<close> (10)
  and \<open>?X \<transforms> ?Y \<with> ?P @tag \<T>\<P>\<close> \<Rightarrow>
      \<open>ERROR(TEXT(\<open>Malformed Rule\<close> (?X \<transforms> ?Y \<with> ?P @tag \<T>\<P>)))\<close> (10)
  and \<open>?X \<transforms> ?Y \<with> ?P @tag \<T>\<P>'\<close> \<Rightarrow>
      \<open>ERROR(TEXT(\<open>Malformed Rule\<close> (?X \<transforms> ?Y \<with> ?P @tag \<T>\<P>')))\<close> (10)

  and \<open>?X \<transforms> ?Y \<with> ?P @tag \<T>\<P>\<close> \<Rightarrow>
      \<open>?X \<transforms> ?Y \<with> _  @tag \<T>\<P>\<close>   (30)
  and \<open>?X \<transforms> ?Y \<remains> _ \<with> _ @tag \<T>\<P>\<close>
   \<Rightarrow> \<open>?X \<transforms> ?Y \<remains> _ \<with> _ @tag \<T>\<P>\<close> (50)
  and \<open>?X \<transforms> \<phi>TagA ?mode (?Y \<remains> _) \<with> _ @tag \<T>\<P>\<close>
   \<Rightarrow> \<open>?X \<transforms> \<phi>TagA ?mode (?Y \<remains> _) \<with> _ @tag \<T>\<P>\<close> (50)
  and \<open>?X \<transforms> _ \<Ztypecolon> ?U \<remains> _ \<with> _ @tag \<T>\<P>\<close>
   \<Rightarrow> \<open>?X \<transforms> ?var_y \<Ztypecolon> ?U \<remains> _ \<with> _ @tag \<T>\<P>\<close> (60)
  and \<open>?X \<transforms> \<phi>TagA ?mode (_ \<Ztypecolon> ?U \<remains> _) \<with> _ @tag \<T>\<P>\<close>
   \<Rightarrow> \<open>?X \<transforms> \<phi>TagA ?mode (?var_y \<Ztypecolon> ?U \<remains> _) \<with> _ @tag \<T>\<P>\<close> (60)
  and \<open>?X \<transforms> _ \<Ztypecolon> ?U \<with> _ @tag \<T>\<P>\<close>
   \<Rightarrow> \<open>?X \<transforms> ?var_y \<Ztypecolon> ?U \<with> _ @tag \<T>\<P>\<close> (60)
  and \<open>?X \<transforms> \<phi>TagA ?mode (_ \<Ztypecolon> ?U) \<with> _ @tag \<T>\<P>\<close>
   \<Rightarrow> \<open>?X \<transforms> \<phi>TagA ?mode (?var_y \<Ztypecolon> ?U) \<with> _ @tag \<T>\<P>\<close> (60)

  and \<open>?x \<Ztypecolon> ?T \<transforms> ?y \<Ztypecolon> ?U \<^emph> ?R \<with> ?P @tag \<T>\<P>\<close> \<Rightarrow>
          \<open>ERROR TEXT(\<open>Malformed Rule. Please use\<close>
                      (x \<Ztypecolon> ?T \<^emph> 1 \<transforms> ?y \<Ztypecolon> ?U \<^emph> ?R \<with> ?P)
                      \<open>instead of the given\<close>
                      (?x \<Ztypecolon> ?T \<transforms> ?y \<Ztypecolon> ?U \<^emph> ?R \<with> ?P @tag \<T>\<P>))\<close> (71)
  

  and \<open>_ \<Ztypecolon> ?T \<OTast> _ \<transforms> ?var_Y \<with> _ @tag \<T>\<P>'\<close>
   \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<OTast> _ \<transforms>  _ \<with> _ @tag \<T>\<P>'\<close> (40)
  and \<open>?var_X \<transforms> _ \<Ztypecolon> ?U \<OTast> _ \<with> _ @tag \<T>\<P>'\<close>
   \<Rightarrow> \<open>_ \<transforms> _ \<Ztypecolon> ?U \<OTast> _ \<with> _ @tag \<T>\<P>'\<close> (40)
  and \<open>(?var_x, _) \<Ztypecolon> ?T \<OTast> _ \<transforms> _ \<Ztypecolon> ?U \<OTast> _ \<with> _ @tag \<T>\<P>'\<close>
   \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<OTast> _ \<transforms> ?var_y \<Ztypecolon> ?U \<OTast> _ \<with> _ @tag \<T>\<P>'\<close> (50)
  and \<open>?var_x \<Ztypecolon> ?T \<OTast> _ \<transforms> _ \<Ztypecolon> ?U \<OTast> _ \<with> _ @tag \<T>\<P>'\<close>
   \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<OTast> _ \<transforms> ?var_y \<Ztypecolon> ?U \<OTast> _ \<with> _ @tag \<T>\<P>'\<close> (50)


  and \<open>?X \<transforms> ?Y \<with> ?P @clean\<close>
   \<Rightarrow> \<open>ERROR TEXT(\<open>cannot infer the binding pattern of\<close> (?X \<transforms> ?Y \<with> ?P)
                  \<open>Please indicate manually\<close>)\<close> (10)
  and \<open>?var_X \<transforms> ?Y @clean\<close> \<Rightarrow> \<open>_ \<transforms> ?Y \<with> _ @clean\<close> (20)
  and \<open>?X \<transforms> ?var_Y @clean\<close> \<Rightarrow> \<open>?X \<transforms> _ \<with> _ @clean\<close> (20)
  and \<open>?var_x \<Ztypecolon> ?var_T \<transforms> _ \<Ztypecolon> ?U @clean\<close> \<Rightarrow> \<open>_ \<transforms> _ \<Ztypecolon> ?U \<with> _ @clean\<close> (25)
  and \<open>_ \<Ztypecolon> ?T \<transforms> ?var_y \<Ztypecolon> ?var_U @clean\<close> \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<transforms> _ \<with> _ @clean\<close> (25)
  and \<open>?var_X \<transforms> _ \<Ztypecolon> ?U @clean\<close> \<Rightarrow> \<open>_ \<transforms> _ \<Ztypecolon> ?U \<with> _ @clean\<close> (25)
  and \<open>_ \<Ztypecolon> ?T \<transforms> ?var_Y @clean\<close> \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<transforms> _ \<with> _ @clean\<close> (25)
  and \<open>?X \<transforms> 1 @clean\<close> \<Rightarrow> \<open>?X \<transforms> _ \<with> _ @clean\<close> (100)
  and \<open>1 \<transforms> ?Y @clean\<close> \<Rightarrow> \<open>_ \<transforms> ?Y \<with> _ @clean\<close> (100)
  and \<open>?X \<transforms> _ \<Ztypecolon> \<circle> @clean\<close> \<Rightarrow> \<open>?X \<transforms> _ \<with> _ @clean\<close> (100)
  and \<open>_ \<Ztypecolon> \<circle> \<transforms> ?Y @clean\<close> \<Rightarrow> \<open>_ \<transforms> ?Y \<with> _ @clean\<close> (100)
]]

lemma REMAINS_expn[\<phi>expns,simp]:
  \<open> p \<Turnstile> (A \<remains> R) \<longleftrightarrow> (p \<Turnstile> A * R) \<close>
  unfolding REMAINS_def
  by simp

subsubsection \<open>Allocation of Priorities\<close>

\<phi>reasoner_group
  ToA_all         = (100, [0, 4999]) for \<open>_ \<transforms> _ \<with> _\<close>
                    \<open>Rules of transformation\<close>
  ToA_bottom      = (0, [0, 15]) in ToA_all
                    \<open>System transformation rules, of the lowest priority\<close>
  ToA             = (100, [16, 4999]) in ToA_all > ToA_bottom
                    \<open>User rules for transformation\<close>
  ToA_bk          = (100, [16, 999]) in ToA
                    \<open>Backtracking rules\<close>
  ToA_cut         = (1000, [1000, 1399]) in ToA
                    \<open>Deterministic transformation rules without backtracking, meaning the reasoning
                     on the specified cases is definite and no branching.\<close>
  NToA_tgt        = (1430, [1400, 1499]) > ToA_cut in ToA
                    \<open>\<close>
  ToA_splitting     = (1550, [1500,1599]) > ToA_cut in ToA
                    \<open>Transformation rules splitting the reasoning goal into more subgoals\<close>
  ToA_splitting_target = (1600, [1600,1601]) > ToA_splitting in ToA
                    \<open>split the separation sequent in the target part and reason the tranformation for
                     each separated item one by one.\<close>
  ToA_assertion_cut = (1700, [1700,1899]) > ToA_splitting in ToA
                    \<open>Deterministic transformation rules between unsplitted assertions.\<close>
  ToA_normalizing = (2000, [1950, 2299]) > ToA_assertion_cut in ToA
                    \<open>Rules normalizing the transformation problem. A normalization rule should neither
                     branch nor yield new subgoal, i.e., always from onetransformation to another
                     transformaiton. If it branches, see %ToA_branches; if yields new assertions,
                     see %ToA_assertion_cut\<close>
  ToA_fixes_quant = (2500, [2500, 2590]) > NToA_tgt in ToA
                    \<open>Transformation rules fixing quantified variables.\<close>
  ToA_red         = (2600, [2600, 2649]) > ToA_fixes_quant in ToA
                    \<open>Transformation rules reducing literal or trivial cases.\<close>
  ToA_success     = (3000, [2960, 3499])
                    \<open>Transformation rules that are shortcuts leading to success on special cases\<close>
  ToA_systop      = (4900, [4900, 4999]) in ToA
                    \<open>System rules of the highest priority\<close>
  ToA_assigning_var = (4100, [4100, 4110]) in ToA and < ToA_systop
                    \<open>Tranformation rules assigning variable targets or sources, of the highest priority
                     as occurrences of schematic variables are usually not considered in the subsequent
                     normal process of the reasoning, and may cause unexpected exception in them.\<close>
  ToA_refl        = (4000, [3990, 4019]) in ToA and < ToA_assigning_var and > ToA_success
                    \<open>Reflexive tranformation rules\<close>
  ToA_splitting_source = (50, [50,50]) for \<open>_ * _ \<transforms> _ \<with> _\<close> < ToA_cut in ToA
                    \<open>split the separation sequent in the source part and reason the tranformation for
                     each separated item one by one.\<close>
  ToA_elim_intro  = (19, [19,19]) in ToA < default
                    \<open>Elimination and introduction rules that unfold \<phi>-types\<close>
  ToA_weak        = (20, [20,24]) in ToA < default and > ToA_elim_intro
                    \<open>Weak transformation rules giving some reasoning support temporarily and expecting to be orverride\<close>
  ToA_derived     = (50, [25,79]) in ToA < default and > ToA_weak
                    \<open>Automatically derived transformations. Many substructures are contained in this large range.\<close>
  ToA_derived_red = (150, [130,170]) for \<open>_ * _ \<transforms> _ \<with> _\<close> > ToA_derived > default in ToA
                    \<open>Automatically derived transformation reductions.\<close>
  ToA_weak_red    = (120, [120,129]) for \<open>_ * _ \<transforms> _ \<with> _\<close> < ToA_derived_red in ToA
                    \<open>Weak reduction rules giving some reasoning support temporarily and expecting to be orverride\<close>
  ToA_user        = (100, [80,119]) in ToA and < ToA_weak_red and > ToA_derived
                    \<open>default group for user rules\<close>

declare [[
  \<phi>default_reasoner_group \<open>_ \<transforms> _ \<with> _ @tag \<T>\<P>\<close> : %ToA_user (10)
                      and \<open>?var \<transforms> _ \<Ztypecolon> _ \<with> _ @tag \<T>\<P>\<close> : %ToA_elim_intro (100)
                      and \<open>_ \<Ztypecolon> _ \<transforms> ?var \<with> _ @tag \<T>\<P>\<close> : %ToA_elim_intro (100)
]]

\<phi>reasoner_group ToA_clean_all = (100, [10,3000]) for \<open>_ \<transforms> _ \<with> _ @clean\<close>
      \<open>All transformation cleaning wastes and debris\<close>
  and ToA_clean = (1020, [1000,1050]) in ToA_clean_all \<open>\<close>
  and ToA_clean_fallback = (20,[10,30]) in ToA_clean_all < ToA_clean \<open>\<close>

declare [[
  \<phi>default_reasoner_group \<open>_ \<transforms> _ \<with> _ @clean\<close> : %ToA_clean (20)
]]

paragraph \<open>Bottom Groups\<close>

\<phi>reasoner_group
  ToA_falling_latice = (1, [0,4]) for \<open>_ \<transforms> _ \<with> _\<close> in ToA_bottom
                    \<open>Fallbacks of transformation rules\<close>
  ToA_unified_refl = (5, [5,6]) for \<open>_ \<transforms> _ \<with> _\<close> in ToA_bottom and > ToA_falling_latice
                     \<open>Reflexive tranformation rules with unification, of a low priority because
                      unification is aggresive.\<close>
  ToA_derv_unify_refl = (7, [7,8]) for \<open>_ \<transforms> _ \<with> _\<close> in ToA_bottom and > ToA_unified_refl
                     \<open>derived ToA_unified_refl that override the default behaviors.\<close>
  ToA_varify_target_object = (9, [9,9]) for \<open>_ \<transforms> _ \<with> _\<close> in ToA_bottom and > ToA_derv_unify_refl
                    \<open>Varifies the fixed target object, using Object_Equiv\<close>
  ToA_inst_qunat  = (10, [10,10]) for \<open>_ \<transforms> _ \<with> _\<close> in ToA_bottom and > ToA_varify_target_object
                    \<open>Transformation rules instantiating quantified variables. It is unsafe unless
                     all fixable variables are fixed. If any variable is fixed later than the instantiation,
                     the instantiated schematic variable cannot caputure the later fixed variable.\<close>
  ToA_branches    = (12, [11,15]) for \<open>_ \<transforms> _ \<with> _\<close> in ToA_bottom and > ToA_inst_qunat
                    \<open>Branching transformation rules.\<close>


paragraph \<open>Fallback\<close>

text \<open>There are two trivial solutions for such problem.

  On commutative algebra, a transformation can do nothing but simply return the source to the remainder
  and demand subsequent transformation to the target. Such transformation is of the lowest priority
  serving as a fallback of the ordinary reasoning.

  \<open> x \<Ztypecolon> T \<^emph>[True] U \<transforms> (snd x, fst x) \<Ztypecolon> U \<^emph>[True] T \<close>

  Another trivial solution is on unital algebras, where a transformation can assign the target object
  to the identity element of the type so the source term directly go to the remainder.

  \<open> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<transforms> (one, fst x) \<Ztypecolon> U \<^emph>[True] T \<close> where \<open>one \<Ztypecolon> U \<equiv> emp\<close>

  This is the fallback rule for unital algebras that are non-commutative, and in this case when
  all transformations from T to U fail, assigning \<open>U\<close> to identity element is the only available search
  branch so the fallback is safe. For commutative algebra, the previous fallback is applied.
  When \<open>U\<close> is kept swapping and all source terms are passed, the still remaining \<open>U\<close> is assigned
  with the identity element, so the case of \<open>one \<Ztypecolon> U \<equiv> emp\<close> is still covered.



(*Implementation note:

  By default, such rule is not activated as it really does nothing, and clients have a way
  to know if the reasoning fails. However, if such fallback is expected, one can use reasoning goal
  \<open> Try Cs (x \<Ztypecolon> T \<^emph>[Cw] W \<transforms> y \<Ztypecolon> U \<^emph>[Cr] R) \<close>
  in which boolean condition \<open>Cs\<close> returns whether the reasoning really ever made some changes.*)
 \<close>


text \<open>Rules are given in \<section>\<open>Reasoning/Basic Transformation Rules/Fallback\<close>\<close>


subsubsection \<open>Extracting Pure Facts Implies Inside\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF A P
\<Longrightarrow> \<r>EIF (A @tag \<T>\<P>) P \<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF A P
\<Longrightarrow> \<r>EIF (A @tag \<T>\<P>') P \<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC P A
\<Longrightarrow> \<r>ESC P (A @tag \<T>\<P>) \<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC P A
\<Longrightarrow> \<r>ESC P (A @tag \<T>\<P>') \<close>
  unfolding Action_Tag_def .

text \<open>This is used in \<phi>-derivers, particularly in induction when\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> P\<^sub>A \<suffices> A
\<Longrightarrow> B \<implies> P\<^sub>B
\<Longrightarrow> \<r>EIF (A \<transforms> B \<with> P) (P\<^sub>A \<longrightarrow> P\<^sub>B \<and> P) \<close>
  unfolding Action_Tag_def \<r>EIF_def \<r>ESC_def Satisfiable_def Transformation_def
  by clarsimp

ML \<open>
fun extracting_elim_or_intro_ToA is_intro ctxt sequent =
  let val target = case HOLogic.dest_Trueprop (Thm.major_prem_of sequent)
                     of Const(\<^const_name>\<open>\<r>EIF\<close>, _) $ target $ _ => target
                      | _ => raise THM ("extracting_elim_or_intro_ToA", 1, [sequent])
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
      then SOME ((ctxt, @{lemma' \<open> \<r>EIF S C
                              \<Longrightarrow> \<r>EIF ((A \<transforms> A) \<longrightarrow> S) C \<close>
                             by simp}
                          RS sequent), Seq.empty)
      else NONE
  end
\<close>

\<phi>reasoner_ML Transformation\<^sub>I_\<A>EIF' %extract_pure+10 (\<open>\<r>EIF ((?var \<transforms> _ \<with> ?var_P) \<longrightarrow> _) _ \<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () => extracting_elim_or_intro_ToA true ctxt sequent)
\<close>

\<phi>reasoner_ML Transformation\<^sub>E_\<A>EIF' %extract_pure+10 (\<open>\<r>EIF ((_ \<transforms> ?var \<with> ?var_P) \<longrightarrow> _) _ \<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () => extracting_elim_or_intro_ToA false ctxt sequent)
\<close>


(*TODO*)
lemma ToA_EIF_sat:
  \<open> (\<And>v. \<simplify> vA v : v \<Turnstile> A)
\<Longrightarrow> (\<And>v. \<simplify> vB v : v \<Turnstile> B)
\<Longrightarrow> \<r>EIF (A \<transforms> B \<with> P) (\<forall>v. vA v \<longrightarrow> vB v \<and> P) \<close>
  unfolding \<r>EIF_def Satisfiable_def Transformation_def Simplify_def
  by clarsimp

lemma ToA_ESC_sat:
  \<open> (\<And>v. \<simplify> vA v : v \<Turnstile> A)
\<Longrightarrow> (\<And>v. \<simplify> vB v : v \<Turnstile> B)
\<Longrightarrow> \<r>ESC (\<forall>v. vA v \<longrightarrow> vB v \<and> P) (A \<transforms> B \<with> P) \<close>
  unfolding \<r>ESC_def Satisfiable_def Transformation_def Simplify_def
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
  \<open> Generate_Implication_Reasoning (Satisfiable X \<longrightarrow> Y) (Satisfiable X) Y \<close>
  unfolding Generate_Implication_Reasoning_def
  ..

lemma [\<phi>reason 1100]:
  \<open> Y \<implies> P
\<Longrightarrow> Generate_Implication_Reasoning (X \<transforms> Y) (Satisfiable X) P \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Satisfiable_def \<r>EIF_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> Y \<implies> Q
\<Longrightarrow> Generate_Implication_Reasoning (X \<transforms> Y \<with> P) (Satisfiable X) (Q \<and> P) \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Satisfiable_def \<r>EIF_def
  by blast


subsection \<open>Top\<close>

notation top ("\<top>")

subsubsection \<open>Rewrites\<close>

lemma Top_Satisfiable[simp]:
  \<open>Satisfiable \<top> \<longleftrightarrow> True\<close>
  unfolding Satisfiable_def
  by clarsimp

subsubsection \<open>Transformation Rules\<close>

\<phi>reasoner_group ToA_top = (%ToA_success, [%ToA_success-1, %ToA_success+1]) for \<open>_ \<transforms> \<top> \<with> _\<close>
                          \<open>Transformation rules handling \<top>\<close>

text \<open>The target part is assumed having no schematic variable, so it is safe to do such shortcuts
      comparing with the bottom-in-source.\<close>

(*TODO!*)

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason %ToA_top]:
  \<open>Any \<transforms> \<top>\<close>
  unfolding Transformation_def by blast

lemma [\<phi>reason %ToA_top]:
  \<open>Any \<transforms> \<top> \<remains> 1\<close>
  unfolding Transformation_def
  by simp

lemma [\<phi>reason %ToA_top]:
  \<open> A \<transforms> \<top> * B
\<Longrightarrow> A \<transforms> \<top> * B \<remains> 1\<close>
  unfolding Transformation_def
  by simp

(*The following procedure only supports commutative semigroup*)
 
lemma [\<phi>reason %ToA_top+1 if \<open>fn (ctxt,sequent) =>
          case Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
            of (_, (_ (*times*) $ _ $ R), _)
               => let fun chk (Const(\<^const_name>\<open>times\<close>, _) $ X $ Const(\<^const_name>\<open>top\<close>, _)) = chk X
                        | chk (Const(\<^const_name>\<open>top\<close>, _)) = false
                        | chk _ = true
                   in chk R
                  end\<close>]:
  \<open> Any \<transforms> R * \<top> \<with> P
\<Longrightarrow> Any \<transforms> \<top> * R \<with> P\<close>
  for Any :: \<open>'a::sep_ab_semigroup BI\<close>
  by (simp add: mult.commute)

(*when we reach here, it means R all consists of \<top>, so that we can eliminate them one-by-one,
  until the last one which can be done by \<open>Any \<transforms> \<top>\<close> directly.
  Again we assume and only consider commutative semigroup*)

lemma [\<phi>reason %ToA_top]:
  \<open> A \<transforms> R \<with> P
\<Longrightarrow> A * B \<transforms> \<top> * R \<with> P\<close>
  for A :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding Transformation_def
  by (clarsimp, insert sep_disj_commuteI sep_mult_commute, blast)

lemma [\<phi>reason %ToA_top-1]:
  \<open> A \<transforms> R \<with> P
\<Longrightarrow> A \<transforms> \<top> * R \<with> P\<close>
  for A :: \<open>'a::sep_algebra BI\<close>
  unfolding Transformation_def
  by clarsimp (metis mult_1_class.mult_1_left sep_magma_1_right)

lemma [\<phi>reason %fail]:
  \<open> FAIL TEXT(\<open>Sorry, currently we do not support solving \<open>\<top> * R\<close> problems on non-monoidal and non-commutative group.\<close>)
\<Longrightarrow> X \<transforms> \<top> * R \<with> P\<close>
  unfolding Transformation_def FAIL_def
  by blast



subsection \<open>Bottom\<close>

text \<open>Despite of semantically \<open>0 = \<bottom>\<close> where syntactically \<open>\<bottom> \<equiv> {}\<close>, but there is not syntactically
  \<open>0 \<equiv> {}\<close>. We prefer to use \<open>0\<close> instead of the more usual \<open>\<bottom>\<close> for the sake of forming
  a semiring together with \<open>1 \<equiv> emp\<close>, \<open>*\<close>, \<open>+ \<equiv> \<or>\<^sub>B\<^sub>I\<close>, to leverage the existing automation of semiring.\<close>

abbreviation Bottom ("\<bottom>\<^sub>B\<^sub>I") where \<open>Bottom \<equiv> (0::'a::sep_magma BI)\<close>
abbreviation Bottom_abs ("\<bottom>\<^sub>\<lambda>") where \<open>Bottom_abs \<equiv> (0 :: 'b \<Rightarrow> 'a::sep_magma BI)\<close>

lemma bot_eq_BI_bot [\<phi>programming_base_simps, \<phi>programming_simps]:
  \<open>bot = \<bottom>\<^sub>B\<^sub>I\<close>
  unfolding zero_BI_def bot_BI_def ..

lemma zero_implies_any[simp]:
  \<open>0 \<transforms> X \<with> Any\<close>
  unfolding Transformation_def zero_set_def Satisfaction_def
  by (cases X; simp add: zero_BI_def)

subsubsection \<open>Rewrites\<close>

lemma Bot_Satisfiable[simp]:
  \<open> Satisfiable 0 \<longleftrightarrow> False \<close>
  unfolding Satisfiable_def
  by clarsimp

subsubsection \<open>Transformation Rules\<close>

\<phi>reasoner_group ToA_bot = (%ToA_cut+5, [%ToA_cut, %ToA_cut+10]) for \<open>0 \<transforms> _ \<with> _\<close>
   \<open>Transformation rules when the source assertion is 0.
    The rule is not of a highest priority because the target may contain schematic variables,
    and the usual reasoning procedure is still required to unfold the target connective-by-connective
    to ensure every variables inside is instantiated.\<close>

lemma [\<phi>reason %ToA_cut for \<open>0 \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>?var \<transforms> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open>0 \<transforms> X \<with> False @tag \<T>\<P>\<close>
  unfolding Action_Tag_def
  by simp


lemma [\<phi>reason %ToA_bot for \<open>0 \<transforms> _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>?var \<transforms> _ \<remains> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open>0 \<transforms> X \<remains> 0 \<with> False @tag \<T>\<P>\<close>
  using zero_implies_any Transformation_def Action_Tag_def
  by simp


paragraph \<open>Reductions\<close>

lemma [\<phi>reason %ToA_red for \<open>0 * _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>?var * _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open> 0 \<transforms> X \<with> P
\<Longrightarrow> 0 * R \<transforms> X \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ * 0 \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>_ * ?var \<transforms> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open> 0 \<transforms> X \<with> P
\<Longrightarrow> R * 0 \<transforms> X \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ + 0 \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>_ + ?var \<transforms> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open> Y \<transforms> X \<with> P
\<Longrightarrow> Y + 0 \<transforms> X \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>0 + _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>?var + _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> Y \<transforms> X \<with> P
\<Longrightarrow> 0 + Y \<transforms> X \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<transforms> _ + 0 \<with> _ @tag \<T>\<P>\<close>
                            \<open>_ \<transforms> _ + ?var \<with> _ @tag \<T>\<P>\<close>]:
  \<open> Y \<transforms> X \<with> P
\<Longrightarrow> Y \<transforms> X + 0 \<with> P\<close>
  by simp
 
lemma [\<phi>reason %ToA_red for \<open>_ \<transforms> 0 + _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>_ \<transforms> ?var + _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open> Y \<transforms> X \<with> P
\<Longrightarrow> Y \<transforms> 0 + X \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<transforms> _ + 0 \<remains> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>_ \<transforms> _ + ?var \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> Y \<transforms> X \<remains> R \<with> P
\<Longrightarrow> Y \<transforms> X + 0 \<remains> R \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<transforms> 0 + _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>
                            \<open>_ \<transforms> ?var + _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> Y \<transforms> X \<remains> R \<with> P
\<Longrightarrow> Y \<transforms> 0 + X \<remains> R \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 0 \<transforms> Y \<with> P
\<Longrightarrow> 0 x \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> R * 0 \<transforms> Y \<with> P
\<Longrightarrow> R * 0 x \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 0 * R \<transforms> Y \<with> P
\<Longrightarrow> 0 x * R \<transforms> Y \<with> P \<close>
  by simp


subsection \<open>Unit\<close>

lemma \<phi>None_expn[\<phi>expns, simp]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<phi>None) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>None_def \<phi>Type_def
  by simp

lemma \<phi>None_inhabited[elim!]:
  \<open>Satisfiable (x \<Ztypecolon> \<phi>None) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma Prod_\<phi>None_red:
  \<open> x \<Ztypecolon> T \<^emph> \<circle> \<equiv> fst x \<Ztypecolon> T\<close>
  \<open> y \<Ztypecolon> \<circle> \<^emph> T \<equiv> snd y \<Ztypecolon> T\<close>
  \<open> x' \<Ztypecolon> \<circle> \<^emph> (\<circle> :: ('v::sep_magma_1, 'x) \<phi>) \<equiv> 1\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding atomize_eq BI_eq_iff
  by ((rule \<phi>Type_eqI)?; clarsimp)+

subsubsection \<open>Properties\<close>

lemma [\<phi>reason %extract_pure]:
  \<open>1 \<implies> True\<close>
  unfolding \<r>EIF_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> True \<suffices> 1 \<close>
  unfolding \<r>ESC_def Satisfiable_def
  by simp

lemma Emp_Satisfiable[simp]:
  \<open> Satisfiable 1 \<longleftrightarrow> True \<close>
  unfolding Satisfiable_def
  by clarsimp

subsubsection \<open>Transformation Rules\<close>

lemma [\<phi>reason %ToA_success]:
  \<open>X \<transforms> 1 \<remains> X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

lemma [\<phi>reason %ToA_red]:
  " H \<transforms> X \<with> P
\<Longrightarrow> H \<transforms> 1 * X \<with> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left .

lemma [\<phi>reason %ToA_red]:
  " H \<transforms> X \<remains> R \<with> P
\<Longrightarrow> H \<transforms> 1 * X \<remains> R \<with> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left .

lemma [\<phi>reason %ToA_red]:
  " R \<transforms> X \<with> P
\<Longrightarrow> 1 * R \<transforms> X \<with> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left .


subsection \<open>Additive Disjunction\<close>

text \<open>Is the \<^term>\<open>(+) :: 'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> directly\<close>

subsubsection \<open>Basic Rules\<close>

lemma Disjunction_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (A + B) \<longleftrightarrow> p \<Turnstile> A \<or> p \<Turnstile> B\<close>
  unfolding Satisfaction_def
  by (simp add: plus_BI_def)

lemma Add_Disj_Satisfiable[simp]:
  \<open> Satisfiable (A + B) \<longleftrightarrow> Satisfiable A \<or> Satisfiable B \<close>
  unfolding Satisfiable_def
  by clarsimp blast

lemma [\<phi>reason %cutting]:
  \<open> X \<implies> A
\<Longrightarrow> Y \<implies> B
\<Longrightarrow> X + Y \<implies> A \<or> B\<close>
  unfolding \<r>EIF_def Satisfiable_def
  by simp blast

lemma [\<phi>reason %cutting]:
  \<open> A \<suffices> X
\<Longrightarrow> B \<suffices> Y
\<Longrightarrow> A \<or> B \<suffices> X + Y\<close>
  unfolding \<r>ESC_def Satisfiable_def
  by simp blast

text \<open>The above two rules are reversible.\<close>

lemma set_plus_inhabited[elim!]:
  \<open>Satisfiable (S + T) \<Longrightarrow> (Satisfiable S \<Longrightarrow> C) \<Longrightarrow> (Satisfiable T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Satisfiable_def
  by (simp, blast)

lemma implies_union:
  \<open> A \<transforms> X \<with> P
\<Longrightarrow> A \<transforms> X + Y \<with> P\<close>
  \<open> A \<transforms> Y \<with> P
\<Longrightarrow> A \<transforms> X + Y \<with> P\<close>
  unfolding Transformation_def
  by simp_all

declare add_mono[\<phi>reason 1000]


subsubsection \<open>Transformation Rules\<close>

paragraph \<open>In Source\<close>

lemma [\<phi>reason %ToA_splitting]:
  \<open> B \<transforms> X \<with> P1
\<Longrightarrow> A \<transforms> X \<with> P2
\<Longrightarrow> A + B \<transforms> X \<with> P1 \<or> P2\<close>
  by (simp add: Transformation_def)

lemma [\<phi>reason %ToA_splitting]:
  \<open> B * R \<transforms> X \<with> P1
\<Longrightarrow> A * R \<transforms> X \<with> P2
\<Longrightarrow> (A + B) * R \<transforms> X \<with> P1 \<or> P2\<close>
  by (simp add: Transformation_def distrib_left) blast

lemma [\<phi>reason %ToA_splitting+10]:
  \<open> B \<transforms> X \<remains> RB \<with> P1
\<Longrightarrow> A \<transforms> X \<remains> RA \<with> P2
\<Longrightarrow> RA + RB \<transforms> RR @clean
\<Longrightarrow> A + B \<transforms> X \<remains> RR \<with> P1 \<or> P2\<close>
  by (simp add: Transformation_def Action_Tag_def; meson)

lemma [\<phi>reason %ToA_splitting+10]:
  \<open> B * R \<transforms> X \<remains> RB \<with> P1
\<Longrightarrow> A * R \<transforms> X \<remains> RA \<with> P2
\<Longrightarrow> RA + RB \<transforms> RR @clean
\<Longrightarrow> (A + B) * R \<transforms> X \<remains> RR \<with> P1 \<or> P2\<close>
  by (simp add: Transformation_def Action_Tag_def; blast)

lemma [\<phi>reason add]:
  \<open> A \<transforms> R @clean
\<Longrightarrow> 0 + A \<transforms> R @clean \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason add]:
  \<open> A \<transforms> R @clean
\<Longrightarrow> A + 0 \<transforms> R @clean \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason add]:
  \<open> A + A \<transforms> A @clean \<close>
  unfolding Action_Tag_def
  by simp


paragraph \<open>In Target\<close>

lemma ToA_disj_target_A:
  \<open> X \<transforms> A \<with> P
\<Longrightarrow> X \<transforms> A + B \<with> P\<close>
  unfolding plus_set_def
  by (metis implies_union(1) plus_set_def)

lemma ToA_disj_target_B:
  \<open>  X \<transforms> B \<with> P
\<Longrightarrow>  X \<transforms> A + B \<with> P\<close>
  by (simp add: Transformation_def)
 
declare [[\<phi>reason ! %ToA_branches ToA_disj_target_A ToA_disj_target_B for \<open>?X \<transforms> ?A + ?B \<with> ?P @tag \<T>\<P>\<close>]]

hide_fact ToA_disj_target_A ToA_disj_target_B

lemma ToA_disj_target_A':
  \<open>  X \<transforms> A \<remains> R \<with> P
\<Longrightarrow>  X \<transforms> A + B \<remains> R \<with> P\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def
  by (simp add: distrib_left; blast)

lemma ToA_disj_target_B':
  \<open> X \<transforms> B \<remains> R \<with> P
\<Longrightarrow> X \<transforms> A + B \<remains> R \<with> P\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def
  by (simp add: distrib_left; blast)

declare [[\<phi>reason ! %ToA_branches ToA_disj_target_A' ToA_disj_target_B'
            for \<open>?X \<transforms> ?A + ?B \<remains> _ \<with> _ @tag \<T>\<P>\<close>]]

hide_fact ToA_disj_target_A' ToA_disj_target_B'

lemma [\<phi>reason add]:
  \<open> A \<transforms> A + A @clean \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason add]:
  \<open> X \<transforms> A @clean
\<Longrightarrow> X \<transforms> A + 0 @clean \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason add]:
  \<open> X \<transforms> A @clean
\<Longrightarrow> X \<transforms> 0 + A @clean \<close>
  unfolding Action_Tag_def
  by simp


subsection \<open>Existential Quantification\<close>

lemma ExBI_inhabited_E[elim!]:
  \<open>Satisfiable (ExBI S) \<Longrightarrow> (\<And>x. Satisfiable (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Satisfiable_def
  by simp blast

lemma [\<phi>reason %cutting]:
  \<open> (\<And>x. S x \<implies> C x)
\<Longrightarrow> ExBI S \<implies> Ex C \<close>
  unfolding Satisfiable_def \<r>EIF_def
  by (simp; blast)

lemma [\<phi>reason %cutting]:
  \<open> (\<And>x. C x \<suffices> S x)
\<Longrightarrow> Ex C \<suffices> ExBI S \<close>
  unfolding Satisfiable_def \<r>ESC_def
  by (simp; blast)

lemma ExBI_Satisfiable[simp]:
  \<open> Satisfiable (\<exists>*x. S x) \<longleftrightarrow> (\<exists>x. Satisfiable (S x)) \<close>
  unfolding Satisfiable_def
  by clarsimp blast


subsubsection \<open>Syntax\<close>

syntax
  "_SetcomprNu" :: "'a \<Rightarrow> pttrns \<Rightarrow> bool \<Rightarrow> 'a BI"  ("_ \<subj>/ _./ _" [14,0,15] 14)

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
            = Const (\<^const_syntax>\<open>ExBI\<close>, dummyT) $ trans_one (Bs,trans B) A
        | trans B Bs
            = Const (\<^const_syntax>\<open>ExBI\<close>, dummyT) $ trans_one (Bs, (fn Bs =>
                (* \<open>\<top>\<close> is notated, so since Isabelle2025 its head arrives wrapped in a positional
                   constraint; \<open>is_head\<close> recognizes it through the wrapper and, because it only
                   answers for a bare constant underneath, still means "P IS \<open>\<top>\<close>" rather than
                   "P's head is \<open>\<top>\<close>" *)
                if Phi_Syntax_Constraint.is_head [\<^const_syntax>\<open>top\<close>] P
                then subst 0 Bs X
                else Const (\<^const_syntax>\<open>Subjection\<close>, dummyT) $ subst 0 Bs X $ subst 0 Bs P
              )) B
   in trans idts [] end)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>ExBI\<close>, fn ctxt => fn [X] =>
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
          | trans (Vs,Bs) (Abs(A,T, Const(\<^const_syntax>\<open>ExBI\<close>, _) $ X))
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

lemma " BI (Union { BI.dest (S x) |x. P x }) = (S x \<subj> x. P x) "
  by (simp add: set_eq_iff ExBI_def Subjection_def) (meson Satisfaction_def)

subsubsection \<open>Basic Rules\<close>

lemma BI_Ex_comm:
  \<open>(\<exists>* x y. A x y) = (\<exists>* y x. A x y)\<close>
  unfolding BI_eq_iff
  by (simp, blast)


subsubsection \<open>Simplifications\<close>

lemma ExBI_pair: "ExBI T = (\<exists>*a b. T (a,b))"
  unfolding BI_eq_iff by clarsimp

lemma ExBI_simps[simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  \<open>ExBI 0 = 0\<close>
  \<open>ExBI (\<lambda>_. T) = T\<close>
  \<open>((\<exists>*c. X c) \<subj> PP) = (\<exists>*c. X c \<subj> PP)\<close>
  \<open>(F' y \<subj> y. embedded_func f' P' x' y) = (F' (f' x') \<subj> P' x')\<close>
(*  \<open>(\<exists>* x. x = t \<and> P x) = P t\<close>
"\<And>P. (\<exists>x. x = t \<and> P x) = P t"
    "\<And>P. (\<exists>x. t = x \<and> P x) = P t"*)
  unfolding BI_eq_iff embedded_func_def
  by simp_all

lemma ExBI_defined[\<phi>programming_base_simps, simp, \<phi>safe_simp]:
  \<comment> \<open>only safe for source side but unsafe for target side, because it could instantiate variables
      of types parameters which could be instantiated arbitrarily?... I am not pretty sure... It is subtle here\<close>
  \<open>(\<exists>* x. F x \<subj> x = y) = (F y)\<close>
  \<open>(\<exists>* x. F x \<subj> y = x) = (F y)\<close>
  \<open>(\<exists>* x. F x \<subj> x = y \<and> P x) = (F y \<subj> P y)\<close>
  \<open>(\<exists>* x. F x \<subj> y = x \<and> P x) = (F y \<subj> P y)\<close>
  unfolding BI_eq_iff
  by simp_all

lemma Ex_transformation_expn:
  \<open>((\<exists>*x. A x) \<transforms> B \<with> P) \<longleftrightarrow> (\<forall>x. A x \<transforms> B \<with> P)\<close>
  unfolding Transformation_def ExBI_expn
  by blast

lemma ExBI_split_prod[\<phi>programming_base_simps, \<phi>safe_simp]:
  \<open> (\<exists>*x. (case x of (a,b) \<Rightarrow> f a b)) = (\<exists>*a b. f a b) \<close>
  unfolding BI_eq_iff
  by clarsimp

lemma ExBI_subj_split_prod[\<phi>programming_base_simps, \<phi>safe_simp]:
  \<open> (\<exists>* x. A x \<subj> (case x of (a,b) \<Rightarrow> P a b)) = (\<exists>* a b. A (a,b) \<subj> P a b) \<close>
  unfolding BI_eq_iff
  by clarsimp




paragraph \<open>With Multiplicative Conjunction\<close>

lemma ExBI_times_left [simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  "((\<exists>* c. T c) * R) = (\<exists>* c. T c * R )"
  by (simp add: BI_eq_iff, blast)

lemma ExBI_times_right[simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  "(L * (\<exists>*c. T c)) = (\<exists>* c. L * T c)"
  by (simp add: BI_eq_iff, blast)


paragraph \<open>With Additive Disjunction\<close>

lemma ExBI_addisj:
  \<open>A + (\<exists>*c. B c) \<equiv> \<exists>*c. A + B c\<close>
  \<open>(\<exists>*c. B c) + A \<equiv> \<exists>*c. B c + A\<close>
  unfolding atomize_eq BI_eq_iff
  by simp+


subsubsection \<open>Transformation Rules\<close>

lemma ExBI_transformation:
  \<open>(\<And>x. S x \<transforms> S' x \<with> P)
\<Longrightarrow> ExBI S \<transforms> ExBI S' \<with> P\<close>
  unfolding Transformation_def by (clarsimp, blast)

lemma ExBI_transformation_I:
  \<open> S \<transforms> S' x \<with> P
\<Longrightarrow> S \<transforms> (ExBI S') \<with> P\<close>
  unfolding Transformation_def by (clarsimp, blast)

lemma ExBI_transformation_I_R:
  \<open> S \<transforms> S' x \<remains> R \<with> P
\<Longrightarrow> S \<transforms> (ExBI S') \<remains> R \<with> P\<close>
  unfolding Transformation_def
  by (clarsimp, blast)


lemma ExBI_additive_disj:
  \<open>(\<exists>*x. A x + B x) = (\<exists>*x. A x) + (\<exists>*x. B x)\<close>
  unfolding BI_eq_iff by (simp_all add: plus_fun) blast+

ML_file \<open>library/tools/simproc_ExSet_expand_quantifier.ML\<close>


subsubsection \<open>ToA Reasoning\<close>

lemma skolemize_transformation[\<phi>reason %ToA_fixes_quant]:
  "(\<And>x.  T x \<transforms> U \<with> P x)
\<Longrightarrow> ExBI T \<transforms> U \<with> Ex P"
  unfolding Transformation_def by simp fastforce

lemma skolemize_transformation_R[\<phi>reason %ToA_fixes_quant+5]:
  "(\<And>x.  T x \<transforms> U \<remains> R x \<with> P x)
\<Longrightarrow> ExBI R \<transforms> RR @clean
\<Longrightarrow> ExBI T \<transforms> U \<remains> RR \<with> Ex P"
  unfolding Transformation_def REMAINS_def Action_Tag_def by (simp; blast)

lemma skolemize_transformation_tR[\<phi>reason %ToA_fixes_quant+5]:
  "(\<And>x.  T x \<transforms> \<phi>TagA mode (U \<remains> R x) \<with> P x)
\<Longrightarrow> ExBI R \<transforms> RR @clean
\<Longrightarrow> ExBI T \<transforms> \<phi>TagA mode (U \<remains> RR) \<with> Ex P"
  unfolding Transformation_def REMAINS_def \<phi>TagA_def Action_Tag_def
  by (simp; blast)

lemma [\<phi>reason %ToA_fixes_quant]:
  "(\<And>x. T x * W \<transforms> U \<with> P x)
\<Longrightarrow> ExBI T * W \<transforms> U \<with> Ex P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason %ToA_fixes_quant+5]:
  "(\<And>x. T x * W \<transforms> U \<remains> R x \<with> P x)
\<Longrightarrow> ExBI R \<transforms> RR @clean
\<Longrightarrow> ExBI T * W \<transforms> U \<remains> RR \<with> Ex P"
  unfolding Transformation_def Action_Tag_def by (simp; blast)

lemma [\<phi>reason %ToA_fixes_quant+5]:
  "(\<And>x. T x * W \<transforms> \<phi>TagA mode (U \<remains> R x) \<with> P x)
\<Longrightarrow> ExBI R \<transforms> RR @clean
\<Longrightarrow> ExBI T * W \<transforms> \<phi>TagA mode (U \<remains> RR) \<with> Ex P"
  unfolding Transformation_def \<phi>TagA_def Action_Tag_def
  by (simp; blast)

subsubsection \<open>Cleaning\<close>

lemma [\<phi>reason add]:
  \<open> A \<transforms> R @clean
\<Longrightarrow> (\<exists>*_. A) \<transforms> R @clean \<close>
  unfolding Action_Tag_def Transformation_def
  by simp

lemma [\<phi>reason add]:
  \<open> A \<transforms> R @clean
\<Longrightarrow> A \<transforms> (\<exists>*_. R) @clean \<close>
  unfolding Action_Tag_def Transformation_def
  by simp


text \<open>Continued in \ref{supp-ex-conj}\<close>


subsection \<open>Additive Conjunction\<close>


lemma Additive_Conj_expn[iff, \<phi>expns]:
  \<open>p \<Turnstile> (A \<sqinter> B) \<longleftrightarrow> p \<Turnstile> A \<and> p \<Turnstile> B\<close>
  by (cases A; cases B; simp)

lemma additive_conj_inhabited_E[elim!]:
  \<open>Satisfiable (A \<sqinter> B) \<Longrightarrow> (Satisfiable A \<Longrightarrow> Satisfiable B \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Satisfiable_def
  by simp blast

lemma [\<phi>reason %cutting]:
  \<open> A \<implies> P
\<Longrightarrow> B \<implies> Q
\<Longrightarrow> A \<sqinter> B \<implies> P \<and> Q\<close>
  unfolding Action_Tag_def \<r>EIF_def
  by blast

lemma
  \<open> P \<suffices> A
\<Longrightarrow> Q \<suffices> B
\<Longrightarrow> P \<and> Q \<suffices> A \<sqinter> B\<close>
  unfolding Action_Tag_def Satisfiable_def
  oops

text \<open>There is no sufficiency reasoning for additive conjunction, because the sufficient condition
  of \<open>A \<sqinter> B\<close> cannot be reasoned separately (by considering \<open>A\<close> and \<open>B\<close> separately).\<close>


subsubsection \<open>Simplification\<close>

paragraph \<open>With ExBI\<close>

lemma ExBI_adconj:
  \<open>A \<sqinter> (\<exists>*c. B c) \<equiv> \<exists>*c. A \<sqinter> B c\<close>
  \<open>(\<exists>*c. B c) \<sqinter> A \<equiv> \<exists>*c. B c \<sqinter> A\<close>
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
  \<open> X \<transforms> A \<with> P1
\<Longrightarrow> X \<transforms> B \<with> P2
\<Longrightarrow> X \<transforms> A \<sqinter> B \<with> P1 \<and> P2 \<close>
  unfolding Transformation_def
  by simp

lemma NToA_conj_src_A:
  \<open> A \<transforms> X \<with> P
\<Longrightarrow> A \<sqinter> B \<transforms> X \<with> P \<close>
  unfolding Transformation_def
  by simp blast

lemma NToA_conj_src_B:
  \<open> B \<transforms> X \<with> P
\<Longrightarrow> A \<sqinter> B \<transforms> X \<with> P \<close>
  unfolding Transformation_def
  by simp blast

text \<open>Continued in \ref{supp-ex-conj}\<close>


subsection \<open>Subjection: Conjunction to a Pure Fact\<close>

text \<open>This is the only widely used additive conjunction under the interpretation of the \<phi> data refinement\<close>

subsubsection \<open>Basic Rules\<close>

lemma Subjection_inhabited_E[elim!]:
  \<open>Satisfiable (S \<subj> P) \<Longrightarrow> (Satisfiable S \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Satisfiable_def
  by simp

lemma [\<phi>reason %cutting]:
  \<open> (\<condition> P \<Longrightarrow> S \<implies> C)
\<Longrightarrow> S \<subj> P \<implies> P \<and> C \<close>
  unfolding Satisfiable_def Action_Tag_def Premise_def \<r>EIF_def
  by simp

lemma [\<phi>reason %cutting]:
  \<open> (\<condition> P \<Longrightarrow> C \<suffices> S)
\<Longrightarrow> P \<and> C \<suffices> S \<subj> P \<close>
  unfolding Satisfiable_def Action_Tag_def Premise_def \<r>ESC_def
  by simp 

lemma Subjection_imp_I:
  \<open> P
\<Longrightarrow> S \<transforms> S' \<with> Q
\<Longrightarrow> S \<transforms> S' \<subj> P \<with> Q\<close>
  unfolding Transformation_def by simp


subsubsection \<open>Simplification\<close>

lemma Subjection_cong:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<subj> P) \<equiv> (S' \<subj> P')\<close>
  unfolding atomize_eq BI_eq_iff by (simp, blast)

lemma Subjection_eq:
  \<open>(A \<subj> P) = (A' \<subj> P) \<longleftrightarrow> (P \<longrightarrow> A = A')\<close>
  unfolding BI_eq_iff
  by clarsimp blast

lemma Subjection_imp_simp[simp]:
  \<open> (A \<transforms> B \<subj> P \<with> Q) \<longleftrightarrow> (A \<transforms> B \<with> P \<and> Q) \<close>
  unfolding Transformation_def by simp

lemma Subjection_True [simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  \<open>(T \<subj> True) = T\<close>
  unfolding BI_eq_iff by simp

lemma Subjection_Flase[simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  \<open>(T \<subj> False) = 0\<close>
  unfolding BI_eq_iff by simp

lemma Subjection_Subjection[simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  \<open>(S \<subj> P \<subj> Q) = (S \<subj> P \<and> Q)\<close>
  unfolding BI_eq_iff
  by simp



lemma Subjection_Zero[simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  \<open>(0 \<subj> P) = 0\<close>
  unfolding BI_eq_iff
  by simp

lemma Subjection_transformation:
  \<open> S \<transforms> S' \<with> P
\<Longrightarrow> S \<subj> Q \<transforms> S' \<subj> Q \<with> P\<close>
  unfolding Transformation_def by (simp; blast)

lemma Subjection_transformation_rewr:
  \<open> (A \<subj> Q \<transforms> B \<with> P) \<longleftrightarrow> (Q \<longrightarrow> (A \<transforms> B \<with> P))\<close>
  unfolding Transformation_def by (simp; blast)


subparagraph \<open>With Additive Conjunction\<close>

lemma Subjection_addconj[simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  \<open>(A \<subj> P) \<sqinter> B \<equiv> (A \<sqinter> B) \<subj> P\<close>
  \<open>B \<sqinter> (A \<subj> P) \<equiv> (B \<sqinter> A) \<subj> P\<close>
  unfolding atomize_eq BI_eq_iff
  by (clarsimp; blast)+

subparagraph \<open>With Additive Disjunction\<close>

lemma Subjection_plus_distrib:
  \<open>(A + B \<subj> P) = (A \<subj> P) + (B \<subj> P)\<close>
  unfolding BI_eq_iff
  by simp blast

subparagraph \<open>With Multiplicative Conjunction\<close>

lemma Subjection_times[simp, \<phi>programming_base_simps, \<phi>safe_simp]:
  \<open>(S \<subj> P) * T = (S * T \<subj> P)\<close>
  \<open>T * (S \<subj> P) = (T * S \<subj> P)\<close>
  unfolding BI_eq_iff
  by (simp, blast)+


subsubsection \<open>Transformation Rules\<close>

\<phi>reasoner_group ToA_subj = (%ToA_assertion_cut, [%ToA_assertion_cut, %ToA_assertion_cut+20]) for \<open>T \<transforms> U \<subj> Q \<with> P\<close>
  \<open>Transformation rules handling \<open>Subjection\<close>\<close>

lemma [\<phi>reason %ToA_subj]:
  " T \<transforms> U \<with> P
\<Longrightarrow> \<premise> (P \<longrightarrow> Q)
\<Longrightarrow> T \<transforms> U \<subj> Q \<with> P "
  unfolding Transformation_def Premise_def
  by simp

lemma [\<phi>reason %ToA_red]:
  " T \<transforms> U \<with> P \<Longrightarrow>
    T \<transforms> U \<subj> True \<with> P "
  unfolding Transformation_def by simp

lemma [\<phi>reason %ToA_subj]:
  " T \<transforms> U \<remains> R \<with> P
\<Longrightarrow> \<premise> (P \<longrightarrow> Q)
\<Longrightarrow> T \<transforms> U \<subj> Q \<remains> R \<with> P "
  unfolding Transformation_def Premise_def
  by simp

lemma [\<phi>reason %ToA_red]:
  " T \<transforms> U \<remains> R \<with> P \<Longrightarrow>
    T \<transforms> U \<subj> True \<remains> R \<with> P "
  unfolding Transformation_def by simp

lemma [\<phi>reason %ToA_subj+10]: (*THINK: add Q in P, is good or not?*)
  "\<condition> Q \<longrightarrow> (T \<transforms> U \<with> P @tag \<T>\<P>)
\<Longrightarrow> T \<subj> Q \<transforms> U \<with> Q \<and> P @tag \<T>\<P>"
  unfolding Transformation_def Premise_def Action_Tag_def
  by simp blast

lemma [\<phi>reason %ToA_subj+20]:
  "\<condition> Q \<longrightarrow> (T \<transforms> U \<remains> R \<with> P @tag \<T>\<P>)
\<Longrightarrow> T \<subj> Q \<transforms> U \<remains> R \<subj> Q \<with> P @tag \<T>\<P>"
  unfolding Transformation_def Premise_def Action_Tag_def
  by simp blast

lemma [\<phi>reason %ToA_subj+20]:
  "\<condition> Q \<longrightarrow> (T \<transforms> \<phi>TagA mode (U \<remains> R) \<with> P @tag \<T>\<P>)
\<Longrightarrow> T \<subj> Q \<transforms> \<phi>TagA mode (U \<remains> R \<subj> Q) \<with> P @tag \<T>\<P>"
  unfolding Transformation_def Premise_def \<phi>TagA_def Action_Tag_def
  by simp blast

lemma [\<phi>reason %ToA_subj+10]:
  \<open>\<condition> Q \<longrightarrow> (T * W \<transforms> U \<with> P @tag \<T>\<P>)
\<Longrightarrow> (T \<subj> Q) * W \<transforms> U \<with> P @tag \<T>\<P> \<close>
  unfolding Transformation_def Premise_def Action_Tag_def
  by simp blast

lemma [\<phi>reason %ToA_subj+20]:
  "\<condition> Q \<longrightarrow> (T * W \<transforms> U \<remains> R \<with> P @tag \<T>\<P>)
\<Longrightarrow> (T \<subj> Q) * W \<transforms> U \<remains> R \<subj> Q \<with> P @tag \<T>\<P>"
  unfolding Transformation_def Premise_def Action_Tag_def
  by simp blast

lemma [\<phi>reason %ToA_subj+20]:
  "\<condition> Q \<longrightarrow> (T * W \<transforms> \<phi>TagA mode (U \<remains> R) \<with> P @tag \<T>\<P>)
\<Longrightarrow> (T \<subj> Q) * W \<transforms> \<phi>TagA mode (U \<remains> R \<subj> Q) \<with> P @tag \<T>\<P>"
  unfolding Transformation_def Premise_def \<phi>TagA_def Action_Tag_def
  by simp blast



subsection \<open>Multiplicative Conjunction\<close>

text \<open>Is the \<^term>\<open>(*) :: ('a::sep_magma) BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> directly\<close>

lemma set_mult_inhabited[elim!]:
  \<open>Satisfiable (S * T) \<Longrightarrow> (Satisfiable S \<Longrightarrow> Satisfiable T \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Satisfiable_def
  by (simp, blast)

lemma [\<phi>reason %cutting]:
  \<open> X \<implies> A
\<Longrightarrow> Y \<implies> B
\<Longrightarrow> X * Y \<implies> A \<and> B\<close>
  unfolding \<r>EIF_def
  using set_mult_inhabited by blast

lemma [\<phi>reason %cutting]:
  \<open> X \<implies> A
\<Longrightarrow> Y \<implies> B
\<Longrightarrow> X \<remains> Y \<implies> A \<and> B\<close>
  unfolding \<r>EIF_def REMAINS_def
  using set_mult_inhabited by blast

lemma
  \<open> A \<suffices> X
\<Longrightarrow> B \<suffices> Y
\<Longrightarrow> A \<and> B \<suffices> X * Y\<close>
  unfolding Action_Tag_def Satisfiable_def
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
  "U' \<transforms> U \<with> P \<Longrightarrow> R * U' \<transforms> R * U \<with> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma transformation_right_frame:
  "U' \<transforms> U \<with> P \<Longrightarrow> U' * R \<transforms> U * R \<with> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma transformation_bi_frame:
  " R' \<transforms> R \<with> P
\<Longrightarrow> L' \<transforms> L \<with> Q
\<Longrightarrow> L' * R' \<transforms> L * R \<with> P \<and> Q "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast


subsection \<open>Finite Multiplicative Quantification (FMQ)\<close>

definition Mul_Quant :: \<open>('a \<Rightarrow> 'b::sep_algebra BI) \<Rightarrow> 'a set \<Rightarrow> 'b BI\<close> ("\<big_ast>")
  where \<open>Mul_Quant A S \<equiv> (prod A S \<subj> finite S)\<close>

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

lemma sep_quant_sing[simp, \<phi>safe_simp]:
  \<open>\<big_ast> A {i} = A i\<close>
  unfolding Mul_Quant_def
  by simp

lemma sep_quant_empty[simp, \<phi>safe_simp]:
  \<open>\<big_ast> A {} = 1\<close>
  unfolding Mul_Quant_def
  by simp

lemma sep_quant_insert:
  \<open>i \<notin> I \<Longrightarrow> \<big_ast> A (insert i I) = A i * \<big_ast> A I\<close>
  unfolding Mul_Quant_def
  by (clarsimp simp add: Subjection_eq)

lemma sep_quant_reindex:
  \<open> inj_on f I
\<Longrightarrow> \<big_ast>i\<in>f`I. A i \<equiv> \<big_ast>i\<in>I. A (f i)\<close>
  unfolding Mul_Quant_def BI_eq_iff atomize_eq
  by (clarsimp; rule; clarsimp simp add: finite_image_iff prod.reindex_cong)

lemma finite_prod_subjection:
  \<open>finite I \<Longrightarrow> (\<Prod>i\<in>I. A i \<subj> P i) = ((\<Prod>i\<in>I. A i) \<subj> (\<forall>i\<in>I. P i))\<close>
  unfolding BI_eq_iff
proof (clarify; rule; clarsimp)
  fix u
  assume \<open>finite I\<close>
  have \<open>u \<Turnstile> (\<Prod>i\<in>I. A i \<subj> P i) \<longrightarrow> u \<Turnstile> prod A I \<and> (\<forall>x\<in>I. P x)\<close>
    by (induct arbitrary: u rule: finite_induct[OF \<open>finite I\<close>]; simp; blast)
  moreover assume \<open>u \<Turnstile> (\<Prod>i\<in>I. A i \<subj> P i)\<close>
  ultimately show \<open>u \<Turnstile> prod A I \<and> (\<forall>x\<in>I. P x)\<close>
    by blast
qed 

lemma sep_quant_subjection[\<phi>programming_base_simps, \<phi>programming_simps, \<phi>safe_simp]:
  \<open>(\<big_ast>i\<in>I. A i \<subj> P i) = ((\<big_ast>i\<in>I. A i) \<subj> (\<forall>i\<in>I. P i))\<close>
  unfolding BI_eq_iff
  by (clarify; rule; clarsimp simp add: Mul_Quant_def finite_prod_subjection)

lemma sep_quant_ExBI[\<phi>programming_base_simps, \<phi>programming_simps, \<phi>safe_simp]:
  \<open>(\<big_ast>i\<in>I. \<exists>*j. A i j) = (\<exists>*j. \<big_ast>i\<in>I. A i (j i))\<close>
proof -
  have t1: \<open>\<And>u. finite I \<Longrightarrow> u \<Turnstile> (\<Prod>i\<in>I. ExBI (A i)) \<longleftrightarrow> (\<exists>x. u \<Turnstile> (\<Prod>i\<in>I. A i (x i)))\<close> (is \<open>\<And>u. _ \<Longrightarrow> ?goal u\<close>)
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
  \<open>(\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) = ((\<big_ast>(i,j) \<in> I \<times> J. A i j) \<subj> finite I)\<close>
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
  \<open>(\<big_ast>i\<in>I. A i) + (\<big_ast>i\<in>I. B i) \<transforms> (\<big_ast>i\<in>I. A i + B i)\<close>
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
  \<open> (\<And>i\<in>S. A i \<implies> P i)
\<Longrightarrow> (\<big_ast>i\<in>S. A i) \<implies> (\<forall>i\<in>S. P i) \<close>
  unfolding Mul_Quant_def Action_Tag_def Satisfiable_def meta_Ball_def Premise_def \<r>EIF_def
  by clarsimp (metis dvdE dvd_prodI sep_conj_expn)


subsubsection \<open>Transformation\<close>

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> A x \<transforms> Y \<with> P
\<Longrightarrow> (\<big_ast>i\<in>{x}. A i) \<transforms> Y \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 1 \<transforms> Y \<with> P
\<Longrightarrow> (\<big_ast>i\<in>{}. A i) \<transforms> Y \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> A x * R \<transforms> Y \<with> P
\<Longrightarrow> (\<big_ast>i\<in>{x}. A i) * R \<transforms> Y \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> R \<transforms> Y \<with> P
\<Longrightarrow> (\<big_ast>i\<in>{}. A i) * R \<transforms> Y \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> A x \<with> P
\<Longrightarrow> X \<transforms> (\<big_ast>i\<in>{x}. A i) \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> 1 \<with> P
\<Longrightarrow> X \<transforms> (\<big_ast>i\<in>{}. A i) \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> A x \<remains> R \<with> P
\<Longrightarrow> X \<transforms> (\<big_ast>i\<in>{x}. A i) \<remains> R \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> 1 \<remains> R \<with> P
\<Longrightarrow> X \<transforms> (\<big_ast>i\<in>{}. A i) \<remains> R \<with> P\<close>
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
  \<open> (\<big_ast>i\<in>I. A i * B i) \<transforms> Y \<with> P
\<Longrightarrow> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<transforms> Y \<with> P\<close>
  unfolding sep_quant_sep
  by simp

lemma [\<phi>reason %ToA_weak_red]:
  \<open> (\<big_ast>i\<in>I. A i * B i) * W \<transforms> Y \<with> P
\<Longrightarrow> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) * W \<transforms> Y \<with> P\<close>
  unfolding sep_quant_sep[symmetric]
  by (simp add: mult.assoc)

lemma [\<phi>reason %ToA_weak_red]:
  \<open> X \<transforms> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<with> P
\<Longrightarrow> X \<transforms> (\<big_ast>i\<in>I. A i * B i) \<with> P \<close>
  unfolding sep_quant_sep
  by simp

lemma [\<phi>reason %ToA_weak_red]:
  \<open> X \<transforms> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) * R \<with> P
\<Longrightarrow> X \<transforms> (\<big_ast>i\<in>I. A i * B i) * R \<with> P \<close>
  unfolding sep_quant_sep
  by simp

lemma [\<phi>reason %ToA_weak_red]:
  \<open> X \<transforms> (\<big_ast>i\<in>I. A i) * (\<big_ast>i\<in>I. B i) \<remains> R \<with> P
\<Longrightarrow> X \<transforms> (\<big_ast>i\<in>I. A i * B i) \<remains> R \<with> P \<close>
  unfolding sep_quant_sep
  by simp




paragraph \<open>Transformation Functor\<close>

lemma sep_quant_transformation[\<phi>reason %ToA_cut]:
  \<open> \<guard> \<condition> I = J
\<Longrightarrow> (\<And>i\<in>I. A i \<transforms> B i \<with> P i)
\<Longrightarrow> (\<big_ast>i\<in>I. A i) \<transforms> (\<big_ast>i\<in>J. B i) \<with> (\<forall>i\<in>I. P i) \<close>
  unfolding Transformation_def Mul_Quant_def meta_Ball_def Premise_def \<r>Guard_def
  proof clarsimp
    fix v
    assume \<open>finite J\<close>
    show \<open> (\<And>x. x \<in> J \<Longrightarrow> \<forall>v. v \<Turnstile> A x \<longrightarrow> v \<Turnstile> B x \<and> P x)
        \<Longrightarrow> v \<Turnstile> prod A J \<Longrightarrow> v \<Turnstile> prod B J \<and> (\<forall>x\<in>J. P x) \<close> 
      by (induct arbitrary: v rule: finite_induct[OF \<open>finite J\<close>]; clarsimp; blast)
  qed


lemma [\<phi>reason %ToA_cut]:
  \<open> \<guard> \<condition> I = J
\<Longrightarrow> (\<And>i\<in>J. A i \<transforms> B i \<remains> R i \<with> P i)
\<Longrightarrow> (\<big_ast>i\<in>J. R i) \<transforms> RR @clean
\<Longrightarrow> (\<big_ast>i\<in>I. A i) \<transforms> (\<big_ast>i\<in>J. B i) \<remains> RR \<with> (\<forall>i\<in>J. P i) \<close>
  unfolding REMAINS_def Premise_def \<r>Guard_def Action_Tag_def
  subgoal premises prems proof -
    have t1: \<open>(\<big_ast>i\<in>I. A i) \<transforms> (\<big_ast>i\<in>J. B i) * (\<big_ast>i\<in>J. R i) \<with> (\<forall>i\<in>J. P i)\<close>
      by (insert prems, simp add: sep_quant_sep sep_quant_transformation[unfolded Premise_def \<r>Guard_def])
    show ?thesis
      using mk_intro_transformation prems(3) t1 transformation_left_frame by blast
  qed .

thm transformation_trans[OF sep_quant_transformation, where Q=True, simplified]

paragraph \<open>Scalar Associative\<close>

lemma [\<phi>reason %ToA_normalizing]:
  \<open> (\<condition> finite I \<Longrightarrow> (\<big_ast>(i,j) \<in> I \<times> J. A i j) \<transforms> B \<with> P)
\<Longrightarrow> (\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) \<transforms> B \<with> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def Subjection_transformation_rewr
  by simp

lemma [\<phi>reason %ToA_normalizing]:
  \<open> (\<condition> finite I \<Longrightarrow> (\<big_ast>(i,j) \<in> I \<times> J. A i j) * R \<transforms> B \<with> P)
\<Longrightarrow> (\<big_ast>i\<in>I. \<big_ast>j\<in>J. A i j) * R \<transforms> B \<with> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def Subjection_transformation_rewr Subjection_times
  by simp

lemma [\<phi>reason %ToA_normalizing]:
  \<open> A \<transforms> (\<big_ast>(i,j) \<in> I \<times> J. B i j) \<with> P
\<Longrightarrow> \<premise> finite I
\<Longrightarrow> A \<transforms> (\<big_ast>i\<in>I. \<big_ast>j\<in>J. B i j) \<with> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def
  by simp

lemma [\<phi>reason %ToA_normalizing]:
  \<open> A \<transforms> (\<big_ast>(i,j) \<in> I \<times> J. B i j) \<remains> R \<with> P
\<Longrightarrow> \<premise> finite I
\<Longrightarrow> A \<transforms> (\<big_ast>i\<in>I. \<big_ast>j\<in>J. B i j) \<remains> R \<with> P \<close>
  unfolding sep_quant_scalar_assoc Premise_def
  by simp





subsection \<open>Universal Quantification\<close>

term inf

definition AllSet :: \<open>('a \<Rightarrow> 'b BI) \<Rightarrow> 'b BI\<close> (binder "\<forall>\<^sub>B\<^sub>I" 10)
  where \<open>AllSet X = BI {y. \<forall>x. y \<Turnstile> X x}\<close>

lemma AllSet_expn[simp, \<phi>expns]:
  \<open>p \<Turnstile> (\<forall>\<^sub>B\<^sub>Ix. B x) \<longleftrightarrow> (\<forall>x. p \<Turnstile> B x)\<close>
  unfolding AllSet_def Satisfaction_def by simp

lemma AllSet_sub:
  \<open>A \<le> (\<forall>\<^sub>B\<^sub>I x. B x) \<longleftrightarrow> (\<forall>x. A \<le> B x)\<close>
  unfolding AllSet_def
  by (cases A; rule; simp add: subset_iff BI_sub_iff)

lemma BI_All_comm:
  \<open>(\<forall>\<^sub>B\<^sub>I x y. A x y) = (\<forall>\<^sub>B\<^sub>I y x. A x y)\<close>
  unfolding BI_eq_iff
  by (simp, blast)

lemma [elim!]:
  \<open>Satisfiable (AllSet S) \<Longrightarrow> (Satisfiable (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Satisfiable_def
  by clarsimp blast

lemma [\<phi>inhabitance_rule 1000]:
  \<open> S x \<implies> C
\<Longrightarrow> AllSet S \<implies> C \<close>
  unfolding Action_Tag_def \<r>EIF_def
  by clarsimp blast


subsection \<open>Supplementary Connective\<close>

subsubsection \<open>World Shift\<close> \<comment> \<open>Functional refinement in assertion-level, functional counterpart of \<open>\<Zcomp>\<close>\<close>

definition World_Shift :: \<open>('c \<Rightarrow> 'd) \<Rightarrow> 'c BI \<Rightarrow> 'd BI\<close> ("\<Psi>[_]" [10] 1000)
  where \<open>(\<Psi>[\<psi>] S) = BI {\<psi> u |u. u \<Turnstile> S}\<close>
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
  \<open> \<Psi>[\<psi>] (A \<sqinter> B) \<transforms> (\<Psi>[\<psi>] A \<sqinter> \<Psi>[\<psi>] B) \<close>
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

lemma \<Psi>_ExBI:
  \<open>\<Psi>[d] (\<exists>*c. S c) = (\<exists>*c. \<Psi>[d] (S c))\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)

lemma \<Psi>_Subjection:
  \<open>\<Psi>[d] (S \<subj> P) = (\<Psi>[d] S \<subj> P)\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)


section \<open>Basic \<phi>-Types \& Embedding of Logic Connectives\<close>

subsection \<open>Identity \<phi>-Type\<close>

definition Itself :: " ('a,'a) \<phi> " where "Itself x = BI {x}"

lemma Itself_expn[\<phi>expns, iff]:
  "p \<Turnstile> (x \<Ztypecolon> Itself) \<longleftrightarrow> p = x"
  unfolding \<phi>Type_def Itself_def Satisfaction_def by auto

lemma Itself_expn'[\<phi>expns, iff]:
  "p \<Turnstile> (Itself x) \<longleftrightarrow> p = x"
  unfolding Itself_def Satisfaction_def by auto

lemma Itself_inhabited_E[elim!]:
  \<open> Satisfiable (x \<Ztypecolon> Itself) \<Longrightarrow> C \<Longrightarrow> C \<close> .

lemma Itself_inhabited[\<phi>reason %cutting, simp, intro!]:
  \<open> Satisfiable (x \<Ztypecolon> Itself) \<close>
  unfolding Satisfiable_def
  by blast

lemma [\<phi>reason %cutting]:
  \<open> Abstract_Domain Itself (\<lambda>_. True) \<close>
  unfolding Abstract_Domain_def \<r>EIF_def Satisfiable_def
  by clarsimp

lemma [\<phi>reason %abstract_domain]:
  \<open> Abstract_Domain\<^sub>L Itself (\<lambda>_. True) \<close>
  unfolding Abstract_Domain\<^sub>L_def \<r>ESC_def Satisfiable_def
  by simp

lemma Itself_E:
  \<open> \<premise> v \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> v \<Ztypecolon> Itself \<transforms> x \<Ztypecolon> T \<close>
  unfolding Transformation_def Premise_def by simp

text \<open>The introduction rule of Itself cannot be written in such \<exists>free-ToA form but in To-Transformation form.\<close>

lemma satisfication_encoding:
  \<open> (x \<Ztypecolon> Itself \<transforms> y \<Ztypecolon> T \<with> P) \<longleftrightarrow> x \<Turnstile> (y \<Ztypecolon> T) \<and> P \<close>
  unfolding Transformation_def by simp


subsubsection \<open>Construction from Raw Abstraction represented by Itself \<close>
  \<comment> \<open>is a sort of reasoning process useful later in making initial Hoare triples from semantic raw
      representation (which are represented by Itself, i.e., no abstraction).\<close>

\<phi>reasoner_group abstract_from_raw = (100, [16, 1399]) for \<open>v \<Ztypecolon> Itself \<transforms> x \<Ztypecolon> T\<close>
      > ToA_bottom and < ToA_splitting_target
      \<open>Rules constructing abstraction from raw representations\<close>
  and abstract_from_raw_cut = (1000, [1000, 1030]) for \<open>v \<Ztypecolon> Itself \<transforms> x \<Ztypecolon> T\<close> in abstract_from_raw
      \<open>Cutting rules constructing abstraction from raw representations\<close>
  and derived_abstract_from_raw = (70, [60,80]) for \<open>v \<Ztypecolon> Itself \<transforms> x \<Ztypecolon> T\<close>
                                                 in abstract_from_raw and < abstract_from_raw_cut
      \<open>Derived rules\<close>

declare [[\<phi>reason_default_pattern
      \<open> _ \<Ztypecolon> Itself \<transforms> _ \<Ztypecolon> ?T \<with> _ @tag \<T>\<P> \<close> \<Rightarrow> \<open> _ \<Ztypecolon> Itself \<transforms> _ \<Ztypecolon> ?T \<with> _ @tag \<T>\<P> \<close> (1120)
  and \<open> _ \<Ztypecolon> Itself \<transforms> ?A \<with> _ @tag \<T>\<P> \<close> \<Rightarrow> \<open> _ \<Ztypecolon> Itself \<transforms> ?A \<with> _ @tag \<T>\<P> \<close> (1110)
]]

declare Itself_E[\<phi>reason default %ToA_falling_latice]

lemma [\<phi>reason default %ToA_falling_latice+1 except \<open>?var \<Ztypecolon> Itself \<transforms> _ @tag \<T>\<P>\<close>]:
  \<open> (\<condition> c = c' \<Longrightarrow> c' \<Ztypecolon> Itself \<transforms> A)
\<Longrightarrow> \<premise> c = c'
\<Longrightarrow> c \<Ztypecolon> Itself \<transforms> A \<close>
  unfolding Premise_def
  by simp

declare [[\<phi>chk_source_val = false]]

lemma [\<phi>reason %abstract_from_raw_cut]:
  \<open> c\<^sub>a \<Ztypecolon> Itself \<transforms> A
\<Longrightarrow> c\<^sub>b \<Ztypecolon> Itself \<transforms> B
\<Longrightarrow> \<premise> c\<^sub>a ## c\<^sub>b
\<Longrightarrow> (c\<^sub>a * c\<^sub>b) \<Ztypecolon> Itself \<transforms> A * B\<close>
  unfolding Transformation_def Premise_def
  by (clarsimp; blast)

declare [[\<phi>chk_source_val = true]]



subsection \<open>Embedding of \<open>\<top>\<close>\<close>

definition \<phi>Any :: \<open>('c, 'x) \<phi>\<close> ("\<top>\<^sub>\<phi>") where \<open>\<top>\<^sub>\<phi> = (\<lambda>_. \<top>)\<close>

setup \<open>Sign.mandatory_path "\<phi>Any"\<close>

lemma unfold [\<phi>programming_base_simps, \<phi>programming_simps, \<phi>safe_simp]:
  \<open>(x \<Ztypecolon> \<top>\<^sub>\<phi>) = \<top>\<close>
  unfolding \<phi>Any_def \<phi>Type_def ..

lemma expansion[iff]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<top>\<^sub>\<phi>) \<longleftrightarrow> True\<close>
  unfolding \<phi>Any.unfold
  by simp

setup \<open>Sign.parent_path\<close>

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %extract_pure]:
  \<open>x \<Ztypecolon> \<top>\<^sub>\<phi> \<implies> True\<close>
  unfolding \<r>EIF_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open>True \<suffices> x \<Ztypecolon> \<top>\<^sub>\<phi>\<close>
  unfolding \<r>ESC_def Satisfiable_def
  by simp

subsubsection \<open>Transformation Rules\<close>

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> \<top> \<with> P
\<Longrightarrow> X \<transforms> x \<Ztypecolon> \<top>\<^sub>\<phi> \<with> P\<close>
  unfolding \<phi>Any.unfold
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> \<top> \<remains> R \<with> P
\<Longrightarrow> X \<transforms> x \<Ztypecolon> \<top>\<^sub>\<phi> \<remains> R \<with> P\<close>
  unfolding \<phi>Any.unfold
  by simp

paragraph \<open>Separation Extraction\<close>

text \<open>In ToA, the \<open>\<top>\<^sub>\<phi>\<close> behaviors like a wildcard that can absorb an undetermined number of \<phi>-type items,
  and which \<phi>-type items are absorbed cannot be determined just from the type information. Therefore,
  we require explicit annotations to be given to give the range of the absorption of \<open>\<top>\<^sub>\<phi>\<close>.

TODO: make such annotation syntax.
\<close>

lemma [\<phi>reason %ToA_top+1]:
  \<open> May_Assign (snd x) unspec
\<Longrightarrow> x \<Ztypecolon> T \<OTast> \<circle> \<transforms> ((), unspec) \<Ztypecolon> \<top>\<^sub>\<phi> \<OTast> \<circle> \<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding Transformation_def \<phi>Prod'_def
  by clarsimp


subsection \<open>Embedding of \<open>\<bottom>\<close>\<close>

definition \<phi>Bot :: \<open>('c,'a) \<phi>\<close> ("\<bottom>\<^sub>\<phi>") where \<open>\<bottom>\<^sub>\<phi> = (\<lambda>_. 0)\<close>

setup \<open>Sign.mandatory_path "\<phi>Bot"\<close>

lemma unfold[\<phi>programming_base_simps, \<phi>programming_simps, \<phi>safe_simp]:
  \<open>(x \<Ztypecolon> \<bottom>\<^sub>\<phi>) = 0\<close>
  unfolding \<phi>Bot_def \<phi>Type_def ..

lemma expansion[simp]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<bottom>\<^sub>\<phi>) \<longleftrightarrow> False\<close>
  unfolding \<phi>Bot.unfold
  by simp

setup \<open>Sign.parent_path\<close>

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %extract_pure]:
  \<open>x \<Ztypecolon> \<bottom>\<^sub>\<phi> \<implies> False \<close>
  unfolding \<r>EIF_def \<phi>Bot.unfold Satisfiable_def
  by simp

lemma [\<phi>reason %extract_pure]:
  \<open>False \<suffices> x \<Ztypecolon> \<bottom>\<^sub>\<phi>\<close>
  unfolding \<r>ESC_def \<phi>Bot.unfold Satisfiable_def
  by simp

subsubsection \<open>Transformation Rules\<close>

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> 0 \<transforms> Y \<with> P
\<Longrightarrow> x \<Ztypecolon> \<bottom>\<^sub>\<phi> \<transforms> Y \<with> P\<close>
  unfolding \<phi>Bot.unfold
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 0 * W \<transforms> Y \<with> P
\<Longrightarrow> (x \<Ztypecolon> \<bottom>\<^sub>\<phi>) * W \<transforms> Y \<with> P\<close>
  unfolding \<phi>Bot.unfold
  by simp

paragraph \<open>Separation Extraction\<close>

(*TODO: more think!*)

lemma [\<phi>reason %ToA_top]:
  \<open> May_Assign (snd x) unspec
\<Longrightarrow> x \<Ztypecolon> \<bottom>\<^sub>\<phi> \<OTast> \<circle> \<transforms> (any, unspec) \<Ztypecolon> U \<OTast> \<circle> \<close>
  unfolding Transformation_def \<phi>Prod'_def
  by clarsimp


subsection \<open>Embedding of Separation Conjunction\<close>

lemma \<phi>Prod_expn' [\<phi>programming_base_simps, \<phi>programming_simps, \<phi>safe_simp]:
  \<open>((a,b) \<Ztypecolon> A \<^emph> B) = (a \<Ztypecolon> A) * (b \<Ztypecolon> B)\<close>
  unfolding BI_eq_iff by (simp add: set_mult_expn) blast

lemma \<phi>Prod_expn'':
  \<open> NO_MATCH (xx,yy) x
\<Longrightarrow> (x \<Ztypecolon> A \<^emph> B) = (fst x \<Ztypecolon> A) * (snd x \<Ztypecolon> B)\<close>
  unfolding BI_eq_iff by (cases x; simp add: set_mult_expn) blast

bundle \<phi>Prod_expn = \<phi>Prod_expn'[simp] \<phi>Prod_expn''[simp]

subsubsection \<open>Basic Rules\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> fst x \<Ztypecolon> T1 \<implies> C1
\<Longrightarrow> snd x \<Ztypecolon> T2 \<implies> C2
\<Longrightarrow> x \<Ztypecolon> T1 \<^emph> T2 \<implies> C1 \<and> C2\<close>
  unfolding Satisfiable_def Action_Tag_def \<r>EIF_def
  by (cases x; simp, blast)

paragraph \<open>Frame Rules\<close>

lemma transformation_right_frame_ty:
  \<open>(\<And>a. \<condition> a = fst x \<Longrightarrow> a \<Ztypecolon> T \<transforms> f(a) \<Ztypecolon> U \<with> P(a))
\<Longrightarrow> x \<Ztypecolon> T \<^emph> R \<transforms> apfst f x \<Ztypecolon> U \<^emph> R \<with> P(fst x) \<close>
  unfolding Transformation_def
  by (cases x; clarsimp; blast)

lemma transformation_left_frame_ty:
  \<open>(\<And>a. \<condition> a = snd x \<Longrightarrow> a \<Ztypecolon> T \<transforms> f(a) \<Ztypecolon> U \<with> P(a))
\<Longrightarrow> x \<Ztypecolon> R \<^emph> T \<transforms> apsnd f x \<Ztypecolon> R \<^emph> U \<with> P(snd x) \<close>
  unfolding Transformation_def
  by (cases x; clarsimp; blast)

subsubsection \<open>Abstract Domain\<close>

text \<open>The upper bound of the abstraction domain is simple.\<close>
(*
lemma \<comment> \<open>will be derived later\<close>:
  \<open> Abstract_Domain T D\<^sub>T
\<Longrightarrow> Abstract_Domain U D\<^sub>U
\<Longrightarrow> Abstract_Domain (T \<^emph> U) (\<lambda>(x,y). D\<^sub>T x \<and> D\<^sub>U y) \<close>
  unfolding Abstract_Domain_def Action_Tag_def Satisfiable_def
  by (clarsimp, blast)
*)

text \<open>However, the lower bound is non-trivial, in which case we have to show the separation combination
  is compatible between the two \<phi>-types. The compatibility is encoded by predicate \<open>Separation_Disj\<^sub>\<psi>\<close>
  and \<open>Separation_Disj\<^sub>\<phi>\<close> which are solved by means of the domainoid introduced later.
  So the rules are given until \cref{phi-types/Domainoid/App}.
\<close>


subsubsection \<open>Transformation Rules\<close>

lemma destruct_\<phi>Prod_\<phi>app: (*TODO: merge this into general destruction*)
  \<open>x \<Ztypecolon> T \<^emph> U \<transforms> (fst x \<Ztypecolon> T) * (snd x \<Ztypecolon> U)\<close>
  by (cases x; simp add: Transformation_def set_mult_expn) blast

lemma \<phi>Prod_transformation:
  " x \<Ztypecolon> N \<transforms> x' \<Ztypecolon> N' \<with> Pa
\<Longrightarrow> y \<Ztypecolon> M \<transforms> y' \<Ztypecolon> M' \<with> Pb
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<transforms> (x',y') \<Ztypecolon> N' \<^emph> M' \<with> Pa \<and> Pb"
  unfolding Transformation_def by simp blast
  (*The rule is not added into the \<phi>-LPR because such product is solved by Structural Extract*)

paragraph \<open>Reduction\<close>

lemma [\<phi>reason %ToA_red]:
  " A \<transforms> (fst x \<Ztypecolon> N) * (snd x \<Ztypecolon> M) \<with> P
\<Longrightarrow> A \<transforms> x \<Ztypecolon> N \<^emph> M \<with> P"
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason %ToA_red+1 for \<open>_ \<transforms> (_,_) \<Ztypecolon> _ \<^emph> _ \<with> _ @tag \<T>\<P>\<close>
                              \<open>_ \<transforms> ?var_y \<Ztypecolon> _ \<^emph> _ \<with> _ @tag \<T>\<P>\<close>]:
  " A \<transforms> (x \<Ztypecolon> N) * (y \<Ztypecolon> M) \<with> P
\<Longrightarrow> A \<transforms> (x,y) \<Ztypecolon> N \<^emph> M \<with> P"
  by (simp add: \<phi>Prod_expn')

text \<open>The reductions on source are not enabled as they may break the form of original source assertion\<close>

paragraph \<open>Separation Extraction\<close>

text \<open>see \<section>\<open>Technical \<phi>-Types required in Reasoning Transformation/Separation Extraction of \<open>\<phi>\<close>Prod\<close>\<close>

lemma Structural_Extract_\<phi>Prod_a [\<phi>reason %ToA_cut except \<open>(_ :: ?'a::sep_semigroup BI) \<transforms> _ \<with> _ @tag \<T>\<P>'\<close>]:
      \<comment> \<open>merely the rule for non-semigroup algebras.
          for others, see \<section>\<open>Technical \<phi>-Types required in Reasoning Transformation/Separation Extraction of \<open>\<phi>\<close>Prod\<close>\<close>
  \<open> fst a \<Ztypecolon> A \<transforms> b \<Ztypecolon> Y \<with> P @tag \<T>\<P>
\<Longrightarrow> a \<Ztypecolon> A \<OTast> X \<transforms> ((b, snd a), unspec) \<Ztypecolon> (Y \<^emph> X) \<OTast> \<circle> \<with> P @tag \<T>\<P>' \<close>
  for A :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding Action_Tag_def Transformation_def \<phi>Prod'_def
  by clarsimp blast


subsection \<open>Embedding of Empty\<close>

subsubsection \<open>Rewrites\<close>

lemma \<phi>None_itself_is_one[simp, \<phi>safe_simp]:
  \<open>(any \<Ztypecolon> \<phi>None) = 1\<close>
  unfolding BI_eq_iff by simp

lemma \<phi>Prod_\<phi>None:
  \<open>((x',y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'a::sep_magma_1 BI)\<close>
  \<open>((x,y') \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'b::sep_magma_1 BI)\<close>
  unfolding BI_eq_iff
  by (simp_all add: set_mult_expn)


subsubsection \<open>Transformation Rules\<close>

lemma [\<phi>reason %ToA_red]:
  " H \<transforms> X \<with> P
\<Longrightarrow> H \<transforms> (any \<Ztypecolon> \<circle>) * X \<with> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left \<phi>None_itself_is_one .

lemma [\<phi>reason %ToA_red]:
  " H \<transforms> X \<remains> R \<with> P
\<Longrightarrow> H \<transforms> (any \<Ztypecolon> \<circle>) * X \<remains> R \<with> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left \<phi>None_itself_is_one .

lemma [\<phi>reason %ToA_red]:
  " R \<transforms> X \<with> P
\<Longrightarrow> (any \<Ztypecolon> \<circle>) * R \<transforms> X \<with> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left \<phi>None_itself_is_one .

lemma [\<phi>reason %ToA_success]:
  \<open>X \<transforms> any \<Ztypecolon> \<circle> \<remains> X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<transforms> _ \<Ztypecolon> \<circle> \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> X \<transforms> 1 \<remains> R \<with> P @tag \<T>\<P>
\<Longrightarrow> X \<transforms> y \<Ztypecolon> \<circle> \<remains> R \<with> P @tag \<T>\<P> \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> 1 \<transforms> Y \<with> P
\<Longrightarrow> x \<Ztypecolon> \<circle> \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> W \<transforms> Y \<with> P
\<Longrightarrow> (x \<Ztypecolon> \<circle>) * W \<transforms> Y \<with> P \<close>
  for W :: \<open>'c::sep_magma_1 BI\<close>
  by simp

lemma [\<phi>reason %ToA_success]:
  \<open> x \<Ztypecolon> \<circle> \<OTast> U \<transforms> (snd x, unspec) \<Ztypecolon> U \<OTast> \<circle> \<close>
  unfolding \<phi>Prod'_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason %ToA_success]:
  \<open> x \<Ztypecolon> T \<OTast> \<circle> \<transforms> (unspec, fst x) \<Ztypecolon> \<circle> \<OTast> T \<close>
  unfolding \<phi>Prod'_def
  by (cases x; simp add: \<phi>Prod_expn')


subsection \<open>Injection into Unital Algebra\<close>

definition \<phi>Some :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<black_circle> _" [91] 90)
  where \<open>\<black_circle> T = (\<lambda>x. Some `\<^sub>I (x \<Ztypecolon> T))\<close>

lemma \<phi>Some_expn[simp, \<phi>expns]:
  \<open>p \<Turnstile> (x \<Ztypecolon> \<black_circle> T) \<longleftrightarrow> (\<exists>v. p = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>Some_def
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
  \<open> x \<Ztypecolon> \<black_circle> T \<transforms> y \<Ztypecolon> \<black_circle> U \<with> P \<equiv> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<with> P \<close>
  unfolding atomize_eq Transformation_def
  by clarsimp blast

lemma [\<phi>reason %ToA_cut]:
  \<open> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<with> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<transforms> y \<Ztypecolon> \<black_circle> U \<with> P \<close>
  unfolding \<phi>Some_transformation_strip .

lemma [\<phi>reason %ToA_cut]:
  \<open> x \<Ztypecolon> T \<OTast> W \<transforms> y \<Ztypecolon> U \<OTast> R \<with> P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<OTast> \<black_circle> W \<transforms> y \<Ztypecolon> \<black_circle> U \<OTast> \<black_circle> R \<with> P\<close>
  by (simp add: \<phi>Some_\<phi>Prod \<phi>Some_transformation_strip \<phi>Prod'_def)

subsubsection \<open>Properties\<close> \<comment> \<open>Some properties have to be given early before derivers ready\<close>

lemma Abstract_Domain_\<phi>Some[\<phi>reason %abstract_domain]:
  \<open> Abstract_Domain T D
\<Longrightarrow> Abstract_Domain (\<black_circle> T) D \<close>
  unfolding Abstract_Domain_def \<r>EIF_def Satisfiable_def
  by clarsimp



subsubsection \<open>Conditional Empty\<close>

definition \<phi>Cond_Unital :: \<open>bool \<Rightarrow> ('v, 'x) \<phi> \<Rightarrow> ('v::sep_magma_1, 'x) \<phi>\<close> ("\<half_blkcirc>[_] _" [20,91] 90)
  \<comment> \<open>Conditional Unital Insertion\<close>
  where \<open>\<half_blkcirc>[C] T = (if C then T else \<circle>)\<close>

definition \<phi>Cond_UniIns :: \<open>bool \<Rightarrow> ('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<half_bc2>[_] _" [20,91] 90)
  \<comment> \<open>Conditional Unital Insertion\<close>
  where \<open>\<half_bc2>[C] T = (if C then \<black_circle> T else \<circle>)\<close>


paragraph \<open>Rewrites\<close>

lemma \<phi>Cond_Unital_unfold_simp[simp, \<phi>safe_simp]:
  \<open> \<half_blkcirc>[True] T \<equiv> T \<close>
  \<open> \<half_blkcirc>[False] T \<equiv> \<circle> \<close>
  unfolding \<phi>Cond_Unital_def
  by simp+

lemma \<phi>Cond_UniIns_unfold_simp[simp, \<phi>safe_simp]:
  \<open> \<half_bc2>[True]  T \<equiv> \<black_circle> T \<close>
  \<open> \<half_bc2>[False] T \<equiv> \<circle> \<close>
  unfolding \<phi>Cond_UniIns_def
  by simp+

lemma \<phi>Cond_Unital_expn[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> \<half_blkcirc>[C] T) \<longleftrightarrow> (if C then p \<Turnstile> (x \<Ztypecolon> T) else p = None) \<close>
  by clarsimp

lemma \<phi>Cond_UniIns_expn[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> \<half_bc2>[C] T) \<longleftrightarrow> (if C then p \<Turnstile> (x \<Ztypecolon> \<black_circle> T) else p = None) \<close>
  by clarsimp

lemma \<phi>Cond_Unital_Prod:
  \<open>\<half_blkcirc>[C] T \<^emph> \<half_blkcirc>[C] U \<equiv> \<half_blkcirc>[C] (T \<^emph> U)\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI; cases C; clarsimp)

lemma \<phi>Cond_UniIns_Prod:
  \<open>\<half_bc2>[C] T \<^emph> \<half_bc2>[C] U \<equiv> \<half_bc2>[C] (T \<^emph> U)\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI; cases C; clarsimp; force)

lemma \<phi>Cond_Unital_trans_rewr:
  \<open> x \<Ztypecolon> \<half_blkcirc>[C] T \<transforms> y \<Ztypecolon> \<half_blkcirc>[C] U \<with> C \<longrightarrow> P \<equiv> C \<longrightarrow> (x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<with> P) \<close>
  unfolding atomize_eq Transformation_def
  by (cases C; clarsimp; blast)


section \<open>Basic \<phi>-Type Properties\<close>

text \<open>The two properties are essential for reasoning the general transformation including separation extraction.\<close>


subsection \<open>Identity Element I\&E\<close>

definition Identity_Element\<^sub>I :: \<open>'a::one BI \<Rightarrow> bool \<Rightarrow> bool\<close> where \<open>Identity_Element\<^sub>I S P \<longleftrightarrow> (S \<transforms> 1 \<with> P)\<close>
definition Identity_Element\<^sub>E :: \<open>'a::one BI \<Rightarrow> bool\<close> where \<open>Identity_Element\<^sub>E S \<longleftrightarrow> (1 \<transforms> S)\<close>

definition Identity_Elements\<^sub>I :: \<open>('c::one,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Identity_Elements\<^sub>I T D P \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x))\<close>

definition Identity_Elements\<^sub>E :: \<open>('c::one,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Identity_Elements\<^sub>E T D \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T))\<close>

definition Identity_Elements :: \<open>('c::one,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Identity_Elements T D \<longleftrightarrow> Identity_Elements\<^sub>I T D (\<lambda>_. True) \<and> Identity_Elements\<^sub>E T D\<close>

lemma Identity_Elements_alt_def:
  \<open>Identity_Elements T D \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> T) = 1)\<close>
  unfolding Identity_Elements_def Identity_Elements\<^sub>I_def Identity_Element\<^sub>I_def
            Identity_Elements\<^sub>E_def Identity_Element\<^sub>E_def BI_eq_ToA
  by (rule; clarsimp)
  

definition Hint_Identity_Element :: \<open>('c::one,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>Hint_Identity_Element T one \<equiv> True\<close>
  \<comment> \<open>a pure syntactical hint\<close>

declare [[ \<phi>reason_default_pattern
      \<open>Identity_Element\<^sub>I ?S _\<close> \<Rightarrow> \<open>Identity_Element\<^sub>I ?S _\<close> (100)
  and \<open>Identity_Element\<^sub>I (_ \<Ztypecolon> ?T) _\<close> \<Rightarrow> \<open>Identity_Element\<^sub>I (_ \<Ztypecolon> ?T) _\<close> (110)
  and \<open>Identity_Element\<^sub>E ?S\<close> \<Rightarrow> \<open>Identity_Element\<^sub>E ?S\<close> (100)
  and \<open>Identity_Element\<^sub>E (_ \<Ztypecolon> ?T)\<close> \<Rightarrow> \<open>Identity_Element\<^sub>E (_ \<Ztypecolon> ?T)\<close> (110)

  and \<open>Identity_Elements\<^sub>I ?T _ _\<close> \<Rightarrow> \<open>Identity_Elements\<^sub>I ?T _ _\<close> (100)
  and \<open>Identity_Elements\<^sub>E ?T _\<close> \<Rightarrow> \<open>Identity_Elements\<^sub>E ?T _\<close> (100)

  and \<open>Hint_Identity_Element ?T _\<close> \<Rightarrow> \<open>Hint_Identity_Element ?T _\<close> (100)
  and \<open>Identity_Elements ?T _\<close> \<Rightarrow> \<open>Identity_Elements ?T _\<close> (100)
]]

\<phi>reasoner_group identity_element = (100,[1,3000]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
    \<open>Reasoning rules deducing if the given assertion can transform to or be transformed from the
     assertion of identity element.\<close>
 and identity_element_fallback = (1,[1,1]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > fail
    \<open>Fallbacks of reasoning Identity_Element.\<close>
 and identity_element_\<phi> = (10, [10, 11]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
    \<open>Turning to \<open>Identity_Elements\<^sub>I\<close> and \<open>Identity_Elements\<^sub>E\<close>\<close>
 and derived_identity_element = (50, [50,55]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > identity_element_\<phi>
    \<open>Automatically derived Identity_Element rules\<close>
 and identity_element_top = (2900, [2900,2999]) in identity_element \<open>top\<close>
 and identity_element_cut = (1000, [1000,1029]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > derived_identity_element < identity_element_top
    \<open>Cutting rules for Identity_Element\<close>
 and identity_element_OPEN_MAKE = (1100, [1100,1100]) in identity_element
     and > identity_element_cut < identity_element_top \<open>\<close>
 and identity_element_red = (2500, [2500, 2530]) for (\<open>Identity_Element\<^sub>I _ _\<close>, \<open>Identity_Element\<^sub>E _\<close>)
     in identity_element > identity_element_cut
    \<open>Literal Reduction\<close>
 and identity_element_ToA = (50, [50,51]) for \<open>_ \<transforms> _ \<with> _\<close> in ToA
    \<open>Entry points from ToA to Identity_Element\<close>

 and identity_element_hint = (1000, [10, 2000]) for \<open>Hint_Identity_Element T ie\<close>
    \<open>syntactical hints suggesting an identity element of the given \<phi>-type\<close>

subsubsection \<open>Extracting Pure Facts\<close>

paragraph \<open>Identity_Element\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC Q (Satisfiable S)
\<Longrightarrow> \<r>EIF (Identity_Element\<^sub>I S P) (Q \<longrightarrow> P) \<close>
  unfolding Identity_Element\<^sub>I_def \<r>ESC_def \<r>EIF_def Transformation_def Satisfiable_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF (Satisfiable S) P
\<Longrightarrow> \<r>EIF (Identity_Element\<^sub>E S) P \<close>
  unfolding Identity_Element\<^sub>E_def \<r>ESC_def \<r>EIF_def Transformation_def Satisfiable_def
  by blast

lemma Identity_Element\<^sub>I_\<A>EIF_sat:
  \<open> \<r>EIF (Identity_Element\<^sub>I S P) (\<forall>v. v \<Turnstile> S \<longrightarrow> v = 1 \<and> P) \<close>
  unfolding Identity_Element\<^sub>I_def \<r>EIF_def Transformation_def
  by blast

lemma Identity_Element\<^sub>I_\<A>ESC_sat:
  \<open> \<r>ESC (\<forall>v. v \<Turnstile> S \<longrightarrow> v = 1 \<and> P) (Identity_Element\<^sub>I S P) \<close>
  unfolding Identity_Element\<^sub>I_def \<r>ESC_def Transformation_def
  by blast

lemma Identity_Element\<^sub>E_\<A>EIF_sat:
  \<open> \<r>EIF (Identity_Element\<^sub>E S) (1 \<Turnstile> S) \<close>
  unfolding Identity_Element\<^sub>E_def \<r>EIF_def Transformation_def
  by blast

lemma Identity_Element\<^sub>E_\<A>ESC_sat:
  \<open> \<r>ESC (1 \<Turnstile> S) (Identity_Element\<^sub>E S) \<close>
  unfolding Identity_Element\<^sub>E_def \<r>ESC_def Transformation_def
  by blast

bundle Identity_Element\<^sub>I_sat = Identity_Element\<^sub>I_\<A>EIF_sat [\<phi>reason %extract_pure_sat]
                               Identity_Element\<^sub>I_\<A>ESC_sat [\<phi>reason %extract_pure_sat]
bundle Identity_Element\<^sub>E_sat = Identity_Element\<^sub>E_\<A>EIF_sat [\<phi>reason %extract_pure_sat]
                               Identity_Element\<^sub>E_\<A>ESC_sat [\<phi>reason %extract_pure_sat]

bundle Identity_Element_sat begin
  unbundle Identity_Element\<^sub>I_sat and Identity_Element\<^sub>E_sat
end


paragraph \<open>Identity_Elements\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x. \<r>EIF (Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x)) (Q x))
\<Longrightarrow> \<r>EIF (Identity_Elements\<^sub>I T D P) (\<forall>x. D x \<longrightarrow> Q x)\<close>
  unfolding \<r>EIF_def Identity_Elements\<^sub>I_def
  by clarsimp

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x. \<r>EIF (Identity_Element\<^sub>E (x \<Ztypecolon> T)) (Q x))
\<Longrightarrow> \<r>EIF (Identity_Elements\<^sub>E T D) (\<forall>x. D x \<longrightarrow> Q x) \<close>
  unfolding \<r>EIF_def Identity_Elements\<^sub>E_def
  by clarsimp

subsubsection \<open>System Rules\<close>

lemma Identity_Elements\<^sub>I_sub:
  \<open> D' \<le> D
\<Longrightarrow> P \<le> P'
\<Longrightarrow> Identity_Elements\<^sub>I T D P 
\<Longrightarrow> Identity_Elements\<^sub>I T D' P' \<close>
  unfolding Identity_Elements\<^sub>I_def Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp simp add: le_fun_def; blast)

lemma [\<phi>reason %cutting]:
  \<open> Identity_Elements\<^sub>I T D\<^sub>I P
\<Longrightarrow> Identity_Elements\<^sub>E T D\<^sub>E
\<Longrightarrow> Identity_Elements T (\<lambda>x. D\<^sub>I x \<and> D\<^sub>E x) \<close>
  unfolding Identity_Elements_def
  by (smt (verit, best) Identity_Elements\<^sub>E_def Identity_Elements\<^sub>I_sub predicate1I)


subsubsection \<open>Fallback\<close>

lemma [\<phi>reason default %fail]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show\<close> (S \<transforms> 1))
\<Longrightarrow> Identity_Element\<^sub>I S Any \<close>
  unfolding TRACE_FAIL_def
  by blast

lemma [\<phi>reason default %fail]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show\<close> (1 \<transforms> S))
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


subsubsection \<open>Special Forms\<close>

lemma [\<phi>reason %identity_element_red for \<open>Identity_Element\<^sub>I _ True\<close>]:
  \<open> Identity_Element\<^sub>I X Any
\<Longrightarrow> Identity_Element\<^sub>I X True \<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by simp

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> Identity_Element\<^sub>I (\<phi>TagA mode X) P \<close>
  unfolding \<phi>TagA_def .

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> Identity_Element\<^sub>E (\<phi>TagA mode X) \<close>
  unfolding \<phi>TagA_def .


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
  \<open> (\<condition>  C \<Longrightarrow> Identity_Elements\<^sub>I A D\<^sub>A P\<^sub>A)
\<Longrightarrow> (\<condition> \<not>C \<Longrightarrow> Identity_Elements\<^sub>I B D\<^sub>B P\<^sub>B)
\<Longrightarrow> Identity_Elements\<^sub>I (If C A B) (if C then D\<^sub>A else D\<^sub>B) (if C then P\<^sub>A else P\<^sub>B) \<close>
  by (cases C; simp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<condition>  C \<Longrightarrow> Identity_Elements\<^sub>E (If C A B) D\<^sub>A)
\<Longrightarrow> (\<condition> \<not>C \<Longrightarrow> Identity_Elements\<^sub>E (If C A B) D\<^sub>B)
\<Longrightarrow> Identity_Elements\<^sub>E (If C A B) (If C D\<^sub>A D\<^sub>B)\<close>
  by (cases C; simp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<condition> C \<Longrightarrow> Identity_Element\<^sub>I A Pa)
\<Longrightarrow> (\<condition> \<not> C \<Longrightarrow> Identity_Element\<^sub>I B Pb)
\<Longrightarrow> Identity_Element\<^sub>I (If C A B) (If C Pa Pb) \<close>
  by (cases C; simp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<condition> C \<Longrightarrow> Identity_Element\<^sub>E A)
\<Longrightarrow> (\<condition> \<not> C \<Longrightarrow> Identity_Element\<^sub>E B)
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
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> Identity_Element\<^sub>I (A a) (P a))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> Identity_Element\<^sub>I (B b) (Q b))
\<Longrightarrow> Identity_Element\<^sub>I (case_sum A B x) (pred_sum P Q x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> Identity_Element\<^sub>E (A a))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> Identity_Element\<^sub>E (B b))
\<Longrightarrow> Identity_Element\<^sub>E (case_sum A B x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> Identity_Elements\<^sub>I (A a) (D\<^sub>A a) (P a))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> Identity_Elements\<^sub>I (B b) (D\<^sub>B b) (Q b))
\<Longrightarrow> Identity_Elements\<^sub>I (case_sum A B x) (case_sum D\<^sub>A D\<^sub>B x) (case_sum P Q x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> Identity_Elements\<^sub>E (A a) (D\<^sub>A a))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> Identity_Elements\<^sub>E (B b) (D\<^sub>B b))
\<Longrightarrow> Identity_Elements\<^sub>E (case_sum A B x) (case_sum D\<^sub>A D\<^sub>B x) \<close>
  unfolding Premise_def
  by (cases x; clarsimp)



subsubsection \<open>ToA Entry Point\<close>

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<transforms> 1 \<with> P @tag \<T>\<P> \<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def .

lemma [\<phi>reason default ! %identity_element_ToA+1 for \<open>_ \<transforms> ?var \<Ztypecolon> \<circle> \<with> _ @tag \<T>\<P> \<close>]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<transforms> unspec \<Ztypecolon> \<circle> \<with> P @tag \<T>\<P> \<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def
  by simp

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<transforms> x \<Ztypecolon> \<circle> \<with> P @tag \<T>\<P> \<close>
  unfolding Identity_Element\<^sub>I_def Action_Tag_def
  by simp

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> 1 \<transforms> X @tag \<T>\<P> \<close>
  unfolding Identity_Element\<^sub>E_def Action_Tag_def .

lemma [\<phi>reason default ! %identity_element_ToA+1 for \<open>?var \<Ztypecolon> \<circle> \<transforms> _ \<with> _ @tag \<T>\<P> \<close>]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> x \<Ztypecolon> \<circle> \<transforms> X @tag \<T>\<P> \<close>
  unfolding Identity_Element\<^sub>E_def Action_Tag_def
  by simp

lemma [\<phi>reason default ! %identity_element_ToA]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> x \<Ztypecolon> \<circle> \<transforms> X @tag \<T>\<P> \<close>
  unfolding Identity_Element\<^sub>E_def Action_Tag_def
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
\<Longrightarrow> \<premise> D x
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x) \<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Premise_def
  using transformation_trans by fastforce

lemma [\<phi>reason no explorative backtrack %identity_element_\<phi>+1 for \<open>Identity_Element\<^sub>I (?var \<Ztypecolon> _) _\<close>]:
  \<open> Identity_Elements\<^sub>I T D P
\<Longrightarrow> Hint_Identity_Element T x \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> \<premise> D x
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x) \<close>
  unfolding Identity_Element\<^sub>I_def Identity_Elements\<^sub>I_def Premise_def
            Orelse_shortcut_def Ant_Seq_def
  using transformation_trans by fastforce

lemma [\<phi>reason no explorative backtrack %identity_element_\<phi>]:
  \<open> Identity_Elements\<^sub>E T D
\<Longrightarrow> \<premise> D x
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
\<Longrightarrow> Identity_Element\<^sub>I (ExBI A) (Ex P)\<close>
  unfolding Identity_Element\<^sub>I_def
  by (metis ExBI_expn Transformation_def)

lemma (*The above rule is local complete*)
  \<open>Identity_Element\<^sub>I (ExBI A) P \<Longrightarrow> Identity_Element\<^sub>I (A x) P\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp; blast)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>E (A x)
\<Longrightarrow> Identity_Element\<^sub>E (ExBI A)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp; blast)

lemma (*The above rule is not local complete*)
  \<open>Identity_Element\<^sub>E (ExBI A) \<Longrightarrow> \<exists>x. Identity_Element\<^sub>E (A x)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def ExBI_expn
  by clarsimp

lemma [\<phi>reason %identity_element_cut]:
  \<open> (\<condition> P \<Longrightarrow> Identity_Element\<^sub>I A Q)
\<Longrightarrow> Identity_Element\<^sub>I (A \<subj> P) (P \<and> Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (simp; blast)

lemma
  \<open> Identity_Element\<^sub>I (A \<subj> P) (P \<and> Q) \<Longrightarrow> (P \<Longrightarrow> Identity_Element\<^sub>I A Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Satisfiable_def
  by (cases P; clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> \<premise> P
\<Longrightarrow> Identity_Element\<^sub>E (A \<subj> P)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def Premise_def
  by (clarsimp; blast)

lemma (*The above rule is local complete*)
  \<open> Identity_Element\<^sub>E (A \<subj> P) \<Longrightarrow> P \<and> Identity_Element\<^sub>E A \<close>
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
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (A \<remains> B) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def REMAINS_def
  by (clarsimp, insert mult_1_class.mult_1_left sep_magma_1_left, blast)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I A P
\<Longrightarrow> Identity_Element\<^sub>I B Q
\<Longrightarrow> Identity_Element\<^sub>I (A \<remains> B) (P \<and> Q) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Premise_def REMAINS_def
  by (clarsimp, insert mult_1_class.mult_1_right, blast)


lemma [\<phi>reason %identity_element_cut]: 
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (A \<sqinter> B) \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp)

lemma (*the above rule is local complete*)
  \<open> Identity_Element\<^sub>E (A \<sqinter> B) \<Longrightarrow> Identity_Element\<^sub>E A \<and> Identity_Element\<^sub>E B \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp)

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Element\<^sub>I A P \<or> Identity_Element\<^sub>I B Q
\<Longrightarrow> Identity_Element\<^sub>I (A \<sqinter> B) (P \<or> Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp, blast)

lemma (*the above rule is not local complete*)
  \<open> Identity_Element\<^sub>I (A \<sqinter> B) True \<Longrightarrow> Identity_Element\<^sub>I A True \<or> Identity_Element\<^sub>I B True \<close>
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
\<Longrightarrow> \<premise> finite S
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


subsection \<open>Equivalence of Objects\<close>

definition Object_Equiv :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Object_Equiv T eq \<longleftrightarrow> (\<forall>x. eq x x) \<and> (\<forall>x y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<transforms> y \<Ztypecolon> T))\<close>

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
  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>Object_Equiv _ _\<close>       (%\<phi>attr)
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
  \<phi>reason_default_pattern \<open>Object_Equiv ?T _ @tag \<A>_singular_unit\<close> \<Rightarrow>
                          \<open>Object_Equiv ?T _ @tag \<A>_singular_unit\<close> (100)
]]

lemma [\<phi>reason %object_equiv_cut+1]:
  \<open> Identity_Elements\<^sub>I T D\<^sub>I P
\<Longrightarrow> Identity_Elements\<^sub>E T D\<^sub>E
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> Object_Equiv T (\<lambda>x y. eq x y \<or> D\<^sub>I x \<and> (P x \<longrightarrow> D\<^sub>E y)) @tag \<A>_singular_unit \<close>
  unfolding Object_Equiv_def Identity_Elements\<^sub>E_def Identity_Elements\<^sub>I_def Action_Tag_def
            Transformation_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
  by clarsimp blast

lemma [\<phi>reason %object_equiv_cut]: \<comment> \<open>for non-unital algebras\<close>
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv T eq @tag \<A>_singular_unit \<close>
  unfolding Action_Tag_def
  by clarsimp



subsubsection \<open>Extracting Pure Facts\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x y. \<condition> eq x y \<Longrightarrow> \<r>EIF (x \<Ztypecolon> T \<transforms> y \<Ztypecolon> T) (P x y) )
\<Longrightarrow> \<r>EIF (Object_Equiv T eq) ((\<forall>x. eq x x) \<and> (\<forall>x y. eq x y \<longrightarrow> P x y))\<close>
  unfolding \<r>EIF_def Object_Equiv_def Premise_def Transformation_def
  by clarsimp

lemma [\<phi>reason %extract_pure]:
  \<open> (\<And>x y. \<condition> eq x y \<Longrightarrow> \<r>ESC (P x y) (x \<Ztypecolon> T \<transforms> y \<Ztypecolon> T))
\<Longrightarrow> \<r>ESC ((\<forall>x. eq x x) \<and> (\<forall>x y. eq x y \<longrightarrow> P x y)) (Object_Equiv T eq) \<close>
  unfolding \<r>ESC_def Object_Equiv_def Premise_def Transformation_def
  by clarsimp


subsubsection \<open>Reasoning Rules\<close>

lemma Object_Equiv_fallback[\<phi>reason default %object_equiv_fallback]:
  \<open>Object_Equiv T (=)\<close>
  unfolding Object_Equiv_def by simp

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv \<circle> (\<lambda>_ _. True) \<close>
  unfolding Object_Equiv_def Transformation_def
  by simp

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv (\<black_circle> T) eq \<close>
  unfolding Object_Equiv_def Transformation_def
  by auto

lemma [\<phi>reason %object_equiv_cut]:
  \<open> (\<And>a. Object_Equiv (\<lambda>x. S x a) (R a))
\<Longrightarrow> Object_Equiv (\<lambda>x. ExBI (S x)) (\<lambda>x y. \<forall>a. R a x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by (clarsimp; blast)

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv S R
\<Longrightarrow> Object_Equiv (\<lambda>x. S x \<subj> P x) (\<lambda>x y. P x \<longrightarrow> R x y \<and> P y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. S1 x \<sqinter> S2 x) (\<lambda>x y. R1 x y \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. S1 x + S2 x) (\<lambda>x y. R1 x y \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

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

lemma
  \<open> Object_Equiv S1 R1
\<Longrightarrow> Object_Equiv S2 R2
\<Longrightarrow> Object_Equiv (\<lambda>x. BI {p. p \<Turnstile> S1 x \<longrightarrow> p \<Turnstile> S2 x}) (\<lambda>x y. R1 y x \<and> R2 x y) \<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
  by clarsimp

lemma [\<phi>reason %object_equiv_cut]:
  \<open> (\<condition> C \<Longrightarrow> Object_Equiv A Ea)
\<Longrightarrow> (\<condition> \<not> C \<Longrightarrow> Object_Equiv B Eb)
\<Longrightarrow> Object_Equiv (if C then A else B) (if C then Ea else Eb) \<close>
  unfolding Premise_def
  by (cases C; simp)

lemma Object_Equiv_Mul_Quant[\<phi>reason %object_equiv_cut]:
  \<open> (\<forall>i x. eq i x x)
\<Longrightarrow> (\<And>i\<in>S. Object_Equiv (\<lambda>x. A x i) (eq i))
\<Longrightarrow> Object_Equiv (\<lambda>x. \<big_ast>i\<in>S. A x i) (\<lambda>x y. \<forall>i. eq i x y)\<close>
  unfolding Object_Equiv_def Transformation_def \<phi>Type_def
            meta_Ball_def Premise_def Mul_Quant_def
  proof (clarsimp)
    fix x y v
    assume prems: \<open>(\<And>x. x \<in> S \<Longrightarrow> \<forall>xa y. eq x xa y \<longrightarrow> (\<forall>v. v \<Turnstile> A xa x \<longrightarrow> v \<Turnstile> A y x))\<close>
                  \<open>\<forall>i. eq i x y\<close>
                  \<open>v \<Turnstile> prod (A x) S\<close>
       and \<open>finite S\<close>
    show \<open>v \<Turnstile> prod (A y) S\<close>
      by (insert prems;
          induct arbitrary: x y v rule: finite_induct[OF \<open>finite S\<close>];
          clarsimp simp add: set_mult_expn;
          metis)
  qed


subsection \<open>Equivalent Class\<close>

definition \<open>Equiv_Class T r \<longleftrightarrow> (\<forall>v x y. v \<Turnstile> T x \<and> v \<Turnstile> T y \<longrightarrow> r x y )\<close>

lemma Equiv_Class_alt_def:
  \<open> Equiv_Class T r \<longleftrightarrow> (\<forall>v x y. v \<Turnstile> (x \<Ztypecolon> T) \<and> v \<Turnstile> (y \<Ztypecolon> T) \<longrightarrow> r x y) \<close>
  unfolding \<phi>Type_def Equiv_Class_def
  by simp

definition \<open>Injective_on T D \<longleftrightarrow> Equiv_Class T (\<lambda>x y. x \<in> D \<and> y \<in> D \<longrightarrow> x = y)\<close>


subsubsection \<open>Properties\<close>

definition concretize :: \<open>('c,'x) \<phi> \<Rightarrow> 'x \<Rightarrow> 'c\<close>
  where \<open>concretize T = (\<lambda>x. @c. c \<Turnstile> (x \<Ztypecolon> T))\<close>

lemma concretize_SAT:
  \<open> Satisfiable (x \<Ztypecolon> T)
\<Longrightarrow> concretize T x \<Turnstile> (x \<Ztypecolon> T) \<close>
  unfolding concretize_def Satisfiable_def
  by (meson someI_ex)
  
lemma concretize_inj:
  \<open> Injective_on T D
\<Longrightarrow> Abstract_Domain\<^sub>L T (\<lambda>x. x \<in> D)
\<Longrightarrow> inj_on (concretize T) D \<close>
  unfolding inj_on_def Equiv_Class_def concretize_def Abstract_Domain\<^sub>L_def \<r>ESC_def Satisfiable_def
            \<phi>Type_def Injective_on_def
  by (auto, metis someI)



subsubsection \<open>Reasoning Configures\<close>

\<phi>reasoner_group Equiv_Class_all = (100, [10,3000]) \<open>\<close>
  and Equiv_Class = (1000, [1000,1030]) in Equiv_Class_all \<open>\<close>
  and Equiv_Class_default = (25, [10,50]) in Equiv_Class_all and < Equiv_Class \<open>\<close>
  and Equiv_Class_derived = (75, [70, 80]) in Equiv_Class_all and < Equiv_Class and > Equiv_Class_default \<open>\<close>

declare [[
  \<phi>reason_default_pattern \<open>Equiv_Class ?T ?var\<close> \<Rightarrow> \<open>Equiv_Class ?T _\<close> (100)
                      and \<open>Equiv_Class ?T _\<close> \<Rightarrow> \<open>Equiv_Class ?T ?var\<close> (80),
  \<phi>default_reasoner_group \<open>Equiv_Class _ _\<close> : %Equiv_Class (100)
]]


subsubsection \<open>Reasoning Rules\<close>

lemma [\<phi>reason %Equiv_Class]:
  \<open> Equiv_Class T (\<lambda>x y. x \<in> D \<and> y \<in> D \<longrightarrow> x = y)
\<Longrightarrow> Injective_on T D \<close>
  unfolding Injective_on_def
  by simp

lemma [\<phi>reason add]:
  \<open> Equiv_Class (\<lambda>x. A (fst x) (snd x)) (\<lambda>(x\<^sub>1,_) (x\<^sub>2,_). r x\<^sub>1 x\<^sub>2)
\<Longrightarrow> Equiv_Class (\<lambda>x. ExBI (A x)) r \<close>
  unfolding Equiv_Class_def
  by auto blast

lemma (*the above rule is the strongest*)
  \<open> Equiv_Class (\<lambda>x. ExBI (A x)) r
\<Longrightarrow> Equiv_Class (\<lambda>x. A (fst x) (snd x)) (\<lambda>(x\<^sub>1,_) (x\<^sub>2,_). r x\<^sub>1 x\<^sub>2) \<close>
  unfolding Equiv_Class_def
  by auto

lemma [\<phi>reason add]:
  \<open> Equiv_Class A (\<lambda>x y. P x \<and> P y \<longrightarrow> r x y)
\<Longrightarrow> Equiv_Class (\<lambda>x. A x \<subj> P x) r \<close>
  unfolding Equiv_Class_def
  by auto

lemma (*the above rule is the strongest*)
  \<open> Equiv_Class (\<lambda>x. A x \<subj> P x) r
\<Longrightarrow> Equiv_Class A (\<lambda>x y. P x \<and> P y \<longrightarrow> r x y) \<close>
  unfolding Equiv_Class_def
  by auto

lemma [\<phi>reason add]:
  \<open> \<premise> (\<forall>x. r x x)
\<Longrightarrow> Equiv_Class Itself r \<close>
  unfolding Equiv_Class_def Premise_def
  by simp

lemma [\<phi>reason %Equiv_Class_default except \<open>Equiv_Class _ ?var\<close> ]:
  \<open> Equiv_Class T r
\<Longrightarrow> \<premise> (\<forall>x y. r x y \<longrightarrow> r' x y)
\<Longrightarrow> Equiv_Class T r' \<close>
  unfolding Premise_def Equiv_Class_def
  by auto

lemma [\<phi>reason add]:
  \<open> Equiv_Class T (\<lambda>x y. \<forall>x' y'. x = f x' \<and> y = f y' \<longrightarrow> r x' y')
\<Longrightarrow> Equiv_Class (\<lambda>x. f x \<Ztypecolon> T) r \<close>
  unfolding Equiv_Class_def \<phi>Type_def
  by auto

lemma (*the above rule is the strongest*)
  \<open> Equiv_Class (\<lambda>x. f x \<Ztypecolon> T) r
\<Longrightarrow> Equiv_Class T (\<lambda>x y. \<forall>x' y'. x = f x' \<and> y = f y' \<longrightarrow> r x' y') \<close>
  unfolding Equiv_Class_def \<phi>Type_def
  by auto

lemma [\<phi>reason add]:
  \<open> A \<implies> P
\<Longrightarrow> \<premise> (P \<longrightarrow> (\<forall>a b. r a b))
\<Longrightarrow> Equiv_Class (\<lambda>x. A) r \<close>
  unfolding Equiv_Class_def Premise_def \<r>EIF_def Satisfiable_def
  by simp blast

lemma (*the above rule is the strongest*)
  \<open> Equiv_Class (\<lambda>x. A) r
\<Longrightarrow> Satisfiable A
\<Longrightarrow> \<forall>a b. r a b \<close>
  unfolding Equiv_Class_def Satisfiable_def
  by auto




section \<open>Reasoning\<close>

ML_file \<open>library/syntax/Phi_Syntax0.ML\<close>

subsection \<open>Preliminary\<close>

subsubsection \<open>Mapping \<phi>-Type Items by Transformation\<close>

consts \<A>_map_each_item :: \<open>action \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<transforms> _ \<with> _ @tag \<A>_map_each_item _\<close> \<Rightarrow>
      \<open>?X \<transforms> _ \<with> _ @tag \<A>_map_each_item _\<close>    (100)
  and \<open>?X @tag \<A>_map_each_item ?\<A> \<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Bad Rule: \<close> (?X @tag \<A>_map_each_item ?\<A>)) \<close>    (0)
]]

\<phi>reasoner_group \<A>_map_each_item = (1050, [1010, 3000]) for (\<open>X \<transforms> _ \<with> _ @tag \<A>_map_each_item \<A>\<close>)
      \<open>Reasoning rules applying action \<open>\<A>\<close> onto each atomic items in \<open>X\<close>\<close>
  and \<A>_map_each_item_fallback = (1000, [1000, 1000]) for (\<open>X \<transforms> _ \<with> _ @tag \<A>_map_each_item \<A>\<close>)
      \<open>Fallback rules ending \<A>_map_each_item\<close>

paragraph \<open>Implementation\<close>

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> 1 \<transforms> 1 @tag \<A>_map_each_item A \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> 0 \<transforms> 0 @tag \<A>_map_each_item A \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> \<top> \<transforms> \<top> @tag \<A>_map_each_item A \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> \<condition> Q \<longrightarrow> (X \<transforms> Y \<with> P @tag \<A>_map_each_item A)
\<Longrightarrow> X \<subj> Q \<transforms> Y \<subj> Q \<with> P @tag \<A>_map_each_item A\<close>
  unfolding Action_Tag_def Premise_def Transformation_def
  by simp blast

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> A \<transforms> X \<with> P @tag \<A>_map_each_item \<A>
\<Longrightarrow> B \<transforms> Y \<with> Q @tag \<A>_map_each_item \<A>
\<Longrightarrow> A \<sqinter> B \<transforms> X \<sqinter> Y \<with> P \<and> Q @tag \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Transformation_def
  by simp blast

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> A \<transforms> X \<with> P @tag \<A>_map_each_item \<A>
\<Longrightarrow> B \<transforms> Y \<with> Q @tag \<A>_map_each_item \<A>
\<Longrightarrow> A + B \<transforms> X + Y \<with> P \<or> Q @tag \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Transformation_def
  by simp

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> (\<And>c. X c \<transforms> Y c \<with> P @tag \<A>_map_each_item A)
\<Longrightarrow> ExBI X \<transforms> ExBI Y \<with> P @tag \<A>_map_each_item A\<close>
  unfolding Action_Tag_def
  using ExBI_transformation .

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> (\<And>c. X c \<transforms> Y c \<with> P @tag \<A>_map_each_item A)
\<Longrightarrow> AllSet X \<transforms> AllSet Y \<with> P @tag \<A>_map_each_item A\<close>
  unfolding Action_Tag_def Transformation_def
  by simp blast

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> A \<transforms> X \<with> P @tag \<A>_map_each_item \<A>
\<Longrightarrow> B \<transforms> Y \<with> Q @tag \<A>_map_each_item \<A>
\<Longrightarrow> A * B \<transforms> X * Y \<with> P \<and> Q @tag \<A>_map_each_item \<A> \<close>
  unfolding Action_Tag_def Transformation_def
  by simp blast

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> X \<transforms> Y \<with> P @tag \<A>_map_each_item A
\<Longrightarrow> W \<transforms> R \<with> Q @tag \<A>_map_each_item A
\<Longrightarrow> X \<remains> W \<transforms> Y \<remains> R \<with> P \<and> Q @tag \<A>_map_each_item A\<close>
  unfolding REMAINS_def
  by (simp add: Action_Tag_def transformation_bi_frame;
      metis transformation_bi_frame transformation_weaken)

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> (\<condition>   C \<Longrightarrow> A \<transforms> A' \<with> P @tag \<A>_map_each_item \<A>)
\<Longrightarrow> (\<condition> \<not> C \<Longrightarrow> B \<transforms> B' \<with> Q @tag \<A>_map_each_item \<A>)
\<Longrightarrow> If C A B \<transforms> If C A' B' \<with> If C P Q @tag \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Premise_def
  by (cases C; simp)

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> A a \<transforms> A' a \<with> P a @tag \<A>_map_each_item \<A>)
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> B b \<transforms> B' b \<with> Q b @tag \<A>_map_each_item \<A>)
\<Longrightarrow> (case_sum A B x) \<transforms> (case_sum A' B' x) \<with> case_sum P Q x @tag \<A>_map_each_item \<A>\<close>
  unfolding Action_Tag_def Premise_def
  by (cases x; simp)

lemma [\<phi>reason %\<A>_map_each_item]:
  \<open> (\<And>i\<in>I. A i \<transforms> B i \<with> P i @tag \<A>_map_each_item \<A>)
\<Longrightarrow> (\<big_ast>i\<in>I. A i) \<transforms> (\<big_ast>i\<in>I. B i) \<with> (\<forall>i \<in> I. P i) @tag \<A>_map_each_item \<A> \<close>
  unfolding Action_Tag_def Premise_def
  by (clarsimp simp add: sep_quant_transformation)

lemma [\<phi>reason %\<A>_map_each_item_fallback]: \<comment> \<open>fallback\<close>
  \<open> X \<transforms> Y \<with> P @tag A
\<Longrightarrow> X \<transforms> Y \<with> P @tag \<A>_map_each_item A\<close>
  unfolding Action_Tag_def .


subsection \<open>Cleaning\<close>

subsubsection \<open>Success\<close>

lemma [\<phi>reason %ToA_clean for \<open>_ \<Ztypecolon> _ \<transforms> _ \<Ztypecolon> \<circle> @clean\<close>
                              \<open>_ \<Ztypecolon> \<circle> \<transforms> _ \<Ztypecolon> _ @clean\<close> ]:
  \<open> a \<Ztypecolon> \<circle> \<transforms> b \<Ztypecolon> \<circle> @clean \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %ToA_clean+10 for \<open>_ \<Ztypecolon> _ \<transforms> _ @clean\<close> ]:
  \<open> a \<Ztypecolon> \<circle> \<transforms> 1 @clean \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %ToA_clean+10 for \<open>_ \<transforms> _ \<Ztypecolon> _ @clean\<close> ]:
  \<open> 1 \<transforms> a \<Ztypecolon> \<circle> @clean \<close>
  unfolding Action_Tag_def
  by simp


subsubsection \<open>Fallbacks\<close>

lemma [\<phi>reason default %ToA_clean_fallback for \<open>_ \<transforms> _ \<with> _ @clean\<close>]:
  \<open> X \<transforms> X @clean \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason default %ToA_clean_fallback-5 for \<open>_ \<transforms> (_,_) \<Ztypecolon> _ @clean\<close>]:
  \<open> W \<transforms> y \<Ztypecolon> T @clean
\<Longrightarrow> W \<transforms> (fst y, snd y) \<Ztypecolon> T @clean \<close>
  by simp

lemma [\<phi>reason default %ToA_clean_fallback-5 for \<open>_ \<transforms> (_,_,_) \<Ztypecolon> _ @clean\<close>]:
  \<open> W \<transforms> y \<Ztypecolon> T @clean
\<Longrightarrow> W \<transforms> (fst y, fst (snd y), snd (snd y)) \<Ztypecolon> T @clean \<close>
  by simp

lemma [\<phi>reason default %ToA_clean_fallback-10 for \<open>_ \<Ztypecolon> _ \<transforms> _ \<Ztypecolon> _ \<with> _ @clean\<close>]:
  \<open> \<premise> x = y
\<Longrightarrow> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> T @clean \<close>
  unfolding Action_Tag_def Premise_def
  by simp


subsubsection \<open>Empty Assertion\<close>

lemma [\<phi>reason %ToA_clean]:
  \<open> R \<transforms> Y @clean
\<Longrightarrow> 1 * R \<transforms> Y @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %ToA_clean]:
  \<open> R \<transforms> Y @clean
\<Longrightarrow> R * 1 \<transforms> R @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %ToA_clean+30]:
  \<open> R \<transforms> Y @clean
\<Longrightarrow> (r \<Ztypecolon> \<circle>) * R \<transforms> Y @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason add]:
  \<open> R \<transforms> Y @clean
\<Longrightarrow> R * (x \<Ztypecolon> \<circle>) \<transforms> Y @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  by simp


subsubsection \<open>Empty Type\<close>

lemma [\<phi>reason add]:
  \<open> W \<transforms> y \<Ztypecolon> U @clean
\<Longrightarrow> W \<transforms> (x,y) \<Ztypecolon> \<circle> \<^emph> U @clean \<close>
  for W :: \<open>'c::sep_magma_1 BI\<close>
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> W \<transforms> x \<Ztypecolon> T @clean
\<Longrightarrow> W \<transforms> (x,y) \<Ztypecolon> T \<^emph> \<circle> @clean \<close>
  for W :: \<open>'c::sep_magma_1 BI\<close>
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> W \<transforms> (x,y) \<Ztypecolon> T \<^emph> U @clean
\<Longrightarrow> W \<transforms> (x,y,z) \<Ztypecolon> T \<^emph> U \<^emph> \<circle> @clean \<close>
  for W :: \<open>'c::sep_magma_1 BI\<close>
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> y \<Ztypecolon> U \<transforms> R @clean
\<Longrightarrow> (x,y) \<Ztypecolon> \<circle> \<^emph> U \<transforms> R @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> x \<Ztypecolon> T \<transforms> R @clean
\<Longrightarrow> (x,y) \<Ztypecolon> T \<^emph> \<circle> \<transforms> R @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> (x,y) \<Ztypecolon> T \<^emph> U \<transforms> R @clean
\<Longrightarrow> (x,y,z) \<Ztypecolon> T \<^emph> U \<^emph> \<circle> \<transforms> R @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> snd x \<Ztypecolon> U \<transforms> R @clean
\<Longrightarrow> x \<Ztypecolon> \<circle> \<^emph> U \<transforms> R @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> fst x \<Ztypecolon> T \<transforms> R @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> \<circle> \<transforms> R @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> apsnd fst x \<Ztypecolon> T \<^emph> U \<transforms> R @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> U \<^emph> \<circle> \<transforms> R @clean \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  by (cases x; simp add: \<phi>Prod_expn')





subsubsection \<open>Conditioned Empty\<close>

declare [[
  \<phi>reason_default_pattern
      \<open>_ \<transforms> (_,_) \<Ztypecolon> \<half_blkcirc>[?C] _ \<^emph> _ @clean\<close> \<Rightarrow> \<open>_ \<transforms> (_,_) \<Ztypecolon> \<half_blkcirc>[?C] _ \<^emph> _ @clean\<close> (100)
  and \<open>_ \<transforms> (_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ @clean\<close> \<Rightarrow> \<open>_ \<transforms> (_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ @clean\<close> (100)
  and \<open>_ \<transforms> (_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ @clean\<close> \<Rightarrow> \<open>_ \<transforms> (_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ @clean\<close> (100)
  and \<open>_ \<transforms> (_,_,_) \<Ztypecolon> _ \<^emph> _ \<^emph> \<half_blkcirc>[?C] _ @clean\<close> \<Rightarrow> \<open>_ \<transforms> (_,_,_) \<Ztypecolon> _ \<^emph> _ \<^emph> \<half_blkcirc>[?C] _ @clean\<close> (100)
  and \<open>_ \<transforms> (_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ @clean\<close> \<Rightarrow> \<open>_ \<transforms> (_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ @clean\<close> (100)
  and \<open>(_,_) \<Ztypecolon> \<half_blkcirc>[?C] _ \<^emph> _ \<transforms> _ @clean\<close> \<Rightarrow> \<open>(_,_) \<Ztypecolon> \<half_blkcirc>[?C] _ \<^emph> _ \<transforms> _ @clean\<close> (100)
  and \<open>(_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ \<transforms> _ @clean\<close> \<Rightarrow> \<open>(_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ \<transforms> _ @clean\<close> (100)
  and \<open>(_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<transforms> _ @clean\<close> \<Rightarrow> \<open>(_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<transforms> _ @clean\<close> (100)
  and \<open>(_,_,_) \<Ztypecolon> _ \<^emph> _ \<^emph> \<half_blkcirc>[?C] _ \<transforms> _ @clean\<close> \<Rightarrow> \<open>(_,_,_) \<Ztypecolon> _ \<^emph> _ \<^emph> \<half_blkcirc>[?C] _ \<transforms> _ @clean\<close> (100)
  and \<open>(_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ \<transforms> _ @clean\<close> \<Rightarrow> \<open>(_,_,_) \<Ztypecolon> _ \<^emph> \<half_blkcirc>[?C] _ \<^emph> _ \<transforms> _ @clean\<close> (100),
  \<phi>default_reasoner_group \<open>(_,_) \<Ztypecolon> ?T \<transforms> _ \<with> _ @clean\<close> : %ToA_clean+10 (30)
]]



lemma [\<phi>reason add]:
  \<open> W \<transforms> x \<Ztypecolon> \<circle> @clean
\<Longrightarrow> W \<transforms> x \<Ztypecolon> \<half_blkcirc>[False] T @clean \<close>
  \<open> W \<transforms> x \<Ztypecolon> T @clean
\<Longrightarrow> W \<transforms> x \<Ztypecolon> \<half_blkcirc>[True] T @clean \<close>
  by simp_all

lemma [\<phi>reason add]:
  \<open> x \<Ztypecolon> \<circle> \<transforms> R @clean
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[False] T \<transforms> R @clean \<close>
  \<open> x \<Ztypecolon> T \<transforms> R @clean
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[True] T \<transforms> R @clean \<close>
  by simp_all

lemma [\<phi>reason add]:
  \<open> W \<transforms> xy \<Ztypecolon> T \<^emph> U @clean
\<Longrightarrow> W \<transforms> xy \<Ztypecolon> \<half_blkcirc>[True] T \<^emph> U @clean \<close>
  \<open> W \<transforms> y \<Ztypecolon> U @clean
\<Longrightarrow> W \<transforms> (x, y) \<Ztypecolon> \<half_blkcirc>[False] T \<^emph> U @clean \<close>
  by (simp add: \<phi>Prod_expn')+

lemma [\<phi>reason add]:
  \<open> W \<transforms> x3 \<Ztypecolon> T \<^emph> U \<^emph> S @clean
\<Longrightarrow> W \<transforms> x3 \<Ztypecolon> T \<^emph> \<half_blkcirc>[True] U \<^emph> S @clean \<close>
  \<open> W \<transforms> xz \<Ztypecolon> T \<^emph> S @clean
\<Longrightarrow> W \<transforms> apsnd (Pair unspec) xz \<Ztypecolon> T \<^emph> \<half_blkcirc>[False] U \<^emph> S @clean \<close>
  \<open> W \<transforms> (x,z) \<Ztypecolon> T \<^emph> S @clean
\<Longrightarrow> W \<transforms> (x,y,z) \<Ztypecolon> T \<^emph> \<half_blkcirc>[False] U \<^emph> S @clean \<close>
  by (simp add: \<phi>Prod_expn', cases xz, simp_all add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> W \<transforms> x3 \<Ztypecolon> T \<^emph> U \<^emph> S @clean
\<Longrightarrow> W \<transforms> x3 \<Ztypecolon> T \<^emph> U \<^emph> \<half_blkcirc>[True] S @clean \<close>
  \<open> W \<transforms> xy \<Ztypecolon> T \<^emph> U @clean
\<Longrightarrow> W \<transforms> apsnd (\<lambda>y. (y, unspec)) xy \<Ztypecolon> T \<^emph> U \<^emph> \<half_blkcirc>[False] S @clean \<close>
  \<open> W \<transforms> (x,y) \<Ztypecolon> T \<^emph> U @clean
\<Longrightarrow> W \<transforms> (x,y,unspec) \<Ztypecolon> T \<^emph> U \<^emph> \<half_blkcirc>[False] S @clean \<close>
  by (simp add: \<phi>Prod_expn', cases xy, simp_all add: \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> W \<transforms> xy \<Ztypecolon> T \<^emph> U @clean
\<Longrightarrow> W \<transforms> xy \<Ztypecolon> T \<^emph> \<half_blkcirc>[True] U @clean \<close>
  \<open> W \<transforms> x \<Ztypecolon> T @clean
\<Longrightarrow> W \<transforms> (x, y) \<Ztypecolon> T \<^emph> \<half_blkcirc>[False] U @clean \<close>
  by (simp add: \<phi>Prod_expn')+

lemma [\<phi>reason add]:
  \<open> x \<Ztypecolon> T \<^emph> U \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[True] T \<^emph> U \<transforms> W @clean \<close>
  \<open> snd x \<Ztypecolon> U \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[False] T \<^emph> U \<transforms> W @clean \<close>
  \<open> b \<Ztypecolon> U \<transforms> W @clean
\<Longrightarrow> (a,b) \<Ztypecolon> \<half_blkcirc>[False] T \<^emph> U \<transforms> W @clean \<close>
  by (cases x; simp add: \<phi>Prod_expn')+

lemma [\<phi>reason add]:
  \<open> x \<Ztypecolon> T \<^emph> U \<^emph> S \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> \<half_blkcirc>[True] U \<^emph> S \<transforms> W @clean \<close>
  \<open> apsnd snd x \<Ztypecolon> T \<^emph> S \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> \<half_blkcirc>[False] U \<^emph> S \<transforms> W @clean \<close>
  \<open> (a,c) \<Ztypecolon> T \<^emph> S \<transforms> W @clean
\<Longrightarrow> (a,b,c) \<Ztypecolon> T \<^emph> \<half_blkcirc>[False] U \<^emph> S \<transforms> W @clean \<close>
  by (cases x; simp add: \<phi>Prod_expn')+

lemma [\<phi>reason add]:
  \<open> x \<Ztypecolon> T \<^emph> U \<^emph> S \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> U \<^emph> \<half_blkcirc>[True] S \<transforms> W @clean \<close>
  \<open> apsnd fst x \<Ztypecolon> T \<^emph> U \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> U \<^emph> \<half_blkcirc>[False] S \<transforms> W @clean \<close>
  \<open> (a,b) \<Ztypecolon> T \<^emph> U \<transforms> W @clean
\<Longrightarrow> (a,b,c) \<Ztypecolon> T \<^emph> U \<^emph> \<half_blkcirc>[False] S \<transforms> W @clean \<close>
  by (cases x; simp add: \<phi>Prod_expn')+

lemma [\<phi>reason add]:
  \<open> x \<Ztypecolon> T \<^emph> U \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> \<half_blkcirc>[True] U \<transforms> W @clean \<close>
  \<open> fst x \<Ztypecolon> T \<transforms> W @clean
\<Longrightarrow> x \<Ztypecolon> T \<^emph> \<half_blkcirc>[False] U \<transforms> W @clean \<close>
  \<open> a \<Ztypecolon> T \<transforms> W @clean
\<Longrightarrow> (a,b) \<Ztypecolon> T \<^emph> \<half_blkcirc>[False] U \<transforms> W @clean \<close>
  by (cases x; simp add: \<phi>Prod_expn')+


subsubsection \<open>\<open>\<Psi>[Some]\<close>\<close>

lemma [\<phi>reason %ToA_clean_fallback for \<open>\<Psi>[Some] _ * \<Psi>[Some] _ \<transforms> \<Psi>[Some] _ \<with> _ @clean\<close>]:
  \<open> \<Psi>[Some] X * \<Psi>[Some] Y \<transforms> \<Psi>[Some] (X * Y) @clean \<close>
  unfolding Action_Tag_def
  using Transformation_def by fastforce


subsection \<open>Associative Multiplication\<close>

definition \<open>\<r>Assoc_Mul A B C \<longleftrightarrow> ((A * B) * C = A * (B * C)) \<close>

paragraph \<open>Basic Settings\<close>

\<phi>reasoner_group \<r>Assoc_Mul_all = (100, [10,3000]) for \<open>\<r>Assoc_Mul A B C\<close> \<open>\<close>
  and \<r>Assoc_Mul = (1000, [1000,1030]) in \<r>Assoc_Mul_all \<open>\<close>
  and \<r>Assoc_Mul_default = (20, [10, 50]) in \<r>Assoc_Mul_all and < \<r>Assoc_Mul \<open>\<close>

declare [[
  \<phi>default_reasoner_group \<open>\<r>Assoc_Mul _ _ _\<close> : %\<r>Assoc_Mul (100)
]]

setup \<open>Sign.mandatory_path "\<r>Assoc_Mul"\<close>

lemma "apply":
  \<open> \<r>Assoc_Mul A B C
\<Longrightarrow> A * B * C \<transforms> A * (B * C) \<close>
  unfolding \<r>Assoc_Mul_def by simp

lemma "rev_apply":
  \<open> \<r>Assoc_Mul A B C
\<Longrightarrow> A * (B * C) \<transforms> A * B * C \<close>
  unfolding \<r>Assoc_Mul_def by simp

setup \<open>Sign.parent_path\<close>

paragraph \<open>Reasoning Rules\<close>

lemma [\<phi>reason add]:
  \<open> \<r>Assoc_Mul A B C \<close>
  for A :: \<open>'a::semigroup_mult\<close>
  unfolding \<r>Assoc_Mul_def
  by (simp add: mult.assoc)

lemma [\<phi>reason add]:
  \<open> \<r>Assoc_Mul 1 B C \<close>
  \<open> \<r>Assoc_Mul A 1 C \<close>
  \<open> \<r>Assoc_Mul A B 1 \<close>
  for A :: \<open>'a::mult_1\<close>
  unfolding \<r>Assoc_Mul_def
  by simp+

lemma [\<phi>reason add]:
  \<open> \<r>Assoc_Mul (x \<Ztypecolon> \<circle>) B C \<close>
  \<open> \<r>Assoc_Mul A (x \<Ztypecolon> \<circle>) C \<close>
  \<open> \<r>Assoc_Mul A B (x \<Ztypecolon> \<circle>) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding \<r>Assoc_Mul_def
  by simp+

lemma [\<phi>reason add]:
  \<open> \<r>Assoc_Mul (x \<Ztypecolon> \<half_blkcirc>[False] T) B C \<close>
  \<open> \<r>Assoc_Mul A (x \<Ztypecolon> \<half_blkcirc>[False] T) C \<close>
  \<open> \<r>Assoc_Mul A B (x \<Ztypecolon> \<half_blkcirc>[False] T) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding \<r>Assoc_Mul_def
  by simp+

lemma [\<phi>reason add]:
  \<open> \<r>Assoc_Mul (x \<Ztypecolon> T) B C
\<Longrightarrow> \<r>Assoc_Mul (x \<Ztypecolon> \<half_blkcirc>[True] T) B C \<close>
  \<open> \<r>Assoc_Mul A (x \<Ztypecolon> T) C
\<Longrightarrow> \<r>Assoc_Mul A (x \<Ztypecolon> \<half_blkcirc>[True] T) C \<close>
  \<open> \<r>Assoc_Mul A B (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Assoc_Mul A B (x \<Ztypecolon> \<half_blkcirc>[True] T) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding \<r>Assoc_Mul_def
  by simp+



subsection \<open>Commutative Muiltiplication\<close>

definition \<open>\<r>Comm_Mul A B \<longleftrightarrow> (A * B = B * A)\<close>

paragraph \<open>Basic Settings\<close>

\<phi>reasoner_group \<r>Comm_Mul_all = (100, [10,3000]) for \<open>\<r>Comm_Mul A B\<close> \<open>\<close>
  and \<r>Comm_Mul = (1000, [1000,1030]) in \<r>Comm_Mul_all \<open>\<close>
  and \<r>Comm_Mul_default = (20, [10, 50]) in \<r>Comm_Mul_all and < \<r>Comm_Mul \<open>\<close>

declare [[
  \<phi>default_reasoner_group \<open>\<r>Comm_Mul _ _\<close> : %\<r>Comm_Mul (100)
]]

setup \<open>Sign.mandatory_path "\<r>Comm_Mul"\<close>

lemma "apply":
  \<open> \<r>Comm_Mul A B
\<Longrightarrow> A * B \<transforms> B * A \<close>
  unfolding \<r>Comm_Mul_def by simp

lemma "rev_apply":
  \<open> \<r>Comm_Mul B A
\<Longrightarrow> A * B \<transforms> B * A \<close>
  unfolding \<r>Comm_Mul_def by simp

setup \<open>Sign.parent_path\<close>

paragraph \<open>Reasoning Rules\<close>

lemma [\<phi>reason add]:
  \<open> \<r>Comm_Mul A B \<close>
  for A :: \<open>'a::ab_semigroup_mult\<close>
  unfolding \<r>Comm_Mul_def
  by (simp add: mult.commute)

lemma [\<phi>reason add]:
  \<open> \<r>Comm_Mul 1 A \<close>
  \<open> \<r>Comm_Mul A 1 \<close>
  for A :: \<open>'a::mult_1\<close>
  unfolding \<r>Comm_Mul_def
  by simp+

lemma [\<phi>reason add]:
  \<open> \<r>Comm_Mul (x \<Ztypecolon> \<circle>) A \<close>
  \<open> \<r>Comm_Mul A (x \<Ztypecolon> \<circle>) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding \<r>Comm_Mul_def
  by simp+

lemma [\<phi>reason add]:
  \<open> \<r>Comm_Mul (x \<Ztypecolon> \<half_blkcirc>[False] T) A \<close>
  \<open> \<r>Comm_Mul A (x \<Ztypecolon> \<half_blkcirc>[False] T) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding \<r>Comm_Mul_def
  by simp+

lemma [\<phi>reason add]:
  \<open> \<r>Comm_Mul (x \<Ztypecolon> T) A
\<Longrightarrow> \<r>Comm_Mul (x \<Ztypecolon> \<half_blkcirc>[True] T) A \<close>
  \<open> \<r>Comm_Mul A (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Comm_Mul A (x \<Ztypecolon> \<half_blkcirc>[True] T) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding \<r>Comm_Mul_def
  by simp+



subsubsection \<open>Separation Extraction of \<open>\<phi>\<close>Prod\<close>

text \<open>Using the technical auxiliaries, we can give the separation extraction for \<open>\<phi>Prod\<close>\<close>
 
lemma [\<phi>reason %ToA_cut]:
  \<open> (fst x, fst ww) \<Ztypecolon> A \<OTast> WY \<transforms> b \<Ztypecolon> Y \<OTast> B \<with> P1 @tag \<T>\<P>'
\<Longrightarrow> (snd b, snd ww) \<Ztypecolon> B \<OTast> WX \<transforms> c \<Ztypecolon> X \<OTast> R \<with> P2 @tag \<T>\<P>'
\<Longrightarrow> \<r>Assoc_Mul (fst x \<Ztypecolon> A) (fst ww \<Ztypecolon> WY) (snd ww \<Ztypecolon> WX)
\<Longrightarrow> \<r>Assoc_Mul (fst b \<Ztypecolon> Y) (snd b \<Ztypecolon> B) (snd ww \<Ztypecolon> WX)
\<Longrightarrow> \<r>Assoc_Mul (fst b \<Ztypecolon> Y) (fst c \<Ztypecolon> X) (snd c \<Ztypecolon> R)
\<Longrightarrow> snd x \<Ztypecolon> WW \<transforms> ww \<Ztypecolon> WY \<^emph> WX @clean
\<Longrightarrow> x \<Ztypecolon> A \<OTast> WW \<transforms> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<OTast> R \<with> (P1 \<and> P2) @tag \<T>\<P>'\<close>
  for A :: \<open>('a::sep_magma_1,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def \<phi>Prod'_def \<r>Assoc_Mul_def
  apply (clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')
  subgoal premises prems
    by (insert prems(1)[THEN transformation_right_frame, where R=\<open>snd ww \<Ztypecolon> WX\<close>]
               prems(2)[THEN transformation_left_frame, where R=\<open>fst b \<Ztypecolon> Y\<close>]
               prems(3)[symmetric]
               prems(4)[symmetric]
               prems(5)[symmetric]
               prems(6)[THEN transformation_left_frame, where R=\<open>fst x \<Ztypecolon> A\<close>],
           cases b, simp,
           insert mk_elim_transformation transformation_trans, blast) .

lemma [\<phi>reason %ToA_cut+1]:
  \<open> (fst x, fst ww) \<Ztypecolon> A \<OTast> WY \<transforms> b \<Ztypecolon> Y \<OTast> B \<with> P1 @tag \<T>\<P>'
\<Longrightarrow> (snd b, snd ww) \<Ztypecolon> B \<OTast> WX \<transforms> c \<Ztypecolon> X \<OTast> R \<with> P2 @tag \<T>\<P>'
\<Longrightarrow> snd x \<Ztypecolon> WW \<transforms> ww \<Ztypecolon> WY \<^emph> WX @clean
\<Longrightarrow> x \<Ztypecolon> A \<OTast> WW \<transforms> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<OTast> R \<with> (P1 \<and> P2) @tag \<T>\<P>'\<close>
  for A :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def \<phi>Prod'_def
  apply (clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')
  subgoal premises prems
    by (insert prems(1)[THEN transformation_right_frame, where R=\<open>snd ww \<Ztypecolon> WX\<close>]
               prems(2)[THEN transformation_left_frame, where R=\<open>fst b \<Ztypecolon> Y\<close>]
               prems(3)[THEN transformation_left_frame, where R=\<open>fst x \<Ztypecolon> A\<close>],
           cases b, simp add: mult.assoc,
           insert mk_elim_transformation transformation_trans, blast) .

lemma [\<phi>reason add]:
  \<open> X \<transforms> wx \<Ztypecolon> WX @clean
\<Longrightarrow> X \<transforms> (unspec, wx) \<Ztypecolon> \<circle> \<^emph> WX @clean \<close>
  for WX :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding Action_Tag_def
  by (clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> X \<transforms> wy \<Ztypecolon> WY @clean
\<Longrightarrow> X \<transforms> (wy, unspec) \<Ztypecolon> WY \<^emph> \<circle> @clean \<close>
  for WY :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding Action_Tag_def
  by (clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')


lemma [\<phi>reason %ToA_cut]:
  \<open> (fst (fst x), fst wr) \<Ztypecolon> T \<OTast> W \<transforms> yr \<Ztypecolon> Y \<OTast> Rt \<with> P1 @tag \<T>\<P>'
\<Longrightarrow> apfst snd x \<Ztypecolon> U \<OTast> W2 \<transforms> wr \<Ztypecolon> W \<OTast> Ru \<with> P2 @tag \<T>\<P>'
\<Longrightarrow> \<r>Assoc_Mul (fst (fst x) \<Ztypecolon> T) (snd (fst x) \<Ztypecolon> U ) (snd x \<Ztypecolon> W2)
\<Longrightarrow> \<r>Assoc_Mul (fst (fst x) \<Ztypecolon> T) (fst wr \<Ztypecolon> W ) (snd wr \<Ztypecolon> Ru)
\<Longrightarrow> \<r>Assoc_Mul (fst yr \<Ztypecolon> Y) (snd yr \<Ztypecolon> Rt) (snd wr \<Ztypecolon> Ru)
\<Longrightarrow> (snd yr, snd wr) \<Ztypecolon> Rt \<^emph> Ru \<transforms> rr \<Ztypecolon> RR @clean
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<OTast> W2 \<transforms> (fst yr, rr) \<Ztypecolon> Y \<OTast> RR \<with> P1 \<and> P2 @tag \<T>\<P>' \<close>
  for T :: \<open>('a::sep_magma_1,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def \<phi>Prod'_def \<r>Assoc_Mul_def
  apply (simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric])
  subgoal premises prems
    by (insert prems(1)[THEN transformation_right_frame, where R=\<open>snd wr \<Ztypecolon> Ru\<close>]
               prems(2)[THEN transformation_left_frame, where R=\<open>fst (fst x) \<Ztypecolon> T\<close>]
               prems(3)[symmetric]
               prems(4)[symmetric]
               prems(5)[symmetric]
               prems(6)[THEN transformation_left_frame, where R=\<open>(fst yr \<Ztypecolon> Y)\<close>],
        simp,
        smt (z3) mk_elim_transformation mk_intro_transformation transformation_weaken) .

lemma [\<phi>reason %ToA_cut+1]:
  \<open> (fst (fst x), fst wr) \<Ztypecolon> T \<OTast> W \<transforms> yr \<Ztypecolon> Y \<OTast> Rt \<with> P1 @tag \<T>\<P>'
\<Longrightarrow> apfst snd x \<Ztypecolon> U \<OTast> W2 \<transforms> wr \<Ztypecolon> W \<OTast> Ru \<with> P2 @tag \<T>\<P>'
\<Longrightarrow> (snd yr, snd wr) \<Ztypecolon> Rt \<^emph> Ru \<transforms> rr \<Ztypecolon> RR @clean
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<OTast> W2 \<transforms> (fst yr, rr) \<Ztypecolon> Y \<OTast> RR \<with> P1 \<and> P2 @tag \<T>\<P>' \<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def \<phi>Prod'_def
  apply (simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric])
  subgoal premises prems
    by (insert prems(1)[THEN transformation_right_frame, where R=\<open>snd wr \<Ztypecolon> Ru\<close>]
               prems(2)[THEN transformation_left_frame, where R=\<open>fst (fst x) \<Ztypecolon> T\<close>]
               prems(3)[THEN transformation_left_frame, where R=\<open>(fst yr \<Ztypecolon> Y)\<close>],
        simp add: mult.assoc[symmetric],
        smt (z3) transformation_trans transformation_weaken) .

lemma [\<phi>reason add]:
  \<open> snd x \<Ztypecolon> Rb \<transforms> Y @clean
\<Longrightarrow> x \<Ztypecolon> \<circle> \<^emph> Rb \<transforms> Y @clean \<close>
  for Rb :: \<open>('c::sep_magma_1, 'b) \<phi>\<close>
  unfolding Action_Tag_def
  by (clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')

lemma [\<phi>reason add]:
  \<open> fst x \<Ztypecolon> Ra \<transforms> Y @clean
\<Longrightarrow> x \<Ztypecolon> Ra \<^emph> \<circle> \<transforms> Y @clean \<close>
  for Ra :: \<open>('c::sep_magma_1, 'b) \<phi>\<close>
  unfolding Action_Tag_def
  by (clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')



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
      (ctxt addsimps @{thms' Sum_Type.sum.case HOL.simp_thms}
            |> fold Simplifier.add_proc [\<^simproc>\<open>NO_MATCH\<close>, \<^simproc>\<open>defined_Ex\<close>, \<^simproc>\<open>HOL.defined_All\<close>,
                         \<^simproc>\<open>defined_all\<close>, \<^simproc>\<open>defined_Collect\<close>, \<^simproc>\<open>Set.defined_All\<close>,
                         \<^simproc>\<open>Set.defined_Bex\<close>, \<^simproc>\<open>unit_eq\<close>, \<^simproc>\<open>case_prod_beta\<close>,
                         \<^simproc>\<open>case_prod_eta\<close>, \<^simproc>\<open>Collect_mem\<close>,
                         Phi_Conv.move_Ex_for_set_notation])
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
      ctxt addsimps @{thms' ExBI_defined}
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
  mult.assoc[where 'a=\<open>'a::sep_semigroup BI\<close>]
  bot_eq_BI_bot

  (*BI connectives*)
  Subjection_Subjection Subjection_Zero Subjection_True Subjection_Flase
  Subjection_times Subjection_addconj

  ExBI_simps ExBI_split_prod ExBI_subj_split_prod

  sep_quant_subjection sep_quant_ExBI

  \<phi>Prod_expn'' \<phi>Prod_expn'
  HOL.if_True HOL.if_False

  \<phi>Bot.unfold \<phi>Any.unfold \<phi>None_itself_is_one

  (*Usual simps*)
  fst_conv snd_conv

lemmas [assertion_simps_source] =
  ExBI_times_left ExBI_times_right ExBI_adconj ExBI_addisj

  REMAINS_def

  sep_quant_sep

lemmas [assertion_simps_target] =
  sep_quant_sep[symmetric]

lemmas [\<phi>programming_base_simps, \<phi>programming_simps, \<phi>safe_simp] =
  add_0_right[where 'a=\<open>'a::sep_magma BI\<close>] add_0_left[where 'a=\<open>'a::sep_magma BI\<close>]
  zero_fun_def[symmetric, where 'b=\<open>'a::sep_magma BI\<close>]
  plus_fun[where 'a=\<open>'a::sep_magma BI\<close>]
  distrib_right[where 'a=\<open>'a::sep_semigroup BI\<close>]
  mult.assoc[where 'a=\<open>'a::sep_semigroup BI\<close>]
  REMAINS_def

lemmas [\<phi>programming_base_simps] =
  mult_zero_right[where 'a=\<open>'a::sep_magma BI\<close>] mult_zero_left[where 'a=\<open>'a::sep_magma BI\<close>]
  mult_1_right[where 'a=\<open>'a::sep_magma_1 BI\<close>] mult_1_left[where 'a=\<open>'a::sep_magma_1 BI\<close>]
  zero_fun

  HOL.simp_thms

  HOL.if_True HOL.if_False


ML_file \<open>library/reasoning/quantifier.ML\<close>

simproc_setup defined_ExBI ( \<open>ExBI A\<close> ) = \<open>K BI_Quantifiers.defined_Ex\<close>

setup \<open>Context.theory_map (Phi_Programming_Simp_Hook.add 100 (fn () => fn ctxt =>
    ctxt delsimps @{thms' ExBI_defined}
         |> fold Simplifier.del_proc [@{simproc defined_ExBI}]))
\<close>

setup \<open>Context.theory_map (
  Assertion_SS_Source.map (fn ctxt =>
    ctxt |> fold Simplifier.add_proc [@{simproc defined_ExBI}] ) #>
  Assertion_SS.map (fn ctxt =>
    ctxt |> fold Simplifier.add_proc [@{simproc Funcomp_Lambda}]) #>
  Phi_Safe_Simps.map (fn ctxt =>
    ctxt |> fold Simplifier.add_proc [@{simproc defined_ExBI}, @{simproc Funcomp_Lambda}]))\<close>


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

ML \<open>
fun conv_transformation_by_assertion_ss ctxt =
  let val src_ctxt = Assertion_SS_Source.enhance (Assertion_SS.equip ctxt)
      val target_ctxt = Assertion_SS_Target.enhance (Assertion_SS.equip ctxt)
   in Phi_Syntax.transformation_conv (Simplifier.rewrite src_ctxt)
                                     (Simplifier.rewrite target_ctxt)
                                     Conv.all_conv
  end

fun skolemize_transformation ctxt th =
  let fun skolem th =
       (case Phi_Syntax.dest_transformation (Thm.major_prem_of th)
          of (Const(\<^const_name>\<open>ExBI\<close>, _) $ _,
              Const(\<^const_name>\<open>\<phi>TagA\<close>, _) $ _ $ (Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _), _) =>
              skolem (@{thm' skolemize_transformation_tR} RS th)
           | (Const(\<^const_name>\<open>ExBI\<close>, _) $ _,
              Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _ , _) =>
              skolem (@{thm' skolemize_transformation_R} RS th)
           | (Const(\<^const_name>\<open>ExBI\<close>, _) $ _, _, _) =>
              skolem (@{thm' skolemize_transformation} RS th)
           | _ => th)
   in th
   |> Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
            conv_transformation_by_assertion_ss ctxt
          ) ctxt) 1
   |> skolem
  end
\<close>


subsection \<open>Transformation-based Simplification\<close>

type_synonym forward_direction = bool (*false for backward*)

consts \<A>simp' :: \<open> forward_direction \<Rightarrow> action \<close>
       \<A>_transitive_simp' :: \<open> forward_direction \<Rightarrow> action\<close>
                  (*rules where simplifications will be applied
                    repeatedly on the simplified results given by the previous step.
                    The annotation exists only in the literal source syntacitcally but once
                    it is added to \<phi>-LPR, will be reduced by a rule pass
                    converting \<open>X \<transforms> Y @tag \<A>_transitive_simp\<close> to
                    \<open>Y \<transforms> Z @tag \<A>simp \<Longrightarrow> X \<transforms> Z @tag \<A>simp\<close>*)
      \<A>try_simp' :: \<open> action \<Rightarrow> bool \<comment> \<open>output: made any substantial change\<close> \<Rightarrow> action \<close>

abbreviation \<open>\<A>simp \<equiv> \<A>simp' True\<close>
abbreviation \<open>\<A>try_simp \<equiv> \<A>try_simp' \<A>simp\<close>
abbreviation \<open>\<A>_transitive_simp \<equiv> \<A>_transitive_simp' True\<close>

abbreviation \<open>\<A>backward_simp \<equiv> \<A>simp' False\<close>
abbreviation \<open>\<A>try_backward_simp \<equiv> \<A>try_simp' \<A>backward_simp\<close>
abbreviation \<open>\<A>_backward_transitive_simp \<equiv> \<A>_transitive_simp' False\<close>

text \<open>Potentially weakening transformations designed for simplifying state sequents of the CoP.

  \<^prop>\<open>x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<subj> y. r y @tag \<A>simp\<close>

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

  Note \<^prop>\<open>A @tag \<A>simp\<close> requires the process to at least make one meaningful reduction
  step that at least simplifies something. Backtracking happens if fails to simplify anything.
  Use \<^term>\<open>\<A>try_simp CHANGED\<close> to try to simplify something or keep it unchanged on failure.
\<close>

subsubsection \<open>Convention\<close>

\<phi>reasoner_group \<phi>simp_all = (100, [1,4000]) for ( \<open>X \<transforms> Y \<with> P @tag \<A>simp' direction\<close> )
      \<open>Simplifying the assertion by means of transformation, which may weaken the assertion and
       refine the abstraction (or backwardly strengthen by \<open>\<A>backward_simp\<close>)\<close>
 and \<phi>simp = (100, [80, 120]) in \<phi>simp_all
      \<open>User rules of transformation-based simplification\<close>
 and \<phi>simp_fallback = (10, [5,20]) in \<phi>simp_all
      \<open>Fallbacks of transformation-based simplification\<close>
 and \<phi>simp_derived = (50, [30,70]) in \<phi>simp_all and > \<phi>simp_fallback and < \<phi>simp
      \<open>Automatically derived transformation-based simplification\<close>
 and \<phi>simp_cut = (1000, [1000, 1030]) in \<phi>simp_all
      \<open>Cutting rules of transformation-based simplification\<close>

declare [[ \<phi>reason_default_pattern
      \<open>?X \<transforms> (y \<Ztypecolon> _ \<subj> y. _) \<with> ?P @tag \<A>simp' True\<close> \<Rightarrow>
      \<open>?X \<transforms> _ \<with> _ @tag \<A>simp' True\<close> (100)
  and \<open>?X \<transforms> (y \<Ztypecolon> _ \<subj> y. _) \<with> ?P @tag \<A>_transitive_simp' True\<close> \<Rightarrow>
      \<open>?X \<transforms> _ \<with> _ @tag \<A>_transitive_simp' True\<close> (100)

  and \<open>_ \<transforms> (y \<Ztypecolon> ?T y \<subj> y. _) \<with> ?P @tag \<A>simp' False\<close> \<Rightarrow>
      \<open>_ \<transforms> (y \<Ztypecolon> ?T y \<subj> y. _) \<with> _ @tag \<A>simp' False\<close> (100)
  and \<open>_ \<transforms> (y \<Ztypecolon> ?T y \<subj> y. _) \<with> ?P @tag \<A>_transitive_simp' False\<close> \<Rightarrow>
      \<open>_ \<transforms> (y \<Ztypecolon> ?T y \<subj> y. _) \<with> _ @tag \<A>_transitive_simp' False\<close> (100)

  and \<open>?X @tag \<A>simp' ?direction\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Bad form: \<close> (?X @tag \<A>simp' ?direction) \<newline>
                  \<open>Expect: \<open>_ \<transforms> (y \<Ztypecolon> ?Y \<subj> y. ?r y) @tag \<A>simp\<close>\<close>)\<close> (0)
  and \<open>?X @tag \<A>_transitive_simp' ?direction\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Bad form: \<close> (?X @tag \<A>_transitive_simp' ?direction) \<newline>
                  \<open>Expect: \<open>_ \<transforms> (y \<Ztypecolon> ?Y \<subj> y. ?r y) @tag \<A>simp\<close>\<close>)\<close> (0)
  and \<open>?X @tag \<A>try_simp' ?direction ?changed\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Bad rule, \<A>try_simp' is preserved for internal use only.\<close> \<newline>
                  (?X @tag \<A>try_simp' ?direction ?changed))\<close> (0)
]]

lemma [\<phi>reason %\<phi>simp_cut+1 for \<open>_ \<transforms> (y \<Ztypecolon> _ \<subj> y. _) @tag \<A>try_simp' _ _\<close>]:
  \<open> \<guard> X \<transforms> (y \<Ztypecolon> U \<subj> y. R y) @tag A
\<Longrightarrow> X \<transforms> (y \<Ztypecolon> U \<subj> y. R y) @tag \<A>try_simp' A True \<close>
  unfolding Action_Tag_def \<r>Guard_def .

lemma [\<phi>reason %\<phi>simp_cut for \<open>_ \<transforms> (y \<Ztypecolon> _ \<subj> y. _) @tag \<A>try_simp' _ _\<close>]:
  \<open> x \<Ztypecolon> T \<transforms> (y \<Ztypecolon> T \<subj> y. y = x) @tag \<A>try_simp' A False \<close>
  unfolding Action_Tag_def \<r>Guard_def
  by simp


subsubsection \<open>Implementation\<close>

consts \<A>simp_if_need :: \<open>forward_direction \<Rightarrow> action\<close>
       \<A>exhausitive_simp :: \<open> forward_direction
                            \<Rightarrow> bool \<comment> \<open>input: set this to False to disable the simp\<close>
                            \<Rightarrow> action\<close>
       \<A>_apply_simplication :: \<open>action\<close>

lemma [\<phi>reason %cutting for \<open>_ \<transforms> _ \<with> _ @tag \<A>_apply_simplication\<close>]:
  \<open> X \<transforms> Y' \<with> Any @tag \<A>_map_each_item (\<A>exhausitive_simp True True)
\<Longrightarrow> \<simplify>[assertion_simps SOURCE] Y : Y'
\<Longrightarrow> X \<transforms> Y @tag \<A>_apply_simplication \<close>
  unfolding Action_Tag_def Transformation_def Simplify_def
  by simp

lemma \<A>simp_invoke:
  \<open> X \<transforms> Y \<with> Any @tag \<A>_map_each_item (\<A>exhausitive_simp True True)
\<Longrightarrow> X \<transforms> Y \<close>
  unfolding Action_Tag_def
  by (simp add: transformation_weaken)

ML_file \<open>library/tools/CoP_simp.ML\<close>

context begin

private lemma \<A>simp_chk_no_need:
  \<open> X \<transforms> X @tag \<A>simp_if_need direction\<close>
  unfolding Action_Tag_def
  by simp

private lemma \<A>simp_chk_no_need':
  \<open> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> T \<subj> y. y = x @tag \<A>simp_if_need direction\<close>
  unfolding Action_Tag_def
  by (simp add: ExBI_defined)

private lemma \<A>simp_chk_go:
  \<open> X \<transforms> Y @tag \<A>try_simp' (\<A>simp' direction) ANY
\<Longrightarrow> X \<transforms> Y @tag \<A>simp_if_need direction\<close>
  unfolding Action_Tag_def .

private lemma \<A>simp_chk_go_transitive:
  \<open> X \<transforms> y \<Ztypecolon> U \<subj> y. r y @tag \<A>try_simp' (\<A>simp' True) CHANGED
\<Longrightarrow> \<forall>y. \<condition> r y \<longrightarrow> (y \<Ztypecolon> U \<transforms> z \<Ztypecolon> Z \<subj> z. w y z @tag \<A>exhausitive_simp True CHANGED)
\<Longrightarrow> \<simplify>[\<safe>] r' : (\<lambda>z. \<exists>y. r y \<and> w y z)
\<Longrightarrow> X \<transforms> z \<Ztypecolon> Z \<subj> z. r' z @tag \<A>exhausitive_simp True ANY\<close>
  unfolding Action_Tag_def Transformation_def Premise_def Simplify_def
  by clarsimp blast

private lemma \<A>simp_chk_go_transitive_backward:
  \<open> (\<And>y. \<condition> w y \<Longrightarrow> y \<Ztypecolon> U \<transforms> z \<Ztypecolon> Z \<subj> z. r y z @tag \<A>try_simp' (\<A>simp' False) CHANGED)
\<Longrightarrow> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<subj> y. w y @tag \<A>exhausitive_simp False CHANGED
\<Longrightarrow> \<simplify>[\<safe>] r' : (\<lambda>z. \<exists>y. w y \<and> r y z)
\<Longrightarrow> x \<Ztypecolon> T \<transforms> z \<Ztypecolon> Z \<subj> z. r' z @tag \<A>exhausitive_simp False ANY\<close>
  unfolding Action_Tag_def Transformation_def Premise_def Simplify_def
  by clarsimp blast

private lemma \<A>simp_chk_no_need_transitive:
  \<open> X \<transforms> X @tag \<A>exhausitive_simp direction ANY\<close>
  unfolding Action_Tag_def
  by simp

private lemma \<A>simp_chk_no_need'_transitive:
  \<open> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> T \<subj> y. y = x @tag \<A>exhausitive_simp direction ANY\<close>
  unfolding Action_Tag_def
  by (simp add: ExBI_defined)

\<phi>reasoner_ML \<A>simp_if_need %cutting (\<open>_ \<transforms> _ \<with> _ @tag \<A>simp_if_need _\<close>) = \<open>
fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, goal) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
      val (ToA, Const _ $ direction_term) = PLPR_Syntax.dest_action_of' (K true) goal
      val (X, Y', _) = Phi_Syntax.dest_transformation ToA
      val direction = case direction_term of Const(\<^const_name>\<open>True\<close>, _) => true
                                           | Const(\<^const_name>\<open>False\<close>, _) => false
                                           | _ => raise TERM ("The direction of \<A>simp_if_need must be a literal", [direction_term])
      val (Y, ex_bound) =
            case Y' of Const(\<^const_name>\<open>ExBI\<close>, _) $ Abs (N, Ty,
                          Const(\<^const_name>\<open>Subjection\<close>, _) $ (Y as Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ Bound 0 $ _) $ _)
                         => (Y, SOME (N,Ty))
                     | _ => (Y', NONE)
   in if (if direction then Phi_CoP_Simp.is_simp_needed (Context.Proof ctxt) bvs X
                       else Phi_CoP_Backward_Simp.is_simp_needed (Context.Proof ctxt) (the_list ex_bound @ bvs) Y)
   then SOME ((ctxt, @{thm' \<A>simp_chk_go} RS' (ctxt, sequent)), Seq.empty)
   else let val rule = if is_some ex_bound then @{thm' \<A>simp_chk_no_need'}
                                           else @{thm' \<A>simp_chk_no_need}
    in SOME ((ctxt, rule RS' (ctxt, sequent)), Seq.empty)
   end
  end)
\<close>

\<phi>reasoner_ML \<A>exhausitive_simp %cutting (\<open>_ \<transforms> _ \<with> _ @tag \<A>exhausitive_simp _ _\<close>) = \<open>
let val norm_tail = @{lemma' \<open>
        x \<Ztypecolon> T \<transforms> z \<Ztypecolon> Z \<subj> z. r z @tag A
    \<Longrightarrow> \<simplify>[assertion_simps SOURCE] Z' : z \<Ztypecolon> Z \<subj> z. r z
    \<Longrightarrow> x \<Ztypecolon> T \<transforms> Z' @tag A\<close>
        by (simp add: Action_Tag_def Simplify_def)}

 in fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, goal) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
      val (ToA, Const _ (*\<A>exhausitive_simp*)
                  $ direction_term
                  $ IS_NEEDED
          ) = PLPR_Syntax.dest_action_of' (K true) goal
      val (X, Y', _) = Phi_Syntax.dest_transformation ToA
      val direction = case direction_term of Const(\<^const_name>\<open>True\<close>, _) => true
                                           | Const(\<^const_name>\<open>False\<close>, _) => false
                                           | _ => raise TERM ("The direction of \<A>simp_if_need must be a literal", [direction_term])
      val (Y, ex_bound) =
            case Y' of Const(\<^const_name>\<open>ExBI\<close>, _) $ Abs (N, Ty,
                          Const(\<^const_name>\<open>Subjection\<close>, _) $ (Y as Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ Bound 0 $ _) $ _)
                         => (Y, SOME (N, Ty))
                     | _ => (Y', NONE)
      val is_needed =
          IS_NEEDED <> \<^Const>\<open>False\<close> andalso
         (if direction then Phi_CoP_Simp.is_simp_needed (Context.Proof ctxt) bvs X
                       else Phi_CoP_Backward_Simp.is_simp_needed (Context.Proof ctxt) (the_list ex_bound @ bvs) Y)
   in if is_needed
   then let val sequent' = if is_some ex_bound
                           then sequent
                           else norm_tail RS sequent
     in SOME ((ctxt, (if direction then @{thm' \<A>simp_chk_go_transitive}
                                   else @{thm' \<A>simp_chk_go_transitive_backward})
                      RS' (ctxt, sequent)), Seq.empty)
    end
   else let val rule = if is_some ex_bound then @{thm' \<A>simp_chk_no_need'_transitive}
                                           else @{thm' \<A>simp_chk_no_need_transitive}
    in SOME ((ctxt, rule RS' (ctxt, sequent)), Seq.empty)
   end
  end)
end
\<close>

end

paragraph \<open>Invoking CoP-simp in ToA reasoning\<close>

ML \<open>

val normalize_source = @{lemma
  \<open> X \<transforms> X' @tag \<A>_map_each_item (\<A>exhausitive_simp True True)
\<Longrightarrow> X' \<transforms> Y \<with> P
\<Longrightarrow> X \<transforms> Y \<with> P \<close>
  by (clarsimp simp: Action_Tag_def Transformation_def, blast)
}

fun normalize_source_of_ToA (ctxt, sequent) =
  let val (bvs, ToA) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
      val (X, _, _) = Phi_Syntax.dest_transformation ToA
   in if Phi_Syntax.exists_item_of_assertion (Phi_CoP_Simp.is_simp_needed (Context.Proof ctxt)) bvs X
      then (
        Phi_Reasoner.info_print ctxt 2 (K "normalizing the source assertion of the transformation") ;
        case Phi_Reasoner.internal_reason NONE (SOME 1) (ctxt, normalize_source RS sequent)
          of NONE => (ctxt, sequent)
           | SOME (ctxt', sequent') => 
                (ctxt', Conv.gconv_rule (Phi_Conv.hhf_concl_conv (conv_transformation_by_assertion_ss) ctxt') 1 sequent'))
      else (ctxt, sequent)
  end

fun normalize_target_of_ToA parse (ctxt, sequent) =
  let val (bvs, ToA) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
      val (Y, rule) = parse (Phi_Syntax.dest_transformation ToA)
                      (* of (_, Const(\<^const_name>\<open>REMAINS\<close>, _) $ Y $ _, _) => (Y, true)
                          | (_, Y, _) => (Y, false) *)
   in if Phi_CoP_Backward_Simp.is_simp_needed (Context.Proof ctxt) bvs Y
      then (
        Phi_Reasoner.info_print ctxt 2 (K "normalizing the target assertion of the transformation") ;
        case Phi_Reasoner.internal_reason NONE (SOME 1) (ctxt, rule RS sequent)
          of NONE => (ctxt, sequent)
           | SOME ret => ret)
      else (ctxt, sequent)
  end

fun chk_target_of_ToA_requires_normalization parse_term (ctxt, sequent) =
  let val (bvs, ToA) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
      val target = parse_term (#2 (Phi_Syntax.dest_transformation ToA))
   in Phi_CoP_Backward_Simp.is_simp_needed (Context.Proof ctxt) bvs target orelse
      (case target
         of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T =>
              let val head = Term.head_of x
               in not (is_Var head) orelse exists_subterm (fn y => y aconv head) T
              end
          | _ => false)
  end
\<close>



subsubsection \<open>Simplification Protect\<close>

definition [simplification_protect]:
  \<open>\<phi>TBS_Simp_Protect X U r direction \<equiv> X \<transforms> y \<Ztypecolon> U \<subj> y. r y @tag \<A>simp' direction\<close>

lemma [cong]:
  \<open> X \<equiv> X'
\<Longrightarrow> U \<equiv> U'
\<Longrightarrow> r \<equiv> r'
\<Longrightarrow> \<phi>TBS_Simp_Protect X U r direction \<equiv> \<phi>TBS_Simp_Protect X' U' r' direction \<close>
  by simp

subsubsection \<open>Extracting Pure\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC P A
\<Longrightarrow> \<r>ESC P (A @tag \<A>simp' direction) \<close>
  unfolding Action_Tag_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF A P
\<Longrightarrow> \<r>EIF (A @tag \<A>simp' direction) P \<close>
  unfolding Action_Tag_def
  by blast


subsection \<open>Falling Lattice of Transformation Sub-procedures\<close>

subsubsection \<open>From \<open>\<T>\<P>'\<close> to \<open>\<T>\<P>\<close>\<close>

lemma [\<phi>reason default %ToA_falling_latice+3]:
  \<open> \<guard> fst x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<with> P @tag \<T>\<P>
\<Longrightarrow> May_Assign (snd x) unspec
\<Longrightarrow> x \<Ztypecolon> T \<OTast> \<circle> \<transforms> (y, unspec) \<Ztypecolon> U \<OTast> \<circle> \<with> P @tag \<T>\<P>' \<close>
  unfolding \<r>Guard_def Action_Tag_def \<phi>Prod'_def Transformation_def
  by simp

(*TODO: optimize!*)
lemma [\<phi>reason default %ToA_falling_latice+2]:
  \<open> x \<Ztypecolon> X \<OTast> Y \<transforms> prod.swap x \<Ztypecolon> Y \<OTast> X @tag \<T>\<P>' \<close>
  for X :: \<open>('a::sep_algebra,'b) \<phi>\<close>
  unfolding Action_Tag_def \<phi>Prod'_def \<phi>Prod_def \<phi>Type_def Transformation_def
  by (cases x; simp add: mult.commute)

lemma [\<phi>reason default %ToA_falling_latice+1]:
  \<open> \<guard> Push_Envir_Var prove_obligations_in_time True \<and>\<^sub>\<r>
         Identity_Element\<^sub>I (fst x \<Ztypecolon> T) P \<and>\<^sub>\<r>
         Pop_Envir_Var prove_obligations_in_time
\<Longrightarrow> x \<Ztypecolon> T \<OTast> U \<transforms> (snd x, unspec) \<Ztypecolon> U \<OTast> \<circle> \<with> P @tag \<T>\<P>'\<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  \<comment> \<open>the transformation from T to U fails, and the algebra is non-commutative, nor any methods of a higher priority,
      so \<open>T\<close> or \<open>U\<close> can only be identity if the reasoning can continue\<close>
  unfolding \<r>Guard_def Ant_Seq_def Identity_Element\<^sub>I_def Transformation_def Action_Tag_def \<phi>Prod'_def
  by (clarsimp; fastforce)

lemma [\<phi>reason default %ToA_falling_latice]:
  \<open> Identity_Element\<^sub>E (one \<Ztypecolon> U)
\<Longrightarrow> x \<Ztypecolon> T \<OTast> \<circle> \<transforms> (one, fst x) \<Ztypecolon> U \<OTast> T @tag \<T>\<P>'\<close>
  for T :: \<open>('c::sep_magma_1, 'x) \<phi>\<close>
  unfolding \<r>Guard_def Ant_Seq_def Identity_Element\<^sub>E_def Transformation_def Premise_def Action_Tag_def \<phi>Prod'_def
  by (clarsimp; force)


subsubsection \<open>From \<open>\<T>\<P>\<close> to \<open>\<T>\<P>'\<close>\<close>

lemma [\<phi>reason default %ToA_falling_latice+3]:
  \<open> (x, w) \<Ztypecolon> T \<OTast> W \<transforms> yr \<Ztypecolon> U \<OTast> R \<with> P @tag \<T>\<P>'
\<Longrightarrow> Identity_Element\<^sub>E (w \<Ztypecolon> W)
\<Longrightarrow> snd yr \<Ztypecolon> R \<transforms> RR @clean
\<Longrightarrow> x \<Ztypecolon> T \<transforms> fst yr \<Ztypecolon> U \<remains> RR \<with> P @tag \<T>\<P> \<close>
  unfolding Premise_def Identity_Element\<^sub>E_def Try_def Action_Tag_def \<phi>Prod'_def REMAINS_def
  by (clarsimp simp add: \<phi>Some_transformation_strip \<phi>Prod_expn'' \<phi>Prod_expn',
      smt (z3) BI_eq_ToA mult_1_class.mult_1_right transformation_left_frame transformation_trans)

lemma [\<phi>reason default %ToA_falling_latice+3]:
  \<open> (x,w) \<Ztypecolon> T \<OTast> W \<transforms> y \<Ztypecolon> U \<OTast> R \<with> P1 @tag \<T>\<P>'
\<Longrightarrow> \<simplify>[\<safe>] y' : y
\<Longrightarrow> \<simplify>[\<safe>] y\<^sub>1 : fst y'
\<Longrightarrow> \<simplify>[\<safe>] r  : snd y'
\<Longrightarrow> A \<transforms> w \<Ztypecolon> W \<remains> RR \<with> P2 @tag \<T>\<P>
\<Longrightarrow> (r \<Ztypecolon> R) * RR \<transforms> RRR @clean
\<Longrightarrow> (x \<Ztypecolon> T) * A \<transforms> y\<^sub>1 \<Ztypecolon> U \<remains> RRR \<with> P2 \<and> P1 @tag \<T>\<P> \<close>
  for A :: \<open>'a::sep_monoid BI\<close>
  unfolding Action_Tag_def Simplify_def Action_Tag_def \<phi>Prod'_def REMAINS_def
  apply (clarsimp simp: \<phi>Some_\<phi>Prod \<phi>Some_transformation_strip \<phi>Prod_expn' \<phi>Prod_expn'' mult.assoc[symmetric])
  subgoal premises prems
  by (insert prems(1)[THEN transformation_right_frame, where R=\<open>RR\<close>]
            prems(5)[THEN transformation_left_frame, where R=\<open>x \<Ztypecolon> T\<close>]
            prems(6)[THEN transformation_left_frame, where R=\<open>fst y \<Ztypecolon> U\<close>],
      smt (z3) mult.assoc transformation_trans) .

lemma [\<phi>reason default %ToA_falling_latice+3]:
  \<open> (x, w) \<Ztypecolon> T \<OTast> W \<transforms> y \<Ztypecolon> U \<OTast> R \<with> P1 @tag \<T>\<P>'
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
\<Longrightarrow> A \<transforms> w \<Ztypecolon> W \<with> P2 @tag \<T>\<P>
\<Longrightarrow> (x \<Ztypecolon> T) * A \<transforms> fst y \<Ztypecolon> U \<with> P2 \<and> Q \<and> P1 @tag \<T>\<P> \<close>
  for A :: \<open>'a :: sep_magma_1 BI\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def Premise_def
            Transformation_def Try_def Ant_Seq_def \<phi>Prod'_def
  by (clarsimp; fastforce)

(*
lemma (*ToA_splitting_source_no_remainder_first*)
      [no_atp, \<phi>reason %ToA_falling_latice+2 except \<open>_ \<transforms> (_ :: ?'a :: sep_semigroup BI) \<with> _ @tag \<T>\<P>\<close>]:
  " R = 1 \<and>\<^sub>\<r> (A * B \<transforms> Y \<with> P @tag \<T>\<P>) \<or>\<^sub>c\<^sub>u\<^sub>t
    P = (P1 \<and> P2) \<and>\<^sub>\<r> (A \<transforms> Y \<with> P1 @tag \<T>\<P>) \<and>\<^sub>\<r>
    (\<condition> P1 \<longrightarrow> (B \<transforms> R \<with> P2 @tag \<T>\<P>))
\<Longrightarrow> A * B \<transforms> Y \<remains> R \<with> P @tag \<T>\<P>"
  unfolding Orelse_shortcut_def Transformation_def REMAINS_def Premise_def Ant_Seq_def Action_Tag_def
  by clarsimp (metis One_expn mult_1_class.mult_1_right sep_magma_1_left)
*)

lemma [\<phi>reason default %ToA_falling_latice+2]: \<comment> \<open>when X fails to match \<open>x \<Ztypecolon> T\<close>\<close>
  \<open> R \<transforms> Y \<remains> R' \<with> P @tag \<T>\<P>
\<Longrightarrow> X * R \<transforms> Y \<remains> X * R' \<with> P @tag \<T>\<P> \<close>
  for Y :: \<open>'c::sep_algebra BI\<close>
  unfolding Action_Tag_def REMAINS_def
  by (simp add: mult.left_commute transformation_left_frame)

lemma [\<phi>reason default %ToA_falling_latice+1]: \<comment> \<open>when X fails to match \<open>x \<Ztypecolon> T\<close>, nor a abelian semigroup\<close>
  \<open> Identity_Element\<^sub>E (var_y \<Ztypecolon> U)
\<Longrightarrow> X \<transforms> var_y \<Ztypecolon> U \<remains> X @tag \<T>\<P> \<close>
  for X :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Transformation_def Identity_Element\<^sub>E_def Action_Tag_def
  by (clarsimp, force)

subsubsection \<open>For Non-Unital Algeras\<close>

lemma closed_homo_sep_Some:
  \<open> closed_homo_sep Some \<close>
  unfolding closed_homo_sep_def closed_homo_sep_disj_def homo_sep_def homo_sep_mult_def homo_sep_disj_def
  by simp

lemma [\<phi>reason default %ToA_falling_latice
               for \<open>_ \<transforms> _ * _ \<with> _ @tag \<T>\<P>\<close>
                   \<open>_ * _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
               except \<open>(_ :: ?'a::sep_magma_1 BI) \<transforms> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open> \<simplify>[assertion_simps SOURCE] X' : \<Psi>[Some] X
\<Longrightarrow> \<simplify>[assertion_simps TARGET] Y' : \<Psi>[Some] Y
\<Longrightarrow> X' \<transforms> Y' \<with> P @tag \<T>\<P>
\<Longrightarrow> X \<transforms> Y \<with> P @tag \<T>\<P> \<close>
  unfolding Transformation_def Action_Tag_def Simplify_def
  by auto

lemma [assertion_simps]:
  \<open> \<Psi>[Some] (x \<Ztypecolon> T) = (x \<Ztypecolon> \<black_circle> T) \<close>
  unfolding BI_eq_iff
  by (auto simp: split_option_all)

lemma [assertion_simps]:
  \<open>\<Psi>[Some] (X * Y) = \<Psi>[Some] X * \<Psi>[Some] Y\<close>
  for X :: \<open>'c::sep_magma BI\<close>
  by (simp add: \<Psi>_Multiplicative_Conj[OF closed_homo_sep_Some])

lemma [assertion_simps]:
  \<open> \<Psi>[Some] (A \<subj> P) = (\<Psi>[Some] A \<subj> P) \<close>
  unfolding BI_eq_iff
  by simp blast

lemma [assertion_simps]:
  \<open> \<Psi>[Some] (\<exists>*x. A x) = (\<exists>*x. \<Psi>[Some] (A x)) \<close>
  unfolding BI_eq_iff
  by simp blast

lemma [assertion_simps]:
  \<open> \<Psi>[Some] (A + B) = \<Psi>[Some] A + \<Psi>[Some] B \<close>
  unfolding BI_eq_iff
  by simp blast

lemma [assertion_simps]:
  \<open> \<Psi>[Some] (A \<sqinter> B) = \<Psi>[Some] A \<sqinter> \<Psi>[Some] B \<close>
  unfolding BI_eq_iff
  by simp blast



subsection \<open>Essential Reasoning Procedures\<close>

subsubsection \<open>Reflexive Transformation\<close>

paragraph \<open>When the target and the source are either alpha-equivalent or unified\<close>

text \<open>Applying reflexive transformation on alpha-equivalent couples of source and target is safe,
so be applied of high priority.
In contrast, unification by reflexive transformation is aggressive. Therefore, they are applied
only when no other rules are applicable.\<close>

declare transformation_refl [\<phi>reason %ToA_refl for \<open>?A \<transforms> ?A \<with> _ @tag \<T>\<P>\<close>
                                                   \<open>_ \<Ztypecolon> ?T \<transforms> ?var_y \<Ztypecolon> ?T \<with> _ @tag \<T>\<P>\<close>,
                             \<phi>reason %ToA_unified_refl for \<open>_ \<Ztypecolon> ?T \<transforms> ?var_y \<Ztypecolon> ?U \<with> _ @tag \<T>\<P>\<close>]

lemma [\<phi>reason default %ToA_unified_refl for \<open>?A \<transforms> ?A' \<with> _ @tag \<T>\<P>\<close>]:
  \<open> A \<transforms> A \<close>
  unfolding Premise_def \<r>Guard_def Action_Tag_def
  by simp

lemma [\<phi>reason %ToA_refl for \<open>?A * _ \<transforms> (?A :: ?'c::sep_magma_1 BI) \<with> _ @tag \<T>\<P>\<close>,
       \<phi>reason default %ToA_unified_refl for \<open>?A * _ \<transforms> (?A' :: ?'c::sep_magma_1 BI) \<with> _ @tag \<T>\<P>\<close>]:
  \<open> Identity_Element\<^sub>I R P
\<Longrightarrow> A * R \<transforms> A \<with> P \<close>
  for A :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Action_Tag_def
  by clarsimp fastforce

lemma transformation_refl_assigning_remainder [
          \<phi>reason %ToA_assigning_var for \<open>?A * _ \<transforms> ?A \<remains> _ \<with> _ @tag \<T>\<P> \<close>
                                         \<open>(_ \<Ztypecolon> ?T) * _ \<transforms> ?var_y \<Ztypecolon> ?T \<remains> _ \<with> _ @tag \<T>\<P> \<close>,
          \<phi>reason default %ToA_unified_refl for \<open>_ * _ \<transforms> _ \<remains> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open>A * R \<transforms> A \<remains> R\<close>
  unfolding REMAINS_def Action_Tag_def
  by simp

lemma transformation_refl_with_remainder [
        \<phi>reason %ToA_assigning_var for \<open>?A \<transforms> ?A \<remains> _ \<with> _ @tag \<T>\<P>\<close>
                                       \<open>_ \<Ztypecolon> ?T \<transforms> ?var_y \<Ztypecolon> ?T \<remains> _ \<with> _ @tag \<T>\<P>\<close>,
        \<phi>reason default %ToA_unified_refl for \<open>_ \<transforms> _ \<remains> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open>A \<transforms> A \<remains> 1\<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def REMAINS_def
  by simp

lemma transformation_refl_assigning_W [
        \<phi>reason %ToA_assigning_var,
        \<phi>reason default %ToA_unified_refl for \<open>_ \<Ztypecolon> _ \<OTast> _ \<transforms> _ \<Ztypecolon> (_ \<^emph> _) \<OTast> _ \<with> _ @tag \<T>\<P>'\<close> ]:
  \<open> x \<Ztypecolon> T \<OTast> U \<transforms> (x, unspec) \<Ztypecolon> (T \<^emph> U) \<OTast> \<circle> \<close>
  unfolding Action_Tag_def \<phi>Prod'_def \<phi>Prod_expn'
  by simp

lemma transformation_refl_assigning_R [
        \<phi>reason %ToA_assigning_var,
        \<phi>reason default %ToA_unified_refl for \<open>_ \<Ztypecolon> (_ \<^emph> _) \<OTast> _ \<transforms> _ \<Ztypecolon> _ \<OTast> _ \<with> _ @tag \<T>\<P>'\<close> ]:
  \<open> May_Assign (snd x) unspec
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<OTast> \<circle> \<transforms> fst x \<Ztypecolon> T \<OTast> U \<close>
  unfolding Action_Tag_def \<phi>Prod'_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma transformation_refl_with_WR [
        \<phi>reason %ToA_assigning_var+1,
        \<phi>reason default %ToA_unified_refl+1 for \<open>_ \<Ztypecolon> _ \<OTast> _ \<transforms> _ \<Ztypecolon> _ \<OTast> _ \<with> _ @tag \<T>\<P>'\<close> ]:
        \<comment> \<open>Higher than \<open>transformation_refl\<close> to set the condition variable Cr\<close>
  \<open> May_Assign (snd x) unspec
\<Longrightarrow> x \<Ztypecolon> T \<OTast> \<circle> \<transforms> x \<Ztypecolon> T \<OTast> \<circle> \<close>
  unfolding Action_Tag_def
  by simp

lemma ToA_refls_by_T_eq:
  \<open> T = T'
\<Longrightarrow> May_Assign (snd x\<^sub>2) unspec
\<Longrightarrow> x\<^sub>2 \<Ztypecolon> T \<OTast> \<circle> \<transforms> x\<^sub>2 \<Ztypecolon> T' \<OTast> \<circle> \<close>
  \<open> T = T'
\<Longrightarrow> (x \<Ztypecolon> T) * R \<transforms> x \<Ztypecolon> T' \<remains> R \<close>
  \<open> T = T'
\<Longrightarrow> x \<Ztypecolon> T \<transforms> x \<Ztypecolon> T' \<close>
  unfolding \<phi>Prod'_def REMAINS_def
  by simp_all


paragraph \<open>When the target is a schematic variable\<close>

text \<open>Schematic variables occurring in source are assigned with zeros, and is
  covered by \<section>\<open>Phi_BI/Bottom/Transformation_Rules\<close>\<close>

ML \<open>
(* (\<And>x. X x \<transforms> ?Y \<with> P) where ?Y is a variable.
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
      val (argTys, \<^Type>\<open>BI \<open>TY\<close>\<close>) = Term.strip_type (snd V)
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
      val Y'2 = fold_rev (fn j => fn TM =>
                  let val (name,T) = List.nth (vs, N-1-j)
                   in \<^Const>\<open>ExBI \<open>T\<close> \<open>TY\<close>\<close> $ Abs (name, T, TM)
                  end) bads Y'1
      val Y'3 = fold_rev (fn (_, Bound j) => (fn TM =>
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

\<phi>reasoner_ML transformation_refl_var %ToA_assigning_var (\<open>_ \<transforms> ?var_Y \<with> _ @tag \<T>\<P>\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm' transformation_refl[THEN Action_Tag_I[where A=\<T>\<P>]]},
          SOME @{thm' ExBI_transformation_I[THEN Action_Tag_I[where A=\<T>\<P>], OF Action_Tag_D[where A=\<T>\<P>]]},
          I, I
      ) ctxt thm) \<close>

\<phi>reasoner_ML transformation_refl_var_R %ToA_assigning_var (\<open>_ * _ \<transforms> ?var_Y \<remains> _ \<with> _ @tag \<T>\<P>\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (apply_refl_by_unifying (
          @{thm' transformation_refl_assigning_remainder[THEN Action_Tag_I[where A=\<T>\<P>]]},
          SOME @{thm' ExBI_transformation_I_R[THEN Action_Tag_I[where A=\<T>\<P>], OF Action_Tag_D[where A=\<T>\<P>]]},
          (fn _ $ A $ R => A), (fn _ (*REMAINS*) $ A $ _ => A)
      ) ctxt thm) \<close>

text \<open>Here, we assign the semantics of schematic variables occurring in targets and sources to be,
  a wild-card for any single separation item.\<close>

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

subsubsection \<open>Varify Target Object\<close>

lemma [\<phi>reason default %ToA_varify_target_object for \<open>_ \<transforms> _ \<Ztypecolon> _ \<with> _ @tag \<T>\<P>\<close>
                                              except \<open>_ \<transforms> ?var_y' \<Ztypecolon> _ \<with> _ @tag \<T>\<P>\<close> ]:
  \<open> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<subj> y. r y @tag \<A>exhausitive_simp False True
\<Longrightarrow> Object_Equiv U eq
\<Longrightarrow> \<simplify> P : (\<forall>y'. r y' \<longrightarrow> eq y' y)
\<Longrightarrow> X \<transforms> x \<Ztypecolon> T \<with> Q @tag \<T>\<P>
\<Longrightarrow> \<premise> P
\<Longrightarrow> X \<transforms> y \<Ztypecolon> U \<with> Q @tag \<T>\<P> \<close>
  unfolding Action_Tag_def Transformation_def Premise_def Object_Equiv_def Simplify_def
  by clarsimp metis

lemma [\<phi>reason default %ToA_varify_target_object for \<open>_ \<transforms> _ \<Ztypecolon> _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>
                                              except \<open>_ \<transforms> ?var_y' \<Ztypecolon> _ \<remains> _ \<with> _  @tag \<T>\<P>\<close>]:
  \<open> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<subj> y. r y @tag \<A>exhausitive_simp False True
\<Longrightarrow> Object_Equiv U eq
\<Longrightarrow> \<simplify> P : (\<forall>y'. r y' \<longrightarrow> eq y' y)
\<Longrightarrow> X \<transforms> x \<Ztypecolon> T \<remains> R \<with> Q @tag \<T>\<P>
\<Longrightarrow> \<premise> P
\<Longrightarrow> X \<transforms> y \<Ztypecolon> U \<remains> R \<with> Q @tag \<T>\<P>\<close>
  unfolding Action_Tag_def Transformation_def Premise_def Object_Equiv_def Simplify_def
  by (clarsimp; metis)


subsubsection \<open>Basic Transformation Rules\<close>

paragraph \<open>Plainize\<close>

lemma [\<phi>reason %ToA_normalizing]:
  " T1 * (T2 * R) \<transforms> X \<with> P
\<Longrightarrow> (T1 * T2) * R \<transforms> X \<with> P"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding mult.assoc .

lemma [\<phi>reason %ToA_normalizing]:
  " T \<transforms> X1 * (X2 * R) \<with> P
\<Longrightarrow> T \<transforms> (X1 * X2) * R \<with> P"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding mult.assoc .

lemma [\<phi>reason %ToA_normalizing]:
  " T \<transforms> X1 * (X2 * X3) \<remains> R \<with> P
\<Longrightarrow> T \<transforms> (X1 * X2) * X3 \<remains> R \<with> P "
  for R :: \<open>'a::sep_monoid BI\<close>
  unfolding mult.assoc .


lemma [\<phi>reason %ToA_splitting_target]:
  " A \<transforms> X \<remains> R \<with> P1 @tag \<T>\<P>
\<Longrightarrow> \<condition> P1 \<longrightarrow> (R \<transforms> Y \<with> P2 @tag \<T>\<P>)
\<Longrightarrow> A \<transforms> X * Y \<with> P1 \<and> P2 @tag \<T>\<P>"
  unfolding Action_Tag_def REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def
  by (clarsimp; force)


lemma [\<phi>reason %ToA_splitting_target]:
  " A \<transforms> X \<remains> R1 \<with> P1 @tag \<T>\<P>
\<Longrightarrow> \<condition> P1 \<longrightarrow> (R1 \<transforms> Y \<remains> R' \<with> P2 @tag \<T>\<P>)
\<Longrightarrow> \<r>Assoc_Mul X Y R'
\<Longrightarrow> A \<transforms> X * Y \<remains> R' \<with> P1 \<and> P2 @tag \<T>\<P> "
  unfolding Action_Tag_def REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def \<r>Assoc_Mul_def
  by (clarsimp, meson)



subsubsection \<open>Entry Point of Transformation Reasoning\<close>

setup \<open>Config.put_global (Phi_Syntax.enable_auto_chk_and_conv) false\<close>

paragraph \<open>Major Implementation\<close>

subparagraph \<open>Short-cuts\<close>

lemma [\<phi>reason %ToA_refl for \<open>?X \<transforms> ?X \<with> ?P\<close>
                             \<open>?X \<transforms> ?var \<with> ?P\<close>]:
  \<open>X \<transforms> X\<close>
  unfolding Action_Tag_def using transformation_refl .

lemma [\<phi>reason %ToA_red for \<open>?X \<transforms> ?Y \<subj> True \<with> ?P\<close>]:
  \<open> X \<transforms> Y \<with> P
\<Longrightarrow> X \<transforms> Y \<subj> True \<with> P \<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason %ToA_normalizing for \<open>?X \<transforms> ?Y\<close>]:
  \<open> X \<transforms> Y \<with> Any
\<Longrightarrow> X \<transforms> Y \<close>
  unfolding Action_Tag_def
  by (simp add: transformation_weaken)

subparagraph \<open>ML\<close>

ML \<open>
val augment_ToA_by_implication = Attrib.setup_config_bool \<^binding>\<open>augment_ToA_by_implication\<close> (K false)
val under_NToA_ctxt = Config.declare_bool ("under_NToA_ctxt", \<^here>) (K false)

structure ToA_Hooks = Hooks (
  type arg = {deep: bool}
  type state = context_state
)

val NToA_init_having_Q = @{lemma
  \<open> X \<implies> Q
\<Longrightarrow> \<condition> Q \<longrightarrow> (X \<transforms> Y \<with> P @tag \<T>\<P>)
\<Longrightarrow> X \<transforms> Y \<with> P @tag \<T>\<P>\<close>
  by (clarsimp simp: \<r>EIF_def Simplify_def Identity_Element\<^sub>I_def Satisfiable_def Premise_def
                     Action_Tag_def Transformation_def, blast)}
\<close>


\<phi>reasoner_ML ToR_Entry_Point 2000 (\<open>?X \<transforms> ?Y \<with> ?var_P\<close>) = \<open>
fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val sequent = skolemize_transformation ctxt sequent
      val (ctxt, sequent) = normalize_source_of_ToA (ctxt, sequent)
      val sequent = @{thm' Action_Tag_D[where A=\<open>\<T>\<P>\<close>]} RS sequent
      val sequent = if Config.get ctxt augment_ToA_by_implication
                    then NToA_init_having_Q RS sequent
                    else sequent
   in SOME ((ctxt,sequent), Seq.empty)
  end
)\<close>

setup \<open>Config.put_global Phi_Syntax.enable_auto_chk_and_conv true\<close>


subsection \<open>Supplementary Transformations\<close>

subsubsection \<open>Supplementary for Ex \& Conj \label{supp-ex-conj}\<close>

ML \<open>fun ToA_ex_intro_reasoning (ctxt,sequent) =
  let val (_, X'', _) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      fun parse (Const(\<^const_name>\<open>ExBI\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X) = (false, ty, X)
        | parse (Const(\<^const_name>\<open>REMAINS\<close>, _) $ (Const(\<^const_name>\<open>ExBI\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X) $ _)
            = (true, ty, X)
        | parse X = parse (Envir.beta_eta_contract X)
      val (has_focus, _, X'1) = parse X''
      val X = case X'1 of Abs (_, _, X) => X | X => Term.incr_boundvars 1 X $ Bound 0
      val ex_var_is_in_obj_only = Phi_Syntax.forall_item_of_assertion_blv (fn (_,lv) =>
                                    (fn (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) => not (Term.loose_bvar1 (T, lv))
                                      | A => not (Term.loose_bvar1 (A, lv)))) []
      val rule0 = if has_focus
                  then if ex_var_is_in_obj_only X
                  then @{thm' ExBI_transformation_I_R[where x=\<open>id c\<close> for c,
                                      OF Action_Tag_D[where A=\<open>\<T>\<P>\<close>], THEN Action_Tag_I[where A=\<open>\<T>\<P>\<close>]]}
                  else @{thm' ExBI_transformation_I_R[
                                      OF Action_Tag_D[where A=\<open>\<T>\<P>\<close>], THEN Action_Tag_I[where A=\<open>\<T>\<P>\<close>]]}
                  else if ex_var_is_in_obj_only X
                  then @{thm' ExBI_transformation_I[where x=\<open>id c\<close> for c,
                                      OF Action_Tag_D[where A=\<open>\<T>\<P>\<close>], THEN Action_Tag_I[where A=\<open>\<T>\<P>\<close>]]}
                  else @{thm' ExBI_transformation_I[
                                      OF Action_Tag_D[where A=\<open>\<T>\<P>\<close>], THEN Action_Tag_I[where A=\<open>\<T>\<P>\<close>]]}
   in SOME ((ctxt, rule0 RS sequent), Seq.empty)
  end\<close>

\<phi>reasoner_ML ToA_ex_intro default ! %ToA_inst_qunat ( \<open>_ \<transforms> ExBI _ \<with> _ @tag \<T>\<P>\<close>
                                                    | \<open>_ \<transforms> ExBI _ \<remains> _ \<with> _ @tag \<T>\<P>\<close> )
  = \<open>fn stat => Seq.make (fn () => ToA_ex_intro_reasoning (snd stat))\<close>

(*diverges to 3 branches, left branch, right branch, and instantiating the Ex in the domain if any. *)
\<phi>reasoner_ML NToA_conj_src ! %ToA_branches  (\<open>_ \<sqinter> _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>) = \<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val tail = (case Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
                    of (_, Const(\<^const_name>\<open>ExBI\<close>, _) $ X, _) =>
                            if Term.exists_Const (fn (\<^const_name>\<open>inf\<close>, _) => true
                                                   | _ => false) X
                            then Seq.make (fn () => ToA_ex_intro_reasoning (ctxt,sequent))
                            else Seq.empty
                     | _ => Seq.empty)
   in SOME ((ctxt, @{thm' NToA_conj_src_A
                            [OF Action_Tag_D[where A=\<open>\<T>\<P>\<close>], THEN Action_Tag_I[where A=\<open>\<T>\<P>\<close>]]} RS sequent),
        Seq.make (fn () => SOME ((ctxt, @{thm' NToA_conj_src_B
                            [OF Action_Tag_D[where A=\<open>\<T>\<P>\<close>], THEN Action_Tag_I[where A=\<open>\<T>\<P>\<close>]]} RS sequent), tail)))
  end
  )\<close>


subsubsection \<open>Evaluations\<close>

declare [[\<phi>chk_source_val = false]]

lemma [\<phi>reason %ToA_red]:
  \<open> (y,x) \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> prod.swap (x,y) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (f x, y) \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> apfst f (x,y) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, f y) \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> apsnd f (x,y) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> x \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> fst (x,y) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> y \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> snd (x,y) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, z) \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> (fst (x,y), z) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (y, z) \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> (snd (x,y), z) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, y) \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> (x, fst (y, z)) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> (x, z) \<Ztypecolon> T \<transforms> Y \<with> P
\<Longrightarrow> (x, snd (y, z)) \<Ztypecolon> T \<transforms> Y \<with> P \<close>
  by simp
declare [[\<phi>chk_source_val = true]]

subsubsection \<open>Let\<close>

lemma [\<phi>reason %ToA_red]:
  " T x \<transforms> U \<with> P
\<Longrightarrow> Let x T \<transforms> U \<with> P"
  unfolding Let_def .

lemma [\<phi>reason %ToA_red]:
  " T \<transforms> U x \<with> P
\<Longrightarrow> T \<transforms> Let x U \<with> P"
  unfolding Let_def .

lemma [\<phi>reason %ToA_red]:
  " T \<transforms> U x \<remains> R \<with> P
\<Longrightarrow> T \<transforms> Let x U \<remains> R \<with> P"
  unfolding Let_def .

subsubsection \<open>Case Prod\<close>

\<phi>reasoner_group ToA_red_caseprod =
  (%ToA_red, [%ToA_red, %ToA_red+10]) for (\<open>_ \<transforms> case_prod _ _ \<with> _\<close>, \<open>case_prod _ _ \<transforms> _ \<with> _\<close>)
  \<open>Transformations reducing \<open>case_prod\<close>\<close>

lemma [\<phi>reason %ToA_red_caseprod+10]:
  " T \<transforms> f x y \<with> P
\<Longrightarrow> T \<transforms> case_prod f (x,y) \<with> P"
  by simp

lemma [\<phi>reason %ToA_red_caseprod+10]:
  " T \<transforms> f x y \<remains> R \<with> P
\<Longrightarrow> T \<transforms> case_prod f (x,y) \<remains> R \<with> P"
  by simp

lemma [\<phi>reason %ToA_red_caseprod+10]:
  " A x y \<transforms> B \<with> P
\<Longrightarrow> case_prod A (x,y) \<transforms> B \<with> P"
  by simp

lemma [\<phi>reason %ToA_red_caseprod]:
  " T \<transforms> f (fst xy) (snd xy) \<with> P
\<Longrightarrow> T \<transforms> case_prod f xy \<with> P"
  unfolding Transformation_def
  by (cases xy; simp)

lemma [\<phi>reason %ToA_red_caseprod]:
  " T \<transforms> f (fst xy) (snd xy) \<remains> R \<with> P
\<Longrightarrow> T \<transforms> case_prod f xy \<remains> R \<with> P"
  unfolding Transformation_def
  by (cases xy; simp)

lemma [\<phi>reason %ToA_red_caseprod]:
  " A (fst xy) (snd xy) \<transforms> B \<with> P
\<Longrightarrow> case_prod A xy \<transforms> B \<with> P"
  by (cases xy; simp)


subsubsection \<open>Conditional Branch\<close>

paragraph \<open>Normalization\<close>

lemma [\<phi>reason %ToA_normalizing]:
  \<open> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<transforms> Y \<with> P
\<Longrightarrow> x \<Ztypecolon> If C A B \<transforms> Y \<with> P\<close>
  by (cases C; simp)

text \<open>\<^term>\<open>x \<Ztypecolon> (If C T U) \<OTast> W\<close> is not reduced because the \<open>C\<^sub>W\<close> and \<open>W\<close> have to be specially assigned.\<close>

(*TODO: the following rule is limited!! W\<^sub>1, W\<^sub>2*)

lemma [\<phi>reason %ToA_normalizing]: \<comment> \<open>\<open>W\<close> shouldn't contain schematic variable. Why a source can contain
                                      variable?\<close>
  \<open> If C ((x \<Ztypecolon> A) * W) ((x \<Ztypecolon> B) * W) \<transforms> Y \<with> P
\<Longrightarrow> (x \<Ztypecolon> If C A B) * W \<transforms> Y \<with> P\<close>
  by (cases C; simp)

lemma [\<phi>reason %ToA_normalizing]:
  \<open> X \<transforms> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<with> P
\<Longrightarrow> X \<transforms> x \<Ztypecolon> If C A B \<with> P\<close>
  by (cases C; simp)

paragraph \<open>Reduction for constant boolean condition\<close>

subparagraph \<open>Source\<close>

lemma NToA_cond_source_A[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] C
\<Longrightarrow> A \<transforms> X \<with> P
\<Longrightarrow> (if C then A else B) \<transforms> X \<with> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] \<not> C
\<Longrightarrow> B \<transforms> X \<with> P
\<Longrightarrow> (if C then A else B) \<transforms> X \<with> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_A_ty[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] C
\<Longrightarrow> x \<Ztypecolon> T \<OTast> W \<transforms> X \<with> P
\<Longrightarrow> x \<Ztypecolon> (if C then T else U) \<OTast> W \<transforms> X \<with> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B_ty[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] \<not> C
\<Longrightarrow> x \<Ztypecolon> U \<OTast> W \<transforms> X \<with> P
\<Longrightarrow> x \<Ztypecolon> (if C then T else U) \<OTast> W \<transforms> X \<with> P\<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  by (simp add: Transformation_def distrib_left)


subparagraph \<open>Target\<close>

lemma NToA_cond_target_A[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] C
\<Longrightarrow> X \<transforms> A \<with> P
\<Longrightarrow> X \<transforms> (if C then A else B) \<with> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_B[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] \<not> C
\<Longrightarrow> X \<transforms> B \<with> P
\<Longrightarrow> X \<transforms> (if C then A else B) \<with> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_A'[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] C
\<Longrightarrow> X \<transforms> A \<remains> R \<with> P
\<Longrightarrow> X \<transforms> (if C then A else B) \<remains> R \<with> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_B'[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] \<not> C
\<Longrightarrow> X \<transforms> B \<remains> R \<with> P
\<Longrightarrow> X \<transforms> (if C then A else B) \<remains> R \<with> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma NToA_cond_target_A_ty[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] C
\<Longrightarrow> X \<transforms> y \<Ztypecolon> T \<OTast> R \<with> P
\<Longrightarrow> X \<transforms> y \<Ztypecolon> (if C then T else U) \<OTast> R \<with> P\<close>
  unfolding Premise_def \<r>Guard_def \<phi>Prod'_def
  by simp

lemma NToA_cond_target_B_ty[\<phi>reason %ToA_red]:
  \<open> \<guard> \<condition>[NO_INST] \<not> C
\<Longrightarrow> X \<transforms> y \<Ztypecolon> U \<OTast> R \<with> P
\<Longrightarrow> X \<transforms> y \<Ztypecolon> (if C then T else U) \<OTast> R \<with> P\<close>
  unfolding Premise_def \<r>Guard_def
  by simp


paragraph \<open>When the condition boolean is a variable\<close>

text \<open>The condition should be regarded as an output, and the reasoning process assigns which
the branch that it chooses to the output condition variable.\<close>

subparagraph \<open>Normalizing\<close>

lemma [\<phi>reason %ToA_red for \<open>If (id ?var) _ _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> If C T U \<transforms> Y \<with> P @tag \<T>\<P>
\<Longrightarrow> If (id C) T U \<transforms> Y \<with> P @tag \<T>\<P> \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<Ztypecolon> If (id ?var) _ _ \<OTast> _ \<transforms> _ \<with> _ @tag \<T>\<P>'\<close>]:
  \<open> x \<Ztypecolon> If C T U \<OTast> W \<transforms> Y \<with> P @tag \<T>\<P>'
\<Longrightarrow> x \<Ztypecolon> If (id C) T U \<OTast> W \<transforms> Y \<with> P @tag \<T>\<P>'\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<transforms> If (id ?var) _ _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> X \<transforms> If C A B \<with> P @tag \<T>\<P>
\<Longrightarrow> X \<transforms> If (id C) A B \<with> P @tag \<T>\<P> \<close>
  by simp

lemma [\<phi>reason %ToA_red for \<open>_ \<transforms> _ \<Ztypecolon> (If (id ?var) _ _) \<OTast> _ \<with> _ @tag \<T>\<P>' \<close>]:
  \<open> X \<transforms> y \<Ztypecolon> (If C A B) \<OTast> R \<with> P @tag \<T>\<P>'
\<Longrightarrow> X \<transforms> y \<Ztypecolon> (If (id C) A B) \<OTast> R \<with> P @tag \<T>\<P>' \<close>
  by simp

subparagraph \<open>Source\<close>

text \<open>the \<open>id ?x\<close> here is the protector generated by instantiating existence in target.\<close>

declare [[\<phi>reason ! %ToA_branches NToA_cond_source_A NToA_cond_source_B
        for \<open>(if ?var_condition then ?A else ?B) \<transforms> ?X \<with> ?P @tag \<T>\<P>\<close>]]

hide_fact NToA_cond_source_A NToA_cond_source_B

declare [[\<phi>reason ! %ToA_branches NToA_cond_source_A_ty NToA_cond_source_B_ty
      for \<open>_ \<Ztypecolon> (if ?var then _ else _) \<OTast> _ \<transforms> _ \<with> _ @tag \<T>\<P>'\<close>]]

hide_fact NToA_cond_source_A_ty NToA_cond_source_B_ty


subparagraph \<open>Target\<close>

declare [[\<phi>reason ! %ToA_branches NToA_cond_target_A NToA_cond_target_B
            for \<open>?X \<transforms> (if ?var_condition then ?A else ?B) \<with> ?P @tag \<T>\<P>\<close> ]]

hide_fact NToA_cond_target_A NToA_cond_target_B

declare [[\<phi>reason ! %ToA_branches NToA_cond_target_B' NToA_cond_target_A'
            for \<open>?X \<transforms> (if ?var_condition then ?A else ?B) \<remains> _ \<with> ?P @tag \<T>\<P>\<close> ]]

hide_fact NToA_cond_target_A' NToA_cond_target_B'

declare [[\<phi>reason ! %ToA_branches NToA_cond_target_A_ty NToA_cond_target_B_ty
            for \<open>_ \<transforms> _ \<Ztypecolon> (if ?var then _ else _) \<OTast> _ \<with> _ @tag \<T>\<P>'\<close> ]]

hide_fact NToA_cond_target_A_ty NToA_cond_target_B_ty


paragraph \<open>Case Split\<close>

\<phi>reasoner_group ToA_splitting_If = (%ToA_splitting, [%ToA_splitting, %ToA_splitting+1])
                                   for (\<open>If C A B \<transforms> Y\<close>, \<open>X \<transforms> If C A B\<close>)
                                    in ToA_splitting
  \<open>ToA splitting \<open>If\<close> in either source or target, into two sub-goals.\<close>

subparagraph \<open>Source\<close>

lemma ToA_cond_branch_src:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<condition>   C \<longrightarrow> (A \<transforms> Ya \<with> P @tag \<T>\<P>))
\<Longrightarrow> (\<condition> \<not> C \<longrightarrow> (B \<transforms> Yb \<with> Q @tag \<T>\<P>))
\<Longrightarrow> If C A B \<transforms> Y \<with> If C P Q @tag \<T>\<P> \<close>
  unfolding Action_Tag_def
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma ToA_cond_branch_src_R:
  \<open> Y = If C Ya Yb
\<Longrightarrow> (\<condition>   C \<longrightarrow> (A \<transforms> Ya \<remains> Ra \<with> P @tag \<T>\<P>))
\<Longrightarrow> (\<condition> \<not> C \<longrightarrow> (B \<transforms> Yb \<remains> Rb \<with> Q @tag \<T>\<P>))
\<Longrightarrow> If C A B \<transforms> Y \<remains> If C Ra Rb \<with> If C P Q @tag \<T>\<P> \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

(*lemma ToA_cond_branch_src_R':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<condition>   C \<Longrightarrow> ((\<condition> False) \<and> P = False) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<transforms> Ya \<remains>[True] Ra \<with> P))
\<Longrightarrow> (\<condition> \<not> C \<Longrightarrow> ((\<condition> False) \<and> Q = False) \<or>\<^sub>c\<^sub>u\<^sub>t (B \<transforms> Yb \<remains>[True] Rb \<with> Q))
\<Longrightarrow> If C A B \<transforms> Y \<remains>[True] If C Ra Rb \<with> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)
*)

lemma [\<phi>reason %ToA_splitting_If]:
  \<open> (\<condition>   C \<Longrightarrow> (x \<Ztypecolon> T\<^sub>a \<OTast> W\<^sub>a \<transforms> y\<^sub>a \<Ztypecolon> U \<OTast> Ra \<with> P @tag \<T>\<P>'))
\<Longrightarrow> (\<condition> \<not> C \<Longrightarrow> (x \<Ztypecolon> T\<^sub>b \<OTast> W\<^sub>b \<transforms> y\<^sub>b \<Ztypecolon> U \<OTast> Rb \<with> Q  @tag \<T>\<P>'))
\<Longrightarrow> x \<Ztypecolon> (If C T\<^sub>a T\<^sub>b) \<OTast> (If C W\<^sub>a W\<^sub>b) \<transforms> If C y\<^sub>a y\<^sub>b \<Ztypecolon> U \<OTast> If C Ra Rb \<with> If C P Q @tag \<T>\<P>' \<close>
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
 
\<phi>reasoner_ML \<open>ML (If C A B \<transforms> Y \<with> P @tag \<T>\<P>)\<close> %ToA_splitting_If
             ( \<open>If _ _ _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
             | except \<open>If ?var _ _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_branch_src}, @{thm' ToA_cond_branch_src_R},
          (true, @{thms' if_cancel[folded atomize_eq]}, @{thms' if_True if_False}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>


subparagraph \<open>Target\<close>

lemma [\<phi>reason %ToA_splitting_If except \<open>_ \<transforms> (if ?var then _ else _) \<with> _ @tag \<T>\<P>\<close>]:
  \<open> (\<condition> C \<longrightarrow> (X \<transforms> A \<with> P @tag \<T>\<P>))
\<Longrightarrow> (\<condition> \<not> C \<longrightarrow> (X \<transforms> B \<with> Q @tag \<T>\<P>))
\<Longrightarrow> X \<transforms> (if C then A else B) \<with> If C P Q @tag \<T>\<P> \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma [\<phi>reason %ToA_splitting_If except \<open>_ \<transforms> (if ?var then _ else _) \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> (\<condition> C \<longrightarrow> (X \<transforms> A \<remains> Ra \<with> P @tag \<T>\<P>))
\<Longrightarrow> (\<condition> \<not> C \<longrightarrow> (X \<transforms> B \<remains> Rb \<with> Q @tag \<T>\<P>))
\<Longrightarrow> X \<transforms> (if C then A else B) \<remains> If C Ra Rb \<with> If C P Q @tag \<T>\<P> \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

(*
lemma [\<phi>reason %ToA_splitting_If+1 for \<open>_ \<transforms> (if _ then _ else _) \<remains>[True] _ \<with> _\<close>
                    except \<open>_ \<transforms> (if ?var then _ else _) \<remains>[_] _ \<with> _\<close>]:
  \<open> (\<condition> C \<Longrightarrow> ((\<condition> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<transforms> A \<remains>[True] Ra \<with> P))
\<Longrightarrow> (\<condition> \<not> C \<Longrightarrow> ((\<condition> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<transforms> B \<remains>[True] Rb \<with> Q))
\<Longrightarrow> X \<transforms> (if C then A else B) \<remains>[True] If C Ra Rb \<with> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)*)

lemma [\<phi>reason %ToA_splitting_If except \<open>_ \<transforms> _ \<Ztypecolon> (if ?var then _ else _) \<OTast> _ \<with> _ @tag \<T>\<P>'\<close>]:
  \<open> (\<condition> C \<longrightarrow> (X \<transforms> y\<^sub>a \<Ztypecolon> T \<OTast> Ra \<with> P @tag \<T>\<P>'))
\<Longrightarrow> (\<condition> \<not> C \<longrightarrow> (X \<transforms> y\<^sub>b \<Ztypecolon> U \<OTast> Rb \<with> Q @tag \<T>\<P>'))
\<Longrightarrow> X \<transforms> (if C then y\<^sub>a else y\<^sub>b) \<Ztypecolon> (if C then T else U) \<OTast> If C Ra Rb \<with> If C P Q @tag \<T>\<P>' \<close>
  unfolding Try_def Premise_def Orelse_shortcut_def
  by (cases C; simp)


subsubsection \<open>Conditioned Remains\<close>

paragraph \<open>When the conditional boolean is fixed\<close>

\<phi>reasoner_group ToA_constant_remains = (%ToA_splitting_source, [%ToA_splitting_source-4,%ToA_splitting_source+2])
                                        for (\<open>X \<transforms> Y \<remains> R \<with> P\<close>)
                                         in ToA \<open>\<close>

lemma [\<phi>reason default %ToA_constant_remains except \<open>_ \<transforms> _ \<remains> ?var \<with> _ @tag \<T>\<P>\<close>]:
  \<open> X \<transforms> Y * R \<with> P @tag \<T>\<P>
\<Longrightarrow> X \<transforms> Y \<remains> R \<with> P @tag \<T>\<P> \<close>
  unfolding REMAINS_def
  by simp


paragraph \<open>Reduction\<close>

subparagraph \<open>Source\<close>

lemma ToA_CR_src [\<phi>reason %ToA_red]:
  " Y * R \<transforms> X \<with> P @tag \<T>\<P>
\<Longrightarrow> Y \<remains> R \<transforms> X \<with> P @tag \<T>\<P> "
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def Action_Tag_def
  by simp

lemma ToA_CR_src' [\<phi>reason %ToA_red]:
  " (Y * R) * A \<transforms> X \<with> P @tag \<T>\<P>
\<Longrightarrow> (Y \<remains> R) * A \<transforms> X \<with> P @tag \<T>\<P> "
  unfolding Transformation_def split_paired_All \<r>Guard_def Premise_def Action_Tag_def
  by simp



subparagraph \<open>Target\<close>

lemma ToA_CR_target [\<phi>reason %ToA_red]:
  " Y \<transforms> X * R \<remains> R2 \<with> P @tag \<T>\<P>
\<Longrightarrow> Y \<transforms> (X \<remains> R) \<remains> R2 \<with> P @tag \<T>\<P> "
  unfolding \<r>Guard_def Premise_def REMAINS_def
  by simp

subsubsection \<open>Case Sum\<close>

paragraph \<open>Reduction\<close>

subparagraph \<open>Target\<close>

lemma ToA_case_sum_target_L[\<phi>reason %ToA_red]:
  \<open> X \<transforms> A x \<with> P
\<Longrightarrow> X \<transforms> case_sum A B (Inl x) \<with> P \<close>
  by simp

lemma ToA_case_sum_target_L'[\<phi>reason %ToA_red]:
  \<open> X \<transforms> A x \<remains> R \<with> P
\<Longrightarrow> X \<transforms> case_sum A B (Inl x) \<remains> R \<with> P \<close>
  by simp

lemma ToA_case_sum_target_L_ty[\<phi>reason %ToA_red]:
  \<open> X \<transforms> y \<Ztypecolon> U\<^sub>a c \<OTast> R \<with> P
\<Longrightarrow> X \<transforms> y \<Ztypecolon> case_sum U\<^sub>a U\<^sub>b (Inl c) \<OTast> R \<with> P \<close>
  by simp

lemma ToA_case_sum_target_R[\<phi>reason %ToA_red]:
  \<open> X \<transforms> B x \<with> P
\<Longrightarrow> X \<transforms> case_sum A B (Inr x) \<with> P \<close>
  by simp

lemma ToA_case_sum_target_R'[\<phi>reason %ToA_red]:
  \<open> X \<transforms> B x \<remains> R \<with> P
\<Longrightarrow> X \<transforms> case_sum A B (Inr x) \<remains> R \<with> P \<close>
  by simp

lemma ToA_case_sum_target_R_ty[\<phi>reason %ToA_red]:
  \<open> X \<transforms> y \<Ztypecolon> U\<^sub>b c \<OTast> R \<with> P
\<Longrightarrow> X \<transforms> y \<Ztypecolon> case_sum U\<^sub>a U\<^sub>b (Inr c) \<OTast> R \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]: \<comment> \<open>This form can occur when reducing \<open>y \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[C] R\<close>\<close>
  \<open> X \<transforms> case_sum A B x \<with> P
\<Longrightarrow> X \<transforms> case_sum A B (fst (x, y)) \<with> P \<close>
  by simp


subparagraph \<open>Source\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> A x \<transforms> Y \<with> P
\<Longrightarrow> case_sum A B (Inl x) \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> B x \<transforms> Y \<with> P
\<Longrightarrow> case_sum A B (Inr x) \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> A x * W \<transforms> Y \<with> P
\<Longrightarrow> case_sum A B (Inl x) * W \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> B x * W \<transforms> Y \<with> P
\<Longrightarrow> case_sum A B (Inr x) * W \<transforms> Y \<with> P \<close>
  by simp

lemma [\<phi>reason %ToA_red]: \<comment> \<open>This form can occur when reducing \<open>x \<Ztypecolon> (T +\<^sub>\<phi> U) \<^emph>[C] W\<close>\<close>
  \<open> case_sum A B x \<transforms> Y \<with> P
\<Longrightarrow> case_sum A B (fst (x, y)) \<transforms> Y \<with> P \<close>
  by simp


paragraph \<open>Case Split\<close>

subparagraph \<open>Target\<close>

lemma [\<phi>reason %ToA_splitting except \<open>_ \<transforms> case_sum _ _ ?var \<with> _ @tag \<T>\<P> \<close>]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> X \<transforms> A a \<with> P a @tag \<T>\<P>)
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> X \<transforms> B b \<with> Q b @tag \<T>\<P>)
\<Longrightarrow> X \<transforms> case_sum A B x \<with> case_sum P Q x @tag \<T>\<P> \<close>
  by (cases x; simp)

lemma [\<phi>reason %ToA_splitting except \<open>_ \<transforms> case_sum _ _ ?var \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> X \<transforms> A a \<remains> Ra a \<with> P a @tag \<T>\<P>)
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> X \<transforms> B b \<remains> Rb b \<with> Q b @tag \<T>\<P>)
\<Longrightarrow> X \<transforms> case_sum A B x \<remains> case_sum Ra Rb x \<with> case_sum P Q x @tag \<T>\<P> \<close>
  by (cases x; simp add: Simplify_def)

lemma [\<phi>reason %ToA_splitting+1 except \<open>_ \<transforms> _ \<Ztypecolon> (case_sum _ _ ?var) \<OTast> _ \<with> _ @tag \<T>\<P>'\<close>]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> xx \<Ztypecolon> T \<OTast> W\<^sub>a a \<transforms> y\<^sub>a a \<Ztypecolon> U\<^sub>a a \<OTast> R\<^sub>a a \<with> P\<^sub>a a @tag \<T>\<P>')
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> xx \<Ztypecolon> T \<OTast> W\<^sub>b b \<transforms> y\<^sub>b b \<Ztypecolon> U\<^sub>b b \<OTast> R\<^sub>b b \<with> P\<^sub>b b @tag \<T>\<P>')
\<Longrightarrow> xx \<Ztypecolon> T \<OTast> (case_sum W\<^sub>a W\<^sub>b x)
    \<transforms> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> (case_sum U\<^sub>a U\<^sub>b x) \<OTast> (case_sum R\<^sub>a R\<^sub>b x)
    \<with> case_sum P\<^sub>a P\<^sub>b x @tag \<T>\<P>' \<close>
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
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> (xx, w\<^sub>a a) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a \<transforms> y\<^sub>a a \<Ztypecolon> U\<^sub>a a \<^emph>[C\<^sub>a a] R\<^sub>a a \<with> P\<^sub>a a)
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> (xx, w\<^sub>b b) \<Ztypecolon> T \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b \<transforms> y\<^sub>b b \<Ztypecolon> U\<^sub>b b \<^emph>[C\<^sub>b b] R\<^sub>b b \<with> P\<^sub>b b)
\<Longrightarrow> \<condition> S\<^sub>a \<or> S\<^sub>b
\<Longrightarrow> (xx, case_sum (Inl o w\<^sub>a) (Inr o w\<^sub>b) x) \<Ztypecolon> T \<^emph>[case_sum C\<^sub>W\<^sub>a C\<^sub>W\<^sub>b x] (case_sum (Inl\<^sub>\<phi> W\<^sub>a) (Inr\<^sub>\<phi> W\<^sub>b) x)
    \<transforms> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> (case_sum U\<^sub>a U\<^sub>b x) \<^emph>[case_sum C\<^sub>a C\<^sub>b x] (case_sum R\<^sub>a R\<^sub>b x) \<with> case_sum P\<^sub>a P\<^sub>b x \<close>
  unfolding Premise_def Try_def
  sorry
*)

lemma [\<phi>reason %ToA_splitting except \<open>_ \<transforms> _ \<Ztypecolon> (case_sum _ _ ?var) \<OTast> _ \<with> _ @tag \<T>\<P>'\<close>]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> xx \<Ztypecolon> T \<OTast> W\<^sub>a a \<transforms> y\<^sub>a a \<Ztypecolon> U\<^sub>a a \<OTast> R\<^sub>a a \<with> P\<^sub>a a @tag \<T>\<P>')
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> xx \<Ztypecolon> T \<OTast> W\<^sub>b b \<transforms> y\<^sub>b b \<Ztypecolon> U\<^sub>b b \<OTast> R\<^sub>b b \<with> P\<^sub>b b @tag \<T>\<P>')
\<Longrightarrow> \<condition> S\<^sub>a \<or> S\<^sub>b
\<Longrightarrow> xx \<Ztypecolon> T \<OTast> (case_sum W\<^sub>a W\<^sub>b x)
    \<transforms> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> (case_sum U\<^sub>a U\<^sub>b x) \<OTast> (case_sum R\<^sub>a R\<^sub>b x) \<with> case_sum P\<^sub>a P\<^sub>b x @tag \<T>\<P>' \<close>
  unfolding Premise_def Try_def
  by (cases x; simp)

(*
lemma [\<phi>reason %ToA_splitting except \<open>_ \<transforms> case_sum _ _ ?var \<remains>[_] _ \<with> _\<close>
                                     \<open>_ \<transforms> case_sum _ _ (id ?var) \<remains>[_] _ \<with> _\<close>]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> X \<transforms> A a \<remains>[True] Ra a \<with> P a)
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> X \<transforms> B b \<remains>[True] Rb b \<with> Q b)
\<Longrightarrow> X \<transforms> case_sum A B x \<remains>[True] case_sum Ra Rb x \<with> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def)*)


subparagraph \<open>Source\<close>

lemma ToA_case_sum_src:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<condition> x = Inl a \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> P = (\<lambda>_. False) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<transforms> Ya a \<with> P a @tag \<T>\<P>))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> Q = (\<lambda>_. False) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<transforms> Yb b \<with> Q b @tag \<T>\<P>))
\<Longrightarrow> case_sum A B x \<transforms> Y \<with> case_sum P Q x @tag \<T>\<P> \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def Ant_Seq_def)

lemma ToA_case_sum_src_R:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<condition> x = Inl a \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> (Ca,Ra,P) = ((\<lambda>_. True),0,(\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<transforms> Ya a \<remains> Ra a \<with> P a @tag \<T>\<P>))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> (Cb,Rb,Q) = ((\<lambda>_. True),0,(\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<transforms> Yb b \<remains> Rb b \<with> Q b @tag \<T>\<P>))
\<Longrightarrow> case_sum A B x \<transforms> Y \<remains> case_sum Ra Rb x \<with> case_sum P Q x @tag \<T>\<P> \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def Ant_Seq_def)

(*lemma ToA_case_sum_src_R':
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<condition> x = Inl a \<Longrightarrow> ((\<condition> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<transforms> Ya a \<remains>[True] Ra a \<with> P a))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> ((\<condition> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<transforms> Yb b \<remains>[True] Rb b \<with> Q b))
\<Longrightarrow> case_sum A B x \<transforms> Y \<remains>[True] case_sum Ra Rb x \<with> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)*)
(*
lemma [\<phi>reason %ToA_splitting for \<open>case_sum (\<lambda>_. _ \<Ztypecolon> _ \<^emph>[_] _) (\<lambda>_. _ \<Ztypecolon> _ \<^emph>[_] _) _ \<transforms> _ \<Ztypecolon> _ \<^emph>[_] _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> (y\<^sub>a,C\<^sub>W\<^sub>a,W\<^sub>a,Ca,Ra,P) = (unspec, (\<lambda>_. True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_. True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (x\<^sub>a a \<Ztypecolon> T\<^sub>a a \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a \<transforms> y\<^sub>a a \<Ztypecolon> U \<^emph>[Ca a] Ra a \<with> P a @tag \<T>\<P>))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> (y\<^sub>b,C\<^sub>W\<^sub>b,W\<^sub>b,Cb,Rb,Q) = (unspec, (\<lambda>_.True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_.True), (\<lambda>_. \<bottom>\<^sub>\<phi>), (\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (x\<^sub>b b \<Ztypecolon> T\<^sub>b b \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b \<transforms> y\<^sub>b b \<Ztypecolon> U \<^emph>[Cb b] Rb b \<with> Q b @tag \<T>\<P>))
\<Longrightarrow> (case x of Inl a \<Rightarrow> x\<^sub>a a \<Ztypecolon> T\<^sub>a a \<^emph>[C\<^sub>W\<^sub>a a] W\<^sub>a a | Inr b \<Rightarrow> x\<^sub>b b \<Ztypecolon> T\<^sub>b b \<^emph>[C\<^sub>W\<^sub>b b] W\<^sub>b b)
    \<transforms> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> U \<^emph>[case_sum Ca Cb x] case_sum Ra Rb x \<with> case_sum P Q x @tag \<T>\<P> \<close>
  unfolding Try_def Simplify_def Premise_def Orelse_shortcut_def Ant_Seq_def
  by (cases x; simp)
*)
(*
lemma [\<phi>reason %ToA_splitting+1 for \<open>case_sum _ _ _ \<transforms> _ \<Ztypecolon> _ \<^emph>[_] _ \<with> _\<close>]:
  \<open> (\<And>a. \<condition> x = Inl a \<Longrightarrow> ((\<condition> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (A a \<transforms> y\<^sub>a a \<Ztypecolon> U \<^emph>[True] Ra a \<with> P a))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> ((\<condition> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (B b \<transforms> y\<^sub>b b \<Ztypecolon> U \<^emph>[True] Rb b \<with> Q b))
\<Longrightarrow> case_sum A B x \<transforms> case_sum y\<^sub>a y\<^sub>b x \<Ztypecolon> U \<^emph>[True] case_sum Ra Rb x \<with> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)*)

lemma ToA_case_sum_src_W:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<condition> x = Inl a \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> P = (\<lambda>_. False) \<or>\<^sub>c\<^sub>u\<^sub>t (A a * W \<transforms> Ya a \<with> P a @tag \<T>\<P>))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> Q = (\<lambda>_. False) \<or>\<^sub>c\<^sub>u\<^sub>t (B b * W \<transforms> Yb b \<with> Q b @tag \<T>\<P>))
\<Longrightarrow> case_sum A B x * W \<transforms> Y \<with> case_sum P Q x @tag \<T>\<P> \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def Ant_Seq_def)

lemma ToA_case_sum_src_WR:
  \<open> Y = case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<condition> x = Inl a \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> (Ca,Ra,P) = ((\<lambda>_. True),0,(\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (A a * W \<transforms> Ya a \<remains> Ra a \<with> P a @tag \<T>\<P>))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> \<condition> False \<and>\<^sub>\<r> (Cb,Rb,Q) = ((\<lambda>_. True),0,(\<lambda>_. False)) \<or>\<^sub>c\<^sub>u\<^sub>t
                                (B b * W \<transforms> Yb b \<remains> Rb b \<with> Q b @tag \<T>\<P>))
\<Longrightarrow> case_sum A B x * W \<transforms> Y \<remains> case_sum Ra Rb x \<with> case_sum P Q x @tag \<T>\<P> \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def Ant_Seq_def)

(*lemma ToA_case_sum_src_WR':
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<condition> x = Inl a \<Longrightarrow> ((\<condition> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A a \<transforms> Ya a \<remains>[True] Ra a \<with> P a))
\<Longrightarrow> (\<And>b. \<condition> x = Inr b \<Longrightarrow> ((\<condition> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * B b \<transforms> Yb b \<remains>[True] Rb b \<with> Q b))
\<Longrightarrow> W * case_sum A B x \<transforms> Y \<remains>[True] case_sum Ra Rb x \<with> case_sum P Q x \<close>
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

\<phi>reasoner_ML \<open>ML (case_sum A B x \<transforms> Y \<with> P @tag \<T>\<P>)\<close> %ToA_splitting
        ( \<open>case_sum _ _ _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
        | except \<open>case_sum _ _ ?var \<transforms> _ \<with> _ @tag \<T>\<P>\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_case_sum_src}, @{thm' ToA_case_sum_src_R}, (*@{thm' ToA_case_sum_src_R'},*)
          (true, @{thms' case_sum_degenerate}, @{thms' sum.case}),
          reasoner_ToA_conditioned_subgoals_sum, \<^context>) o snd\<close>

\<phi>reasoner_ML \<open>ML (case_sum A B x * W \<transforms> Y \<with> P @tag \<T>\<P>)\<close> %ToA_splitting
        ( \<open>case_sum _ _ _ * _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close>
        | except \<open>case_sum _ _ ?var * _ \<transforms> _ \<with> _ @tag \<T>\<P>\<close> )
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_case_sum_src_W}, @{thm' ToA_case_sum_src_WR}, (*@{thm' ToA_case_sum_src_WR'},*)
          (true, @{thms' case_sum_degenerate}, @{thms' sum.case}),
          reasoner_ToA_conditioned_subgoals_sum, \<^context>) o snd\<close>


paragraph \<open>When the sum type is a variable\<close>

subparagraph \<open>Normalizing\<close>

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> case_sum A B var \<with> P
\<Longrightarrow> X \<transforms> case_sum A B (id var) \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> case_sum A B var \<remains> R \<with> P
\<Longrightarrow> X \<transforms> case_sum A B (id var) \<remains> R \<with> P\<close>
  by simp

lemma [\<phi>reason %ToA_red]:
  \<open> X \<transforms> y \<Ztypecolon> (case_sum A B var) \<OTast> R \<with> P
\<Longrightarrow> X \<transforms> y \<Ztypecolon> (case_sum A B (id var)) \<OTast> R \<with> P\<close>
  by simp

subparagraph \<open>Major Reasoning\<close>

declare [[
    \<phi>reason ! %ToA_branches ToA_case_sum_target_L ToA_case_sum_target_R
        for \<open>_ \<transforms> case_sum _ _ ?var \<with> _ @tag \<T>\<P>\<close>,
    \<phi>reason ! %ToA_branches ToA_case_sum_target_L' ToA_case_sum_target_R'
        for \<open>_ \<transforms> case_sum _ _ ?var \<remains> _ \<with> _ @tag \<T>\<P>\<close>,
    \<phi>reason ! %ToA_branches ToA_case_sum_target_L_ty ToA_case_sum_target_R_ty
        for \<open>_ \<transforms> _ \<Ztypecolon> (case_sum _ _ ?var) \<OTast> _ \<with> _ @tag \<T>\<P>'\<close>
]]

(*TODO: the source part!*)


section \<open>Helpful Stuffs\<close>

subsection \<open>Methods\<close>

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