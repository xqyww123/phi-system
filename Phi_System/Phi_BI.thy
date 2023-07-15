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

subsection \<open>Bottom\<close>

abbreviation Bottom ("\<bottom>") where \<open>Bottom \<equiv> (0::'a::sep_magma BI)\<close>
abbreviation Bottom_abs ("\<bottom>\<^sub>\<lambda>") where \<open>Bottom_abs \<equiv> (0 :: 'b \<Rightarrow> 'a::sep_magma BI)\<close>

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
  \<open>\<not> (p \<Turnstile> \<bottom>)\<close>
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


subsection \<open>Inhabitance\<close>

definition Inhabited :: " 'a BI \<Rightarrow> bool " where  "Inhabited S = (\<exists>p. p \<Turnstile> S)"

abbreviation Inhabitance_Implication :: \<open>'a BI \<Rightarrow> bool \<Rightarrow> bool\<close> (infix "\<i>\<m>\<p>\<l>\<i>\<e>\<s>" 10)
  where \<open>S \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<equiv> Inhabited S \<longrightarrow> P @action \<A>EIF\<close>

declare [[
  \<phi>reason_default_pattern \<open>Inhabited ?X \<longrightarrow> _\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>bad form\<close>)\<close> (100)
]]

ML_file \<open>library/tools/inhabited_rule.ML\<close>

lemma Inhabited_I:
  \<open>x \<Turnstile> S \<Longrightarrow> Inhabited S\<close>
  unfolding Inhabited_def ..

lemma Inhabited_cong[cong]:
  \<open>X \<equiv> X \<Longrightarrow> Inhabited X \<equiv> Inhabited X\<close> .

lemma Inhabited_fallback_True:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> True \<close>
  unfolding Action_Tag_def by blast

\<phi>reasoner_ML Inhabited_fallback default 2 (\<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close>) =
\<open>fn (ctxt,sequent) => Seq.make (fn () =>
  if Config.get ctxt Phi_Reasoners.mode_generate_extraction_rule
  then SOME ((ctxt, Thm.permute_prems 0 ~1 sequent), Seq.empty)
  else SOME ((ctxt, @{thm Inhabited_fallback_True} RS sequent), Seq.empty)
)\<close>

lemma Membership_E_Inhabitance:
  \<open> x \<Turnstile> S
\<Longrightarrow> Inhabited S \<longrightarrow> C
\<Longrightarrow> C\<close>
  unfolding Inhabited_def by blast


subsection \<open>\<phi>-Type\<close>

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete BI "

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a BI" (infix "\<Ztypecolon>" 20) where " (x \<Ztypecolon> T) = (T x)"

text \<open>The implementation represents BI assertions by sets simply, in shallow embedding manner.\<close>

lemma typing_inhabited: "p \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (x \<Ztypecolon> T)"
  unfolding Inhabited_def \<phi>Type_def by blast

lemma \<phi>Type_eqI:
  \<open>(\<forall>x p. p \<Turnstile> (x \<Ztypecolon> a) \<longleftrightarrow> p \<Turnstile> (x \<Ztypecolon> b)) \<Longrightarrow> a = b\<close>
  unfolding \<phi>Type_def Satisfaction_def by blast

ML_file \<open>library/tools/simp_congruence.ML\<close>

declare [[
  \<phi>reason_default_pattern_ML \<open>?x \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close> \<Rightarrow> \<open>
    fn ctxt => fn tm as (_ (*Trueprop*) $ (_ (*Action_Tag*) $ (_ (*imp*) $ (
                            _ (*Inhabited*) $ (_ (*\<phi>Type*) $ x $ _)) $ _) $ _)) =>
      if is_Var x orelse not (Context_Position.is_visible_generic ctxt)
      then NONE
      else error("Bad form: In \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<close> the x must be a schematic variable. But it gives\n" ^
                 Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt tm)\<close> (1000)
]]

subsection \<open>Transformation of Abstraction\<close>

text \<open>The only meaningful implication \<open>\<longrightarrow>\<close> under the interpretation of \<phi> data refinement\<close>

definition Transformation :: " 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool \<Rightarrow> bool " ("(2_)/ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (2_)/ \<w>\<i>\<t>\<h> (2_)" [13,13,13] 12)
  where "(A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) \<longleftrightarrow> (\<forall>v. v \<Turnstile> A \<longrightarrow> v \<Turnstile> B \<and> P)"

abbreviation SimpleTransformation :: " 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool " ("(2_)/ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (2_)" [13,13] 12)
  where \<open>SimpleTransformation T U \<equiv> Transformation T U True\<close>

subsubsection \<open>Reasoning Setup - I\<close>

ML \<open>val phi_allow_source_object_to_be_not_variable =
          Config.declare_bool ("phi_allow_source_object_to_be_not_variable", \<^here>) (K false)\<close>

declare [[
  \<phi>reason_default_pattern \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> _\<close> (10),
  \<phi>reason_default_pattern_ML \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>fn ctxt =>
      fn tm as (Trueprop $ (Transformation $ X $ (PhiTyp $ y $ U) $ _)) =>
        let val idx = Term.maxidx_term X (Term.maxidx_term y (Term.maxidx_term U ~1)) + 1
            val P  = Var(("P", idx), HOLogic.boolT)
            val y' = Var(("var_y", idx), Term.fastype_of y)
            val _ = if Context_Position.is_visible_generic ctxt andalso
                       not (Config.get_generic ctxt phi_allow_source_object_to_be_not_variable)
                    then (case X of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _
                                      => if is_Var x then ()
                                         else error ("The ToA rule should be in form \<open>?x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> where \<open>?x\<close> must be a variable.\n" ^
                                                     Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt tm)
                                  | _ => ())
                    else ()
         in if is_Var X then SOME [Trueprop $ (Transformation $ X $ (PhiTyp $ y  $ U) $ P)]
                        else SOME [Trueprop $ (Transformation $ X $ (PhiTyp $ y' $ U) $ P)]
        end\<close> (20)
]]

text \<open>Semantics of antecedent \<^pattern_prop>\<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> ?P\<close>:
  Given the source \<^term>\<open>X\<close> and the target \<^term>\<open>Y\<close>, find a reasoning way to do the transformation,
  which may bring in additional pure facts \<^pattern_term>\<open>?P\<close> and generate proof obligations.\<close>

definition FOCUS_TAG :: " 'a \<Rightarrow> 'a "  ("\<blangle> _ \<brangle>") where [iff]: "\<blangle> x \<brangle> = x"

abbreviation Remains :: \<open> 'a::{sep_disj,times} BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<close> (infix "\<r>\<e>\<m>\<a>\<i>\<n>\<s>" 13)
  where \<open>(X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R) \<equiv> R * \<blangle> X \<brangle>\<close>

declare [[
  \<phi>reason_default_pattern \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close> (20),
  \<phi>reason_default_pattern_ML \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close> \<Rightarrow> \<open>fn _ =>
    fn Trueprop $ (Transformation $ X $ (Times $ R $ (FOCUS $ (PhiTyp $ y $ U))) $ _) =>
      let val idx = Term.maxidx_term X (Term.maxidx_term y (Term.maxidx_term U ~1)) + 1
          val P  = Var(("P", idx), HOLogic.boolT)
          val R' = Var(("R", idx), Term.fastype_of R)
          val y' = Var(("var_y", idx), Term.fastype_of y)
       in if is_Var X then SOME [Trueprop $ (Transformation $ X $ (Times $ R' $ (FOCUS $ (PhiTyp $ y  $ U))) $ P)]
                      else SOME [Trueprop $ (Transformation $ X $ (Times $ R' $ (FOCUS $ (PhiTyp $ y' $ U))) $ P)]
      end\<close> (30)
]]
   
text \<open>For antecedent \<^pattern_prop>\<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<w>\<i>\<t>\<h> _\<close>, the semantics is slightly different
  where it specifies extracting given \<^term>\<open>Y\<close> from given \<^term>\<open>X\<close> and leaving some \<^schematic_term>\<open>?R\<close>.\<close>

subsubsection \<open>Rules\<close>

lemma \<phi>Type_eqI_imp:
  \<open> (\<And>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> U)
\<Longrightarrow> (\<And>x. x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T)
\<Longrightarrow> T = U\<close>
  unfolding \<phi>Type_def Transformation_def Satisfaction_def
  by auto

lemma transformation_refl[simp]:
  "A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A" unfolding Transformation_def by fast

lemma implies_trans:
  "A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> (P \<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> C \<w>\<i>\<t>\<h> P \<and> Q"
  unfolding Transformation_def Premise_def by auto

lemma implies_weaken:
  \<open> P \<longrightarrow> P'
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P'\<close>
  unfolding Transformation_def by simp

lemma implies_intro_inhab:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> Inhabited A \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def Inhabited_def Satisfaction_def
  by blast

lemma assertion_eq_intro:
  \<open> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Q
\<Longrightarrow> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> P
\<Longrightarrow> P = Q\<close>
  unfolding Transformation_def BI_eq_iff by blast


subsubsection \<open>Reasoning Setup - II\<close>

declare transformation_refl [\<phi>reason 4000 for \<open>?A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A \<w>\<i>\<t>\<h> ?P\<close> \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y \<Ztypecolon> ?T \<w>\<i>\<t>\<h> _\<close>]
declare transformation_refl [
    \<phi>reason 900 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> if \<open>fn (ctxt, sequent) =>
        let val _ (*Trueprop*) $ (_ (*Transformation*) $ A $ B $ _) = Thm.major_prem_of sequent
            fun chk_var (Var _) = true
              | chk_var (X $ _) = chk_var X
              | chk_var _ = false
            (*check if is an atom BI assertion, or a \<phi>-type whose abstract object is schematic var.
              If so, we will try to apply `transformation_refl` with backtrack*)
            fun chk (Const(\<^const_name>\<open>times\<close>, _)) = false
              | chk (Var _) = true
              | chk (Free _) = true
              | chk (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _) = chk_var x
              | chk (X $ _) = chk X
              | chk (Const(\<^const_name>\<open>plus\<close>, _)) = false
              | chk (Const(\<^const_name>\<open>Subjection\<close>, _)) = false
              | chk (Const(\<^const_name>\<open>ExSet\<close>, _)) = false
              | chk (Const(\<^const_name>\<open>inf\<close>, _)) = false
              | chk (Const(\<^const_name>\<open>sup\<close>, _)) = false
              | chk (Const(\<^const_name>\<open>top\<close>, _)) = false
              | chk (Const(\<^const_name>\<open>bot\<close>, _)) = false
              | chk (Abs _) = raise Phi_Help.REQUIRE_LAMBDA_NORMLAIZTION
              | chk (Const _) = true
              | chk _ = false
         in chk B
         handle Phi_Help.REQUIRE_LAMBDA_NORMLAIZTION => (
            chk (Envir.beta_eta_contract B)
            handle Phi_Help.REQUIRE_LAMBDA_NORMLAIZTION => false)
        end \<close>]

ML \<open>fun check_ToA_rule rule =
  let fun chk_target (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _) =
            (case x of Var _ => true
                     | _ => false)
        | chk_target (Const(\<^const_name>\<open>times\<close>, _) $ A $ B) = chk_target A andalso chk_target B
        | chk_target (Const(\<^const_name>\<open>Subjection\<close>, _) $ X) = chk_target X
        | chk_target (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = chk_target X
        | chk_target (Abs (_,_,X)) = chk_target X
        | chk_target _ = true
      fun chk (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ Y $ _) = is_Var X orelse chk_target Y
        | chk (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = chk X
        | chk (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = chk X
        | chk (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = chk X
        | chk _ = true
   in if forall chk (Thm.prems_of rule)
      then ()
      else warning "In the antecedents of a ToA rule, the target object should be a variable."
  end
\<close>

setup \<open>Context.theory_map (Phi_Reasoner.add_pass ("Phi_BI.ToA_rule_chk", \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>,
  fn _ => fn (rules, mode, pats, guard, ctxt) =>
             (if null (fst pats) then List.app check_ToA_rule rules else () ;
              (rules, mode, pats, guard, ctxt))))\<close>


paragraph \<open>Inhabitance Reasoning - Part II\<close>

lemma [\<phi>reason 1100]:
  \<open> Generate_Implication_Reasoning (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) (Inhabited X) (Inhabited Y) \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Inhabited_def by blast

lemma [\<phi>reason 1000]:
  \<open> Generate_Implication_Reasoning (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) (Inhabited X) (Inhabited Y \<and> P) \<close>
  unfolding Generate_Implication_Reasoning_def Transformation_def Inhabited_def by blast


subsection \<open>Bottom\<close>

text \<open>We write the bottom as \<open>0::'a BI\<close> instead of the usual \<open>\<bottom>\<close> though they are equal,
  in order to leverage the existing automation on semiring (\<open>0, 1, *, +\<close>).\<close>

lemma zero_implies_any[\<phi>reason 2000, simp]:
  \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close>
  unfolding Transformation_def zero_set_def Satisfaction_def by simp


subsection \<open>Top\<close>

notation top ("\<top>")


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

lemma additive_conj_implication[\<phi>reason 1000]:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> P
\<Longrightarrow> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Q
\<Longrightarrow> A \<and>\<^sub>B\<^sub>I B \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> Q\<close>
  unfolding Action_Tag_def
  by blast


subsubsection \<open>Subjection: Conjunction to a Pure Fact\<close>

text \<open>This is the only widely used additive conjunction under the interpretation of the \<phi> data refinement\<close>

lemma Subjection_inhabited_E[elim!]:
  \<open>Inhabited (S \<s>\<u>\<b>\<j> P) \<Longrightarrow> (Inhabited S \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> C
\<Longrightarrow> S \<s>\<u>\<b>\<j> P \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<and> C \<close>
  unfolding Inhabited_def Action_Tag_def
  by simp

lemma Subjection_cong[cong]:
  \<open>P \<equiv> P' \<Longrightarrow> (P' \<Longrightarrow> S \<equiv> S') \<Longrightarrow> (S \<s>\<u>\<b>\<j> P) \<equiv> (S' \<s>\<u>\<b>\<j> P')\<close>
  unfolding atomize_eq BI_eq_iff by (simp, blast)

lemma Subjection_imp_I:
  \<open> P
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> Q
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q\<close>
  unfolding Transformation_def by simp

lemma Subjection_imp_simp[simp]:
  \<open> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q) \<longleftrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P \<and> Q) \<close>
  unfolding Transformation_def by simp

lemma Subjection_True [simp, \<phi>programming_safe_simps]:
  \<open>(T \<s>\<u>\<b>\<j> True) = T\<close>
  unfolding BI_eq_iff by simp

lemma Subjection_Flase[simp, \<phi>programming_safe_simps]:
  \<open>(T \<s>\<u>\<b>\<j> False) = 0\<close>
  unfolding BI_eq_iff by simp

lemma Subjection_Subjection:
  \<open>(S \<s>\<u>\<b>\<j> P \<s>\<u>\<b>\<j> Q) = (S \<s>\<u>\<b>\<j> P \<and> Q)\<close>
  unfolding BI_eq_iff
  by simp

lemma Subjection_Zero[simp]:
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

lemma Subjection_times[simp]:
  \<open>(S \<s>\<u>\<b>\<j> P) * T = (S * T \<s>\<u>\<b>\<j> P)\<close>
  \<open>T * (S \<s>\<u>\<b>\<j> P) = (T * S \<s>\<u>\<b>\<j> P)\<close>
  unfolding BI_eq_iff
  by (simp, blast)+

lemma Subjection_plus:
  \<open>(A + B \<s>\<u>\<b>\<j> P) = (A \<s>\<u>\<b>\<j> P) + (B \<s>\<u>\<b>\<j> P)\<close>
  unfolding BI_eq_iff
  by simp blast

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

lemma [\<phi>inhabitance_rule 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> B
\<Longrightarrow> X * Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<and> B\<close>
  unfolding Action_Tag_def
  using set_mult_inhabited by blast

lemma implies_left_prod:
  "U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> R * U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * U \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma implies_right_prod:
  "U' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow> U' * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U * R \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast

lemma implies_prod_bi_prod:
  " R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> L' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> L \<w>\<i>\<t>\<h> Q
\<Longrightarrow> L' * R' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> L * R \<w>\<i>\<t>\<h> P \<and> Q "
  unfolding Transformation_def split_paired_All sep_conj_expn by blast




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


subsubsection \<open>Rules\<close>

lemma ExSet_pair: "ExSet T = (\<exists>*a b. T (a,b))"
  unfolding BI_eq_iff by clarsimp

lemma ExSet_times_left [simp]: "(ExSet T * R) = (\<exists>* c. T c * R )" by (simp add: BI_eq_iff, blast)
lemma ExSet_times_right[simp]: "(L * ExSet T) = (\<exists>* c. L * T c)" by (simp add: BI_eq_iff, blast)

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
  unfolding BI_eq_iff by simp_all blast

declare ExSet_simps(1)[\<phi>programming_safe_simps]

lemma ExSet_transformation:
  \<open>(\<And>x. S x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' x \<w>\<i>\<t>\<h> P)
\<Longrightarrow> ExSet S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet S' \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp, blast)

lemma ExSet_transformation_I:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' x \<w>\<i>\<t>\<h> P
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (ExSet S') \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (clarsimp, blast)

lemma ExSet_additive_disj:
  \<open>(\<exists>*x. A x + B x) = ExSet A + ExSet B\<close>
  \<open>ExSet (A + B) = ExSet A + ExSet B\<close>
  unfolding BI_eq_iff by (simp_all add: plus_fun) blast+

ML_file \<open>library/tools/simproc_ExSet_expand_quantifier.ML\<close>

lemma Ex_transformation_expn:
  \<open>((\<exists>*x. A x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P) \<longleftrightarrow> (\<forall>x. A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P)\<close>
  unfolding Transformation_def ExSet_expn
  by blast



subsection \<open>Universal Quantification\<close>

definition AllSet :: \<open>('a \<Rightarrow> 'b BI) \<Rightarrow> 'b BI\<close> (binder "\<forall>\<^sup>S" 10)
  where \<open>AllSet X = {y. \<forall>x. y \<in> X x}\<close>

lemma AllSet_expn[simp, \<phi>expns]:
  \<open>p \<Turnstile> (\<forall>\<^sup>Sx. B x) \<longleftrightarrow> (\<forall>x. p \<Turnstile> B x)\<close>
  unfolding AllSet_def Satisfaction_def by simp

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

lemma [elim!]:
  \<open>Inhabited (AllSet S) \<Longrightarrow> (Inhabited (S x) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def
  by clarsimp blast

lemma [\<phi>inhabitance_rule 1000]:
  \<open> Inhabited (S x) \<longrightarrow> C @action \<A>EIF
\<Longrightarrow> Inhabited (AllSet S) \<longrightarrow> C @action \<A>EIF \<close>
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

lemma [\<phi>inhabitance_rule 1000]:
  \<open> x \<Ztypecolon> Itself \<i>\<m>\<p>\<l>\<i>\<e>\<s> True \<close>
  using Inhabited_fallback_True .

lemma Itself_E[\<phi>reason 20]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> v \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<close>
  unfolding Transformation_def Premise_def by simp

lemma satisfication_encoding:
  \<open> (x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<w>\<i>\<t>\<h> P) \<longleftrightarrow> x \<Turnstile> (y \<Ztypecolon> T) \<and> P \<close>
  unfolding Transformation_def by simp


subsubsection \<open>Embedding of Empty\<close>

definition \<phi>None :: \<open>('v::one, unit) \<phi>\<close> ("\<circle>")
  where \<open>\<phi>None = (\<lambda>x. { 1 }) \<close>

lemma \<phi>None_expn[\<phi>expns, simp]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>None) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>None_def \<phi>Type_def by simp

lemma \<phi>None_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>None) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>None_itself_is_one[simp]:
  \<open>(any \<Ztypecolon> \<phi>None) = 1\<close>
  unfolding set_eq_iff by simp

(*
lemma [\<phi>reason 1200]:
  \<open>any \<Ztypecolon> \<phi>None \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<Ztypecolon> Itself\<close>
  unfolding Transformation_def by simp *)



subsubsection \<open>Embedding of Separation Conjunction\<close>

definition \<phi>Prod :: " ('concrete::sep_magma, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b). B b * A a)"

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





subsection \<open>Equivalence of Objects\<close>

definition Object_Equiv :: \<open>('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Object_Equiv T eq \<longleftrightarrow> (\<forall>x y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T))\<close>

declare [[
    \<phi>reason_default_pattern \<open>Object_Equiv ?T _\<close> \<Rightarrow> \<open>Object_Equiv ?T _\<close> (100),
    \<phi>premise_attribute? [\<phi>reason add] for \<open>Object_Equiv _ _\<close>
]]

lemma ToA_by_Equive_Class
      [\<phi>reason !1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>
                  except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y  \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> Object_Equiv U eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def by clarsimp

lemma ToA_by_Equive_Class'
      [\<phi>reason !1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                   except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_y' \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y  \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Object_Equiv U eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq y y'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Transformation_def Premise_def FOCUS_TAG_def
  by (clarsimp, meson Transformation_def implies_left_prod)

lemma [\<phi>reason default 1]:
  \<open>Object_Equiv T (=)\<close>
  unfolding Object_Equiv_def by simp

(*
lemma [\<phi>reason 800 for \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> _\<close>]:
  " Object_Equiv T eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T"
  unfolding Object_Equiv_def Transformation_def Premise_def by clarsimp*)

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


end