chapter \<open>Integrated Deduction Environment for Programming (IDE-P)\<close>

theory IDE_CP_Core
  imports
    "Phi_Semantics_Framework.Phi_Semantics_Framework"
    "Phi_Algebras.Map_of_Tree"
    Calculus_of_Programming
    IDE_CP_Reasoning1
  keywords
    "proc" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "\<Longleftarrow>" "\<Longleftarrow>'" "$" "subj"
    "var" "invar" "\<Longrightarrow>" "@action" "\<exists>" "throws" "pure_fact"
    "input" "certified" "requires" :: quasi_command
  and "\<medium_left_bracket>" :: prf_goal % "proof"
  and ";;" :: prf_goal % "proof"
  and "\<medium_right_bracket>" :: prf_goal % "proof"
  and "\<phi>processor" :: thy_decl % "ML"
  and (* "\<phi>interface" "\<phi>export_llvm" *) "\<phi>overloads" :: thy_decl
abbrevs
  "!!" = "!!"
  and "<argument>" = "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t"
  and "<do>" = "\<^bold>d\<^bold>o"
  and "<param>" = "\<p>\<a>\<r>\<a>\<m>"
  and "<label>" = "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l"
      and "<subty>" = "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e"
      and "<by>" = "\<^bold>b\<^bold>y"
      and "<simplify>" = "\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>"
      and "<when>" = "\<^bold>w\<^bold>h\<^bold>e\<^bold>n"
      and "<try>" = "\<^bold>t\<^bold>r\<^bold>y"
  and "<obligation>" = "\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n>"
  and ">->" = "\<Zinj>"
  and "<;>" = "\<Zcomp>"
  and "<val>" = "\<v>\<a>\<l>"
  and "<ret>" = "\<^bold>r\<^bold>e\<^bold>t"
  and "<is>" = "\<i>\<s>"
begin

section \<open>Preliminary Configuration\<close>

named_theorems \<phi>lemmata \<open>Contextual facts during the programming. They are automatically
       aggregated from every attached \<^prop>\<open>P\<close> in \<^prop>\<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk in [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Sth \<s>\<u>\<b>\<j> P\<close>
       during the programming. Do not modify it manually because it is managed automatically and
       cleared frequently\<close>

lemma [\<phi>programming_simps]:
  \<open>(A\<heavy_comma> (B\<heavy_comma> C)) = (A\<heavy_comma> B\<heavy_comma> C)\<close>
  unfolding mult.assoc ..

subsubsection \<open>Syntax \& Prelude ML\<close>

ML_file \<open>library/syntax/Phi_Syntax.ML\<close>
ML_file \<open>library/syntax/procedure2.ML\<close>

section \<open>Antecedent Jobs \& Annotations in Sequents\<close>

subsection \<open>Parameter From User\<close>

definition ParamTag :: " 'a::{} \<Rightarrow> bool" ("\<p>\<a>\<r>\<a>\<m> _" [1000] 26) where "\<p>\<a>\<r>\<a>\<m> x \<equiv> True"

text \<open>Antecedent \<^prop>\<open>\<p>\<a>\<r>\<a>\<m> x\<close> asks users to input some term that matches pattern \<^term>\<open>x\<close>.
  \<phi>-Processor `set_param` processes this antecedent.\<close>

lemma ParamTag: "\<p>\<a>\<r>\<a>\<m> x" for x :: "'a::{}" unfolding ParamTag_def using TrueI .
lemma [elim!,\<phi>inhabitance_rule]: "\<p>\<a>\<r>\<a>\<m> x \<Longrightarrow> C \<Longrightarrow> C" .
lemma [cong]: "\<p>\<a>\<r>\<a>\<m> x \<longleftrightarrow> \<p>\<a>\<r>\<a>\<m> x" \<comment> \<open>Disable simplification on parameters\<close> ..

ML_file \<open>library/syntax/param.ML\<close>

subsection \<open>Proof Obligation\<close>

text \<open>See \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close> given in \<open>\<phi>\<close>-Logic Programming Reasoner.\<close>

subsection \<open>Judgement Obligation\<close>

definition Argument :: "'a::{} \<Rightarrow> 'a" ("\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _" [11] 10) where [iff]: "Argument x \<equiv> x"

lemma Argument_I[intro!]: "P \<Longrightarrow> Argument P" unfolding Argument_def .

text \<open>Antecedent \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P\<close> represents the wrapped antecedent \<^prop>\<open>P\<close>
  is a problem intended to be solved by users. Different with \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q\<close> where
  boolean \<^prop>\<open>Q\<close> is a pure assertion being a verification condition,
  the wrapped \<^prop>\<open>P\<close> is a judgement in the programming, such as a transformation of abstraction
  or a view shift or any others representing specific properties.

  In addition, \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P\<close> suppresses any attempts from the automatic reasoner. \<^prop>\<open>P\<close>
  will be protected as intact.
\<close>

subsection \<open>Reasoning Obligation\<close>

definition Do  :: \<open>prop \<Rightarrow> prop\<close> ("\<^bold>d\<^bold>o _"   [3] 2) where [iff]: \<open>Do  X \<equiv> X\<close>

text \<open>In a rule, \<^prop>\<open>\<^bold>d\<^bold>o A\<close> annotates the antecedent \<^prop>\<open>A\<close> is a reasoning task as a result
obtained from the reasoning, instead of a prerequisite condition of applying the rule.
During the reasoning process,

\<^item> once it encounters an antecedent \<^prop>\<open>A\<close> not wrapped by \<open>\<^bold>d\<^bold>o\<close>, \<^prop>\<open>A\<close> is evaluated immediately
  and once it fails the search branch backtracks;

\<^item> by contrast, once it encounters an antecedent \<^prop>\<open>\<^bold>d\<^bold>o A\<close> wrapped by \<open>\<^bold>d\<^bold>o\<close>, it means an obtained
  reasoning obligation as an outcome of the reasoning,
  just like \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close> meaning an extracted verification condition.
  So conforming to \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close>, no immediate reasoning work is invoked and the antecedent
  is returned and is given before the \<^schematic_prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> \<dots>\<close> in order,
  as an outcome of the reasoning,.

  For example, if during a reasoning process, two \<^prop>\<open>\<^bold>d\<^bold>o A1\<close> and \<^prop>\<open>\<^bold>d\<^bold>o A2\<close> are encountered in
  order, and if the reasoning succeeds, the final outcome would be
  \[ \<^schematic_prop>\<open>\<^bold>d\<^bold>o A1 \<Longrightarrow> \<^bold>d\<^bold>o A2 \<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> \<dots> \<Longrightarrow> Conclusion\<close> \]
\<close>

lemma Do_I: \<open>PROP P \<Longrightarrow> \<^bold>d\<^bold>o PROP P\<close> unfolding Do_def .
lemma Do_D: \<open>\<^bold>d\<^bold>o PROP P \<Longrightarrow> PROP P\<close> unfolding Do_def .

ML_file \<open>library/system/reasoners.ML\<close>

definition Do_embed :: \<open>bool \<Rightarrow> bool\<close> where \<open>Do_embed X \<equiv> X\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>Do (Trueprop P) \<equiv> Trueprop (Do_embed P)\<close>
  unfolding Do_def Do_embed_def .

\<phi>reasoner_ML ParamTag 1000 (\<open>\<p>\<a>\<r>\<a>\<m> ?P\<close>) = \<open>
  Phi_Reasoners.wrap (K Phi_Sys_Reasoner.defer_param_antecedent)
\<close>

\<phi>reasoner_ML Argument 1000 (\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t ?P\<close>) = \<open>
  Phi_Reasoners.wrap (K Phi_Sys_Reasoner.defer_antecedent)
\<close>

\<phi>reasoner_ML Do 1200 (\<open>\<^bold>d\<^bold>o (PROP ?P)\<close>) = \<open>
  Phi_Reasoners.wrap (K Phi_Sys_Reasoner.defer_antecedent)
\<close>

subsection \<open>Text Label\<close>

text \<open>This part presents a mechanism to encode text symbol inside sequent.
  It may be used anywhere needing some text annotation for any purpose.\<close>

paragraph \<open>Label tag\<close> text \<open>embeds any text string in the name of a lambda abstraction from
  \<^typ>\<open>unit\<close> to \<^typ>\<open>unit\<close>, i.e. term \<^verbatim>\<open>Abs ("embeded text", unit, Bound 0)\<close> if readers are familiar with
  the internal representation of terms in Isabelle.

  This way encodes text strings using machine string which reaches the optimal performance.
  A deficiency is it is unstable for \<alpha>-conversion. Fortunately, \<alpha>-conversion doesn't happen during
  the unification with a schematic variable, although the unification with another label makes
  the result undecidable.
\<close>

datatype label = LABEL_TAG "unit \<Rightarrow> unit"

lemma [cong]: "LABEL_TAG x \<equiv> LABEL_TAG x"  using reflexive .
lemma label_eq: "x = y" for x :: label by (cases x, cases y) auto

syntax "_LABEL_" :: "idt \<Rightarrow> label" ("LABEL _" [0] 1000)
translations "LABEL name" == "CONST LABEL_TAG (\<lambda>name. ())"


paragraph \<open>Label Input\<close> (*depreciated*)

definition LabelTag :: " label \<Rightarrow> bool" ("\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l _" [1000] 26) where "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<equiv> True"

text \<open>The \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> indicate \<^term>\<open>x\<close> is a \<^typ>\<open>label\<close> that should be set by user, e.g.,
  \<^prop>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l name \<Longrightarrow> do_something_relating name\<close>.
  The \<phi>-processor `set_label` processes the \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> antecedent.\<close>

lemma LabelTag: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x" unfolding LabelTag_def ..
lemma [elim!,\<phi>inhabitance_rule]: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<Longrightarrow> C \<Longrightarrow> C" by auto


paragraph \<open>Label Binding of Objects\<close>

definition Labelled :: "label \<Rightarrow> 'a::{} \<Rightarrow> 'a" where [iff]: "Labelled name x \<equiv> x"

lemma Labelled_def_sym: \<open>x::'a::{} \<equiv> Labelled name x\<close> unfolding Labelled_def .
lemma Labelled_I': \<open>PROP P \<Longrightarrow> PROP (Labelled name (PROP P))\<close> unfolding Labelled_def .
lemma Labelled_I : \<open>P \<Longrightarrow> PROP Trueprop (Labelled name P)\<close> unfolding Labelled_def .

syntax "_LABELED_" :: "idt \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>:/ (_)" [1000,11] 10)
translations "name\<^bold>: X" == "CONST Labelled (LABEL name) X"

syntax "_LABELED_PROP_" :: "idt \<Rightarrow> prop \<Rightarrow> prop" ("_\<^bold>:/ (_)" [1000,11] 10)
translations "_LABELED_PROP_ name X" => "CONST Labelled (LABEL name) X"

ML_file \<open>library/syntax/label.ML\<close>
ML_file \<open>library/tools/named_premises.ML\<close>


definition Labelled_embed :: "label \<Rightarrow> bool \<Rightarrow> bool" where "Labelled_embed name x \<equiv> x"

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>Labelled L (Trueprop P) \<equiv> Trueprop (Labelled_embed L P)\<close>
  unfolding Labelled_embed_def Labelled_def .

subsection \<open>General Syntax\<close>

definition Technical :: \<open>'a::{} \<Rightarrow> 'a\<close> ("TECHNICAL _" [17] 16) where \<open>Technical x \<equiv> x\<close>

lemma Technical_I : \<open>P \<Longrightarrow> Technical P\<close> unfolding Technical_def .
lemma Technical_I': \<open>PROP P \<Longrightarrow> PROP Technical P\<close> unfolding Technical_def .
lemma Technical_D : \<open>Technical P \<Longrightarrow> P\<close> unfolding Technical_def .
lemma Technical_D': \<open>PROP Technical P \<Longrightarrow> PROP P\<close> unfolding Technical_def .

optional_translations (\<phi>hide_techinicals)
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (CONST Trueprop (CONST Technical X)) Y"
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (CONST Trueprop (name\<^bold>: CONST Technical X)) Y"
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (CONST Technical X) Y"
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (name\<^bold>: CONST Technical X) Y"
  "L" <= "CONST Technical X\<heavy_comma> L"
  "R" <= "R \<heavy_comma> CONST Technical X"
  "R\<heavy_comma> L" <= "R \<heavy_comma> CONST Technical X\<heavy_comma> L"
  "\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<s>\<t>\<a>\<t>\<e>: XCONST Void" <= "\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<s>\<t>\<a>\<t>\<e>: TECHNICAL X"
  "\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<v>\<i>\<e>\<w>: XCONST Void" <= "\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<v>\<i>\<e>\<w>: TECHNICAL X"
  \<open>show hidden internal techinical constructs\<close>

declare [[\<phi>hide_techinicals,
          \<phi>premise_attribute [THEN Technical_D ] for \<open>Technical ?P\<close>,
          \<phi>premise_attribute [THEN Technical_D'] for \<open>PROP Technical ?P\<close>]]

definition Technical_embed :: \<open>bool \<Rightarrow> bool\<close> where \<open>Technical_embed X \<equiv> X\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>Technical (Trueprop P) \<equiv> Trueprop (Technical_embed P)\<close>
  unfolding Technical_def Technical_embed_def .

lemma [\<phi>inhabitance_rule]:
  \<open>Inhabited (TECHNICAL X) \<Longrightarrow> (Inhabited X \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Technical_def .

section \<open>Mechanisms\<close>

subsection \<open>Programming Modes\<close>

typedecl working_mode

consts working_mode_procedure   :: working_mode
       working_mode_implication :: working_mode
       working_mode_view_shift  :: working_mode

definition \<phi>Programming_Method :: \<open>prop \<Rightarrow> working_mode \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Programming_Method Target mode Programming_Deduction Post_Reasoning Future_Works
          \<equiv> (   PROP Programming_Deduction
            \<Longrightarrow> PROP Post_Reasoning
            \<Longrightarrow> PROP Future_Works
            \<Longrightarrow> PROP Target)\<close>

declare [[\<phi>reason_default_pattern
      \<open>PROP \<phi>Programming_Method ?T _ _ _ _\<close> \<Rightarrow> \<open>PROP \<phi>Programming_Method ?T _ _ _ _\<close> (100)
]]

lemma reason_programming:
  \<open> PROP \<phi>Programming_Method Target working_mode Programming_Deduction Post_Reasoning Future_Works
\<Longrightarrow> TERM working_mode
\<Longrightarrow> PROP Programming_Deduction
\<Longrightarrow> PROP Post_Reasoning
\<Longrightarrow> PROP Future_Works
\<Longrightarrow> PROP Target\<close>
  unfolding \<phi>Programming_Method_def
  subgoal premises prems using prems(1)[OF prems(3) prems(4) prems(5)] . .

ML_file \<open>library/system/Phi_Working_Mode.ML\<close>
ML_file \<open>library/system/Phi_Envir.ML\<close>


subsubsection \<open>Built-in Programming Methods\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method
            (Trueprop (X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P))
            working_mode_implication
            (\<And>\<CC>c. \<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l>\<^bold>: (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(\<CC>c) \<i>\<s> X) \<Longrightarrow> \<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(\<CC>c) \<i>\<s> Y \<s>\<u>\<b>\<j> P)
            (Trueprop True)
            (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def conjunction_imp all_conjunction Action_Tag_def
            Labelled_def
  using \<phi>make_implication .

lemma [\<phi>reason 1100 for \<open>PROP \<phi>Programming_Method (Trueprop (?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?var_P)) _ _ _ _\<close>]:
  \<open> PROP \<phi>Programming_Method
            (Trueprop (X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y))
            working_mode_implication
            (\<And>\<CC>c. \<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l>\<^bold>: (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(\<CC>c) \<i>\<s> X) \<Longrightarrow> \<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(\<CC>c) \<i>\<s> Y \<s>\<u>\<b>\<j> True)
            (Trueprop True)
            (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def conjunction_imp all_conjunction Action_Tag_def Labelled_def
  using \<phi>make_implication .

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method
            (Trueprop (X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P))
            working_mode_view_shift
            (\<And>\<CC>c \<RR>r. \<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l>\<^bold>: (\<v>\<i>\<e>\<w> \<CC>c [\<RR>r] \<i>\<s> X) \<Longrightarrow> \<v>\<i>\<e>\<w> \<CC>c [\<RR>r] \<i>\<s> Y \<s>\<u>\<b>\<j> P)
            (Trueprop True)
            (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def conjunction_imp all_conjunction Action_Tag_def Labelled_def
  using \<phi>make_view_shift .

lemma [\<phi>reason 1100 for \<open>PROP \<phi>Programming_Method (Trueprop (?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<a>\<n>\<d> ?var_P)) _ _ _ _\<close>]:
  \<open> PROP \<phi>Programming_Method
            (Trueprop (X \<s>\<h>\<i>\<f>\<t>\<s> Y))
            working_mode_view_shift
            (\<And>\<CC>c \<RR>r. \<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l>\<^bold>: (\<v>\<i>\<e>\<w> \<CC>c [\<RR>r] \<i>\<s> X) \<Longrightarrow> \<v>\<i>\<e>\<w> \<CC>c [\<RR>r] \<i>\<s> Y \<s>\<u>\<b>\<j> True)
            (Trueprop True)
            (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def conjunction_imp all_conjunction Action_Tag_def Labelled_def
  using \<phi>make_view_shift .

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method
            (Trueprop (\<p>\<r>\<o>\<c> G \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
            working_mode_procedure
            (\<And>\<SS>s \<RR>r. \<phi>\<i>\<n>\<i>\<t>\<i>\<a>\<l>\<^bold>: (\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<SS>s [\<RR>r] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> X) \<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> G \<o>\<n> \<SS>s [\<RR>r] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E)
            (Trueprop True)
            (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def conjunction_imp all_conjunction Action_Tag_def Labelled_def
  using \<phi>reassemble_proc_final .

hide_fact \<phi>make_implication \<phi>make_view_shift \<phi>reassemble_proc_final


subsubsection \<open>General Rules Normalizing Programming Methods\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (Trueprop Q) M D R F
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (P \<longrightarrow> Q)) M (P \<Longrightarrow> PROP D) (P \<Longrightarrow> PROP R) (P \<Longrightarrow> PROP F)\<close>
  unfolding \<phi>Programming_Method_def
proof (intro impI)
  assume A: \<open>PROP D \<Longrightarrow> PROP R \<Longrightarrow> PROP F \<Longrightarrow> Q\<close>
    and  D: \<open>P \<Longrightarrow> PROP D\<close>
    and  R: \<open>P \<Longrightarrow> PROP R\<close>
    and  F: \<open>P \<Longrightarrow> PROP F\<close>
    and  P: \<open>P\<close>
  show \<open>Q\<close> using A[OF D[OF P] R[OF P] F[OF P]] .
qed

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method Q M D R F
\<Longrightarrow> PROP \<phi>Programming_Method (PROP P \<Longrightarrow> PROP Q) M (PROP P \<Longrightarrow> PROP D) (PROP P \<Longrightarrow> PROP R)
                             (PROP P \<Longrightarrow> PROP F)\<close>
  unfolding \<phi>Programming_Method_def
proof -
  assume A: \<open>PROP D \<Longrightarrow> PROP R \<Longrightarrow> PROP F \<Longrightarrow> PROP Q\<close>
    and  D: \<open>PROP P \<Longrightarrow> PROP D\<close>
    and  R: \<open>PROP P \<Longrightarrow> PROP R\<close>
    and  F: \<open>PROP P \<Longrightarrow> PROP F\<close>
    and  P: \<open>PROP P\<close>
  show \<open>PROP Q\<close> using A[OF D[OF P] R[OF P] F[OF P]] .
qed

lemma \<phi>Programming_Method_All:
  \<open> (\<And>x. PROP \<phi>Programming_Method (Trueprop (P x)) M (D x) (R x) (F x))
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (All P)) M (\<And>x. PROP D x) (\<And>x. PROP R x) (\<And>x. PROP F x)\<close>
  unfolding \<phi>Programming_Method_def
proof (intro allI)
  fix x :: 'a
  assume A: \<open>\<And>x. PROP D x \<Longrightarrow> PROP R x \<Longrightarrow> PROP F x \<Longrightarrow> P x\<close>
    and  D: \<open>\<And>x. PROP D x\<close>
    and  R: \<open>\<And>x. PROP R x\<close>
    and  F: \<open>\<And>x. PROP F x\<close>
  show \<open>P x\<close> using A[OF D R F] .
qed

lemma \<phi>Programming_Method_ALL:
  \<open> (\<And>x. PROP \<phi>Programming_Method (P x) M (D x) (R x) (F x))
\<Longrightarrow> PROP \<phi>Programming_Method (\<And>x. PROP P x) M (\<And>x. PROP D x) (\<And>x. PROP R x) (\<And>x. PROP F x)\<close>
  unfolding \<phi>Programming_Method_def
proof -
  fix x :: 'a
  assume A: \<open>\<And>x. PROP D x \<Longrightarrow> PROP R x \<Longrightarrow> PROP F x \<Longrightarrow> PROP P x\<close>
    and  D: \<open>\<And>x. PROP D x\<close>
    and  R: \<open>\<And>x. PROP R x\<close>
    and  F: \<open>\<And>x. PROP F x\<close>
  show \<open>PROP P x\<close> using A[OF D R F] .
qed

\<phi>reasoner_ML \<open>\<phi>Programming_Method (Trueprop (All P))\<close> 1000
  (\<open>PROP \<phi>Programming_Method (Trueprop (All ?P)) _ _ _ _\<close>)
  = \<open>fn (ctxt,sequent) =>
  let val _ $ (_ $ (_ $ P)) $ _ $ _ $ _ $ _ = Thm.major_prem_of sequent
      fun rename N' (Abs ("x",T,X)) = Abs (N',T,X)
        | rename N' (X $ Y) = rename N' X $ rename N' Y
        | rename _ X = X
      val rule = @{thm \<phi>Programming_Method_All}
      val rule' = case P of Abs (N,_,_) => Thm.renamed_prop (rename N (Thm.prop_of rule)) rule
                          | _ => rule
  in Phi_Reasoner.single_RS rule' (ctxt,sequent)
  end
\<close>

\<phi>reasoner_ML \<open>\<phi>Programming_Method (Pure.all P)\<close> 1000
  (\<open>PROP \<phi>Programming_Method (Pure.all ?P) _ _ _ _\<close>)
  = \<open>fn (ctxt,sequent) =>
  let val _ $ (_ $ P) $ _ $ _ $ _ $ _ = Thm.major_prem_of sequent
      fun rename N' (Abs ("x",T,X)) = Abs (N',T,X)
        | rename N' (X $ Y) = rename N' X $ rename N' Y
        | rename _ X = X
      val rule = @{thm \<phi>Programming_Method_ALL}
      val rule' = case P of Abs (N,_,_) => Thm.renamed_prop (rename N (Thm.prop_of rule)) rule
                          | _ => rule
  in Phi_Reasoner.single_RS rule' (ctxt,sequent)
  end
\<close>

hide_fact \<phi>Programming_Method_All \<phi>Programming_Method_ALL


subsection \<open>Automation\<close>

named_theorems \<phi>sledgehammer_simps \<open>Simplification rules used before applying slegehammer automation\<close>

ML_file \<open>library/tools/sledgehammer_solver.ML\<close>


subsection \<open>Ad-hoc Overload\<close>

ML_file \<open>library/system/app_rules.ML\<close>

attribute_setup \<phi>overload = \<open>Scan.lift (Parse.and_list1 Phi_App_Rules.name_position) >> (fn names =>
  Thm.declaration_attribute (fn th => fold (Phi_App_Rules.overload th) names))\<close>

\<phi>overloads D \<open>Destructive subtyping rules\<close>
\<phi>overloads cast \<open>Transform the content of a container\<close>

text \<open>
Convention of Overloading Distance:

\<^item> 0. Transparent, the matching is perfect.
\<^item> 1. Almost Transparent, but still incomparable to the really transparent, meaning tiny cost still
      exists, maybe in time or reasoning only
\<^item> 3. Expected Conversion: some conversion and therefore information lost is inevitable but it is
      expected so can be accepted.
\<^item> 5. Less Expected Conversion: in some (rare) case the information lost can be severe
        but generally still can be accepted for most of usages.
\<^item> 9. Slightly Aggressive.
\<^item> 12. Aggressive in most of the situations.
\<^item> 15. Bad.

Threshold Cost Always!
\<close>

subsection \<open>Synthesis\<close>

text \<open>The synthesis involves not only making a program but also finding a view shift or a ToA.

On a ready state of a construction like \<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S\<close> or \<open>(\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S)\<close>,
the synthesis mechanism makes some program or find some ToA to bring or to make the given
specification come true. Example: given the specification \<open>X\<close>, the synthesis mechanism is expected
to deduce \<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S'\<heavy_comma> X\<close> or \<open>(\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S'\<heavy_comma> X)\<close>. The state \<open>S\<close> may be
changed to \<open>S'\<close>, but the change is minimal and only necessary for synthesising the \<open>X\<close>.

On a state sequent having some antecedent like \<open>P \<Longrightarrow> Q\<close>, the synthesis mechanism is expected
to solve the antecedent \<open>P\<close> according to the given specification from user.
For example, the \<open>P\<close> can be the specification of a procedure to be programmed, like the guard
\<open>P \<equiv> \<p>\<r>\<o>\<c> ?f \<lbrace> X \<longmapsto> ?cond \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close> of the branch statement. In this case
the mechanism is to synthesis that guard according to the user-given specification, like \<open>$x > 2\<close>
to synthesis \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> X \<longmapsto> $x > 2 \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace>\<close>.
\<close>

definition DoSynthesis :: \<open>'a \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>DoSynthesis term sequent result \<equiv> (PROP sequent \<Longrightarrow> PROP result)\<close>

definition Synthesis_Parse :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  where \<open>Synthesis_Parse input parsed \<longleftrightarrow>  True\<close>

declare [[\<phi>reason_default_pattern \<open>Synthesis_Parse ?in _\<close> \<Rightarrow> \<open>Synthesis_Parse ?in _\<close> (100)]]

lemma \<phi>synthesis:
  \<open> PROP sequent
\<Longrightarrow> PROP DoSynthesis X sequent result
\<Longrightarrow> PROP result\<close>
  unfolding DoSynthesis_def .

text \<open>
  Overall, the synthesis procedure consists of 2 phases.
  The first phase is a pre-process parsing the user input. Performed by antecedent
    \<^schematic_prop>\<open>Synthesis_Parse input ?parsed\<close>,
  it rewrites the user \<^term>\<open>input\<close> to \<^schematic_term>\<open>?parsed\<close>.

  The rewrite process enables user to input partially instead of always giving the complete
  assertion every time, for example, just the abstract object \<^term>\<open>x\<close> to
  denote \<^pattern_term>\<open>x \<Ztypecolon> _\<close> and leave the type unspecified to accept anything.
  For example, user may input just an abstract object \<^term>\<open>x\<close> to mean to
    synthesis \<^term>\<open>x \<Ztypecolon> T\<close> for some unspecified \<^term>\<open>T\<close>;
    user may also input \<^term>\<open>0::nat\<close> to mean to synthesis \<^term>\<open>0 \<Ztypecolon> Natural_Number\<close>.

  One can disable \<phi>_synthesis_parsing to disable this feature.

  The second phase does the real work, synthesising the \<open>?parsed\<close>.

  As the given specifications are on abstraction, ways to synthesis an abstract specification
  are many and not uniquely determined syntactically of course.
  Therefore we apply an A* algorithm according to explicitly annotated cost. The algorithm finds the
  solution having the minimum cost.

  Besides, in order to reduce the search space, we assume a large amount of operators having
  specific programs to refine them (such as plus and subtract),
  so that synthesising a composite expression can be split structurally (and syntactically) to
  several small problems for synthesising its operands and for finding a proper program refining the operator.

  To find such a proper instantiation requires to know the abstraction relations of the operands,
  but it is not an easy problem because transformation of abstraction can happen at every application.
  The choice of the abstraction relation of a sub-expression affects the synthesis of the inner
  operations of the sub-expression and also the outer operation using it.
  Choices of the intermediate abstraction relations have to be counted globally.

  Therefore the synthesis reasoning also contains two phases. The first phase split the synthesis
  problem for the original big composite expression down to several small problems of
  choosing the intermediate abstraction relations and instantiating proper refinement for each
  operators. And the second phase is an heuristic search finding the optimum choices
  and the instantiations.
  The first phase is a greedy algorithm as what we assumed.
  The first-reached solution (according to the PLPR priority of the configured rules) is adopted
  and the remains are dropped.
  The second phase is exhaustive for every possible search branches (with pruning).

  Candidates of the second phase are measured by the distance of the transformation used inside.
  An ideal solution is to involve no transformation at all.
  A transformation is an edge and each one is labelled with a distance manually.
  The distance of a path \<open>e\<^sub>1;e\<^sub>2;\<dots>;e\<^sub>n\<close> is the maximum distance of its edges (transformations),
  \<open>max{e\<^sub>i}\<close>.

\<close>

definition DoSynthesis_embed :: \<open>'a \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>DoSynthesis_embed term sequent result \<equiv> (sequent \<longrightarrow> result)\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>DoSynthesis term (Trueprop sequent) (Trueprop result) \<equiv> Trueprop (DoSynthesis_embed term sequent result)\<close>
  unfolding DoSynthesis_def DoSynthesis_embed_def atomize_imp .

definition Optimal_Synthesis :: \<open>prop \<Rightarrow> prop\<close> ("OPTIMAL'_SYNTHESIS _" [3] 2)
  where \<open>Optimal_Synthesis P \<equiv> P\<close>
definition End_Optimal_Synthesis where \<open>End_Optimal_Synthesis \<longleftrightarrow> True\<close>

lemma Do_Optimal_Synthesis:
  \<open> PROP P
\<Longrightarrow> PROP Optimal_Synthesis P\<close>
  unfolding Optimal_Synthesis_def .

lemma End_Optimal_Synthesis_I:
  \<open>End_Optimal_Synthesis\<close> unfolding End_Optimal_Synthesis_def ..

\<phi>reasoner_ML End_Optimal_Synthesis 1000 (\<open>End_Optimal_Synthesis\<close>) = \<open>
   apsnd (fn th => @{thm End_Optimal_Synthesis_I} RS th)
#> PLPR_Optimum_Solution.finish
\<close>

\<phi>reasoner_ML Optimal_Synthesis 1000 (\<open>PROP Optimal_Synthesis _\<close>) = \<open>fn (ctxt,sequent) =>
  Phi_Sys_Reasoner.gen_defer_antecedent (fn _ =>
    find_index (fn \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>End_Optimal_Synthesis\<close>, _)) => true
                 | _ => false)
  ) (@{thm Do_Optimal_Synthesis} RS sequent)
  |> Seq.map (pair ctxt)
\<close>


subsubsection \<open>Parse the Term to be Synthesised\<close>

lemma [\<phi>reason 9999 for
  \<open>Synthesis_Parse (?X'::?'ret \<Rightarrow> assn) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse X X\<close> for X :: \<open>'ret \<Rightarrow> assn\<close>
  \<comment> \<open>We do not need to rewrite the input once it is already an assertion\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 9999 for
  \<open>Synthesis_Parse (?X'::assn) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse X (\<lambda>_. X)\<close> for X :: \<open>assn\<close>
  \<comment> \<open>We do not need to rewrite the input once it is already an assertion\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 10
    for \<open>Synthesis_Parse ?x (?Y::?'ret \<Rightarrow> assn)\<close>
    except \<open>Synthesis_Parse (?x \<Ztypecolon> ?T) ?Y\<close>
           \<open>Synthesis_Parse (?x::assn) ?Y\<close>
           \<open>Synthesis_Parse (?x::?'ret \<Rightarrow> assn) ?Y\<close>
]:
  \<open>Synthesis_Parse x (\<lambda>ret. (x \<Ztypecolon> X ret :: assn))\<close>
  \<comment> \<open>The fallback parser recognizes the input to be the abstract object and leaves
      the \<phi>-type unspecified to be arbitrarily anything.\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 20
  for \<open>Synthesis_Parse (numeral ?n::?'bb::numeral) ?X\<close>
      \<open>Synthesis_Parse (0::?'cc::zero) ?X\<close>
      \<open>Synthesis_Parse (1::?'dd::one) ?X\<close>
  except \<open>Synthesis_Parse (?n::nat) ?X\<close>
]:
  \<open> Synthesis_Parse (n :: nat) X
\<Longrightarrow> Synthesis_Parse n X\<close>
 \<comment> \<open>Given any input of 0, 1, or \<^schematic_term>\<open>numeral ?sth\<close>, of a schematic type
      unspecified by user, the input is regarded as of natural number type.\<close>
  unfolding Synthesis_Parse_def
  ..

lemma [\<phi>reason 20 for \<open>Synthesis_Parse (?T :: ?'ret2 \<Rightarrow> (fiction,?'x) \<phi>) (?Y::?'ret \<Rightarrow> assn)\<close>]:
  \<open> Synthesis_Parse T (\<lambda>ret. x \<Ztypecolon> T ret :: assn) \<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 20 for \<open>Synthesis_Parse (?T :: (fiction,?'x) \<phi>) (?Y::?'ret \<Rightarrow> assn)\<close>]:
  \<open> Synthesis_Parse T (\<lambda>ret. x \<Ztypecolon> T :: assn) \<close>
  unfolding Synthesis_Parse_def ..


subsubsection \<open>Tagging the target of a synthesis rule\<close>

(* definition Synthesis :: \<open>'a set \<Rightarrow> 'a set\<close> ("SYNTHESIS _" [17] 16) where [iff]: \<open>Synthesis S = S\<close> *)

consts synthesis :: action

text \<open>
  Only procedure rules need to be tagged by \<^const>\<open>synthesis\<close>. The view shift and the ToA do not.


  Occurring in the post-condition of a rule (either a procedure specification or a view shift
    or an implication), SYNTHESIS tags the target of the rule, i.e., the construct that this
    procedure or this transformation synthesises.
  For example, \<^prop>\<open>\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> @action synthesis\<close>
    represents the procedure f generates
    something that meets Z, and it is a synthesis rule for synthesising the target \<open>Z\<close>.

  Occurring during reasoning, antecedent like
    \<^schematic_prop>\<open>\<p>\<r>\<o>\<c> ?f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> \<blangle> Z ret \<brangle> \<rbrace> @action synthesis \<Longrightarrow> C\<close>,
  represents a reasoning task to find some procedure or some transformation to synthesis
  something meeting Z.

TODO: update the comment.
\<close>

declare [[\<phi>reason_default_pattern
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close> \<Rightarrow>
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?Z ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>    (100)
  and \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R  \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close> \<Rightarrow>
      \<open>\<p>\<r>\<o>\<c> _ \<lbrace> ?X \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?x \<Ztypecolon> _ \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>    (110)
  and \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> ?Y \<brangle> \<a>\<n>\<d> _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> ?Y \<brangle> \<a>\<n>\<d> _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ * \<blangle> ?Y \<brangle> \<a>\<n>\<d> _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ * \<blangle> ?Y \<brangle> \<a>\<n>\<d> _\<close>    (100)
]]

ML \<open>
structure Post_Synthesis_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>post_synthesis_simp\<close>
  val comment = "Rules simplifying after the synthesis operation."
)
\<close>

consts post_synthesis_simp :: mode

\<phi>reasoner_ML post_synthesis_simp 1200 (\<open>Simplify post_synthesis_simp ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_by_ss' NONE Post_Synthesis_SS.get'\<close>

subsubsection \<open>Synthesis Operations\<close>

paragraph \<open>Fallbacks\<close>

text \<open>On programming mode, the synthesis operation always tries to find a procedure.
  View shifts have to be wrapped in a procedure. The following is an automatic wrapper. \<close>

lemma Synthesis_Proc_fallback_VS
  [\<phi>reason 10 for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. _ \<heavy_comma> \<blangle> ?X' ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>]:
  \<open> S1 \<s>\<h>\<i>\<f>\<t>\<s> S2\<heavy_comma> \<blangle> X' \<brangle> \<a>\<n>\<d> Any
\<Longrightarrow> \<p>\<r>\<o>\<c> Return \<phi>V_none \<lbrace> S1 \<longmapsto> \<lambda>v. S2\<heavy_comma> \<blangle> X' \<brangle> \<rbrace> @action synthesis\<close>
  unfolding \<phi>Procedure_def Return_def det_lift_def View_Shift_def by simp

text \<open>The fallback from VS to IMP is given by @{thm view_shift_by_implication}\<close>


paragraph \<open>Construction on Programming\<close>

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?S1)) ?RET\<close>
]:
  " \<r>CALL Synthesis_Parse X X'
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> S1 \<longmapsto> \<lambda>v. S2\<heavy_comma> \<blangle> X' v \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> Begin_Optimum_Solution
\<Longrightarrow> End_Optimal_Synthesis
\<Longrightarrow> Simplify post_synthesis_simp X'' X'
\<Longrightarrow> Simplify (assertion_simps ABNORMAL) E'' E
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S1))
      (Trueprop (\<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>v. S2\<heavy_comma> X'' v) \<t>\<h>\<r>\<o>\<w>\<s> E''))"
  unfolding FOCUS_TAG_def Action_Tag_def DoSynthesis_def Simplify_def
  using \<phi>apply_proc by fastforce

paragraph \<open>Construction on View Shifting\<close>

text \<open>On view shifting mode, the synthesis operation tries to find a view shifting.\<close>

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (Trueprop (\<v>\<i>\<e>\<w> ?blk [?H] \<i>\<s> ?S1)) ?RET\<close>
]:
  " \<r>CALL Synthesis_Parse X X'
\<Longrightarrow> S1 \<s>\<h>\<i>\<f>\<t>\<s> S2\<heavy_comma> \<blangle> X' \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Begin_Optimum_Solution
\<Longrightarrow> End_Optimal_Synthesis
\<Longrightarrow> \<r>Success
\<Longrightarrow> Simplify post_synthesis_simp X'' X'
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<v>\<i>\<e>\<w> blk [H] \<i>\<s> S1))
      (Trueprop ((\<v>\<i>\<e>\<w> blk [H] \<i>\<s> S2\<heavy_comma> X'') \<and> P))"
  unfolding FOCUS_TAG_def Action_Tag_def DoSynthesis_def Simplify_def
  using \<phi>apply_view_shift
  by metis

paragraph \<open>Construction on ToA\<close>

text \<open>On view shifting mode, the synthesis operation tries to find a view shifting.\<close>

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (Trueprop (\<v>\<i>\<e>\<w> ?blk [?H] \<i>\<s> ?S1)) ?RET\<close>
]:
  " \<r>CALL Synthesis_Parse X X'
\<Longrightarrow> S1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> S2\<heavy_comma> \<blangle> X' \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Begin_Optimum_Solution
\<Longrightarrow> End_Optimal_Synthesis
\<Longrightarrow> \<r>Success
\<Longrightarrow> Simplify post_synthesis_simp X'' X'
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S1))
      (Trueprop ((\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S2\<heavy_comma> X'') \<and> P))"
  unfolding FOCUS_TAG_def Action_Tag_def DoSynthesis_def Simplify_def
  by (meson \<phi>apply_implication_impl)


paragraph \<open>Solving an antecedent by Synthesis\<close>

(*TODO: rename this to Synthesis_of*)
definition Synthesis_by :: \<open>'a \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>Synthesis_by X Q \<equiv> Q\<close>

text \<open>If the synthesis procedure is invoked on an inference rule like \<^prop>\<open>P \<Longrightarrow> Q\<close>,
  it invokes the Synthesis_by procedure which tries to solve the antecedent \<^prop>\<open>P\<close>
    under the instruction of the given \<^term>\<open>X\<close> to be synthesised,
  by reasoning antecedent \<^prop>\<open>PROP Synthesis_by X P\<close>.

  Note the procedure of Synthesis_by will not trigger Synthesis_Parse because this
    generic procedure does not the type to be synthesised. Lacking of this type information
    affects the preciseness of Synthesis_Parse rule. The procedure of Synthesis_Parse
    should be triggered at the entry point of each specific operation, where the expected type
    is clear.\<close>

definition Synthesis_by_embed :: \<open>'a \<Rightarrow> bool \<Rightarrow> bool\<close> where \<open>Synthesis_by_embed X Q \<equiv> Q\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>Synthesis_by X (Trueprop P) \<equiv> Trueprop (Synthesis_by_embed X P)\<close>
  unfolding Synthesis_by_embed_def Synthesis_by_def .

declare [[\<phi>reason_default_pattern \<open>PROP Synthesis_by ?X ?Q\<close> \<Rightarrow> \<open>PROP Synthesis_by ?X ?Q\<close> (100)]]

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (PROP ?P \<Longrightarrow> PROP ?Q) ?RET\<close>
]:
  " PROP Synthesis_by X (PROP P)
\<Longrightarrow> Begin_Optimum_Solution
\<Longrightarrow> End_Optimal_Synthesis
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP DoSynthesis X (PROP P \<Longrightarrow> PROP Q) (PROP Q)"
  unfolding DoSynthesis_def Synthesis_by_def Action_Tag_def .

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. PROP Synthesis_by X (PROP P x))
\<Longrightarrow> PROP Synthesis_by X (\<And>x. PROP P x)\<close>
  unfolding Synthesis_by_def .

lemma [\<phi>reason 1200]:
  \<open>(PROP P \<Longrightarrow> PROP Synthesis_by X (PROP Q))
\<Longrightarrow> PROP Synthesis_by X (PROP P \<Longrightarrow> PROP Q)\<close>
  unfolding Synthesis_by_def .

lemma [\<phi>reason 1210]:
  \<open> \<r>CALL Synthesis_Parse X' X
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> X ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> Simplify post_synthesis_simp X'' X
\<Longrightarrow> Simplify (assertion_simps ABNORMAL) E'' E
\<Longrightarrow> PROP Synthesis_by X' (Trueprop (\<p>\<r>\<o>\<c> f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> X'' ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'' ))\<close>
  unfolding Synthesis_by_def Action_Tag_def Simplify_def by fastforce

lemma [\<phi>reason 1200]:
  \<open> \<r>CALL Synthesis_Parse X' X
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> X ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> Simplify post_synthesis_simp X'' X
\<Longrightarrow> Simplify (assertion_simps ABNORMAL) E'' E
\<Longrightarrow> PROP Synthesis_by X' (Trueprop (\<p>\<r>\<o>\<c> f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> X'' ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'' ))\<close>
  unfolding Synthesis_by_def Action_Tag_def Simplify_def by fastforce

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. PROP Synthesis_by X (Trueprop (P x)))
\<Longrightarrow> PROP Synthesis_by X (Trueprop (All P))\<close>
  unfolding Synthesis_by_def Action_Tag_def ..

lemma [\<phi>reason 1200]:
  \<open> (P \<Longrightarrow> PROP Synthesis_by X (Trueprop Q))
\<Longrightarrow> PROP Synthesis_by X (Trueprop (P \<longrightarrow> Q))\<close>
  unfolding Synthesis_by_def Action_Tag_def ..


subsubsection \<open>General Synthesis Rules\<close>

lemma [\<phi>reason 1200]:
  \<open> \<p>\<r>\<o>\<c> F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> f x \<brangle> \<Ztypecolon> T ret \<rbrace> @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> case_named f (tag x) \<brangle> \<Ztypecolon> T ret \<rbrace> @action synthesis\<close>
  by simp

lemma [\<phi>reason 1200]:
  \<open> PROP Synthesis_by X (Trueprop P)
\<Longrightarrow> PROP Synthesis_by X (Trueprop (\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P))\<close>
  unfolding Argument_def .

lemma [\<phi>reason 1200]:
  \<open> PROP Synthesis_by X (PROP P)
\<Longrightarrow> PROP Synthesis_by X (PROP (Argument P))\<close>
  unfolding Argument_def .

lemma [\<phi>reason 1200 for \<open>PROP Synthesis_by ?X (Trueprop (_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X' \<a>\<n>\<d> _))\<close>]:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> Simplify post_synthesis_simp X' X
\<Longrightarrow> PROP Synthesis_by X (Trueprop (A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X' \<a>\<n>\<d> P))\<close>
  unfolding Synthesis_by_def Simplify_def by meson

lemma [\<phi>reason 1200 for \<open>PROP Synthesis_by ?X (Trueprop (_ \<s>\<h>\<i>\<f>\<t>\<s> ?X' \<a>\<n>\<d> _))\<close>]:
  \<open> A \<s>\<h>\<i>\<f>\<t>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> Simplify post_synthesis_simp X' X
\<Longrightarrow> PROP Synthesis_by X (Trueprop (A \<s>\<h>\<i>\<f>\<t>\<s> X' \<a>\<n>\<d> P))\<close>
  unfolding Synthesis_by_def Simplify_def by meson

lemma [\<phi>reason 1500 for \<open>PROP Synthesis_by ?X (\<And>a. _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> ?P)\<close>]:
  \<open> (\<And>a. A a \<i>\<m>\<p>\<l>\<i>\<e>\<s> X a \<a>\<n>\<d> P)
\<Longrightarrow> Simplify post_synthesis_simp X' X
\<Longrightarrow> PROP Synthesis_by X (\<And>a. A a \<i>\<m>\<p>\<l>\<i>\<e>\<s> X' a \<a>\<n>\<d> P)\<close>
  unfolding Synthesis_by_def Simplify_def by meson

lemma [\<phi>reason 1500 for \<open>PROP Synthesis_by ?X (\<And>a. ?A a \<s>\<h>\<i>\<f>\<t>\<s> ?B a \<a>\<n>\<d> ?P)\<close>]:
  \<open> (\<And>a. A a \<s>\<h>\<i>\<f>\<t>\<s> X a \<a>\<n>\<d> P)
\<Longrightarrow> Simplify post_synthesis_simp X' X
\<Longrightarrow> PROP Synthesis_by X (\<And>a. A a \<s>\<h>\<i>\<f>\<t>\<s> X' a \<a>\<n>\<d> P)\<close>
  unfolding Synthesis_by_def Simplify_def by meson

lemma [\<phi>reason 1500 for \<open>PROP Synthesis_by ?X (\<And>a. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> ?P)\<close>]:
  \<open> (\<And>a. A a \<i>\<m>\<p>\<l>\<i>\<e>\<s> X a \<a>\<n>\<d> P)
\<Longrightarrow> Simplify post_synthesis_simp X' X
\<Longrightarrow> PROP Synthesis_by X (\<And>a. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A a \<i>\<m>\<p>\<l>\<i>\<e>\<s> X' a \<a>\<n>\<d> P)\<close>
  unfolding Synthesis_by_def Argument_def Simplify_def by meson

lemma [\<phi>reason 1500 for \<open>PROP Synthesis_by ?X (\<And>a. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t ?A a \<s>\<h>\<i>\<f>\<t>\<s> ?B a \<a>\<n>\<d> ?P)\<close>]:
  \<open> (\<And>a. A a \<s>\<h>\<i>\<f>\<t>\<s> X a \<a>\<n>\<d> P)
\<Longrightarrow> Simplify post_synthesis_simp X' X
\<Longrightarrow> PROP Synthesis_by X (\<And>a. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A a \<s>\<h>\<i>\<f>\<t>\<s> X' a \<a>\<n>\<d> P)\<close>
  unfolding Synthesis_by_def Argument_def Simplify_def by meson

subsection \<open>Application\<close>
\<comment> \<open>of procedures, ToA, and any other things\<close>

text \<open>It is a generic framework allowing to apply general things on the state sequent.
These general things named \<^emph>\<open>application\<close> includes
\<^item> procedures --- therefore appending a procedure on the current construction
\<^item> transformations of abstraction and view shifts --- transforming the abstract state
\<^item> actions --- meta operations combining several applications or transformations, cf. section Action.
\<close>

definition \<phi>Application :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application App_Rules State Result
                      \<equiv> (PROP State \<Longrightarrow> PROP App_Rules \<Longrightarrow> PROP Result)\<close>

(* lemma \<phi>Application_cong[cong]:
  \<open> App1 \<equiv> App2 \<Longrightarrow> Stat1 \<equiv> Stat2 \<Longrightarrow> Res1 \<equiv> Res2
\<Longrightarrow> \<phi>Application App1 Stat1 Res1 \<equiv> \<phi>Application App2 Stat2 Res2\<close>
  unfolding \<phi>Application *)

lemma \<phi>application:
  \<open> PROP Apps
\<Longrightarrow> PROP State
\<Longrightarrow> PROP \<phi>Application Apps State Result
\<Longrightarrow> \<r>Success
\<Longrightarrow> PROP Result\<close>
  unfolding \<phi>Application_def Pure.prop_def Optimum_Solution_def Optimum_Among_def .

definition \<phi>Application_Conv :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application_Conv P Q \<equiv> (PROP P \<Longrightarrow> PROP Q)\<close>

lemma \<phi>Application_Conv:
  \<open> PROP P
\<Longrightarrow> PROP \<phi>Application_Conv P Q
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP Q\<close>
  unfolding \<phi>Application_Conv_def .

ML_file \<open>library/system/application.ML\<close>


subsubsection \<open>Common Rules of Application Methods\<close>

(*
lemma \<phi>Application_opt_L:
  \<open> Stop_Divergence
\<Longrightarrow> PROP \<phi>Application (PROP App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (Optimum_Among (PROP App &&& PROP Apps)) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def conjunction_imp Optimum_Among_def .

lemma \<phi>Application_opt_R:
  \<open> PROP \<phi>Application (Optimum_Among Apps) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (Optimum_Among (PROP App &&& PROP Apps)) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def conjunction_imp Optimum_Among_def .

declare [[\<phi>reason 1010 \<phi>Application_opt_L \<phi>Application_opt_R for
            \<open>PROP \<phi>Application (Optimum_Among (PROP ?App &&& PROP ?Apps)) ?State ?Result\<close>]]

lemma [\<phi>reason 1000 \<phi>Application_opt_L \<phi>Application_opt_R for
            \<open>PROP \<phi>Application (Optimum_Among ?App) ?State ?Result\<close>]:
  \<open> Stop_Divergence
\<Longrightarrow> PROP \<phi>Application App State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (Optimum_Among App) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def Optimum_Among_def .
*)

lemma [\<phi>reason 80 for \<open>
  PROP \<phi>Application (PROP ?App &&& PROP ?Apps) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application (PROP App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (PROP App &&& PROP Apps) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def conjunction_imp .

lemma [\<phi>reason 70 for \<open>
  PROP \<phi>Application (PROP ?App &&& PROP ?Apps) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application (PROP Apps) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (PROP App &&& PROP Apps) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def conjunction_imp .

lemma [\<phi>reason 1100 for \<open>
  PROP \<phi>Application (PROP ?Prem \<Longrightarrow> PROP ?App) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application (PROP App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (PROP Prem \<Longrightarrow> PROP App) State (PROP Prem \<Longrightarrow> PROP Result)\<close>
  unfolding prop_def \<phi>Application_def imp_implication
  subgoal premises prems using prems(1)[OF  prems(2) prems(3)[OF prems(4)]] . .

lemma [\<phi>reason 1100 for \<open>
  PROP \<phi>Application (Trueprop (?Prem \<longrightarrow> ?App)) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop App) State Result
\<Longrightarrow> PROP \<phi>Application (Trueprop (Prem \<longrightarrow> App)) State (Prem \<Longrightarrow> PROP Result)\<close>
  unfolding prop_def \<phi>Application_def imp_implication
  subgoal premises prems using prems(1)[OF prems(2) prems(3)[OF prems(4)]] . .

lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application (Pure.all ?App) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application (PROP (App x)) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (Pure.all App) State (PROP Result)\<close>
  unfolding \<phi>Application_def
  subgoal premises prems
    apply (tactic \<open>Tactic.resolve_tac \<^context>
      [((Thm.forall_elim \<^cterm>\<open>x\<close> @{thm prems(3)}) RS @{thm prems(1)[OF prems(2)]})] 1\<close>) . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application (Trueprop App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (App @action Act) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def Action_Tag_def
  subgoal premises prems using prems(1)[OF prems(2) prems(3)] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application (Trueprop (\<forall>a b. App (a,b))) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (Trueprop (All App)) State (PROP Result)\<close>
  unfolding split_paired_All .

lemma [\<phi>reason 1100]:
  \<open> PROP \<phi>Application (Trueprop (App x)) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (Trueprop (All App)) State (PROP Result)\<close>
  unfolding \<phi>Application_def
  subgoal premises p by (rule p(1), rule p(2), rule p(3)[THEN spec[where x=x]]) .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application (Trueprop (\<forall>a. App (\<phi>V_pair x a))) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application (Trueprop (All App)) State (PROP Result)\<close>
  unfolding \<phi>Application_def
  subgoal premises p by (rule p(1), rule p(2), rule, rule p(3)[THEN spec]) .




subsubsection \<open>Application as a Resolution\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Application_Conv X' X
\<Longrightarrow> PROP \<phi>Application X' (PROP X \<Longrightarrow> PROP Y) Y\<close>
  unfolding \<phi>Application_def \<phi>Application_Conv_def
  subgoal premises prems using prems(3)[THEN prems(1), THEN prems(2)] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (Trueprop X') (Trueprop X)
\<Longrightarrow> PROP \<phi>Application (Trueprop X') (Trueprop (X \<longrightarrow> Y)) (Trueprop Y)\<close>
  unfolding \<phi>Application_def \<phi>Application_Conv_def by blast

lemma [\<phi>reason 3000 for \<open>PROP \<phi>Application_Conv (PROP ?X) (PROP ?X')\<close>]:
  \<open>PROP \<phi>Application_Conv (PROP X) (PROP X)\<close>
  unfolding \<phi>Application_Conv_def .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (A x) X
\<Longrightarrow> PROP \<phi>Application_Conv (Pure.all A) X\<close>
  unfolding \<phi>Application_Conv_def
proof -
  assume A: \<open>PROP A x \<Longrightarrow> PROP X\<close>
    and  B: \<open>\<And>x. PROP A x\<close>
  from A[OF B[of x]] show \<open>PROP X\<close> .
qed

lemma [\<phi>reason 1200]:
  \<open> PROP May_By_Assumption X
\<Longrightarrow> PROP \<phi>Application_Conv A Y
\<Longrightarrow> PROP \<phi>Application_Conv (PROP X \<Longrightarrow> PROP A) Y\<close>
  unfolding \<phi>Application_Conv_def May_By_Assumption_def
  subgoal premises p using p(1)[THEN p(3), THEN p(2)] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv X (PROP Y)
\<Longrightarrow> PROP \<phi>Application_Conv X (PROP Y @action A)\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (PROP Y) X
\<Longrightarrow> PROP \<phi>Application_Conv (PROP Y @action A) X\<close>
  unfolding Action_Tag_def .


subsubsection \<open>Applying on Procedure Mode\<close>

text \<open>TODO: move this to user manual.

\begin{convention}
In an application, source \<^schematic_term>\<open>?X\<close> denotes the pattern matching the whole state
and the frame rule is not used by which \<^schematic_term>\<open>?X\<close> can actually match any leading items,
whereas source \<^schematic_term>\<open>?x \<Ztypecolon> ?T\<close> matches only the first \<phi>-type.
In this way, we differentiate the representation of the purpose for transforming the whole state
and that for only the single leading item.
\end{convention}

\begin{convention}
The construction in a ready state should always be specified by a simple MTF.
\end{convention}
\<close>


paragraph \<open>Transformation Methods\<close>

lemma [\<phi>reason 3000 for \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> ?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?T \<a>\<n>\<d> ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?x' \<Ztypecolon> ?X'))) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (x \<Ztypecolon> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk R (Void\<heavy_comma> x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))
\<Longrightarrow> PROP \<phi>Application (Trueprop (x \<Ztypecolon> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk R (x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))\<close>
  by simp

lemma [\<phi>reason 3100 for \<open>
  PROP \<phi>Application (Trueprop (?S' \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?T \<a>\<n>\<d> ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (S \<i>\<m>\<p>\<l>\<i>\<e>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk R S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (CurrentConstruction mode blk R T) \<and> P)\<close>
  unfolding \<phi>Application_def
  using \<phi>apply_implication .

lemma [\<phi>reason 1500 for \<open>
  PROP \<phi>Application (Trueprop (?S' \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?T \<a>\<n>\<d> ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?R\<heavy_comma> ?S))) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (S \<i>\<m>\<p>\<l>\<i>\<e>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk RR (R\<heavy_comma> S)))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (CurrentConstruction mode blk RR (R\<heavy_comma> T)) \<and> P)\<close>
  unfolding \<phi>Application_def
  using \<phi>apply_implication implies_left_prod by blast

lemma \<phi>apply_transformation_fully[\<phi>reason for \<open>
  PROP \<phi>Application (Trueprop (?S' \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?T' \<a>\<n>\<d> ?P))
      (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'' \<a>\<n>\<d> Any @action ToSA
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (S' \<i>\<m>\<p>\<l>\<i>\<e>\<s> T' \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk RR S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (CurrentConstruction mode blk RR T) \<and> P)"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_def FOCUS_TAG_def Action_Tag_def
  by (meson \<phi>apply_implication implies_left_prod \<phi>apply_view_shift)


paragraph \<open>View Shift Methods\<close>

lemma [\<phi>reason 3000 for \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> ?X \<s>\<h>\<i>\<f>\<t>\<s> ?T \<a>\<n>\<d> ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?x' \<Ztypecolon> ?X'))) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (x \<Ztypecolon> X \<s>\<h>\<i>\<f>\<t>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk R (Void\<heavy_comma> x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))
\<Longrightarrow> PROP \<phi>Application (Trueprop (x \<Ztypecolon> X \<s>\<h>\<i>\<f>\<t>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk R (x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))\<close>
  by simp

lemma \<phi>apply_view_shift_fast[\<phi>reason 1800 for \<open>
  PROP \<phi>Application (Trueprop (?S' \<s>\<h>\<i>\<f>\<t>\<s> ?T \<a>\<n>\<d> ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (S \<s>\<h>\<i>\<f>\<t>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk R S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (CurrentConstruction mode blk R T) \<and> P)\<close>
  unfolding \<phi>Application_def
  using "\<phi>apply_view_shift" .

lemma [\<phi>reason 1500 for \<open>
  PROP \<phi>Application (Trueprop (?S' \<s>\<h>\<i>\<f>\<t>\<s> ?T \<a>\<n>\<d> ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?R\<heavy_comma> ?S))) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (S \<s>\<h>\<i>\<f>\<t>\<s> T \<a>\<n>\<d> P))
      (Trueprop (CurrentConstruction mode blk RR (R\<heavy_comma> S)))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (CurrentConstruction mode blk RR (R\<heavy_comma> T)) \<and> P)\<close>
  unfolding \<phi>Application_def
  using "\<phi>apply_view_shift" \<phi>view_shift_intro_frame by blast

lemma \<phi>apply_view_shift_fully[\<phi>reason for \<open>
  PROP \<phi>Application (Trueprop (?S' \<s>\<h>\<i>\<f>\<t>\<s> ?T' \<a>\<n>\<d> ?P))
      (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'' \<a>\<n>\<d> P1 @action ToSA
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (S' \<s>\<h>\<i>\<f>\<t>\<s> T' \<a>\<n>\<d> P2))
      (Trueprop (CurrentConstruction mode blk RR S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (CurrentConstruction mode blk RR T) \<and> (P1 \<and> P2))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_def FOCUS_TAG_def Action_Tag_def
  using \<phi>apply_implication \<phi>apply_view_shift \<phi>view_shift_intro_frame by blast



paragraph \<open>Procedure Methods\<close>

lemma apply_proc_fast[\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (\<p>\<r>\<o>\<c> ?f \<lbrace> ?S \<longmapsto> ?T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E ))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?S)) ?Result
\<close>  \<open>
  PROP \<phi>Application (Trueprop (\<p>\<r>\<o>\<c> ?f \<lbrace> ?var_S \<longmapsto> ?T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E ))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?S)) ?Result
\<close>
]:
  \<open> PROP \<phi>Application (Trueprop (\<p>\<r>\<o>\<c> f \<lbrace> S \<longmapsto> T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E ))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E)\<close>
  unfolding \<phi>Application_def
  using \<phi>apply_proc .


lemma \<phi>apply_proc_fully[\<phi>reason for
    \<open>PROP \<phi>Application (Trueprop (\<p>\<r>\<o>\<c> ?f \<lbrace> ?S' \<longmapsto> ?T' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E ))
            (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?S)) ?Result\<close>
]:
  \<open> \<phi>IntroFrameVar' R S'' S' T T' E'' E'
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'' \<a>\<n>\<d> P @action ToSA
\<Longrightarrow> Simplify (assertion_simps undefined) E''' E''
\<Longrightarrow> (\<And>v. Remove_Values (E''' v) (E v))
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (\<p>\<r>\<o>\<c> f \<lbrace> S' \<longmapsto> T' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' ))
    (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S))
    (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E) \<and> P)\<close>
  unfolding \<phi>Application_def \<phi>IntroFrameVar'_def
    FOCUS_TAG_def Simplify_def Action_Tag_def Simplify_def Remove_Values_def
  apply rule
  subgoal premises prems
    apply (simp only: prems(1))
    using \<phi>apply_proc[OF \<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> _ [_] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> _\<close>,
          OF \<open>\<p>\<r>\<o>\<c> f \<lbrace> S' \<longmapsto> T' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' \<close>[THEN \<phi>frame[where R=R],
              THEN \<phi>CONSEQ[rotated 1, OF view_shift_by_implication[OF \<open>S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'' \<a>\<n>\<d> P\<close>],
                OF view_shift_refl, OF view_shift_by_implication[OF \<open>E''' _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> E _\<close>],
                simplified prems(1), unfolded \<open>E''' = E''\<close>, simplified prems(1)]]] .
  using \<phi>apply_implication by blast



subsubsection \<open>Applying on a Block / End a Block\<close>

definition \<open>Simple_HO_Unification f f' \<longleftrightarrow> (f = f')\<close>

text \<open>\<^schematic_prop>\<open>Simple_HO_Unification A (?f x\<^sub>1 \<dots> x\<^sub>n)\<close> encodes a higher order unification
  which find an instantiation of \<open>f\<close> where terms \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are not free in \<open>f\<close>.

  Such \<open>f\<close> is the most general if \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are all variables.
  To prove this, we show there is a unique \<open>f\<close> such that \<open>f x \<equiv> A\<close> if \<open>x\<close> is a variable
    not free in \<open>f\<close>.
  Assume \<open>f\<^sub>1 x \<equiv> A\<close> and \<open>f\<^sub>2 x \<equiv> A\<close> then we have \<open>f\<^sub>1 x \<equiv> f\<^sub>2 x\<close>
  and then \<open>(\<lambda>x. f\<^sub>1 x) \<equiv> (\<lambda>x. f\<^sub>2 x)\<close>.
  Because x is not free in \<open>f\<^sub>1, f\<^sub>2\<close>, by eta-contraction, we have \<open>f\<^sub>1 \<equiv> f\<^sub>2\<close>.
  The \<open>\<equiv>\<close> here means alpha-beta-eta equivalence.
\<close>

lemma Simple_HO_Unification_I:
  \<open> Premise procedure_simplification (f = f')
\<Longrightarrow> Simple_HO_Unification f f'\<close>
  unfolding Simple_HO_Unification_def Premise_def by simp

\<phi>reasoner_ML Simple_HO_Unification 1200 (\<open>Simple_HO_Unification ?f ?f'\<close>) = \<open>
let

fun inc_bound 0 X = X
  | inc_bound d (Bound i) = Bound (i+d)
  | inc_bound d (A $ B) = inc_bound d A $ inc_bound d B
  | inc_bound d (Abs (N,T,X)) = Abs (N,T, inc_bound d X)
  | inc_bound _ X = X

fun abstract_bound_over (x, body) =
  let
    fun abs x lev tm =
      if x aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (inc_bound 1 x) (lev + 1) t)
        | t $ u =>
            (abs x lev t $ (abs x lev u handle Same.SAME => u)
              handle Same.SAME => t $ abs x lev u)
        | _ => raise Same.SAME)
  in abs x 0 body handle Same.SAME => body end

fun my_abstract_over _ (v as Free (name,ty)) body =
      Abs (name, ty, abstract_over (v,body))
  | my_abstract_over btys (Bound i) body =
      Abs ("", nth btys i, abstract_bound_over (Bound i,body))
  | my_abstract_over _ (v as Const (_,ty)) body =
      Abs ("", ty, abstract_over (v,body))
  | my_abstract_over _ v body =
      Abs ("", fastype_of v, abstract_bound_over (v,body))

fun dec_bound_level d [] = []
  | dec_bound_level d (h::l) = inc_bound (d+1) h :: (dec_bound_level (d+1) l)

in
  fn (ctxt,sequent) =>
    let
      val (Vs, _, \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Simple_HO_Unification\<close>, _) $ f $ f'))
        = Phi_Help.leading_antecedent (Thm.prop_of sequent)
      val btys = rev (map snd Vs)
      val f' = Envir.beta_eta_contract f'
    in (case Term.strip_comb f' of (Var v, args) =>
        if forall is_Bound args
        then sequent
        else Thm.instantiate (TVars.empty, Vars.make [
                (v, Thm.cterm_of ctxt (fold_rev (my_abstract_over btys)
                                                (dec_bound_level (~ (length args)) args) f))])
             sequent
        | _ => sequent)
       |> (fn seq => Seq.single (ctxt, @{thm Simple_HO_Unification_I} RS seq))
    end
end
\<close>

lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Conv (Trueprop (\<p>\<r>\<o>\<c> ?f \<lbrace> ?X \<longmapsto> ?Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) (Trueprop (\<p>\<r>\<o>\<c> ?f' \<lbrace> ?X' \<longmapsto> ?Y' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E' ))
\<close>]:
  \<open> Simple_HO_Unification f f'
\<Longrightarrow> X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> Any1 @action ToSA
\<Longrightarrow> (\<And>ret. Y ret \<s>\<h>\<i>\<f>\<t>\<s> Y' ret \<a>\<n>\<d> Any2 @action ToSA)
\<Longrightarrow> (\<And>ex.  E ex \<s>\<h>\<i>\<f>\<t>\<s> E' ex \<a>\<n>\<d> Any3 @action ToSA)
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E ))
                           (Trueprop (\<p>\<r>\<o>\<c> f' \<lbrace> X' \<longmapsto> Y' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E' ))\<close>
  unfolding \<phi>Application_Conv_def Simple_HO_Unification_def FOCUS_TAG_def Action_Tag_def
  using \<phi>CONSEQ view_shift_by_implication by blast

lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Conv (Trueprop (PendingConstruction _ _ _ _ _))
                         (Trueprop (PendingConstruction _ _ _ _ _))
\<close>]:
  \<open> Simple_HO_Unification f f'
\<Longrightarrow> (\<And>ret. S ret \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' ret \<a>\<n>\<d> Any2 @action ToSA)
\<Longrightarrow> (\<And>ex.  E ex \<i>\<m>\<p>\<l>\<i>\<e>\<s> E' ex \<a>\<n>\<d> Any3 @action ToSA)
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (PendingConstruction f  s R S  E ))
                           (Trueprop (PendingConstruction f' s R S' E'))\<close>
  unfolding \<phi>Application_Conv_def Simple_HO_Unification_def Action_Tag_def
  using \<phi>apply_implication_pending \<phi>apply_implication_pending_E by blast


subsubsection \<open>Applying on View Shift Mode\<close>

lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Conv (Trueprop (?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<a>\<n>\<d> ?P)) (Trueprop (?X' \<s>\<h>\<i>\<f>\<t>\<s> ?Y' \<a>\<n>\<d> ?P'))
\<close>]:
  \<open> X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> Any1 @action ToSA
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y' \<a>\<n>\<d> Any2 @action ToSA
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Any1 \<and> Any2 \<and> P \<longrightarrow> P')
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P)) (Trueprop (X' \<s>\<h>\<i>\<f>\<t>\<s> Y' \<a>\<n>\<d> P'))\<close>
  unfolding \<phi>Application_Conv_def Simple_HO_Unification_def Action_Tag_def Premise_def
  by (metis View_Shift_def view_shift_by_implication)


subsubsection \<open>Applying on Implication Mode\<close>

lemma apply_cast_on_imply_exact[\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?S \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?T \<a>\<n>\<d> ?P))
                           (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?x) \<i>\<s> ?S')) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (S \<i>\<m>\<p>\<l>\<i>\<e>\<s> T \<a>\<n>\<d> P))
                             (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S))
                             (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> ((\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T) \<and> P))\<close>
  unfolding \<phi>Application_def Imply_def ToA_Construction_def
  by blast

lemma apply_cast_on_imply_right_prod[\<phi>reason 1600 for \<open>
  PROP \<phi>Application (Trueprop (?S \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?T \<a>\<n>\<d> ?P))
                           (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?x) \<i>\<s> ?R * ?S')) ?Result
\<close>]:
  \<open> PROP \<phi>Application
            (Trueprop (S \<i>\<m>\<p>\<l>\<i>\<e>\<s> T \<a>\<n>\<d> P))
            (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> R * S))
            (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> ((\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> R * T) \<and> P))\<close>
  unfolding \<phi>Application_def ToA_Construction_def
  using implies_left_prod by (metis Imply_def)

lemma [\<phi>reason 100 for \<open>
  PROP \<phi>Application (Trueprop ((_::?'a::sep_magma_1 set) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _)) (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(_) \<i>\<s> _)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'' \<a>\<n>\<d> Any @action ToSA
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (S' \<i>\<m>\<p>\<l>\<i>\<e>\<s> T' \<a>\<n>\<d> P))
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T) \<and> P)"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_def Action_Tag_def
  by (meson \<phi>apply_implication_impl implies_left_prod)

lemma [\<phi>reason 90
  for \<open>PROP \<phi>Application (Trueprop (_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _)) (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(_) \<i>\<s> _)) ?Result\<close>
  except \<open>PROP \<phi>Application (Trueprop ((_::?'a::sep_magma_1 set) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _)) (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(_) \<i>\<s> _)) ?Result\<close>
]:
  " S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> Any @action ToSA
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (S' \<i>\<m>\<p>\<l>\<i>\<e>\<s> T \<a>\<n>\<d> P))
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T) \<and> P)"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_def Action_Tag_def
  by (meson \<phi>apply_implication_impl implies_left_prod)






subsubsection \<open>Automatic_Transformation\<close>

lemma [\<phi>reason 2000]:
  \<open> PROP \<phi>Application (RP \<Longrightarrow> RX @action morphism_mode) (Trueprop S) (PROP RET)
\<Longrightarrow> PROP \<phi>Application (Trueprop (Automatic_Transformation any_mode RP RX)) (Trueprop S) (PROP RET)\<close>
  unfolding \<phi>Application_def Automatic_Transformation_def Action_Tag_def
  subgoal premises prems using prems(1)[OF prems(2), OF prems(3)[THEN mp], simplified] . .

lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application (?S' \<s>\<h>\<i>\<f>\<t>\<s> ?T' \<a>\<n>\<d> ?P2 @action morphism_mode)
        (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  " \<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'' \<a>\<n>\<d> P1 @action ToSA' False
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (S' \<s>\<h>\<i>\<f>\<t>\<s> T' \<a>\<n>\<d> P2 @action morphism_mode)
      (Trueprop (CurrentConstruction mode blk RR S))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (CurrentConstruction mode blk RR T) \<and> (P1 \<and> P2))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_def Action_Tag_def Simplify_def
  using \<phi>apply_implication \<phi>apply_view_shift \<phi>frame_view by blast



subsection \<open>Action\<close>

text \<open>Action provides a kind of meta calling mechanism.
  The expression of an action is nothing but a syntactical symbol.
  The symbol itself does not given any semantic information about what it does exactly.
  Its effect to the programming is interpreted by reasoning, or more specifically, by the
    configured reasoning rules binding on the action symbol.
  The rules perform the actual transformations, applications, or any other operations.
  And this performance defines the semantics of the action.

  Applying an action can be read as invoking certain automatic operation linked to the name of the
  action, to do some transformations or generate some code or do anything feasible.
  It makes the action calling very flexible.
  Semantic conversion made by reasoners written in ML can be involved, which gives
  sufficient space for many automatic operation.
\<close>

(*TODO: polish below*)

text \<open>The action symbol is encoded to be a fixed free variable or a constant of \<^typ>\<open>action\<close>.
  Therefore the pattern matching can be native and fast.
  Note an action can be parameterized like, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> action\<close> parameterized
    by a nat and a boolean. Other parameters can come from the sequent.
\<close>

text \<open>\<^prop>\<open>A @action Act\<close> tells antecedent \<^prop>\<open>A\<close> is bound to the action Act, typically
  a procedure rule or an implication or a view shift rule.\<close>

definition Do_Action :: \<open>action \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>Do_Action action sequent result \<equiv> (PROP sequent \<Longrightarrow> PROP result)\<close>

text \<open>\<^prop>\<open>PROP Do_Action action sequent result\<close> is the antecedent to be reasoned
  to return the construction result of the sequent by the action.\<close>

declare [[\<phi>reason_default_pattern \<open>PROP Do_Action ?A ?S _\<close> \<Rightarrow> \<open>PROP Do_Action ?A ?S _\<close> (100) ]]


subsubsection \<open>Two Methods of Applying Action\<close>

text \<open>There are two way to activate the construction of an action.
  One is by application mechanism where user inputs a theorem of shape \<^prop>\<open>PROP Call_Action action\<close>;
  another is by synthesis, where user inputs a cartouche of \<^term>\<open>action\<close>.\<close>

paragraph \<open>First way, by Application\<close>

definition Call_Action :: \<open>action \<Rightarrow> prop\<close> where \<open>Call_Action \<equiv> Pure.term\<close>

lemma Call_Action_I[intro!]: \<open>PROP Call_Action XX\<close> unfolding Call_Action_def term_def .

lemma [\<phi>reason 2000]:
  \<open> PROP Do_Action action sequent result
\<Longrightarrow> PROP \<phi>Application (Call_Action action) sequent result\<close>
  unfolding \<phi>Application_def Do_Action_def .

paragraph \<open>Second way, by Synthesis\<close>

lemma [\<phi>reason 1400]:
  \<open> \<r>CALL Synthesis_Parse action action'
\<Longrightarrow> PROP Do_Action action' sequent result
\<Longrightarrow> \<r>Success
\<Longrightarrow> PROP DoSynthesis action sequent result\<close>
  for action :: action
  unfolding DoSynthesis_def Do_Action_def .
(*
subsubsection \<open>Classes of Actions\<close>

class view_shift  (* The action can be a view shift. FIX ME: the semantics of them is very unclear *)
class implication (* The action can be an implication *)
class procedure   (* The action can be a procedure *)
class simplification begin
subclass implication .
end
class multi_args_fixed_first
    (* The action may has multiple arguments, but the first argument is fixed to be
       the first one in the sequent to be applied. The remain arguments can be out of
       order in the sequent.
       The action has to always have the shape of `?remain_args \<heavy_comma> ?the_first_arg \<longmapsto> \<cdots>`
        even when the ?remain_args is the Void. *)
class single_target (* The argument of the action consists of only the first \<phi>-Type element. *)
class whole_target (* The action applies on the whole assertion. *)
class structural (* structural homomorphism, A \<longmapsto> B \<Longrightarrow> T(A) \<longmapsto> T(B) *)
class structural_1_2 (* homomorphism of form A \<longmapsto> B * C \<Longrightarrow> T(A) \<longmapsto> T(B) * T(C) *)
class structural_2_1 (* homomorphism of form A * B \<longmapsto> C \<Longrightarrow> T(A) * T(B) \<longmapsto> T(C) *)

typedecl implication_single_target_structural
instance implication_single_target_structural :: implication ..
instance implication_single_target_structural :: single_target ..
instance implication_single_target_structural :: structural ..

typedecl simplification
instance simplification :: simplification .. *)

subsubsection \<open>Rules of Executing Action\<close>

paragraph \<open>Fallback\<close>

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>Don't know how to do\<close> action \<open>on\<close> Sequent)
\<Longrightarrow> PROP Do_Action action Sequent Sequent\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def .


subsection \<open>Generic Assignment \& Access\<close>

subsubsection \<open>Annotation\<close>

definition Value_of :: \<open>'x \<Rightarrow> 'v \<Rightarrow> 'x\<close> (infix "<val-of>" 22)
  where [iff, post_synthesis_simp]: \<open>(x <val-of> v) = x\<close>
  \<comment> \<open>This tag annotates that \<open>x\<close> is the value of \<open>Var v\<close> or \<open>Val v\<close>.

    One usage is during synthesis of variable access.
    When user types in \<open>$var\<close> meaning to synthesis the value of variable \<open>var\<close>,
    the system reasons \<open>?x <val-of> var \<Ztypecolon> \<v>\<a>\<l> ?T\<close> which is semantically identical to
    \<open>?x \<Ztypecolon> \<v>\<a>\<l> T\<close> but is annotated that what we want is not arbitrary \<open>?x\<close> but, the value
    of the variable \<open>var\<close>. With the syntactical annotation, the reasoning can be properly
    configured to synthesis the desired value.\<close>

definition Set_Value :: \<open>'x \<Rightarrow> 'v \<Rightarrow> 'x\<close> ("_ <set-to> _" [51, 1000] 50)
  where [iff, post_synthesis_simp]: \<open>(y <set-to> x) = y\<close>
  \<comment> \<open>This tag is mainly used in synthesis, annotating the action of assigning some value
      container \<open>x\<close> like a variable with value \<open>y\<close>.
     As the evaluation of the \<close>


subsubsection \<open>Syntax\<close>

nonterminal \<phi>identifier

syntax
  "_identifier_" :: "\<phi>identifier \<Rightarrow> logic" ("$\"_")
  "_get_identifier_" :: "\<phi>identifier \<Rightarrow> logic" ("$_")
  "_set_identifier_" :: "\<phi>identifier \<Rightarrow> logic \<Rightarrow> logic" ("$_ := _" [991, 51] 50)
  "_identifier_id_" :: \<open>id \<Rightarrow> \<phi>identifier\<close> ("_")
  "_identifier_num_" :: \<open>num_token \<Rightarrow> \<phi>identifier\<close> ("_")
  "_identifier_1_" :: \<open>\<phi>identifier\<close> ("1")
  "_identifier_logic_" :: \<open>logic \<Rightarrow> \<phi>identifier\<close> ("'(_')")

consts \<phi>identifier :: "unit \<Rightarrow> unit" \<comment> \<open>used only in syntax parsing\<close>

subsubsection \<open>Rule \& Implementation\<close>

lemma "__value_access_0__":
  \<open> \<p>\<r>\<o>\<c> F \<lbrace> R \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> R\<heavy_comma> \<blangle> Void \<brangle> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  by fastforce

ML_file \<open>library/system/generic_variable_access.ML\<close>

lemma [\<phi>reason 1000]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (x <val-of> any \<Ztypecolon> T) TY\<close>
  unfolding Value_of_def .



section \<open>Implementing the Interactive Environment\<close>

text \<open>The implementation consists of three steps:
\<^enum> building the ML systems and libraries;
\<^enum> defining the Isar commands;
\<^enum> defining \<^emph>\<open>\<phi>processors\<close>.
\<close>

text \<open>\<phi>Processor realizes specific facilities for programming in a statement,
  such as applying an application, setting a parameter or a label, invoking program synthesis,
  proving a proof obligation, simplifying or transforming the state sequent,
  and fixing an existentially quantified variable.
\<close>

subsection \<open>ML codes\<close>

ML_file "library/instructions.ML"
ML_file "library/tools/parse.ML"
ML_file "library/system/processor.ML"
ML_file "library/system/procedure.ML"
ML_file \<open>library/system/sys.ML\<close>
ML_file \<open>library/system/generic_variable_access2.ML\<close>
ML_file \<open>library/system/obtain.ML\<close>
(* ML_file "./codegen/compilation.ML" *)
ML_file \<open>library/system/modifier.ML\<close>
ML_file \<open>library/system/toplevel.ML\<close>


hide_fact "__value_access_0__"

subsection \<open>Isar Commands \& Attributes\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<phi>instr"}, NuInstructions.list_definitions #> map snd))  \<close>

attribute_setup \<phi>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<phi>-system\<close>

attribute_setup \<phi>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (Phi_Processor.get_attr ctx name) (ctx,toks))
  || Scan.lift Phi_Processor.process_attr\<close>
  \<open>Evaluate the IDE-CP process on the target theorem.
  Particular processor can be specified to be invoked alone.\<close>

attribute_setup elim_premise_tag = \<open>
Scan.succeed (Thm.rule_attribute [] (fn _ => fn th =>
      if can PLPR_Syntax.dest_premise_tag (Thm.concl_of th) then th RS @{thm Premise_D} else th))
\<close>

attribute_setup elim_Do_tag = \<open>
Scan.succeed (Thm.rule_attribute [] (fn _ => fn th =>
  case Thm.concl_of th
    of Const(\<^const_name>\<open>Do\<close>, _) $ _ => th RS @{thm Do_D}
     | _ => th))
\<close>

attribute_setup elim_Simplify_tag = \<open>
Scan.succeed (Thm.rule_attribute [] (fn _ => fn th =>
  case Thm.concl_of th
    of _ $ (Const(\<^const_name>\<open>Simplify\<close>, _) $ _ $ _ $ _) => th RS @{thm Simplify_D}
     | _ => th))
\<close>

declare [[\<phi>premise_attribute  [elim_Do_tag] for \<open>\<^bold>d\<^bold>o PROP _\<close>,
          \<phi>premise_attribute  [elim_premise_tag] for \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> ?x\<close>,
          \<phi>premise_attribute  [elim_premise_tag] for \<open>\<s>\<i>\<m>\<p>\<r>\<e>\<m> ?x\<close>,
          \<phi>premise_attribute? [useful] for \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> ?x\<close>,
          \<phi>premise_attribute? [useful] for \<open>\<s>\<i>\<m>\<p>\<r>\<e>\<m> ?x\<close>,
          \<phi>premise_attribute? [\<phi>reason] for \<open>\<phi>SemType _ _\<close> \<open>\<^bold>d\<^bold>o \<phi>SemType _ _\<close>,
          \<phi>premise_attribute  [elim_Simplify_tag] for \<open>Simplify _ _ _\<close> \<open>\<^bold>d\<^bold>o Simplify _ _ _\<close>,
          \<phi>premise_attribute? [useful] for \<open>Simplify _ _ _\<close> \<open>\<^bold>d\<^bold>o Simplify _ _ _\<close>,
          \<phi>premise_attribute? [\<phi>reason 200] for \<open>is_functional ?S\<close>,
          \<phi>premise_attribute? [\<phi>reason 200] for \<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _\<close>
]]

subsection \<open>User Interface Processors\<close>

text \<open>Convention of priorities:
  \<^item> Simplifications and Conversions for canonical forms < 1000
  \<^item> Reasoning Antecedents = 1000
  \<^item> General Application not bound on specific pattern or keyword : 9000~9999
\<close>


subsubsection \<open>Controls\<close>

\<phi>processor set_auto_level 10 (\<open>PROP ?P\<close>) \<open>(fn (ctxt, sequent) => Phi_Parse.auto_level_force >>
  (fn auto_level' => fn _ => (Config.put Phi_Reasoner.auto_level auto_level' ctxt, sequent)))\<close>
  \<open>Note the declared auto-level is only valid during the current statement.
   In the next statement, the auto-level will be reset to the default fully-automated level.\<close>

(*
\<phi>processor repeat 12 (\<open>PROP ?P\<close>) \<open>let
  in fn (ctxt, sequent) =>
    Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*") >> (fn (tok,n) => fn () =>
        (case Int.fromString n of SOME n => funpow n | _ => error ("should be a number: "^n))
          (Phi_Processor.process_by_input [tok]) (ctxt, sequent)
    )
  end\<close> *)


subsubsection \<open>Constructive\<close>

\<phi>processor accept_call 500 (\<open>\<p>\<e>\<n>\<d>\<i>\<n>\<g> ?f \<o>\<n> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?T \<t>\<h>\<r>\<o>\<w>\<s> ?E\<close>)
  \<open>fn stat => Scan.succeed (fn _ => Phi_Sys.accept_proc stat)\<close>

lemma \<phi>cast_exception_UI:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>a. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t E a \<s>\<h>\<i>\<f>\<t>\<s> E' a)
\<Longrightarrow> PendingConstruction f blk H T E'"
  unfolding Argument_def
  using \<phi>apply_view_shift_pending_E .

(*immediately before the accept call*)
\<phi>processor throws 490 (\<open>\<p>\<e>\<n>\<d>\<i>\<n>\<g> ?f \<o>\<n> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?T \<t>\<h>\<r>\<o>\<w>\<s> ?E\<close>)
  \<open>fn (ctxt, sequent) => \<^keyword>\<open>throws\<close> >> (fn _ => fn _ =>
    (ctxt, sequent RS @{thm "\<phi>cast_exception_UI"})
)\<close>

hide_fact \<phi>cast_exception_UI

\<phi>processor "apply" 9000 (\<open>?P\<close>) \<open> fn (ctxt,sequent) => Phi_App_Rules.parser >> (fn xnames => fn _ =>
  (Phi_Apply.apply (Phi_App_Rules.app_rules ctxt [xnames]) (ctxt, sequent)))\<close>

ML_file \<open>library/additions/delay_by_parenthenmsis.ML\<close>

\<phi>processor delayed_apply 8998 (\<open>CurrentConstruction ?mode ?blk ?H ?S\<close> | \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?s) \<i>\<s> ?S'\<close>)
\<open> fn (ctxt,sequent) =>
  (Phi_App_Rules.parser --| \<^keyword>\<open>(\<close>) >> (fn xnames => fn _ =>
    if Phi_Delay_Application.synt_can_delay_apply' (Context.Proof ctxt) (fst xnames)
    then (Phi_Delay_Application.delay_app (Phi_Delay_Application.Apply (
              Phi_App_Rules.app_rules ctxt [xnames])) ctxt, sequent)
    else raise Bypass NONE)\<close>

\<phi>processor apply_delayed 8998 (\<open>CurrentConstruction ?mode ?blk ?H ?S\<close> | \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?s) \<i>\<s> ?S'\<close>)
\<open> fn s => \<^keyword>\<open>)\<close> >> (fn _ => fn _ => Phi_Delay_Application.invoke_delayed_one s)\<close>

\<phi>processor comma 8999 (\<open>?P\<close>) \<open> fn s => 
  \<^keyword>\<open>,\<close> >> (fn _ => fn _ => Phi_Delay_Application.comma s)\<close>

\<phi>processor embedded_block 8999 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
\<open> fn stat => (\<^keyword>\<open>(\<close> >> (fn _ => fn _ =>
  raise Process_State_Call (
          stat |> apfst (Phi_Delay_Application.delay_app Phi_Delay_Application.End_Block),
          Phi_Toplevel.begin_block_cmd ([],[]) false)))\<close>

\<phi>processor set_param 5000 (premises \<open>\<p>\<a>\<r>\<a>\<m> ?P\<close>) \<open>fn stat => Parse.term >> (fn term => fn _ =>
  Phi_Sys.set_param_cmd term stat)\<close>

\<phi>processor set_label 5000 (premises \<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l ?P\<close>) \<open>fn stat => Parse.name >> (fn name => fn _ =>
  Phi_Sys.set_label name stat)\<close>

\<phi>processor rule 9000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
  \<open>fn (ctxt, sequent) => Phi_App_Rules.parser >> (fn thm => fn _ =>
    let open Phi_Envir
    val apps = Phi_App_Rules.app_rules ctxt [thm]
    val sequent = perhaps (try (fn th => @{thm Argument_I} RS th)) sequent
    in Phi_Apply.apply apps (ctxt,sequent) end)\<close>

(* case Seq.pull (Thm.biresolution (SOME ctxt) false (map (pair false) apps) 1 sequent)
         of SOME (th, _) => (ctxt,th)
          | _ => raise THM ("RSN: no unifiers", 1, sequent::apps) *)

ML \<open>val phi_synthesis_parsing = Attrib.setup_config_bool \<^binding>\<open>\<phi>_synthesis_parsing\<close> (K false)\<close>

\<phi>processor synthesis 8800 (\<open>CurrentConstruction ?mode ?blk ?H ?S\<close> | \<open>PROP ?P \<Longrightarrow> PROP ?RM\<close>)
  \<open>fn (ctxt, sequent) => Parse.group (fn () => "term") (Parse.inner_syntax (Parse.cartouche || Parse.number))
>> (fn raw_term => fn _ =>
  let
    val ctxt_parser = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
                        |> Config.put phi_synthesis_parsing true
                        |> Config.put Generic_Variable_Access.mode_synthesis true
    val binds = Variable.binds_of ctxt_parser
    val term = Syntax.parse_term ctxt_parser raw_term                               
                  |> Term.map_aterms (
                        fn X as Var (name, _) =>
                            (case Vartab.lookup binds name of SOME (_,Y) => Y | _ => X)
                         | X => X
                     ) (*patch to enable term binding*)
                  |> Syntax.check_term ctxt_parser
                  |> Thm.cterm_of ctxt
   in
    Phi_Sys.synthesis term (ctxt, sequent)
  end)\<close>

(*access local value or variable or any generic variables*)
\<phi>processor get_var 5000 (\<open>CurrentConstruction ?mode ?blk ?H ?S\<close> | \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?s) \<i>\<s> ?S'\<close> | \<open>PROP ?P \<Longrightarrow> PROP ?RM\<close>)  \<open>
  fn (ctxt,sequent) => \<^keyword>\<open>$\<close> |-- (Parse.short_ident || Parse.long_ident || Parse.number)
  >> (fn var => fn _ =>
    let
      val ctxt_parser = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
                          |> Config.put phi_synthesis_parsing true
                          |> Config.put Generic_Variable_Access.mode_synthesis true
      val term = Syntax.parse_term ctxt_parser ("$" ^ var)
                  |> Syntax.check_term ctxt_parser
                  |> Thm.cterm_of ctxt
    in
      Phi_Sys.synthesis term (ctxt,sequent)
    end)
\<close>

\<phi>processor assign_var 5000 (\<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?S\<close>) \<open>
  fn (ctxt,sequent) => (\<^keyword>\<open>\<rightarrow>\<close> |--
          Parse.list1 (Scan.option \<^keyword>\<open>$\<close> |-- Scan.option Parse.keyword
                       --| Scan.option \<^keyword>\<open>$\<close> -- Parse.binding))
>> (fn vars => fn _ =>
  let
    val (vars', _ ) =
          fold_map (fn (NONE,b)    => (fn k' => ((k',b),k'))
                     | (SOME k, b) => (fn _  => ((SOME k, b), SOME k))) vars NONE
  in Generic_Variable_Access.assignment_cmd vars' (ctxt,sequent)
  end
)\<close>


\<phi>processor existential_elimination 150 ( \<open>CurrentConstruction ?mode ?blk ?H (ExSet ?T)\<close> |
                                         \<open>ToA_Construction ?s (ExSet ?S)\<close>)
  \<open>fn stat => (\<^keyword>\<open>\<exists>\<close> |-- Parse.list1 Parse.binding) #> (fn (insts,toks) => (fn _ =>
      raise Process_State_Call' (toks, stat, NuObtain.choose insts), []))\<close>

\<phi>processor automatic_existential_elimination 800 ( \<open>CurrentConstruction ?mode ?blk ?H (ExSet ?T)\<close> |
                                                   \<open>ToA_Construction ?s (ExSet ?S)\<close>)
  \<open>fn (ctxt,sequent) => Scan.succeed (fn _ =>
    let
      val _ = if Config.get ctxt NuObtain.enable_auto
              andalso Config.get ctxt Phi_Reasoner.auto_level >= 2
              then () else raise Bypass NONE
      val mode = Phi_Working_Mode.mode1 ctxt
    in
      case #spec_of mode (Thm.concl_of sequent)
        of Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs _ =>
            (* the auto choose works only when the lambda variable is given explicitly,
               i.e. no eta contract. *)
            raise Process_State_Call ((ctxt,sequent), NuObtain.auto_choose)
         | _ => raise Bypass NONE
    end)\<close>



subsubsection \<open>Simplifiers \& Reasoners\<close>

\<phi>processor \<phi>simplifier 100 (\<open>CurrentConstruction ?mode ?blk ?H ?T\<close> | \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?x) \<i>\<s> ?S\<close>)
  \<open>Phi_Processor.simplifier\<close>
(* \<phi>processor \<phi>simplifier_final 9999 \<open>PROP P\<close>  \<open>Phi_Processors.simplifier []\<close> *)

\<phi>processor move_fact1  90 (\<open>?Any \<and> ?P\<close>)
\<open>fn stat => Scan.succeed (fn _ => raise Bypass (SOME (Phi_Sys.move_lemmata stat)))\<close>

\<phi>processor move_fact2 110 (\<open>?Any \<and> ?P\<close>)
\<open>fn stat => Scan.succeed (fn _ => raise Bypass (SOME (Phi_Sys.move_lemmata stat)))\<close>

\<phi>processor automatic_morphism 90 (\<open>CurrentConstruction ?mode ?blk ?H ?T\<close> | \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?x) \<i>\<s> ?S\<close>)
\<open>not_safe (fn stat => Scan.succeed (fn _ => Phi_Sys.apply_automatic_morphism stat
      handle Empty => raise Bypass NONE))\<close>

(* Any simplification should finish before priority 999, or else
 *  this processor will be triggered unnecessarily frequently.*)
\<phi>processor set_\<phi>this 999 (\<open>CurrentConstruction ?mode ?blk ?H ?T\<close> | \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(?x) \<i>\<s> ?S\<close>)
\<open>fn (ctxt, sequent) => Scan.succeed (fn _ =>
  let
    val ctxt' = Phi_Envir.update_programming_sequent' sequent ctxt
  in
    raise Bypass (SOME(ctxt', sequent))
  end)\<close>


\<phi>processor \<phi>reason 1000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
\<open>fn (ctxt,sequent0) => Scan.succeed (fn _ =>
let val sequent = case Thm.major_prem_of sequent0
                    of Const(\<^const_name>\<open>Do\<close>, _) $ _ => @{thm Do_I} RS sequent0
                     | _ => sequent0
    val _ = Phi_Reasoner.info_print ctxt 2 (fn _ =>
              "reasoning the leading antecedent of the state sequent." ^ Position.here \<^here>);
in if Config.get ctxt Phi_Reasoner.auto_level >= 1
      andalso (case Thm.major_prem_of sequent
                 of _ (*Trueprop*) $ (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>default\<close> $ _) => false
                  | _ (*Trueprop*) $ (\<^Const>\<open>Premise\<close> $ \<^Const>\<open>MODE_COLLECT\<close> $ _) => false
                  | _ (*Trueprop*) $ (Const (\<^const_name>\<open>Argument\<close>, _) $ _) => false
                  | _ (*Trueprop*) $ (Const (\<^const_name>\<open>ParamTag\<close>, _) $ _) => false
                  | _ => true)
   then case Phi_Reasoner.reason (SOME 1) (ctxt, sequent)
          of SOME (ctxt',sequent') => (ctxt', sequent')
           | NONE => raise Bypass (SOME (ctxt,sequent0))
   else raise Bypass NONE
end)\<close>

\<phi>processor enter_proof 790 (premises \<open>Premise _ _\<close> | premises \<open>Simplify _ _ _\<close>)
  \<open>fn stat => \<^keyword>\<open>certified\<close> >> (fn _ => fn _ =>
      raise Terminate_Process (stat, SOME (snd oo Phi_Toplevel.prove_prem false)))\<close>

\<phi>processor auto_obligation_solver 800 (premises \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> ?P\<close> | premises \<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> ?P\<close>)
  \<open>fn (ctxt,sequent) => Scan.succeed (fn proc_id =>
    case Thm.major_prem_of sequent
      of _ (*Trueprop*) $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ Const (\<^const_name>\<open>True\<close>, _))
         => (ctxt, @{thm Premise_True} RS sequent)
       | _ => (
    if Config.get ctxt Phi_Reasoner.auto_level >= 2
    then let val id = Option.map (Phi_ID.encode o Phi_ID.cons proc_id) (Phi_ID.get_if_is_named ctxt)
          in (ctxt, Phi_Sledgehammer_Solver.auto id (ctxt,sequent))
          handle Phi_Reasoners.Automation_Fail err =>
              error (Phi_Reasoners.error_message err)
         end
(*case Seq.pull (Phi_Reasoners.auto_obligation_solver ctxt sequent)
           of SOME (ret, _) => (ctxt, ret)
            | NONE => raise Bypass NONE *)
    else raise Bypass NONE))\<close>

\<phi>processor pure_fact 2000 (\<open>PROP ?P\<close>) \<open>
let
  val for_fixes = Scan.optional (Parse.$$$ "for" |-- Parse.!!! Parse.params) [];
  val statement = Parse.and_list1 (
          Parse_Spec.opt_thm_name ":" -- Scan.repeat1 Parse.prop -- for_fixes);
in
  fn (ctxt, sequent) => Parse.position \<^keyword>\<open>pure_fact\<close> -- statement >> (
  fn ((_,pos), raw_statements) => fn _ =>
  let val id = Phi_ID.get ctxt

      (*We first generate names of the facts if not given*)
      fun gen_name (_, ids) = String.concatWith "_" ("\<phi>fact" :: rev_map string_of_int [] ids)
      val ctxt' = fold_index (fn (i,(((b', raw_attrs),bodys'),fixes)) => fn ctxt =>
        let val id' = Phi_ID.cons i id
            fun id'' j = if fst id' = "" then NONE else SOME (Phi_ID.encode (Phi_ID.cons j id'))
            val attrs = map (Attrib.check_src ctxt #> Attrib.attribute_cmd ctxt) raw_attrs

            val b = if Binding.is_empty b'
                    then Binding.make (gen_name id', pos)
                    else b'
            val (_,ctxt') = Proof_Context.add_fixes_cmd fixes ctxt
            val thms = map (Syntax.parse_prop ctxt') bodys'
                     |> Syntax.check_props ctxt'
                     |> map_index (fn (j,term) => term
                          |> Thm.cterm_of ctxt'
                          |> Goal.init
                          |> (fn thm => Phi_Sledgehammer_Solver.auto (id'' j)
                                                    (ctxt', @{thm Premise_D[where mode=default]} RS thm))
                          |> Goal.conclude
                          |> single
                          |> Variable.export ctxt' ctxt
                          |> rpair []
                      )
          in snd (Proof_Context.note_thms "" ((b,attrs), thms) ctxt) end
    ) raw_statements ctxt

   in (ctxt', sequent)
  end
)
end
\<close>

\<phi>processor fold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => Phi_Parse.$$$ "fold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.fold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>

\<phi>processor unfold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => Phi_Parse.$$$ "unfold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.unfold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>

\<phi>processor simplify 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => Phi_Parse.$$$ "simplify" |-- \<^keyword>\<open>(\<close> |-- Parse.list Parse.thm --| \<^keyword>\<open>)\<close>
>> (fn thms => fn _ =>
    (ctxt, Simplifier.full_simplify (ctxt addsimps Attrib.eval_thms ctxt thms) sequent)
)\<close>


(* \<phi>processor goal 1300 \<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?T\<close> \<open>
  fn (ctxt, sequent) => Parse.$$$ "goal" >> (fn _ => fn _ =>
    let
      val goal = Proof_Context.get_thm ctxt "\<phi>thesis" |> Drule.dest_term
      val (_,_,desired_nu) = Phi_Syntax.dest_procedure_c goal
      val ty = Thm.typ_of_cterm desired_nu
      val prot = Const (\<^const_name>\<open>Implicit_Protector\<close>, ty --> ty) |> Thm.cterm_of ctxt
      val ctxt = Config.put Phi_Reasoner.auto_level 1 ctxt
    in Phi_Sys.cast (Thm.apply prot desired_nu) (ctxt,sequent) end
)\<close> *)


end
