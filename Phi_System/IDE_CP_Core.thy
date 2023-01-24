chapter \<open>Integrated Deduction Environment for Programming (IDE-P)\<close>

theory IDE_CP_Core
  imports
    "Phi_Semantics_Framework.Phi_Semantics_Framework"
    "HOL-Library.Adhoc_Overloading"
    "Phi_Algebras.Map_of_Tree"
    Calculus_of_Programming
    IDE_CP_Reasoning1
  keywords
    "proc" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "\<Longleftarrow>" "\<Longleftarrow>'" "$" "subj"
    "var" "invar" "\<Longrightarrow>" "@action" "\<exists>" "throws"
    "input" "affirm" :: quasi_command
  and "\<medium_left_bracket>" :: prf_decl % "proof"
  and ";;" :: prf_decl % "proof"
  and "\<medium_right_bracket>." :: prf_decl % "proof"
  and "\<medium_right_bracket>" :: prf_goal % "proof"
  and "\<phi>processor" :: thy_decl % "ML"
  and (* "\<phi>interface" "\<phi>export_llvm" *) "\<phi>overloads" :: thy_decl
abbrevs
  "!!" = "!!"
  and "<argument>" = "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t"
  and "<param>" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
  and "<label>" = "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l"
      and "<subty>" = "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e"
      and "<by>" = "\<^bold>b\<^bold>y"
      and "<simplify>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y"
      and "<when>" = "\<^bold>w\<^bold>h\<^bold>e\<^bold>n"
      and "<try>" = "\<^bold>t\<^bold>r\<^bold>y"
  and "<obligation>" = "\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n"
  and ">->" = "\<Zinj>"
  and "<;>" = "\<Zcomp>"
  and "<val>" = "\<^bold>v\<^bold>a\<^bold>l"
  and "<ret>" = "\<^bold>r\<^bold>e\<^bold>t"
  and "<is>" = "\<^bold>i\<^bold>s"
begin

section \<open>Preliminary Configuration\<close>

named_theorems \<phi>lemmata \<open>Contextual facts during the programming. They are automatically
       aggregated from every attached \<^prop>\<open>P\<close> in \<^prop>\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk in [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Sth \<^bold>s\<^bold>u\<^bold>b\<^bold>j P\<close>
       during the programming. Do not modify it manually because it is managed automatically and
       cleared frequently\<close>

lemma [\<phi>programming_simps]:
  \<open>(A\<heavy_comma> (B\<heavy_comma> C)) = (A\<heavy_comma> B\<heavy_comma> C)\<close>
  unfolding mult.assoc ..

declare set_mult_inhabited[\<phi>inhabitance_rule]

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited 1 \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsubsection \<open>Syntax\<close>

ML_file \<open>library/syntax/Phi_Syntax.ML\<close>
ML_file \<open>library/syntax/procedure2.ML\<close>
ML_file \<open>library/system/Phi_Working_Mode.ML\<close>
ML_file \<open>library/system/Phi_Envir.ML\<close>

section \<open>Antecedent Jobs \& Annotations in Sequents\<close>


subsection \<open>Annotations in Sequents \& Specifications\<close>

(*subsubsection \<open>Technical Tags\<close> (*depreciated*)

datatype uniq_id = UNIQ_ID
  \<comment> \<open>A technical tag that is during the exporting translated to a unique ID.
    It is useful to generate unique name of anonymous functions.\<close> *)

(* subsubsection \<open>Fix\<close>

definition Fix :: \<open>'a set \<Rightarrow> 'a set\<close> ("FIX _" [16] 15) where [iff]: \<open>Fix S = S\<close>

text \<open>During the reasoning of ToSA, annotation \<^term>\<open>FIX S\<close> prevents the reasoner to permute the
  item \<^term>\<open>S\<close>. The order of \<open>S\<close> is fixed.
For example, a cast may apply only on the first object,
  after user rotates the target to the first.\<close>

lemma [\<phi>reason 2000]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s FIX Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Fix_def .

lemma (in \<phi>spec) [\<phi>reason 2000]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> FIX Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Fix_def .

(* lemma (in \<phi>empty) cast_obj_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t Y \<longmapsto> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e (FIX OBJ Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ Y' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Imply_def Argument_def Fix_def
  by (simp_all add: \<phi>expns, blast) *)
*)

subsubsection \<open>Useless Tag\<close>

definition USELESS :: \<open>bool \<Rightarrow> bool\<close> where \<open>USELESS x = x\<close>

lemma [simp]: \<open>USELESS True\<close> unfolding USELESS_def ..

text \<open>Simplification plays an important role in the programming in IDE_CP.
  We use it to simplify the specification and evaluate the abstract state.

  It is powerful as a transformation preserving all information,
  but sometimes we expect the transformation is weaker and unequal by disposing
  some useless information that we do not need.
  For example, we want to rewrite \<^term>\<open>x \<Ztypecolon> T\<close> to \<^term>\<open>y \<Ztypecolon> U\<close> but the rewrite may be held
  only with an additional proposition \<^term>\<open>Useless\<close> which is useless for us,
  \[ \<^prop>\<open>x \<Ztypecolon> T \<equiv> y \<Ztypecolon> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Useless\<close> \]
  In cases like this, we can wrap the useless proposition by tag \<open>\<open>USELESS\<close>\<close>,
  as \<^prop>\<open>x \<Ztypecolon> T \<equiv> y \<Ztypecolon> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j USELESS Useless\<close>. The equality is still held because
  \<^prop>\<open>USELESS P \<equiv> P\<close>, but IDE-CP is configured to drop the \<^prop>\<open>Useless\<close>
  so the work space will not be polluted by helpless propositions.
\<close>


subsubsection \<open>Structural Morphism\<close>

(*TODO: explain*)

definition SMorphism :: \<open>'a \<Rightarrow> 'a\<close> ("SMORPH _" [15] 14)
  where [iff]: \<open>SMorphism X = X\<close>

definition Morphism :: \<open>mode \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Morphism _ R Q = (R \<longrightarrow> Q)\<close>

consts morphism_mode :: mode

abbreviation Automatic_Morphism :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> where \<open>Automatic_Morphism \<equiv> Morphism MODE_AUTO\<close>


text \<open>
Note, the argument here means any \<phi>-Type in the pre-condition, not necessary argument value.

  If in a procedure or an implication rule or a view shift rule,
  there is an argument where the procedure or the rule retains its structure,
  this argument can be marked by \<^term>\<open>SMORPH arg\<close>.

  Recall when applying the procedure or the rule, the reasoner extracts \<^term>\<open>arg\<close> from the
    current \<phi>-BI specification \<^term>\<open>X\<close> of the current sequent.
  This extraction may break \<^term>\<open>X\<close> especially when the \<^term>\<open>arg\<close> to be extracted is
    scattered and embedded in multiple \<phi>-Types in \<^term>\<open>X\<close>.
  For example, extract \<^term>\<open>(x1, y2) \<Ztypecolon> (A1 * B2)\<close> from
    \<^term>\<open>((x1, x2) \<Ztypecolon> (A1 * A2)) * ((y1, (y2, y3)) \<Ztypecolon> (B1 * (B2 * B3)))\<close>.
  After the application, the following sequent will have broken structures because
    the original structure of \<^term>\<open>X\<close> is destroyed in order to extract \<^term>\<open>arg\<close>.
  However, the structure of the new \<^term>\<open>arg'\<close> may not changes.
  If so, by reversing the extraction, it is possible to recovery the original structure of \<^term>\<open>X\<close>,
    only with changed value of the corresponding part of \<^term>\<open>arg\<close> in \<^term>\<open>X\<close>.

  The system supports multiple arguments to be marked by \<^term>\<open>SMORPH arg\<close>.
  And the system applies the reverse morphism in the correct order.
  A requirement is,
  those structural-retained argument should locate at the end of the procedure's or the rule's
    argument list. Or else, because the reasoner does not record the extraction morphism of
    arguments not marked by \<^term>\<open>SMORPH arg\<close>, those arguments which occur after the
    structural-retained arguments change the \<phi>-BI specification by their extraction
    causing the recorded morphism of previous \<^term>\<open>SMORPH arg\<close> mismatch the current
    \<phi>-BI specification and so possibly not able to be applied any more.
\<close>



subsection \<open>Programming Job asking User Input\<close>

subsubsection \<open>Parameter\<close>

definition ParamTag :: " 'a \<Rightarrow> bool" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 26) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> True"

text \<open>Antecedent \<^prop>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> asks users to input some term that matches pattern \<^term>\<open>x\<close>.
  \<phi>-Processor `set_param` processes this antecedent.\<close>

lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
lemma [elim!,\<phi>inhabitance_rule]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" .
lemma [cong]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<longleftrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" \<comment> \<open>Disable simplification on parameters\<close> ..

ML_file \<open>library/syntax/param.ML\<close>


subsubsection \<open>Rule as an Argument\<close>

definition Argument :: "'a \<Rightarrow> 'a" ("\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _" [11] 10) where "Argument x = x"

lemma Argument_I: "P \<Longrightarrow> Argument P" unfolding Argument_def .

text \<open>Sequent in pattern \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P \<Longrightarrow> PROP Q\<close> asks users to input a theorem \<^prop>\<open>P\<close>
  or any rule of conclusion \<^prop>\<open>P\<close> and arbitrary antecedents.
  Argument emphasizes the meaning of \<^emph>\<open>input by user\<close> and tags and protects the proposition \<open>P\<close>
  to prevent any unexpected auto-reasoning,
  e.g., in the case of \<^schematic_prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<Longrightarrow> C\<close>
  if there is no the tag\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<close> the system may interpret
  \<^schematic_term>\<open>x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close> as a transformation problem and reason it unexpectedly
  using an immediate solution \<^prop>\<open>x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T\<close>.

  This antecedent is handled by the `rule` processor.
\<close>


subsubsection \<open>Text Label\<close>

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
ML_file \<open>library/system/named_premises.ML\<close>
ML_file \<open>library/system/premise_attribute.ML\<close>

subsection \<open>Reasoning Job done by \<phi>-LPR\<close>

subsubsection \<open>Introduce Frame Variable\<close>

named_theorems frame_var_rewrs \<open>Rewriting rules to normalize after inserting the frame variable\<close>

declare mult.assoc[symmetric, frame_var_rewrs]
  Subjection_times[frame_var_rewrs]
  ExSet_times_right[frame_var_rewrs]

consts frame_var_rewrs :: mode

\<phi>reasoner_ML Subty_Simplify 2000 (\<open>Simplify frame_var_rewrs ?x ?y\<close>)
  = \<open>PLPR_Simplifier.simplifier_only (fn ctxt =>
          Named_Theorems.get ctxt \<^named_theorems>\<open>frame_var_rewrs\<close>)\<close>

definition \<phi>IntroFrameVar :: "assn \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> bool"
  where "\<phi>IntroFrameVar R S' S T' T \<longleftrightarrow> S' = (R * S) \<and> T' = R * T "

definition \<phi>IntroFrameVar' ::
  "assn \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> ('ret \<Rightarrow> assn) \<Rightarrow> ('ret \<Rightarrow> assn) \<Rightarrow> ('ex \<Rightarrow> assn) \<Rightarrow> ('ex \<Rightarrow> assn) \<Rightarrow> bool"
  where "\<phi>IntroFrameVar' R S' S T' T E' E \<longleftrightarrow> S' = (R * S) \<and> T' = (\<lambda>ret. R * T ret) \<and> E' = (\<lambda>ex. R * E ex) "

definition TAIL :: \<open>assn \<Rightarrow> assn\<close> where \<open>TAIL S = S\<close>

text \<open>Antecedent \<^schematic_prop>\<open>\<phi>IntroFrameVar ?R ?S' S ?T' T\<close> appends a frame variable
  \<^schematic_term>\<open>?R\<close> to the source MTF \<^term>\<open>S\<close> if the items in \<^term>\<open>S\<close> do not have an ending
  frame variable already nor the ending item is not tagged by \<open>TAIL\<close>.
  If so, the reasoner returns \<open>?S' := ?R * S\<close> for a schematic \<open>?R\<close>,
  or else, the \<open>S\<close> is returned unchanged \<open>?S' := ?S\<close>.
  \<open>\<phi>IntroFrameVar'\<close> is similar.

  Tag \<open>TAIL\<close> is meaningful only when it tags the last item of a \<open>\<^emph>\<close>-sequence.
  It has a meaning of `the remaining everything' like, the target (RHS) item tagged by this
  means the item matches the whole remaining part of the source (LHS) part.
  \<open>TAIL\<close> also means, the tagged item is at the end and has a sense of ending, so no further
  padding is required (e.g. padding-of-void during ToSA reasoning).
\<close>

lemma \<phi>IntroFrameVar_No:
  "\<phi>IntroFrameVar Void S S T T"
  unfolding \<phi>IntroFrameVar_def by simp

lemma \<phi>IntroFrameVar'_No:
  "\<phi>IntroFrameVar' Void S S T T E E"
  unfolding \<phi>IntroFrameVar'_def by simp

lemma \<phi>IntroFrameVar_Yes:
  " Simplify frame_var_rewrs S' (R * S)
\<Longrightarrow> Simplify frame_var_rewrs T' (R * T)
\<Longrightarrow> \<phi>IntroFrameVar R S' S T' T"
  unfolding \<phi>IntroFrameVar_def by blast

lemma \<phi>IntroFrameVar'_Yes:
  " Simplify frame_var_rewrs S' (R * S)
\<Longrightarrow> Simplify frame_var_rewrs T' (\<lambda>ret. R * T ret)
\<Longrightarrow> Simplify frame_var_rewrs E' (\<lambda>ex. R * E ex)
\<Longrightarrow> \<phi>IntroFrameVar' R S' S T' T E' E"
  unfolding \<phi>IntroFrameVar'_def by blast


\<phi>reasoner_ML \<phi>IntroFrameVar 1000 ("\<phi>IntroFrameVar ?R ?S' ?S ?T' ?T") =
\<open>fn (ctxt, sequent) =>
  let
    val (Const (\<^const_name>\<open>\<phi>IntroFrameVar\<close>, _) $ _ $ _ $ S $ _ $ _) =
        Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val tail = hd (Phi_Syntax.strip_separations S)
    fun suppressed (Var _) = true
      | suppressed (\<^const>\<open>TAIL\<close> $ _) = true
      | suppressed _ = false
  in
    if suppressed tail andalso fastype_of tail = \<^typ>\<open>assn\<close>
    then Seq.single (ctxt, @{thm \<phi>IntroFrameVar_No}  RS sequent)
    else Seq.single (ctxt, @{thm \<phi>IntroFrameVar_Yes} RS sequent)
  end\<close>

\<phi>reasoner_ML \<phi>IntroFrameVar' 1000 ("\<phi>IntroFrameVar' ?R ?S' ?S ?T' ?T ?E' ?E") =
\<open>fn (ctxt, sequent) =>
  let
    val (Const (\<^const_name>\<open>\<phi>IntroFrameVar'\<close>, _) $ _ $ _ $ S $ _ $ _ $ _ $ _) =
        Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val tail = hd (Phi_Syntax.strip_separations S)
    fun suppressed (Var _) = true
      | suppressed (\<^const>\<open>TAIL\<close> $ _) = true
      | suppressed _ = false
  in
    if suppressed tail andalso fastype_of tail = \<^typ>\<open>assn\<close>
    then Seq.single (ctxt, @{thm \<phi>IntroFrameVar'_No}  RS sequent)
    else Seq.single (ctxt, @{thm \<phi>IntroFrameVar'_Yes} RS sequent)
  end\<close>

subsection \<open>General Syntax\<close>

definition HIDDEN_PREM :: \<open>'a::{} \<Rightarrow> 'a\<close> where \<open>HIDDEN_PREM x \<equiv> x\<close>

lemma HIDDEN_PREM_I : \<open>P \<Longrightarrow> HIDDEN_PREM P\<close> unfolding HIDDEN_PREM_def .
lemma HIDDEN_PREM_I': \<open>PROP P \<Longrightarrow> PROP HIDDEN_PREM P\<close> unfolding HIDDEN_PREM_def .
lemma HIDDEN_PREM_D : \<open>HIDDEN_PREM P \<Longrightarrow> P\<close> unfolding HIDDEN_PREM_def .
lemma HIDDEN_PREM_D': \<open>PROP HIDDEN_PREM P \<Longrightarrow> PROP P\<close> unfolding HIDDEN_PREM_def .
   
optional_translations (\<phi>hide_techinicals)
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (CONST Trueprop (CONST HIDDEN_PREM X)) Y"
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (CONST Trueprop (name\<^bold>: CONST HIDDEN_PREM X)) Y"
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (CONST HIDDEN_PREM X) Y"
  ("aprop") "Y" <= ("aprop") "(CONST Pure.imp) (name\<^bold>: CONST HIDDEN_PREM X) Y"
  \<open>show hidden internal techinical constructs\<close>

declare [[\<phi>hide_techinicals,
          \<phi>premise_attribute [THEN HIDDEN_PREM_D ] for \<open>HIDDEN_PREM ?P\<close>,
          \<phi>premise_attribute [THEN HIDDEN_PREM_D'] for \<open>PROP HIDDEN_PREM ?P\<close>]]

section \<open>Mechanisms\<close>

subsection \<open>Ad-hoc Overload\<close>

ML_file \<open>library/system/app_rules.ML\<close>

attribute_setup \<phi>overload = \<open>Scan.lift (Parse.and_list1 Phi_App_Rules.name_position) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (Phi_App_Rules.overload th) bindings))\<close>

\<phi>overloads D \<open>Destructive subtyping rules\<close>
\<phi>overloads cast \<open>Transform the content of a container\<close>


subsection \<open>Synthesis\<close>

text \<open>The section presents a generic synthesis framework.
  It is called generic because it supports different semantics of synthesis on different kinds of
    sequent. For example, on Programming_CurrentConstruction, the behavior is to reason
    a procedure to generate an output satisfying the desired specification;
    on View_Shift_CurrentConstruction, it is to reason a view shift;
    on a form of \<open>P \<Longrightarrow> Q\<close>, it is to reason a proposition P according to the given term.\<close>

definition DoSynthesis :: \<open>'a \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>DoSynthesis term sequent result \<equiv> (PROP sequent \<Longrightarrow> PROP result)\<close>

definition Synthesis_Parse :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  where \<open>Synthesis_Parse input parsed \<longleftrightarrow>  True\<close>

lemma \<phi>synthesis:
  \<open> PROP sequent
\<Longrightarrow> PROP DoSynthesis X sequent result
\<Longrightarrow> PROP result\<close>
  unfolding DoSynthesis_def .

text \<open>
  Overall, the synthesis procedure consists of 2 phases.
  The first phase is a pre-process, performed by antecedent
    \<^schematic_prop>\<open>Synthesis_Parse input ?parsed\<close>,
  which rewrites the user \<^term>\<open>input\<close> to \<^schematic_term>\<open>?parsed\<close>.
  The second phase invokes the reasoning process for synthesising the \<^schematic_term>\<open>?parsed\<close>.

  The rewrite process enables user to input partially instead of always giving the complete
  assertion every time, for example, just the abstract object \<^term>\<open>x\<close> to
  denote \<^schematic_term>\<open>x \<Ztypecolon> _\<close> and leave the type unspecified to accept anything.
  For example, user may input just an abstract object \<^term>\<open>x\<close> to mean to
    synthesis \<^term>\<open>x \<Ztypecolon> T\<close> for some unspecified \<^term>\<open>T\<close>;
    user may also input \<^term>\<open>0::nat\<close> to mean to synthesis \<^term>\<open>0 \<Ztypecolon> Natural_Number\<close>.

  One can disable \<phi>_synthesis_parsing to disable this feature.\<close>


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


subsubsection \<open>Tagging the target of a synthesis rule\<close>

definition Synthesis :: \<open>'a set \<Rightarrow> 'a set\<close> ("SYNTHESIS _" [15] 14) where [iff]: \<open>Synthesis S = S\<close>

consts synthesis :: \<open>subgoal \<Rightarrow> unit action\<close>

text \<open>
  Occurring in the post-condition of a rule (either a procedure specification or a view shift
    or an implication), SYNTHESIS tags the target of the rule, i.e., the construct that this
    procedure or this transformation synthesises.
  For example, \<^prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> SYNTHESIS Z \<rbrace> @action synthesis G\<close>
    represents the procedure f generates
    something that meets Z, and it is a synthesis rule for synthesising the target \<open>Z\<close>.

  Occurring during reasoning, antecedent like
    \<^schematic_prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> SYNTHESIS Z \<rbrace> @action synthesis G \<Longrightarrow> C\<close>,
  represents a reasoning task to find some procedure or some transformation to synthesis
  something meeting Z.

TODO: replace <@GOAL> G to \<open>@action synthesis G\<close>
\<close>

declare [[\<phi>reason_default_pattern \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X \<longmapsto> ?Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
                               \<Rightarrow> \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c _ \<lbrace> ?X \<longmapsto> ?Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _  @action synthesis _\<close>]]
    

subsubsection \<open>Synthesis Operations\<close>

paragraph \<open>Construction on Programming\<close>

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S1)) ?RET\<close>
]:
  " \<r>CALL Synthesis_Parse X X'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S1 \<longmapsto> \<lambda>v. S2\<heavy_comma> SYNTHESIS X' v \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action synthesis G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S1))
      (Trueprop (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>v. S2\<heavy_comma> X' v) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))"
  unfolding Synthesis_def Action_Tag_def DoSynthesis_def
  using \<phi>apply_proc .

text \<open>On programming mode, the synthesis operation always tries to find a procedure.
  View shifts have to be wrapped in a procedure. The following is an automatic wrapper. \<close>

lemma Synthesis_Proc_fallback_VS [\<phi>reason 30
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S1 \<longmapsto> \<lambda>v. ?S2\<heavy_comma> SYNTHESIS ?X' v \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> SYNTHESIS X' @action synthesis G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> S1 \<longmapsto> \<lambda>v. S2\<heavy_comma> SYNTHESIS X' \<rbrace> @action synthesis G\<close>
  unfolding \<phi>Procedure_def Return_def det_lift_def View_Shift_def by simp

paragraph \<open>Construction on View Shifting\<close>

text \<open>On view shifting mode, the synthesis operation tries to find a view shifting.\<close>

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?blk [?H] \<^bold>i\<^bold>s ?S1)) ?RET\<close>
]:
  " \<r>CALL Synthesis_Parse X X'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> SYNTHESIS X' @action synthesis G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w blk [H] \<^bold>i\<^bold>s S1))
      (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w blk [H] \<^bold>i\<^bold>s S2\<heavy_comma> X'))"
  unfolding Synthesis_def Action_Tag_def DoSynthesis_def
  using \<phi>apply_view_shift by blast

paragraph \<open>Solving an antecedent by Synthesis\<close>

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

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (PROP ?P \<Longrightarrow> PROP ?Q) ?RET\<close>
]:
  " SUBGOAL TOP_GOAL G
\<Longrightarrow> PROP Synthesis_by X (PROP P) @action synthesis G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X (PROP P \<Longrightarrow> PROP Q) (PROP Q)"
  unfolding DoSynthesis_def Synthesis_by_def Action_Tag_def .

(*BUG?!*)
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
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action synthesis G
\<Longrightarrow> PROP Synthesis_by X' (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E )) @action synthesis G\<close>
  unfolding Synthesis_by_def .

lemma [\<phi>reason 1200]:
  \<open> \<r>CALL Synthesis_Parse X' X
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action synthesis G
\<Longrightarrow> PROP Synthesis_by X' (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> X ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E )) @action synthesis G\<close>
  unfolding Synthesis_by_def Synthesis_def .

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. PROP Synthesis_by X (Trueprop (P x)) @action synthesis G)
\<Longrightarrow> PROP Synthesis_by X (Trueprop (All P)) @action synthesis G\<close>
  unfolding Synthesis_by_def Action_Tag_def ..

lemma [\<phi>reason 1200]:
  \<open> (P \<Longrightarrow> PROP Synthesis_by X (Trueprop Q) @action synthesis G)
\<Longrightarrow> PROP Synthesis_by X (Trueprop (P \<longrightarrow> Q)) @action synthesis G\<close>
  unfolding Synthesis_by_def Action_Tag_def ..


subsubsection \<open>General Synthesis Rules\<close>

lemma [\<phi>reason 1200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS f x \<Ztypecolon> T ret \<rbrace>  @action synthesis G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS (case_named f (tag x)) \<Ztypecolon> T ret \<rbrace>  @action synthesis G\<close>
  by simp

subsection \<open>Application\<close> 
\<comment> \<open>of procedures, ToA, and any other things\<close>

text \<open>It is a generic framework allowing to apply general things on the state sequent.
These general things named \<^emph>\<open>application\<close> includes
\<^item> procedures --- therefore appending a procedure on the current construction
\<^item> transformations of abstraction and view shifts --- transforming the abstract state
\<^item> actions --- meta operations combining several applications or transformations, cf. section Action.
\<close>

definition \<phi>Application :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application App_Rules State Result \<equiv> (PROP State \<Longrightarrow> PROP App_Rules \<Longrightarrow> PROP Result)\<close>

definition \<phi>Application_Method :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application_Method \<equiv> \<phi>Application\<close>

definition \<phi>Application_Success :: "prop"
  where \<open>\<phi>Application_Success \<equiv> Trueprop True\<close>

(* lemma \<phi>Application_Method_cong[cong]:
  \<open> App1 \<equiv> App2 \<Longrightarrow> Stat1 \<equiv> Stat2 \<Longrightarrow> Res1 \<equiv> Res2
\<Longrightarrow> \<phi>Application_Method App1 Stat1 Res1 \<equiv> \<phi>Application_Method App2 Stat2 Res2\<close>
  unfolding \<phi>Application_Method *)


lemma \<phi>Application_normalize:
  \<open>(P \<Longrightarrow> PROP \<phi>Application (PROP Apps) (PROP State) (PROP Result))
 \<equiv> (\<phi>Application (PROP Apps) (PROP State) (P \<Longrightarrow> PROP Result))\<close>
  unfolding \<phi>Application_def ..

lemma \<phi>application_start_reasoning:
  \<open> PROP \<phi>Application_Method (PROP Apps) (PROP State) (PROP Result)
\<Longrightarrow> PROP \<phi>Application (PROP Apps) (PROP State) (PROP Result)\<close>
  unfolding \<phi>Application_def \<phi>Application_Method_def .

lemma \<phi>application:
  \<open> PROP Apps
\<Longrightarrow> PROP State
\<Longrightarrow> PROP \<phi>Application (PROP Apps) (PROP State) (PROP Result)
\<Longrightarrow> \<r>Success
\<Longrightarrow> PROP Pure.prop Result\<close>
  unfolding \<phi>Application_def Pure.prop_def .

lemma \<phi>application_success:
  \<open>PROP \<phi>Application_Success\<close>
  unfolding \<phi>Application_Success_def ..


definition \<phi>Application_Conv :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application_Conv P Q \<equiv> (PROP P \<Longrightarrow> PROP Q)\<close>

lemma \<phi>Application_Conv:
  \<open> PROP P
\<Longrightarrow> PROP \<phi>Application_Conv P Q
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP Q\<close>
  unfolding \<phi>Application_Conv_def .

ML_file \<open>library/system/application.ML\<close>

\<phi>reasoner_ML \<phi>Application 2000 (\<open>PROP \<phi>Application (PROP ?App) (PROP ?State) (PROP ?Result)\<close>) =
  \<open>NuApply.start_reasoning\<close>

\<phi>reasoner_ML \<phi>Application_Success 2000 (\<open>PROP \<phi>Application_Success\<close>) =
  \<open>NuApply.success_application\<close>


subsubsection \<open>Common Rules of Application Methods\<close>

lemma [\<phi>reason for \<open>
  PROP \<phi>Application_Method (PROP ?App &&& PROP ?Apps) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (PROP App &&& PROP Apps) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def conjunction_imp .

lemma [\<phi>reason for \<open>
  PROP \<phi>Application_Method (PROP ?App &&& PROP ?Apps) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP Apps) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (PROP App &&& PROP Apps) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def conjunction_imp .

lemma [\<phi>reason 1100 for \<open>
  PROP \<phi>Application_Method (PROP ?Prem \<Longrightarrow> PROP ?App) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (PROP Prem \<Longrightarrow> PROP App) State (PROP Prem \<Longrightarrow> PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def imp_implication
  subgoal premises prems using prems(1)[OF  prems(2) prems(3)[OF prems(4)]] . .

lemma [\<phi>reason 1100 for \<open>
  PROP \<phi>Application_Method (Trueprop (?Prem \<longrightarrow> ?App)) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (Prem \<longrightarrow> App)) State (Prem \<Longrightarrow> PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def imp_implication
  subgoal premises prems using prems(1)[OF prems(2) prems(3)[OF prems(4)]] . .


lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Method (Pure.all ?App) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (PROP (App x)) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (Pure.all App) State (PROP Result)\<close>
  unfolding \<phi>Application_def \<phi>Application_Method_def
  subgoal premises prems
    apply (tactic \<open>Tactic.resolve_tac \<^context>
      [((Thm.forall_elim \<^cterm>\<open>x\<close> @{thm prems(3)}) RS @{thm prems(1)[OF prems(2)]})] 1\<close>) . .


lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Method (Trueprop (All ?App)) ?State ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop (App x)) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (All App)) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def imp_implication
  subgoal premises prems using prems(1)[OF prems(2) prems(3)[THEN spec[where x=x]]] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Method (Trueprop App) State (PROP Result)
\<Longrightarrow> PROP \<phi>Application_Method (App @action Act) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def Action_Tag_def
  subgoal premises prems using prems(1)[OF prems(2) prems(3)] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv X' X
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method X' (PROP X \<Longrightarrow> PROP Y) Y\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def \<phi>Application_Conv_def
  subgoal premises prems using prems(3)[OF prems(1)[OF prems(4)]] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (Trueprop X') (Trueprop X)
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop X') (Trueprop (X \<longrightarrow> Y)) (Trueprop Y)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def \<phi>Application_Conv_def by blast

lemma [\<phi>reason 2000 for \<open>PROP \<phi>Application_Conv (PROP ?X) (PROP ?X')\<close>]:
  \<open>PROP \<phi>Application_Conv (PROP X) (PROP X)\<close>
  unfolding \<phi>Application_Conv_def .

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. PROP \<phi>Application_Conv (Trueprop (X' x)) (Trueprop (X x)))
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (All X')) (Trueprop (All X))\<close>
  unfolding \<phi>Application_Conv_def by blast

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (Trueprop X)  (Trueprop X')
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop Y') (Trueprop Y)
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (X' \<longrightarrow> Y')) (Trueprop (X \<longrightarrow> Y))\<close>
  unfolding \<phi>Application_Conv_def by blast

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. PROP \<phi>Application_Conv (X' x) (X x))
\<Longrightarrow> PROP \<phi>Application_Conv (\<And>x. PROP X' x) (\<And>x. PROP X x)\<close>
  unfolding \<phi>Application_Conv_def
proof -
  assume A: \<open>(\<And>x. PROP X' x \<Longrightarrow> PROP X x)\<close>
    and  B: \<open>\<And>x. PROP X' x\<close>
  show \<open>\<And>x. PROP X x\<close> proof -
    fix x show \<open>PROP X x\<close> using B[where x=x, THEN A] .
  qed
qed

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (PROP X)  (PROP X')
\<Longrightarrow> PROP \<phi>Application_Conv (PROP Y') (PROP Y)
\<Longrightarrow> PROP \<phi>Application_Conv (PROP X' \<Longrightarrow> PROP Y') (PROP X \<Longrightarrow> PROP Y)\<close>
  unfolding \<phi>Application_Conv_def
  subgoal premises prems using prems(4)[THEN prems(1), THEN prems(3), THEN prems(2)] . .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (PROP X) (PROP Y)
\<Longrightarrow> PROP \<phi>Application_Conv (PROP X) (PROP Y @action A)\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1200]:
  \<open> PROP \<phi>Application_Conv (PROP X) (PROP Y)
\<Longrightarrow> PROP \<phi>Application_Conv (PROP X @action A) (PROP Y)\<close>
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
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?x' \<Ztypecolon> ?X'))) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (CurrentConstruction mode blk R (Void\<heavy_comma> x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (CurrentConstruction mode blk R (x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))\<close>
  by simp

lemma \<phi>apply_subtyping_fast[\<phi>reason 1800 for \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (CurrentConstruction mode blk R S))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (CurrentConstruction mode blk R T) \<and> P)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using \<phi>apply_implication .

lemma [\<phi>reason 1500 for \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?R\<heavy_comma> ?S))) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (CurrentConstruction mode blk RR (R\<heavy_comma> S)))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (CurrentConstruction mode blk RR (R\<heavy_comma> T)) \<and> P)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using \<phi>apply_implication implies_left_prod by blast

lemma \<phi>apply_transformation_fully[\<phi>reason for \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T' \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action ToSA
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (CurrentConstruction mode blk RR S))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (CurrentConstruction mode blk RR T) \<and> P)"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def FOCUS_TAG_def Action_Tag_def
  by (meson \<phi>apply_implication implies_left_prod \<phi>apply_view_shift)
  

paragraph \<open>View Shift Methods\<close>

lemma [\<phi>reason 3000 for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?x \<Ztypecolon> ?X \<longmapsto> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?x' \<Ztypecolon> ?X'))) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> X \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (CurrentConstruction mode blk R (Void\<heavy_comma> x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> X \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (CurrentConstruction mode blk R (x' \<Ztypecolon> X')))
      (Trueprop ((CurrentConstruction mode blk R T') \<and> P'))\<close>
  by simp

lemma \<phi>apply_view_shift_fast[\<phi>reason 1800 for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (CurrentConstruction mode blk R S))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (CurrentConstruction mode blk R T) \<and> P)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>apply_view_shift" .

lemma [\<phi>reason 1500 for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?R\<heavy_comma> ?S))) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (CurrentConstruction mode blk RR (R\<heavy_comma> S)))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (CurrentConstruction mode blk RR (R\<heavy_comma> T)) \<and> P)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>apply_view_shift" \<phi>view_shift_intro_frame by blast

lemma \<phi>apply_view_shift_fully[\<phi>reason for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
      (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 @action ToSA
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S' \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2))
      (Trueprop (CurrentConstruction mode blk RR S))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (CurrentConstruction mode blk RR T) \<and> (P1 \<and> P2))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def FOCUS_TAG_def Action_Tag_def
  using "\<phi>apply_view_shift" \<phi>view_shift_intro_frame
  by (metis (no_types, lifting))


paragraph \<open>Procedure Methods\<close>

lemma apply_proc_fast[\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S \<longmapsto> ?T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E ))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>  \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?var_S \<longmapsto> ?T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E ))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>
]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E ))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using \<phi>apply_proc .


lemma \<phi>apply_proc_fully[\<phi>reason for
    \<open>PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S' \<longmapsto> ?T' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E ))
            (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result\<close>
]:
  \<open> \<phi>IntroFrameVar' R S'' S' T T' E'' E'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action ToSA
\<Longrightarrow> Simplify (assertion_simps undefined) E''' E''
\<Longrightarrow> (\<And>v. Remove_Values (E''' v) (E v))
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S' \<longmapsto> T' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' ))
    (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
    (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E) \<and> P)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def \<phi>IntroFrameVar'_def
    FOCUS_TAG_def Simplify_def Action_Tag_def Simplify_def Remove_Values_def
  apply rule
  subgoal premises prems
    apply (simp only: prems(1))
    using \<phi>apply_proc[OF \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _\<close>,
          OF \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S' \<longmapsto> T' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<close>[THEN \<phi>frame[where R=R],
              THEN \<phi>CONSEQ[rotated 1, OF \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>,
                OF view_shift_id, OF view_shift_by_implication[OF \<open>E''' _ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s E _\<close>],
                simplified prems(1), unfolded \<open>E''' = E''\<close>, simplified prems(1)]]] .
  by (meson \<phi>apply_view_shift)


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
  PROP \<phi>Application_Conv (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X \<longmapsto> ?Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E )) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f' \<lbrace> ?X' \<longmapsto> ?Y' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E' ))
\<close>]:
  \<open> Simple_HO_Unification f f'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1 @action ToSA
\<Longrightarrow> (\<And>ret. \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y ret \<longmapsto> Y' ret \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 @action ToSA)
\<Longrightarrow> (\<And>ex.  \<^bold>v\<^bold>i\<^bold>e\<^bold>w E ex \<longmapsto> E' ex \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any3 @action ToSA)
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E )) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> X' \<longmapsto> Y' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' ))\<close>
  unfolding \<phi>Application_Conv_def Simple_HO_Unification_def FOCUS_TAG_def Action_Tag_def
  using \<phi>CONSEQ by blast


subsubsection \<open>Applying on View Shift Mode\<close>

lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Conv (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P)) (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X' \<longmapsto> ?Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P'))
\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1 @action ToSA
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 @action ToSA
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (Any1 \<and> Any2 \<and> P \<longrightarrow> P')
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)) (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P'))\<close>
  unfolding \<phi>Application_Conv_def Simple_HO_Unification_def FOCUS_TAG_def
    Action_Tag_def View_Shift_def
  by blast


subsubsection \<open>Applying on Implication Mode\<close>

lemma apply_cast_on_imply_exact[\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
                           (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?x) \<^bold>i\<^bold>s ?S')) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
                             (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s S))
                             (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> ((\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def Imply_def ToA_Construction_def
  by blast

lemma apply_cast_on_imply_right_prod[\<phi>reason 1600 for \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
                           (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?x) \<^bold>i\<^bold>s ?R * ?S')) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method
            (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
            (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s R * S))
            (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> ((\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s R * T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def ToA_Construction_def
  using implies_left_prod
  by (metis Imply_def)


subsubsection \<open>Morphism\<close>

lemma [\<phi>reason 2000]:
  \<open> PROP \<phi>Application_Method (RP \<Longrightarrow> RX @action morphism_mode) (Trueprop S) (PROP RET)
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (Morphism any_mode RP RX)) (Trueprop S) (PROP RET)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def Morphism_def Action_Tag_def
  subgoal premises prems using prems(1)[OF prems(2), OF prems(3)[THEN mp], simplified] . .

lemma [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Method (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P2 @action morphism_mode)
        (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  " \<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 @action ToSA' False
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S' \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 @action morphism_mode)
      (Trueprop (CurrentConstruction mode blk RR S))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (CurrentConstruction mode blk RR T) \<and> (P1 \<and> P2))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def
    FOCUS_TAG_def Action_Tag_def Simplify_def
  using "\<phi>apply_view_shift" \<phi>view_shift_intro_frame
  by (metis (no_types, lifting))



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

text \<open>The action symbol is encoded to be a fixed free variable or a constant of \<^typ>\<open>'cat action\<close>.
  Therefore the pattern matching can be native and fast.
  Note an action can be parameterized like, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> 'cat action\<close> parameterized
    by a nat and a boolean. Other parameters can come from the sequent.
\<close>

text \<open>\<^prop>\<open>A @action Act\<close> tells antecedent \<^prop>\<open>A\<close> is bound to the action Act, typically
  a procedure rule or an implication or a view shift rule.\<close>

definition Do_Action :: \<open>'cat action \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>Do_Action action sequent result \<equiv> (PROP sequent \<Longrightarrow> PROP result)\<close>

text \<open>\<^prop>\<open>PROP Do_Action action sequent result\<close> is the antecedent to be reasoned
  to return the construction result of the sequent by the action.\<close>

subsubsection \<open>Methods of Applying Action\<close>

text \<open>There are two way to activate the construction of an action.
  One is by application mechanism where user inputs a theorem of shape \<^prop>\<open>PROP Call_Action action\<close>;
  another is by synthesis, where user inputs a cartouche of \<^term>\<open>action\<close>.\<close>

paragraph \<open>First way, by Application\<close>

definition Call_Action :: \<open>'cat action \<Rightarrow> prop\<close> where \<open>Call_Action \<equiv> Pure.term\<close>

lemma Call_Action_I: \<open>PROP Call_Action XX\<close> unfolding Call_Action_def term_def .

lemma [\<phi>reason 2000]:
  \<open> PROP Do_Action action sequent result
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Call_Action action) sequent result\<close>
  unfolding \<phi>Application_Method_def Do_Action_def \<phi>Application_def .

paragraph \<open>Second way, by Synthesis\<close>

lemma [\<phi>reason 1400]:
  \<open> \<r>CALL Synthesis_Parse action action'
\<Longrightarrow> PROP Do_Action action' sequent result
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis (action::'cat action) sequent result\<close>
  unfolding DoSynthesis_def Do_Action_def .

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
instance simplification :: simplification ..

consts can_be_implication :: \<open>'a \<Rightarrow> 'a\<close> (* The action can be an implication *)

subsubsection \<open>Rules of Executing Action\<close>

paragraph \<open>Generalization\<close>

lemma [\<phi>reason 2000
    for \<open>PROP Do_Action (?action::?'a::multi_args_fixed_first action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Re\<close>
    except \<open>PROP Do_Action ?action (Trueprop (CurrentConstruction ?mode ?s ?H (?R \<heavy_comma> ?X))) ?Re\<close>
]:
  \<open> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H (Void \<heavy_comma> X))) Re
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X)) Re\<close>
  for action :: \<open>'a::multi_args_fixed_first action\<close>
  by simp

lemma [\<phi>reason 30]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action (can_be_implication action)\<close>
  unfolding Action_Tag_def
  by (simp add: view_shift_by_implication) 


paragraph \<open>Action by View Shift\<close>


lemma [\<phi>reason 1100 for \<open>PROP Do_Action (?action::?'a::view_shift action) (Trueprop (CurrentConstruction ?mode ?s ?R ?X)) ?Result\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X1 \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 @action action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R1\<heavy_comma> X1 \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action (action)
      (Trueprop (CurrentConstruction mode s R X))
      (Trueprop (CurrentConstruction mode s R (R1\<heavy_comma> Y) \<and> (Any \<and> Any2)))\<close>
  for action :: \<open>('a::view_shift) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift \<phi>frame_view by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{view_shift, whole_target} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> Any))\<close>
  for action :: \<open>('a::{view_shift, whole_target}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift \<phi>frame_view by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{view_shift, single_target} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
    except \<open>PROP Do_Action ?action (Trueprop (CurrentConstruction ?mode ?s ?H (?R \<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> Any))\<close>
  for action :: \<open>('a::{view_shift, single_target}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift \<phi>frame_view by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{view_shift, single_target} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?R \<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H (R \<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R \<heavy_comma> Y) \<and> Any))\<close>
  for action :: \<open>('a::{view_shift, single_target}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift \<phi>frame_view by blast


lemma [\<phi>reason 1200 for \<open>PROP Do_Action (?action::?'a::{multi_args_fixed_first,view_shift} action) (Trueprop (CurrentConstruction ?mode ?s ?R ?X)) ?Result\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Xr\<heavy_comma> X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 @action action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R1\<heavy_comma> Xr \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action (action)
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R1\<heavy_comma> Y) \<and> Any \<and> Any2))\<close>
  for action :: \<open>('a::{multi_args_fixed_first,view_shift}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  by (metis (no_types, lifting) \<phi>apply_view_shift \<phi>view_shift_intro_frame \<phi>view_shift_intro_frame_R ab_semigroup_mult_class.mult_ac(1))


paragraph \<open>Action by Implication\<close>

subparagraph \<open>On CurrentConstruction\<close>

lemma [\<phi>reason 1090 for \<open>PROP Do_Action (?action::?'a::implication action) (Trueprop (CurrentConstruction ?mode ?s ?H ?XX)) ?Result\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w XX \<longmapsto> R\<heavy_comma> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 @action ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H XX))
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> Y) \<and> (P2 \<and> P)))\<close>
  for action :: \<open>'a::implication action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190
    for \<open>PROP Do_Action (?action::?'a::{whole_target,implication} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> P))\<close>
  for action :: \<open>'a::{whole_target,implication} action\<close>
  unfolding Do_Action_def Action_Tag_def
  using \<phi>apply_view_shift view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190
    for \<open>PROP Do_Action (?action::?'a::{single_target,implication} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
    except  \<open>PROP Do_Action ?action (Trueprop (CurrentConstruction ?mode ?s ?H (?R\<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> P))\<close>
  for action :: \<open>'a::{single_target,implication} action\<close>
  unfolding Do_Action_def Action_Tag_def
  using \<phi>apply_view_shift view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190
    for \<open>PROP Do_Action (?action::?'a::{single_target,implication} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?R \<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> Y) \<and> P))\<close>
  for action :: \<open>'a::{single_target,implication} action\<close>
  unfolding Do_Action_def Action_Tag_def
  using \<phi>apply_view_shift view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190 for \<open>PROP Do_Action (?action::?'a::{implication,multi_args_fixed_first} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?RR \<heavy_comma> ?X))) ?Result\<close>]:
  \<open> Xr \<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w RR \<longmapsto> R\<heavy_comma> Xr \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 @action ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H (RR \<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> Y) \<and> P2 \<and> P))\<close>
  for action :: \<open>'a::{implication,multi_args_fixed_first} action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  by (metis (no_types, lifting) \<phi>apply_implication \<phi>apply_view_shift \<phi>view_shift_intro_frame_R
                                ab_semigroup_mult_class.mult_ac(1) implies_left_prod)

(* No need to provide general search rule because the rule of
\<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action action\<close>
(see paragraph Generalization) converts all general search of view_shift for implication. *)

subparagraph \<open>On \<open>\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s P\<close>\<close>

lemma [\<phi>reason 1100
    for \<open>PROP Do_Action (?action::?'a::{implication, single_target} action)
                        (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?s) \<^bold>i\<^bold>s ?X)) ?Result\<close>
    except \<open>PROP Do_Action ?action (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?s) \<^bold>i\<^bold>s (?R * ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s X))
      (Trueprop ((\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s Y) \<and> P))\<close>
  for action :: \<open>'a::{implication,single_target} action\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def ToA_Construction_def by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{single_target,implication} action)
                        (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?s) \<^bold>i\<^bold>s (?R * ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s R * X))
      (Trueprop ((\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s R * Y) \<and> P))\<close>
  for action :: \<open>'a::{implication,single_target} action\<close>
  unfolding Do_Action_def Action_Tag_def ToA_Construction_def
  by (meson Imply_def implies_left_prod)

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{implication, whole_target} action)
                        (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?s) \<^bold>i\<^bold>s ?X)) ?Result\<close>
    except \<open>PROP Do_Action ?action (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?s) \<^bold>i\<^bold>s (?R * ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s X))
      (Trueprop ((\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s Y) \<and> P))\<close>
  for action :: \<open>'a::{implication,whole_target} action\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def ToA_Construction_def by blast

(* TODO!
lemma [\<phi>reason 1190 on \<open>PROP Do_Action (?action::?'a::{implication,multi_args_fixed_first} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?RR \<heavy_comma> ?X))) ?Result\<close>]:
  \<open> Xr * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (s \<in> (RR * X)))
      (Trueprop (s \<in> (R * Y) \<and> P))\<close>
  for action :: \<open>'a::{implication,multi_args_fixed_first} action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  by (metis (no_types, lifting) \<phi>apply_implication \<phi>spec.\<phi>apply_view_shift \<phi>spec_axioms \<phi>view_shift_intro_frame_R ab_semigroup_mult_class.mult_ac(1) implies_left_prod)
*)


(*
lemma [\<phi>reason 1100]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> PROP Assertion_Level_Reasoning (XX \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * X \<^bold>a\<^bold>n\<^bold>d P2)
\<Longrightarrow> PROP Do_Action action
      (Trueprop (s \<in> XX))
      (Trueprop (s \<in> (R * Y) \<and> P2 \<and> P))\<close>
  for action :: \<open>'a::implication action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift view_shift_by_implication implies_left_prod by blast
*)



subsection \<open>Actions\<close>
(*TODO: move this*)

subsubsection \<open>Identity\<close>

consts to_Identity   :: \<open>implication_single_target_structural action\<close>
consts from_Identity :: \<open>implication_single_target_structural action\<close>

lemma to_Identity_\<phi>app:   \<open>PROP Call_Action to_Identity\<close>   using Call_Action_I .
lemma from_Identity_\<phi>app: \<open>PROP Call_Action from_Identity\<close> using Call_Action_I .

subsubsection \<open>Duplicate \& Shrink\<close>

typedecl action_dup_typ
instance action_dup_typ :: view_shift ..
instance action_dup_typ :: implication ..
instance action_dup_typ :: procedure ..
instance action_dup_typ :: single_target ..
instance action_dup_typ :: structural_1_2 ..

typedecl action_drop_typ
instance action_drop_typ :: view_shift ..
instance action_drop_typ :: implication ..
instance action_drop_typ :: procedure ..
instance action_drop_typ :: multi_args_fixed_first ..
  \<comment> \<open>Because it may need an auxiliary Black Hole\<close>

typedecl action_shrink_typ
instance action_shrink_typ :: view_shift ..
instance action_shrink_typ :: implication ..
instance action_shrink_typ :: procedure ..
instance action_shrink_typ :: multi_args_fixed_first ..
instance action_shrink_typ :: structural_2_1 ..

consts action_dup :: \<open>action_dup_typ action\<close>
consts action_drop :: \<open>action_drop_typ action\<close>
consts action_shrink :: \<open>action_shrink_typ action\<close>

lemma dup_\<phi>app:    \<open>PROP Call_Action action_dup\<close>    using Call_Action_I .
lemma drop_\<phi>app:   \<open>PROP Call_Action action_drop\<close>   using Call_Action_I .
lemma shrink_\<phi>app: \<open>PROP Call_Action action_shrink\<close> using Call_Action_I .


subsection \<open>Generic Assignment \& Access\<close>

subsubsection \<open>Annotation\<close>

definition Value_of :: \<open>'x \<Rightarrow> 'v \<Rightarrow> 'x\<close> (infix "<val-of>" 22)
  where [iff]: \<open>(x <val-of> v) = x\<close>
  \<comment> \<open>This tag annotates that \<open>x\<close> is the value of \<open>Var v\<close> or \<open>Val v\<close>.

    One usage is during synthesis of variable access.
    When user types in \<open>$var\<close> meaning to synthesis the value of variable \<open>var\<close>,
    the system reasons \<open>?x <val-of> var \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l ?T\<close> which is semantically identical to
    \<open>?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close> but is annotated that what we want is not arbitrary \<open>?x\<close> but, the value
    of the variable \<open>var\<close>. With the syntactical annotation, the reasoning can be properly
    configured to synthesis the desired value.\<close>

definition Set_Value :: \<open>'x \<Rightarrow> 'v \<Rightarrow> 'x\<close> ("_ <set-to> _" [51, 1000] 50)
  where [iff]: \<open>(y <set-to> x) = y\<close>
  \<comment> \<open>This tag is mainly used in synthesis, annotating the action of assigning some value
      container \<open>x\<close> like a variable with value \<open>y\<close>.
     As the evaluation of the \<close>


subsubsection \<open>Syntax\<close>

nonterminal \<phi>identifier

syntax
  "_identifier_" :: "\<phi>identifier \<Rightarrow> logic" ("$\"_" [991] 990)
  "_get_identifier_" :: "\<phi>identifier \<Rightarrow> logic" ("$_" [991] 990)
  "_set_identifier_" :: "\<phi>identifier \<Rightarrow> logic \<Rightarrow> logic" ("$_ := _" [991, 51] 50)
  "_identifier_id_" :: \<open>id \<Rightarrow> \<phi>identifier\<close> ("_" [992] 991)
  "_identifier_num_" :: \<open>num_token \<Rightarrow> \<phi>identifier\<close> ("_" [992] 991)
  "_identifier_1_" :: \<open>\<phi>identifier\<close> ("1")
  "_identifier_logic_" :: \<open>logic \<Rightarrow> \<phi>identifier\<close> ("'(_')" [992] 991)

consts \<phi>identifier :: "unit \<Rightarrow> unit" \<comment> \<open>used only in syntax parsing\<close>

subsubsection \<open>Rule \& Implementation\<close>

lemma "__value_access_0__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E 
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R\<heavy_comma> Void \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
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

declare [[\<phi>premise_attribute  [elim_premise_tag] for \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ?x\<close>,
          \<phi>premise_attribute? [useful] for \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ?x\<close>,
          \<phi>premise_attribute? [\<phi>reason] for \<open>\<phi>SemType _ _\<close>]]

subsection \<open>IDE Processors\<close>

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

\<phi>processor repeat 12 (\<open>PROP ?P\<close>) \<open>let
  in fn (ctxt, sequent) =>
    Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*") >> (fn (tok,n) => fn () =>
        (case Int.fromString n of SOME n => funpow n | _ => error ("should be a number: "^n))
          (Phi_Processor.process_by_input [tok]) (ctxt, sequent)
    )
  end\<close>


subsubsection \<open>Constructive\<close>

\<phi>processor accept_call 500 (\<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g ?f \<^bold>o\<^bold>n ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E\<close>)
  \<open>fn stat => Scan.succeed (fn _ => Phi_Sys.accept_proc stat)\<close>

lemma \<phi>cast_exception_UI:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>a. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w E a \<longmapsto> E' a)
\<Longrightarrow> PendingConstruction f blk H T E'"
  unfolding Argument_def
  using \<phi>apply_view_shift_pending_E .

(*immediately before the accept call*)
\<phi>processor throws 490 (\<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g ?f \<^bold>o\<^bold>n ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E\<close>)
  \<open>fn (ctxt, sequent) => \<^keyword>\<open>throws\<close> >> (fn _ => fn () =>
    (ctxt, sequent RS @{thm "\<phi>cast_exception_UI"})
)\<close>

hide_fact \<phi>cast_exception_UI

\<phi>processor "apply" 9000 (\<open>?P\<close>) \<open> fn (ctxt,sequent) => Phi_App_Rules.parser >> (fn xnames => fn _ =>
  (NuApply.apply (Phi_App_Rules.app_rules ctxt xnames) (ctxt, sequent)))\<close>

\<phi>processor set_param 5000 (\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ?P \<Longrightarrow> PROP ?Q\<close>) \<open>fn stat => Parse.term >> (fn term => fn _ =>
  Phi_Sys.set_param_cmd term stat)\<close>

\<phi>processor set_label 5000 (\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l ?P \<Longrightarrow> PROP ?Q\<close>) \<open>fn stat => Parse.name >> (fn name => fn _ =>
  Phi_Sys.set_label name stat)\<close>

\<phi>processor rule 9000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
  \<open>fn (ctxt, sequent) => Phi_App_Rules.parser >> (fn thms => fn _ =>
    let open Phi_Envir
    val apps = Phi_App_Rules.app_rules ctxt thms
    val sequent = perhaps (try (fn th => @{thm Argument_I} RS th)) sequent
    in case Seq.pull (Thm.biresolution (SOME ctxt) false (map (pair false) apps) 1 sequent)
         of SOME (th, _) => (ctxt,th)
          | _ => raise THM ("RSN: no unifiers", 1, sequent::apps) end)\<close>

ML \<open>val phi_synthesis_parsing = Attrib.setup_config_bool \<^binding>\<open>\<phi>_synthesis_parsing\<close> (K false)\<close>

\<phi>processor synthesis 8800 (\<open>CurrentConstruction ?mode ?blk ?H ?S\<close> | \<open>PROP ?P \<Longrightarrow> PROP ?RM\<close>)
  \<open>fn (ctxt, sequent) => Parse.group (fn () => "term") (Parse.inner_syntax (Parse.cartouche || Parse.number))
>> (fn raw_term => fn () =>
  let
    val ctxt_parser = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
                        |> Config.put phi_synthesis_parsing true
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

\<phi>processor get_var 5000 (\<open>CurrentConstruction ?mode ?blk ?H ?S\<close> | \<open>\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?s) \<^bold>i\<^bold>s ?S'\<close>)  \<open>
  fn (ctxt,sequent) => \<^keyword>\<open>$\<close> |-- (Parse.short_ident || Parse.long_ident || Parse.number)
  >> (fn var => fn () =>
    let
      val ctxt_parser = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
                          |> Config.put phi_synthesis_parsing true
      val term = Syntax.parse_term ctxt_parser ("$" ^ var)
                  |> Syntax.check_term ctxt_parser
                  |> Thm.cterm_of ctxt
    in
      Phi_Sys.synthesis term (ctxt,sequent)
    end)
\<close>

\<phi>processor assign_var 5000 (\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S\<close>) \<open>
  fn (ctxt,sequent) => (\<^keyword>\<open>\<rightarrow>\<close> |--
          Parse.list1 (Scan.option \<^keyword>\<open>$\<close> |-- Scan.option Parse.keyword
                       --| Scan.option \<^keyword>\<open>$\<close> -- Parse.binding))
>> (fn vars => fn () =>
  let
    val (vars', _ ) =
          fold_map (fn (NONE,b)    => (fn k' => ((k',b),k'))
                     | (SOME k, b) => (fn _  => ((SOME k, b), SOME k))) vars NONE
  in Generic_Variable_Access.assignment_cmd vars' (ctxt,sequent)
  end
)\<close>


\<phi>processor existential_elimination 150 ( \<open>CurrentConstruction ?mode ?blk ?H (ExSet ?T)\<close> |
                                         \<open>ToA_Construction ?s (ExSet ?S)\<close>)
  \<open>fn stat => (\<^keyword>\<open>\<exists>\<close> |-- Parse.list1 Parse.binding) #> (fn (insts,toks) => (fn () =>
      raise Process_State_Call' (toks, stat, NuObtain.choose insts), []))\<close>

\<phi>processor automatic_existential_elimination 800 ( \<open>CurrentConstruction ?mode ?blk ?H (ExSet ?T)\<close> |
                                                   \<open>ToA_Construction ?s (ExSet ?S)\<close>)
  \<open>fn (ctxt,sequent) => Scan.succeed (fn () =>
    let
      val _ = if Config.get ctxt NuObtain.enable_auto
              andalso Config.get ctxt Phi_Reasoner.auto_level >= 2
              then () else raise Bypass NONE
      val mode = Phi_Working_Mode.working_mode_on1 ctxt (Thm.concl_of sequent)
    in
      case #spec_of mode (Thm.concl_of sequent)
        of Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs _ =>
            (* the auto choose works only when the lambda variable is given explicitly,
               i.e. no eta contract. *)
            raise Process_State_Call ((ctxt,sequent), NuObtain.auto_choose)
         | _ => raise Bypass NONE
    end)\<close>



subsubsection \<open>Simplifiers \& Reasoners\<close>

\<phi>processor \<phi>simplifier 100 (\<open>CurrentConstruction ?mode ?blk ?H ?T\<close> | \<open>\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?x) \<^bold>i\<^bold>s ?S\<close>)
  \<open>Phi_Processor.simplifier\<close>
(* \<phi>processor \<phi>simplifier_final 9999 \<open>PROP P\<close>  \<open>Phi_Processors.simplifier []\<close> *)

\<phi>processor move_fact1  90 (\<open>?Any \<and> ?P\<close>)
\<open>fn stat => Scan.succeed (fn _ => raise Bypass (SOME (Phi_Sys.move_lemmata stat)))\<close>

\<phi>processor move_fact2 110 (\<open>?Any \<and> ?P\<close>)
\<open>fn stat => Scan.succeed (fn _ => raise Bypass (SOME (Phi_Sys.move_lemmata stat)))\<close>

\<phi>processor automatic_morphism 90 (\<open>CurrentConstruction ?mode ?blk ?H ?T\<close> | \<open>\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?x) \<^bold>i\<^bold>s ?S\<close>)
\<open>not_safe (fn stat => Scan.succeed (fn _ => Phi_Sys.apply_automatic_morphism stat
      handle Empty => raise Bypass NONE))\<close>

(* Any simplification should finish before priority 999, or else
 *  this processor will be triggered unnecessarily frequently.*)
\<phi>processor set_\<phi>this 999 (\<open>CurrentConstruction ?mode ?blk ?H ?T\<close> | \<open>\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(?x) \<^bold>i\<^bold>s ?S\<close>)
\<open>fn (ctxt, sequent) => Scan.succeed (fn _ =>
  let
    val ctxt' = Phi_Envir.update_programming_sequent' sequent ctxt
  in
    raise Bypass (SOME(ctxt', sequent))
  end)\<close>


\<phi>processor \<phi>reason 1000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
\<open>fn (ctxt,sequent) => Scan.succeed (fn _ => (
  Phi_Reasoner.debug_info ctxt (fn _ =>
      "reasoning the leading antecedent of the state sequent." ^ Position.here \<^here>);
  if Config.get ctxt Phi_Reasoner.auto_level >= 1
    andalso (case Thm.major_prem_of sequent
               of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Premise\<close>, _) $ _ $ _)
                    => false
                | _ => true)
  then case Phi_Reasoner.reason (SOME 1) (ctxt, sequent)
         of SOME (ctxt',sequent') => (ctxt', sequent')
          | NONE => raise Bypass (SOME (ctxt,sequent))
  else raise Bypass NONE
))\<close>

\<phi>processor enter_proof 790 (\<open>Premise ?mode ?P \<Longrightarrow> PROP ?Any\<close>)
  \<open>fn stat => \<^keyword>\<open>affirm\<close> >> (fn _ => fn () =>
      raise Terminate_Process (stat, snd o Phi_Toplevel.prove_prem false))\<close>

\<phi>processor auto_obligation_solver 800 (\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ?P \<Longrightarrow> PROP ?Q\<close> | \<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n ?P \<Longrightarrow> PROP ?Q\<close>)
  \<open>fn (ctxt,sequent) => Scan.succeed (fn () =>
    if Config.get ctxt Phi_Reasoner.auto_level >= 2
    then case Seq.pull (Phi_Reasoners.auto_obligation_solver ctxt sequent)
           of SOME (ret, _) => (ctxt, ret)
            | NONE => raise Bypass NONE
    else raise Bypass NONE)\<close>

\<phi>processor fold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => Phi_Parse.$$$ "fold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.fold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>

\<phi>processor unfold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => Phi_Parse.$$$ "unfold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.unfold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>


(* \<phi>processor goal 1300 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close> \<open>
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
