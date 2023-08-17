chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

text \<open>The part includes small process that can be built without infrastructure of
  IDE-CP, and declarations of other large process.\<close>

theory IDE_CP_Reasoning1
  imports Spec_Framework Phi_BI
  abbrevs "<subj-reasoning>" = "\<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g>"
begin

section \<open>Annotations Guiding the Reasoning\<close>

subsection \<open>General Tags\<close>

consts SOURCE :: mode
       TARGET :: mode
       ABNORMAL :: mode

subsection \<open>Small Annotations\<close>

subsubsection \<open>Matches\<close>

definition Assertion_Matches :: \<open>'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI\<close> (infixl "<matches>" 18)
  where \<open>(S <matches> pattern) = S\<close>

text \<open>The annotation marking on a target \<^term>\<open>Y <matches> A\<close> in a ToA or a view shift
  restricts that the source have to first match pattern \<open>A\<close>.\<close>

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (Y <matches> A) \<w>\<i>\<t>\<h> P\<close>
  unfolding Assertion_Matches_def .

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P \<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> (Y <matches> A) \<w>\<i>\<t>\<h> P\<close>
  unfolding Assertion_Matches_def .

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
  \[ \<^prop>\<open>x \<Ztypecolon> T \<equiv> y \<Ztypecolon> U \<s>\<u>\<b>\<j> Useless\<close> \]
  In cases like this, we can wrap the useless proposition by tag \<open>\<open>USELESS\<close>\<close>,
  as \<^prop>\<open>x \<Ztypecolon> T \<equiv> y \<Ztypecolon> U \<s>\<u>\<b>\<j> USELESS Useless\<close>. The equality is still held because
  \<^prop>\<open>USELESS P \<equiv> P\<close>, but IDE-CP is configured to drop the \<^prop>\<open>Useless\<close>
  so the work space will not be polluted by helpless propositions.
\<close>

subsubsection \<open>Generated Rules during Reasoning or Programming\<close>

text \<open>Annotate a rule generated during the programming, to differentiate from the normal
  contextual facts. The normal facts are stored in \<open>\<phi>lemmata\<close> while the generated rules
  are in \<open>\<phi>generated\<close> (or maybe a better name like \<phi>generated_rules?)\<close>

(*TODO: explain*)
(*TODO: polish*)

(*definition SMorphism :: \<open>'a \<Rightarrow> 'a\<close> ("SMORPH _" [17] 16) (*TODO: rename it, maybe like SP standing for 
                                                          Structural Preserving*)
  where [iff]: \<open>SMorphism X = X\<close>
*)
definition Generated_Rule :: \<open>mode \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Generated_Rule _ embedded_prems stuff = (embedded_prems \<longrightarrow> stuff)\<close>

(*consts morphism_mode :: mode (*TODO: depreciate*)*)

(*abbreviation Automatic_Rule :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> where \<open>Automatic_Rule \<equiv> Generated_Rule (MODE_AUTO default)\<close>*)

(*consts REVERSE_TRANSFORMATION :: mode
abbreviation Reverse_Transformation :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Reverse_Transformation \<equiv> Generated_Rule (MODE_AUTO REVERSE_TRANSFORMATION)\<close>
*)

text \<open>TODO: update this

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

(*
declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> Reverse_Transformation _ _ \<and> _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> Reverse_Transformation _ _ \<and> _\<close>    (110)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ *  \<blangle> ?Y \<brangle> \<w>\<i>\<t>\<h> Reverse_Transformation _ _ \<and> _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ *  \<blangle> ?Y \<brangle> \<w>\<i>\<t>\<h> Reverse_Transformation _ _ \<and> _\<close>    (120)
]]
*)

subsubsection \<open>Beta-reduction Hint for \<phi>-Type\<close>

definition \<beta>_Hint_for_\<phi> (binder "\<lambda>\<^sub>\<beta> " 10)
  where \<open>\<beta>_Hint_for_\<phi> f \<equiv> f\<close>

text \<open>Occasionally, it can be convenient technically to use \<open>x \<Ztypecolon> (\<lambda>a. S a)\<close> that will be \<beta>-reduced
      transparently to \<open>S\<close>. The tag \<^const>\<open>\<beta>_Hint_for_\<phi>\<close> allowing syntax \<open>x \<Ztypecolon> (\<lambda>\<^sub>\<beta> a. S a)\<close> hints
      the reasoner to \<beta>-reduce the \<phi>-type term.\<close>

lemma \<beta>_Hint_for_\<phi>[simp]:
  \<open>x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<equiv> S x\<close>
  unfolding \<beta>_Hint_for_\<phi>_def \<phi>Type_def .

lemma [\<phi>reason 1000]:
  \<open> S x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> S x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>
\<Longrightarrow> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A> \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> R * S x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> R * S x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>
\<Longrightarrow> R * (x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A> \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S x \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S x \<w>\<i>\<t>\<h> P @action \<A>
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<w>\<i>\<t>\<h> P @action \<A> \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S x \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S x \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P @action \<A>
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P @action \<A> \<close>
  by simp


section \<open>Normalization of Assertions\<close>

consts assertion_simps :: \<open>mode \<Rightarrow> mode\<close>
       semantic_mode :: mode

ML \<open>
structure Assertion_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>assertion_simps\<close>
  val comment = "Simplification rules normalizing an assertion. \
                       \It is applied before NToA process."
  val attribute = NONE
)

val _ = Theory.setup (Context.theory_map (Assertion_SS.map (fn ctxt =>
      (ctxt addsimprocs [\<^simproc>\<open>NO_MATCH\<close>, \<^simproc>\<open>defined_Ex\<close>, \<^simproc>\<open>HOL.defined_All\<close>,
                         \<^simproc>\<open>defined_all\<close>, \<^simproc>\<open>defined_Collect\<close>, \<^simproc>\<open>Set.defined_All\<close>,
                         \<^simproc>\<open>Set.defined_Bex\<close>, \<^simproc>\<open>unit_eq\<close>, \<^simproc>\<open>case_prod_beta\<close>,
                         \<^simproc>\<open>case_prod_eta\<close>, \<^simproc>\<open>Collect_mem\<close>,
                         Phi_Conv.move_Ex_for_set_notation]
            addsimps @{thms' Sum_Type.sum.case HOL.simp_thms})
          |> Simplifier.add_cong @{thm' Subjection_cong}
    )))

structure Assertion_SS_Source = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>assertion_simps_source\<close>
  val comment = "Simp rules normalizing particularly source part of an assertion."
  val attribute = NONE
)

structure Assertion_SS_Target = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>assertion_simps_target\<close>
  val comment = "Simp rules normalizing particularly target part of an assertion."
  val attribute = NONE
)

structure Assertion_SS_Abnormal = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>assertion_simps_abnormal\<close>
  val comment = "Simp rules normalizing particularly the abnormal spec of a triple."
  val attribute = NONE
)

\<close>

\<phi>reasoner_ML assertion_simp_source 1300
  (\<open>Simplify (assertion_simps SOURCE) ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Source.get' ctxt))) o snd\<close>

\<phi>reasoner_ML assertion_simp_target 1300
  (\<open>Simplify (assertion_simps TARGET) ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Target.get' ctxt))) o snd\<close>

\<phi>reasoner_ML assertion_simp_abnormal 1300
  (\<open>Simplify (assertion_simps ABNORMAL) ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Abnormal.get' ctxt))) o snd\<close>

\<phi>reasoner_ML assertion_simp 1200
  (\<open>Premise (assertion_simps _) _\<close> | \<open>Simplify (assertion_simps ?ANY) ?X' ?X\<close>
     )
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) Assertion_SS.get') o snd\<close>

\<phi>reasoner_ML semantic_simps 1200
  (\<open>Premise semantic_mode _\<close> | \<open>Simplify semantic_mode ?X' ?X\<close>
     )
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) (fn ctxt =>
        Simplifier.clear_simpset ctxt addsimps @{thms \<phi>V_simps \<phi>arg.sel \<phi>arg.collapse})) o snd\<close>

lemmas [assertion_simps] =
  mult_zero_right[where 'a=\<open>'a::sep_magma BI\<close>] mult_zero_left[where 'a=\<open>'a::sep_magma BI\<close>]
  mult_1_right[where 'a=\<open>'a::sep_magma_1 BI\<close>]
  mult_1_left[where 'a=\<open>'a::sep_magma_1 BI\<close>]
  add_0_right[where 'a=\<open>'a::sep_magma BI\<close>] add_0_left[where 'a=\<open>'a::sep_magma BI\<close>]
  zero_fun zero_fun_def[symmetric, where 'b=\<open>'a::sep_magma BI\<close>]
  plus_fun[where 'a=\<open>'a::sep_magma BI\<close>]
  Subjection_Subjection Subjection_Zero Subjection_times Subjection_addconj
  ExSet_simps(1,3,4,5,6)
  distrib_right[where 'a=\<open>'a::sep_semigroup BI\<close>]
  mult.assoc[symmetric, where 'a=\<open>'a::sep_semigroup BI\<close>]
  \<phi>V_simps
  \<phi>Prod_expn'' \<phi>Prod_expn'

lemmas [assertion_simps_source] =
          ExSet_times_left ExSet_times_right ExSet_simps_adconj ExSet_simps_addisj



section \<open>Small Reasoning Process\<close>

subsection \<open>Auxiliaries\<close>

ML_file \<open>library/tools/helper_reasoners.ML\<close>

subsubsection \<open>Semantic Expansion of \<phi>-Types\<close>

consts MODE_\<phi>EXPN :: mode \<comment> \<open>relating to named_theorems \<open>\<phi>expn\<close>\<close>

abbreviation \<phi>expn_Premise ("<\<phi>expn> _" [26] 26) where \<open>\<phi>expn_Premise \<equiv> Premise MODE_\<phi>EXPN\<close>

\<phi>reasoner_ML \<phi>expn_Premise 10 (\<open><\<phi>expn> ?P\<close>) = \<open>
  Seq.ORELSE (
  Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) (fn ctxt =>
                            ctxt addsimps (Useful_Thms.get ctxt))),
  Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) (fn ctxt =>
        Phi_Expansions.enhance (ctxt addsimps (Useful_Thms.get ctxt))))) o snd
\<close>


text \<open>Antecedent \<^prop>\<open><\<phi>expn> P\<close> indicates the reasoner solving the premise \<^prop>\<open>P\<close> using
  simplification rules of \<open>\<phi>expns\<close>.\<close>

subsubsection \<open>Name tag by type\<close>

(*TODO: elaborate this*)

datatype ('x, 'name) named (infix "<named>" 30) = tag 'x (*TODO: rename!!*)

syntax "__named__" :: \<open>logic \<Rightarrow> tuple_args \<Rightarrow> logic\<close> (infix "<<named>>" 25)


ML_file \<open>library/syntax/name_by_type.ML\<close>

text \<open>It is a tool to annotate names on a term, e.g. \<^term>\<open>x <<named>> a, b\<close>.
  The name tag is useful in lambda abstraction (including quantification) because the
  name of an abstraction variable is not preserved in many transformation especially
  simplifications. The name can be useful in the deductive programming, e.g. universally
  quantified variables in a sub-procedure like
  \[ \<open>\<forall>x y. proc f \<lbrace> VAL x \<Ztypecolon> T\<heavy_comma> VAL y \<Ztypecolon> U \<longmapsto> any \<rbrace> \<Longrightarrow> any'\<close> \]
  When starting to write the sub-procedure f by command \<open>\<medium_left_bracket>\<close>, \<phi>-system fixes variables x and y
    with the name of x and y. The name of x and y then are significant for programming.
  To preserve the name, we use \<^typ>\<open>'any <named> '\<phi>name_x \<times> '\<phi>name_y\<close>,
    \<^prop>\<open>\<forall>(x :: 'any <named> '\<phi>name_x). sth\<close>.
  We use free type variable to annotate it because it is most stable. No transformation
    changes the name of a free type variable.

  This feature is mostly used in \<^emph>\<open>Expansion of Quantification\<close> given in the immediate subsection.
  Therefore we put this part in the subsection of reasoning jobs, though itself is not related to
  any reasoning work.
\<close>

lemma named_forall: "All P \<longleftrightarrow> (\<forall>x. P (tag x))" by (metis named.exhaust)
lemma named_exists: "Ex P \<longleftrightarrow> (\<exists>x. P (tag x))" by (metis named.exhaust)
lemma [simp]: "tag (case x of tag x \<Rightarrow> x) = x" by (cases x) simp
lemma named_All: "(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (tag x))"
proof fix x assume "(\<And>x. PROP P x)" then show "PROP P (tag x)" .
next fix x :: "'a <named> 'b" assume "(\<And>x. PROP P (tag x))" from \<open>PROP P (tag (case x of tag x \<Rightarrow> x))\<close> show "PROP P x" by simp
qed

lemma named_ExSet: "(ExSet T) = (\<exists>*c. T (tag c) )" by (clarsimp simp add: named_exists BI_eq_iff)


subsubsection \<open>Expansion of Quantification\<close>

definition \<open>eoq__fst = fst\<close>
definition \<open>eoq__snd = snd\<close>

named_theorems named_expansion \<open>Rewriting rules expanding named quantification.\<close>

lemma eoq__fst[unfolded atomize_eq[symmetric], named_expansion]:
        \<open>eoq__fst (x,y) = x\<close> unfolding eoq__fst_def by simp
lemma eoq__snd[unfolded atomize_eq[symmetric], named_expansion]:
        \<open>eoq__snd (x,y) = y\<close> unfolding eoq__snd_def by simp

lemmas [unfolded atomize_eq[symmetric], named_expansion] =
  Product_Type.prod.case named.case id_apply

ML_file  "./library/tools/quant_expansion.ML"

hide_fact  eoq__fst eoq__snd
hide_const eoq__fst eoq__snd

simproc_setup named_forall_expansion ("All (P :: 'a <named> 'names \<Rightarrow> bool)") =
  \<open>K (QuantExpansion.simproc_of
          (fn Type(\<^type_name>\<open>\<phi>arg\<close>, _) => QuantExpansion.forall_expansion_arg_encoding
            | _ => QuantExpansion.forall_expansion))\<close>

simproc_setup named_ex_expansion ("Ex (P :: 'a <named> 'names \<Rightarrow> bool)") =
  \<open>K (QuantExpansion.simproc_of
          (fn Type(\<^type_name>\<open>\<phi>arg\<close>, _) => QuantExpansion.exists_expansion_arg_encoding
            | _ => QuantExpansion.exists_expansion))\<close>

simproc_setup named_exSet_expansion ("ExSet (P :: 'a <named> 'names \<Rightarrow> 'b BI)") =
  \<open>K (QuantExpansion.simproc_of (K QuantExpansion.ExNu_expansion))\<close>

simproc_setup named_metaAll_expansion ("Pure.all (P :: 'a <named> 'names \<Rightarrow> prop)") =
  \<open>K (QuantExpansion.simproc_of
          (fn Type(\<^type_name>\<open>\<phi>arg\<close>, _) => QuantExpansion.meta_All_expansion_arg_encoding
            | _ => QuantExpansion.meta_All_expansion))\<close>

(*TODO: merge to procedure 1*)
ML_file "./library/syntax/procedure3.ML"


subsubsection \<open>Rename \<lambda>-Abstraction\<close>

definition rename_abstraction :: \<open>'\<phi>name_name itself \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>rename_abstraction name origin_abs named_abs \<longleftrightarrow> (origin_abs = named_abs)\<close>

lemma rename_abstraction:
  \<open>rename_abstraction name X X\<close>
  unfolding rename_abstraction_def ..

\<phi>reasoner_ML rename_abstraction 1100 (\<open>rename_abstraction TYPE(?'name) ?Y ?Y'\<close>) =
\<open>fn (_, (ctxt, sequent)) =>
  case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>rename_abstraction\<close>, _)
                $ (Const (\<^const_name>\<open>Pure.type\<close>, Type(\<^type_name>\<open>itself\<close>, [name'])))
                $ Abs(_,ty,body)
                $ Var Y'') =>
      let
        val name = case Phi_Syntax.dest_name_tylabels name'
                     of [x] => x
                      | _ => raise TYPE ("only one name is expected", [name'], [])
        val Y' = Abs(name, ty, body) |> Thm.cterm_of ctxt
        val sequent = @{thm rename_abstraction} RS Thm.instantiate (TVars.empty, Vars.make [(Y'',Y')]) sequent
      in
        Seq.single (ctxt, sequent)
      end
     | term => raise THM ("Bad shape of rename_abstraction antecedent", 0, [sequent])
\<close>

hide_fact rename_abstraction


subsubsection \<open>\<lambda>-Abstraction Tag\<close>

definition "lambda_abstraction" :: " 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool "
  where "lambda_abstraction x Y Y' \<longleftrightarrow> Y' x = Y"

lemma lambda_abstraction: "lambda_abstraction x (Y' x) Y'"
  unfolding lambda_abstraction_def ..

lemma [\<phi>reason 1200 for \<open>lambda_abstraction (?x,?y) ?fx ?f\<close>]:
  \<open> lambda_abstraction y fx f1
\<Longrightarrow> lambda_abstraction x f1 f2
\<Longrightarrow> lambda_abstraction (x,y) fx (case_prod f2)\<close>
  unfolding lambda_abstraction_def by simp

\<phi>reasoner_ML lambda_abstraction 1100 ("lambda_abstraction ?x ?Y ?Y'") = \<open>fn (_, (ctxt, sequent)) =>
  let
    val (Vs, _, \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>lambda_abstraction\<close>, _) $ x $ Y $ _))
      = Phi_Help.leading_antecedent (Thm.prop_of sequent)
    val Y' = Abs("", fastype_of x, abstract_over (x, Y))
    val idx = Thm.maxidx_of sequent + 1
    val vars = map Var (List.tabulate (length Vs, (fn i => ("v", i+idx))) ~~ map snd Vs)
    fun subst X = Term.subst_bounds (vars, X)
    val idx = idx + length Vs
    val rule = Drule.infer_instantiate ctxt
                  (map (apsnd (Thm.cterm_of ctxt)) [(("x",idx), subst x), (("Y'",idx),subst Y')])
                  (Thm.incr_indexes idx @{thm lambda_abstraction})
  in
    Seq.single (ctxt, rule RS sequent)
  end
\<close>

hide_fact lambda_abstraction

lemma [\<phi>reason 1200 for \<open>lambda_abstraction (tag ?x) ?fx ?f\<close>]:
  \<open> lambda_abstraction x fx f
\<Longrightarrow> rename_abstraction TYPE('name) f f'
\<Longrightarrow> lambda_abstraction (tag x :: 'any <named> 'name) fx (case_named f')\<close>
  unfolding lambda_abstraction_def rename_abstraction_def by simp


subsubsection \<open>Introduce Frame Variable\<close>

named_theorems frame_var_rewrs \<open>Rewriting rules to normalize after inserting the frame variable\<close>

declare mult.assoc[symmetric, frame_var_rewrs]
  Subjection_times[frame_var_rewrs]
  ExSet_times_right[frame_var_rewrs]

consts frame_var_rewrs :: mode

\<phi>reasoner_ML Subty_Simplify 2000 (\<open>Simplify frame_var_rewrs ?x ?y\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_only (K Seq.empty) (fn ctxt =>
          Named_Theorems.get ctxt \<^named_theorems>\<open>frame_var_rewrs\<close>)) o snd\<close>

definition \<phi>IntroFrameVar :: "'a::sep_magma BI option \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool"
  where "\<phi>IntroFrameVar R S' S T' T \<longleftrightarrow> (case R of Some R' \<Rightarrow> S' = (R' * S) \<and> T' = R' * T
                                                 | None \<Rightarrow> S' = S \<and> T' = T )"

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
  padding is required (e.g. padding-of-void during NToA reasoning).
\<close>

lemma \<phi>IntroFrameVar_No:
  "\<phi>IntroFrameVar None S S T T"
  unfolding \<phi>IntroFrameVar_def by simp

lemma \<phi>IntroFrameVar'_No:
  "\<phi>IntroFrameVar' 1 S S T T E E"
  unfolding \<phi>IntroFrameVar'_def by simp

lemma \<phi>IntroFrameVar_Yes:
  "\<phi>IntroFrameVar (Some R) (R * \<blangle> S \<brangle>) S (R * T) T"
  unfolding \<phi>IntroFrameVar_def FOCUS_TAG_def by simp

lemma \<phi>IntroFrameVar'_Yes:
  " \<phi>IntroFrameVar' R (R * \<blangle> S \<brangle>) S (\<lambda>ret. R * T ret) T (\<lambda>ex. R * E ex) E"
  unfolding \<phi>IntroFrameVar'_def FOCUS_TAG_def by blast

\<phi>reasoner_ML \<phi>IntroFrameVar 1000 ("\<phi>IntroFrameVar ?R ?S' ?S ?T' ?T") =
\<open>fn (_, (ctxt, sequent)) =>
  let
    val (Const (\<^const_name>\<open>\<phi>IntroFrameVar\<close>, \<^Type>\<open>fun \<^Type>\<open>option \<^Type>\<open>set Ty\<close>\<close> _\<close>) $ _ $ _ $ S $ _ $ _) =
        Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val tail = hd (Phi_Syntax.strip_separations S)
    fun suppressed (Var _) = true
      | suppressed (\<^const>\<open>TAIL\<close> $ _) = true
      | suppressed _ = false
  in
    if suppressed tail (* andalso fastype_of tail = \<^typ>\<open>assn\<close> *)
    then Seq.single (ctxt, @{thm \<phi>IntroFrameVar_No}  RS sequent)
    else if Sign.of_sort (Proof_Context.theory_of ctxt) (Ty, \<^sort>\<open>sep_magma_1\<close>)
         then Seq.single (ctxt, @{thm \<phi>IntroFrameVar_Yes} RS sequent)
         else Seq.of_list [(ctxt, @{thm \<phi>IntroFrameVar_Yes}  RS sequent),
                           (ctxt, @{thm \<phi>IntroFrameVar_No} RS sequent)]
  end\<close>

\<phi>reasoner_ML \<phi>IntroFrameVar' 1000 ("\<phi>IntroFrameVar' ?R ?S' ?S ?T' ?T ?E' ?E") =
\<open>fn (_, (ctxt, sequent)) =>
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

hide_fact \<phi>IntroFrameVar_No \<phi>IntroFrameVar'_No \<phi>IntroFrameVar_Yes \<phi>IntroFrameVar'_Yes


subsubsection \<open>Reasoning Embedded in BI Assertion\<close>

definition Subjec_Reasoning :: \<open> 'p set \<Rightarrow> bool \<Rightarrow> 'p set \<close> (infixl "\<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g>" 15)
  where \<open>Subjec_Reasoning \<equiv> Subjection\<close>

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g> A \<w>\<i>\<t>\<h> P\<close>
  unfolding Subjec_Reasoning_def Transformation_def
  by simp

subsection \<open>Embed BI Assertion into \<phi>-Type\<close>

lemma \<phi>Type_conv_eq_1:
  \<open>T = U \<Longrightarrow> (x \<Ztypecolon> T) = U x\<close>
  unfolding \<phi>Type_def by simp

lemma \<phi>Type_conv_eq_2:
  \<open>T = U \<Longrightarrow> (x \<Ztypecolon> T) = (x \<Ztypecolon> U)\<close>
  unfolding \<phi>Type_def by simp

ML_file \<open>library/phi_type_algebra/helps.ML\<close>
ML_file \<open>library/tools/embed_BI_into_phi_types.ML\<close>

consts mode_embed_into_\<phi>type :: mode

\<phi>reasoner_ML Simp_Premise 10 (\<open>\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode_embed_into_\<phi>type] _ : _\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) (fn ctxt => Embed_into_Phi_Type.equip ctxt)) o snd\<close>
 
lemmas [embed_into_\<phi>type] =
    \<phi>None_itself_is_one[where any=\<open>()\<close>] \<phi>Prod_expn' \<phi>Any_def


subsection \<open>Semantic Type of Multiple Values\<close>

lemma [\<phi>reason 1200 for \<open>\<phi>_Have_Types (\<lambda>vs. ?R vs\<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst vs] ?T) _\<close>]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R vs) TYs
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R (\<phi>V_snd vs)\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst vs] T) (TY#TYs)\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def \<phi>arg_forall \<phi>SemType_def subset_iff
  by (clarsimp simp add: to_vals_prod_def to_vals_VAL_def Val_inhabited_rewr)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[vs] T) [TY]\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def \<phi>arg_forall \<phi>SemType_def subset_iff
  by (clarsimp simp add: to_vals_prod_def to_vals_VAL_def Val_inhabited_rewr)

lemma [\<phi>reason 1200]:
  \<open> \<phi>_Have_Types R TYs
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R vs\<heavy_comma> S) TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def by clarsimp

lemma [\<phi>reason 2000]:
  \<open> \<phi>_Have_Types (\<lambda>_::unit \<phi>arg. Void) []\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def to_vals_unit_def by clarsimp

lemma [\<phi>reason 1020 except \<open>\<phi>_Have_Types (\<lambda>vs. ?A vs\<heavy_comma> ?B vs) _\<close>]:
  \<open> \<phi>_Have_Types (\<lambda>vs. Void\<heavy_comma> R vs) TYs
\<Longrightarrow> \<phi>_Have_Types R TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def by clarsimp

lemma [\<phi>reason 1000]:
  \<open> FAIL TEXT(\<open>Fail to infer the semantic type of\<close> R)
\<Longrightarrow> \<phi>_Have_Types R TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def FAIL_def by clarsimp

lemma [\<phi>reason 1200]:
  \<open> \<phi>_Have_Types (\<lambda>ret. (exp ret) (v ret)) TYs
\<Longrightarrow> \<phi>_Have_Types (\<lambda>ret. Let (v ret) (exp ret)) TYs\<close>
  unfolding Let_def .

lemma [\<phi>reason 1200]:
  \<open> \<phi>_Have_Types (\<lambda>ret. f ret (fst (x ret)) (snd (x ret))) TYs
\<Longrightarrow> \<phi>_Have_Types (\<lambda>ret. case_prod (f ret) (x ret)) TYs\<close>
  by (simp add: case_prod_beta')

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. \<phi>_Have_Types (\<lambda>ret. (S ret) x) TYs)
\<Longrightarrow> \<phi>_Have_Types (\<lambda>ret. ExSet (S ret)) TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def Inhabited_def ExSet_expn
  by clarsimp blast

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. \<phi>_Have_Types (\<lambda>ret. S ret) TYs)
\<Longrightarrow> \<phi>_Have_Types (\<lambda>ret. S ret \<s>\<u>\<b>\<j> P ret) TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def Inhabited_def Subjection_expn
  by clarsimp


section \<open>Identity Element I\&E\<close>

definition Identity_Element\<^sub>I :: \<open>'a::one BI \<Rightarrow> bool \<Rightarrow> bool\<close> where \<open>Identity_Element\<^sub>I S P \<longleftrightarrow> (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P)\<close>
definition Identity_Element\<^sub>E :: \<open>'a::one BI \<Rightarrow> bool\<close> where \<open>Identity_Element\<^sub>E S \<longleftrightarrow> (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S)\<close>

declare [[ \<phi>reason_default_pattern
      \<open>Identity_Element\<^sub>I ?S _\<close> \<Rightarrow> \<open>Identity_Element\<^sub>I ?S _\<close> (100)
  and \<open>Identity_Element\<^sub>I (_ \<Ztypecolon> ?T) _\<close> \<Rightarrow> \<open>Identity_Element\<^sub>I (_ \<Ztypecolon> ?T) _\<close> (110)
  and \<open>Identity_Element\<^sub>E ?S\<close> \<Rightarrow> \<open>Identity_Element\<^sub>E ?S\<close> (100)
  and \<open>Identity_Element\<^sub>E (_ \<Ztypecolon> ?T)\<close> \<Rightarrow> \<open>Identity_Element\<^sub>E (_ \<Ztypecolon> ?T)\<close> (110)
]]

subsubsection \<open>Termination\<close>

lemma [\<phi>reason 3000]:
  \<open>Identity_Element\<^sub>I 0 True\<close>
  unfolding Identity_Element\<^sub>I_def by simp

lemma [\<phi>reason 3000]:
  \<open>Identity_Element\<^sub>E 1\<close>
  unfolding Identity_Element\<^sub>E_def by simp

lemma [\<phi>reason 3000]:
  \<open>Identity_Element\<^sub>I 1 True\<close>
  unfolding Identity_Element\<^sub>I_def by simp

lemma Identity_Element\<^sub>E_empty[\<phi>reason 3000]:
  \<open>Identity_Element\<^sub>E (any \<Ztypecolon> \<circle>)\<close>
  unfolding Identity_Element\<^sub>E_def by simp

lemma Identity_Element\<^sub>I_empty[\<phi>reason 3000]:
  \<open>Identity_Element\<^sub>I (any \<Ztypecolon> \<circle>) True\<close>
  unfolding Identity_Element\<^sub>I_def by simp

lemma [\<phi>reason 3000 for \<open>Identity_Element\<^sub>I {_} _\<close> ]:
  \<open>Identity_Element\<^sub>I {1} True\<close>
  unfolding Identity_Element\<^sub>I_def one_set_def by simp

lemma [\<phi>reason 3000 for \<open>Identity_Element\<^sub>E {_}\<close>]:
  \<open>Identity_Element\<^sub>E {1}\<close>
  unfolding Identity_Element\<^sub>E_def one_set_def by simp


subsubsection \<open>Special Forms\<close>

lemma [\<phi>reason 1000 for \<open>Identity_Element\<^sub>I _ True\<close>]:
  \<open> Identity_Element\<^sub>I X Any
\<Longrightarrow> Identity_Element\<^sub>I X True \<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>I (If C (x \<Ztypecolon> A) (x \<Ztypecolon> B)) P
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> If C A B) P\<close>
  by (cases C; simp)

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>E (If C (x \<Ztypecolon> A) (x \<Ztypecolon> B))
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> If C A B)\<close>
  by (cases C; simp)

lemma [\<phi>reason 1000]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Element\<^sub>I A Pa)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Identity_Element\<^sub>I B Pb)
\<Longrightarrow> Identity_Element\<^sub>I (If C A B) (If C Pa Pb) \<close>
  by (cases C; simp)

lemma [\<phi>reason 1000]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Identity_Element\<^sub>E A)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Identity_Element\<^sub>E B)
\<Longrightarrow> Identity_Element\<^sub>E (If C A B) \<close>
  by (cases C; simp)

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>I (S x) P
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y)) P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>E (S x)
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y)) \<close>
  by simp


subsubsection \<open>Logic Connectives\<close>

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>I (1 \<Ztypecolon> Itself) True \<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> Identity_Element\<^sub>E (1 \<Ztypecolon> Itself) \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by clarsimp

lemma [\<phi>reason no explorative backtrack 1 except \<open>Identity_Element\<^sub>I (?var_x \<Ztypecolon> _) _\<close>]:
  \<open> Identity_Element\<^sub>I (z \<Ztypecolon> T) P
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x z
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P \<close>
  unfolding Identity_Element\<^sub>I_def Object_Equiv_def Premise_def
  using transformation_trans by fastforce

lemma [\<phi>reason no explorative backtrack 1 except \<open>Identity_Element\<^sub>E (?var_x \<Ztypecolon> _)\<close>]:
  \<open> Identity_Element\<^sub>E (z \<Ztypecolon> T)
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq z x
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T) \<close>
  unfolding Identity_Element\<^sub>E_def Object_Equiv_def Premise_def
  using transformation_trans by fastforce

lemma [\<phi>reason 1200]:
  \<open> Identity_Element\<^sub>I A P1
\<Longrightarrow> Identity_Element\<^sub>I B P2
\<Longrightarrow> Identity_Element\<^sub>I (A + B) (P1 \<or> P2)\<close>
  unfolding Identity_Element\<^sub>I_def
  using \<phi>CASE_IMP by force

lemma (*The above rule is local complete*)
  \<open>Identity_Element\<^sub>I (A + B) P \<Longrightarrow> Identity_Element\<^sub>I A P \<and> Identity_Element\<^sub>I B P\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by clarsimp

lemma [\<phi>reason 3000]:
  \<open> Identity_Element\<^sub>E A \<or> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (A + B)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by clarsimp

lemma (*The above rule is not local complete*)
  \<open> Identity_Element\<^sub>E (A + B) \<Longrightarrow> Identity_Element\<^sub>E A \<and> Identity_Element\<^sub>E B\<close>
  oops

lemma [\<phi>reason 1200]:
  \<open> Identity_Element\<^sub>I (A x) P
\<Longrightarrow> Identity_Element\<^sub>I (AllSet A) P\<close>
  unfolding Identity_Element\<^sub>I_def
  by (metis AllSet_expn Transformation_def)
(*The rule is not local complete*)

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. Identity_Element\<^sub>E (A x))
\<Longrightarrow> Identity_Element\<^sub>E (AllSet A)\<close>
  unfolding Identity_Element\<^sub>E_def
  by (metis AllSet_expn Transformation_def)

lemma (*The above rule is local complete*)
  \<open> Identity_Element\<^sub>E (AllSet A) \<Longrightarrow> Identity_Element\<^sub>E (A x) \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by clarsimp

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. Identity_Element\<^sub>I (A x) (P x))
\<Longrightarrow> Identity_Element\<^sub>I (ExSet A) (Ex P)\<close>
  unfolding Identity_Element\<^sub>I_def
  by (metis ExSet_expn Transformation_def)

lemma (*The above rule is local complete*)
  \<open>Identity_Element\<^sub>I (ExSet A) P \<Longrightarrow> Identity_Element\<^sub>I (A x) P\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp; blast)

lemma [\<phi>reason 1200]:
  \<open> Identity_Element\<^sub>E (A x)
\<Longrightarrow> Identity_Element\<^sub>E (ExSet A)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp; blast)

lemma (*The above rule is not local complete*)
  \<open>Identity_Element\<^sub>E (ExSet A) \<Longrightarrow> \<exists>x. Identity_Element\<^sub>E (A x)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def ExSet_expn
  by clarsimp

lemma [\<phi>reason 1200]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> Identity_Element\<^sub>I A Q)
\<Longrightarrow> Identity_Element\<^sub>I (A \<s>\<u>\<b>\<j> P) (P \<and> Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (simp; blast)

lemma
  \<open> Identity_Element\<^sub>I (A \<s>\<u>\<b>\<j> P) (P \<and> Q) \<Longrightarrow> (P \<Longrightarrow> Identity_Element\<^sub>I A Q)\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Inhabited_def
  by (cases P; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P
\<Longrightarrow> Identity_Element\<^sub>E (A \<s>\<u>\<b>\<j> P)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def Premise_def
  by (clarsimp; blast)

lemma (*The above rule is local complete*)
  \<open> Identity_Element\<^sub>E (A \<s>\<u>\<b>\<j> P) \<Longrightarrow> P \<and> Identity_Element\<^sub>E A \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def Premise_def
  by (clarsimp; blast)

lemma [\<phi>reason 1200]: 
  \<open> Identity_Element\<^sub>I A P
\<Longrightarrow> Identity_Element\<^sub>I B Q
\<Longrightarrow> Identity_Element\<^sub>I (A * B) (P \<and> Q) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by (clarsimp simp add: set_mult_expn, insert mult_1_class.mult_1_left; blast)
  (* It is not complete, example: algebra {e,a} where the sep conjunction is only defined
     on the unit, x ## y \<longleftrightarrow> x = e \<and> y = e.
     Let A = B = {e,a}, we have A * B = {e}. Both A B are not stateless but A * B is. *)

lemma [\<phi>reason 1200]: 
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

lemma [\<phi>reason 1200]:
  \<open> Identity_Element\<^sub>I (x \<Ztypecolon> T) P
\<Longrightarrow> Identity_Element\<^sub>I (y \<Ztypecolon> U) Q
\<Longrightarrow> Identity_Element\<^sub>I ((x,y) \<Ztypecolon> T \<^emph> U) (P \<and> Q)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding Identity_Element\<^sub>I_def \<phi>Prod_expn' Transformation_def
  apply (simp add: set_mult_expn)
  using mult_1_class.mult_1_left by blast

lemma [\<phi>reason 1200]: 
  \<open> Identity_Element\<^sub>E (x \<Ztypecolon> T)
\<Longrightarrow> Identity_Element\<^sub>E (y \<Ztypecolon> U)
\<Longrightarrow> Identity_Element\<^sub>E ((x,y) \<Ztypecolon> T \<^emph> U) \<close>
  for T :: \<open>'a \<Rightarrow> 'b::sep_magma_1 BI\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp simp add: \<phi>Prod_expn', insert set_mult_expn, fastforce)


lemma [\<phi>reason 1200]: 
  \<open> Identity_Element\<^sub>E A
\<Longrightarrow> Identity_Element\<^sub>E B
\<Longrightarrow> Identity_Element\<^sub>E (A \<and>\<^sub>B\<^sub>I B) \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp)

lemma (*the above rule is local complete*)
  \<open> Identity_Element\<^sub>E (A \<and>\<^sub>B\<^sub>I B) \<Longrightarrow> Identity_Element\<^sub>E A \<and> Identity_Element\<^sub>E B \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def
  by (clarsimp)

lemma [\<phi>reason 1200]:
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

lemma [\<phi>reason 1200]:
  \<open>Identity_Element\<^sub>I (1 \<Ztypecolon> Itself) True\<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Itself_expn
  by simp

lemma [\<phi>reason 1200]:
  \<open>Identity_Element\<^sub>E (1 \<Ztypecolon> Itself)\<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def Itself_expn
  by simp

lemma [\<phi>reason 1200]:
  \<open>Identity_Element\<^sub>I (any \<Ztypecolon> \<phi>None) True\<close>
  unfolding Identity_Element\<^sub>I_def by simp

lemma [\<phi>reason 1200]:
  \<open>Identity_Element\<^sub>E (any \<Ztypecolon> \<phi>None)\<close>
  unfolding Identity_Element\<^sub>E_def by simp

lemma [\<phi>reason 1200]:
  \<open> (\<And>i. Identity_Element\<^sub>I (A i) (P i))
\<Longrightarrow> Identity_Element\<^sub>I (\<big_ast>i\<in>S. A i) (\<forall>i\<in>S. P i)\<close>
  unfolding Identity_Element\<^sub>I_def Mul_Quant_def Transformation_def
proof clarsimp
  fix v
  assume prems: \<open>(\<And>i. \<forall>v. v \<Turnstile> A i \<longrightarrow> v = 1 \<and> P i)\<close>
                \<open>v \<Turnstile> prod A S\<close>
     and \<open>finite S\<close>
  show \<open>v = 1 \<and> (\<forall>x\<in>S. P x)\<close>
    by (insert prems; induct rule: finite_induct[OF \<open>finite S\<close>]; clarsimp; fastforce)
qed

lemma [\<phi>reason 1200]:
  \<open> (\<And>i. Identity_Element\<^sub>E (A i))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> finite S
\<Longrightarrow> Identity_Element\<^sub>E (\<big_ast>i\<in>S. A i) \<close>
  unfolding Identity_Element\<^sub>E_def Mul_Quant_def Transformation_def Premise_def
proof clarsimp
  fix v
  assume prems: \<open>(\<And>i. 1 \<Turnstile> A i)\<close>
     and \<open>finite S\<close>
  show \<open>1 \<Turnstile> prod A S\<close>
    by (insert prems;
        induct rule: finite_induct[OF \<open>finite S\<close>];
        clarsimp;
        (insert mult_1_class.mult_1_left sep_magma_1_right, blast))
qed


section \<open>Determine Separation Disjunction on Specification Level\<close>

text \<open>The section covers two mechanisms about reasoning the separation disjunction between two given assertions,
i.e., if (respectively to each mechanism) any of or certain of two objects \<open>u \<Turnstile> A\<close> and \<open>v \<Turnstile> B\<close>
satisfying the given assertions \<open>A\<close> and \<open>B\<close>, have defined group operation (of the separation algebra)
between them, denoted by \<open>u ## v\<close> following the paper by Calcagno.
The motivation to infer such compatibility is based on two reasons.

\<^enum> The first mechanism focuses on the property below.
\<close>

definition Separation_Disj :: \<open>('a::sep_magma \<Rightarrow> 'b::sep_magma) \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool\<close>
  where \<open>Separation_Disj \<psi> X Y \<longleftrightarrow> (\<forall>u v. u \<Turnstile> X \<and> v \<Turnstile> Y \<and> \<psi> u ## \<psi> v \<longrightarrow> u ## v)\<close>

text \<open>
  The standard homomorphism from a partial algebra \<open>\<A>\<close> to another \<open>\<B>\<close> only assumes the group operation
  defined (between two certain elements) in \<open>\<A>\<close>, is also defined in \<open>\<B>\<close>, but not reversely, i.e.,
  \<open>u ## v \<longrightarrow> \<psi>(u) ## \<psi>(v)   but not generally   \<psi>(u) ## \<psi>(v) \<longrightarrow> u ## v \<close>
  It blocks the \<open>x \<Ztypecolon> (\<psi> \<Zcomp> T) \<^emph> (\<psi> \<Zcomp> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> zip(x) \<Ztypecolon> (\<psi> \<Zcomp> T \<^emph> U)\<close>, one side of the \<phi>-type separation homomorphism.

  Certainly, to circumvent it, we can ask a stronger assumption i.e. closed homomorphism,
  but not all homomorphisms are closed. An example is super permission...

  As a remedy, \<open>Separation_Disj\<^sub>\<psi> A B\<close> allows the \<phi>-type transformation for non-closed separation homomorphism.

  To enable \<open>x \<Ztypecolon> (\<psi> \<Zcomp> T) \<^emph> (\<psi> \<Zcomp> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> zip(x) \<Ztypecolon> \<psi> \<Zcomp> (T \<^emph> U)\<close>, the weakest condition is
  \<open>SD\<^sub>\<psi>'(A,B) \<longleftrightarrow> (\<forall>u v. u \<Turnstile> A \<and> v \<Turnstile> B \<and> \<psi> u ## \<psi> v \<longrightarrow> \<exists>u' v'. u' \<Turnstile> A \<and> v' \<Turnstile> B \<and> \<psi>(u) * \<psi>(v) = \<psi>(u') * \<psi>(v') \<and> u' ## v')\<close>
  However, \<open>SD\<^sub>\<psi>'(A,B)\<close> is difficult to automate and \<open>\<psi>(u) * \<psi>(v) = \<psi>(u') * \<psi>(v')\<close> is hard to deal.
  We fail to find a reasoning rule splitting \<open>SD\<^sub>\<psi>'(A, B\<^sub>1 \<^emph> B\<^sub>2)\<close> to the respective cases for \<open>B\<^sub>1\<close> and \<open>B\<^sub>2\<close>.
  Due to this, we apply an approximation assuming the \<open>u',v'\<close> are equal to the \<open>u,v\<close>, and then
  we get the form of \<open>Separation_Disj\<^sub>\<psi>\<close> and it has simpler reasoning rules such as
  \<open> Separation_Disj \<psi> A B\<^sub>1
\<Longrightarrow> Separation_Disj \<psi> A B\<^sub>2
\<Longrightarrow> Separation_Disj \<psi> A (B\<^sub>1 * B\<^sub>2)\<close> for separation homomorphism \<open>\<psi>\<close>.

\<^enum> Another mechanism focus on satisfaction of multiplicative conjunction, of the following form,
  \<open>Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> with_what_condition \<longrightarrow> Inhabited (A * B)\<close>

  The implication reasoning \<open>Inhabited A \<longrightarrow> P\<close> infers a weaker but simpler approximation
  of the pure fact implied inside \<open>A\<close>.
  However, only the weakening part is not enough for \<phi>-types of mappings such as
  \<open>f \<Ztypecolon> T \<Rrightarrow> U := {g. (\<forall>u x. u \<Turnstile> x \<Ztypecolon> T \<longrightarrow> g(y) \<Turnstile> f(x) \<Ztypecolon> U)}\<close> (forward simulation)
  whose domain \<phi>-type \<open>T\<close> is contravariant.
  To extract its implication, the dual of the implication reasoning is required, namely satisfaction reasoning.
  It infers a stronger approximation \<open>Q\<close> such that \<open>Q \<longrightarrow> Inhabited A\<close> for a given assertion \<open>A\<close>.
  By it, we can complete the implication rule of \<open>f \<Ztypecolon> T \<Rrightarrow> U\<close>,
  \<open> (\<And>x. Q x \<longrightarrow> Inhabited (x \<Ztypecolon> T))
\<Longrightarrow> (\<And>x. Inhabited (x \<Ztypecolon> T) \<rightarrow> P x)
\<Longrightarrow> (\<And>y. Inhabited (y \<Ztypecolon> U) \<rightarrow> P' y)
\<Longrightarrow> Inhabited (f \<Ztypecolon> T \<Rrightarrow> U) \<longrightarrow> (\<forall>x. Q x \<longrightarrow> P x \<and> P' (f x))\<close>.
  
  The rules of satisfaction reasoning for logical connectives are given where???, except those
  for conjunctive operators (\<open>\<and>\<close> and \<open>*\<close>).
  For \<open>\<and>\<close>, it is due to that the inhabitance of each side of the conjunction
  does not imply the inhabitance of the both sides, because the residents may not equal.
  For \<open>*\<close>, it is due to, though we have two residents \<open>u \<Turnstile> A\<close> and \<open>v \<Turnstile> B\<close> for each assertions,
  we do not know if \<open>u ## v\<close>, so we cannot deduce \<open>u * v \<Turnstile> A * B\<close>.

  Even though \<open>\<and>\<close> is less-intuitive and rarely used under our interpretation of data refinement,
  multiplicative conjunction is essential,
  especially for example, when the key of the map is a tuple and the tuple fields are connected by \<open>*\<close>.

The satisfaction reasoning of multiplicative conjunctions, together with the above \<open>Separation_Disj\<^sub>\<psi>\<close>,
relies on the notion of \<^emph>\<open>domainoid\<close>, which is invented in order to reason the separation disjunction
on an abstract domain, particularly by means of \<open>Domainoid_Homo\<close> presented later.
\<close>

type_synonym ('a,'d) domainoid = \<open> 'a \<Rightarrow> 'd \<close>
  \<comment> \<open>A forgetful functor that extracts domains and trims data\<close>

definition domainoid :: \<open>('a::sep_magma,'d::sep_magma) domainoid \<Rightarrow> bool\<close>
  where \<open>domainoid \<delta> \<longleftrightarrow> closed_homo_sep \<delta>\<close>

text \<open>A domainoid extraction \<open>\<delta>\<close> is a closed homomorphism and also a forgetful functor that extracts the domain
  parts and forgets the data parts of a SA, such that \<open>\<delta>(x) ## \<delta>(y) \<longleftrightarrow> x ## y\<close> is sufficient to
  determine the separation disjunction \<open>x ## y\<close>, but of a simpler expression.
  Usually, \<open>\<delta>(x)\<close> is the domain of the resource \<open>x\<close>, such as the address of a memory object,
  but it can be others like \<open>address \<rightarrow> permission\<close> the permission map of a sharing memory
  \<open>address \<rightarrow> permission \<times> value\<close>. Considering this, we call it domain-oid extraction or simply domainoid.

  By extracting the domainoids of two \<phi>-type assertions or other assertions, we can determine the
  separation disjunction between the two assertions without involving and reducing to
  concrete representations of the resources, as usually we only abstract the data and leave the
  resource identifiers untouched.

  With abbreviation \<open>domainoid d \<triangleq> closed_homo_sep \<delta>\<close> we emphasize \<open>\<delta>\<close> is a domainoid.

  Modality \<open>\<DD>[d] S \<triangleq> (\<delta> u \<Ztypecolon> Itself \<s>\<u>\<b>\<j> u. u \<Turnstile> S \<and> domainoid \<delta>)\<close> maps an assertion \<open>S\<close> to the domainoids
  of its resources, if we still use separation logic to specify the domainoids (on the algebra of the domainoids).
  The modality is homomorphic over all logical connectives except additive conjunctions (including universal quantification).
  Though domainoid is designed to solve satisfaction of multiplicative conjunction, it still can do nothing
  to additive conjunctions.

  For mapping the domainoid functor onto the abstract domain of a \<phi>-type \<open>x \<Ztypecolon> T\<close>,
  there are lower and upper homomorphisms giving stronger and lower approximations respectively
  for domainoid \<open>d\<close>,
  \<open>Domainoid_Homo\<^sub>L d T d' \<longleftrightarrow> (\<forall>x. d' x \<longrightarrow> \<DD>[d] (x \<Ztypecolon> T) )\<close>
  \<open>Domainoid_Homo\<^sub>U d T d' \<longleftrightarrow> (\<forall>x. \<DD>[d] (x \<Ztypecolon> T) \<longrightarrow> d' x )\<close>
  We use approximations in case of the precise expression is too complicated.

  The lower homomorphism is used for deducing the satisfaction of multiplicative conjunction.
  The upper homomorphism is for enabling transformation of non-closed separation homomorphism.
\<close>

subsection \<open>The Algebra of Domainoid\<close>

definition domainoid_BI_functor :: \<open>('a,'d) domainoid \<Rightarrow> 'a::sep_magma BI \<Rightarrow> 'd::sep_magma set\<close> ("\<DD>[_]" [10] 1000)
  where \<open>(\<DD>[d] S) = {d u |u. u \<Turnstile> S \<and> domainoid d}\<close>

declare [[
  \<phi>reason_default_pattern \<open>\<DD>[?d] ?S \<le> ?S'\<close> \<Rightarrow> \<open>\<DD>[?d] ?S \<le> ?S'\<close> \<open>\<DD>[?d] ?S \<le> ?var_S'\<close> (200)
                      and \<open>?S \<le> \<DD>[?d] ?S'\<close> \<Rightarrow> \<open>?S \<le> \<DD>[?d] ?S'\<close> \<open>?var_S \<le> \<DD>[?d] ?S'\<close> (200)
]]

lemma domainoid_BI_functor_expn[\<phi>expns, simp]:
  \<open>p \<Turnstile> \<DD>[d] S \<longleftrightarrow> (\<exists>u. p = d u \<and> u \<Turnstile> S \<and> domainoid d)\<close>
  unfolding domainoid_BI_functor_def Satisfaction_def
  by clarsimp

lemma domainoid_BI_functor_expn'[\<phi>expns, simp]:
  \<open>p \<in> \<DD>[d] S \<longleftrightarrow> (\<exists>u. p = d u \<and> u \<Turnstile> S \<and> domainoid d)\<close>
  unfolding domainoid_BI_functor_def Satisfaction_def
  by clarsimp


subsubsection \<open>Homomorphism of \<phi>-Type\<close>

(* A --domainoid--> D(A)
   \<down> \<psi>               \<down> D(\<psi>)
   B --domainoid--> D(B) *)
definition homo_domainoid :: \<open> ('a::sep_magma,'da::sep_magma) domainoid
                            \<Rightarrow> ('b::sep_magma,'ba::sep_magma) domainoid
                            \<Rightarrow> ('a \<Rightarrow> 'b)
                            \<Rightarrow> ('da \<Rightarrow> 'ba)
                            \<Rightarrow> bool\<close>
  where \<open>homo_domainoid D\<^sub>A D\<^sub>B \<psi> \<psi>\<^sub>D \<longleftrightarrow>
            domainoid D\<^sub>A \<and> domainoid D\<^sub>B \<and> homo_sep \<psi> \<and> (\<forall>a. D\<^sub>B (\<psi> a) = \<psi>\<^sub>D (D\<^sub>A a))\<close>

definition Domainoid_Homo\<^sub>U :: \<open>('c::sep_magma,'d::sep_magma) domainoid \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'd set) \<Rightarrow> bool\<close>
  where \<open>Domainoid_Homo\<^sub>U dm T dm' \<longleftrightarrow> domainoid dm \<and> (\<forall>x u. u \<Turnstile> \<DD>[dm] (x \<Ztypecolon> T) \<longrightarrow> u \<in> dm' x )\<close>
  \<comment> \<open>\<phi>-Type Homomorphism, \<open>dm'\<close> is the image of the \<open>dm\<close> in the abstract domain\<close>

definition Domainoid_Homo\<^sub>L :: \<open>('c::sep_magma,'d::sep_magma) domainoid \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'd set) \<Rightarrow> bool\<close>
  where \<open>Domainoid_Homo\<^sub>L dm T dm' \<longleftrightarrow> domainoid dm \<and> (\<forall>x u'. u' \<in> dm' x \<longrightarrow> u' \<Turnstile> \<DD>[dm] (x \<Ztypecolon> T) )\<close>
  \<comment> \<open>\<phi>-Type Homomorphism, \<open>dm'\<close> is the image of the \<open>dm\<close> in the abstract domain\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 1000]:
  \<open> Domainoid_Homo\<^sub>L d T dm\<^sub>T
\<Longrightarrow> dm\<^sub>T x \<le> \<DD>[d] (x \<Ztypecolon> T)\<close>
  unfolding Domainoid_Homo\<^sub>L_def set_eq_iff
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> Domainoid_Homo\<^sub>U d T dm\<^sub>T
\<Longrightarrow> \<DD>[d] (x \<Ztypecolon> T) \<le> dm\<^sub>T x\<close>
  unfolding Domainoid_Homo\<^sub>U_def set_eq_iff
  by clarsimp


subsubsection \<open>Homomorphism over BI connectives\<close>

lemma \<DD>_1:
  \<open> domainoid d
\<Longrightarrow> homo_one d
\<Longrightarrow> \<DD>[d] 1 = 1 \<close>
  unfolding BI_eq_iff homo_one_def
  by simp

lemma \<DD>_0:
  \<open> \<DD>[d] 0 = 0 \<close>
  unfolding BI_eq_iff
  by clarsimp

lemma \<DD>_Multiplicative_Conj:
  \<open>\<DD>[d] (A * B) = \<DD>[d] A * \<DD>[d] B\<close>
  unfolding BI_eq_iff
  by (clarsimp simp add: domainoid_def closed_homo_sep_def closed_homo_sep_disj_def homo_sep_def
                         homo_sep_mult_def; rule; clarsimp; metis)

lemma \<DD>_Mul_Quant:
  \<open> domainoid d
\<Longrightarrow> homo_one d
\<Longrightarrow> \<DD>[d] (\<big_ast>i\<in>S. A i) = (\<big_ast>i\<in>S. \<DD>[d] (A i)) \<close>
proof -
  assume \<open>domainoid d\<close> and \<open>homo_one d\<close>
  { assume \<open>finite S\<close>
    have \<open>\<DD>[d] (\<Prod>i\<in>S. A i) = (\<Prod>i\<in>S. \<DD>[d] (A i))\<close>
      by (induct rule: finite_induct[OF \<open>finite S\<close>];
          simp add: \<DD>_1 \<open>domainoid d\<close> \<open>homo_one d\<close> \<DD>_Multiplicative_Conj)
  }
  then show \<open>\<DD>[d] (\<big_ast>i\<in>S. A i) = (\<big_ast>i\<in>S. \<DD>[d] (A i))\<close>
    unfolding Mul_Quant_def
    by (smt (verit, best) Subjection_Flase Subjection_True \<DD>_0)
qed

lemma \<DD>_Additive_Disj:
  \<open>\<DD>[d] (A + B) = \<DD>[d] A + \<DD>[d] B\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)

lemma \<DD>_ExSet:
  \<open>\<DD>[d] (ExSet S) = (\<exists>*c. \<DD>[d] (S c))\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)

lemma \<DD>_Subjection:
  \<open>\<DD>[d] (S \<s>\<u>\<b>\<j> P) = (\<DD>[d] S \<s>\<u>\<b>\<j> P)\<close>
  unfolding BI_eq_iff
  by (clarsimp; metis)


subsubsection \<open>Reasoning Rules of Approximation\<close>

lemma [\<phi>reason 1000]:
  \<open> domainoid d
\<Longrightarrow> homo_one d
\<Longrightarrow> \<DD>[d] 1 \<le> 1 \<close>
  unfolding \<DD>_1 by simp

lemma [\<phi>reason 1000]:
  \<open> domainoid d
\<Longrightarrow> homo_one d
\<Longrightarrow> 1 \<le> \<DD>[d] 1 \<close>
  unfolding \<DD>_1 by simp

lemma [\<phi>reason 1000]:
  \<open> 0 \<le> \<DD>[d] 0 \<close>
  unfolding \<DD>_0 by simp

lemma [\<phi>reason 1000]:
  \<open> \<DD>[d] 0 \<le> 0 \<close>
  unfolding \<DD>_0 by simp

lemma [\<phi>reason 1000]:
  \<open> A' \<le> \<DD>[d] A
\<Longrightarrow> B' \<le> \<DD>[d] B
\<Longrightarrow> A' * B' \<le> \<DD>[d] (A * B)\<close>
  unfolding \<DD>_Multiplicative_Conj
  by (meson order.trans times_set_subset(1) times_set_subset(2))

lemma [\<phi>reason 1000]:
  \<open> \<DD>[d] A \<le> A'
\<Longrightarrow> \<DD>[d] B \<le> B'
\<Longrightarrow> \<DD>[d] (A * B) \<le> A' * B'\<close>
  unfolding \<DD>_Multiplicative_Conj
  by (meson order.trans times_set_subset(1) times_set_subset(2))

lemma [\<phi>reason 1000]:
  \<open> domainoid d
\<Longrightarrow> homo_one d
\<Longrightarrow> (\<And>i\<in>S. \<DD>[d] (A i) \<le> A' i)
\<Longrightarrow> \<DD>[d] (\<big_ast>i\<in>S. A i) \<le> (\<big_ast>i\<in>S. A' i) \<close>
  unfolding \<DD>_Mul_Quant
  by (simp add: Mul_Quant_ord)

lemma [\<phi>reason 1000]:
  \<open> domainoid d
\<Longrightarrow> homo_one d
\<Longrightarrow> (\<And>i\<in>S. A' i \<le> \<DD>[d] (A i))
\<Longrightarrow> (\<big_ast>i\<in>S. A' i) \<le> \<DD>[d] (\<big_ast>i\<in>S. A i) \<close>
  unfolding \<DD>_Mul_Quant
  by (simp add: Mul_Quant_ord)

lemma [\<phi>reason 1000]:
  \<open> A' \<le> \<DD>[d] A
\<Longrightarrow> B' \<le> \<DD>[d] B
\<Longrightarrow> A' + B' \<le> \<DD>[d] (A + B) \<close>
  unfolding \<DD>_Additive_Disj
  by (clarsimp; fastforce)

lemma [\<phi>reason 1000]:
  \<open> \<DD>[d] A \<le> A'
\<Longrightarrow> \<DD>[d] B \<le> B'
\<Longrightarrow> \<DD>[d] (A + B) \<le> A' + B' \<close>
  unfolding \<DD>_Additive_Disj
  by (clarsimp; fastforce)

lemma [\<phi>reason 1000]:
  \<open> (\<And>c. \<DD>[d] (S c) \<le> S' c)
\<Longrightarrow> \<DD>[d] (ExSet S) \<le> ExSet S'\<close>
  unfolding \<DD>_ExSet
  by (simp add: ExSet_ord)

lemma [\<phi>reason 1000]:
  \<open> (\<And>c. S' c \<le> \<DD>[d] (S c))
\<Longrightarrow> ExSet S' \<le> \<DD>[d] (ExSet S)\<close>
  unfolding \<DD>_ExSet
  by (simp add: ExSet_ord)

lemma [\<phi>reason 1000]:
  \<open> ((\<DD>[d] S) \<s>\<u>\<b>\<j> P) \<le> S'
\<Longrightarrow> \<DD>[d] (S \<s>\<u>\<b>\<j> P) \<le> S'\<close>
  unfolding \<DD>_Subjection
  by (clarsimp simp add: Subjection_ord)

lemma [\<phi>reason 1000]:
  \<open> S' \<le> ((\<DD>[d] S) \<s>\<u>\<b>\<j> P)
\<Longrightarrow> S' \<le> \<DD>[d] (S \<s>\<u>\<b>\<j> P)\<close>
  unfolding \<DD>_Subjection
  by (clarsimp simp add: Subjection_ord)


subsection \<open>Domainoid gives Satisfaction of Separation Conjunction\<close>

lemma [\<phi>reason 1000]:
  \<open> Pa \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A
\<Longrightarrow> Pb \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> B
\<Longrightarrow> domainoid d
\<Longrightarrow> A' \<le> \<DD>[d] A \<comment>\<open>expand \<open>\<DD>[d] A, \<DD>[d] B\<close> to a simpler but still strong enough approximation\<close>
\<Longrightarrow> B' \<le> \<DD>[d] B
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Pa \<and> Pb \<longrightarrow> (\<exists>a b. a \<in> A' \<and> b \<in> B' \<and> a ## b))
\<Longrightarrow> Pa \<and> Pb \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A * B\<close>
  unfolding Inhabited_def subset_iff Premise_def Action_Tag_def
  by (clarsimp simp add: domainoid_def closed_homo_sep_def closed_homo_sep_disj_def; blast)

lemma \<comment> \<open>The above rule is reversible for any domainoid \<open>d\<close>\<close>
  \<open> domainoid d \<Longrightarrow> Inhabited (A * B) \<longleftrightarrow> (\<exists>a b. a \<in> \<DD>[d] A \<and> b \<in> \<DD>[d] B \<and> a ## b)\<close>
  unfolding Inhabited_def
  by (clarsimp simp add: domainoid_def closed_homo_sep_def closed_homo_sep_disj_def; blast)


subsection \<open>Domainoid gives Separation_Disj\<close>

lemma [\<phi>reason 1000]:
  \<open> Domainoid_Homo\<^sub>U dm\<^sub>A T dm\<^sub>T
\<Longrightarrow> Domainoid_Homo\<^sub>U dm\<^sub>A U dm\<^sub>U
\<Longrightarrow> homo_domainoid dm\<^sub>A dm\<^sub>B \<psi> \<psi>\<^sub>D \<and> has_\<psi>\<^sub>D = True \<or>\<^sub>c\<^sub>u\<^sub>t has_\<psi>\<^sub>D = False
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>d\<^sub>x d\<^sub>y. d\<^sub>x \<in> dm\<^sub>T x \<and> d\<^sub>y \<in> dm\<^sub>U y \<and> (has_\<psi>\<^sub>D \<longrightarrow> \<psi>\<^sub>D d\<^sub>x ## \<psi>\<^sub>D d\<^sub>y) \<longrightarrow> d\<^sub>x ## d\<^sub>y)
\<Longrightarrow> Separation_Disj \<psi> (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<close>
  for \<psi> :: \<open>'c::sep_magma \<Rightarrow> 'cc::sep_magma\<close>
  unfolding Separation_Disj_def Domainoid_Homo\<^sub>U_def Orelse_shortcut_def
  by (clarsimp simp add: domainoid_def Premise_def homo_domainoid_def
                         closed_homo_sep_def closed_homo_sep_disj_def; metis)


lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> A B\<^sub>1
\<Longrightarrow> Separation_Disj \<psi> A B\<^sub>2
\<Longrightarrow> Separation_Disj \<psi> A (B\<^sub>1 * B\<^sub>2)\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_right)

lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> A (fst y \<Ztypecolon> U\<^sub>1)
\<Longrightarrow> Separation_Disj \<psi> A (snd y \<Ztypecolon> U\<^sub>2)
\<Longrightarrow> Separation_Disj \<psi> A (y \<Ztypecolon> U\<^sub>1 \<^emph> U\<^sub>2)\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_right)

lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> A\<^sub>1 B
\<Longrightarrow> Separation_Disj \<psi> A\<^sub>2 B
\<Longrightarrow> Separation_Disj \<psi> (A\<^sub>1 * A\<^sub>2) B\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_left)

lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> (fst x \<Ztypecolon> T\<^sub>1) B
\<Longrightarrow> Separation_Disj \<psi> (snd x \<Ztypecolon> T\<^sub>2) B
\<Longrightarrow> Separation_Disj \<psi> (x \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2) B\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_left)

(*definition Separation_Disj :: \<open>'a::sep_magma set \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where \<open>Separation_Disj X Y \<longleftrightarrow> (\<forall>u v. u \<Turnstile> X \<and> v \<Turnstile> Y \<longrightarrow> u ## v)\<close>*)



section \<open>Declaration of Reasonig Process\<close>

subsection \<open>ToA Reasoning\<close>

text \<open>NToA : Normalized ToA reasoning, the usual ToA reasoning having simplification and other
             normalization at the beginning. \<close>

consts NToA' :: \<open>bool \<comment> \<open>whether to reason deeper transformation for each desired \<phi>-type
                          by invoking more time-consuming reasoning process,
                          or just apply unification to match the desired.\<close>
              \<Rightarrow> mode\<close>

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

lemma [\<phi>reason 3000 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P @action NToA' ?mode\<close>]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action NToA' mode\<close>
  unfolding Action_Tag_def using transformation_refl .

subsection \<open>Declaration of Convergence of Branch\<close>

consts invoke_branch_convergence :: \<open>action\<close>


subsection \<open>Removing Values\<close> (*TODO: depreciate me*)

definition \<open>Remove_Values (Input::assn) (Output::assn) \<longleftrightarrow> (Input \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Output)\<close>

text \<open>The process \<^prop>\<open>Remove_Values Input Output\<close> removes value assertions \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<close>
  from the assertion \<open>Input\<close>. Bounded values such the return value of a procedure are not removed.\<close>


subsection \<open>Value Operations\<close> (*TODO: depreciate me*)


subsubsection \<open>Operations for a single Value\<close>

(*
lemma "_rule_extract_and_remove_the_first_value_"[no_atp]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y \<w>\<i>\<t>\<h> P @action NToA' False
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)
*)

lemma "_rule_push_a_value_"[no_atp]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B * (x \<Ztypecolon> \<v>\<a>\<l>[v] T) \<close>
  for A :: \<open>'a::sep_magma_1 BI\<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: Val_expn)

(*
subsubsection \<open>Collects all Values in an Assertion / from the State Sequent\<close>

consts collect_clean_value :: \<open>bool \<Rightarrow> action\<close>

lemma apply_collect_clean_value[no_atp]:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> V @action collect_clean_value WHETHER_CLEAN
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> V\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1200 for \<open>?S \<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S' \<w>\<i>\<t>\<h> ?V @action collect_clean_value True\<close>]:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> V @action collect_clean_value True
\<Longrightarrow> S \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> V @action collect_clean_value True\<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?S \<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S' \<w>\<i>\<t>\<h> ?V @action collect_clean_value False\<close>]:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> V @action collect_clean_value False
\<Longrightarrow> S \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<w>\<i>\<t>\<h> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> V
    @action collect_clean_value False\<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100 for \<open>?S\<heavy_comma> ?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S' \<w>\<i>\<t>\<h> ?V @action collect_clean_value ?CLEAN\<close>]:
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> V @action collect_clean_value CLEAN
\<Longrightarrow> S\<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S'\<heavy_comma> X \<w>\<i>\<t>\<h> V @action collect_clean_value CLEAN\<close>
  unfolding Action_Tag_def using implies_right_prod .

lemma [\<phi>reason 1050 for \<open>?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S' \<w>\<i>\<t>\<h> ?V @action collect_clean_value True\<close>]:
  \<open> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Void \<w>\<i>\<t>\<h> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> True
    @action collect_clean_value True\<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1050 for \<open>?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S' \<w>\<i>\<t>\<h> ?V @action collect_clean_value False\<close>]:
  \<open> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<w>\<i>\<t>\<h> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> True
    @action collect_clean_value False\<close>
  unfolding Action_Tag_def Transformation_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1000 for \<open>?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S' \<w>\<i>\<t>\<h> ?V @action collect_clean_value ?clean\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> True @action collect_clean_value clean\<close>
  unfolding Action_Tag_def using transformation_refl .
*)
end
