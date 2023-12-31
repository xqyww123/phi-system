chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

text \<open>The part includes small process that can be built without infrastructure of
  IDE-CP, and declarations of other large process.\<close>

theory IDE_CP_Reasoning1
  imports Spec_Framework Phi_BI
  abbrevs "<subj-reasoning>" = "\<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g>"
begin

section \<open>Annotations Guiding the Reasoning\<close>

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

paragraph \<open>Identity_Element\<close>

lemma [\<phi>reason %cutting]:
  \<open> Identity_Element\<^sub>I (S x) P
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y)) P \<close>
  by simp

lemma [\<phi>reason %cutting]:
  \<open> Identity_Element\<^sub>E (S x)
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y)) \<close>
  by simp

paragraph \<open>Transformation Rules\<close>

lemma [\<phi>reason 1000]:
  \<open> S x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

(*TODO! this \<A>?!*)
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
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P @action \<A>
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<lambda>\<^sub>\<beta> y. S y) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P @action \<A> \<close>
  by simp



section \<open>Small Reasoning Process\<close>

subsection \<open>Auxiliaries\<close>


subsubsection \<open>Semantic Expansion of \<phi>-Types\<close>

consts MODE_\<phi>EXPN :: mode \<comment> \<open>relating to named_theorems \<open>\<phi>expn\<close>\<close>

abbreviation \<phi>expn_Premise ("<\<phi>expn> _" [26] 26) where \<open>\<phi>expn_Premise \<equiv> Premise MODE_\<phi>EXPN\<close>

\<phi>reasoner_ML \<phi>expn_Premise 10 (\<open><\<phi>expn> ?P\<close>) = \<open>
  Seq.ORELSE (
  Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) (fn ctxt =>
                            ctxt addsimps (Useful_Thms.get ctxt)) {fix_vars=false}),
  Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) (fn ctxt =>
        Phi_Expansions.enhance (ctxt addsimps (Useful_Thms.get ctxt))) {fix_vars=false})) o snd
\<close>

lemma Premise_MODE_\<phi>EXPN[iff]: \<open><\<phi>expn> True\<close>
  unfolding Premise_def ..

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

lemma named_ExSet: "(\<exists>*c. T c) = (\<exists>*c. T (tag c) )" by (clarsimp simp add: named_exists BI_eq_iff)


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
          Named_Theorems.get ctxt \<^named_theorems>\<open>frame_var_rewrs\<close>) {fix_vars=false}) o snd\<close>

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
  "\<phi>IntroFrameVar (if C then Some R else None) (S \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) S (T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) T"
  unfolding \<phi>IntroFrameVar_def REMAINS_def by simp

lemma \<phi>IntroFrameVar'_Yes:
  " \<phi>IntroFrameVar' R (S \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R) S (\<lambda>ret. R * T ret) T (\<lambda>ex. R * E ex) E"
  unfolding \<phi>IntroFrameVar'_def REMAINS_def by simp

\<phi>reasoner_ML \<phi>IntroFrameVar 1000 ("\<phi>IntroFrameVar ?R ?S' ?S ?T' ?T") =
\<open>fn (_, (ctxt, sequent)) =>
  let val (Const (\<^const_name>\<open>\<phi>IntroFrameVar\<close>, _) $ _ $ _ $ S $ _ $ _) =
          Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
      val suppressed = case S
                         of Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ C $ R =>
                              Term.is_Var (Term.head_of R) andalso
                              (case C of Const(\<^const_name>\<open>True\<close>, _) => true
                                       | _ => Term.is_Var (Term.head_of C))
                          | _ => (case hd (Phi_Syntax.strip_separations S)
                         of (\<^const>\<open>TAIL\<close> $ _) => true
                          | RR => Term.is_Var (Term.head_of RR))
  in if suppressed
     then Seq.single (ctxt, @{thm \<phi>IntroFrameVar_No}  RS sequent)
     else Seq.single (ctxt, @{thm \<phi>IntroFrameVar_Yes} RS sequent)
  end\<close>

\<phi>reasoner_ML \<phi>IntroFrameVar' 1000 ("\<phi>IntroFrameVar' ?R ?S' ?S ?T' ?T ?E' ?E") =
\<open>fn (_, (ctxt, sequent)) =>
  let val (Const (\<^const_name>\<open>\<phi>IntroFrameVar'\<close>, _) $ _ $ _ $ S $ _ $ _ $ _ $ _) =
          Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
      val suppressed = case S
                         of Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ C $ R =>
                              Term.is_Var (Term.head_of R) andalso
                              (case C of Const(\<^const_name>\<open>True\<close>, _) => true
                                       | _ => Term.is_Var (Term.head_of C))
                          | _ => (case hd (Phi_Syntax.strip_separations S)
                         of (\<^const>\<open>TAIL\<close> $ _) => true
                          | RR => Term.is_Var (Term.head_of RR))
  in if suppressed
     then Seq.single (ctxt, @{thm \<phi>IntroFrameVar'_No}  RS sequent)
     else Seq.single (ctxt, @{thm \<phi>IntroFrameVar'_Yes} RS sequent)
  end\<close>

hide_fact \<phi>IntroFrameVar_No \<phi>IntroFrameVar'_No \<phi>IntroFrameVar_Yes \<phi>IntroFrameVar'_Yes


subsubsection \<open>Reasoning Goals Embedded in BI Assertion\<close>

definition Subj_Reasoning :: \<open> 'p set \<Rightarrow> bool \<Rightarrow> 'p set \<close> (infixl "\<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g>" 15)
  where \<open>Subj_Reasoning \<equiv> Subjection\<close>

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g> A \<w>\<i>\<t>\<h> P\<close>
  unfolding Subj_Reasoning_def Transformation_def
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
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty)
                        (fn ctxt => Embed_into_Phi_Type.equip ctxt) {fix_vars=true}) o snd\<close>

 
lemmas [embed_into_\<phi>type] =
    \<phi>None_itself_is_one[where any=\<open>()\<close>] \<phi>Prod_expn' \<phi>Any_def

ML \<open>Embed_into_Phi_Type.print \<^context> true\<close>

paragraph \<open>Debug Usage\<close>

method_setup embed_into_\<phi>type = \<open>
let val no_asmN = "no_asm";
    val no_asm_useN = "no_asm_use";
    val no_asm_simpN = "no_asm_simp";
    val asm_lrN = "asm_lr";

    fun conv_mode x =
      ((Args.parens (Args.$$$ no_asmN) >> K simp_tac ||
        Args.parens (Args.$$$ no_asm_simpN) >> K asm_simp_tac ||
        Args.parens (Args.$$$ no_asm_useN) >> K full_simp_tac ||
        Scan.succeed asm_full_simp_tac) |> Scan.lift) x;
in conv_mode >> (fn simp => fn ctxt =>
      Method.METHOD (fn ths => Method.insert_tac ctxt ths 1 THEN simp
          (Phi_Conv.Embed_into_Phi_Type.equip ctxt) 1 ))
end\<close>

subsection \<open>Semantic Type of Multiple Values\<close>

lemma [\<phi>reason 1200 for \<open>\<phi>_Have_Types (\<lambda>vs. ?R vs\<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst vs] ?T) _\<close>]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R vs) TYs
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R (\<phi>V_snd vs)\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst vs] T) (TY#TYs)\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def \<phi>arg_forall \<phi>SemType_def subset_iff
  by (clarsimp simp add: to_vals_prod_def to_vals_VAL_def Val_inh_rewr)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[vs] T) [TY]\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def \<phi>arg_forall \<phi>SemType_def subset_iff
  by (clarsimp simp add: to_vals_prod_def to_vals_VAL_def Val_inh_rewr)

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


subsection \<open>Removing Values\<close> (*TODO: depreciate me*)

definition \<open>Remove_Values (Input::assn) (Output::assn) \<longleftrightarrow> (Input \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Output)\<close>

text \<open>The process \<^prop>\<open>Remove_Values Input Output\<close> removes value assertions \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<close>
  from the assertion \<open>Input\<close>. Bounded values such the return value of a procedure are not removed.\<close>

text \<open>Given an assertion X, antecedent \<^term>\<open>Remove_Values X X'\<close>
  returns X' where all free value assertions \<^term>\<open>x \<Ztypecolon> Val raw T\<close> filtered out, where \<^term>\<open>raw\<close>
  contains at least one free variable of \<^typ>\<open>'a \<phi>arg\<close>.

  It is typically used in exception. When a computation triggers an exception at state X,
    the state recorded in the exception is exactly X' where value assertions are filtered out.\<close>

declare [[\<phi>reason_default_pattern \<open>Remove_Values ?X _\<close> \<Rightarrow> \<open>Remove_Values ?X _\<close> (100)]]

(* lemma [\<phi>reason for \<open>Remove_Values ?ex ?var_X ?Z\<close>]:
  \<open>Remove_Values ex X X\<close>
  unfolding Remove_Values_def using transformation_refl . *)

lemma [\<phi>reason 1200]:
  \<open>(\<And>c. Remove_Values (T c) (T' c))
\<Longrightarrow> Remove_Values (ExSet T) (ExSet T')\<close>
  unfolding Remove_Values_def Transformation_def
  by simp blast

lemma [\<phi>reason 1200]:
  \<open>(\<And>c. Remove_Values (R * T c) (R' * T' c))
\<Longrightarrow> Remove_Values (R * ExSet T) (R' * ExSet T')\<close>
  unfolding Remove_Values_def Transformation_def
  by simp blast

lemma [\<phi>reason 1200]:
  \<open> Remove_Values T T'
\<Longrightarrow> Remove_Values (T \<s>\<u>\<b>\<j> P) (T' \<s>\<u>\<b>\<j> P)\<close>
  unfolding Remove_Values_def Transformation_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values (R * T) (R' * T')
\<Longrightarrow> Remove_Values (R * (T \<s>\<u>\<b>\<j> P)) (R' * (T' \<s>\<u>\<b>\<j> P))\<close>
  unfolding Remove_Values_def Transformation_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values B B'
\<Longrightarrow> Remove_Values (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) (A' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B')\<close>
  unfolding REMAINS_def Remove_Values_def Transformation_def
  by (cases C; simp; blast)

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values B B'
\<Longrightarrow> Remove_Values (A + B) (A' + B')\<close>
  unfolding Remove_Values_def Transformation_def
  by blast

lemma [\<phi>reason 1200]:
  \<open> Remove_Values R R'
\<Longrightarrow> Remove_Values (R * (x \<Ztypecolon> Val raw T)) R'\<close>
  unfolding Remove_Values_def Transformation_def by (simp add: Val_expn)

lemma [\<phi>reason 1200]:
  \<open>Remove_Values (x \<Ztypecolon> Val raw T) 1\<close>
  unfolding Remove_Values_def Transformation_def by (simp add: Val_expn)

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values (1 * A) A'\<close>
  unfolding Remove_Values_def Transformation_def by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values (A * 1) A'\<close>
  unfolding Remove_Values_def Transformation_def by simp

lemma [\<phi>reason 1200]:
  \<open>Remove_Values (A * 0) 0\<close>
  unfolding Remove_Values_def Transformation_def by simp

lemma [\<phi>reason 1100]:
  \<open> Remove_Values B B'
\<Longrightarrow> Remove_Values A A'
\<Longrightarrow> Remove_Values (A * B) (A' * B')\<close>
  unfolding Remove_Values_def Transformation_def by simp blast

lemma [\<phi>reason 1000]:
  \<open> Remove_Values A A\<close>
  unfolding Remove_Values_def
  by simp



section \<open>Declaration of Reasonig Process\<close>

subsection \<open>Declaration of Convergence of Branch\<close>

consts invoke_br_join :: \<open>action\<close> (*TODO: move?*)


end
