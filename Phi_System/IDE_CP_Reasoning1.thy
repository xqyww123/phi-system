chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

text \<open>The part includes small process that can be built without infrastructure of
  IDE-CP, and declarations of other large process.\<close>

theory IDE_CP_Reasoning1
  imports Spec_Framework
begin

section \<open>Annotations Guiding the Reasoning\<close>

subsection \<open>General Tags\<close>

consts SOURCE :: mode
       TARGET :: mode
       ABNORMAL :: mode

subsection \<open>Small Annotations\<close>

subsubsection \<open>Matches\<close>

definition Assertion_Matches :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixl "<matches>" 18)
  where \<open>(S <matches> pattern) = S\<close>

text \<open>The annotation marking on a target \<^term>\<open>Y <matches> A\<close> in a ToA or a view shift
  restricts that the source have to first match pattern \<open>A\<close>.\<close>

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P \<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (Y <matches> A) \<a>\<n>\<d> P\<close>
  unfolding Assertion_Matches_def .

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P \<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> (Y <matches> A) \<a>\<n>\<d> P\<close>
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

subsubsection \<open>Structural Morphism\<close>

(*TODO: explain*)

definition SMorphism :: \<open>'a \<Rightarrow> 'a\<close> ("SMORPH _" [17] 16)
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

declare [[\<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> Automatic_Morphism _ _ \<and> _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> Automatic_Morphism _ _ \<and> _\<close>    (110)
  and \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ *  \<blangle> ?Y \<brangle> \<a>\<n>\<d> Automatic_Morphism _ _ \<and> _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ *  \<blangle> ?Y \<brangle> \<a>\<n>\<d> Automatic_Morphism _ _ \<and> _\<close>    (120)
]]


section \<open>Normalization of Assertions\<close>

consts assertion_simps :: \<open>mode \<Rightarrow> mode\<close>

ML \<open>
structure Assertion_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>assertion_simps\<close>
  val comment = "Simplification rules normalizing an assertion. \
                       \It is applied before ToSA process."
)

structure Assertion_SS_Source = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = \<^binding>\<open>assertion_simps_source\<close>
  val comment = "Simp rules normalizing particularly source part of an assertion."
)

structure Assertion_SS_Target = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = \<^binding>\<open>assertion_simps_target\<close>
  val comment = "Simp rules normalizing particularly target part of an assertion."
)

structure Assertion_SS_Abnormal = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = \<^binding>\<open>assertion_simps_abnormal\<close>
  val comment = "Simp rules normalizing particularly the abnormal spec of a triple."
)
\<close>

\<phi>reasoner_ML assertion_simp_source 1300
  (\<open>Simplify (assertion_simps SOURCE) ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_by_ss' NONE (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Source.get' ctxt))\<close>

\<phi>reasoner_ML assertion_simp_target 1300
  (\<open>Simplify (assertion_simps TARGET) ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_by_ss' NONE (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Target.get' ctxt))\<close>

\<phi>reasoner_ML assertion_simp_abnormal 1300
  (\<open>Simplify (assertion_simps ABNORMAL) ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_by_ss' NONE (fn ctxt =>
      Raw_Simplifier.merge_ss (Assertion_SS.get' ctxt, Assertion_SS_Abnormal.get' ctxt))\<close>

\<phi>reasoner_ML assertion_simp 1200
  (\<open>Premise (assertion_simps _) _\<close> | \<open>Simplify (assertion_simps ?ANY) ?X' ?X\<close>
     )
  = \<open>PLPR_Simplifier.simplifier_by_ss' NONE Assertion_SS.get'\<close>

lemmas [assertion_simps] =
  mult_zero_right[where 'a=\<open>'a::sep_magma set\<close>] mult_zero_left[where 'a=\<open>'a::sep_magma set\<close>]
  mult_1_right[where 'a=\<open>'a::sep_magma_1 set\<close>]
  mult_1_left[where 'a=\<open>'a::sep_magma_1 set\<close>]
  add_0_right[where 'a=\<open>'a::sep_magma set\<close>] add_0_left[where 'a=\<open>'a::sep_magma set\<close>]
  zero_fun[where 'a=\<open>'a::sep_magma set\<close>] zero_fun_def[symmetric, where 'b=\<open>'a::sep_magma set\<close>]
  plus_fun[where 'a=\<open>'a::sep_magma set\<close>]
  Subjection_Zero ExSet_simps distrib_right[where 'a=\<open>'a::sep_semigroup set\<close>]
  mult.assoc[symmetric, where 'a=\<open>'a::sep_semigroup set\<close>]
  \<phi>V_simps

lemmas [assertion_simps_source] = ExSet_times_left ExSet_times_right

section \<open>Small Reasoning Process\<close>

subsubsection \<open>Semantic Expansion of \<phi>-Types\<close>

consts MODE_\<phi>EXPN :: mode \<comment> \<open>relating to named_theorems \<open>\<phi>expn\<close>\<close>

abbreviation \<phi>expn_Premise ("<\<phi>expn> _" [26] 26) where \<open>\<phi>expn_Premise \<equiv> Premise MODE_\<phi>EXPN\<close>

\<phi>reasoner \<phi>expn_Premise 10 (\<open><\<phi>expn> ?P\<close>)
  = (rule Premise_I; simp add: \<phi>expns)

text \<open>Antecedent \<^prop>\<open><\<phi>expn> P\<close> indicates the reasoner solving the premise \<^prop>\<open>P\<close> using
  simplification rules of \<open>\<phi>expns\<close>.\<close>

subsubsection \<open>Name tag by type\<close>

(*TODO: elaborate this*)

datatype ('x, 'name) named (infix "<named>" 30) = tag 'x

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

lemma named_ExSet: "(ExSet T) = (\<exists>*c. T (tag c) )" by (auto simp add: named_exists \<phi>expns)


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

simproc_setup named_exSet_expansion ("ExSet (P :: 'a <named> 'names \<Rightarrow> 'b set)") =
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
\<open>fn (ctxt, sequent) =>
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

\<phi>reasoner_ML lambda_abstraction 1100 ("lambda_abstraction ?x ?Y ?Y'") = \<open>fn (ctxt, sequent) =>
  let
    val (Vs, _, \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>lambda_abstraction\<close>, _) $ x $ Y $ _))
      = Phi_Help.leading_antecedent (Thm.prop_of sequent)
    val Y' = Abs("", fastype_of x, abstract_over (x, Y))
    val idx = Thm.maxidx_of sequent
    val vars = map Var (List.tabulate (length Vs, (fn i => ("v", i+idx))) ~~ map snd Vs)
    fun subst X = Term.subst_bounds (vars, X)
    val rule = Drule.infer_instantiate ctxt
                  (map (apsnd (Thm.cterm_of ctxt)) [(("x",0), subst x), (("Y'",0),subst Y')])
                  @{thm lambda_abstraction}
  in
    Seq.single (ctxt, rule RS sequent)
  end
\<close>

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
  = \<open>PLPR_Simplifier.simplifier_only NONE (fn ctxt =>
          Named_Theorems.get ctxt \<^named_theorems>\<open>frame_var_rewrs\<close>)\<close>

definition \<phi>IntroFrameVar :: "'a::sep_magma_1 set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
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
  "\<phi>IntroFrameVar 1 S S T T"
  unfolding \<phi>IntroFrameVar_def by simp

lemma \<phi>IntroFrameVar'_No:
  "\<phi>IntroFrameVar' 1 S S T T E E"
  unfolding \<phi>IntroFrameVar'_def by simp

lemma \<phi>IntroFrameVar_Yes:
  "\<phi>IntroFrameVar R (R * \<blangle> S \<brangle>) S (R * T) T"
  unfolding \<phi>IntroFrameVar_def FOCUS_TAG_def by blast

lemma \<phi>IntroFrameVar'_Yes:
  " \<phi>IntroFrameVar' R (R * \<blangle> S \<brangle>) S (\<lambda>ret. R * T ret) T (\<lambda>ex. R * E ex) E"
  unfolding \<phi>IntroFrameVar'_def FOCUS_TAG_def by blast


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


subsection \<open>Embedded Reasoning\<close>

definition Embedded_Reasoning :: \<open>bool \<Rightarrow> bool\<close> where \<open>Embedded_Reasoning X \<longleftrightarrow> X\<close>

text \<open>Annotate a boolean assertion in a proof obligation is actually an embedded reasoning
antecedent.\<close>

subsubsection \<open>Implementation\<close>

definition Pass_Embedded_Reasoning :: \<open>bool \<Rightarrow> bool\<close>
  where \<open>Pass_Embedded_Reasoning X \<longleftrightarrow> X\<close>

definition Pass_Embedded_Reasoning' :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Pass_Embedded_Reasoning' IN OUT \<longleftrightarrow> (OUT \<longleftrightarrow> IN)\<close>

declare [[\<phi>reason_default_pattern
      \<open>Pass_Embedded_Reasoning' ?X _\<close> \<Rightarrow> \<open>Pass_Embedded_Reasoning' ?X _\<close> (100)
]]

lemma [\<phi>reason 1000]:
  \<open> Pass_Embedded_Reasoning' X Y
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Y
\<Longrightarrow> Pass_Embedded_Reasoning X\<close>
  unfolding Pass_Embedded_Reasoning_def Pass_Embedded_Reasoning'_def Premise_def
  by blast

lemma [\<phi>reason 1110]:
  \<open> R
\<Longrightarrow> Pass_Embedded_Reasoning' X Y
\<Longrightarrow> Pass_Embedded_Reasoning' (Embedded_Reasoning R \<and> X) Y\<close>
  unfolding Pass_Embedded_Reasoning'_def Embedded_Reasoning_def by blast

lemma [\<phi>reason 1100]:
  \<open> Pass_Embedded_Reasoning' X Y
\<Longrightarrow> Pass_Embedded_Reasoning' (P \<and> X) (P \<and> Y)\<close>
  unfolding Pass_Embedded_Reasoning'_def by blast

lemma [\<phi>reason 1010]:
  \<open> R
\<Longrightarrow> Pass_Embedded_Reasoning' (Embedded_Reasoning R) True \<close>
  unfolding Pass_Embedded_Reasoning'_def Embedded_Reasoning_def by blast

lemma [\<phi>reason 1000]:
  \<open> Pass_Embedded_Reasoning' P P \<close>
  unfolding Pass_Embedded_Reasoning'_def by blast


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
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def by clarsimp




section \<open>Declaration of Large Processes\<close>

subsection \<open>Transformation of State Abstraction (ToSA)\<close>

text \<open>
  Supporting implication \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y @action ToSA\<close> only,
  ToSA is a reasoning process of Transformation of Abstraction (ToA) for
  assertions of (fictional) computation state.
\<close>

consts ToSA' :: \<open>bool \<comment> \<open>whether to reason deeper transformation for each desired \<phi>-type
                          by invoking more time-consuming reasoning process,
                          or just apply unification to match the desired.\<close>
              \<Rightarrow> mode\<close>

text \<open>The boolean flag indicates whether to reason the transformation of \<phi>-types in depth.
For \<open>X\<^sub>1 * \<cdots> * X\<^sub>n \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y\<^sub>1 * \<cdots> * Y\<^sub>m @action ToSA' ?flag\<close>,

\<^item> If the flag is turned on, for every desired \<phi>-Type \<^term>\<open>Y\<^sub>i\<close>, the reasoner
  infers in depth whether some source \<phi>-Type \<^term>\<open>X\<^sub>j\<close> can be transformed into \<^term>\<open>Y\<^sub>i\<close>,
  by invoking any configured reasoning rules bound on the type of \<^term>\<open>Y\<^sub>i\<close>.

\<^item> If the flag is turned off, such in-depth inference is not applied, so the
  reasoning succeeds only if for every desired \<phi>-Type \<^term>\<open>Y\<^sub>i\<close> there is another
  \<^term>\<open>X\<^sub>j\<close> that unifies \<^term>\<open>Y\<^sub>i\<close>.

The the flag is turned off, obviously the performance can be improved a lot though
the reasoning is weaker.
\<close>

abbreviation \<open>ToSA \<equiv> ToSA' True\<close>

lemma [\<phi>reason 3000 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X' \<a>\<n>\<d> ?P @action ToSA' ?mode\<close>]:
  \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action ToSA' mode\<close>
  unfolding Action_Tag_def using implies_refl .



subsection \<open>Removing Values\<close>

definition \<open>Remove_Values (Input::assn) (Output::assn) \<longleftrightarrow> (Input \<i>\<m>\<p>\<l>\<i>\<e>\<s> Output)\<close>

text \<open>The process \<^prop>\<open>Remove_Values Input Output\<close> removes value assertions \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<close>
  from the assertion \<open>Input\<close>. Bounded values such the return value of a procedure are not removed.\<close>


subsection \<open>Collects all Values in an Assertion / from the State Sequent\<close>

consts collect_clean_value :: \<open>bool \<Rightarrow> action\<close>

lemma apply_collect_clean_value:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> V @action collect_clean_value WHETHER_CLEAN
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> V\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1200 for \<open>?S \<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?S' \<a>\<n>\<d> ?V @action collect_clean_value True\<close>]:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> V @action collect_clean_value True
\<Longrightarrow> S \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> V @action collect_clean_value True\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?S \<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?S' \<a>\<n>\<d> ?V @action collect_clean_value False\<close>]:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> V @action collect_clean_value False
\<Longrightarrow> S \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<a>\<n>\<d> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> V
    @action collect_clean_value False\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100 for \<open>?S\<heavy_comma> ?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?S' \<a>\<n>\<d> ?V @action collect_clean_value ?CLEAN\<close>]:
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> V @action collect_clean_value CLEAN
\<Longrightarrow> S\<heavy_comma> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> S'\<heavy_comma> X \<a>\<n>\<d> V @action collect_clean_value CLEAN\<close>
  unfolding Action_Tag_def using implies_right_prod .

lemma [\<phi>reason 1050 for \<open>?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?S' \<a>\<n>\<d> ?V @action collect_clean_value True\<close>]:
  \<open> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> Void \<a>\<n>\<d> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> True
    @action collect_clean_value True\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1050 for \<open>?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?S' \<a>\<n>\<d> ?V @action collect_clean_value False\<close>]:
  \<open> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<a>\<n>\<d> \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> True
    @action collect_clean_value False\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1000 for \<open>?S \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?S' \<a>\<n>\<d> ?V @action collect_clean_value ?clean\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> True @action collect_clean_value clean\<close>
  unfolding Action_Tag_def using implies_refl .

end
