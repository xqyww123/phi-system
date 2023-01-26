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

subsection \<open>Small Annotations\<close>

subsubsection \<open>Matches\<close>

definition Assertion_Matches :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixl "<matches>" 18)
  where \<open>(S <matches> pattern) = S\<close>

text \<open>The annotation marking on a target \<^term>\<open>Y <matches> A\<close> in a ToA or a view shift
  restricts that the source have to first match pattern \<open>A\<close>.\<close>

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (Y <matches> A) \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Assertion_Matches_def .

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s (Y <matches> A) \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Assertion_Matches_def .



section \<open>Normalization of Assertions\<close>

consts assertion_simps :: \<open>mode \<Rightarrow> mode\<close>

named_theorems assertion_simps \<open>Simplification rules normalizing an assertion.
                                It is applied before ToSA process.\<close>
  and assertion_simps_source \<open>Simp rules normalizing particularly source part of an assertion.\<close>
  and assertion_simps_target \<open>Simp rules normalizing particularly target part of an assertion.\<close>

\<phi>reasoner_ML assertion_simp_source 1300
  (\<open>Simplify (assertion_simps SOURCE) ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_only (fn ctxt =>
        Named_Theorems.get ctxt \<^named_theorems>\<open>assertion_simps\<close>
      @ Named_Theorems.get ctxt \<^named_theorems>\<open>assertion_simps_source\<close>)\<close>

\<phi>reasoner_ML assertion_simp_target 1300
  (\<open>Simplify (assertion_simps TARGET) ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_only (fn ctxt =>
        Named_Theorems.get ctxt \<^named_theorems>\<open>assertion_simps\<close>
      @ Named_Theorems.get ctxt \<^named_theorems>\<open>assertion_simps_target\<close>)\<close>

\<phi>reasoner_ML assertion_simp 1300
  (\<open>Simplify (assertion_simps ?ANY) ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_only (fn ctxt => Named_Theorems.get ctxt \<^named_theorems>\<open>assertion_simps\<close>)\<close>

lemmas [assertion_simps] =
  mult_zero_right[where 'a=assn] mult_zero_left[where 'a=assn] mult_1_right[where 'a=assn]
  mult_1_left[where 'a=assn] add_0_right[where 'a=assn] add_0_left[where 'a=assn]
  zero_fun[where 'a=assn] zero_fun_def[symmetric, where 'b=assn] plus_fun[where 'a=assn]
  Subjection_Zero ExSet_simps FOCUS_TAG_def[where 'a=assn] ExSet_0
  distrib_right[where 'a=assn]

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

ML_file "./library/tools/quant_expansion.ML"

simproc_setup named_forall_expansion ("All (P :: 'a <named> 'names \<Rightarrow> bool)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.forall_expansion)\<close>

simproc_setup named_exSet_expansion ("ExSet (P :: 'a <named> 'names \<Rightarrow> 'b set)") =
  \<open>K (fn ctx => fn cterms => QuantExpansion.simproc_of QuantExpansion.ExNu_expansion ctx cterms)\<close>

simproc_setup named_pureAll_expansion ("Pure.all (P :: 'a <named> 'names \<Rightarrow> prop)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.pure_All_expansion)\<close>


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

ML \<open>Name.variant "" Name.context\<close>

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



section \<open>Declaration of Large Processes\<close>

subsection \<open>Transformation of State Abstraction (ToSA)\<close>

text \<open>
  Supporting either view shift \<open>X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y @action ToSA\<close> or
  implication \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y @action ToSA\<close>,
  ToSA is a reasoning process of Transformation of Abstraction (ToA) for
  assertions of (fictional) computation state.
\<close>

consts ToSA' :: \<open>bool \<comment> \<open>whether to reason deeper transformation for each desired \<phi>-type
                          by invoking more time-consuming reasoning process,
                          or just apply unification to match the desired.\<close>
              \<Rightarrow> mode\<close>

text \<open>The boolean flag indicates whether to reason the transformation of \<phi>-types in depth.
For \<open>X\<^sub>1 * \<cdots> * X\<^sub>n \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<^sub>1 * \<cdots> * Y\<^sub>m @action ToSA' ?flag\<close>,

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

lemma [\<phi>reason 3000 for \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?X' \<^bold>a\<^bold>n\<^bold>d ?P @action ToSA' ?mode\<close>]:
  \<open>X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s X @action ToSA' mode\<close>
  unfolding Action_Tag_def using \<phi>view_refl .

subsection \<open>Removing Values\<close>

definition \<open>Remove_Values (Input::assn) (Output::assn) \<longleftrightarrow> (Input \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Output)\<close>

text \<open>The process \<^prop>\<open>Remove_Values Input Output\<close> removes value assertions \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close>
  from the assertion \<open>Input\<close>. Bounded values such the return value of a procedure are not removed.\<close>


subsection \<open>Collects all Values in an Assertion / from the State Sequent\<close>

consts collect_clean_value :: \<open>bool \<Rightarrow> unit action\<close>

lemma apply_collect_clean_value:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d V @action collect_clean_value WHETHER_CLEAN
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d V\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1200 for \<open>?S \<heavy_comma> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?S' \<^bold>a\<^bold>n\<^bold>d ?V @action collect_clean_value True\<close>]:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d V @action collect_clean_value True
\<Longrightarrow> S \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> V @action collect_clean_value True\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?S \<heavy_comma> ?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?S' \<^bold>a\<^bold>n\<^bold>d ?V @action collect_clean_value False\<close>]:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d V @action collect_clean_value False
\<Longrightarrow> S \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<^bold>a\<^bold>n\<^bold>d \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> V
    @action collect_clean_value False\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1100 for \<open>?S\<heavy_comma> ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?S' \<^bold>a\<^bold>n\<^bold>d ?V @action collect_clean_value ?CLEAN\<close>]:
  \<open> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d V @action collect_clean_value CLEAN
\<Longrightarrow> S\<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S'\<heavy_comma> X \<^bold>a\<^bold>n\<^bold>d V @action collect_clean_value CLEAN\<close>
  unfolding Action_Tag_def using implies_right_prod .

lemma [\<phi>reason 1050 for \<open>?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?S' \<^bold>a\<^bold>n\<^bold>d ?V @action collect_clean_value True\<close>]:
  \<open> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Void \<^bold>a\<^bold>n\<^bold>d \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> True
    @action collect_clean_value True\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1050 for \<open>?x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[?v] ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?S' \<^bold>a\<^bold>n\<^bold>d ?V @action collect_clean_value False\<close>]:
  \<open> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T \<^bold>a\<^bold>n\<^bold>d \<phi>arg.dest v \<in> (x \<Ztypecolon> T) \<and> True
    @action collect_clean_value False\<close>
  unfolding Action_Tag_def Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1000 for \<open>?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?S' \<^bold>a\<^bold>n\<^bold>d ?V @action collect_clean_value ?clean\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d True @action collect_clean_value clean\<close>
  unfolding Action_Tag_def using implies_refl .

end