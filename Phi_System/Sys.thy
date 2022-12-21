theory Sys
  imports
    "Phi_Semantics_Framework.Phi_Semantics_Framework"
    "Phi_Logic_Programming_Reasoner.Phi_Logic_Programming_Reasoner"
    "HOL-Library.Adhoc_Overloading"
    Spec_Framework
    "Phi_Algebras.Map_of_Tree"
    Calculus_of_Programming
  keywords
    "proc" "rec_proc" (*"\<phi>cast"*) :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "\<Longleftarrow>" "\<Longleftarrow>'" "$" "subj"
    "var" "invar" "\<Longrightarrow>" "goal" "\<exists>" "throws"
    "argument" "return" "affirm" :: quasi_command
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


section \<open>Basic Constructions of the Deductive Programming\<close>

subsection \<open>Preliminary\<close>

named_theorems \<phi>lemmata \<open>Contextual facts during the programming. They are automatically
       aggregated from every attached \<^prop>\<open>P\<close> in \<^prop>\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk in [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Sth \<^bold>s\<^bold>u\<^bold>b\<^bold>j P\<close>
       during the programming. Do not modify it manually because it is managed automatically and
       cleared frequently\<close>

context \<phi>spec begin

lemma [\<phi>programming_simps]:
  \<open>(A\<heavy_comma> (B\<heavy_comma> C)) = (A\<heavy_comma> B\<heavy_comma> C)\<close>
  unfolding mult.assoc ..

end



subsubsection \<open>Forward Declaration of Reasoning Tags\<close>


definition \<open>Filter_Out_Free_Values (T::'a set) (T'::'a set) \<equiv> Trueprop (T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T')\<close>

definition Argument :: "'a \<Rightarrow> 'a" ("\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _" [11] 10) where "Argument x = x"


consts assertion_simplification :: mode
named_theorems assertion_simps




section \<open>More Features of the Deductive Programming\<close>

subsection \<open>Antecedents of Reasoning - Part I\<close>


subsubsection \<open>Mode\<close>

consts MODE_\<phi>EXPN :: mode \<comment> \<open>relating to named_theorems \<open>\<phi>expn\<close>\<close>

abbreviation \<phi>expn_Premise ("<\<phi>expn> _" [26] 26) where \<open>\<phi>expn_Premise \<equiv> Premise MODE_\<phi>EXPN\<close>


subsubsection \<open>Label tag\<close> (*depreciated*)

datatype label = LABEL_TAG "unit \<Rightarrow> unit"

lemma [cong]: "LABEL_TAG x \<equiv> LABEL_TAG x"  using reflexive .
lemma label_eq: "x = y" for x :: label by (cases x, cases y) auto

syntax "_LABEL_" :: "idt \<Rightarrow> label" ("LABEL _" [0] 1000)
translations "LABEL name" == "CONST LABEL_TAG (\<lambda>name. ())"



subsubsection \<open>Parameter Input\<close>

definition ParamTag :: " 'a \<Rightarrow> bool" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 26) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> True"

text (in \<phi>empty)
 \<open>The \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> represents \<^term>\<open>x\<close> is a parameter that should be given by user, e.g.,
  \<^prop>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_size \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int value bit_size \<lbrace> A \<longmapsto> B \<rbrace>\<close>.
  The \<phi>-processor `set_param` processes the \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> antecedent.\<close>

lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
lemma [elim!,\<phi>reason_elim!]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto
lemma [cong]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<longleftrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" ..



subsubsection \<open>Label Input\<close> (*depreciated*)

definition LabelTag :: " label \<Rightarrow> bool" ("\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l _" [1000] 26) where "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<equiv> True"

text \<open>The \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> indicate \<^term>\<open>x\<close> is a \<^typ>\<open>label\<close> that should be set by user, e.g.,
  \<^prop>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l name \<Longrightarrow> do_something_relating name\<close>.
  The \<phi>-processor `set_label` processes the \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> antecedent.\<close>

lemma LabelTag: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x" unfolding LabelTag_def ..
lemma [elim!,\<phi>reason_elim!]: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<Longrightarrow> C \<Longrightarrow> C" by auto



subsubsection \<open>Explicit name tag\<close> (*depreciated*)

definition Labelled :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "Labelled name x = x" \<comment>\<open>name tag\<close>

(* consts "named_sugar" :: " 'i_am \<Rightarrow> 'merely \<Rightarrow> 'a_sugar " ("\<ltbrak>_\<rtbrak>. _" [10,15] 14)
translations
  "\<ltbrak>name\<rtbrak>. x \<Ztypecolon> T" == "x \<Ztypecolon> (\<ltbrak>name\<rtbrak>. T)"
  "\<ltbrak>name\<rtbrak>. x" == "CONST Labelled (LABEL name) x" *)

lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..
lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..



subsubsection \<open>Hidden name hint\<close> (*depreciated*)

definition NameHint :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "NameHint name x = x" \<comment>\<open>name tag\<close>
translations "X" <= "CONST NameHint name X"


subsubsection \<open>Argument tag\<close>

lemma Argument_I: "P \<Longrightarrow> Argument P" unfolding Argument_def .

text \<open>Sequent in pattern \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P \<Longrightarrow> PROP Q\<close> hints users to input a theorem \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> P\<close>
  in order to deduce the sequent into \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> PROP Q\<close>, which is processed by the `rule` processor.
  Argument servers as a protector to prevent the unexpected auto-reasoning, e.g., the case for cast where
  the reasoner always attempts to solve an unprotected case premises and `Argument` tagging the Subty premise
  in this case prevent this automatic behavior when expecting user to input the cast rule.\<close>

lemma Argument_strip_top:
  \<open>Trueprop (\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P) \<equiv> Trueprop P\<close>
  unfolding Argument_def .


subsubsection \<open>Structural Morphism\<close>

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


subsubsection \<open>Technical Tags\<close> (*depreciated*)

datatype uniq_id = UNIQ_ID
  \<comment> \<open>A technical tag that is during the exporting translated to a unique ID.
    It is useful to generate unique name of anonymous functions.\<close>




subsubsection \<open>Name tag by type\<close>

datatype ('x, 'name) named (infix "<named>" 30) = tag 'x

syntax "__named__" :: \<open>logic \<Rightarrow> tuple_args \<Rightarrow> logic\<close> (infix "<<named>>" 25)


ML_file \<open>library/name_by_type.ML\<close>

text (in \<phi>empty) \<open>It is a tool to annotate names on a term, e.g. \<^term>\<open>x <<named>> a, b\<close>.
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

  This feature is mostly used in Variable Extraction (see ???).\<close>


lemma named_forall: "All P \<longleftrightarrow> (\<forall>x. P (tag x))" by (metis named.exhaust)
lemma named_exists: "Ex P \<longleftrightarrow> (\<exists>x. P (tag x))" by (metis named.exhaust)
lemma [simp]: "tag (case x of tag x \<Rightarrow> x) = x" by (cases x) simp
lemma named_All: "(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (tag x))"
proof fix x assume "(\<And>x. PROP P x)" then show "PROP P (tag x)" .
next fix x :: "'a <named> 'b" assume "(\<And>x. PROP P (tag x))" from \<open>PROP P (tag (case x of tag x \<Rightarrow> x))\<close> show "PROP P x" by simp
qed

lemma named_ExSet: "(ExSet T) = (\<exists>*c. T (tag c) )" by (auto simp add: named_exists \<phi>expns)

subsubsection \<open>Rename \<lambda>-Abstraction\<close>

definition rename_abstraction :: \<open>'\<phi>name_name itself \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>rename_abstraction name origin_abs named_abs \<longleftrightarrow> (origin_abs = named_abs)\<close>

lemma rename_abstraction:
  \<open>rename_abstraction name X X\<close>
  unfolding rename_abstraction_def ..

\<phi>reasoner_ML rename_abstraction 1100 (conclusion "rename_abstraction TYPE(?'name) ?Y ?Y'") =
\<open>fn (ctxt, sequent) =>
  case Thm.major_prem_of sequent
    of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>rename_abstraction\<close>, _)
                $ (Const (\<^const_name>\<open>Pure.type\<close>, Type(\<^type_name>\<open>itself\<close>, [name'])))
                $ Abs(_,ty,body)
                $ Var Y'') =>
      let
        val name = case PhiSyntax.dest_name_tylabels name'
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

\<phi>reasoner_ML lambda_abstraction 1100 (conclusion "lambda_abstraction ?x ?Y ?Y'") = \<open>fn (ctxt, sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>lambda_abstraction\<close>, _) $ x $ Y $ _)
      = Thm.major_prem_of sequent
    val Y' = Abs("", fastype_of x, abstract_over (x, Y))
    val rule = Drule.infer_instantiate ctxt
          (map (apsnd (Thm.cterm_of ctxt)) [(("x",0),x), (("Y'",0),Y')]) @{thm lambda_abstraction}
  in
    Seq.single (ctxt, rule RS sequent)
  end
\<close>

lemma [\<phi>reason 1200 for \<open>lambda_abstraction (tag ?x) ?fx ?f\<close>]:
  \<open> lambda_abstraction x fx f
\<Longrightarrow> rename_abstraction TYPE('name) f f'
\<Longrightarrow> lambda_abstraction (tag x :: 'any <named> 'name) fx (case_named f')\<close>
  unfolding lambda_abstraction_def rename_abstraction_def by simp


subsubsection \<open>Extract Proof Obligation\<close>

\<phi>reasoner \<phi>expn_Premise 10 (conclusion \<open><\<phi>expn> ?P\<close>)
  = (rule Premise_I; simp add: \<phi>expns)


subsection \<open>General\<close>

subsubsection \<open>Syntax\<close>

ML_file \<open>library/PhiSyntax.ML\<close>
ML_file \<open>library/Phi_Working_Mode.ML\<close>
ML_file \<open>library/NuBasics.ML\<close>

consts val_of :: " 'a \<Rightarrow> 'b "
consts key_of :: " 'a \<Rightarrow> 'b "

datatype ('a, 'b) object (infixr "\<Zinj>" 60) = object (key_of_obj: 'a) (val_of_obj: 'b) (infixr "\<Zinj>" 60)
adhoc_overloading key_of key_of_obj and val_of val_of_obj
declare object.split[split]


lemma object_forall: "All P \<longleftrightarrow> (\<forall>a x. P (a \<Zinj> x))" by (metis object.exhaust)
lemma object_exists: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<Zinj> x))" by (metis object.exhaust)
lemma object_All: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a \<Zinj> b))" 
proof fix a b assume "(\<And>x. PROP P x) " then show "PROP P (a \<Zinj> b)" .
next fix x assume "\<And>a b. PROP P (a \<Zinj> b)"
    from \<open>PROP P (key_of x \<Zinj> val_of x)\<close> show "PROP P x" by simp
  qed



subsubsection \<open>Reasoning Rules \& Settings\<close>

declare set_mult_inhabited[\<phi>reason_elim!] Premise_def[\<phi>expns]

lemma (in \<phi>empty_sem) [\<phi>reason]:
  \<open> (\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY)
\<Longrightarrow> \<phi>\<phi>SemType T TY\<close>
  ..

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited 1 \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsubsection \<open>Finalization Rewrites\<close>

consts procedure_simplification :: mode
named_theorems procedure_simps

declare proc_bind_SKIP[procedure_simps]
  proc_bind_SKIP'[procedure_simps]
  proc_bind_assoc[procedure_simps]
  proc_bind_return_none[procedure_simps]

\<phi>reasoner procedure_equivalent 1200 (conclusion \<open>Premise procedure_simplification ?P\<close>)
  = (rule Premise_I; simp only: procedure_simps; fail)

\<phi>reasoner procedure_simplification 1200
    (conclusion \<open>?Q = ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> procedure_simplification\<close>)
  = ((simp only: procedure_simps)?, rule Conv_Action_Tag_I; fail)

context \<phi>spec begin

lemma "\<phi>__final_proc_rewrite__":
  \<open> f = f' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> procedure_simplification
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f  \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>\<close>
  unfolding Action_Tag_def by simp

lemma "\<phi>__final_proc_rewrite__'":
  \<open> f = f' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> procedure_simplification
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f  \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Action_Tag_def by simp

end

subsection \<open>Ad-hoc Overload\<close>

ML_file \<open>library/applicant.ML\<close>

attribute_setup \<phi>overload = \<open>Scan.lift (Parse.and_list1 NuApplicant.name_position) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuApplicant.overload th) bindings))\<close>

\<phi>overloads D \<open>Destructive subtyping rules\<close>
\<phi>overloads cast \<open>Invoke subtyping on the internal content\<close>


subsection \<open>Cast \& View Shift\<close>

lemma implies_refl_ty[\<phi>reason 30 for \<open>?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?T \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> T" unfolding Imply_def by fast

lemma cast_whole_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Argument_def .

context \<phi>spec begin

lemma View_Shift_by_Subtyp[intro?]:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Imply_def View_Shift_def INTERP_SPEC_def
  by (clarsimp, metis set_mult_expn)

lemma view_shift_0[\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> X\<close>
  by (blast intro: View_Shift_by_Subtyp zero_implies_any)
  
lemma view_shift_id[\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<longmapsto> ?B \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> A"
  by (blast intro: View_Shift_by_Subtyp implies_refl)

lemma view_shift_id_ty[\<phi>reason 30 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?x \<Ztypecolon> ?T \<longmapsto> ?y \<Ztypecolon> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> T \<longmapsto> y \<Ztypecolon> T"
  by (blast intro: View_Shift_by_Subtyp implies_refl_ty)

lemma view_shift_union[\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X + Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> X + Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  by (simp add: View_Shift_def distrib_left)+

(* abbreviation SimpleSubty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2_ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _)" [2,14] 13)
  where "(A \<longmapsto> B) \<equiv> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d True)" *)
(* lemma SubtyE[elim]: "A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Imply_def Inhabited_def by (auto intro: Inhabited_subset)
lemma SubtyI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P" unfolding Imply_def Inhabited_def by auto *)

lemma is_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> x' \<Ztypecolon> N" using view_shift_id by force
lemma as_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> X' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> X'"  by blast 

lemma \<phi>view_shift_trans:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> (P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q)
    \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding View_Shift_def by blast


lemma \<phi>view_shift_intro_frame:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R * U' \<longmapsto> R * U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  by (simp add: \<phi>frame_view)

lemma \<phi>view_shift_intro_frame_R:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w U' * R \<longmapsto> U * R \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  by (simp add: \<phi>frame_view mult.commute)

lemma (in \<phi>spec) "\<phi>view_shift":
  " CurrentConstruction mode blk H T
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> CurrentConstruction mode blk H T'"
  unfolding CurrentConstruction_def View_Shift_def
  by blast

lemma (in \<phi>spec) "\<phi>view_shift_P":
  " CurrentConstruction mode blk H T
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> (CurrentConstruction mode blk H T') \<and> P"
  unfolding CurrentConstruction_def View_Shift_def
  by blast

lemma view_shift_whole_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Argument_def .


lemma \<phi>CONSEQ'E:
   "(\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v \<^bold>w\<^bold>i\<^bold>t\<^bold>h P3)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A  \<longmapsto> B  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>"
  using \<phi>CONSEQ view_shift_id by blast

end


subsection \<open>Antecedents of Reasoning - Part II\<close>

subsubsection \<open>Introduce Frame Variable\<close>

named_theorems frame_var_rewrs \<open>Rewriting rules to normalize after inserting the frame variable\<close>

declare mult.assoc[symmetric, frame_var_rewrs]
  Subjection_times[frame_var_rewrs]
  ExSet_times[frame_var_rewrs]

consts frame_var_rewrs :: mode

\<phi>reasoner Subty_Simplify 2000 (conclusion \<open>Simplify frame_var_rewrs ?x ?y\<close>)
  = ((simp only: frame_var_rewrs)?, rule Simplify_I)


context \<phi>spec begin

definition \<phi>IntroFrameVar ::
  "('FIC_N,'FIC) assn
\<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn
\<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn
\<Rightarrow> bool"
  where "\<phi>IntroFrameVar R S' S T' T \<longleftrightarrow> S' = (R * S) \<and> T' = R * T "

definition \<phi>IntroFrameVar' ::
  "('FIC_N,'FIC) assn
\<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('FIC_N,'FIC) assn
\<Rightarrow> ('ret \<Rightarrow> ('FIC_N,'FIC) assn) \<Rightarrow> ('ret \<Rightarrow> ('FIC_N,'FIC) assn)
\<Rightarrow> ('ex \<Rightarrow> ('FIC_N,'FIC) assn) \<Rightarrow> ('ex \<Rightarrow> ('FIC_N,'FIC) assn)
\<Rightarrow> bool"
  where "\<phi>IntroFrameVar' R S' S T' T E' E \<longleftrightarrow> S' = (R * S) \<and> T' = (\<lambda>ret. R * T ret) \<and> E' = (\<lambda>ex. R * E ex) "


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


\<phi>reasoner_ML \<phi>IntroFrameVar 1000 (conclusion "\<phi>IntroFrameVar ?R ?S' ?S ?T' ?T") =
\<open>fn (ctxt, sequent) =>
  let
    val (Const (\<^const_name>\<open>\<phi>spec.\<phi>IntroFrameVar\<close>, _) $ _ $ _ $ S $ _ $ _) =
        Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val tail = PhiSyntax.strip_separations S |> NuHelp.last
  in
    if is_Var tail andalso fastype_of tail = PhiSyntax.get_assn_typ ctxt
    then Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar_No"  RS sequent)
    else Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar_Yes" RS sequent)
  end\<close>

\<phi>reasoner_ML \<phi>IntroFrameVar' 1000 (conclusion "\<phi>IntroFrameVar' ?R ?S' ?S ?T' ?T ?E' ?E") =
\<open>fn (ctxt, sequent) =>
  let
    val (Const (\<^const_name>\<open>\<phi>spec.\<phi>IntroFrameVar'\<close>, _) $ _ $ _ $ S $ _ $ _ $ _ $ _) =
        Thm.major_prem_of sequent |> HOLogic.dest_Trueprop
    val tail = PhiSyntax.strip_separations S |> NuHelp.last
  in
    if is_Var tail andalso fastype_of tail = PhiSyntax.get_assn_typ ctxt
    then Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar'_No" RS sequent)
    else Seq.single (ctxt, Proof_Context.get_thm ctxt "local.\<phi>IntroFrameVar'_Yes" RS sequent)
  end\<close>


end


subsubsection \<open>Fix\<close>

definition Fix :: \<open>'a set \<Rightarrow> 'a set\<close> ("FIX _" [16] 15) where [iff]: \<open>Fix S = S\<close>

text \<open>During the subtyping reasoning, \<^term>\<open>FIX S\<close> annotates the reasoner
  do not attempt to permute objects to solve the subtyping. It means the order is sensitive
  and fixed. For example, a cast may apply only on the first object,
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



subsubsection \<open>Matches\<close>

text \<open>The tag restricts in sub-type reasoning the original type must match certain pattern.\<close>

definition TyMatches :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixl "<matches>" 18)
  where \<open>(S <matches> pattern) = S\<close>

lemma [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (Y <matches> A) \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding TyMatches_def .

lemma (in \<phi>spec) [\<phi>reason 2000]:
  \<open>Matches X A \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> (Y <matches> A) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding TyMatches_def .


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

ML_file "./library/QuantExpansion.ML"

(*
subsubsection \<open>Constrain at Most One Solution when Reasoning A Proposition\<close>

definition Unique_Solution :: \<open>bool \<Rightarrow> bool\<close>
  where [iff]: \<open>Unique_Solution P \<longleftrightarrow> P\<close>

definition Meet_A_Solution :: bool
  where [iff]: \<open>Meet_A_Solution \<longleftrightarrow> True\<close>

lemma start_unique_solution_reasoning:
  \<open> P
\<Longrightarrow> Meet_A_Solution
\<Longrightarrow> Unique_Solution P\<close>
  unfolding Unique_Solution_def . *)



subsection \<open>Synthesis\<close>

text \<open>The section presents a generic synthesis framework.
  It is called generic because it supports different semantics of synthesis on different kinds of
    sequent. For example, on Programming_CurrentConstruction, the behavior is to reason
    a procedure to generate an output satisfying the desired specification;
    on View_Shift_CurrentConstruction, it is to reason a view shift;
    on a form of \<open>P \<Longrightarrow> Q\<close>, it is to reason a proposition P according to the given term.\<close>

definition DoSynthesis :: \<open>'a \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>DoSynthesis term sequent result \<equiv> (PROP sequent \<Longrightarrow> PROP result)\<close>

definition Synthesis_Parse :: \<open>'a \<Rightarrow> 'b \<Rightarrow> prop\<close>
  where \<open>Synthesis_Parse input parsed \<equiv> Trueprop True\<close>

lemma \<phi>synthesis:
  \<open> PROP sequent
\<Longrightarrow> PROP DoSynthesis X sequent result
\<Longrightarrow> PROP result\<close>
  unfolding DoSynthesis_def .

text \<open>
  Overall, the synthesis procedure consists of 2 phases. The first phase as a pre-processor,
    parses the input from user and then the second phase triggers the reasoning process
    on the parsed input.

  The reason why we parse the input is because, inputting always complete assertions
    can be verbose.
  For example, user may input just an abstract object \<^term>\<open>x\<close> to mean to
    synthesis \<^term>\<open>x \<Ztypecolon> T\<close> for some unspecified \<^term>\<open>T\<close>;
    user may also input \<^term>\<open>0::nat\<close> to mean to synthesis \<^term>\<open>0 \<Ztypecolon> Natural_Number\<close>.

  Antecedent \<^schematic_term>\<open>Synthesis_Parse input ?parsed\<close> provides this function to parse the user
    input \<^term>\<open>input\<close> before the synthesis. Configured by several rules, the reasoner instantiates
    \<^schematic_term>\<open>?parsed\<close> and solves this antecedent.

  By disabling \<phi>_synthesis_parsing to disable this feature.\<close>


subsubsection \<open>Parse the Term to be Synthesised\<close>

context \<phi>spec begin

lemma [\<phi>reason 9999 for
  \<open>PROP Synthesis_Parse (?X'::?'ret \<Rightarrow> ('FIC_N,'FIC)assn) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse X X\<close> for X :: \<open>'ret \<Rightarrow> ('FIC_N,'FIC)assn\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 9999 for
  \<open>PROP Synthesis_Parse (?X'::('FIC_N,'FIC)assn) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse X (\<lambda>_. X)\<close> for X :: \<open>('FIC_N,'FIC)assn\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 30 
    for \<open>PROP Synthesis_Parse ?x (?Y::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
    except \<open>PROP Synthesis_Parse (?x \<Ztypecolon> ?T) ?Y\<close>
           \<open>PROP Synthesis_Parse (?x::('FIC_N,'FIC) assn) ?Y\<close>
           \<open>PROP Synthesis_Parse (?x::?'ret \<Rightarrow> ('FIC_N,'FIC) assn) ?Y\<close>
]:
  \<open>PROP Synthesis_Parse x (\<lambda>ret. (x \<Ztypecolon> X ret :: ('FIC_N,'FIC)assn))\<close>
  unfolding Synthesis_Parse_def ..


lemma [\<phi>reason 10
  for \<open>PROP Synthesis_Parse (numeral ?n::?'bb::numeral) ?X\<close>
      \<open>PROP Synthesis_Parse (0::?'cc::zero) ?X\<close>
      \<open>PROP Synthesis_Parse (1::?'dd::one) ?X\<close>
  except \<open>PROP Synthesis_Parse (?n::nat) ?X\<close>
]:
  \<open> PROP Synthesis_Parse (n :: nat) X
\<Longrightarrow> PROP Synthesis_Parse n X\<close>
 \<comment> \<open>This rule specifies: when input any 0, 1, or \<^schematic_term>\<open>numeral ?sth\<close>, of unspecified type,
      they should be treated as of natural number type.\<close>
  unfolding Synthesis_Parse_def
  ..

end


subsubsection \<open>Tagging the part a construction can synthesis\<close>

definition Synthesis :: \<open>'a set \<Rightarrow> 'a set\<close> ("SYNTHESIS _" [15] 14) where [iff]: \<open>Synthesis S = S\<close>

text (in \<phi>spec) \<open>
  Occurring in a rule, SYNTHESIS tags a part of the post \<phi>-type of a triple or a view shifting,
    representing this part can be synthesised by this construction.
  For example, \<^prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> SYNTHESIS Z \<rbrace>\<close> represents the procedure f generates
    something that meets Z.

  Occurring during reasoning, like \<^schematic_prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> X \<longmapsto> \<lambda>ret. Y\<heavy_comma> SYNTHESIS Z \<rbrace> \<Longrightarrow> C\<close>,
    it represents the reasoner needs to find some construction (here it specifies it must be a
    procedure) ?f that generates something meeting Z.
\<close>

subsubsection \<open>Synthesis Operations\<close>

context \<phi>spec begin

paragraph \<open>Construction on Programming\<close>

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S1)) ?RET\<close>
]:
  " PROP Synthesis_Parse X X'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S1 \<longmapsto> \<lambda>v. S2\<heavy_comma> SYNTHESIS X' v \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S1))
      (Trueprop (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>v. S2\<heavy_comma> X' v) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))"
  unfolding Synthesis_def GOAL_CTXT_def DoSynthesis_def
  using \<phi>apply_proc .

text \<open>On programming mode, the synthesis operation always tries to find a procedure.
  View shifts have to be wrapped in a procedure. The following is an automatic wrapper. \<close>

lemma [\<phi>reason 30
    for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S1 \<longmapsto> \<lambda>v. ?S2\<heavy_comma> SYNTHESIS ?X' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> SYNTHESIS X' \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> S1 \<longmapsto> \<lambda>v. S2\<heavy_comma> SYNTHESIS X' \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding \<phi>Procedure_def Return_def det_lift_def View_Shift_def by simp

paragraph \<open>Construction on View Shifting\<close>

text \<open>On view shifting mode, the synthesis operation tries to find a view shifting.\<close>

lemma [\<phi>reason 1200
    for \<open>PROP DoSynthesis ?X (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?blk [?H] \<^bold>i\<^bold>s ?S1)) ?RET\<close>
]:
  " PROP Synthesis_Parse X X'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> SYNTHESIS X' \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X
      (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w blk [H] \<^bold>i\<^bold>s S1))
      (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w blk [H] \<^bold>i\<^bold>s S2\<heavy_comma> X'))"
  unfolding Synthesis_def GOAL_CTXT_def DoSynthesis_def
  using \<phi>apply_view_shift .

end

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
\<Longrightarrow> PROP Synthesis_by X (PROP P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis X (PROP P \<Longrightarrow> PROP Q) (PROP Q)"
  unfolding DoSynthesis_def Synthesis_by_def GOAL_CTXT_def .

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. PROP Synthesis_by X (PROP P x))
\<Longrightarrow> PROP Synthesis_by X (\<And>x. PROP P x)\<close>
  unfolding Synthesis_by_def .

lemma [\<phi>reason 1200]:
  \<open>(PROP P \<Longrightarrow> PROP Synthesis_by X (PROP Q))
\<Longrightarrow> PROP Synthesis_by X (PROP P \<Longrightarrow> PROP Q)\<close>
  unfolding Synthesis_by_def .

context \<phi>spec begin

lemma [\<phi>reason 1210]:
  \<open> PROP Synthesis_Parse X' X
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> PROP Synthesis_by X' (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def .

lemma [\<phi>reason 1200]:
  \<open> PROP Synthesis_Parse X' X
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS X ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> PROP Synthesis_by X' (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> X ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def Synthesis_def .

lemma [\<phi>reason 1200]:
  \<open> (\<And>x. PROP Synthesis_by X (Trueprop (P x)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G)
\<Longrightarrow> PROP Synthesis_by X (Trueprop (All P)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def GOAL_CTXT_def ..

lemma [\<phi>reason 1200]:
  \<open> (P \<Longrightarrow> PROP Synthesis_by X (Trueprop Q) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G)
\<Longrightarrow> PROP Synthesis_by X (Trueprop (P \<longrightarrow> Q)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Synthesis_by_def GOAL_CTXT_def ..


subsubsection \<open>General Synthesis Rules\<close>

lemma [\<phi>reason 1200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS f x \<Ztypecolon> T ret \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> SYNTHESIS (case_named f (tag x)) \<Ztypecolon> T ret \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P\<close>
  by simp

end

subsection \<open>Application\<close> \<comment> \<open>of procedures, subtypings, and any other things\<close>

definition \<phi>Application :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop\<close>
  where \<open>\<phi>Application Applicants State Result \<equiv> (PROP State \<Longrightarrow> PROP Applicants \<Longrightarrow> PROP Result)\<close>

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


ML_file \<open>library/application.ML\<close>

\<phi>reasoner_ML \<phi>Application 2000 (conclusion \<open>PROP \<phi>Application (PROP ?App) (PROP ?State) (PROP ?Result)\<close>) =
  \<open>NuApply.start_reasoning\<close>

\<phi>reasoner_ML \<phi>Application_Success 2000 (conclusion \<open>PROP \<phi>Application_Success\<close>) =
  \<open>NuApply.success_application\<close>


subsubsection \<open>Rules of Application Methods\<close>

paragraph \<open>Common Rules\<close>

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
\<Longrightarrow> PROP \<phi>Application_Method (App \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) State (PROP Result)\<close>
  unfolding prop_def \<phi>Application_def \<phi>Application_Method_def GOAL_CTXT_def
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


paragraph \<open>Applying on Ongoing Program Construction\<close>

context \<phi>spec begin

subparagraph \<open>Subtyping methods\<close>

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
      (Trueprop ((CurrentConstruction mode blk R T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" .

lemma [\<phi>reason 1500 for \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?R\<heavy_comma> ?S))) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (CurrentConstruction mode blk RR (R\<heavy_comma> S)))
      (Trueprop ((CurrentConstruction mode blk RR (R\<heavy_comma> T)) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" implies_left_prod by blast

lemma \<phi>apply_subtyping_fully[\<phi>reason for \<open>
  PROP \<phi>Application_Method (Trueprop (?S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T' \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (CurrentConstruction mode blk RR S))
      (Trueprop ((CurrentConstruction mode blk RR T) \<and> P))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def
    GOAL_CTXT_def FOCUS_TAG_def Action_Tag_def
  by (meson \<phi>cast_P implies_left_prod \<phi>view_shift_P)
  

subparagraph \<open>View Shift methods\<close>

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
      (Trueprop ((CurrentConstruction mode blk R T) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>view_shift_P" .

lemma [\<phi>reason 1500 for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
          (Trueprop (CurrentConstruction ?mode ?blk ?RR (?R\<heavy_comma> ?S))) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P))
      (Trueprop (CurrentConstruction mode blk RR (R\<heavy_comma> S)))
      (Trueprop ((CurrentConstruction mode blk RR (R\<heavy_comma> T)) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>view_shift_P" \<phi>view_shift_intro_frame by blast

lemma \<phi>apply_view_shift_fully[\<phi>reason for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P))
      (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  "\<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S' \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2))
      (Trueprop (CurrentConstruction mode blk RR S))
      (Trueprop ((CurrentConstruction mode blk RR T) \<and> (P1 \<and> P2)))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def
    GOAL_CTXT_def FOCUS_TAG_def Action_Tag_def
  using "\<phi>view_shift_P" \<phi>view_shift_intro_frame
  by (metis (no_types, lifting))


subparagraph \<open>Procedure methods\<close>

lemma apply_proc_fast[\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S \<longmapsto> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>  \<open>
  PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?var_S \<longmapsto> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result
\<close>
]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
      (Trueprop (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using \<phi>apply_proc .


lemma \<phi>apply_proc_fully[\<phi>reason for
    \<open>PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S' \<longmapsto> ?T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>))
            (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S)) ?Result\<close>
]:
  \<open> \<phi>IntroFrameVar' R S'' S' T T' E'' E'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> Simplify assertion_simplification E''' E''
\<Longrightarrow> (\<And>v. PROP Filter_Out_Free_Values (E''' v) (E v))
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S' \<longmapsto> T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>))
    (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S))
    (Trueprop ((\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def \<phi>IntroFrameVar'_def
    GOAL_CTXT_def FOCUS_TAG_def Simplify_def Action_Tag_def
    Simplify_def Filter_Out_Free_Values_def
  apply rule
  subgoal premises prems
    apply (simp only: prems(1))
    using \<phi>apply_proc[OF \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _\<close>,
          OF \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S' \<longmapsto> T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>\<close>[THEN \<phi>frame[where R=R],
              THEN \<phi>CONSEQ[rotated 1, OF \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>,
                OF view_shift_id, OF View_Shift_by_Subtyp[OF \<open>E''' _ \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s E _\<close>],
                simplified prems(1), unfolded \<open>E''' = E''\<close>, simplified prems(1)]]] .
  by (meson \<phi>apply_view_shift_P)

end


paragraph \<open>Applying on a Block / End a Block\<close>

(*TODO: Not stable. Need better improvement or depreciation.*)

definition \<open>Exhaustive_Abstract f f' \<longleftrightarrow> (f = f')\<close>

lemma Exhaustive_Abstract_I:
  \<open> Premise procedure_simplification (f = f')
\<Longrightarrow> Exhaustive_Abstract f f'\<close>
  unfolding Exhaustive_Abstract_def Premise_def by simp

\<phi>reasoner_ML Exhaustive_Abstract 1200 (conclusion \<open>Exhaustive_Abstract ?f ?f'\<close>) = \<open>
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
  | my_abstract_over _ v body =
      Abs ("", fastype_of v, abstract_bound_over (v,body))

fun strip btys (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, ty, x)) = strip (ty::btys) x
  | strip btys (\<^const>\<open>Pure.imp\<close> $ _ $ x) = strip btys x
  | strip btys (\<^const>\<open>Trueprop\<close> $ x) = (btys, x)
  | strip _ x = raise TERM ("Exhaustive_Abstract/strip", [x])

fun dec_bound_level d [] = []
  | dec_bound_level d (h::l) = inc_bound (d+1) h :: (dec_bound_level (d+1) l)

in
  fn (ctxt,sequent) =>
    let
      val (btys, Const (\<^const_name>\<open>Exhaustive_Abstract\<close>, _) $ f $ f')
        = strip [] (hd (Thm.prems_of sequent))
    in (case Term.strip_comb (Envir.beta_eta_contract f') of (Var v, args) =>
         Thm.instantiate (TVars.empty, Vars.make [
              (v, Thm.cterm_of ctxt (fold_rev (my_abstract_over btys)
                                              (dec_bound_level (~ (length args)) args) f))])
           sequent
        | _ => sequent)
       |> (fn seq => Seq.single (ctxt, @{thm Exhaustive_Abstract_I} RS seq))
    end
end
\<close>

lemma (in \<phi>spec) [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Conv (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?X \<longmapsto> ?Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>)) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f' \<lbrace> ?X' \<longmapsto> ?Y' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E' \<rbrace>))
\<close>]:
  \<open> Exhaustive_Abstract f f'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> (\<And>ret. \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y ret \<longmapsto> Y' ret \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA)
\<Longrightarrow> (\<And>ex.  \<^bold>v\<^bold>i\<^bold>e\<^bold>w E ex \<longmapsto> E' ex \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any3 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA)
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> X' \<longmapsto> Y' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>))\<close>
  unfolding \<phi>Application_Conv_def Exhaustive_Abstract_def GOAL_CTXT_def FOCUS_TAG_def
    Action_Tag_def
  using \<phi>CONSEQ by blast


paragraph \<open>Applying on View Shift Block\<close>

lemma (in \<phi>spec) [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Conv (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P)) (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X' \<longmapsto> ?Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P'))
\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (Any1 \<and> Any2 \<and> P \<longrightarrow> P')
\<Longrightarrow> PROP \<phi>Application_Conv (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)) (Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P'))\<close>
  unfolding \<phi>Application_Conv_def Exhaustive_Abstract_def GOAL_CTXT_def FOCUS_TAG_def
    Action_Tag_def View_Shift_def
  by blast


paragraph \<open>Applying on Ongoing Implication Construction\<close>

lemma apply_cast_on_imply_exact[\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P)) (Trueprop (?x \<in> ?S')) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P)) (Trueprop (x \<in> S)) (Trueprop (x \<in> T \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def Imply_def
  by blast

lemma apply_cast_on_imply_right_prod[\<phi>reason 1600 for \<open>
  PROP \<phi>Application_Method (Trueprop (?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P)) (Trueprop (?x \<in> ?R * ?S')) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method
            (Trueprop (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P))
            (Trueprop (x \<in> R * S))
            (Trueprop (x \<in> R * T \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using implies_left_prod
  by (metis Imply_def)

subparagraph \<open>Morphism\<close>

lemma [\<phi>reason 2000]:
  \<open> PROP \<phi>Application_Method (RP \<Longrightarrow> RX \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> morphism_mode) (Trueprop S) (PROP RET)
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (Morphism any_mode RP RX)) (Trueprop S) (PROP RET)\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def Morphism_def Action_Tag_def
  subgoal premises prems using prems(1)[OF prems(2), OF prems(3)[THEN mp], simplified] . .

lemma (in \<phi>spec) [\<phi>reason 1200 for \<open>
  PROP \<phi>Application_Method (\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S' \<longmapsto> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> morphism_mode)
        (Trueprop (CurrentConstruction ?mode ?blk ?RR ?S)) ?Result
\<close>]:
  " \<phi>IntroFrameVar R S'' S' T T'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' False
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (\<^bold>v\<^bold>i\<^bold>e\<^bold>w S' \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> morphism_mode)
      (Trueprop (CurrentConstruction mode blk RR S))
      (Trueprop ((CurrentConstruction mode blk RR T) \<and> (P1 \<and> P2)))"
  unfolding \<phi>IntroFrameVar_def \<phi>Application_Method_def \<phi>Application_def
    GOAL_CTXT_def FOCUS_TAG_def Action_Tag_def Simplify_def
  using "\<phi>view_shift_P" \<phi>view_shift_intro_frame
  by (metis (no_types, lifting))



subsection \<open>Action\<close>

text \<open>Action is a kind of meta calling mechanism.
  When user inputs some action name to call, initially the system does not know what
    the user intends to do, to construct a procedure or to cast by a view shift or to
      synthesis something or even to call a combination of these features.
  The exact construction is decided by reasoning.
  The action name is encoded into an antecedent, and then the reasoner starts to
    try to solve the antecedent, causing the system starts to construct the sequent
    according to the given action name and configured reasoning rules relating to
    this action name.\<close>

text \<open>The action name is encoded to be a fixed free variable or a constant of \<^typ>\<open>'cat action\<close>.
  Therefore the pattern matching can be native and fast.
  Note an action can be parameterized like, \<^typ>\<open>nat \<Rightarrow> bool \<Rightarrow> 'cat action\<close> parameterized
    by a nat and a boolean. Other parameters can come from the sequent.
\<close>

text \<open>\<^prop>\<open>P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close> tells \<^prop>\<open>A\<close> is something relating to the action Act, typically
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
  \<open> PROP Synthesis_Parse action action'
\<Longrightarrow> PROP Do_Action action' sequent result
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP DoSynthesis (action::'cat action) sequent result\<close>
  unfolding DoSynthesis_def Do_Action_def .

subsubsection \<open>Classes of Actions\<close>

class view_shift  (* The action can be a view shift *)
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

context \<phi>spec begin

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
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (can_be_implication action)\<close>
  unfolding Action_Tag_def
  by (simp add: \<phi>view_shift_by_implication) 


paragraph \<open>Action by View Shift\<close>


lemma [\<phi>reason 1100 for \<open>PROP Do_Action (?action::?'a::view_shift action) (Trueprop (CurrentConstruction ?mode ?s ?R ?X)) ?Result\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X1 \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R1\<heavy_comma> X1 \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action (action)
      (Trueprop (CurrentConstruction mode s R X))
      (Trueprop (CurrentConstruction mode s R (R1\<heavy_comma> Y) \<and> (Any \<and> Any2)))\<close>
  for action :: \<open>('a::view_shift) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>frame_view by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{view_shift, whole_target} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> Any))\<close>
  for action :: \<open>('a::{view_shift, whole_target}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>frame_view by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{view_shift, single_target} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
    except \<open>PROP Do_Action ?action (Trueprop (CurrentConstruction ?mode ?s ?H (?R \<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> Any))\<close>
  for action :: \<open>('a::{view_shift, single_target}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>frame_view by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{view_shift, single_target} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?R \<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H (R \<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R \<heavy_comma> Y) \<and> Any))\<close>
  for action :: \<open>('a::{view_shift, single_target}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>frame_view by blast


lemma [\<phi>reason 1200 for \<open>PROP Do_Action (?action::?'a::{multi_args_fixed_first,view_shift} action) (Trueprop (CurrentConstruction ?mode ?s ?R ?X)) ?Result\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Xr\<heavy_comma> X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R1\<heavy_comma> Xr \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action (action)
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R1\<heavy_comma> Y) \<and> Any \<and> Any2))\<close>
  for action :: \<open>('a::{multi_args_fixed_first,view_shift}) action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  by (metis (no_types, lifting) \<phi>spec.\<phi>view_shift_P \<phi>spec_axioms \<phi>view_shift_intro_frame \<phi>view_shift_intro_frame_R ab_semigroup_mult_class.mult_ac(1))


paragraph \<open>Action by Implication\<close>

subparagraph \<open>On CurrentConstruction\<close>

lemma [\<phi>reason 1090 for \<open>PROP Do_Action (?action::?'a::implication action) (Trueprop (CurrentConstruction ?mode ?s ?H ?XX)) ?Result\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w XX \<longmapsto> R\<heavy_comma> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H XX))
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> Y) \<and> (P2 \<and> P)))\<close>
  for action :: \<open>'a::implication action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190
    for \<open>PROP Do_Action (?action::?'a::{whole_target,implication} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> P))\<close>
  for action :: \<open>'a::{whole_target,implication} action\<close>
  unfolding Do_Action_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190
    for \<open>PROP Do_Action (?action::?'a::{single_target,implication} action) (Trueprop (CurrentConstruction ?mode ?s ?H ?X)) ?Result\<close>
    except  \<open>PROP Do_Action ?action (Trueprop (CurrentConstruction ?mode ?s ?H (?R\<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H X))
      (Trueprop (CurrentConstruction mode s H Y \<and> P))\<close>
  for action :: \<open>'a::{single_target,implication} action\<close>
  unfolding Do_Action_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190
    for \<open>PROP Do_Action (?action::?'a::{single_target,implication} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?R \<heavy_comma> ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> Y) \<and> P))\<close>
  for action :: \<open>'a::{single_target,implication} action\<close>
  unfolding Do_Action_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>view_shift_by_implication implies_left_prod by blast

lemma [\<phi>reason 1190 for \<open>PROP Do_Action (?action::?'a::{implication,multi_args_fixed_first} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?RR \<heavy_comma> ?X))) ?Result\<close>]:
  \<open> Xr \<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w RR \<longmapsto> R\<heavy_comma> Xr \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (CurrentConstruction mode s H (RR \<heavy_comma> X)))
      (Trueprop (CurrentConstruction mode s H (R\<heavy_comma> Y) \<and> P2 \<and> P))\<close>
  for action :: \<open>'a::{implication,multi_args_fixed_first} action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  by (metis (no_types, lifting) \<phi>cast_P \<phi>spec.\<phi>view_shift_P \<phi>spec_axioms \<phi>view_shift_intro_frame_R ab_semigroup_mult_class.mult_ac(1) implies_left_prod)

(* No need to provide general search rule because the rule of
\<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action\<close>
(see paragraph Generalization) converts all general search of view_shift for implication. *)

end

subparagraph \<open>On \<open>x \<in> P\<close>\<close>

lemma [\<phi>reason 1100
    for \<open>PROP Do_Action (?action::?'a::{implication, single_target} action) (Trueprop (?s \<in> ?X)) ?Result\<close>
    except \<open>PROP Do_Action ?action (Trueprop (?s \<in> (?R * ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (s \<in> X))
      (Trueprop (s \<in> Y \<and> P))\<close>
  for action :: \<open>'a::{implication,single_target} action\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def by blast

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{single_target,implication} action) (Trueprop (?s \<in> (?R * ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (s \<in> (R * X)))
      (Trueprop (s \<in> (R * Y) \<and> P))\<close>
  for action :: \<open>'a::{implication,single_target} action\<close>
  unfolding Do_Action_def Action_Tag_def
  by (meson Imply_def implies_left_prod)

lemma [\<phi>reason 1200
    for \<open>PROP Do_Action (?action::?'a::{implication, whole_target} action) (Trueprop (?s \<in> ?X)) ?Result\<close>
    except \<open>PROP Do_Action ?action (Trueprop (?s \<in> (?R * ?X))) ?Result\<close>
]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (s \<in> X))
      (Trueprop (s \<in> Y \<and> P))\<close>
  for action :: \<open>'a::{implication,whole_target} action\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def by blast

(* TODO!
lemma [\<phi>reason 1190 on \<open>PROP Do_Action (?action::?'a::{implication,multi_args_fixed_first} action) (Trueprop (CurrentConstruction ?mode ?s ?H (?RR \<heavy_comma> ?X))) ?Result\<close>]:
  \<open> Xr * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> PROP Do_Action action
      (Trueprop (s \<in> (RR * X)))
      (Trueprop (s \<in> (R * Y) \<and> P))\<close>
  for action :: \<open>'a::{implication,multi_args_fixed_first} action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  by (metis (no_types, lifting) \<phi>cast_P \<phi>spec.\<phi>view_shift_P \<phi>spec_axioms \<phi>view_shift_intro_frame_R ab_semigroup_mult_class.mult_ac(1) implies_left_prod)
*)


(*
lemma [\<phi>reason 1100]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action
\<Longrightarrow> PROP Assertion_Level_Reasoning (XX \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * X \<^bold>a\<^bold>n\<^bold>d P2)
\<Longrightarrow> PROP Do_Action action
      (Trueprop (s \<in> XX))
      (Trueprop (s \<in> (R * Y) \<and> P2 \<and> P))\<close>
  for action :: \<open>'a::implication action\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift_P \<phi>view_shift_by_implication implies_left_prod by blast
*)


subsection \<open>Actions\<close>

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


section \<open>Interactive Programming \& Proving Environment\<close>

subsection \<open>ML codes\<close>

ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/procedure.ML"


ML_file \<open>library/NuSys.ML\<close>
ML_file "./library/processors.ML"
ML_file "./library/obtain.ML"
ML_file "./library/generalization.ML"
(* ML_file "./codegen/compilation.ML" *)
ML_file \<open>library/NuToplevel.ML\<close>


subsection \<open>Isar Commands \& Attributes\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<phi>instr"}, NuInstructions.list_definitions #> map snd))  \<close>

attribute_setup \<phi>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<phi>-system\<close>

attribute_setup \<phi>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (NuProcessor.get_attr ctx name) (ctx,toks))
  || Scan.lift NuProcessor.process_attr\<close>
  \<open>Evaluate the \<phi>-system process or the process of the given processor on the target theorem\<close>


ML \<open>

local open Scan NuToplevel NuSys Parse 
val nustatement = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- opt_attribs -- Scan.repeat1 Parse.propp);
val structured_statement =
  nustatement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));
val statement1 = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.propp);
val requires_statement = \<^keyword>\<open>assumes\<close> |-- Parse.!!! statement1;
val premises_statement = \<^keyword>\<open>premises\<close> |-- Parse.!!! statement1;
val precond_statement = Scan.repeat ((premises_statement >> map (pair NuToplevel.Premise))
                || (requires_statement >> map (pair NuToplevel.Requirement))) >> flat;
val requires_opt1 = Scan.option (\<^keyword>\<open>assumes\<close> |-- Parse.term);
val where_statement = Scan.optional (\<^keyword>\<open>where\<close> |--
        Parse.and_list1 (Scan.repeat Args.var --| Parse.$$$ "=" -- Parse.term)) [];
val defines_statement = Scan.optional ($$$ "defines" |-- Parse.!!! statement1) [];
val goal = Scan.option (\<^keyword>\<open>goal\<close> |-- Parse.term)
val nu_statements = Parse.for_fixes -- Scan.optional Parse_Spec.includes [] --
           where_statement -- defines_statement  -- precond_statement -- goal;

val arg = Parse.term
val arg_ret = (\<^keyword>\<open>argument\<close> |-- arg --| \<^keyword>\<open>return\<close> -- arg -- option (\<^keyword>\<open>throws\<close> |-- arg))

val def_const_flag =
  Scan.optional ((\<^keyword>\<open>(\<close> |-- NuParse.$$$ "nodef" --| \<^keyword>\<open>)\<close>) >> (K false)) true

in

(* val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>exty_simproc\<close> "setup the pecific simproc for \<^const>\<open>ExTy\<close>"
  (Parse.binding >> NuExTyp.set_simproc_cmd) *)

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((def_const_flag -- Parse_Spec.opt_thm_name ":" -- nu_statements -- arg_ret) >>
        (fn (((def_const, b),(((((fixes,includes),lets),defs),preconds),G)), ((arg,ret),throws)) =>  
            (begin_proc_cmd def_const b arg ret throws fixes includes lets defs preconds G)));

val loop_variables = $$$ "var" |-- !!! vars;
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close> "begin a recursive procedure construction"
    (((def_const_flag -- Parse_Spec.opt_thm_name ":") -- loop_variables -- nu_statements -- arg_ret) >>
        (fn ((((def_const,b),vars),(((((fixes,includes),lets),defs),preconds),G)), ((arg,ret),throws)) =>  
            (begin_rec_proc_cmd def_const b arg ret throws (vars,fixes) includes lets defs preconds G)));

(* val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>\<phi>cast\<close> "begin a procedure construction"
    ((Parse_Spec.thm_name ":" -- option ($$$ "and" |-- Parse.term) -- nu_statements - arg_ret) >>
        (fn ((b,(((((fixes,includes),lets),defs),preconds),G)), (arg,ret)) =>
            (begin_cast_cmd b arg ret fixes includes lets defs preconds G))); *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>;;\<close> "Lead statements of \<phi> programs"
    (NuProcessor.powerful_process_p >> Toplevel.proof)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "Begin a \<phi> program block"
   (((optional (\<^keyword>\<open>premises\<close> |--
            and_list (binding -- opt_attribs || Parse.attribs >> pair Binding.empty)) []
      >> NuToplevel.begin_block_cmd)
   -- NuProcessor.powerful_process_p_inert)
   >> (fn (blk,prcs) => Toplevel.proof' (prcs oo blk)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "End a \<phi> program block"
    (option (\<^keyword>\<open>for\<close> |-- term) >> (Toplevel.proof' o NuToplevel.end_block_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>.\<close> "End a \<phi> program block using default tactic"
    (((option (\<^keyword>\<open>for\<close> |-- term) >> (fn cast => fn int =>
        NuToplevel.end_block_cmd cast int
    #> (fn s => Proof.using_facts (Proof_Context.get_thms (Proof.context_of s) "\<phi>") s)
    #> Proof.local_future_terminal_proof
          ((Method.Basic (SIMPLE_METHOD o CHANGED_PROP o auto_tac), Position.no_range)
          ,NONE)))
   -- NuProcessor.powerful_process_p_inert)
   >> (fn (blk,prcs) => Toplevel.proof' (prcs oo blk)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>processor\<close> "define \<phi>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword || Parse.string)
          -- Parse.nat -- (\<^keyword>\<open>(\<close> |-- Parse.enum "|" Parse.term --| \<^keyword>\<open>)\<close> )
          -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
        >> NuProcessor.setup_cmd)

(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>interface\<close> "declare \<phi>interface"
      (Parse.binding --| $$$ "=" -- Parse.const -- option ($$$ ":" |-- Parse.typ --| $$$ "\<longmapsto>" -- Parse.typ)
        >> (Toplevel.theory o NuProcedure.add_interface_command))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<phi>export_llvm\<close> "export LLVM target"
      (Scan.succeed (Toplevel.theory (NuToplevel.export_LLVM))) *)

end
\<close>

attribute_setup intro_forall = \<open>Scan.lift (Scan.repeat Args.var) >> (fn tms =>
  Thm.rule_attribute [] (fn ctx => fn th => 
    let open Thm
    val vs = add_vars th Vars.empty |> Vars.dest
    val foralls = map (fn tm => case find_first (fn (_,v) => #1 (dest_Var (term_of v)) = tm) vs
                  of SOME (_,y) => y | _ => error (#1 tm ^ " is not a var ")) tms
    in Drule.forall_intr_list foralls th end)) \<close>


subsection \<open>Elements of the Language\<close>

text \<open>Convention of priorities:
  \<^item> Simplifications and Conversions for canonical forms < 1000
  \<^item> Reasoning Antecedents = 1000
  \<^item> General Application not bound on specific pattern or keyword : 9000~9999
\<close>


subsubsection \<open>Controls\<close>

\<phi>processor set_auto_level 10 (\<open>PROP ?P\<close>) \<open>(fn (ctxt, sequent) => NuParse.auto_level_force >>
  (fn auto_level' => fn _ => (Config.put Nu_Reasoner.auto_level auto_level' ctxt, sequent)))\<close>
  \<open>Note the declared auto-level is only valid during the current statement.
   In the next statement, the auto-level will be reset to the default fully-automated level.\<close>

\<phi>processor repeat 12 (\<open>PROP ?P\<close>) \<open>let
  in fn (ctxt, sequent) =>
    Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*") >> (fn (tok,n) => fn () =>
        (case Int.fromString n of SOME n => funpow n | _ => error ("should be a number: "^n))
          (NuProcessor.process_by_input [tok]) (ctxt, sequent)
    )
  end\<close>


subsubsection \<open>Constructive\<close>

\<phi>processor (in \<phi>spec) accept_call 500 (\<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g ?f \<^bold>o\<^bold>n ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E\<close>)
  \<open>fn stat => Scan.succeed (fn _ => NuSys.accept_proc stat)\<close>

\<phi>processor "apply" 9000 (\<open>?P\<close>) \<open> fn (ctxt,sequent) => NuApplicant.parser >> (fn xnames => fn _ =>
  (NuApply.apply (NuApplicant.applicant_thms ctxt xnames) (ctxt, sequent)))\<close>

\<phi>processor set_param 5000 (\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ?P \<Longrightarrow> PROP ?Q\<close>) \<open>fn stat => Parse.term >> (fn term => fn _ =>
  NuSys.set_param_cmd term stat)\<close>

\<phi>processor set_label 5000 (\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l ?P \<Longrightarrow> PROP ?Q\<close>) \<open>fn stat => Parse.name >> (fn name => fn _ =>
  NuSys.set_label name stat)\<close>

\<phi>processor rule 9000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
  \<open>fn (ctxt, sequent) => NuApplicant.parser >> (fn thms => fn _ =>
    let open NuBasics
    val apps = NuApplicant.applicant_thms ctxt thms
    val sequent = perhaps (try (fn th => @{thm Argument_I} RS th)) sequent
    in case Seq.pull (Thm.biresolution (SOME ctxt) false (map (pair false) apps) 1 sequent)
         of SOME (th, _) => (ctxt,th)
          | _ => raise THM ("RSN: no unifiers", 1, sequent::apps) end)\<close>

ML \<open>val phi_synthesis_parsing = Config.declare_bool ("\<phi>_synthesis_parsing", \<^here>) (K false)\<close>

\<phi>processor (in \<phi>spec) synthesis 8800 (\<open>CurrentConstruction ?mode ?blk ?H ?S\<close> | \<open>PROP ?P \<Longrightarrow> PROP ?RM\<close>)
  \<open>fn (ctxt, sequent) => Parse.group (fn () => "term") (Parse.inner_syntax (Parse.cartouche || Parse.number))
>> (fn raw_term => fn () =>
  let
    val ctxt_parser = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
                        |> Config.put phi_synthesis_parsing true
    val term = Syntax.parse_term ctxt_parser raw_term
                  |> Syntax.check_term ctxt_parser
                  |> Thm.cterm_of ctxt
   in
    NuSys.synthesis term (ctxt, sequent)
  end)\<close>

\<phi>processor (in \<phi>spec) existential_elimination 150 (\<open>CurrentConstruction ?mode ?blk ?H (ExSet ?T)\<close>)
  \<open>fn stat => (\<^keyword>\<open>\<exists>\<close> |-- Parse.list1 Parse.binding) #> (fn (insts,toks) => (fn () =>
      raise Process_State_Call' (toks, stat, NuObtain.choose insts), []))\<close>

\<phi>processor (in \<phi>spec) implicit_existential_elimination 800 (\<open>CurrentConstruction ?mode ?blk ?H (ExSet ?T)\<close>)
  \<open>fn stat => Scan.succeed (fn () =>
    let
      val _ $ X = PhiSyntax.dest_CurrentConstruction (Thm.concl_of (snd stat)) |> #4
      fun is_Abs (Abs _) = true | is_Abs _ = false
    in
      if is_Abs X andalso Config.get (#1 stat) Nu_Reasoner.auto_level >= 2
      then raise Process_State_Call (stat, NuObtain.auto_choose)
      else raise Bypass NONE
    end)\<close>

subsubsection \<open>Simplifiers \& Reasoners\<close>

\<phi>processor enter_proof 5000 (\<open>Premise ?mode ?P \<Longrightarrow> PROP ?Any\<close>)
  \<open>fn stat => \<^keyword>\<open>affirm\<close> >> (fn _ => fn () =>
      raise Terminate_Process (stat, snd o NuToplevel.prove_prem false))\<close>

\<phi>processor \<phi>simplifier 100 (\<open>\<phi>spec.CurrentConstruction _ _ ?mode ?blk ?H ?T\<close> | \<open>?x \<in> ?S\<close>)
  \<open>NuProcessors.simplifier\<close>
(* \<phi>processor \<phi>simplifier_final 9999 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close> *)

\<phi>processor move_fact1  90 (\<open>?Any \<and> ?P\<close>)
\<open>fn stat => Scan.succeed (fn _ => raise Bypass (SOME (NuSys.move_lemmata stat)))\<close>

\<phi>processor move_fact2 110 (\<open>?Any \<and> ?P\<close>)
\<open>fn stat => Scan.succeed (fn _ => raise Bypass (SOME (NuSys.move_lemmata stat)))\<close>

\<phi>processor automatic_morphism 90 (\<open>\<phi>spec.CurrentConstruction _ _ ?mode ?blk ?H ?T\<close> | \<open>?x \<in> ?S\<close>)
\<open>not_safe (fn stat => Scan.succeed (fn _ => NuSys.apply_automatic_morphism stat
      handle Empty => raise Bypass NONE))\<close>

(* Any simplification should finish before priority 999, or else
 *  this processor will be triggered unnecessarily frequently.*)
\<phi>processor set_\<phi>this 999 (\<open>\<phi>spec.CurrentConstruction _ _ ?mode ?blk ?H ?T\<close> | \<open>?x \<in> ?S\<close>)
\<open>fn (ctxt, sequent) => Scan.succeed (fn _ =>
  let
    val ctxt' = NuBasics.update_programming_sequent' sequent ctxt
  in
    raise Bypass (SOME(ctxt', sequent))
  end)\<close>


\<phi>processor \<phi>reason 1000 (\<open>PROP ?P \<Longrightarrow> PROP ?Q\<close>)
\<open>fn (ctxt,sequent) => Scan.succeed (fn _ =>
  case Nu_Reasoner.reason 1 (ctxt, sequent)
    of SOME (ctxt',sequent') => (ctxt', sequent')
     | NONE => raise Bypass (SOME (ctxt,sequent))
)\<close>

\<phi>processor auto_obligation_solver 800 (\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ?P \<Longrightarrow> PROP ?Q\<close> | \<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n ?P \<Longrightarrow> PROP ?Q\<close>)
  \<open>fn (ctxt,sequent) => Scan.succeed (fn () =>
    if Config.get ctxt Nu_Reasoner.auto_level >= 2
    then case Seq.pull (Nu_Reasoners.auto_obligation_solver ctxt sequent)
           of SOME (ret, _) => (ctxt, ret)
            | NONE => raise Bypass NONE
    else raise Bypass NONE)\<close>

\<phi>processor fold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => NuParse.$$$ "fold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.fold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>

\<phi>processor unfold 2000 (\<open>PROP ?P\<close>) \<open>
  fn (ctxt, sequent) => NuParse.$$$ "unfold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (ctxt, Local_Defs.unfold ctxt (Attrib.eval_thms ctxt thms) sequent)
)\<close>

(*immediately before the accept call*)
\<phi>processor (in \<phi>spec) throws 490 (\<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g ?f \<^bold>o\<^bold>n ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E\<close>)
  \<open>fn (ctxt, sequent) => \<^keyword>\<open>throws\<close> >> (fn _ => fn () =>
    (ctxt, sequent RS (Proof_Context.get_thm ctxt "local._\<phi>cast_exception_"))
)\<close>

(* \<phi>processor goal 1300 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?T\<close> \<open>
  fn (ctxt, sequent) => Parse.$$$ "goal" >> (fn _ => fn _ =>
    let
      val goal = Proof_Context.get_thm ctxt "\<phi>thesis" |> Drule.dest_term
      val (_,_,desired_nu) = PhiSyntax.dest_procedure_c goal
      val ty = Thm.typ_of_cterm desired_nu
      val prot = Const (\<^const_name>\<open>Implicit_Protector\<close>, ty --> ty) |> Thm.cterm_of ctxt
      val ctxt = Config.put Nu_Reasoner.auto_level 1 ctxt
    in NuSys.cast (Thm.apply prot desired_nu) (ctxt,sequent) end
)\<close> *)

paragraph \<open>Quantification Expansion\<close>

simproc_setup named_forall_expansion ("All (P :: 'a <named> 'names \<Rightarrow> bool)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.forall_expansion)\<close>

simproc_setup named_exSet_expansion ("ExSet (P :: 'a <named> 'names \<Rightarrow> 'b set)") =
  \<open>K (fn ctx => fn cterms => QuantExpansion.simproc_of QuantExpansion.ExNu_expansion ctx cterms)\<close>

simproc_setup named_pureAll_expansion ("Pure.all (P :: 'a <named> 'names \<Rightarrow> prop)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.pure_All_expansion)\<close>




section \<open>Elementary \<phi>-Types\<close>

subsection \<open>Syntax Sugars\<close>

text \<open>Sometimes, we do not want to verbosely write a semantic type if it is known syntactically.
  We use syntax translation to achieve a sugar to do this.\<close>

syntax TY_of_\<phi> :: \<open>('a,'b) \<phi> \<Rightarrow> 'TY\<close> ("TY'_of'_\<phi>")

subsection \<open>Type Level Subjection\<close>

definition SubjectionTY :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> ('a,'b) \<phi>\<close> (infixl "\<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j" 25)
  where \<open> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (\<lambda>x. x \<Ztypecolon> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<close>

translations "TY_of_\<phi> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)" \<rightharpoonup> "TY_of_\<phi> T"

lemma SubjectionTY_expn[\<phi>programming_simps, \<phi>expns]:
  \<open>(x \<Ztypecolon> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (x \<Ztypecolon> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding set_eq_iff SubjectionTY_def \<phi>Type_def by simp

lemma SubjectionTY_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<Longrightarrow> (P \<Longrightarrow> Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding SubjectionTY_expn using Subjection_inhabited .

lemma SubjectionTY_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited (x \<Ztypecolon> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> Inhabited (x \<Ztypecolon> T) \<and> P\<close>
  unfolding SubjectionTY_expn by (simp add: \<phi>inhabited)


subsection \<open>Type Level Existential Quantification\<close>

definition ExTyp :: \<open>('c \<Rightarrow> ('a, 'b) \<phi>) \<Rightarrow> ('a, 'c \<Rightarrow> 'b)\<phi>\<close> (binder "\<exists>\<phi>" 10)
  where \<open>ExTyp T = (\<lambda>x. (\<exists>*c. x c \<Ztypecolon> T c))\<close>

syntax
  "_SetcomprPhiTy" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j/ _./ _ " [2,0,2] 2)
  "_SetcomprPhiTy'" :: "logic \<Rightarrow> idts \<Rightarrow> logic \<Rightarrow> logic"

parse_ast_translation \<open>
  let open Ast
    fun idts_to_abs x (Appl [Constant "_idts", a, b]) = Appl [Constant "_abs", a, idts_to_abs x b]
      | idts_to_abs x c = Appl [Constant "_abs", c, x]
    fun parse_SetcomprPhiTy ctxt [Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, x, T],idts,P] =
          Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>,
                idts_to_abs x idts,
                Appl [Constant "\<^const>Sys.ExTyp_binder", idts,
                      (case P of (Appl [Constant "_constrain", Variable "True", _]) => T
                               | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, T, P])]]
      | parse_SetcomprPhiTy ctxt [X,idts,P] =
          Appl [Constant "\<^const>Sys.ExTyp_binder", idts,
                (case P of (Appl [Constant "_constrain", Variable "True", _]) => X
                         | _ => Appl [Constant \<^const_name>\<open>SubjectionTY\<close>, X, P])]
  in [(\<^syntax_const>\<open>_SetcomprPhiTy\<close>, parse_SetcomprPhiTy)] end
\<close>

(* TODO
term \<open>x \<Ztypecolon> (X a) \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j a b c. P a\<close>

translations
  " _SetcomprPhiTy' x idts X" <= "x \<Ztypecolon> (\<exists>\<phi> idts. X)"

print_ast_translation \<open>
  [(\<^syntax_const>\<open>_SetcomprPhiTy'\<close>, (fn _ => fn x => hd (@{print} x)))]
\<close>

term \<open>x \<Ztypecolon> (X a) \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j a b c. P a\<close>

*)

lemma ExTyp_expn[\<phi>expns,\<phi>programming_simps]:
  \<open>(x \<Ztypecolon> ExTyp T) = (\<exists>*a. x a \<Ztypecolon> T a)\<close>
  unfolding set_eq_iff ExTyp_def \<phi>Type_def by (simp add: \<phi>expns)

lemma ExTyp_inhabited[elim!, \<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> ExTyp T) \<Longrightarrow> (Inhabited (\<exists>*a. x a \<Ztypecolon> T a) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding ExTyp_expn .

lemma ExTyp_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited (x \<Ztypecolon> ExTyp T) \<longleftrightarrow> (\<exists>c. Inhabited (x c \<Ztypecolon> T c))\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)



subsection \<open>Identity\<close>

definition Identity :: " ('a,'a) \<phi> " where "Identity x = {x}"

lemma Identity_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> Identity) \<longleftrightarrow> p = x"
  unfolding \<phi>Type_def Identity_def by auto

lemma Identity_inhabited[elim!,\<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> Identity) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma Identity_functional[\<phi>reason]:
  \<open>is_singleton (x \<Ztypecolon> Identity)\<close>
  by (rule is_singletonI''; simp add: \<phi>expns)

lemma Identity_E[\<phi>reason for \<open>?v \<Ztypecolon> Identity \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?x \<Ztypecolon> ?T \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> (x \<Ztypecolon> T) \<Longrightarrow> v \<Ztypecolon> Identity \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

lemma (in \<phi>empty_sem) [simp]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> SemTyp_Of (v \<Ztypecolon> Identity) = TY\<close>
  unfolding \<phi>Type_def Identity_def
  by (simp add: \<phi>SemType_def)

lemma (in \<phi>empty) Identity_E_vs[\<phi>reason for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?v \<Ztypecolon> Identity \<longmapsto> ?x \<Ztypecolon> ?T \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w v \<Ztypecolon> Identity \<longmapsto> x \<Ztypecolon> T\<close>
  by (simp add: Identity_E View_Shift_by_Subtyp)

lemma Action_to_Identity[\<phi>reason 80 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> to_Identity\<close>]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (v \<Ztypecolon> Identity \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j v. v \<in> X) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> to_Identity\<close>
  unfolding Action_Tag_def Imply_def by (simp add: \<phi>expns)

lemma Action_from_Identity:
  \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> X \<Longrightarrow> v \<Ztypecolon> Identity \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> from_Identity\<close>
  unfolding Imply_def Premise_def Action_Tag_def by (simp add: \<phi>expns)


subsection \<open>Inter\<close>

definition \<phi>Inter :: \<open>('c,'ax) \<phi> \<Rightarrow> ('c, 'bx) \<phi> \<Rightarrow> ('c, 'ax \<times> 'bx) \<phi>\<close> (infixl "\<inter>\<^sub>\<phi>" 70)
  where \<open>(T \<inter>\<^sub>\<phi> U) = (\<lambda>(x,y). (x \<Ztypecolon> T) \<inter> (y \<Ztypecolon> U))\<close>

lemma \<phi>Inter_expn[\<phi>expns]:
  \<open>((x,y) \<Ztypecolon> (T \<inter>\<^sub>\<phi> U)) = (x \<Ztypecolon> T) \<inter> (y \<Ztypecolon> U)\<close>
  unfolding set_eq_iff \<phi>Type_def \<phi>Inter_def by simp

lemma \<phi>Inter_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited ((x,y) \<Ztypecolon> (T \<inter>\<^sub>\<phi> U)) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (y \<Ztypecolon> U) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns; blast)


subsection \<open>None\<close>

definition \<phi>None :: \<open>('v::one, unit) \<phi>\<close> ("\<circle>")
  where \<open>\<phi>None = (\<lambda>x. { 1 }) \<close>

lemma \<phi>None_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>None) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>None_def \<phi>Type_def by simp

lemma \<phi>None_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>None) \<Longrightarrow> C \<Longrightarrow> C\<close> .


lemma \<phi>None_itself_is_one[simp]:
  \<open>(() \<Ztypecolon> \<phi>None) = 1\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)


lemma [\<phi>reason 1500
    for \<open>(() \<Ztypecolon> \<phi>None) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::simplification action)\<close>
    except \<open>(() \<Ztypecolon> \<phi>None) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?x \<Ztypecolon> ?T \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::simplification action)\<close>
]:
  \<open>(() \<Ztypecolon> \<phi>None) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def by (simp add: implies_refl)


subsection \<open>Prod\<close>

definition \<phi>Prod :: " ('concrete::sep_magma, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 55)
  where "A \<^emph> B = (\<lambda>(a,b). B b * A a)"

lemma \<phi>Prod_expn[\<phi>expns]:
  "concrete \<in> ((a,b) \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>cb ca. concrete = cb * ca \<and> cb \<in> (b \<Ztypecolon> B) \<and> ca \<in> (a \<Ztypecolon> A) \<and> cb ## ca)"
  unfolding \<phi>Prod_def \<phi>Type_def times_set_def by simp

lemma \<phi>Prod_expn':
  \<open>((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma \<phi>Prod_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<Longrightarrow> (Inhabited (x1 \<Ztypecolon> T1) \<Longrightarrow> Inhabited (x2 \<Ztypecolon> T2) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

(* lemma \<phi>Prod_inhabited_expn[\<phi>inhabited]:
  \<open>Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<longleftrightarrow> Inhabited (x1 \<Ztypecolon> T1) \<and> Inhabited (x2 \<Ztypecolon> T2)\<close>
  unfolding Inhabited_def apply (simp add: \<phi>expns) *)

lemma \<phi>Prod_split: "((a,b) \<Ztypecolon> A \<^emph> B) = (b \<Ztypecolon> B) * (a \<Ztypecolon> A)"
  by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Prod_\<phi>None:
  \<open>((x',y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'a::sep_magma_1 set)\<close>
  \<open>((x,y') \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'b::sep_magma_1 set)\<close>
  unfolding set_eq_iff
  by (simp_all add: \<phi>expns)

(*lemma (in \<phi>empty) SepNu_to_SepSet: "(OBJ (a,b) \<Ztypecolon> A \<^emph> B) = (OBJ a \<Ztypecolon> A) * (OBJ b \<Ztypecolon> B)"
  by (simp add: \<phi>expns set_eq_iff times_list_def) *)

subsubsection \<open>Reasoning Rules\<close>

paragraph \<open>View Shift\<close>

lemma (in \<phi>empty) [\<phi>reason for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w (?x,?y) \<Ztypecolon> ?N \<^emph> ?M \<longmapsto> (?x',?y') \<Ztypecolon> ?N' \<^emph> ?M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> x' \<Ztypecolon> N' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w y \<Ztypecolon> M \<longmapsto> y' \<Ztypecolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w (x,y) \<Ztypecolon> N \<^emph> M \<longmapsto> (x',y') \<Ztypecolon> N' \<^emph> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2"
  unfolding View_Shift_def \<phi>Prod_expn'
  by (smt (verit, best) mult.commute mult.left_commute) 

paragraph \<open>Implication\<close>

lemma [\<phi>reason for \<open>(?x,?y) \<Ztypecolon> ?N \<^emph> ?M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (?x',?y') \<Ztypecolon> ?N' \<^emph> ?M' \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  " x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> N' \<^bold>a\<^bold>n\<^bold>d P1
\<Longrightarrow> y \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y' \<Ztypecolon> M' \<^bold>a\<^bold>n\<^bold>d P2
\<Longrightarrow> (x,y) \<Ztypecolon> N \<^emph> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (x',y') \<Ztypecolon> N' \<^emph> M' \<^bold>a\<^bold>n\<^bold>d P1 \<and> P2"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200]:
  \<open> (y \<Ztypecolon> Y) * (x \<Ztypecolon> X) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> (x,y) \<Ztypecolon> (X \<^emph> Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding \<phi>Prod_split .

lemma [\<phi>reason 1200]:
  \<open> A * (y \<Ztypecolon> Y) * (x \<Ztypecolon> X) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> A * ((x,y) \<Ztypecolon> X \<^emph> Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P\<close>
  for A :: \<open>'a::sep_semigroup set\<close>
  unfolding \<phi>Prod_split
  by (simp add: mult.assoc)

lemma [\<phi>reason 1200]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (z \<Ztypecolon> Z) * (y \<Ztypecolon> Y) \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (y,z) \<Ztypecolon> (Y \<^emph> Z) \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding \<phi>Prod_split .

lemma [\<phi>reason 1200]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A * (z \<Ztypecolon> Z) * (y \<Ztypecolon> Y) \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A * ((y,z) \<Ztypecolon> Y \<^emph> Z) \<^bold>a\<^bold>n\<^bold>d P\<close>
  for A :: \<open>'a::sep_semigroup set\<close>
  unfolding \<phi>Prod_split
  by (simp add: mult.assoc)

lemma [\<phi>reason 1200]:
  \<open> A * B * C \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> A * (B * C) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P\<close>
  for A :: \<open>'a::sep_semigroup set\<close>
  by (simp add: mult.assoc)

lemma [\<phi>reason 1200]:
  \<open> Z \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A * B * C \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> Z \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A * (B * C) \<^bold>a\<^bold>n\<^bold>d P\<close>
  for A :: \<open>'a::sep_semigroup set\<close>
  by (simp add: mult.assoc)

lemma [\<phi>reason 50 for \<open>?A * ?B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X * ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d Q
\<Longrightarrow> A * B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X * Y \<^bold>a\<^bold>n\<^bold>d P \<and> Q\<close>
  for A :: \<open>'a::sep_semigroup set\<close>
  by (meson implies_left_prod implies_right_prod implies_trans)
  
paragraph \<open>Action\<close>

lemma [\<phi>reason 1200 for \<open>?A * ?B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{structural, implication} action)\<close>]:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d Q \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> A * B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X * Y \<^bold>a\<^bold>n\<^bold>d P \<and> Q \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{structural, implication} action\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

paragraph \<open>Simplification\<close>

lemma \<phi>Prod_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (y \<Ztypecolon> U) = (y' \<Ztypecolon> U')
\<Longrightarrow> ((x,y) \<Ztypecolon> T \<^emph> U) = ((x',y') \<Ztypecolon> T' \<^emph> U')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Prod_simp_cong ("(x,y) \<Ztypecolon> (T \<^emph> U)") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>Prod_simp_cong} ctxt)
\<close>

lemma [simp]:
  \<open>((x,y) \<Ztypecolon> ExTyp T \<^emph> U) = ((\<lambda>c. (x c, y)) \<Ztypecolon> (\<exists>\<phi> c. T c \<^emph> U))\<close>
  by (clarsimp simp add: set_eq_iff \<phi>expns; blast)

lemma [simp]:
  \<open> NO_MATCH (ExTyp Any) T
\<Longrightarrow> ((x,y) \<Ztypecolon> T \<^emph> ExTyp U) = ((\<lambda>c. (x, y c)) \<Ztypecolon> (\<exists>\<phi> c. T \<^emph> U c))\<close>
  by (clarsimp simp add: set_eq_iff \<phi>expns; blast)


(*lemma [simp]: "A \<inter> S \<perpendicular> A \<inter> -S"
  unfolding disjoint_def by auto
lemma heap_split_id: "P h1' h2' \<Longrightarrow> \<exists>h1 h2. h1' ++ h2' = h1 ++ h2 \<and> P h1 h2" by auto
lemma heap_split_by_set: "P (h |` S) (h |` (- S)) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  by (rule exI[of _ "h |` S"], rule exI[of _ "h |` (- S)"])
    (auto simp add: map_add_def option.case_eq_if restrict_map_def disjoint_def disjoint_iff domIff)
lemma heap_split_by_addr_set: "P (h |` (MemAddress ` S)) (h |` (- (MemAddress ` S))) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  using heap_split_by_set .*)


subsection \<open>List Item \& Empty List\<close>

subsubsection \<open>List Item\<close>

definition List_Item :: \<open>('v, 'a) \<phi> \<Rightarrow> ('v list, 'a) \<phi>\<close>
  where \<open>List_Item T = (\<lambda>x. { [v] |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma List_Item_expn[\<phi>expns]:
 \<open>p \<in> (x \<Ztypecolon> List_Item T) \<longleftrightarrow> (\<exists>v. p = [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding List_Item_def \<phi>Type_def by simp

lemma List_Item_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> List_Item T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<comment> \<open>A example for how to represent multi-elements list\<close>
  \<open> v1 \<in> (x1 \<Ztypecolon> T1)
\<Longrightarrow> v2 \<in> (x2 \<Ztypecolon> T2)
\<Longrightarrow> [v1,v2] \<in> ((x1, x2) \<Ztypecolon> (List_Item T1 \<^emph> List_Item T2))\<close>
  by (simp add: \<phi>expns times_list_def, rule exI[where x=\<open>[v2]\<close>], rule exI[where x=\<open>[v1]\<close>], simp)

subsubsection \<open>Empty List\<close>

definition Empty_List :: \<open>('v list, unit) \<phi>\<close>
  where \<open>Empty_List = (\<lambda>x. { [] })\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Empty_List) \<longleftrightarrow> p = []\<close>
  unfolding Empty_List_def \<phi>Type_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Empty_List) \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsection \<open>Optional\<close>

definition \<phi>Optional :: \<open>('c,'x) \<phi> \<Rightarrow> bool \<Rightarrow> ('c::one,'x) \<phi>\<close> (infix "?\<^sub>\<phi>" 55)
  where \<open>(T ?\<^sub>\<phi> C) = (\<lambda>x. if C then (x \<Ztypecolon> T) else 1)\<close>

lemma \<phi>Optional_expn[\<phi>expns]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> C) = (if C then x \<Ztypecolon> T else 1)\<close>
  unfolding \<phi>Type_def \<phi>Optional_def by simp

lemma \<phi>Optional_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T ?\<^sub>\<phi> C) \<Longrightarrow> ((C \<Longrightarrow> Inhabited (x \<Ztypecolon> T)) \<Longrightarrow> Z) \<Longrightarrow> Z\<close>
  unfolding Inhabited_def by (cases C; clarsimp simp add: \<phi>expns)

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> True) = (x \<Ztypecolon> T)\<close>
  unfolding set_eq_iff by (simp add: \<phi>Optional_expn)

lemma [simp]:
  \<open>(x \<Ztypecolon> T ?\<^sub>\<phi> False) = 1\<close>
  unfolding set_eq_iff by (simp add: \<phi>Optional_expn)


subsection \<open>Stepwise Abstraction\<close>

definition \<phi>Composition :: \<open>('v,'a) \<phi> \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> ('v,'b) \<phi>\<close> (infixl "\<Zcomp>" 75)
  where \<open>\<phi>Composition T U = (\<lambda>x. (y \<Ztypecolon> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j y. y \<in> U x))\<close>

lemma \<phi>Composition_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T \<Zcomp> U) \<longleftrightarrow> (\<exists>y. p \<in> (y \<Ztypecolon> T) \<and> y \<in> (x \<Ztypecolon> U))\<close>
  unfolding \<phi>Composition_def \<phi>Type_def by (simp add: \<phi>expns)

lemma \<phi>Composition_inhabited[elim,\<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> T \<Zcomp> U) \<Longrightarrow> (\<And>y. Inhabited (x \<Ztypecolon> U) \<Longrightarrow> Inhabited (y \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast



subsection \<open>Refinement\<close>

definition NuRefine :: " ('a, 'b) \<phi> \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) \<phi> " (infixl "<where>" 80)
  where "(N <where> T) x = {p. (x \<in> T \<and>p \<in> (x \<Ztypecolon> N))}"

lemma NuRefine_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <where> P) \<longleftrightarrow> x \<in> P \<and> p \<in> (x \<Ztypecolon> N)"
  unfolding NuRefine_def \<phi>Type_def by simp

lemma NuRefine_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> N <where> P) \<Longrightarrow> (x \<in> P \<Longrightarrow> Inhabited (x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  " x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> M' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x' \<in> S
\<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> M' <where> S \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 30 for \<open>?x \<Ztypecolon> ?T <where> ?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P''\<close>, \<phi>overload D]:
  "x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
    \<Longrightarrow> x \<Ztypecolon> T <where> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<and> x \<in> S"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma refine_\<phi>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> (N <where> P)"
  unfolding Imply_def by (simp add: \<phi>expns)


subsection \<open>Forward Simulation\<close>

definition \<phi>F_simulation :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> (('av \<times> 'bv) set, ('a \<times> 'b) set) \<phi>\<close> (infixr "\<Rrightarrow>\<^sub>r" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow>\<^sub>r U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>u y. (v,u) \<in> g \<and> (x,y) \<in> f \<and> u \<in> (y \<Ztypecolon> U)) })\<close>


subsection \<open>Mapping\<close>

definition \<phi>Mapping :: \<open>('av,'a) \<phi> \<Rightarrow> ('bv,'b) \<phi> \<Rightarrow> ('av \<Rightarrow> 'bv, 'a \<Rightarrow> 'b) \<phi>\<close> (infixr "\<Rrightarrow>" 25)
    \<comment> \<open>Forward Simulation\<close>
  where \<open>(T \<Rrightarrow> U) = (\<lambda>f. { g. \<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U) })\<close>

lemma \<phi>Mapping_expn[\<phi>expns]:
  \<open>g \<in> (f \<Ztypecolon> T \<Rrightarrow> U) \<longleftrightarrow> (\<forall>v x. v \<in> (x \<Ztypecolon> T) \<longrightarrow> g v \<in> (f x \<Ztypecolon> U))\<close>
  unfolding \<phi>Mapping_def \<phi>Type_def by simp

lemma \<phi>Mapping_inhabited[\<phi>expns]:
  \<open>Inhabited (f \<Ztypecolon> T \<Rrightarrow> U) \<Longrightarrow> ((\<And>x. Inhabited (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (f x \<Ztypecolon> U)) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

subsection \<open>Point on a Mapping\<close>

subsubsection \<open>By Key\<close>

definition \<phi>MapAt :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>" 60)
  where \<open>\<phi>MapAt key T x = { 1(key := v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>MapAt_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> key \<^bold>\<rightarrow> T) \<longleftrightarrow> (\<exists>v. p = 1(key := v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>MapAt_def \<phi>Type_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> field \<^bold>\<rightarrow> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Conversions\<close>

lemma \<phi>MapAt_\<phi>Prod:
  \<open>k \<^bold>\<rightarrow> (T \<^emph> U) = (k \<^bold>\<rightarrow> T) \<^emph> (k \<^bold>\<rightarrow> U)\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1))
  by (metis fun_1upd_homo_right1)

lemma \<phi>MapAt_\<phi>None:
  \<open>k \<^bold>\<rightarrow> \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> ?k \<^bold>\<rightarrow> \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> k \<^bold>\<rightarrow> \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s () \<Ztypecolon> \<circle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def
  by (simp add: implies_refl \<phi>MapAt_\<phi>None)

lemma \<phi>MapAt_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> k \<^bold>\<rightarrow> T) = (x' \<Ztypecolon> k \<^bold>\<rightarrow> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>MapAt_simp_cong ("(x \<Ztypecolon> k \<^bold>\<rightarrow> T)") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>MapAt_simp_cong} ctxt)
\<close>

paragraph \<open>Implication \& Action rules\<close>

lemma \<phi>MapAt_cast[\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> k \<^bold>\<rightarrow> U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> ?k \<^bold>\<rightarrow> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{structural, implication} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> k \<^bold>\<rightarrow> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act \<close>
  for Act :: \<open>'a::{structural, implication} action\<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow> ExTyp T) = (\<exists>\<phi> c. k \<^bold>\<rightarrow> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (k \<^bold>\<rightarrow> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)


subsubsection \<open>By List of Keys\<close>

definition \<phi>MapAt_L :: \<open>'key list \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>@" 60)
  where \<open>\<phi>MapAt_L key T x = { push_map key v |v. v \<in> (x \<Ztypecolon> T) }\<close>

abbreviation \<phi>MapAt_L1 :: \<open>'key \<Rightarrow> ('key list \<Rightarrow> 'v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>#" 60)
  where \<open>\<phi>MapAt_L1 key \<equiv> \<phi>MapAt_L [key]\<close>

abbreviation \<phi>MapAt_Lnil :: \<open>'key \<Rightarrow> ('v::one, 'x) \<phi> \<Rightarrow> ('key list \<Rightarrow> 'v, 'x) \<phi>\<close> (infixr "\<^bold>\<rightarrow>\<^sub>[\<^sub>]" 60)
  where \<open>\<phi>MapAt_Lnil key T \<equiv> \<phi>MapAt_L [key] (\<phi>MapAt [] T)\<close>

lemma \<phi>MapAt_L_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) \<longleftrightarrow> (\<exists>v. p = push_map k v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>MapAt_L_def by simp

lemma \<phi>MapAt_L_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Conversion\<close>

lemma \<phi>MapAt_L_\<phi>Prod:
  \<open>k \<^bold>\<rightarrow>\<^sub>@ (T \<^emph> U) = (k \<^bold>\<rightarrow>\<^sub>@ T) \<^emph> (k \<^bold>\<rightarrow>\<^sub>@ U)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule)
  apply (clarsimp simp add: push_map_distrib_sep_mult[symmetric])
  using push_map_sep_disj apply blast
  apply (clarsimp simp add: push_map_distrib_sep_mult)
  by blast

lemma \<phi>MapAt_L_\<phi>MapAt:
  \<open>k1 \<^bold>\<rightarrow>\<^sub>@ k2 \<^bold>\<rightarrow> T = k1 @ k2 \<^bold>\<rightarrow> T\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; force)

lemma \<phi>MapAt_L_\<phi>MapAt_L:
  \<open>k1 \<^bold>\<rightarrow>\<^sub>@ k2 \<^bold>\<rightarrow>\<^sub>@ T = k1 @ k2 \<^bold>\<rightarrow>\<^sub>@ T\<close>
  apply (rule \<phi>Type_eqI; simp add: \<phi>expns)
  by (metis push_map_push_map)

lemma \<phi>MapAt_L_\<phi>None:
  \<open>k \<^bold>\<rightarrow>\<^sub>@ \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

lemma [\<phi>reason for \<open>?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub># \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub># \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s () \<Ztypecolon> \<circle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Action_Tag_def by (simp add: implies_refl \<phi>MapAt_L_\<phi>None)

lemma \<phi>MapAt_L_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) = (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>MapAt_L_simp_cong ("x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>MapAt_L_simp_cong} ctxt)
\<close>

lemma \<phi>MapAt_L_At:
  \<open>(ks \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) = (ks \<^bold>\<rightarrow> T)\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; metis append_self_conv push_map_unit)


paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>MapAt_L_cast[\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{structural, implication} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act \<close>
  for Act :: \<open>'a::{structural, implication} action\<close>
  unfolding Action_Tag_def
  using \<phi>MapAt_L_cast .

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow>\<^sub>@ ExTyp T) = (\<exists>\<phi> c. k \<^bold>\<rightarrow>\<^sub>@ T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(k \<^bold>\<rightarrow>\<^sub>@ (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (k \<^bold>\<rightarrow>\<^sub>@ T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

(* subsection \<open>Down Lifting\<close> (*depreciated*)

definition DownLift :: "('a, 'b) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<phi>" (infixl "<down-lift>" 80)
  where "DownLift N g x = (g x \<Ztypecolon> N)"

lemma DownLift_expn[simp]: " p \<in> (x \<Ztypecolon> N <down-lift> g) \<longleftrightarrow> p \<in> (g x \<Ztypecolon> N) "
  unfolding DownLift_def \<phi>Type_def by simp

lemma [elim!,\<phi>reason_elim!]:
  "Inhabited (x \<Ztypecolon> N <down-lift> g) \<Longrightarrow> (Inhabited (g x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

(* lemma [\<phi>cast_overload E]: " x \<Ztypecolon> N <down-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s g x \<Ztypecolon> N" unfolding Imply_def by simp *)
lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> x \<Ztypecolon> N <down-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> N" unfolding Imply_def by (simp add: \<phi>expns)

(* lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (g y = x) \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <down-lift> g"
  unfolding Intro_def Imply_def by (simp add: \<phi>expns) blast
lemma [\<phi>reason, \<phi>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <down-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s g y \<Ztypecolon> M"
  unfolding Dest_def Imply_def by (simp add: \<phi>expns) *)

lemma [\<phi>reason]: " x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y1 \<Ztypecolon> M \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <down-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns)
lemma "\<down>lift_\<phi>app": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> N <down-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns)



subsection \<open>Up Lifting\<close> (*depreciated*)

definition UpLift :: "('a, 'c) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<phi>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> p \<in> (y \<Ztypecolon> N))}"

lemma UpLift_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <up-lift> f) \<longleftrightarrow> (\<exists>y. (f y = x) \<and> p \<in> (y \<Ztypecolon> N))"
  unfolding UpLift_def \<phi>Type_def by auto

lemma UpLift_inhabited[elim,\<phi>reason_elim]:
  "Inhabited (x \<Ztypecolon> N <up-lift> f) \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> Inhabited (y \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma "\<up>lift_\<phi>app":
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <up-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns) blast
(* lemma [\<phi>overload D]: "x \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists> \<Ztypecolon> M) "
  unfolding Imply_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M <up-lift> g"
  unfolding Intro_def Imply_def by (simp add: \<phi>expns) blast *)

lemma [\<phi>reason 130]:
  "x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> M' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x' \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> M' <up-lift> g"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 20]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s N \<^bold>a\<^bold>n\<^bold>d P x)
\<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s N \<^bold>a\<^bold>n\<^bold>d (\<exists>x. y = g x \<and> P x)"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 150]:
  "(\<And> x. y = g x \<Longrightarrow> x \<Ztypecolon> M \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y' x \<Ztypecolon> M' x \<^bold>a\<^bold>n\<^bold>d P x)
    \<Longrightarrow> y \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*x. y' x \<Ztypecolon> M' x) \<^bold>a\<^bold>n\<^bold>d (\<exists>x. y = g x \<and> P x)"
  unfolding Imply_def by (simp add: \<phi>expns) blast

(* lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t y \<Ztypecolon> M <up-lift> g \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. (x \<Ztypecolon> M) \<and>\<^sup>s g x = y)"
  unfolding Dest_def Imply_def by (simp add: \<phi>expns) blast *)

lemma "x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f x \<Ztypecolon> N <up-lift> f" unfolding Imply_def by (simp add: \<phi>expns) blast
lemma "x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f x \<Ztypecolon> N <up-lift> f" unfolding Imply_def by (simp add: \<phi>expns) blast

(* lemma "\<phi>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<phi>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<phi>Equal_def by (auto 0 6) *)
*)

subsection \<open>Any\<close>

definition \<phi>Any :: \<open>('x, unit) \<phi>\<close>
  where \<open>\<phi>Any = (\<lambda>_. UNIV)\<close>

lemma \<phi>Any_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Any)\<close>
  unfolding \<phi>Any_def \<phi>Type_def by simp

lemma \<phi>Any_inhabited[\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Any) \<Longrightarrow> C \<Longrightarrow> C\<close>
  .

lemma \<phi>Any_cast [\<phi>reason 1200 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?x \<Ztypecolon> \<phi>Any \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<phi>Any\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

lemma (in \<phi>empty) \<phi>Any_vs [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?x \<Ztypecolon> \<phi>Any \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> x \<Ztypecolon> \<phi>Any\<close>
  by (simp add: View_Shift_by_Subtyp \<phi>Any_cast)
  

subsection \<open>Value\<close>

lemma Val_expn [\<phi>expns]:
  \<open>(x \<Ztypecolon> Val val T) = (1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j dest_sem_value val \<in> (x \<Ztypecolon> T))\<close>
  unfolding Val_def \<phi>Type_def by (simp add: \<phi>expns)

lemma Val_inhabited [\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Val val T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast


subsubsection \<open>Syntax to fetch the latest n-th Val\<close>

syntax "__get_val__" :: "logic \<Rightarrow> logic" ("V$_" [1000] 999)
consts "\<phi>__get_val" :: "nat \<Rightarrow> 'b"

parse_ast_translation \<open>let open Ast
fun parse_num (Constant \<^const_syntax>\<open>zero_class.zero\<close>) = Variable "0"
  | parse_num (Constant \<^const_syntax>\<open>one_class.one\<close>) = Variable "1"
  | parse_num (Appl [Constant \<^syntax_const>\<open>_Numeral\<close>, A])
      = parse_num A
  | parse_num (Appl [Constant "_constrain", A, B])
      = Appl [Constant "_constrain", parse_num A, B]
  | parse_num (Appl [Constant "_type_constraint_", x])
      = Appl [Constant "_type_constraint_", parse_num x]
  | parse_num (Constant X) = Variable X
  | parse_num X = X
in [(\<^syntax_const>\<open>__get_val__\<close>, (fn ctxt => fn [A] =>
  @{print} (Appl [Constant \<^const_syntax>\<open>\<phi>__get_val\<close>, parse_num (@{print} A)])
))] end\<close>


setup \<open>let open Ast PhiSyntax
  fun strip_constrain (Const ("_constrain", _) $ x $ _) = strip_constrain x
    | strip_constrain (Const ("_type_constraint_", _) $ x) = strip_constrain x
    | strip_constrain x = x

  fun name_of_Val (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ v $ _ ))
        = SOME v
    | name_of_Val _ = NONE

  fun get_val ctxt ind =
    let
      val values = Thm.prop_of (NuBasics.the_construction ctxt)
                  |> dest_CurrentConstruction |> #4
                  |> strip_separations
                  |> map_filter name_of_Val
    in if ind < length values
       then List.nth (values, ind)
       else error ("Refer a value that does not exists.")
    end

  fun has_get_val (Const (\<^const_name>\<open>\<phi>__get_val\<close>, _)) = true
    | has_get_val (A $ B) = has_get_val A orelse has_get_val B
    | has_get_val (Abs (_,_,X)) = has_get_val X
    | has_get_val _ = false
  fun map_get_val ctxt (Const (\<^const_name>\<open>\<phi>__get_val\<close>, _) $ X)
        = get_val ctxt (Value.parse_nat (Term.term_name (strip_constrain X)))
    | map_get_val ctxt (A $ B) = map_get_val ctxt A $ map_get_val ctxt B
    | map_get_val ctxt (Abs (name,ty,X)) = Abs (name,ty, map_get_val ctxt X)
    | map_get_val ctxt x = x
 in Context.theory_map (Syntax_Phases.term_check ~10 "\<phi>valiable" (fn ctxt =>
      map (fn x => if has_get_val x then map_get_val ctxt x else x)))
end\<close>

subsubsection \<open>Reasoning Rules\<close>

paragraph \<open>Implication\<close>

lemma Val_cast [\<phi>reason]:
  \<open> y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> y \<Ztypecolon> Val v U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> Val v T \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

paragraph \<open>Action\<close>

lemma [\<phi>reason 1200 for \<open>?y \<Ztypecolon> Val ?v ?U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{implication, structural} action)\<close>]:
  \<open> y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> y \<Ztypecolon> Val v U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> Val v T \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{implication, structural} action\<close>
  unfolding Action_Tag_def
  using Val_cast .

paragraph \<open>Simplification\<close>

lemma [\<phi>programming_simps]:
    \<open>Val raw (ExTyp T) = (\<exists>\<phi> c. Val raw (T c))\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)

lemma [\<phi>programming_simps]:
    \<open>Val raw (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (Val raw T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)


lemma \<phi>Val_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Val v T) = (x' \<Ztypecolon> Val v T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup Val_simp_cong ("x \<Ztypecolon> Val v T") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>Val_simp_cong} ctxt)
\<close>

subsubsection \<open>Application Methods for Subtyping\<close>

context \<phi>spec begin

lemma [\<phi>reason 2100 for \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Val_cast implies_left_prod by metis


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (?x' \<Ztypecolon> ?T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x' \<Ztypecolon> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Val_cast implies_left_prod by metis


subsubsection \<open>Synthesis\<close>

lemma [\<phi>reason 1200 for
  \<open>PROP Synthesis_Parse (?x \<Ztypecolon> (?T::?'a \<Rightarrow> 'VAL set)) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse (x \<Ztypecolon> T) (\<lambda>v. x \<Ztypecolon> Val v T)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200 for
  \<open>PROP Synthesis_Parse (?raw::?'a sem_value) (?X::?'ret \<Rightarrow> ('FIC_N,'FIC)assn)\<close>
]:
  \<open>PROP Synthesis_Parse raw (\<lambda>_. x \<Ztypecolon> Val raw T)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S1 \<longmapsto> ?S2\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> Val ?raw ?T  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> x \<Ztypecolon> Val raw T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> SYNTHESIS x \<Ztypecolon> Val raw T  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding GOAL_CTXT_def Action_Tag_def View_Shift_def Synthesis_def
  by blast

lemma [\<phi>reason 1500 for \<open>PROP Synthesis_by (?raw::?'a sem_value) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R1 \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> ?x \<Ztypecolon> Val ret ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R1 \<longmapsto> R2\<heavy_comma> x \<Ztypecolon> Val raw T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> PROP Synthesis_by raw (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c Return raw \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> x \<Ztypecolon> Val ret T \<rbrace>)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for raw :: \<open>'a sem_value\<close>
  unfolding Synthesis_by_def Action_Tag_def GOAL_CTXT_def
            \<phi>Procedure_def View_Shift_def Return_def det_lift_def
  by simp

end

subsubsection \<open>Auto unfolding for value list\<close>

lemma [simp]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv Empty_List) = (1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j USELESS (rawv = \<phi>V_nil))\<close>
  unfolding set_eq_iff USELESS_def
  by (cases rawv; simp add: \<phi>expns)

lemma [simp]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv (List_Item T)) = (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T \<^bold>s\<^bold>u\<^bold>b\<^bold>j USELESS (\<exists>v. rawv = \<phi>V_cons v \<phi>V_nil))\<close>
  unfolding set_eq_iff \<phi>V_cons_def USELESS_def
  apply (cases rawv; clarsimp simp add: \<phi>expns \<phi>V_tl_def \<phi>V_hd_def times_list_def; rule;
          clarsimp simp add: sem_value_All sem_value_exists)
  by blast+

lemma [simp]:
  \<open> [] \<notin> (\<exists>*x. x \<Ztypecolon> L)
\<Longrightarrow> ((\<exists>*x. x \<Ztypecolon> Val rawv (List_Item T \<^emph> L)) :: 'a::sep_algebra set)
      = ((\<exists>*x. x \<Ztypecolon> Val (\<phi>V_tl rawv) L) * (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T))\<close>
  unfolding set_eq_iff
  apply (cases rawv; clarsimp simp add: \<phi>expns \<phi>V_tl_def \<phi>V_hd_def times_list_def)
  by (metis (no_types, opaque_lifting) append_Cons append_Nil list.exhaust_sel list.sel(1) list.sel(2) list.sel(3))

lemma [simp]:
  \<open>[] \<notin> (\<exists>*x. x \<Ztypecolon> (List_Item T \<^emph> L))\<close>
  by (rule; clarsimp simp add: \<phi>expns times_list_def)

lemma [simp]:
  \<open>[] \<notin> (\<exists>*x. x \<Ztypecolon> List_Item T)\<close>
  by (rule; clarsimp simp add: \<phi>expns times_list_def)



subsection \<open>Semantic Type Tagging\<close>

paragraph \<open>Annotation for Single One\<close>

context \<phi>empty_sem begin

definition Of_Type :: \<open>('VAL,'a) \<phi> \<Rightarrow> 'TY \<Rightarrow> ('VAL,'a) \<phi>\<close> (infix "<of-type>" 23)
  where \<open>(T <of-type> TY) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> Well_Type TY)\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-type> TY) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> p \<in> Well_Type TY\<close>
  unfolding Of_Type_def \<phi>Type_def by (simp add: \<phi>expns)

lemma [\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-type> TY) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200 for \<open>\<phi>SemType (?x \<Ztypecolon> ?T <of-type> ?TY) ?TY'\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> T <of-type> TY) TY\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U <of-type> TY \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def \<phi>SemType_def by (simp add: \<phi>expns) blast


paragraph \<open>Annotation for a List\<close>

definition Of_Types :: \<open>('VAL list,'a) \<phi> \<Rightarrow> 'TY list \<Rightarrow> ('VAL list,'a) \<phi>\<close> (infix "<of-types>" 23)
  where \<open>(T <of-types> TYs) = (\<lambda>x. (x \<Ztypecolon> T) \<inter> {p. list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs})\<close>

lemma [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> T <of-types> TYs) \<longleftrightarrow> p \<in> (x \<Ztypecolon> T) \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) p TYs\<close>
  unfolding Of_Types_def \<phi>Type_def by (simp add: \<phi>expns)

lemma [\<phi>reason_elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> T <of-types> TYs) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C \<close>
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

end

subsection \<open>Share \& Option\<close>

subsubsection \<open>Definition of Properties\<close>

definition \<phi>Sep_Disj :: \<open>('a::sep_disj,'b1) \<phi> \<Rightarrow> ('a::sep_disj,'b2) \<phi> \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj T U \<longleftrightarrow> (\<forall>x y u v. u \<in> (x \<Ztypecolon> T) \<and> v \<in> (y \<Ztypecolon> U) \<longrightarrow> u ## v)\<close>

definition \<phi>Sep_Disj_Identical :: \<open>('a::share_semimodule_sep, 'b) \<phi> \<Rightarrow> bool\<close>
  where \<open>\<phi>Sep_Disj_Identical T
    \<longleftrightarrow> (\<forall>x u v. u \<in> (x \<Ztypecolon> T) \<and> v \<in> (x \<Ztypecolon> T) \<and> u ## v \<longrightarrow> u = v)
      \<and> (\<forall>x u. u \<in> (x \<Ztypecolon> T) \<longrightarrow> u ## u)\<close>


subsubsection \<open>Permission Transformer\<close>

definition \<phi>perm_transformer :: \<open>('a::sep_algebra \<Rightarrow> 'b::share_module_sep) \<Rightarrow> ('a,'x) \<phi> \<Rightarrow> ('b,'x) \<phi>\<close>
  where \<open>\<phi>perm_transformer \<psi> T = (\<lambda>x. { \<psi> v |v. v \<in> (x \<Ztypecolon> T) \<and> perm_transformer' \<psi>})\<close>

abbreviation (in perm_transformer) \<open>\<phi> \<equiv> \<phi>perm_transformer \<psi>\<close>

lemma \<phi>perm_transformer_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>perm_transformer \<psi> T)
    \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<in> (x \<Ztypecolon> T) \<and> perm_transformer' \<psi>)\<close>
  unfolding \<phi>perm_transformer_def \<phi>Type_def by (simp add: \<phi>expns)

lemma (in perm_transformer) [\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = \<psi> v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>perm_transformer_def \<phi>Type_def by (simp add: \<phi>expns)

lemma \<phi>perm_transformer_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>perm_transformer \<psi> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns; blast)

paragraph \<open>Implication\<close>

lemma \<phi>perm_transformer_cast[\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_transformer \<psi> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi>perm_transformer \<psi> U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns; blast)

paragraph \<open>Action\<close>

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?U \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{implication, structural} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> \<phi>perm_transformer \<psi> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi>perm_transformer \<psi> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{implication, structural} action\<close>
  unfolding Action_Tag_def using \<phi>perm_transformer_cast .

paragraph \<open>Simplification\<close>

lemma [simp]:
  \<open>(\<phi>perm_transformer \<psi> (ExTyp T)) = (\<exists>\<phi> c. \<phi>perm_transformer \<psi> (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi>perm_transformer \<psi> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (\<phi>perm_transformer \<psi> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>perm_transformer_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi>perm_transformer \<psi> T) = (x' \<Ztypecolon> \<phi>perm_transformer \<psi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>perm_transformer_simp_cong ("x \<Ztypecolon> \<phi>perm_transformer \<psi> T") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>perm_transformer_simp_cong} ctxt)
\<close>


lemma \<phi>perm_transformer_\<phi>None:
  \<open> perm_transformer' \<psi>
\<Longrightarrow> \<phi>perm_transformer \<psi> \<circle> = \<circle>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)
  by (metis inj_at_1_def perm_transformer'.axioms(5))

lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::simplification action)\<close>]:
  \<open>x \<Ztypecolon> \<phi>perm_transformer \<psi> \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> \<circle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::simplification action\<close>
  unfolding Imply_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  using inj_at_1_def perm_transformer'.axioms(5) by blast

lemma \<phi>perm_transformer_MapAt:
  \<open>\<phi>perm_transformer ((o) f) (k \<^bold>\<rightarrow> T) = (k \<^bold>\<rightarrow> \<phi>perm_transformer f T)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>perm_transformer_expns
            perm_transformer_pointwise_eq; rule; clarsimp)
  using inj_at_1.inj_at_1 perm_transformer'.axioms(5) apply fastforce
  by (metis fun_upd_comp inj_at_1.inj_at_1 perm_transformer'.axioms(5) perm_transformer_pointwise)


lemma \<phi>perm_transformer_MapAt_L:
  \<open>\<phi>perm_transformer ((o) f) (k \<^bold>\<rightarrow>\<^sub>@ T) = (k \<^bold>\<rightarrow>\<^sub>@ \<phi>perm_transformer ((o) f) T)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>perm_transformer_expns
            perm_transformer_pointwise_eq; rule; clarsimp)
  using homo_one.push_map_homo homo_sep_mult_def perm_transformer'.axioms(1) apply blast
  by (metis homo_one.push_map_homo homo_sep_mult_def perm_transformer'.axioms(1) push_map_sep_disj)


lemma \<phi>perm_transformer_Prod_imply:
  \<open>x \<Ztypecolon> \<phi>perm_transformer f (T \<^emph> U) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> (\<phi>perm_transformer f T) \<^emph> (\<phi>perm_transformer f U)\<close>
  unfolding Imply_def
  apply (cases x; clarsimp simp add: \<phi>expns \<phi>Sep_Disj_def)
  using homo_sep_disj_semi_def homo_sep_mult.homo_mult perm_transformer'_def by blast

lemma \<phi>perm_transformer_Prod:
  \<open> \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>perm_transformer f (T \<^emph> U) = (\<phi>perm_transformer f T) \<^emph> (\<phi>perm_transformer f U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns \<phi>Sep_Disj_def; rule; clarsimp)
  using homo_sep_disj_semi_def homo_sep_mult.homo_mult perm_transformer'_def apply blast
  by (metis homo_sep_mult.homo_mult perm_transformer'_def sep_disj_commute)


subsubsection \<open>Permission Annotation\<close>

definition \<phi>Share :: \<open>rat \<Rightarrow> ('v::share,'x) \<phi> \<Rightarrow> ('v, 'x) \<phi>\<close> (infixr "\<Znrres>" 60)
  where \<open>\<phi>Share n T = (\<lambda>x. { share n v |v. v \<in> (x \<Ztypecolon> T) \<and> 0 < n }) \<close>

lemma \<phi>Share_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> n \<Znrres> T) \<longleftrightarrow> (\<exists>v. p = share n v \<and> v \<in> (x \<Ztypecolon> T) \<and> 0 < n )\<close>
  unfolding \<phi>Share_def \<phi>Type_def by simp

lemma \<phi>Share_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> n \<Znrres> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> 0 < n \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Auxiliary Tag\<close>

definition half :: \<open>rat \<Rightarrow> rat\<close> where [iff]: \<open>half x = x\<close>

text \<open>Many read-only applicable rules require only non-zero permissions.
  It is reflected as arbitrary schematic variable in the rule, like
    \<^schematic_prop>\<open> x \<Ztypecolon> ?n \<Znrres> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Z\<close>.
  As arbitrary schematic variable, the reasoner may by mistake instantiate it to be the total
  permission. It is not the optimal, and it is better to only assign a half of the permission
    and to leave the remain half to be used potentially later.
  For example, if a rule requires twice the same resource,
    \<^schematic_prop>\<open> (x \<Ztypecolon> ?n \<Znrres> T) * (x \<Ztypecolon> ?m \<Znrres> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Z\<close>.
  The best solution is to assign ?n by a half of the current permission and then assign ?m
    the half of the remaining half.

  Unfortunately, the reasoner can hardly be configured to apply this conservative policy, because
  schematic variables have a semantics of accepting any instantiation and there are many short-cut
  reasoning rule trying to solve greedily a local problem by unification.

  An approach is, if a rule may request a same object by twice, add the tag \<^term>\<open>half\<close> on its
    permission to tell explicitly the reasoner to only assign it a half of the permission.
    \<^schematic_prop>\<open> (x \<Ztypecolon> half ?n \<Znrres> T) * (x \<Ztypecolon> half ?m \<Znrres> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Z\<close>.
\<close>


paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>Share_cast[\<phi>reason]:
  \<open> (x \<Ztypecolon> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (y \<Ztypecolon> U) \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (y \<Ztypecolon> n \<Znrres> U) \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?n \<Znrres> ?T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{structural,implication} action)\<close>]:
  \<open> (x \<Ztypecolon> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (y \<Ztypecolon> U) \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (y \<Ztypecolon> n \<Znrres> U) \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{structural,implication} action\<close>
  unfolding Action_Tag_def using \<phi>Share_cast .

paragraph \<open>Simplifications\<close>

lemma [simp]:
  \<open>(n \<Znrres> ExTyp T) = (\<exists>\<phi> c. n \<Znrres> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(n \<Znrres> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (n \<Znrres> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)


lemma \<phi>Share_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) = (x' \<Ztypecolon> n \<Znrres> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Share_simp_cong ("x \<Ztypecolon> n \<Znrres> T") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>Share_simp_cong} ctxt)
\<close>

subparagraph \<open>Structural Conversions\<close>

lemma \<phi>Share_1[simp]:
  \<open> (1 \<Znrres> T) = T \<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

lemma \<phi>Share_\<phi>Share[simp]:
  \<open> 0 < n \<and> 0 < m
\<Longrightarrow> n \<Znrres> m \<Znrres> T = n*m \<Znrres> T \<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)
  by (metis share_share_not0)

lemma \<phi>Share_share:
  \<open> 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) * (x \<Ztypecolon> m \<Znrres> T) = (x \<Ztypecolon> n+m \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns set_eq_iff; rule; clarsimp)
  using share_sep_left_distrib_0 apply blast
  subgoal for v
  apply (rule exI[where x=\<open>share n v\<close>], rule exI[where x=\<open>share m v\<close>], simp)
    by (metis share_sep_left_distrib_0) .

lemma \<phi>Share_\<phi>MapAt:
  \<open>n \<Znrres> k \<^bold>\<rightarrow> T = k \<^bold>\<rightarrow> n \<Znrres> T\<close>
  for T :: \<open>('a::share_one,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply blast
  by (metis share_fun_updt share_right_one)

lemma \<phi>Share_\<phi>MapAt_L:
  \<open>n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T = k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_one,'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule)
  apply (clarsimp simp add: share_push_map) apply blast
  apply (clarsimp simp add: share_push_map[symmetric]) by blast

lemma \<phi>Share_\<phi>Prod:
  \<open>n \<Znrres> (T \<^emph> U) = (n \<Znrres> T) \<^emph> (n \<Znrres> U)\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis share_sep_disj_left share_sep_disj_right share_sep_right_distrib_0)
  using share_sep_right_distrib_0 by blast

lemma \<phi>Share_\<phi>None:
  \<open>0 < n \<Longrightarrow> n \<Znrres> \<circle> = (\<circle> :: ('a::share_one,unit) \<phi>)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1500 for \<open>?x \<Ztypecolon> ?n \<Znrres> \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'b::simplification action)\<close>]:
  \<open>x \<Ztypecolon> n \<Znrres> \<circle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'b::simplification action\<close>
  unfolding Imply_def Action_Tag_def
  by (simp add: \<phi>expns)

subparagraph \<open>Permission\<close>

lemma share_split_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> (x \<Ztypecolon> n+m \<Znrres> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (x \<Ztypecolon> n \<Znrres> T) * (x \<Ztypecolon> m \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share implies_refl Premise_def)

lemma share_merge_\<phi>app:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> T) * (x \<Ztypecolon> m \<Znrres> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (x \<Ztypecolon> n+m \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  by (simp add: \<phi>Share_share implies_refl Premise_def)


subsubsection \<open>\<phi>-Some\<close>

definition \<phi>Some :: \<open>('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<black_circle> _" [91] 90)
  where \<open>\<phi>Some T = (\<lambda>x. { Some v |v. v \<in> (x \<Ztypecolon> T) })\<close>

abbreviation \<phi>Share_Some ("\<fish_eye> _" [91] 90)
  where \<open>\<phi>Share_Some T \<equiv> \<phi>perm_transformer to_share (\<phi>Some T)\<close>

abbreviation \<phi>Share_Some_L ("\<fish_eye>\<^sub>L _" [91] 90)
  where \<open>\<phi>Share_Some_L T \<equiv> [] \<^bold>\<rightarrow> \<phi>perm_transformer to_share (\<phi>Some T)\<close>

lemma \<phi>Some_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Some T) \<longleftrightarrow> (\<exists>v. p = Some v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>Some_def by simp

lemma \<phi>Some_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Some T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Implication \& Action Rules\<close>

lemma \<phi>Some_cast[\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<black_circle> U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> \<black_circle> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{implication,structural} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<black_circle> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{implication,structural} action\<close>
  unfolding Action_Tag_def using \<phi>Some_cast .

lemma [simp]:
  \<open>(\<black_circle> ExTyp T) = (\<exists>\<phi> c. \<black_circle> T c)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<black_circle> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (\<black_circle> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>Some_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<black_circle> T) = (x' \<Ztypecolon> \<black_circle> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>Some_simp_cong ("x \<Ztypecolon> \<black_circle> T") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>Some_simp_cong} ctxt)
\<close>


subsubsection \<open>\<phi>Sep_Disj\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj X Y
\<Longrightarrow> \<phi>Sep_Disj X (m \<Znrres> Y)\<close>
  for X :: \<open>('a::share_sep_disj,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj Y X
\<Longrightarrow> \<phi>Sep_Disj (m \<Znrres> Y) X\<close>
  for X :: \<open>('a::share_sep_disj,'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj X \<phi>None\<close>
  for X :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj \<phi>None X\<close>
  for X :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k1 \<noteq> k2
||| \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>Sep_Disj (k1 \<^bold>\<rightarrow> T) (k2 \<^bold>\<rightarrow> U)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def Branch_imp
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)+

lemma [\<phi>reason 1200]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k1 \<noteq> k2
||| \<phi>Sep_Disj T U
\<Longrightarrow> \<phi>Sep_Disj (k1 \<^bold>\<rightarrow>\<^sub># T) (k2 \<^bold>\<rightarrow>\<^sub># U)\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def Branch_imp
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def push_map_def)+


lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj X A
\<Longrightarrow> \<phi>Sep_Disj X B
\<Longrightarrow> \<phi>Sep_Disj X (A \<^emph> B) \<close>
  for X :: \<open>('a::sep_disj_intuitive, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)

lemma [\<phi>reason 1300]:
  \<open> \<phi>Sep_Disj X Z
\<Longrightarrow> \<phi>Sep_Disj Y Z
\<Longrightarrow> \<phi>Sep_Disj (X \<^emph> Y) Z \<close>
  for X :: \<open>('a::sep_disj_intuitive, 'b) \<phi>\<close>
  unfolding \<phi>Sep_Disj_def
  by (clarsimp simp add: \<phi>expns sep_disj_fun_def)


subsubsection \<open>\<phi>Sep_Disj_Identical\<close>

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical (n \<Znrres> T)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Identical_\<phi>MapAt[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical (k \<^bold>\<rightarrow> T)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  by force

lemma \<phi>Sep_Disj_Identical_\<phi>MapAt_L[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical (k \<^bold>\<rightarrow>\<^sub>@ T)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  using push_map_sep_disj by blast

lemma \<phi>Sep_Disj_Identical_Prod[\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<phi>Sep_Disj_Identical U
\<Longrightarrow> \<phi>Sep_Disj_Identical (T \<^emph> U)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis self_disj_I sep_disj_commute sep_disj_multD2 sep_mult_commute)


lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>perm_transformer f T)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_transformer ((o) f) (k \<^bold>\<rightarrow> T)) \<close>
  by (subst \<phi>perm_transformer_MapAt; rule \<phi>Sep_Disj_Identical_\<phi>MapAt)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>perm_transformer ((o) f) T)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_transformer ((o) f) (k \<^bold>\<rightarrow>\<^sub>@ T)) \<close>
  by (subst \<phi>perm_transformer_MapAt_L; rule \<phi>Sep_Disj_Identical_\<phi>MapAt_L)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>perm_transformer f T)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_transformer f U)
\<Longrightarrow> \<phi>Sep_Disj_Identical (\<phi>perm_transformer f (T \<^emph> U)) \<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (smt (verit) Imply_def \<phi>Sep_Disj_Identical_Prod \<phi>Sep_Disj_Identical_def \<phi>perm_transformer_Prod_imply)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Identical (\<phi>perm_transformer to_share (\<phi>Some T))\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Sep_Disj_Identical (\<phi>perm_transformer to_share \<phi>None)\<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Sep_Disj_Identical (\<phi>None :: ('a::share_module_sep,unit) \<phi>) \<close>
  unfolding \<phi>Sep_Disj_Identical_def
  by (clarsimp simp add: \<phi>expns)


subsection \<open>Agreement\<close>

definition Agreement :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T agree option, 'x) \<phi>\<close>
  where \<open>Agreement T x = { Some (agree v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma Agreement_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Agreement T) \<longleftrightarrow> (\<exists>v. p = Some (agree v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Agreement_def by simp

lemma Agreement_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Agreement T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Agreement_times:
  \<open>(w \<Ztypecolon> Agreement W) * (x \<Ztypecolon> Agreement T) = ((w,x) \<Ztypecolon> Agreement (W \<inter>\<^sub>\<phi> T))\<close>
  unfolding set_eq_iff
  apply (clarsimp simp add: \<phi>expns; rule; clarsimp)
  subgoal for v
    by (rule exI[where x=\<open>Some (agree v)\<close>]; rule exI[where x=\<open>Some (agree v)\<close>]; simp) .

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>Agreement (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (Agreement T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>Agreement (ExTyp T) = (\<exists>\<phi>c. Agreement (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

paragraph \<open>Rule\<close>

lemma Agreement_cast[\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> Agreement T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> Agreement U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns)

lemma Agreement_dup[
  \<phi>reason 1200 for \<open>?x \<Ztypecolon> Agreement ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?U \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_dup\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>?x \<Ztypecolon> Agreement ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<^bold>a\<^bold>n\<^bold>d ?P\<close>
]:
  \<open> x \<Ztypecolon> Agreement T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_dup\<close>
  unfolding Imply_def Action_Tag_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for v by (rule exI[where x=\<open>Some (agree v)\<close>]; rule exI[where x=\<open>Some (agree v)\<close>]; simp) .

lemma Agreement_shrink[
  \<phi>reason 1200 for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?U \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_shrink\<close>,
  unfolded Action_Tag_def,
  \<phi>reason for \<open>(?x \<Ztypecolon> Agreement ?T) * (?x \<Ztypecolon> Agreement ?T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?x \<Ztypecolon> Agreement ?T \<^bold>a\<^bold>n\<^bold>d ?P\<close>
]:
  \<open> (x \<Ztypecolon> Agreement T) * (x \<Ztypecolon> Agreement T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> Agreement T \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> action_shrink \<close>
  unfolding Imply_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)
  

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> Agreement ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?U \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{structural, implication} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> Agreement T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> Agreement U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{structural, implication} action\<close>
  unfolding Action_Tag_def using Agreement_cast .

subsection \<open>Nonsepable\<close>

definition Nonsepable :: \<open>('T, 'x) \<phi> \<Rightarrow> ('T nonsepable, 'x) \<phi>\<close>
  where \<open>Nonsepable T x = nonsepable ` (x \<Ztypecolon> T)\<close>

lemma Nonsepable_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Nonsepable T) \<longleftrightarrow> (\<exists>v. p = nonsepable v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def Nonsepable_def by blast

lemma Nonsepable_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> Nonsepable T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>Nonsepable (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (Nonsepable T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>Nonsepable (ExTyp T) = (\<exists>\<phi>c. Nonsepable (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)


paragraph \<open>Rule\<close>

lemma Nonsepable_cast[\<phi>reason]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> Nonsepable T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> Nonsepable U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> Nonsepable ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?U \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'a::{structural, implication} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> Nonsepable T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> Nonsepable U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{structural, implication} action\<close>
  unfolding Action_Tag_def using Nonsepable_cast .

subsubsection \<open>Initialized or Not\<close>

paragraph \<open>Algebra to represent uninitialized data\<close>

datatype 'V uninit = initialized 'V | uninitialized

instantiation uninit :: (nonsepable_semigroup) nonsepable_semigroup begin
definition \<open>sep_disj_uninit (x::'a uninit) (y::'a uninit) \<longleftrightarrow> False\<close>
instance apply standard unfolding sep_disj_uninit_def by simp_all
end

paragraph \<open>Definition\<close>

text \<open>\<phi>Init T relates a value with T if the value is initialized; or if not, it relates the zero
  value of that type with T.\<close>

context \<phi>empty_sem begin

definition \<phi>Init :: \<open>'TY \<Rightarrow> ('VAL, 'x) \<phi> \<Rightarrow> ('VAL uninit, 'x) \<phi>\<close>
  where \<open>\<phi>Init TY T x = ({uninitialized} \<^bold>s\<^bold>u\<^bold>b\<^bold>j (\<exists>z. Zero TY = Some z \<and> z \<in> (x \<Ztypecolon> T))) + initialized ` (x \<Ztypecolon> T <of-type> TY)\<close>

abbreviation \<phi>Share_Some_Init ("\<fish_eye>\<lbrakk>_\<rbrakk> _" [0, 91] 90)
  where \<open>\<phi>Share_Some_Init TY T \<equiv> \<fish_eye> \<phi>Init TY T\<close>

lemma \<phi>Inited_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Init TY T) \<longleftrightarrow> (p = uninitialized \<and> (\<exists>z. Zero TY = Some z \<and> z \<in> (x \<Ztypecolon> T)) \<or> (\<exists>v. p = initialized v \<and> v \<in> (x \<Ztypecolon> T <of-type> TY)))\<close>
  unfolding \<phi>Type_def \<phi>Init_def by (simp add: \<phi>expns, blast)
  
lemma \<phi>Inited_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Init TY T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

paragraph \<open>Conversions\<close>

lemma [simp]:
  \<open>\<phi>Init TY (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (\<phi>Init TY T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>\<phi>Init TY (ExTyp T) = (\<exists>\<phi> c. \<phi>Init TY (T c))\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns; blast)

paragraph \<open>Rules\<close>

lemma \<phi>Init_cast[\<phi>reason for \<open>?x \<Ztypecolon> \<phi>Init ?TY ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> \<phi>Init ?TY' ?U \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> \<phi>Init TY T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi>Init TY U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns; rule; clarsimp)

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> \<phi>Init ?TY ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?U \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'aa::{implication,structural} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> \<phi>Init TY T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi>Init TY U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'a::{implication,structural} action\<close>
  unfolding Action_Tag_def using \<phi>Init_cast .

end

definition \<phi>Uninit :: \<open>('v uninit, unit) \<phi>\<close>
  where \<open>\<phi>Uninit x = {uninitialized}\<close>

lemma \<phi>Uninit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Uninit) \<longleftrightarrow> p = uninitialized\<close>
  unfolding \<phi>Type_def \<phi>Uninit_def by simp

lemma \<phi>Uninit_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Uninit) \<Longrightarrow> C \<Longrightarrow> C\<close> .


subsection \<open>Black Hole\<close>

text \<open>Essentially, the system is a Classical Separation Logic.
  For some situation like garbage collection, Intuitionistic Separation Logic can be more convenient.
  Therefore, we employ a `Black Hole' which can contain arbitrary resources to simulate the
    Intuitionistic Separation Logic\<close>

abbreviation (in \<phi>spec) Black_Hole :: \<open>('FIC_N \<Rightarrow> 'FIC) set\<close>
  where \<open>Black_Hole \<equiv> UNIV\<close>

lemma UNIV_subty [\<phi>reason for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s UNIV \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s UNIV\<close>
  unfolding Imply_def by simp

lemma (in \<phi>spec) UNIV_view_shift [\<phi>reason for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> UNIV \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> UNIV\<close>
  using UNIV_subty View_Shift_by_Subtyp by blast


subsection \<open>Misc.\<close>

definition Function_over :: \<open>('a,'b) \<phi> \<Rightarrow> 'c \<Rightarrow> ('a, 'c \<Rightarrow> 'b) \<phi>\<close> (infix "<func-over>" 40)
  where \<open>(T <func-over> x) = (\<lambda>f. f x \<Ztypecolon> T)\<close>

text \<open>
  \<^term>\<open>f \<Ztypecolon> T <func-over> x\<close> constrains f is a function about x,
    i.e. \<^prop>\<open>f \<Ztypecolon> T <func-over> x \<equiv> f x \<Ztypecolon> T\<close>.
  It is useful to circumvent nondeterminacy in the higher-order unification between
    \<^schematic_term>\<open>?f x \<Ztypecolon> T\<close> and \<^term>\<open>g x \<Ztypecolon> T\<close> which has multiple solutions
    including \<^term>\<open>f = g\<close> or \<^term>\<open>f = (\<lambda>_. g x)\<close>.
  Concerning this, \<^term>\<open>f \<Ztypecolon> T <func-over> x\<close> clarifies the ambiguity by a specialized reasoner
    that forces the exhaustive solution, i.e., the residue of \<^schematic_term>\<open>?f\<close> contains no
    free occurrence of \<^term>\<open>x\<close>.

  This specialized reasoner is \<^term>\<open>lambda_abstraction x fx f\<close> as,

\<^prop>\<open> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s fx \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f \<Ztypecolon> T <func-over> x \<^bold>a\<^bold>n\<^bold>d P\<close>

  which does the lambda abstraction, \<open>f = \<lambda>x. fx\<close>.
\<close>

lemma Function_over_expn[\<phi>expns]:
  \<open>(f \<Ztypecolon> T <func-over> x) = (f x \<Ztypecolon> T)\<close>
  unfolding Function_over_def \<phi>Type_def by simp

lemma Function_over_case_named[simp]:
  \<open>(case_named f \<Ztypecolon> T <func-over> tag x) = (f \<Ztypecolon> T <func-over> x)\<close>
  by (simp add: \<phi>expns)

lemmas [unfolded atomize_eq[symmetric], named_expansion] = Function_over_case_named

lemma [\<phi>reason 2000]:
  \<open> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s fx \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s f \<Ztypecolon> T <func-over> x \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def lambda_abstraction_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> f x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> f \<Ztypecolon> T <func-over> x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

context \<phi>spec begin

lemma [\<phi>reason 2000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> fx \<Ztypecolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> f \<Ztypecolon> T <func-over> x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w f x \<Ztypecolon> T \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w f \<Ztypecolon> T <func-over> x \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding lambda_abstraction_def by (simp add: \<phi>expns)


lemma [\<phi>reason 1200 for
  \<open>PROP Synthesis_Parse ?input (\<lambda>v. ?f \<Ztypecolon> ?T v <func-over> ?x :: ('FIC_N,'FIC)assn)\<close>
]:
  \<open> PROP Synthesis_Parse input (\<lambda>v. fx \<Ztypecolon> T v)
\<Longrightarrow> lambda_abstraction x fx f
\<Longrightarrow> PROP Synthesis_Parse input (\<lambda>v. f \<Ztypecolon> T v <func-over> x :: ('FIC_N,'FIC)assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> SYNTHESIS f x \<Ztypecolon> T v \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R1 \<longmapsto> \<lambda>v. R2\<heavy_comma> SYNTHESIS f \<Ztypecolon> T v <func-over> x \<rbrace>  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L P\<close>
  unfolding Synthesis_def lambda_abstraction_def by (simp add: \<phi>expns)

end


section \<open>Reasoning \& Programming\<close>



(*subsubsection \<open>Syntax & Auxiliary\<close>

definition "addr_allocated heap addr \<longleftrightarrow> MemAddress addr \<in> dom heap"
adhoc_overloading allocated addr_allocated

(* lemma addr_allocated_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> addr_allocated h addr \<Longrightarrow> addr_allocated h' addr"
  unfolding addr_allocated_def by auto
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto *)
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto

definition MemAddrState :: "heap \<Rightarrow> nat memaddr \<Rightarrow> 'b::lrep set \<Rightarrow> bool"
  where "MemAddrState h addr S \<longleftrightarrow> addr_allocated h addr \<and> shallowize (the (h (MemAddress addr))) \<in> S"
adhoc_overloading ResourceState MemAddrState

(*lemma MemAddrState_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> MemAddrState h' addr S"
  unfolding MemAddrState_def addr_allocated_def by auto (metis \<phi>set_mono domI map_le_def option.sel) *)

lemma MemAddrState_I_neq[intro]: "k2 \<noteq> k \<Longrightarrow> MemAddrState h k2 S \<Longrightarrow> MemAddrState (h(MemAddress k := v)) k2 S"
  and MemAddrState_I_eq[intro]: "v' \<in> S \<Longrightarrow> MemAddrState (h(MemAddress k \<mapsto> deepize v')) k S"
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_E[elim]:
  "MemAddrState h addr S \<Longrightarrow> (addr_allocated h addr \<Longrightarrow> Inhabited S \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding MemAddrState_def Inhabited_def by blast
lemma MemAddrState_I:
  "addr_allocated h addr \<Longrightarrow> shallowize (the (h (MemAddress addr))) \<in> S \<Longrightarrow> MemAddrState h addr S"
  unfolding MemAddrState_def by auto

(* lemma MemAddrState_retained_N[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<phi>Independent S claim
    \<Longrightarrow> Alive k \<in> claim \<Longrightarrow> MemAddrState (h(k:=None)) addr S"
  unfolding MemAddrState_def \<phi>Independent_def by auto
lemma MemAddrState_retained_S[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<phi>Independent S claim
    \<Longrightarrow> Write k \<in> claim \<Longrightarrow> MemAddrState (h(k \<mapsto> v)) addr S"
  unfolding MemAddrState_def \<phi>Independent_def by auto

*)


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<in> S \<Longrightarrow> h |` S \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<notin> S \<Longrightarrow> h |` (- S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)

*)

subsection \<open>General Rules \& Tools\<close>


(* subsubsection \<open>General Rules\<close>

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>VAL ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s VAL ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> VAL X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s VAL Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma (in \<phi>empty) [\<phi>reason 2000 on \<open>OBJ ?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ ?Y \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> OBJ X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s OBJ Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast) *)


subsubsection \<open>General Simplification for Assertions\<close>

\<phi>reasoner assertion_simplification 1200
  (conclusion \<open>Simplify assertion_simplification ?X' ?X\<close>)
  = ((simp only: assertion_simps)?, rule Simplify_I)

lemmas [assertion_simps] =
  mult_zero_right mult_zero_left mult_1_right mult_1_left add_0_right add_0_left zero_fun
  zero_fun_def[symmetric] plus_fun Subjection_Zero ExSet_const FOCUS_TAG_def ExSet_0



subsubsection \<open>Case Analysis\<close>


lemma [\<phi>reason 1200]: "Premise mode (A = B x y) \<Longrightarrow> Premise mode (A = case_prod B (x,y))" by simp
lemma [\<phi>reason 1200]: "Premise mode (A = B x) \<Longrightarrow> Premise mode (A = case_named B (tag x))" by simp
lemma [\<phi>reason 1200]: "Premise mode (A = B a x) \<Longrightarrow> Premise mode (A = case_object B (a \<Zinj> x))" by simp

definition CaseSplit :: "bool \<Rightarrow> bool" where "CaseSplit x = x"
lemma [elim!]: "CaseSplit x \<Longrightarrow> (x \<Longrightarrow> C) \<Longrightarrow> C" unfolding CaseSplit_def .

 lemma [elim!]:
  "y = case_prod f x \<Longrightarrow> (\<And>x1 x2. y = f x1 x2 \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of a \<Zinj> b \<Rightarrow> f a b) \<Longrightarrow> (\<And>a b. y = f a b \<Longrightarrow> C (a \<Zinj> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of tag a \<Rightarrow> f a) \<Longrightarrow> (\<And>a. y = f a \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp



subsubsection \<open>Same \<phi>-Type\<close>

definition SameNuTy :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " where "SameNuTy A B = True"
text \<open>Technical tag for reasoner converges \<phi>-types of two typings.\<close>

lemma [\<phi>reason 2000]: "SameNuTy (x \<Ztypecolon> T) (x' \<Ztypecolon> T) "
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy B B' \<Longrightarrow> SameNuTy (A * B) (A' * B')"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "(\<And>x. SameNuTy (A x) (A' x)) \<Longrightarrow> SameNuTy (ExSet A) (ExSet A')"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)"
  unfolding SameNuTy_def ..

lemma [\<phi>reason 1000]: "SameNuTy A A" \<comment> \<open>The fallback\<close>
  unfolding SameNuTy_def ..


subsection \<open>Process of Cleaning\<close>

definition \<r>Clean :: \<open>'a::one set \<Rightarrow> bool\<close> where \<open>\<r>Clean S \<longleftrightarrow> (S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1)\<close>

subsubsection \<open>Termination\<close>

lemma [\<phi>reason 3000]:
  \<open>\<r>Clean 1\<close>
  unfolding \<r>Clean_def Imply_def by simp

lemma [\<phi>reason 3000]:
  \<open>\<r>Clean (() \<Ztypecolon> \<phi>None)\<close>
  unfolding \<r>Clean_def Imply_def by simp

lemma [\<phi>reason 3000 for \<open>\<r>Clean (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C)\<close>]:
  \<open> \<r>Clean (x \<Ztypecolon> T ?\<^sub>\<phi> False) \<close>
  unfolding \<r>Clean_def Imply_def by simp

paragraph \<open>Structural Node\<close>

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean A
\<Longrightarrow> \<r>Clean B
\<Longrightarrow> \<r>Clean (A * B)\<close>
  for A :: \<open>'a::sep_magma_1 set\<close>
  unfolding \<r>Clean_def Imply_def
  apply (simp add: \<phi>expns)
  using mult_1_class.mult_1_left by blast

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (y \<Ztypecolon> U)
\<Longrightarrow> \<r>Clean ((x,y) \<Ztypecolon> T \<^emph> U)\<close>
  for T :: \<open>('a::sep_magma_1, 'b) \<phi>\<close>
  unfolding \<r>Clean_def \<phi>Prod_expn' Imply_def
  apply (simp add: \<phi>expns)
  using mult_1_class.mult_1_left by blast

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> k \<^bold>\<rightarrow> T)\<close>
  unfolding \<r>Clean_def Imply_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis fun_1upd1)

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T)\<close>
  unfolding \<r>Clean_def Imply_def
  apply (simp add: \<phi>expns)
  using push_map_1 by blast

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> n \<Znrres> T)\<close>
  for T :: \<open>('a::share_semimodule_mult, 'b) \<phi>\<close>
  unfolding \<r>Clean_def Imply_def apply (simp add: \<phi>expns)
  using share_right_one by blast


subsection \<open>Assertion Level View Shift Reasoning\<close>

text \<open>This is a decision procedure reasoning the entailment between assertions.
  It recognizes \<phi>-Types specifying the same object and reduce the goal of assertion entailment
    to subtyping problems of \<phi>-Types. \<close>

lemmas cast_def = GOAL_CTXT_def FOCUS_TAG_def Imply_def

(* lemma [\<phi>intro0]: "x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * y \<Ztypecolon> Y \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * y\<^sub>m \<Ztypecolon> Y \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> x \<Ztypecolon> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * \<blangle> y \<Ztypecolon> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * \<blangle> y\<^sub>m \<Ztypecolon> Y \<brangle> \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Heap_Subty_Goal_def . *)
(* lemma [\<phi>intro0]: "A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B" unfolding SubtyDual_def  by (simp add: implies_refl) *)

(* lemma [\<phi>intro 1000]:
  "L * H \<longmapsto> L * H \<^bold>d\<^bold>u\<^bold>a\<^bold>l L * h\<^sub>m \<Ztypecolon> \<blangle> H\<^sub>m \<brangle> \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s L * h\<^sub>m \<Ztypecolon> H\<^sub>m \<brangle>"
  unfolding Heap_Subty_Goal_def using cast_dual_id . *)

text \<open>Priority Convention:
\<^item> 4000: Termination
\<^item> 3000: Normalization
\<^item> 2000: The framework of step-by-step searching
\<^item> 2100: Prior rules for specific patterns in the step-by-step searching
\<^item> 2300: Termination of the step-by-step searching
\<^item> \<le> 1999: Rules for search specific object like value, variable, etc.
\<close>

context \<phi>spec begin

subsubsection \<open>Initialization\<close>

lemma [\<phi>reason 2000
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode\<close>
    except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?Y \<heavy_comma> \<blangle> ?YY \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode\<close>
]:
  \<open> Simplify assertion_simplification X' X
\<Longrightarrow> Simplify assertion_simplification Y' Y
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X' \<longmapsto> \<blangle> Y' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode\<close>
  unfolding Action_Tag_def Simplify_def FOCUS_TAG_def
  by simp

lemma [\<phi>reason 2100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?var_Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode\<close>
  unfolding Action_Tag_def using view_shift_id .


subsubsection \<open>Termination\<close>

lemma [\<phi>reason 4010 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?H2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
      "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> H \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  and [\<phi>reason 4010 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> ?R * \<blangle> ?H2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
      "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> 1 * \<blangle> H \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_left FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def
  using view_shift_id by this+

lemma [\<phi>reason 4000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<r>Clean H
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> Void \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding \<r>Clean_def FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def
  using \<phi>view_shift_by_implication .

lemma [\<phi>reason 4010 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> Void \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<r>Clean H
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> Void \<heavy_comma> \<blangle> Void \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding \<r>Clean_def FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def
  by (simp add: \<phi>view_shift_by_implication)

lemma [\<phi>reason 4000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> ?R \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> H \<heavy_comma> \<blangle> Void \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def
  by (simp add: \<phi>view_refl)

lemma [\<phi>reason 4011 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> ?R \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h (Automatic_Morphism ?RP ?RX \<and> ?P)
        \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> H \<heavy_comma> \<blangle> Void \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Automatic_Morphism True (\<^bold>v\<^bold>i\<^bold>e\<^bold>w H'\<heavy_comma> \<blangle> Void \<brangle> \<longmapsto> H' ) \<and> True
     \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding FOCUS_TAG_def GOAL_CTXT_def Morphism_def Action_Tag_def
  by (simp add: \<phi>view_refl)



subsubsection \<open>Void Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 2500 ]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<heavy_comma> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_right .

lemma [\<phi>reason 2500]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> Void \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_right .

subsubsection \<open>Pad Void Holes at left\<close> \<comment> \<open>to standardize\<close>

lemma [\<phi>reason 2500
 except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> (?X1 \<heavy_comma> ?X2) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?X1 + ?X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
        \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> 1 \<heavy_comma> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_left .

lemma [\<phi>reason 2500
   except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?Y1 \<heavy_comma> ?Y2 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?Y1 + ?Y2 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 1 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> ?X1 + ?X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> 1 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?H \<longmapsto> \<blangle> 0 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w 1 \<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult_1_left .

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 3000]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3000]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3000]:
  "(Q \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns) blast


subsubsection \<open>Existential\<close>

lemma [\<phi>reason 3000]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> U c \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> ExSet U \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def Action_Tag_def by (simp add: \<phi>expns, metis)

lemma [\<phi>reason 3000]:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w T x \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) \<Longrightarrow>
   \<^bold>v\<^bold>i\<^bold>e\<^bold>w ExSet T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding View_Shift_def GOAL_CTXT_def Action_Tag_def
  apply (simp add: \<phi>expns)
  by fastforce

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> VAL x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?var_X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
                       \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?var_Y \<longmapsto> 0 \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> 0 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp


lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
                       \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?var_Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> 0 \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> 0 \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0\<heavy_comma> ?R \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w 0\<heavy_comma> R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def zero_set_def Action_Tag_def by simp

lemma [\<phi>reason 3000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y + 0 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def Action_Tag_def by simp

lemma [\<phi>reason 3000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w 0 + Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding View_Shift_def by simp

subsubsection \<open>Divergence of Union\<close>

paragraph \<open>Divide Schematic Variable\<close>

definition \<open>ALSTR_Divide_Assertion_U X A B \<equiv> Trueprop (\<^bold>v\<^bold>i\<^bold>e\<^bold>w A + B \<longmapsto> X)\<close>

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (?var_Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U (A + B) A B\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_id) 

lemma [\<phi>reason for \<open>PROP ALSTR_Divide_Assertion_U (?Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U A A A\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_id)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (?ZR \<heavy_comma> ?Z1) ?A ?B\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U Z1 A1 B1
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U ZR AR BR
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (ZR \<heavy_comma> Z1) (AR \<heavy_comma> A1) (BR \<heavy_comma> B1)\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (smt (z3) INTERP_SPEC_plus View_Shift_def distrib_left mult.commute mult.left_commute plus_set_in_iff)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (0::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U 0 0 (0::('FIC_N,'FIC) assn)\<close>
  unfolding ALSTR_Divide_Assertion_U_def
  by (simp add: view_shift_0)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U (ExSet ?Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>(\<And>c. PROP ALSTR_Divide_Assertion_U (Z c) (A c) (B c))
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (ExSet Z) (ExSet A) (ExSet B)\<close>
  for A :: \<open>'c \<Rightarrow> ('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def Imply_def plus_set_def View_Shift_def
  apply (clarsimp simp add: \<phi>expns)
  by (smt (z3) Fic_Space_Un) 

lemma [\<phi>reason 1200
    for \<open>PROP ALSTR_Divide_Assertion_U (?Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P :: ('FIC_N,'FIC) assn) ?A ?B\<close>
]:
  \<open> PROP ALSTR_Divide_Assertion_U Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U (Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (B \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def plus_set_def View_Shift_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U \<blangle> ?Z \<brangle> ?A (?B::('FIC_N,'FIC) assn)\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U \<blangle> Z \<brangle>  \<blangle> A \<brangle>  \<blangle> B \<brangle>\<close>
  for A :: \<open>('FIC_N,'FIC) assn\<close>
  unfolding ALSTR_Divide_Assertion_U_def plus_set_def by (simp add: \<phi>expns)


paragraph \<open>Main Rules\<close>

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A + ?B \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U X XA XB
\<Longrightarrow> SUBGOAL G G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> XB \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> XA \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A + B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<or> P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding ALSTR_Divide_Assertion_U_def Action_Tag_def
  by (simp add: View_Shift_def distrib_left)

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> (?A + ?B) \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U X XA XB
\<Longrightarrow> SUBGOAL G G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> B \<longmapsto> XB \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> A \<longmapsto> XA \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> A + B \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<or> P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding ALSTR_Divide_Assertion_U_def Action_Tag_def
  by (simp add: View_Shift_def distrib_left)

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding plus_set_def Action_Tag_def apply simp
  by (metis plus_set_def view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding plus_set_def Action_Tag_def apply simp
  by (metis plus_set_def sup_commute view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding cast_def Action_Tag_def
  by (simp add: distrib_left view_shift_union(1))

lemma [\<phi>reason 800]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> R\<heavy_comma> \<blangle> A + B \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding cast_def Action_Tag_def
  by (simp add: distrib_left view_shift_union(2)) 

subsubsection \<open>Step-by-Step Searching Procedure\<close>

lemma [\<phi>reason 2000
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> \<blangle> ?R2 \<heavy_comma> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
 except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> \<blangle> ?R2 \<heavy_comma> FIX ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R  \<longmapsto> R1 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R1 \<longmapsto> \<blangle> R2 \<brangle>     \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R  \<longmapsto> \<blangle> R2 \<heavy_comma> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<and> P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Action_Tag_def
  by (metis View_Shift_imply_P \<phi>frame_view_right \<phi>view_trans)

lemma [\<phi>reason 2010 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?Y \<longmapsto> \<blangle> ?R2 \<heavy_comma> (FIX ?X) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> \<blangle> R2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> \<blangle> R2 \<heavy_comma> FIX X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<and> P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis \<phi>view_shift_intro_frame_R \<phi>view_shift_trans mult.commute)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?Y \<longmapsto> \<blangle> ?R2 \<heavy_comma> (FIX ?X) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> \<blangle> R2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> X \<longmapsto> \<blangle> R2 \<heavy_comma> FIX X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis \<phi>frame_view mult.commute)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> FIX ?Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> FIX Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Fix_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> ?R2 \<heavy_comma> \<blangle> SYNTHESIS ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> SYNTHESIS X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Synthesis_def .

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> SYNTHESIS ?Y \<longmapsto> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> SYNTHESIS Y \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2300 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?V \<longmapsto> ?R' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> X \<longmapsto> R \<heavy_comma> \<blangle> X \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
      \<comment> \<open>successful termination of the step-by-step search\<close>
  unfolding cast_def split_paired_All Action_Tag_def
  by (simp add: view_shift_id)

lemma [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> ?R2\<heavy_comma> \<blangle> SMORPH ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Automatic_Morphism RP RX \<and> P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R2 \<heavy_comma> \<blangle> SMORPH X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Automatic_Morphism RP RX \<and> P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding SMorphism_def .


subsubsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1215 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?y \<Ztypecolon> Val ?v ?U \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?x \<Ztypecolon> Val ?v' ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> y \<Ztypecolon> Val v U \<longmapsto> R \<heavy_comma> \<blangle> x \<Ztypecolon> Val v T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All View_Shift_def
  by (simp add: \<phi>expns times_list_def) metis

lemma [\<phi>reason 1210 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?y \<Ztypecolon> Val ?v ?U \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?x \<Ztypecolon> Val ?v' ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> x \<Ztypecolon> Val v T \<longmapsto> R \<heavy_comma> \<blangle> x \<Ztypecolon> Val v T \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All View_Shift_def Action_Tag_def
  by blast
  

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R\<heavy_comma> ?X \<longmapsto> ?R'''\<heavy_comma> \<blangle> ?x \<Ztypecolon> Val ?v ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R'\<heavy_comma> \<blangle> x \<Ztypecolon> Val v T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> X \<longmapsto> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> Val v T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Action_Tag_def
  by (smt (verit) \<phi>view_shift_intro_frame_R mult.assoc mult.commute)

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?x \<Ztypecolon> Val ?v ?V \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?x \<Ztypecolon> Val ?v ?V \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> x \<Ztypecolon> Val v V \<longmapsto> R' \<heavy_comma> x \<Ztypecolon> Val v V \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def Action_Tag_def
  by (smt (verit, best) \<phi>view_shift_intro_frame_R mult.assoc mult.commute)

lemma ToSA_skip
  [\<phi>reason 70 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' \<heavy_comma> \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> H \<longmapsto> R' \<heavy_comma> H \<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G "
  unfolding cast_def
  by (simp add: \<phi>view_shift_intro_frame mult.commute mult.left_commute)


(* 
We don't need general search any more, because every resource locale configures its reasoning rules.

subsubsection \<open>General Search\<close>

lemma [\<phi>reason 100 on \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w H \<longmapsto> H'\<heavy_comma> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> H \<longmapsto> R\<heavy_comma> H'\<heavy_comma> \<blangle> X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def
  by (simp add: \<phi>view_shift_intro_frame mult.assoc)

lemma [\<phi>reason 10 on \<open>?a \<Zinj> ?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R''' \<heavy_comma> ?a' \<Zinj> ?x' \<Ztypecolon> ?T' \<^bold>a\<^bold>n\<^bold>d ?P\<close>]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
   a \<Zinj> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s a' \<Zinj> x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow>
   a \<Zinj> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> a' \<Zinj> x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding cast_def split_paired_All by (simp add: \<phi>expns)

*)

(* lemma [\<phi>reason 1200
    on \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "CHK_SUBGOAL G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])
*)

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>

subsubsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> T1 \<heavy_comma> T2 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> (T1 \<heavy_comma> T2) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode\<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> X1 \<heavy_comma> X2 \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> \<blangle> R \<heavy_comma> (X1 \<heavy_comma> X2) \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding mult.assoc[symmetric] .

end


(*
subsubsection \<open>Other Reasoning Settings\<close>

lemma [\<phi>intro 14000]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a \<Zinj> x' " unfolding Premise_def by simp
(* lemma [\<phi>intro 13500]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a' \<Zinj> x' " unfolding Premise_def by simp *)

(*TODO: this rule is too aggressive. Maybe a assumption based flag switch?*)
lemma [\<phi>intro 13000]: "False \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<Zinj> x = a' \<Zinj> x' " unfolding Premise_def by simp
  \<comment> \<open>For any other situation (when a is not alpha equivalent to a'), reasoning is pruned early.
  The proof for \<^term>\<open>a = a'\<close> is always assigned to users, because maintaining the consistency of object identities
    is so essential that users should always keep.\<close>
*)

subsection \<open>Assertion Level Implication Reasoning\<close>

subsubsection \<open>Initialization\<close>

lemma [\<phi>reason 2000 except \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y * \<blangle> ?YX \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode\<close>]:
  \<open> Simplify assertion_simplification X' X
\<Longrightarrow> Simplify assertion_simplification Y' Y
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> X' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> Y' \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode\<close>
  unfolding Action_Tag_def Simplify_def FOCUS_TAG_def
  by simp

lemma [\<phi>reason 2100 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode\<close>]:
  \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode\<close>
  unfolding Action_Tag_def using implies_refl .

subsubsection \<open>Termination\<close>

lemma [\<phi>reason 4000 for \<open>?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?H2 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
      "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> H \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  and [\<phi>reason 4000 for \<open>?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R * \<blangle> ?H2 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
      "X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 * \<blangle> X \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def
  using implies_refl by this+

subsubsection \<open>Void Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 2500 ]:
  " H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
    H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> X * 1 \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 2500]:
  " R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
    R * 1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_right .

subsubsection \<open>Pad Void Holes at left\<close> \<comment> \<open>to standardize\<close>

lemma [\<phi>reason 2500
 except \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> (?X1 * ?X2) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
        \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?X1 + ?X2 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
        \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> 1 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> 1 * X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
    H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left .

lemma [\<phi>reason 2500
   except \<open> ?Y1 * ?Y2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open> ?Y1 + ?Y2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open> 1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?X1 + ?X2 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> 1 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
          \<open> ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> 0 \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " 1 * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
    Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left .

lemma [\<phi>reason 1050 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?Y \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
   except \<open>(?X'::?'a::sep_magma_1 set) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?Y' \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  \<comment> \<open>If it doesn't have one, it cannot be reasoned by this procedure, so
      a fallback here handles it.\<close>
  unfolding FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def .


subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 3000]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> U \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
    T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3000]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * U \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
    T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Imply_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3000]:
  "(Q \<Longrightarrow>  T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) \<Longrightarrow>
    T \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Imply_def by (simp add: \<phi>expns) blast


subsubsection \<open>Existential\<close>

lemma [\<phi>reason 3000]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> U c \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow>
    T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ExSet U \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Imply_def by (simp add: \<phi>expns, metis)

lemma [\<phi>reason 3000]:
  "(\<And>x.  T x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G) \<Longrightarrow>
    ExSet T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Imply_def GOAL_CTXT_def
  apply (simp add: \<phi>expns)
  by fastforce

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> VAL x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsubsection \<open>Zero\<close>

lemma [\<phi>reason 3100 for \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?var_X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
                        \<open> ?var_Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 0 \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s 0 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Imply_def zero_set_def by simp


lemma [\<phi>reason 3000 for \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
                        \<open> ?var_Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3000 for \<open> ?R * 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> R * 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3000 for \<open> 0 * ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> 0 * R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Imply_def zero_set_def by simp

lemma [\<phi>reason 3000]:
  \<open>  Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow>  Y + 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Imply_def by simp

lemma [\<phi>reason 3000]:
  \<open>  Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow>  0 + Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Imply_def by simp

subsubsection \<open>Divergence of Union\<close>

paragraph \<open>Divide Schematic Variable\<close>

definition \<open>ALSTR_Divide_Assertion_U_Imp X A B \<equiv> Trueprop ( A + B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X)\<close>

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?var_Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U_Imp (A + B) A B\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (simp add: implies_refl) 

lemma [\<phi>reason for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?Z::('FIC_N,'FIC) assn) ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U_Imp A A A\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (simp add: implies_refl)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?ZR * ?Z1) ?A ?B\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp Z1 A1 B1
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp ZR AR BR
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp (ZR * Z1) (AR * A1) (BR * B1)\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (smt (verit, del_insts) Imply_def plus_set_in_iff set_mult_expn)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp 0 ?A ?B\<close>]:
  \<open>PROP ALSTR_Divide_Assertion_U_Imp 0 0 0\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (simp add: zero_implies_any)

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp (ExSet ?Z) ?A ?B\<close>]:
  \<open>(\<And>c. PROP ALSTR_Divide_Assertion_U_Imp (Z c) (A c) (B c))
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp (ExSet Z) (ExSet A) (ExSet B)\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def Imply_def plus_set_def
  apply (clarsimp simp add: \<phi>expns)
  by (smt (z3) Fic_Space_Un) 

lemma [\<phi>reason 1200
    for \<open>PROP ALSTR_Divide_Assertion_U_Imp (?Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P) ?A ?B\<close>
]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp (Z \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (B \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def plus_set_def Imply_def
  by (simp add: \<phi>expns) 

lemma [\<phi>reason 1200 for \<open>PROP ALSTR_Divide_Assertion_U_Imp \<blangle> ?Z \<brangle> ?A ?B\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp Z A B
\<Longrightarrow> PROP ALSTR_Divide_Assertion_U_Imp \<blangle> Z \<brangle>  \<blangle> A \<brangle>  \<blangle> B \<brangle>\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def plus_set_def by (simp add: \<phi>expns)


paragraph \<open>Main Rules\<close>

lemma [\<phi>reason 3000 for \<open>?A + ?B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp X XA XB
\<Longrightarrow> SUBGOAL G G1
\<Longrightarrow> B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s XB \<^bold>a\<^bold>n\<^bold>d P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s XA \<^bold>a\<^bold>n\<^bold>d P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> A + B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1 \<or> P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  by (simp add: Imply_def distrib_left)

lemma [\<phi>reason 3000 for \<open>?R * (?A + ?B) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> PROP ALSTR_Divide_Assertion_U_Imp X XA XB
\<Longrightarrow> SUBGOAL G G1
\<Longrightarrow> R * B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s XB \<^bold>a\<^bold>n\<^bold>d P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> SOLVE_SUBGOAL G1
\<Longrightarrow> R * A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s XA \<^bold>a\<^bold>n\<^bold>d P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R * (A + B) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1 \<or> P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding ALSTR_Divide_Assertion_U_Imp_def
  apply (simp add: Imply_def distrib_left)
  by (metis plus_set_in_iff set_mult_expn)

lemma [\<phi>reason 800]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> A \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding plus_set_def apply simp
  by (metis implies_union(1) plus_set_def)

lemma [\<phi>reason 800]:
  \<open>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> B \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding plus_set_def
  by (simp add: Imply_def)

lemma [\<phi>reason 800]:
  \<open>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> A \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow>  X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding cast_def
  apply (simp add: distrib_left)
  by (metis plus_set_in_iff set_mult_expn)

lemma [\<phi>reason 800]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> B \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G1
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> A + B \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding cast_def
  apply (simp add: distrib_left)
  by (metis plus_set_in_iff set_mult_expn)


subsubsection \<open>Step-by-Step Searching Procedure\<close>

lemma [\<phi>reason 2000
    for \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
 except \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * (FIX ?X) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " R  \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R1 * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 \<brangle>     \<^bold>a\<^bold>n\<^bold>d P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R  \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 * X \<brangle> \<^bold>a\<^bold>n\<^bold>d P1 \<and> P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Action_Tag_def
  by (metis set_mult_expn)

lemma [\<phi>reason 2010 for \<open> ?R * ?Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * (FIX ?X) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P1
\<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 \<brangle> \<^bold>a\<^bold>n\<^bold>d P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 * (FIX X) \<brangle> \<^bold>a\<^bold>n\<^bold>d P1 \<and> P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis set_mult_expn)

lemma [\<phi>reason 2000 for \<open> ?R * ?Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> ?R2 * (FIX ?X) \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R2 * (FIX X) \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Fix_def Action_Tag_def
  by (metis set_mult_expn)

lemma [\<phi>reason 2000 for \<open>?R * (FIX ?Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " R * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R * (FIX Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Fix_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2000 for \<open> ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R2 * \<blangle> SYNTHESIS ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2 * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R2 * \<blangle> SYNTHESIS X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Synthesis_def .

lemma [\<phi>reason 2000 for \<open> ?R * (SYNTHESIS ?Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " R * Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R * (SYNTHESIS Y) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2300 for \<open> ?R * ?V \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  " R * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * \<blangle> X \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
      \<comment> \<open>successful termination of the step-by-step search\<close>
  unfolding cast_def split_paired_All
  by (simp add: implies_refl)


subsubsection \<open>General Search\<close>

lemma [\<phi>reason 100 for \<open> ?R * ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R''' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s H' * X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> R * H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * H' * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for H :: \<open>'a::sep_semigroup set\<close>
  unfolding cast_def Action_Tag_def
  by (metis (no_types, lifting) mult.assoc set_mult_expn)

lemma [\<phi>reason 70 for \<open> ?R * ?H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R''' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " CHK_SUBGOAL G
  \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
  \<Longrightarrow> R * H \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' * H * \<blangle> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G "
  for H :: \<open>'a::sep_ab_semigroup set\<close> 
  unfolding cast_def Action_Tag_def
  by (smt (verit, del_insts) mult.assoc mult.commute set_mult_expn)

(* lemma [\<phi>reason 1200
    on \<open>?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "CHK_SUBGOAL G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
    \<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])
*)

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>

subsubsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  " R * T1 * T2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R * (T1 * T2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  " T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * X1 * X2 \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> R * (X1 * X2) \<brangle> \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding mult.assoc[symmetric] .









(* subsection \<open>Structural Pairs\<close> (*depreciated*)

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def . *)




subsection \<open>Convergence of Branches\<close>

text \<open>The procedure transforms \<^term>\<open>(If P A B)\<close> into the canonical \<phi>-BI form \<^term>\<open>C\<close>.

  The strongest post-condition of a branch statement results in \<^term>\<open>If P A B\<close> typically.
  It is strongest but not good because it violates the canonical \<phi>-BI form.
  Thus an automation procedure here is presented to transform it.
  Typically it unifies refinement relations in two branches but leaves abstract objects
  in an if expression.

  The transformation is as strong as possible to minimize the loose of information.
  It is clear if two branches are in the same refinement, no information will be lost.
  If not, and any necessary information is lost in this process, user can always manually transform
  the assertion before the end of each branch, to unify the refinement of two branches.
\<close>

text \<open>This merging procedure retains the order of the left side.\<close>

typedecl branch_convergence
instance branch_convergence :: whole_target ..
consts branch_convergence :: \<open>branch_convergence action\<close>

(* text \<open>Though definitionally If is identical to If, there is semantic difference between them.
  If has a systematical meaning. If P A B means the procedure merging two assertions
  A and B, whereas If P A B means to merge two abstract objects or two refinement relations.
  A key difference in the procedure is, there is fallback for If P A B. If there is no further
  rule telling how to do with If P A B, then the result of the procedure on this is just
  If P A B itself --- it is usual that a branch statement returning 1 or 2 is specified by
  \<^term>\<open>(if P then 1 else 2) \<Ztypecolon> \<phi>Nat\<close>. In contrast, there is no fallback for If P A B, because
  a failure of If P A B means the failure of merging those two assertions A and B, which is
  the failure of the whole merging procedure.\<close> *)

subsubsection \<open>Identity\<close>

lemma [\<phi>reason 3000 for \<open>If ?P ?A ?A'' = ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "If P A A = A \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by simp

lemma (in \<phi>spec) [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?A ?A'' \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w If P A A \<longmapsto> A \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by (simp add: view_shift_id)

lemma [\<phi>reason 3000 for \<open>If ?P ?A ?A'' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "If P A A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s A \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def by simp

subsubsection \<open>Zero\<close>

lemma (in \<phi>spec)
  [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?A 0 \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w If P A 0 \<longmapsto> (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by simp

lemma (in \<phi>spec)
  [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P 0 ?A \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "\<^bold>v\<^bold>i\<^bold>e\<^bold>w If P 0 A \<longmapsto> (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> P) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by simp

lemma [\<phi>reason 3000 for \<open>If ?P ?A 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "If P A 0 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (simp add: \<phi>expns zero_set_def)

lemma [\<phi>reason 3000 for \<open>If ?P 0 ?A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "If P 0 A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> P) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (simp add: \<phi>expns zero_set_def)


subsubsection \<open>Fallback\<close>

lemma [\<phi>reason 10 for \<open>If ?P ?A ?B = ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "If P A B = If P A B \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def ..

text \<open>There is no fallback for \<^const>\<open>If\<close>. The If is not allowed to be fallback.
  If the convergence for If fails, the reasoning fails.\<close>

subsubsection \<open>Ad-hoc rules\<close>

lemma [\<phi>reason for \<open>If ?P (?a \<Zinj> ?x) (?b \<Zinj> ?y) = ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  " If P a b = aa \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P x y = z  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (a \<Zinj> x) (b \<Zinj> y) = (aa \<Zinj> z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by force

(* lemma (in \<phi>spec) branch_convergence_skip:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (R1 * X) (N * Y * \<blangle> R2 \<brangle>) \<longmapsto> R \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (R1 * X) (N * \<blangle> R2 * Y \<brangle>) \<longmapsto> R \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def
  by (metis mult.assoc mult.commute)

lemma branch_convergence_skip_imp:
  " If P (R1 * X) (N * Y * \<blangle> R2 \<brangle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> If P (R1 * X) (N * \<blangle> R2 * Y \<brangle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  for R :: \<open>'a::sep_algebra set\<close>
  unfolding FOCUS_TAG_def GOAL_CTXT_def Action_Tag_def
  by (metis mult.assoc mult.commute)
*)

(*
lemma [\<phi>reason 3000]:
  "If P A B = X
  \<Longrightarrow> If (MergeNeg (MergeNeg P)) A B = X"
  unfolding MergeNeg_def by simp

lemma [\<phi>reason 2800]:
  "If P B A = X
  \<Longrightarrow> If (MergeNeg P) A B = X"
  unfolding MergeNeg_def by force
*)

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 1400]:
  \<open> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma [\<phi>reason 1400]:
  \<open> If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma (in \<phi>spec) [\<phi>reason 1400]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) R \<longmapsto> Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) R \<longmapsto> Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma (in \<phi>spec) [\<phi>reason 1400]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<and> Q2) \<longmapsto> Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q2) \<longmapsto> Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Subjection_Subjection .

lemma (in \<phi>spec)
  [\<phi>reason 1300 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QL) (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QR) \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  " If P QL QR = Q \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j QL) (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j QR) \<longmapsto> (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def by force

lemma [\<phi>reason 1300 for \<open>If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QL) (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QR) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  " If P QL QR = Q \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j QL) (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j QR) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def by force

lemma [\<phi>reason 1200
    for \<open>If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longrightarrow> Q) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Imply_def Action_Tag_def by (simp add: \<phi>expns)

lemma (in \<phi>spec) [\<phi>reason 1200
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) ?R \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) R \<longmapsto> (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longrightarrow> Q) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>If ?P ?L (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not>P \<longrightarrow> Q) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def by (simp add: \<phi>expns)

lemma (in \<phi>spec)
  [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?L (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<longmapsto> (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not>P \<longrightarrow> Q) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns; blast)


subsubsection \<open>Existential\<close>

lemma (in \<phi>spec) Conv_Merge_Ex_both:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L x) (R x) \<longmapsto> X x \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (\<exists>* x. L x) (\<exists>* x. R x) \<longmapsto> (\<exists>* x. X x) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; fastforce)

lemma Conv_Merge_Ex_both_imp:
  "(\<And>x. If P (L x) (R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X x \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> If P (\<exists>* x. L x) (\<exists>* x. R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. X x) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; blast)

lemma (in \<phi>spec) Conv_Merge_Ex_R
  [\<phi>reason 1100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P ?L (\<exists>* x. ?R x) \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R x) \<longmapsto> X x \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (\<exists>* x. R x) \<longmapsto> (\<exists>* x. X x) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; fastforce)

lemma Conv_Merge_Ex_R_imp
  [\<phi>reason 1100 for \<open>If ?P ?L (\<exists>* x. ?R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "(\<And>x. If P L (R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X x \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> If P L (\<exists>* x. R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. X x) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def
  by (cases P; simp add: set_eq_iff \<phi>expns; blast)

lemma (in \<phi>spec)
  [\<phi>reason 1100 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (\<exists>* x. ?L x) ?R \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "(\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L x) R \<longmapsto> X x \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (\<exists>* x. L x) R \<longmapsto> (\<exists>* x. X x) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def View_Shift_def
  by (cases P; clarsimp simp add: set_eq_iff \<phi>expns; fastforce)

lemma [\<phi>reason 1100 for \<open>If ?P (\<exists>* x. ?L x) ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  "(\<And>x. If P (L x) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X x \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence)
\<Longrightarrow> If P (\<exists>* x. L x) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>* x. X x) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def by (cases P; simp add: set_eq_iff \<phi>expns; blast)

text \<open>The merging recognize two existential quantifier are identical if their type and variable name
  are the same. If so it uses Conv_Merge_Ex_both to merge the quantification,
  or else the right side is expanded first.\<close>

\<phi>reasoner_ML (in \<phi>spec) Merge_Existential 2000
  (conclusion \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>) =
\<open>fn (ctxt,sequent) =>
  let
    val ((Const (\<^const_name>\<open>If\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exa,tya,_))
                                        $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exb,tyb,_))), _, _)
        = PhiSyntax.dest_view_shift (Thm.major_prem_of sequent)
    val sequent' = if exa = exb andalso tya = tyb
                   then @{thm Conv_Merge_Ex_both} RS sequent
                   else @{thm Conv_Merge_Ex_R} RS sequent
  in Seq.single (ctxt, sequent')
  end\<close>

\<phi>reasoner_ML Merge_Existential_imp 2000 (conclusion \<open>If ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X\<close>) =
\<open>fn (ctxt,sequent) =>
  let
    val ((Const (\<^const_name>\<open>If\<close>, _) $ _ $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exa,tya,_))
                                         $ (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (exb,tyb,_))), _, _)
        = PhiSyntax.dest_implication (Thm.major_prem_of sequent)
    val sequent' = if exa = exb andalso tya = tyb
                   then @{thm Conv_Merge_Ex_both_imp} RS sequent
                   else @{thm Conv_Merge_Ex_R_imp} RS sequent
  in Seq.single (ctxt, sequent')
  end\<close>



subsubsection \<open>Main Procedure\<close>

lemma [\<phi>reason 2000 for \<open>If ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  " If P x y = z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (z \<Ztypecolon> Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def Imply_def by (cases P; simp)

lemma (in \<phi>spec)
  [\<phi>reason 2000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  " If P x y = z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<longmapsto> (z \<Ztypecolon> Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def
  by (cases P; clarsimp simp add: \<phi>expns view_shift_id)

definition \<open>Branch_Convergence_Type_Pattern type the_type_to_match \<equiv> Trueprop True\<close>

lemma [\<phi>reason 10 for \<open>PROP Branch_Convergence_Type_Pattern ?X ?X'\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern X X\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200 for \<open>PROP Branch_Convergence_Type_Pattern (Val ?v ?T) (Val ?v ?T')\<close>]:
  \<open>PROP Branch_Convergence_Type_Pattern (Val v T) (Val v T')\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1200 for \<open>If ?P (?L * (?x \<Ztypecolon> ?T)) ?R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern T T'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' * \<blangle> y \<Ztypecolon> T' \<brangle> \<^bold>a\<^bold>n\<^bold>d Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> If P x y = z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P T T' = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L R' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (L * (x \<Ztypecolon> T)) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X * (z \<Ztypecolon> Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def Action_Tag_def GOAL_CTXT_def FOCUS_TAG_def
  by (smt (z3) Imply_def implies_right_prod)

lemma (in \<phi>spec)
  [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w If ?P (?L * (?x \<Ztypecolon> ?T)) ?R \<longmapsto> ?X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern T T'
\<Longrightarrow> SUBGOAL TOP_GOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' * \<blangle> y \<Ztypecolon> T' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> If P x y = z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P T T' = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R' \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L * (x \<Ztypecolon> T)) R \<longmapsto> X * (z \<Ztypecolon> Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def Action_Tag_def GOAL_CTXT_def FOCUS_TAG_def
  by (smt (z3) View_Shift_def mult.commute mult.left_commute)



subsubsection \<open>Convergence of Structural Nodes\<close>

lemma [\<phi>reason 1200 for \<open>If ?P (?n \<Znrres> ?T) (?n' \<Znrres> ?U) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (n \<Znrres> T) (n \<Znrres> U) = n \<Znrres> Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (?T \<^emph> ?U) (?T' \<^emph> ?U') = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> If P T T' = T'' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P U U' = U'' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (T \<^emph> U) (T' \<^emph> U') = (T'' \<^emph> U'') \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (?k \<^bold>\<rightarrow>\<^sub>@ ?T) (?k' \<^bold>\<rightarrow>\<^sub>@ ?U) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (k \<^bold>\<rightarrow>\<^sub>@ T) (k \<^bold>\<rightarrow>\<^sub>@ U) = k \<^bold>\<rightarrow>\<^sub>@ Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (?k \<^bold>\<rightarrow> ?T) (?k' \<^bold>\<rightarrow> ?U) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (k \<^bold>\<rightarrow> T) (k \<^bold>\<rightarrow> U) = k \<^bold>\<rightarrow> Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 1200 for \<open>If ?P (Val ?v ?T) (Val ?v' ?U) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open>If P (Val v T) (Val v U) = Val v (If P T U) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200 for \<open>If ?P (\<black_circle> ?T) (\<black_circle> ?U) = (\<black_circle> ?Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (\<black_circle> T) (\<black_circle> U) = (\<black_circle> Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by fastforce

lemma [\<phi>reason 1200 for \<open>If ?P (Val ?v ?T) (Val ?v' ?U) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (Val v T) (Val v U) = (Val v Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by fastforce


(* subsubsection \<open>Object\<close>

definition EqualAddress :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool "
  where "EqualAddress _ _ = True"

lemma [\<phi>reason]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a1 = a2
   \<Longrightarrow> EqualAddress (a1 \<Zinj> x1 \<Ztypecolon> T1) (a2 \<Zinj> x2 \<Ztypecolon> T2) "
  unfolding EqualAddress_def .. *)

subsubsection \<open>Unfold\<close>

lemma (in \<phi>spec) [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (N \<heavy_comma> R1 \<heavy_comma> R2) \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (N \<heavy_comma> (R1 \<heavy_comma> R2)) \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason 2000]:
  " If P L (N * R1 * R2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L (N * (R1 * R2)) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  for N :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma [\<phi>reason 2000]:
  " If P (L1 * L2 * L3) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (L1 * (L2 * L3)) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def by (metis mult.assoc)

lemma (in \<phi>spec) [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L1 \<heavy_comma> L2 \<heavy_comma> L3) R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L1 \<heavy_comma> (L2 \<heavy_comma> L3)) R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by (metis mult.assoc)

subsubsection \<open>Eliminate Void Hole\<close>

lemma [\<phi>reason 2000]:
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L (R * 1) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L (1 * R) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L (R' * R) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P L (R' * 1 * R) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma [\<phi>reason 2000]:
  " If P L R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (L * 1) R \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def by (cases P; simp)

lemma (in \<phi>spec) [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R \<heavy_comma> 1) \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)

lemma (in \<phi>spec) [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (1 \<heavy_comma> R) \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)

lemma (in \<phi>spec) [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R' \<heavy_comma> R) \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L (R' \<heavy_comma> 1 \<heavy_comma> R) \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)

lemma (in \<phi>spec) [\<phi>reason 2000]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P L R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w If P (L \<heavy_comma> 1) R \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence"
  unfolding Action_Tag_def by (cases P; simp)


(* subsection \<open>Program Interface\<close> \<comment> \<open>Interfaces exported to target LLVM module\<close>

definition Prog_Interface :: " label \<Rightarrow> 'a itself \<Rightarrow> 'b itself \<Rightarrow> ('a::lrep  \<longmapsto> 'b::lrep) \<Rightarrow> bool"
  where "Prog_Interface _ args rets proc \<longleftrightarrow> True"

lemma Prog_Interface_proc: "TERM proc \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) proc" 
  unfolding Prog_Interface_def ..

lemma Prog_Interface_func:
  "TERM f \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) f" 
  unfolding Prog_Interface_def ..
*)

subsection \<open>Filter Out Values\<close>

text \<open>Given an assertion X, antecedent \<^term>\<open>Filter_Out_Free_Values X X'\<close>
  returns X' where all free value assertions \<^term>\<open>x \<Ztypecolon> Val raw T\<close> filtered out, where \<^term>\<open>raw\<close>
  contains at least one free variable of \<^typ>\<open>'a sem_value\<close>.

  It is typically used in exception. When a computation triggers an exception at state X,
    the state recorded in the exception is exactly X' where value assertions are filtered out.\<close>

definition \<open>Filter_Out_Free_Values' (remain::'a::sep_magma set) (keep::'a set) (check::'a set) (ret::'a set)
              \<equiv> Trueprop (keep = check \<longrightarrow> (remain * keep \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ret))\<close>

(* lemma [\<phi>reason for \<open>PROP Filter_Out_Free_Values ?ex ?var_X ?Z\<close>]:
  \<open>PROP Filter_Out_Free_Values ex X X\<close>
  unfolding Filter_Out_Free_Values_def using implies_refl . *)

lemma [\<phi>reason 1200 for \<open>PROP Filter_Out_Free_Values (ExSet ?T) ?T'\<close>]:
  \<open>(\<And>c. PROP Filter_Out_Free_Values (T c) (T' c))
\<Longrightarrow> PROP Filter_Out_Free_Values (ExSet T) (ExSet T')\<close>
  unfolding Filter_Out_Free_Values_def Imply_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200 for \<open>PROP Filter_Out_Free_Values (?T \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P) ?T'\<close>]:
  \<open> PROP Filter_Out_Free_Values T T'
\<Longrightarrow> PROP Filter_Out_Free_Values (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding Filter_Out_Free_Values_def Imply_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>PROP Filter_Out_Free_Values (?R * ?X) ?Z\<close>]:
  \<open> PROP Filter_Out_Free_Values R R'
\<Longrightarrow> PROP Filter_Out_Free_Values'  R' X X Z
\<Longrightarrow> PROP Filter_Out_Free_Values (R * X) Z\<close>
  unfolding Filter_Out_Free_Values_def Imply_def Filter_Out_Free_Values'_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1100 for \<open>PROP Filter_Out_Free_Values ?R ?Z\<close>]:
  \<open> PROP Filter_Out_Free_Values'  1 R R Z
\<Longrightarrow> PROP Filter_Out_Free_Values R Z\<close>
  for R :: \<open>'a::sep_magma_1 set\<close>
  unfolding Filter_Out_Free_Values_def Filter_Out_Free_Values'_def Imply_def
  by simp

lemma [\<phi>reason 1200 for \<open>PROP Filter_Out_Free_Values' ?R ?Y (SYNTHESIS ?X) ?Z\<close>]:
  \<open> PROP Filter_Out_Free_Values' R Y X Z
\<Longrightarrow> PROP Filter_Out_Free_Values' R Y (SYNTHESIS X) Z\<close>
  unfolding Filter_Out_Free_Values'_def Synthesis_def .

lemma [\<phi>reason 1200 for \<open>PROP Filter_Out_Free_Values' ?R ?Y (FIX ?X) ?Z\<close>]:
  \<open> PROP Filter_Out_Free_Values' R Y X Z
\<Longrightarrow> PROP Filter_Out_Free_Values' R Y (FIX X) Z\<close>
  unfolding Filter_Out_Free_Values'_def Fix_def .

lemma [\<phi>reason 1100 for \<open>PROP Filter_Out_Free_Values' 1 ?Y ?X ?Z\<close>]:
  \<open>PROP Filter_Out_Free_Values' 1 Y X Y\<close>
  for Y :: \<open>'a::sep_magma_1 set\<close>
  unfolding Filter_Out_Free_Values'_def Imply_def by simp

lemma Filter_Out_Free_Values'_accept_1[\<phi>reason 1110 for \<open>PROP Filter_Out_Free_Values' 1 ?Y ?X ?Z\<close>]:
  \<open>PROP Filter_Out_Free_Values' 1 Y X Y\<close>
  for Y :: \<open>'a::sep_magma_1 set\<close>
  unfolding Filter_Out_Free_Values'_def Imply_def by simp

lemma Filter_Out_Free_Values'_accept[\<phi>reason 1100 for \<open>PROP Filter_Out_Free_Values' ?R ?Y ?X ?Z\<close>]:
  \<open>PROP Filter_Out_Free_Values' R Y X (R * Y)\<close>
  unfolding Filter_Out_Free_Values'_def Imply_def by simp

lemma Filter_Out_Free_Values'_reject_val:
  \<open>PROP Filter_Out_Free_Values' R Y (x \<Ztypecolon> Val raw T) R\<close>
  for R :: \<open>'a::sep_algebra set\<close>
  unfolding Filter_Out_Free_Values'_def Imply_def by (simp add: \<phi>expns)

\<phi>reasoner_ML Filter_Out_Free_Values'_reject_val 1200
  (conclusion \<open>PROP Filter_Out_Free_Values' ?R ?Y (?x \<Ztypecolon> Val ?raw ?T) ?Z\<close>) = \<open>
fn (ctxt, sequent) =>
  let
    val Const (\<^const_name>\<open>Filter_Out_Free_Values'\<close>, _) $ R $ _
          $ (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ raw $ _))
          $ _ = Thm.major_prem_of sequent
    fun has_free_val (Free (_, Type (\<^type_name>\<open>sem_value\<close>, [_]))) = true
      | has_free_val (A $ B) = has_free_val A orelse has_free_val B
      | has_free_val (Abs (_,_,X)) = has_free_val X
      | has_free_val _ = false
    val rule =
      if has_free_val raw
      then @{thm Filter_Out_Free_Values'_reject_val}
      else (case R of Const (\<^const_name>\<open>one_class.one\<close>, _) => @{thm Filter_Out_Free_Values'_accept_1}
                    | _ => @{thm Filter_Out_Free_Values'_accept})
  in
    Seq.single (ctxt, rule RS sequent)
  end
\<close>



subsection \<open>Variable Extraction\<close>

definition Variant_Cast :: "'vars \<Rightarrow> 'a set \<Rightarrow> ('vars \<Rightarrow> 'a set) \<Rightarrow> bool" ("\<^bold>v\<^bold>a\<^bold>r\<^bold>y _ \<^bold>i\<^bold>n _/ \<longmapsto> _" )
  where "Variant_Cast insts X X' \<longleftrightarrow> X = X' insts"

text \<open>The main usage of this reasoning is for loop and recursion.
  Given an assertion X, \<^prop>\<open>Variant_Cast vars X X'\<close> tries under instruction from user to
    extract the variable part \<^term>\<open>vars\<close> in the assertion. This part typically will be
    universally quantified inside loop bodies.

  There are two syntax for instructing this extraction.
  One is 'v1 v2 ...' instructing all occurrence of free variables v1 v2... in X will be such generalized.
  Another is 'v1 v2 in pattern' instructing to first pattern match X and then v1 v2 in the matched
    pattern will be generalized.\<close>

lemma Variant_Cast_I: "X = X' vars \<Longrightarrow> Variant_Cast vars X X' "
  unfolding Variant_Cast_def by auto

lemma Variant_Cast_I_always:
  "X = X' vars \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e always vars \<Longrightarrow>
  Variant_Cast vars X (\<lambda>vars. X' vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j always vars)"
  unfolding Variant_Cast_def by (auto simp add: \<phi>expns)

lemma case_prod_expn_I: "A = B x y \<Longrightarrow> A = case_prod B (x,y)" by simp
lemma case_named_expn_I: "A = B x \<Longrightarrow> A = case_named B (tag x)" by simp

ML_file_debug \<open>library/variables_tag.ML\<close>

\<phi>processor vars_by_pattern 3000 (\<open>Variant_Cast ?vars ?X ?X' \<Longrightarrow> PROP ?P\<close>)
\<open>fn (ctxt, sequent) => 
let open Parse Scan NuHelp NuBasics
  fun pattern_match ((vars, pattern), always) _ =
    (ctxt, Nu_Variable_Factor.vary_by_pattern vars pattern always ctxt sequent)
  fun var_term (vars, always) _ =
    (ctxt, Nu_Variable_Factor.vary_by_parts vars always ctxt sequent)
  val none = Scan.succeed []
  val params = (list Parse.params) >> flat
  val syn_pattern_match =
    (params --| \<^keyword>\<open>in\<close> -- term -- option (\<^keyword>\<open>invar\<close> |-- term))
    >> pattern_match
  val syn_var_term = (list1 term -- Scan.option (\<^keyword>\<open>invar\<close> |-- term)) >> var_term
in syn_pattern_match || syn_var_term end\<close>

(*  \<open>Nu_Reasoners.wrap (fn ctxt => Nu_Reasoners.asm_simp_tac (ctxt addsimps Proof_Context.get_thms ctxt "\<phi>expns"))\<close> *)



subsection \<open>Automation for Sharing Permission\<close>

subsubsection \<open>Structure Info\<close>

definition Structure_Info :: \<open>('a,'b) \<phi> \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Structure_Info T P \<longleftrightarrow> (\<forall>x. Inhabited (x \<Ztypecolon> T) \<longrightarrow> P)\<close>
  \<comment> \<open>Extract structure information inside an assertion, typically validity of permissions
      (i.e. large than zero), which is used in the automation procedure.\<close>

lemma [\<phi>reason 1200 for \<open>Structure_Info (?n \<Znrres> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (n \<Znrres> T) (0 < n \<and> P)\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (\<black_circle> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (\<black_circle> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?k \<^bold>\<rightarrow> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (k \<^bold>\<rightarrow> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (k \<^bold>\<rightarrow>\<^sub>@ T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>Structure_Info (?T \<^emph> ?U) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info U Q
\<Longrightarrow> Structure_Info (T \<^emph> U) (P \<and> Q)\<close>
  unfolding Structure_Info_def Inhabited_def
  by (simp add: \<phi>expns; blast)

lemma [\<phi>reason 1200 for \<open>Structure_Info (\<phi>perm_transformer ?\<psi> ?T) ?P\<close>]:
  \<open> Structure_Info T P
\<Longrightarrow> Structure_Info (\<phi>perm_transformer \<psi> T) P\<close>
  unfolding Structure_Info_def Inhabited_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 30 for \<open>Structure_Info ?T ?P\<close>]:
  \<open> Structure_Info T True \<close>
  unfolding Structure_Info_def by blast

subsubsection \<open>Cleaning\<close>

consts clean_automation_waste :: mode

lemma [\<phi>reason 1000 for \<open>?X = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>X = X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200 for \<open>(() \<Ztypecolon> \<phi>None) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>(() \<Ztypecolon> \<phi>None) = 1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?k \<^bold>\<rightarrow> \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow> \<circle>) = (() \<Ztypecolon> \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ \<circle>) = (() \<Ztypecolon> \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?y \<Ztypecolon> \<circle>) = (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> ?Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<circle>) = (() \<Ztypecolon> k \<^bold>\<rightarrow> \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?y \<Ztypecolon> \<circle>) = (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<circle>) = (() \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>MapAt_L_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open> perm_transformer' \<psi>
\<Longrightarrow> (x \<Ztypecolon> \<phi>perm_transformer \<psi> \<circle>) = (() \<Ztypecolon> \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>perm_transformer_\<phi>None
  by simp

declare perm_transformer_pointwise[\<phi>reason 1200]
        perm_transformer_to_share[\<phi>reason 1200]

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> ?n \<Znrres> \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n
\<Longrightarrow> (x \<Ztypecolon> n \<Znrres> \<circle>) = (() \<Ztypecolon> (\<circle> :: ('a::share_one,unit) \<phi>)) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def Premise_def \<phi>Share_\<phi>None by simp

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> ?T \<^emph> \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> T \<^emph> \<circle>) = ((x \<Ztypecolon> T) :: 'a::sep_magma_1 set) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?y) \<Ztypecolon> \<circle> \<^emph> ?U) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>((x,y) \<Ztypecolon> \<circle> \<^emph> U) = ((y \<Ztypecolon> U) :: 'b::sep_magma_1 set) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding \<phi>Prod_\<phi>None Action_Tag_def ..

lemma [\<phi>reason 1200 for \<open>((?x,?r) \<Ztypecolon> (?T \<^emph> ?n \<Znrres> \<circle>)) = (?Z :: ?'a::{share_one,sep_magma_1} set) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n
\<Longrightarrow> ((x,r) \<Ztypecolon> (T \<^emph> n \<Znrres> \<circle>)) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>((?r,?x) \<Ztypecolon> (?n \<Znrres> \<circle> \<^emph> ?T)) = (?Z :: ?'a::{share_one,sep_magma_1} set) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n
\<Longrightarrow> ((r,x) \<Ztypecolon> (n \<Znrres> \<circle> \<^emph> T)) = ((x \<Ztypecolon> T):: 'a::{share_one,sep_magma_1} set) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding set_eq_iff Premise_def Action_Tag_def
  by (simp add: \<phi>expns)



subsubsection \<open>Extract\<close>

text \<open>The canonical form is where all permission annotation are on leaves.
  It minimizes fragments.\<close>

definition Structural_Extract :: \<open>'a::sep_magma set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Structural_Extract From Remain To Residual Aux \<longleftrightarrow> (Residual * From \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Remain * To \<^bold>a\<^bold>n\<^bold>d Aux)\<close>
  \<comment> \<open>Extract To from From, remaining Remain the unused part in From,
      and leaving Residual the part in To that fails to be obtained from From.\<close>

definition \<open>Structural_Extract' = Structural_Extract\<close>

lemma [\<phi>reason 1100]:
  \<open> Structural_Extract' X R Y W P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R = R' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste
\<Longrightarrow> W = W' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract'_def Action_Tag_def
  by simp

lemma Structural_Extract_imply_P:
  \<open> Structural_Extract X R Y W P1
\<Longrightarrow> P1 \<longrightarrow> P2
\<Longrightarrow> Structural_Extract X R Y W P2\<close>
  unfolding Structural_Extract_def Imply_def by blast

lemma Structural_Extract'_imply_P:
  \<open> Structural_Extract' X R Y W P1
\<Longrightarrow> P1 \<longrightarrow> P2
\<Longrightarrow> Structural_Extract' X R Y W P2\<close>
  unfolding Structural_Extract_def Structural_Extract'_def Imply_def
  by blast


lemma Structural_Extract_reverse_morphism_I[intro?]:
  \<open> Structural_Extract X R Y W P
\<Longrightarrow> RP \<longrightarrow> RX
\<Longrightarrow> Structural_Extract X R Y W (Automatic_Morphism RP RX \<and> P)\<close>
  unfolding Morphism_def Structural_Extract_def Imply_def
  by blast

lemma Structural_Extract'_reverse_morphism_I[intro?]:
  \<open> Structural_Extract' X R Y W P
\<Longrightarrow> RP \<longrightarrow> RX
\<Longrightarrow> Structural_Extract' X R Y W (Automatic_Morphism RP RX \<and> P)\<close>
  unfolding Structural_Extract'_def Morphism_def Structural_Extract_def Imply_def
  by blast

lemma [\<phi>reason 1111 for \<open>Structural_Extract ?X ?R' ?Y ?W' (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract' X R Y W (Automatic_Morphism RP (Structural_Extract' rY rW rX rR rP) \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow>  R = R'  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste
\<Longrightarrow>  W = W'  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste
\<Longrightarrow> rR = rR' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste
\<Longrightarrow> rW = rW' \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste
\<Longrightarrow> Structural_Extract X R' Y W' (Automatic_Morphism RP (Structural_Extract rY rW' rX rR' rP) \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract'_def Action_Tag_def
  by simp



paragraph \<open>Termination\<close>

lemma Structural_Extract_\<phi>None_right [\<phi>reason 3000
    for \<open>Structural_Extract ?X ?R (() \<Ztypecolon> \<phi>None) ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract X X (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right GOAL_CTXT_def
  using implies_refl .

lemma Structural_Extract_\<phi>None_left [\<phi>reason 3000
    for \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) ?R ?Y ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X X True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right GOAL_CTXT_def
  using implies_refl .


lemma Structural_Extract_1_right [\<phi>reason 3000
    for \<open>Structural_Extract ?X ?R 1 ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract X X 1 1 True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right GOAL_CTXT_def
  using implies_refl .

lemma Structural_Extract_1_left [\<phi>reason 3000
    for \<open>Structural_Extract 1 ?R ?Y ?W ?P \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>No further extraction is demanded.\<close>
  \<open>Structural_Extract 1 1 X X True \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def mult_1_left \<phi>None_itself_is_one mult_1_right GOAL_CTXT_def
  using implies_refl .


(*TODO: BUG: need to check the case where Y requires only partial share permission but
    this rule may give it the total.*)
lemma Structural_Extract_exact [\<phi>reason 3000
    for \<open>Structural_Extract' ?X ?R ?Y ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>The current object X is exactly what we want to extract.\<close>
  \<open>Structural_Extract' X (() \<Ztypecolon> \<phi>None) X (() \<Ztypecolon> \<phi>None) True  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Structural_Extract_def Structural_Extract'_def
      mult_1_left \<phi>None_itself_is_one mult_1_right GOAL_CTXT_def
  using implies_refl .






lemma [\<phi>reason 3011
    for \<open>Structural_Extract ?X ?R (() \<Ztypecolon> \<phi>None) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract X X (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None)
   (Automatic_Morphism True (Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X' X' True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>None_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_\<phi>None_right[unfolded GOAL_CTXT_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) X X
    (Automatic_Morphism True (Structural_Extract X' X' (() \<Ztypecolon> \<phi>None) (() \<Ztypecolon> \<phi>None) True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>None_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_\<phi>None_right[unfolded GOAL_CTXT_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract ?X ?R 1 ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract X X 1 1 (Automatic_Morphism True (Structural_Extract 1 1 X' X' True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding GOAL_CTXT_def
  by (blast intro: Structural_Extract_1_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_1_right[unfolded GOAL_CTXT_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract 1 ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open>Structural_Extract 1 1 X X (Automatic_Morphism True (Structural_Extract X' X' 1 1 True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding GOAL_CTXT_def
  by (blast intro: Structural_Extract_1_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_1_right[unfolded GOAL_CTXT_def]
                   Structural_Extract_reverse_morphism_I)

lemma [\<phi>reason 3011
    for \<open>Structural_Extract' ?X ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]: \<comment> \<open>The current object X is exactly what we want to extract.\<close>
  \<open>Structural_Extract' X  (() \<Ztypecolon> \<phi>None) X  (() \<Ztypecolon> \<phi>None)
    (Automatic_Morphism True (Structural_Extract' X' (() \<Ztypecolon> \<phi>None) X' (() \<Ztypecolon> \<phi>None) True) \<and> True)
   \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_magma_1 set\<close> and X' :: \<open>'aa::sep_magma_1 set\<close>
  unfolding GOAL_CTXT_def
  by (blast intro: Structural_Extract_exact [unfolded GOAL_CTXT_def]
                   Structural_Extract'_reverse_morphism_I)



paragraph \<open>Fall back\<close>

lemma Structural_Extract_fallback
  [\<phi>reason 10 for \<open>Try ?S (Structural_Extract ?X ?X' ?Y ?Y' ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> Try False (Structural_Extract X X Y Y True)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_ab_semigroup set\<close>
  unfolding Structural_Extract_def Structural_Extract'_def
      \<phi>None_itself_is_one mult_1_left GOAL_CTXT_def Try_def
  by (simp add: implies_refl mult.commute)

lemma [\<phi>reason 10 for \<open>Try ?S (Structural_Extract ?X ?X' ?Y ?Y' (Automatic_Morphism ?RP ?RX \<and> ?P)) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> Try False (Structural_Extract X  X  Y  Y
      (Automatic_Morphism True (Structural_Extract X' X' Y' Y' True) \<and> True))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_ab_semigroup set\<close> and X' :: \<open>'aa::sep_ab_semigroup set\<close>
  unfolding GOAL_CTXT_def Try_def
  by (blast intro: Structural_Extract_fallback[unfolded GOAL_CTXT_def Try_def]
                   Structural_Extract_reverse_morphism_I)



paragraph \<open>Terminations for Specific Node\<close>

lemma Structural_Extract_\<phi>Some
  [\<phi>reason 1200 for \<open>Structural_Extract (?x \<Ztypecolon> \<black_circle> ?T) ?R (?y \<Ztypecolon> \<black_circle> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<black_circle> T) (() \<Ztypecolon> \<phi>None) (y \<Ztypecolon> \<black_circle> U) (() \<Ztypecolon> \<phi>None) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left GOAL_CTXT_def
            Structural_Extract'_def
  using \<phi>Some_cast .

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract (?x \<Ztypecolon> \<black_circle> ?T) ?R (?y \<Ztypecolon> \<black_circle> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<black_circle> T) (() \<Ztypecolon> \<phi>None) (y \<Ztypecolon> \<black_circle> U) (() \<Ztypecolon> \<phi>None)
      (Automatic_Morphism (y' \<Ztypecolon> U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P')
            (Structural_Extract (y' \<Ztypecolon> \<black_circle> U') (() \<Ztypecolon> \<phi>None) (x' \<Ztypecolon> \<black_circle> T') (() \<Ztypecolon> \<phi>None) P')
      \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>Some[unfolded GOAL_CTXT_def]
                   Structural_Extract_reverse_morphism_I)

(*TODO: According to @{thm Agreement_times}, there must be a reasoning mechanism for \<inter>\<^sub>\<phi>
  It scatters information using \<inter>\<^sub>\<phi> 

The bellowing reasoning is too weak! *)

lemma Structural_Extract_aggrement_to
  [\<phi>reason 1200 for \<open>Structural_Extract (?x \<Ztypecolon> Agreement ?T) ?R (?y \<Ztypecolon> Agreement ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left GOAL_CTXT_def \<r>Feasible_def
            Structural_Extract'_def
  apply (cases C; simp)
  \<medium_left_bracket> premises A
    dup
    Agreement_cast[OF A]
  \<medium_right_bracket>.
  using Agreement_cast .

lemma Structural_Extract_aggrement_from:
  \<open> y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>) (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def \<phi>None_itself_is_one mult_1_left GOAL_CTXT_def \<r>Feasible_def
            Structural_Extract'_def
  apply (cases C; simp)
  \<medium_left_bracket> premises A
    Agreement_cast[OF A]
    Agreement_shrink
  \<medium_right_bracket>.
  using Agreement_cast .


lemma [\<phi>reason 1211 for \<open>Structural_Extract (?x \<Ztypecolon> Agreement ?T) ?R (?y \<Ztypecolon> Agreement ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> Agreement T) (x \<Ztypecolon> Agreement T ?\<^sub>\<phi> C) (y \<Ztypecolon> Agreement U) (() \<Ztypecolon> \<circle>)
      (Automatic_Morphism (y' \<Ztypecolon> U' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P')
          (Structural_Extract (y' \<Ztypecolon> Agreement U') (() \<Ztypecolon> \<circle>) (x' \<Ztypecolon> Agreement T') (x' \<Ztypecolon> Agreement T' ?\<^sub>\<phi> C') P')
      \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding GOAL_CTXT_def
  by (blast intro: Structural_Extract_aggrement_to  [unfolded GOAL_CTXT_def]
                   Structural_Extract_aggrement_from[unfolded GOAL_CTXT_def]
                   Structural_Extract_reverse_morphism_I)



paragraph \<open>Normalize the Target\<close>

lemma Structural_Extract_to_mult
  [\<phi>reason 1200 for \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close> ]:
  \<open> Try S1 (Structural_Extract A B Y WY P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract B C X WX P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' A C (X * Y) (WX * WY) (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close>
  unfolding Structural_Extract_def Simplify_def Action_Tag_def Structural_Extract'_def Try_def
  \<medium_left_bracket> premises L and R
    fold mult.assoc
    L[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
    R[THEN implies_right_prod]
  \<medium_right_bracket>. .

lemma Structural_Extract_\<phi>Prod_right
  [\<phi>reason 1200 for \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close> ]:
  \<open> Try S1 (Structural_Extract A B (y \<Ztypecolon> Y) (wy \<Ztypecolon> WY) P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G 
\<Longrightarrow> Try S2 (Structural_Extract B C (x \<Ztypecolon> X) (wx \<Ztypecolon> WX) P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' A C ((y,x) \<Ztypecolon> Y \<^emph> X) ((wy, wx) \<Ztypecolon> WY \<^emph> WX) (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
for A :: \<open>'a::sep_algebra set\<close>
  unfolding \<phi>Prod_expn'
  using Structural_Extract_to_mult .

paragraph \<open>Step by Step\<close>

lemma Structural_Extract_from_mult[\<phi>reason 1200 for
  \<open>Structural_Extract' (?L * ?X :: 'a::sep_algebra set) ?R ?W ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract X R2 Y Wr P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract L R Wr Wr2 P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' (L * X) (R * R2) Y Wr2 (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close>
  unfolding Structural_Extract_def Simplify_def Structural_Extract'_def Try_def
  \<medium_left_bracket> premises R and L
    fold mult.assoc
    L[THEN implies_right_prod]
    R[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  \<medium_right_bracket>. .

lemma Structural_Extract_\<phi>Prod_left [\<phi>reason 1200 for
  \<open>Structural_Extract' ((?x,?y) \<Ztypecolon> (?T::(?'a::sep_algebra,?'b) \<phi>) \<^emph> ?U) ?R (?y \<Ztypecolon> ?W) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract (x \<Ztypecolon> T) (r2 \<Ztypecolon> R2) Y W P1)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract (y \<Ztypecolon> U) (r \<Ztypecolon> R) W W2 P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' ((x,y) \<Ztypecolon> T \<^emph> U) ((r2,r) \<Ztypecolon> (R2 \<^emph> R)) Y W2 (P1 \<and> P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::sep_algebra,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' Simplify_def Action_Tag_def Structural_Extract'_def Try_def
  \<medium_left_bracket> premises R and L
    fold mult.assoc
    L[THEN implies_right_prod]
    R[THEN implies_left_prod, unfolded mult.assoc[symmetric]]
  \<medium_right_bracket>. .


lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W (Automatic_Morphism ?RR ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract A B (y \<Ztypecolon> Y) (wy \<Ztypecolon> WY)
      (Automatic_Morphism RP1 (Structural_Extract (y' \<Ztypecolon> Y') (wy' \<Ztypecolon> WY') A' B' P1') \<and> P1))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G 
\<Longrightarrow> Try S2 (Structural_Extract B C (x \<Ztypecolon> X) (wx \<Ztypecolon> WX)
      (Automatic_Morphism RP2 (Structural_Extract (x' \<Ztypecolon> X') (wx' \<Ztypecolon> WX') B' C' P2') \<and> P2))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m S1 \<or> S2
\<Longrightarrow> Structural_Extract' A C ((y,x) \<Ztypecolon> Y \<^emph> X) ((wy, wx) \<Ztypecolon> WY \<^emph> WX)
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2)
        (Structural_Extract' ((y',x') \<Ztypecolon> Y' \<^emph> X') ((wy', wx') \<Ztypecolon> WY' \<^emph> WX') A' C' (P1' \<and> P2'))
      \<and> P1 \<and> P2)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for A :: \<open>'a::sep_algebra set\<close> and A' :: \<open>'aa::sep_algebra set\<close>
  unfolding GOAL_CTXT_def Morphism_def Compact_Antecedent_def Try_def
  by (blast intro: Structural_Extract_\<phi>Prod_right[unfolded GOAL_CTXT_def Try_def]
                   Structural_Extract_\<phi>Prod_left [unfolded GOAL_CTXT_def Try_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W (Automatic_Morphism ?RR ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract (x \<Ztypecolon> T) (r2 \<Ztypecolon> R2) Y W
      (Automatic_Morphism RP1 (Structural_Extract Y' W' (x' \<Ztypecolon> T') (r2' \<Ztypecolon> R2') P1') \<and> P1))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract (y \<Ztypecolon> U) (r \<Ztypecolon> R) W W2
      (Automatic_Morphism RP2 (Structural_Extract W' W2' (y' \<Ztypecolon> U') (r' \<Ztypecolon> R') P2') \<and> P2))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' ((x,y) \<Ztypecolon> T \<^emph> U) ((r2,r) \<Ztypecolon> (R2 \<^emph> R)) Y W2
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2) (Structural_Extract' Y' W2' ((x',y') \<Ztypecolon> T' \<^emph> U') ((r2',r') \<Ztypecolon> (R2' \<^emph> R')) (P1' \<and> P2')) \<and> P1 \<and> P2)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for Y :: \<open>'a::sep_algebra set\<close> and Y' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def GOAL_CTXT_def Try_def
  by (blast intro: Structural_Extract_\<phi>Prod_right[unfolded GOAL_CTXT_def Try_def]
                   Structural_Extract_\<phi>Prod_left [unfolded GOAL_CTXT_def Try_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' ?A ?C (?X * ?Y) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Try S1 (Structural_Extract A B Y WY
      (Automatic_Morphism RP1 (Structural_Extract Y' WY' A' B' P1') \<and> P1))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Try S2 (Structural_Extract B C X WX
      (Automatic_Morphism RP2 (Structural_Extract X' WX' B' C' P2') \<and> P2))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' A C (X * Y) (WX * WY)
      (Automatic_Morphism (RP1 \<and>\<^sub>\<r> RP2) (Structural_Extract' (X' * Y') (WX' * WY') A' C' (P1' \<and> P2')) \<and> P1 \<and> P2)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close> and X' :: \<open>'aa::sep_algebra set\<close>
  unfolding Morphism_def Compact_Antecedent_def GOAL_CTXT_def Try_def
  by (blast intro: Structural_Extract_to_mult  [unfolded GOAL_CTXT_def Try_def]
                   Structural_Extract_from_mult[unfolded GOAL_CTXT_def Try_def]
                   Structural_Extract'_imply_P)

(*TODO
lemma Structural_Extract_from_mult[\<phi>reason 1200 for
  \<open>Structural_Extract' (?L * ?X :: 'a::sep_algebra set) ?R ?W ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract X R2 Y Wr P1  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract L R Wr Wr2 P2  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (L * X) (R * R2) Y Wr2 (P1 \<and> P2)
    \<and> Automatic_Morphism
    (RP1 &&& RP2)
    (Structural_Extract' (X' * Y') (WX' * WY') A' C' (P1' \<and> P2'))
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for X :: \<open>'a::sep_algebra set\<close>
*)


paragraph \<open>Structural Node\<close>

lemma Structural_Extract_\<phi>MapAt [\<phi>reason 1200 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> (?T::(?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow> ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (yr \<Ztypecolon> k \<^bold>\<rightarrow> Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  apply (simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_\<phi>Prod[symmetric])
  apply (rule \<phi>MapAt_cast) .


lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> (?T::(?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow> ?U) ?R'
    (Automatic_Morphism ?RR ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow> T) (r \<Ztypecolon> k \<^bold>\<rightarrow> R) (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) (w \<Ztypecolon> k \<^bold>\<rightarrow> W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U') (w' \<Ztypecolon> k \<^bold>\<rightarrow> W') (x' \<Ztypecolon> k \<^bold>\<rightarrow> T') (r' \<Ztypecolon> k \<^bold>\<rightarrow> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>MapAt[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)


lemma Structural_Extract_\<phi>MapAt_L [\<phi>reason 1200 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (yr \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Ur) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  apply (simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric])
  thm \<phi>MapAt_L_\<phi>Prod[symmetric]
  apply (rule \<phi>MapAt_L_cast) .

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R'
      (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (yr \<Ztypecolon> Ur)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (yr' \<Ztypecolon> Ur') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (yr \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ Ur)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (yr' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ Ur') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)




lemma Structural_Extract_\<phi>MapAt_L_pad_left [\<phi>reason 1180 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k < length k'
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k @ kd = k'
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  subgoal premises prems
    apply (insert prems(5),
       simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric]
          \<phi>MapAt_L_\<phi>MapAt_L[symmetric, of k kd, unfolded prems(3)])
    apply (rule \<phi>MapAt_L_cast) . .



lemma Structural_Extract_\<phi>MapAt_L_pad_right [\<phi>reason 1150 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R' ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k' < length k
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' @ kd = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close>
  unfolding Structural_Extract_def Premise_def Structural_Extract'_def
  subgoal premises prems
    apply (insert prems(5),
       simp add: \<phi>Prod_expn'[symmetric] \<phi>MapAt_L_\<phi>Prod[symmetric]
          \<phi>MapAt_L_\<phi>MapAt_L[symmetric, of k' kd, unfolded prems(3)])
  apply (rule \<phi>MapAt_L_cast) . .


lemma [\<phi>reason 1183 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R'
      (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k < length k'
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k @ kd = k'
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1153 for
  \<open>Structural_Extract' (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ (?T::(?'k list \<Rightarrow> ?'a::sep_monoid,?'b) \<phi>)) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?R'
    (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m length k' < length k
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m k' @ kd = k
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> kd \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ T) (r \<Ztypecolon> k  \<^bold>\<rightarrow>\<^sub>@ R) (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) (w \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') (w' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ W') (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') (r' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::sep_monoid,'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::sep_monoid,'bb) \<phi>\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>MapAt_L_pad_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_\<phi>MapAt_L_pad_right[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)




lemma Structural_Extract_\<phi>Map_L_norm_right [\<phi>reason 1200]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Premise_def \<phi>MapAt_L_At Structural_Extract'_def .

lemma Structural_Extract_\<phi>Map_L_norm_left [\<phi>reason 1200]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Premise_def \<phi>MapAt_L_At Structural_Extract'_def .


lemma [\<phi>reason 1211 for \<open>
  Structural_Extract (?x \<Ztypecolon> ?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow> ?U) ?W
      (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G
\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow> U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>Map_L_norm_right[unfolded GOAL_CTXT_def]
                   Structural_Extract_\<phi>Map_L_norm_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_imply_P)

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract (?x \<Ztypecolon> ?k \<^bold>\<rightarrow> ?T) ?R (?y \<Ztypecolon> ?k' \<^bold>\<rightarrow>\<^sub>@ ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ [] \<^bold>\<rightarrow> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> T) R (y \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> k' \<^bold>\<rightarrow>\<^sub>@ U') W' (x' \<Ztypecolon> k \<^bold>\<rightarrow> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>Map_L_norm_right[unfolded GOAL_CTXT_def]
                   Structural_Extract_\<phi>Map_L_norm_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_imply_P)



lemma Structural_Extract_\<phi>perm_transformer [\<phi>reason 1200
    for \<open>Structural_Extract' (?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?T) ?R (?y \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> \<phi>perm_transformer \<psi> T)
                        (r \<Ztypecolon> \<phi>perm_transformer \<psi> R)
                        (y \<Ztypecolon> \<phi>perm_transformer \<psi> U)
                        (w \<Ztypecolon> \<phi>perm_transformer \<psi> W)
                        P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Imply_def \<phi>Sep_Disj_def Structural_Extract'_def
  apply (clarsimp simp add: \<phi>expns)
  by (metis (no_types, opaque_lifting) homo_sep_disj_semi_def homo_sep_mult.homo_mult perm_transformer'_def)

lemma [\<phi>reason 1211
    for \<open>Structural_Extract' (?x \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?T) ?R (?y \<Ztypecolon> \<phi>perm_transformer ?\<psi> ?U) ?W
          (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<phi>Sep_Disj W T
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> \<phi>perm_transformer \<psi> T)
                        (r \<Ztypecolon> \<phi>perm_transformer \<psi> R)
                        (y \<Ztypecolon> \<phi>perm_transformer \<psi> U)
                        (w \<Ztypecolon> \<phi>perm_transformer \<psi> W)
       (Automatic_Morphism (RP \<and>\<^sub>\<r> \<phi>Sep_Disj R' U')
   (Structural_Extract' (y' \<Ztypecolon> \<phi>perm_transformer \<psi> U')
                        (w' \<Ztypecolon> \<phi>perm_transformer \<psi> W')
                        (x' \<Ztypecolon> \<phi>perm_transformer \<psi> T')
                        (r' \<Ztypecolon> \<phi>perm_transformer \<psi> R')
                        P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Morphism_def GOAL_CTXT_def Compact_Antecedent_def
  by (blast intro: Structural_Extract_\<phi>perm_transformer[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)



lemma Structural_Extract_\<phi>Optional_left
  [\<phi>reason 1200 for \<open>Structural_Extract (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C) ?R ?Y ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T ?\<^sub>\<phi> True) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  unfolding Structural_Extract'_def
  by simp

lemma Structural_Extract_\<phi>Optional_right:
  \<open> Structural_Extract Y W (x \<Ztypecolon> T) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract Y W (x \<Ztypecolon> T ?\<^sub>\<phi> True) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  unfolding Structural_Extract'_def
  by simp

lemma [\<phi>reason 1211 for \<open>Structural_Extract (?x \<Ztypecolon> ?T ?\<^sub>\<phi> ?C) ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T ?\<^sub>\<phi> True) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> T' ?\<^sub>\<phi> True) R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
 \<comment> \<open>If the mechanism requires to extract something nontrivial (note 1 and \<^term>\<open>() \<Ztypecolon> \<phi>None\<close>
      have been considered by more prior rule), claim the optional \<phi>-type.\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: Structural_Extract_\<phi>Optional_left [unfolded GOAL_CTXT_def]
                   Structural_Extract_\<phi>Optional_right[unfolded GOAL_CTXT_def]
                   Structural_Extract_imply_P)



paragraph \<open>Permission Node\<close>

text \<open>Then, according to the expected permission n and the permission m that we current have,
  there are 4 rules for 4 cases:
  \<^item> m is a schematic variable. let m to be n / 2. it means we only give a half what we have,
      and preserve another half for potential future demand.
  \<^item> m = n
  \<^item> m < n
  \<^item> m > n\<close>
(*
TODO: re-enable this! *)

lemma Structural_Extract_share_half
  [\<phi>reason 1300 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> half ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
    \<comment> \<open>if only requires a half of the permission, give it a half of that currently we have.\<close>
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half(m / 2) \<Znrres> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def Structural_Extract'_def half_def
  \<medium_left_bracket> premises [\<phi>reason] and X
    share_split_\<phi>app[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod]
    fold mult.assoc
    X[THEN implies_right_prod]
  \<medium_right_bracket>. .

lemma Structural_Extract_share_half_rev:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W) (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract'_def Structural_Extract_def GOAL_CTXT_def \<phi>Prod_expn'
  \<medium_left_bracket> premises [\<phi>reason] and X
  have t1: \<open>(r \<Ztypecolon> R) * (x \<Ztypecolon> m / 2 \<Znrres> T) * (y \<Ztypecolon> m / 2 \<Znrres> U) = (r \<Ztypecolon> R) * (y \<Ztypecolon> m / 2 \<Znrres> U) * (x \<Ztypecolon> m / 2 \<Znrres> T)\<close>
    by (metis (mono_tags, lifting) mult.assoc mult.commute)
  ;; unfold t1
     X[THEN implies_right_prod]
     share_merge_\<phi>app[where n=\<open>m/2\<close> and m=\<open>m/2\<close>, simplified, THEN implies_left_prod, folded mult.assoc]
  \<medium_right_bracket>. .


lemma
  [\<phi>reason 1311 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> half ?m \<Znrres> ?U) ?R2
      (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<phi>Sep_Disj_Identical T
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> m / 2 \<Znrres> T) (r \<Ztypecolon> R) (y \<Ztypecolon> m / 2 \<Znrres> U) (w \<Ztypecolon> W)
    (Automatic_Morphism RP
        (Structural_Extract (y' \<Ztypecolon> m / 2 \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m / 2 \<Znrres> T') (r' \<Ztypecolon> R') P')
    \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((x,r) \<Ztypecolon> m / 2 \<Znrres> T \<^emph> R) (y \<Ztypecolon> half (m / 2) \<Znrres> U) (w \<Ztypecolon> W)
    (Automatic_Morphism (RP \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical T')
        (Structural_Extract' (y' \<Ztypecolon> half (m / 2) \<Znrres> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> m \<Znrres> T') ((x',r') \<Ztypecolon> m / 2 \<Znrres> T' \<^emph> R') P')
    \<and> P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def GOAL_CTXT_def Compact_Antecedent_def half_def
  by (blast intro: Structural_Extract_share_half    [unfolded GOAL_CTXT_def half_def]
                   Structural_Extract_share_half_rev[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)



lemma Structural_Extract_share_eq
  [\<phi>reason 1200 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires exactly what we have now, typically this happens after the previous rule or n = 1.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m m = n
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn'[symmetric] Premise_def Structural_Extract'_def
  apply (simp add: \<phi>Share_\<phi>Prod[symmetric])
  using \<phi>Share_cast .

lemma [\<phi>reason 1211 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m m = n
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> m \<Znrres> W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> m \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: Structural_Extract_share_eq[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)



lemma Structural_Extract_share_ge
  [\<phi>reason 1180 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n \<and> n < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def Structural_Extract'_def \<phi>Prod_expn'
  \<medium_left_bracket> premises _ and LE[unfolded Premise_def, useful] and [\<phi>reason] and _ and X
    share_split_\<phi>app[where n=\<open>n\<close> and m=\<open>m-n\<close>, simplified]
    fold mult.assoc
    X[folded \<phi>Prod_expn', THEN \<phi>Share_cast, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
        THEN implies_right_prod]
  have t1: \<open>(r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U) * (x \<Ztypecolon> m - n \<Znrres> T) = (x \<Ztypecolon> m - n \<Znrres> T) * (r \<Ztypecolon> n \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    using mult.assoc mult.commute by blast
  ;; unfold t1
  \<medium_right_bracket>. .

lemma Structural_Extract_share_le
  [\<phi>reason 1170 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires more than what we have, give all what we can give.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < m \<and> m < n
\<Longrightarrow> \<phi>Sep_Disj_Identical U
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close>
  unfolding Structural_Extract_def \<phi>Prod_expn' Structural_Extract'_def
  \<medium_left_bracket> premises _ and LE[unfolded Premise_def, useful] and SDI[\<phi>reason] and _ and X
    X[folded \<phi>Prod_expn', THEN \<phi>Share_cast, unfolded \<phi>Share_\<phi>Prod \<phi>Prod_expn',
        THEN implies_left_prod, folded mult.assoc]
  
  have \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (y \<Ztypecolon> m \<Znrres> U) = (y \<Ztypecolon> n \<Znrres> U)\<close>
    using \<phi>Share_share[where n=\<open>n-m\<close> and m=m, simplified] \<phi>
    by (smt (verit) SDI)
  then have t1: \<open>(y \<Ztypecolon> n - m \<Znrres> U) * (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> m \<Znrres> U) = (r \<Ztypecolon> m \<Znrres> R) * (y \<Ztypecolon> n \<Znrres> U)\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute)
  ;; unfold t1
  \<medium_right_bracket>. .



lemma [\<phi>reason 1183 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2
          (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<comment> \<open>If requires less than what we have, give it.\<close>
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < n \<and> n < m
\<Longrightarrow> \<phi>Sep_Disj_Identical T
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) ((r,x) \<Ztypecolon> (n \<Znrres> R \<^emph> (m-n) \<Znrres> T)) (y \<Ztypecolon> n \<Znrres> U) (w \<Ztypecolon> n \<Znrres> W)
      (Automatic_Morphism (RP \<and>\<^sub>\<r> (\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m m-n = mn) \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical T')
        (Structural_Extract' (y' \<Ztypecolon> n \<Znrres> U') (w' \<Ztypecolon> n \<Znrres> W') (x' \<Ztypecolon> m \<Znrres> T') ((r',x') \<Ztypecolon> (n \<Znrres> R' \<^emph> mn \<Znrres> T')) P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Compact_Antecedent_def GOAL_CTXT_def Premise_def
  by (blast intro: Structural_Extract_share_ge[unfolded GOAL_CTXT_def]
                   Structural_Extract_share_le[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)

lemma [\<phi>reason 1173 for \<open>Structural_Extract' (?x \<Ztypecolon> ?n \<Znrres> ?T) ?R (?y \<Ztypecolon> ?m \<Znrres> ?U) ?R2 (Automatic_Morphism ?RP ?RX \<and> ?P)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> CHK_SUBGOAL G
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m 0 < m \<and> m < n
\<Longrightarrow> \<phi>Sep_Disj_Identical U
\<Longrightarrow> \<r>Feasible
\<Longrightarrow> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> m \<Znrres> T) (r \<Ztypecolon> m \<Znrres> R) (y \<Ztypecolon> n \<Znrres> U) ((w,y) \<Ztypecolon> m \<Znrres> W \<^emph> (n-m) \<Znrres> U)
      (Automatic_Morphism (RP \<and>\<^sub>\<r> (\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m nm = n - m) \<and>\<^sub>\<r> \<phi>Sep_Disj_Identical U')
        (Structural_Extract' (y' \<Ztypecolon> n \<Znrres> U') ((w',y') \<Ztypecolon> m \<Znrres> W' \<^emph> nm \<Znrres> U') (x' \<Ztypecolon> m \<Znrres> T') (r' \<Ztypecolon> m \<Znrres> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep,'bb) \<phi>\<close>
  unfolding Morphism_def Compact_Antecedent_def GOAL_CTXT_def Premise_def
  by (blast intro: Structural_Extract_share_ge[unfolded GOAL_CTXT_def]
                   Structural_Extract_share_le[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)


paragraph \<open>Normalization for Permission\<close>

subparagraph \<open>Extract each component in a composite structure, step by step\<close>

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>Prod .

lemma [\<phi>reason 2011 for
    \<open>Structural_Extract ?X ?R ((?x,?y) \<Ztypecolon> ?n \<Znrres> (?T \<^emph> ?U)) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> T' \<^emph> n \<Znrres> U') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W
      (Automatic_Morphism RP (Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> (T' \<^emph> U')) W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj GOAL_CTXT_def Premise_def \<phi>Share_\<phi>Prod
  by blast

lemma [\<phi>reason 2011 for
    \<open>Structural_Extract ((?x,?y) \<Ztypecolon> ?n \<Znrres> (?T \<^emph> ?U)) ?W ?X ?R (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> T' \<^emph> n \<Znrres> U') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> T \<^emph> n \<Znrres> U) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract ((x',y') \<Ztypecolon> n \<Znrres> (T' \<^emph> U')) W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R ((x,y) \<Ztypecolon> n \<Znrres> (T \<^emph> U)) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_semimodule_sep, 'b) \<phi>\<close> and T' :: \<open>('aa::share_semimodule_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj GOAL_CTXT_def Premise_def \<phi>Share_\<phi>Prod
  by blast



lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt .

lemma [\<phi>reason 2011 for \<open>Structural_Extract ?X ?R (?x \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow> ?T) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close> ]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj GOAL_CTXT_def Premise_def \<phi>Share_\<phi>MapAt
  by blast

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x' \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow> ?T') ?W' ?X' ?R' (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract (x' \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow> n \<Znrres> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('a::share_module_sep,'b) \<phi>\<close> and T' :: \<open>('aa::share_module_sep,'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj GOAL_CTXT_def Premise_def \<phi>Share_\<phi>MapAt
  by blast



lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract X R (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close>
  unfolding \<phi>Share_\<phi>MapAt_L .

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?R ?Y ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) R Y W
      (Automatic_Morphism RP (Structural_Extract Y' W' (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj GOAL_CTXT_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast

lemma [\<phi>reason 2011 for \<open>Structural_Extract ?Y ?W (?x \<Ztypecolon> ?n \<Znrres> ?k \<^bold>\<rightarrow>\<^sub>@ ?T) ?R (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> Structural_Extract Y' W' (x' \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> k \<^bold>\<rightarrow>\<^sub>@ n \<Znrres> T) R Y W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract Y' W' (x' \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> n \<Znrres> k \<^bold>\<rightarrow>\<^sub>@ T) R Y W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  for T :: \<open>('k list \<Rightarrow> 'a::share_module_sep, 'b) \<phi>\<close> and T' :: \<open>('k list \<Rightarrow> 'aa::share_module_sep, 'bb) \<phi>\<close>
  unfolding Morphism_def atomize_imp atomize_conj GOAL_CTXT_def Premise_def \<phi>Share_\<phi>MapAt_L
  by blast





lemma [\<phi>reason 2000]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2000]:
  \<open> Structural_Extract (x \<Ztypecolon> n * m \<Znrres> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) R Y W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def GOAL_CTXT_def
  by (metis Implication_Inhabited_rule Imply_def \<phi>Share_\<phi>Share \<phi>Share_inhabited set_mult_inhabited)

lemma [\<phi>reason 2011 for \<open>Structural_Extract ?X ?R (?x \<Ztypecolon> ?n \<Znrres> ?m \<Znrres> ?T) ?W (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n * m \<Znrres> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W
      (Automatic_Morphism RP (Structural_Extract (x' \<Ztypecolon> n \<Znrres> m \<Znrres> T') W' X' R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x \<Ztypecolon> ?n \<Znrres> ?m \<Znrres> ?T) ?W ?X ?R (Automatic_Morphism ?RP ?RX \<and> ?P)\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < n \<and> 0 < m
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n * m \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n * m \<Znrres> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x' \<Ztypecolon> n \<Znrres> m \<Znrres> T') W' X' R'
      (Automatic_Morphism RP (Structural_Extract X R (x \<Ztypecolon> n \<Znrres> m \<Znrres> T) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Premise_def by simp



text \<open>After all of these normalization, if we encounter the requirement to extract permission n,
  but there is no permission annotation for the current object, we know it is to extract from
  a total permission.\<close>

lemma Structural_Extract_pad_share_left
  [\<phi>reason 2000 for \<open>Structural_Extract (?x \<Ztypecolon> ?T) ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp

lemma Structural_Extract_pad_share_right
  [\<phi>reason 2000 for \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x \<Ztypecolon> ?T) ?R ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (y \<Ztypecolon> n \<Znrres> U) W (x \<Ztypecolon> 1 \<Znrres> T) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (y \<Ztypecolon> n \<Znrres> U) W (x \<Ztypecolon> T) R P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp


lemma [\<phi>reason 2011 for \<open>Structural_Extract (?x \<Ztypecolon> ?T) ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> 1 \<Znrres> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> T') R' P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp

lemma [\<phi>reason 2011 for \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x \<Ztypecolon> ?T) ?R (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>Structural_Extract (?y \<Ztypecolon> ?n \<Znrres> ?U) ?W (?x' \<Ztypecolon> ?m \<Znrres> ?T') ?R (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> 1 \<Znrres> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> 1 \<Znrres> T) R (y \<Ztypecolon> n \<Znrres> U) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract (y' \<Ztypecolon> n \<Znrres> U') W' (x' \<Ztypecolon> T') R'
      (Automatic_Morphism RP (Structural_Extract (x \<Ztypecolon> T) R (y \<Ztypecolon> n \<Znrres> U) W P) \<and> P')
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  by simp



subsection \<open>Actions\<close>





section \<open>Tools for Constructing Semantic Instructions and for Reasoning them\<close>

subsection \<open>Definitions of Elementary Constructions\<close>

context \<phi>empty_sem begin

definition \<phi>M_assert :: \<open>bool \<Rightarrow> (unit,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_assert P = (\<lambda>s. if P then Return \<phi>V_none s else {Invalid})\<close>

definition \<phi>M_assume :: \<open>bool \<Rightarrow> (unit,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_assume P = (\<lambda>s. if P then Return \<phi>V_none s else {PartialCorrect})\<close>

definition \<phi>M_getV_raw :: \<open>('VAL \<Rightarrow> 'v) \<Rightarrow> 'VAL sem_value \<Rightarrow> ('v \<Rightarrow> ('y,'ex,'RES_N,'RES) proc) \<Rightarrow> ('y,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV_raw VDT_dest v F = F (VDT_dest (dest_sem_value v))\<close>

definition \<phi>M_getV :: \<open>'TY \<Rightarrow> ('VAL \<Rightarrow> 'v) \<Rightarrow> 'VAL sem_value \<Rightarrow> ('v \<Rightarrow> ('y,'ex,'RES_N,'RES) proc) \<Rightarrow> ('y,'ex,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV TY VDT_dest v F =
    (\<phi>M_assert (dest_sem_value v \<in> Well_Type TY) \<ggreater> F (VDT_dest (dest_sem_value v)))\<close>

definition \<phi>M_caseV :: \<open>('VAL sem_value \<Rightarrow> ('vr,'ret,'ex,'RES_N,'RES) proc') \<Rightarrow> ('VAL \<times> 'vr,'ret,'ex,'RES_N,'RES) proc'\<close>
  where \<open>\<phi>M_caseV F = (\<lambda>arg. case arg of sem_value (a1,a2) \<Rightarrow> F (sem_value a1) (sem_value a2))\<close>

end

subsection \<open>Reasoning for Elementary Constructions\<close>

context \<phi>empty begin

declare \<phi>SEQ[\<phi>reason!]

lemma \<phi>M_assert[\<phi>reason! for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_assert ?P \<lbrace> ?A \<longmapsto> ?B \<rbrace>\<close>]:
  \<open>(Inhabited X \<Longrightarrow> P) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_assert P \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_assert_def Return_def det_lift_def
  by (clarsimp simp add: \<phi>expns Inhabited_def, blast)

lemma \<phi>M_assert_True[simp]:
  \<open>\<phi>M_assert True = Return \<phi>V_none\<close>
  unfolding \<phi>M_assert_def by simp

lemma \<phi>M_assert':
  \<open>P \<Longrightarrow> Q (F args) \<Longrightarrow> Q ((\<phi>M_assert P \<ggreater> F) args)\<close>
  unfolding \<phi>M_assert_def bind_def Return_def det_lift_def by simp

lemma \<phi>M_assume[\<phi>reason!]:
  \<open>(P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (\<phi>M_assume P \<ggreater> F) \<lbrace> X \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def \<phi>M_assume_def bind_def Return_def det_lift_def
  by clarsimp

lemma \<phi>M_tail_left:  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_tail_right: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. 1 \<heavy_comma> Y v \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_tail_right_right: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. Y v\<heavy_comma> 1 \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_detail_left[\<phi>reason 2200000]:  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace>\<close> by simp
lemma \<phi>M_detail_right[\<phi>reason 2200000]: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> Y \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> X \<longmapsto> \<lambda>v. 1\<heavy_comma> Y v \<rbrace>\<close> by simp


lemma \<phi>M_getV_raw[\<phi>reason!]:
   \<open>(v \<in> (x \<Ztypecolon> A) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_raw VDT_dest (sem_value v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (sem_value v) A \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_raw_def Premise_def
  by (clarsimp simp add: \<phi>expns Subjection_simp_proc_arg)

declare \<phi>M_getV_raw[where X=1, simplified, \<phi>reason!]

lemma \<phi>M_getV[\<phi>reason!]:
   \<open>(v \<in> (x \<Ztypecolon> A) \<Longrightarrow> <\<phi>expn> v \<in> Well_Type TY)
\<Longrightarrow> \<r>Cut
\<Longrightarrow> (v \<in> (x \<Ztypecolon> A) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV TY VDT_dest (sem_value v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (sem_value v) A \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_def Premise_def
  by (clarsimp simp add: \<phi>expns Subjection_simp_proc_arg)

declare \<phi>M_getV[where X=1, simplified, \<phi>reason!]

lemma \<phi>M_caseV[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F va vb \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_caseV F (\<phi>V_pair va vb) \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_caseV_def \<phi>V_pair_def by simp

lemma \<phi>M_Success[\<phi>reason!]:
  \<open> <\<phi>expn> v \<in> (y \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return (sem_value v) \<lbrace> X \<longmapsto> \<lambda>u. X\<heavy_comma> y \<Ztypecolon> Val u T \<rbrace> \<close>
  unfolding \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: \<phi>expns)

declare \<phi>M_Success[where X=1, simplified, \<phi>reason!]

lemma \<phi>M_Success'[\<phi>reason 1100000 for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> ?X \<longmapsto> ?X' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace>\<close>]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace> \<close>
  unfolding Return_def \<phi>Procedure_def det_lift_def by (clarsimp simp add: \<phi>expns)

end


subsection \<open>Elementary Constructions for Reasoning underlying Fictional Separation Logic\<close>

context \<phi>resource_sem begin

definition \<phi>Res_Spec :: \<open>('RES_N, 'RES) assn \<Rightarrow> ('RES_N, 'RES) assn\<close>
  where \<open>\<phi>Res_Spec P = (Valid_Resource \<inter> P)\<close>

lemma \<phi>Res_Spec_0[iff]:
  \<open>\<phi>Res_Spec {} = {}\<close>
  \<open>\<phi>Res_Spec 0 = {}\<close>
  unfolding \<phi>Res_Spec_def by (simp add: zero_set_def)+

lemma \<phi>Res_Spec_1[iff]:
  \<open>\<phi>Res_Spec 1 = 1\<close>
  unfolding \<phi>Res_Spec_def by (simp add: set_eq_iff; blast)

lemma \<phi>Res_Spec_mult_homo:
  \<open>\<phi>Res_Spec (A * B) = \<phi>Res_Spec A * \<phi>Res_Spec B\<close>
  unfolding \<phi>Res_Spec_def
  by (clarsimp simp add: set_eq_iff times_set_def; rule; clarsimp simp add: Valid_Resource_mult_homo; blast)

lemma \<phi>Res_Spec_subj[iff]:
  \<open> \<phi>Res_Spec (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (\<phi>Res_Spec S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<close>
  unfolding \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Spec_subj_\<S>:
  \<open> P
\<Longrightarrow> res \<subseteq> \<S> S E
\<Longrightarrow> res \<subseteq> (\<S> (\<lambda>v. S v \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) E)\<close>
  by (clarsimp simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Spec_ex[iff]:
  \<open> \<phi>Res_Spec (ExSet S) = (\<exists>*x. \<phi>Res_Spec (S x))\<close>
  unfolding \<phi>Res_Spec_def by (simp add: \<phi>expns set_eq_iff)

lemma \<phi>Res_Spec_ex_\<S>:
  \<open> res \<subseteq> \<S> (S x) E
\<Longrightarrow> res \<subseteq> (\<S> (\<lambda>v. (\<exists>*x. S x v)) E)\<close>
  apply (clarsimp simp add: \<phi>expns set_eq_iff subset_iff)
  subgoal for x by (cases x; clarsimp simp add: \<phi>expns set_eq_iff subset_iff; blast) .

end


lemma (in \<phi>spec) \<phi>INTERP_RES_\<phi>Res_Spec:
  \<open>res \<in> INTERP_RES fic \<longleftrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP fic) \<and> Fic_Space fic\<close>
  unfolding In_INTERP_RES \<phi>Res_Spec_def by simp blast

lemma (in \<phi>spec) \<phi>Procedure_\<phi>Res_Spec:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<longleftrightarrow> (\<forall>r res. res \<in> \<phi>Res_Spec (\<I> INTERP (r * p) \<^bold>s\<^bold>u\<^bold>b\<^bold>j p. p \<in> P \<and> Fic_Space (r * p) \<and> r ## p)
      \<longrightarrow> f res \<subseteq> \<S> (\<lambda>v. \<phi>Res_Spec (\<I> INTERP (r * q) \<^bold>s\<^bold>u\<^bold>b\<^bold>j q. q \<in> Q v \<and> Fic_Space (r * q) \<and> r ## q))
                    (\<lambda>v. \<phi>Res_Spec (\<I> INTERP (r * e) \<^bold>s\<^bold>u\<^bold>b\<^bold>j e. e \<in> E v \<and> Fic_Space (r * e) \<and> r ## e)))\<close>
  apply rule
   apply (unfold \<phi>Procedure_alt INTERP_SPEC \<phi>Res_Spec_def subset_iff)
   apply (clarsimp simp add: times_set_def \<phi>expns In_INTERP_RES)
  thm In_INTERP_RES
  subgoal premises prems for r res s c proof-
    have t1: \<open>(\<exists>fic. (\<exists>y. fic = r * y \<and> y \<in> P \<and> r ## y) \<and> res \<in> Valid_Resource \<and> Fic_Space fic \<and> res \<in> \<I> INTERP fic)\<close>
      using Fic_Space_Un prems by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=res], THEN spec[where x=r], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> f res\<close>])
      apply (cases s; clarsimp simp add: \<phi>expns In_INTERP_RES)
      apply force
      using Fic_Space_Un by blast
  qed
  apply (clarsimp simp add: times_set_def \<phi>expns In_INTERP_RES)
  subgoal premises prems for res r s c proof-
    have t1: \<open>res \<in> Valid_Resource \<and> (\<exists>c. res \<in> \<I> INTERP (r * c) \<and> c \<in> P \<and> Fic_Space (r * c) \<and> r ## c)\<close>
      using prems Fic_Space_Un by blast
    show ?thesis
      apply (insert prems(1)[THEN spec[where x=r], THEN spec[where x=res], THEN mp, OF t1,
              THEN spec[where x=s], THEN mp, OF \<open>s \<in> _\<close>])
      apply (cases s; simp add: \<phi>expns In_INTERP_RES)
      using Fic_Space_Un apply blast
      using Fic_Space_Un by blast
  qed .



paragraph \<open>Weakest Precondition Transformer for \<phi>Res_Spec\<close>

lemma (in \<phi>resource_sem) \<phi>M_RS_WP_SEQ[\<phi>reason!]:
  \<open> F res \<subseteq> \<S> P E
\<Longrightarrow> (\<And>ret res. res \<in> P ret \<Longrightarrow> G ret res \<subseteq> \<S> Q E)
\<Longrightarrow> (F \<bind> G) res \<subseteq> \<S> Q E\<close>
  unfolding bind_def subset_iff
  apply clarsimp subgoal for s s'
    by (cases s'; simp; cases s; clarsimp ; blast) .


section \<open>Predefined Resource Snippet\<close>

subsection \<open>Minimal Resource\<close>

locale resource =
  resource_kind entry
+ \<phi>resource_sem Resource_Validator
for entry :: "('RES_N, 'RES::sep_algebra, 'T::sep_algebra) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
+ fixes Valid :: \<open>'T set\<close>
  assumes Valid_1: \<open>1 \<in> Valid\<close>
  assumes Resource_Validator[simp]: \<open>Resource_Validator name = inject ` Valid\<close>
begin

lemma \<r>_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    clean res \<in> Valid_Resource \<and> (\<exists>m. res name = inject m \<and> m \<in> Valid)\<close>
  by (subst split, simp add: Valid_Resource_def times_fun_def image_iff Valid_1, blast)

lemma \<r>_valid_split': \<open>
  NO_MATCH (clean res') res
\<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow> clean res \<in> Valid_Resource \<and> (\<exists>m. res name = inject m \<and> m \<in> Valid)\<close>
  using \<r>_valid_split .

lemma get_res_valid_raw:
  \<open> res \<in> Valid_Resource
\<Longrightarrow> get res \<in> Valid\<close>
  unfolding Valid_Resource_def
  apply simp
  subgoal premises prems
    using prems(1)[THEN spec[where x=name], simplified Resource_Validator]
    by fastforce .

lemma get_res_Valid:
  \<open> res \<in> \<phi>Res_Spec S
\<Longrightarrow> (get res) \<in> Valid\<close>
  unfolding \<phi>Res_Spec_def by (clarsimp simp add: \<r>_valid_split')


definition \<open>raw_basic_fiction I = Interp (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x })\<close>
lemma raw_basic_fiction_\<I>:
  "\<I> (raw_basic_fiction I) = (\<lambda>x. { 1(entry #= y) |y. y \<in> \<I> I x})"
  unfolding raw_basic_fiction_def
  by (rule Interp_inverse) (clarsimp simp add: Interpretation_def one_set_def)

lemma \<F>_itself_expn[\<phi>expns]:
  \<open>R2 ## x
\<Longrightarrow> \<phi>Res_Spec (\<I> (raw_basic_fiction \<F>_it) (R2 * x))
  = \<phi>Res_Spec (\<I> (raw_basic_fiction \<F>_it) R2) * \<phi>Res_Spec {mk x}\<close>
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: \<phi>expns raw_basic_fiction_\<I>)
  apply (rule; clarify)
   apply (simp add: mk_homo_mult sep_mult_assoc')
  using Valid_Resource_mult_homo sep_disj_mk apply blast
  using Valid_Resource_mult_homo inj_homo_mult by force

lemma implies_part:
  \<open> res \<in> R * \<phi>Res_Spec {mk x}
\<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L get res\<close>
  unfolding \<phi>Res_Spec_def join_sub_def times_set_def apply clarsimp
  using get_homo_mult by fastforce

end


subsection \<open>Resources using Fine\<close>

subsubsection \<open>Locale for Resource\<close>

subsubsection \<open>Basic Locale for Interp of Fine Resource\<close>

locale basic_fiction =
  \<phi>spec Resource_Validator INTERPRET
+  R: resource Res Resource_Validator Valid
+  fictional_project_inject INTERPRET Fic \<open>R.raw_basic_fiction I\<close>
for Valid :: "'T::sep_algebra set"
and I :: "('U::sep_algebra, 'T) interp"
and Res :: "('RES_N, 'RES::sep_algebra, 'T) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
and Fic :: "('FIC_N,'FIC::sep_algebra,'U) Virtual_Datatype.Field"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra, 'RES_N \<Rightarrow> 'RES) interp"
begin

paragraph \<open>\<phi>-Type\<close>

definition \<phi> :: \<open>('U, 'x) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'x) \<phi>\<close>
    \<comment> \<open>\<phi>Type for level-1 mapping\<close>
  where \<open>\<phi> T = (\<lambda>x. { mk v |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma \<phi>_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = mk v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>_def by simp

lemma \<phi>_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>_Prod:
  \<open> \<phi> T \<^emph> \<phi> U = \<phi> (T \<^emph> U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis mk_homo_mult)
  by (metis fun_1upd_homo inj.homo_mult sep_disj_mk)

lemma \<phi>_\<phi>None:
  \<open>\<phi> \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = (() \<Ztypecolon> \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp

lemma [\<phi>reason 1300 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = 1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp


lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> \<phi>None_simps\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = (() \<Ztypecolon> \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> \<phi>None_simps\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp


lemma [\<phi>reason 1500 for \<open>(x \<Ztypecolon> \<phi> \<circle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'act::simplification action)\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (() \<Ztypecolon> \<circle>) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close>
  for Act :: \<open>'act::simplification action\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None
  by (simp add: implies_refl)

paragraph \<open>Reasoning Rules\<close>

lemma \<phi>_cast:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi> U \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns)

lemma \<phi>_Structural_Extract[\<phi>reason 1200 for
  \<open>Structural_Extract' (?x \<Ztypecolon> \<phi> ?T) ?R (?y \<Ztypecolon> \<phi> ?U) ?W ?P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W) P  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Structural_Extract_def Structural_Extract'_def
  by (simp add: \<phi>Prod_expn'[symmetric] \<phi>_Prod \<phi>_cast)

lemma [\<phi>reason 1211 for
  \<open>Structural_Extract' (?x \<Ztypecolon> \<phi> ?T) ?R (?y \<Ztypecolon> \<phi> ?U) ?W (Automatic_Morphism ?RP ?RX \<and> ?P) \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  \<open> Structural_Extract  (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> Structural_Extract' (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W)
      (Automatic_Morphism RP (Structural_Extract' (y' \<Ztypecolon> \<phi> U') (w' \<Ztypecolon> \<phi> W') (x' \<Ztypecolon> \<phi> T') (r' \<Ztypecolon> \<phi> R') P') \<and> P)
    \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding Morphism_def GOAL_CTXT_def
  by (blast intro: \<phi>_Structural_Extract[unfolded GOAL_CTXT_def]
                   Structural_Extract'_imply_P)

lemma ToSA_by_structural_extraction:
  " Structure_Info U Q
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y Q' : Q
\<Longrightarrow> SUBGOAL G G2
\<Longrightarrow> (Q' \<Longrightarrow> Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W P2)  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G2)
\<Longrightarrow> SOLVE_SUBGOAL G2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> R2 \<heavy_comma> \<blangle> W \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<heavy_comma> y \<Ztypecolon> \<phi> U \<longmapsto> R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Premise_def GOAL_CTXT_def FOCUS_TAG_def Structural_Extract_def Simplify_def Action_Tag_def Try_def
  \<medium_left_bracket> premises SI and Q and _ and SE and _ and A
    have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
    ;; A[THEN \<phi>frame_view_right]
       SE[THEN mp, OF \<open>Q'\<close>]
  \<medium_right_bracket>
  using \<phi>
  by simp
  .

lemma ToSA_by_structural_extraction__reverse_morphism:
  " Structure_Info U Q
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y Q' : Q
\<Longrightarrow> SUBGOAL G G2
\<Longrightarrow> (Q' \<Longrightarrow> Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W
              (Automatic_Morphism RP2 (Structural_Extract (x' \<Ztypecolon> \<phi> T') W' (y' \<Ztypecolon> \<phi> U') R1' P2') \<and> P2))
            \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G2)
\<Longrightarrow> SOLVE_SUBGOAL G2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> R2 \<heavy_comma> \<blangle> W \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h (Automatic_Morphism RP1 (\<^bold>v\<^bold>i\<^bold>e\<^bold>w R2'\<heavy_comma> \<blangle> W' \<brangle> \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1') \<and> P1)
    \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<heavy_comma> y \<Ztypecolon> \<phi> U \<longmapsto> R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h
      (Automatic_Morphism (RP2 \<and>\<^sub>\<r> RP1) (\<^bold>v\<^bold>i\<^bold>e\<^bold>w R2'\<heavy_comma> R1'\<heavy_comma> \<blangle> x' \<Ztypecolon> \<phi> T' \<brangle> \<longmapsto> A'\<heavy_comma> y' \<Ztypecolon> \<phi> U' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1' \<and> P2') \<and> P1 \<and> P2)
    \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding Premise_def GOAL_CTXT_def FOCUS_TAG_def Structural_Extract_def Simplify_def
            Action_Tag_def Morphism_def Compact_Antecedent_def Try_def
  \<medium_left_bracket> premises SI and Q and _ and SE and _ and A
  have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
    ;; A[THEN \<phi>frame_view_right]
       SE[THEN mp, OF \<open>Q'\<close>]
  \<medium_right_bracket> apply (simp add: \<phi>)
  \<medium_left_bracket>
    have A : \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w R2' \<heavy_comma> W' \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1'\<close> using \<phi>_previous by simp
    have SE: \<open>(R1' \<heavy_comma> x' \<Ztypecolon> \<phi> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s W' \<heavy_comma> y' \<Ztypecolon> \<phi> U' \<^bold>a\<^bold>n\<^bold>d P2')\<close> using \<phi>_previous by simp
    ;; SE A[THEN \<phi>frame_view_right]
  \<medium_right_bracket>. . .


lemma ToSA_skip [\<phi>reason 1200
    for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?X \<longmapsto> ?R'\<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
    except \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<longmapsto> ?R'\<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
]:
  " \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R'\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> X \<longmapsto> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding cast_def split_paired_All Action_Tag_def
  by (smt (verit) \<phi>view_shift_intro_frame_R mult.assoc mult.commute)




lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> \<phi> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> (?Act::?'aa::{structural, implication} action)\<close>]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> \<phi> U \<^bold>a\<^bold>n\<^bold>d P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act \<close>
  for Act :: \<open>'aa::{structural, implication} action\<close>
  unfolding Action_Tag_def using \<phi>_cast .

lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> \<phi> T) \<close>
  unfolding \<r>Clean_def Imply_def apply (simp add: \<phi>expns)
  using mk_homo_one by blast

lemma [\<phi>reason 1200 for \<open>If ?P (\<phi> ?T) (\<phi> ?U) = (\<phi> ?Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>]:
  \<open> If P T U = Z \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence
\<Longrightarrow> If P (\<phi> T) (\<phi> U) = (\<phi> Z) \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> branch_convergence\<close>
  unfolding Action_Tag_def by fastforce

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>(\<phi> (ExTyp T)) = (\<exists>\<phi> c. \<phi> (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi> (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (\<phi> T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi> T) = (x' \<Ztypecolon> \<phi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>\<phi>_simp_cong ("x \<Ztypecolon> \<phi> T") = \<open>
  K (fn ctxt => NuSimpCong.simproc @{thm \<phi>_simp_cong} ctxt)
\<close>

paragraph \<open>Synthesis for moving\<close>

lemma [\<phi>reason 1200 for
  \<open>PROP Synthesis_Parse (\<phi> ?T) (?Y::?'ret \<Rightarrow> ('FIC_N,'FIC) assn)\<close>
]:
  \<open>PROP Synthesis_Parse (\<phi> T) (\<lambda>_. x \<Ztypecolon> \<phi> T :: ('FIC_N,'FIC) assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason for \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?S1 \<longmapsto> \<lambda>ret. ?S2\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> \<phi> ?T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> SUBGOAL G G'
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S1 \<longmapsto> S2\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G'
\<Longrightarrow> SOLVE_SUBGOAL G'
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> S1 \<longmapsto> \<lambda>_. S2\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<phi> T \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding GOAL_CTXT_def FOCUS_TAG_def Synthesis_def Action_Tag_def
  by (metis \<phi>__Return_rule__)

end


subsubsection \<open>Permission Interp\<close>

locale permission_fiction =
  \<phi>spec Resource_Validator INTERPRET
+  R: resource Res Resource_Validator Valid
+  share: perm_transformer perm_transformer
+  fictional_project_inject INTERPRET Fic
      \<open>R.raw_basic_fiction (\<F>_functional perm_transformer)\<close>
for Valid :: "'T::sep_algebra set"
and perm_transformer :: \<open>'T \<Rightarrow> 'U::{share_sep_disj,share_module_sep,sep_algebra}\<close>
and Res :: "('RES_N, 'RES::sep_algebra, 'T) Virtual_Datatype.Field"
and Resource_Validator :: "'RES_N \<Rightarrow> 'RES set"
and Fic :: "('FIC_N, 'FIC::sep_algebra, 'U) Virtual_Datatype.Field"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC, 'RES_N \<Rightarrow> 'RES) interp"
begin

sublocale basic_fiction Valid \<open>\<F>_functional perm_transformer\<close> ..

lemma sep_disj_fiction:
  \<open> Fic_Space r
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }
\<Longrightarrow> r ## mk (perm_transformer x)\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            share.sep_mult_strip_011 R.\<r>_valid_split'
            R.mult_strip_inject_011 interp_split' sep_disj_get_name_eq[symmetric]
            simp del: sep_disj_get_name_eq)
  using sep_disj_multD2 by force

lemma expand_subj:
  \<open> Fic_Space r
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_transformer x)) \<^bold>s\<^bold>u\<^bold>b\<^bold>j r ## mk (perm_transformer x))
  = \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify, rule)
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            share.sep_mult_strip_011 \<phi>Res_Spec_def R.\<r>_valid_split'
            R.mult_strip_inject_011 interp_split')
  subgoal for res_r a r'
    apply (rule exI[where x=\<open>res_r * R.mk a\<close>]; rule)
    apply (metis R.inj_homo_mult R.sep_disj_mk fun_1upd_homo_right1 sep_mult_assoc')
    by (metis R.get_homo_mult R.proj_inj R.sep_disj_get_name_eq fun_upd_same sep_disj_multD1 sep_disj_multI1)

  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns \<phi>Res_Spec_def R.\<r>_valid_split'
        R.mult_strip_inject_011 interp_split' sep_mult_assoc)
  subgoal premises prems for res_r a y proof -
    have t1[simp]: \<open>y ## x\<close>
      using prems(5) prems(7) sep_disj_multD2 by force

    show ?thesis
      apply rule
      apply (rule exI[where x=\<open>a\<close>], rule exI[where x=\<open>R.mk (y * x)\<close>])
      apply (metis R.inj_homo_mult fun_1upd_homo prems(5) prems(6) prems(7) sep_disj_multI2 share.homo_mult t1)
      by (metis prems(8) sep_disj_get_name_eq share.sep_disj_homo_semi t1)
      
  qed .

lemma expand:
  \<open>Fic_Space r
\<Longrightarrow> r ## mk (perm_transformer x)
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_transformer x))) =
    \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

lemma expand_conj:
  \<open> Fic_Space r
\<Longrightarrow> a \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_transformer x))) \<and> r ## mk (perm_transformer x)
\<longleftrightarrow> a \<in> \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, OF prems(1), unfolded set_eq_iff]
      by (simp add: \<phi>expns) .



lemma partial_implies_raw:
  \<open> Fic_Space r
\<Longrightarrow> 0 < n 
\<Longrightarrow> r ## mk (share n (perm_transformer x))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (share n (perm_transformer x))))
\<Longrightarrow> x \<preceq>\<^sub>S\<^sub>L R.get res\<close>
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            \<phi>Res_Spec_def R.\<r>_valid_split' R.mult_strip_inject_011
            R.proj_homo_mult interp_split')
  apply (cases \<open>n \<le> 1\<close>)
  apply (metis join_sub_def join_sub_ext_left sep_disj_get_name_eq share.join_sub_share_join_sub_whole)
  subgoal premises prems for u y a proof -
    have t0: \<open>1 / n * n = 1\<close> using prems(12) by force 
    have t1: \<open>1 / n \<le> 1 \<and> 0 < 1 / n\<close> using prems(12) by force
    have t2: \<open>share (1/n) (share n (perm_transformer x)) \<preceq>\<^sub>S\<^sub>L share n (perm_transformer x)\<close>
      by (simp add: order_less_imp_le prems(2) share.\<psi>_self_disj share_sub t1)
    then have t3: \<open>perm_transformer x \<preceq>\<^sub>S\<^sub>L share n (perm_transformer x)\<close>
      using share_share_not0
      by (metis prems(2) share_left_one t0 t1)
    then show ?thesis
      by (metis join_sub_ext_left prems(11) prems(3) prems(9) sep_disj_get_name_eq share.homo_join_sub)
  qed .

paragraph \<open>Reasoning Rules\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<longmapsto> ?R \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
    [\<phi>reason 1213 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<longmapsto> ?R \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h (Automatic_Morphism ?RP ?RX \<and> ?P)
                        \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]

end



(* lemma VS_merge_ownership:
  \<open> (\<forall>ua ub. ua \<in> (x \<Ztypecolon> T) \<and> ub \<in> (x \<Ztypecolon> T) \<and>
             can_share (perm_transformer ua) \<and> can_share (perm_transformer ub) \<and>
             share na (perm_transformer ua) ## share nb (perm_transformer ub) \<longrightarrow> ua = ub)
\<Longrightarrow> na + nb \<le> 1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> na T) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb T) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> (na + nb) T)\<close>
  unfolding View_Shift_def Premise_def
  apply (clarsimp simp add: \<phi>expns mult.assoc mk_homo_mult[symmetric] times_fine)
  subgoal for res R res_r res_xa res_xb
    apply (cases \<open>share na (perm_transformer res_xa) ## share nb (perm_transformer res_xb)\<close>;
           clarsimp simp add: fun_1upd_homo \<phi>INTERP_RES_\<phi>Res_Spec share_left_distrib)
    apply (rule exI[where x=\<open>res_r * mk (Fine (share (na + nb) (perm_transformer res_xb)))\<close>], simp)
    by (metis share_sep_left_distrib_0) .

lemma VS_split_ownership:
  \<open> (\<forall>u. u \<in> (x \<Ztypecolon> T) \<and> can_share (perm_transformer u) \<and> 0 < n \<and> na + nb \<le> 1
     \<longrightarrow> share na (perm_transformer u) ## share nb (perm_transformer u))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (0 < n \<longrightarrow> na + nb = n \<and> 0 < na \<and> 0 < nb)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> n T) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> na T) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb T)\<close>
  unfolding View_Shift_def Premise_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for res R res_r res_x
    apply (rule exI[where x=\<open>res_r * (mk (Fine (share na (perm_transformer res_x)))
                                    * mk (Fine (share nb (perm_transformer res_x))))\<close>],
           rule conjI, blast)
    by (clarsimp simp add: mk_homo_mult[symmetric] times_fine fun_1upd_homo share_sep_left_distrib_0) .
end*)

(* locale permission_fiction =
  \<phi>spec Resource_Validator INTERPRET
+  R: resource Res Resource_Validator Valid
+  fictional_project_inject INTERPRET Fic \<open>R.raw_basic_fiction I\<close>
for Valid :: "'T::comm_monoid_mult set"
and I :: "('U::{share,comm_monoid_mult}, 'T) interp"
and Res :: "('RES_N, 'RES::{comm_monoid_mult,no_inverse}, 'T) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult} set\<close>
and Fic :: "('FIC_N,'FIC::{no_inverse,comm_monoid_mult},'U) Virtual_Datatype.Field"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::{no_inverse,comm_monoid_mult},'RES_N \<Rightarrow> 'RES) interp"
+
fixes perm_transformer :: \<open>'T \<Rightarrow> 'U\<close>
  and R_dom :: \<open>'T set\<close>
assumes \<open>Fic_Space r
\<Longrightarrow> x \<in> R_dom
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (perm_transformer x)))
  = \<phi>Res_Spec (\<I> INTERP r * { R.mk x})\<close>

begin


end *)




subsubsection \<open>Identity Interp\<close>

locale identity_fiction =
   \<phi>spec Resource_Validator INTERPRET
+  R: resource Res Resource_Validator
+  fictional_project_inject INTERPRET Fic \<open>R.raw_basic_fiction \<F>_it\<close>
for Res :: "('RES_N, 'RES::sep_algebra, 'T::sep_algebra) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra, 'RES_N \<Rightarrow> 'RES) interp"
and Fic :: "('FIC_N,'FIC,'T) Virtual_Datatype.Field"
begin

sublocale basic_fiction where I = \<open>\<F>_it\<close> ..

lemma sep_disj_fiction:
  \<open> Fic_Space r
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec { R.mk x }
\<Longrightarrow> r ## mk x\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarsimp simp add: R.raw_basic_fiction_\<I> \<phi>expns
            \<phi>Res_Spec_def R.\<r>_valid_split'
            R.mult_strip_inject_011 interp_split'
            sep_disj_get_name_eq[symmetric]
            simp del: sep_disj_get_name_eq)
  using sep_disj_multD2 by force

lemma expand_subj:
  \<open> Fic_Space r
\<Longrightarrow> (\<phi>Res_Spec (\<I> INTERP (r * mk x)) \<^bold>s\<^bold>u\<^bold>b\<^bold>j r ## mk x) = \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def set_eq_iff
  apply (clarify; rule; clarsimp simp add: \<phi>expns R.raw_basic_fiction_\<I> interp_split')
  apply (simp add: R.mk_homo_mult)
  using R.sep_disj_mk sep_disj_get_name_eq sep_disj_multD1 sep_disj_multI1 sep_mult_assoc' apply blast
  apply (simp add: R.mk_homo_mult[symmetric] sep_mult_assoc)
  by (metis R.mk_homo_mult R.sep_disj_mk sep_disj_get_name_eq sep_disj_multD2 sep_disj_multI2)

lemma expand:
  \<open> Fic_Space r
\<Longrightarrow> r ## mk x
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk x)) = \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

declare ToSA_by_structural_extraction
   [\<phi>reason 1210 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<longmapsto> ?R \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
   [\<phi>reason 1213 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<longmapsto> ?R \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h (Automatic_Morphism ?RP ?RX \<and> ?P)
        \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]

end


subsection \<open>Nonsepable Mono-Resource\<close>
  \<comment> \<open>The resource non-sepable and having type shape \<^typ>\<open>'a::nonsepable_semigroup option\<close>\<close>

locale nonsepable_mono_resource =
  resource entry Resource_Validator \<open>{None} \<union> Some ` nonsepable ` Valid\<close>
for entry :: "('RES_N, 'RES::sep_algebra, 'T nonsepable option) Virtual_Datatype.Field"
and Resource_Validator :: "'RES_N \<Rightarrow> 'RES set"
and Valid :: "'T set"
begin

definition fiction_agree
  where \<open>fiction_agree = raw_basic_fiction (\<F>_optionwise \<F>_agree)\<close>

end


subsubsection \<open>Interp Agreement\<close>

locale agreement_fiction_for_nosepable_mono_resource =
   \<phi>spec Resource_Validator INTERPRET
+  R: nonsepable_mono_resource Res Resource_Validator Valid
+  fictional_project_inject INTERPRET Fic \<open>R.fiction_agree\<close>
for Valid :: "'T set"
and Res :: "('RES_N, 'RES::sep_algebra, 'T nonsepable option) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra,'RES_N \<Rightarrow> 'RES) interp"
and Fic :: "('FIC_N,'FIC, 'T nonsepable agree option) Virtual_Datatype.Field"
begin

sublocale basic_fiction \<open>{None} \<union> Some ` nonsepable ` Valid\<close>
  \<open>\<F>_optionwise \<F>_agree\<close>
  by (standard; simp add: R.fiction_agree_def)
                       
lemma partial_implies:
  \<open> Fic_Space r
\<Longrightarrow> r ## mk (Some (agree (nonsepable x)))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (Some (agree (nonsepable x)))))
\<Longrightarrow> R.get res = Some (nonsepable x)\<close>
  unfolding \<phi>Res_Spec_def apply (clarsimp simp add: interp_split'
     R.fiction_agree_def R.raw_basic_fiction_\<I> \<phi>expns R.\<r>_valid_split'
     R.mult_strip_inject_011 R.proj_homo_mult \<F>_optionwise_\<I> image_iff Bex_def
     \<F>_agree_def)
  apply (cases \<open>get r\<close>; simp)
  subgoal for u y a aa
    apply (cases aa; simp)
    subgoal premises prems for xa proof -
      have \<open>get r ## Some (agree (nonsepable x))\<close>
        by (simp add: prems(2))
      from this [unfolded \<open>get r = _\<close>, simplified]
      show ?thesis .
    qed . .

lemma VS_double:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w {mk x |x. P x} \<longmapsto> {mk x |x. P x} * {mk x |x. P x}\<close>
  unfolding View_Shift_def
  apply (clarsimp simp add: \<phi>expns mk_homo_mult[symmetric])
  subgoal for x R u x'
    apply (cases x'; simp)
    apply (metis fun_1upd1 inj_homo_one mult_1_class.mult_1_left one_option_def sep_magma_1_right)
    subgoal for a by (rule exI[where x=\<open>u * mk (Some a)\<close>]; simp
                ; rule exI[where x=u]; rule exI[where x=\<open>mk (Some a)\<close>]; simp
                ; rule exI[where x=\<open>mk (Some a)\<close>]; rule exI[where x=\<open>mk (Some a)\<close>]
                ; simp add: mk_homo_mult[symmetric]) . .

lemma VS_contract:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w {mk x |x. P x} * {mk x |x. P x} \<longmapsto> {mk x |x. P x} \<close>
  unfolding View_Shift_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for x R u xa xb
    apply (cases xa; cases xb; simp)
    apply (metis fun_split_1 fun_upd_triv inj_homo_one mk_homo_one one_option_def)
    apply (metis mk_homo_one mult_1_class.mult_1_left one_option_def)
     apply (metis fun_1upd1 inj_homo_one mult_1_class.mult_1_right one_option_def)
    subgoal for a b
      by (cases \<open>a ## b\<close>; simp; cases a; cases b; simp add: mk_homo_mult[symmetric]; blast) . .

paragraph \<open>\<phi>-Type\<close>

abbreviation \<open>\<phi>_ag T \<equiv> \<phi> (Agreement (Nonsepable T))\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<longmapsto> ?R \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
    [\<phi>reason 1213 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?A \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<longmapsto> ?R \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h (Automatic_Morphism ?RP ?RX \<and> ?P)
        \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]

lemma \<phi>_double_\<phi>app:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi>_ag T \<longmapsto> x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nonsepable v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: VS_double)
qed

lemma \<phi>_contract_\<phi>app:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T \<longmapsto> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nonsepable v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: VS_contract)
qed

end



subsection \<open>Resources based on Mapping\<close>

locale mapping_resource =
  resource entry Resource_Validator
for entry :: "('RES_N, 'RES::sep_algebra, ('key \<Rightarrow> 'val::sep_algebra)) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
begin

lemma "__new_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> k \<notin> dom1 (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> updt (\<lambda>f. f(k := u)) res
       \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := u))}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd)
  subgoal premises prems for m proof -
    {
      assume A: \<open>k \<notin> dom1 m\<close>
      have t2: \<open>m ## 1(k := u)\<close>
        using A dom1_def sep_disj_fun_def by fastforce
      have t3: \<open>res(name := inject m) = res\<close>
        by (simp add: fun_upd_idem prems(5))
      have t1: \<open>res(name := inject (m(k := u))) = res * mk (1(k := u)) \<and> res ## mk (1(k := u))\<close>
        thm fun_split_1_not_dom1[where f=m]
        apply (subst fun_split_1_not_dom1[where k=k]) using A apply this
        apply (simp add: t2 inj.homo_mult split)
        by (metis fun_1upd_homo_right1 prems(5) proj_inj sep_disj_get_name_eq t2 t3)
    }
    then show ?thesis
      using prems(2) prems(4) by blast
  qed .

end

subsection \<open>One Level Parital Mapping\<close>

subsubsection \<open>Locale for Resource\<close>

locale partial_map_resource =
  mapping_resource Valid entry Resource_Validator
for Valid :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) set"
and entry :: "('RES_N, 'RES::sep_algebra, 'key \<Rightarrow> 'val::nonsepable_semigroup option) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k \<mapsto> any))}
\<Longrightarrow> updt (\<lambda>f. f(k := u)) res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := u))}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd )
  apply (clarsimp simp add: sep_disj_partial_map_upd
          nonsepable_semigroup_sepdisj_fun mk_homo_mult)
  subgoal premises prems for x aa proof -
    have t1: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(8))
    have t2: \<open>clean x ## (mk aa * mk (1(k := u)))\<close>
      by (simp add: fun_1upd_homo)
    show ?thesis
      by (metis nonsepable_semigroup_sepdisj_fun prems(6) prems(9) sep_disj_mk sep_disj_multI1 sep_mult_assoc' t1 t2)
  qed .

lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k \<mapsto> any))}
\<Longrightarrow> updt (\<lambda>f. f(k := None)) res \<in> \<phi>Res_Spec R\<close>
  using "__updt_rule__"[where u=None, simplified, simplified,
            simplified, simplified one_set_def[symmetric], simplified] .

abbreviation perm_transformer :: \<open>('key \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'val share option)\<close>
  where \<open>perm_transformer \<equiv> (o) to_share\<close>
abbreviation \<open>share_fiction \<equiv> raw_basic_fiction (\<F>_functional perm_transformer)\<close>

(* lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> 1 \<Znrres> v))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k \<mapsto> v)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011)
  subgoal premises prems for res_r y a r
    apply (insert \<open>a * _ = _\<close>[unfolded to_share_strip_011[where b=\<open>1(k \<mapsto> v)\<close>, simplified, OF \<open>a ## _\<close>]])
    apply (clarsimp simp add: times_fine'[symmetric] mk_homo_mult mult.assoc[symmetric])
    using prems(3) by blast
  subgoal premises prems for res_r a r proof -
    have t1[simp]: \<open>a ## 1(k \<mapsto> v)\<close>
      by (metis prems(6) prems(7) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
    show ?thesis
    apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine')
      apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k \<mapsto> v)))"], simp add: prems)
      by (metis (no_types, lifting) map_option_o_map_upd t1 to_share_funcomp_1 to_share_funcomp_sep_disj_I to_share_strip_011)
  qed .


lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> n \<Znrres> v))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011
            proj_homo_mult)
  subgoal premises prems for res_r y a r proof -
    from \<open>a * _ = _\<close>[THEN fun_cong[where x=k], simplified times_fun, simplified]
    have t1: \<open>y k = Some v\<close>
      using prems(6) prems(7) strip_share_fun_mult by force
    then show ?thesis apply (simp add: t1 times_fun)
      using prems(9) sep_disj_partial_map_some_none t1 by fastforce
  qed .

lemma
  assumes A: \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k \<mapsto> n \<Znrres> v))))\<close>
  shows share_fiction_partially_implies'[simp]: \<open>!!( get res) k = Some v\<close>
proof -
  from A[THEN share_fiction_partially_implies]
  show ?thesis by fastforce
qed
*)
lemma raw_unit_assertion_implies[simp]:
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k \<mapsto> v))}
\<Longrightarrow> get res k = Some v\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011
      proj_homo_mult sep_disj_fun_def times_fun)
  by (metis (mono_tags, lifting) sep_disj_option_nonsepable(1) sep_mult_commute times_option(2))


end


subsubsection \<open>Sharing Interp\<close>

locale share_fiction_for_partial_mapping_resource =
   \<phi>resource_sem Resource_Validator
+  R: partial_map_resource Valid Res Resource_Validator
+  fictional_project_inject INTERPRET Fic \<open>R.share_fiction\<close>
+  \<phi>spec Resource_Validator INTERPRET
for Valid :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) set"
and Res :: "('RES_N, 'RES::sep_algebra, 'key \<Rightarrow> 'val option) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra,'RES_N \<Rightarrow> 'RES) interp"
and Fic :: "('FIC_N,'FIC, 'key \<Rightarrow> 'val share option) Virtual_Datatype.Field"
begin

sublocale permission_fiction Valid \<open>R.perm_transformer\<close> by standard blast

lemma expand:
  \<open>Fic_Space r
\<Longrightarrow> r ## mk (R.perm_transformer x)
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (R.perm_transformer x))) =
    \<phi>Res_Spec (\<I> INTERP r) * \<phi>Res_Spec {R.mk x}\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

lemma partial_implies:
  \<open> Fic_Space r
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k \<mapsto> Share n v))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k \<mapsto> Share n v))))
\<Longrightarrow> R.get res k = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k \<mapsto> v)\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, ccfv_threshold) fun_split_1 fun_upd_same join_sub_def one_option_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep)

lemma partial_implies'[simp]:
  assumes FS: \<open>Fic_Space r\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k \<mapsto> Share n v))\<close>
    and A: \<open>res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k \<mapsto> Share n v))))\<close>
  shows \<open>R.get res k = Some v\<close>
proof -
  from partial_implies[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

(* lemma VS_merge_ownership_identity:
  \<open> na + nb \<le> 1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> (na + nb) Identity)\<close>
  by (rule VS_merge_ownership; simp add: \<phi>expns)

lemma VS_split_ownership_identity:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (0 < n \<longrightarrow> na + nb = n \<and> 0 < na \<and> 0 < nb)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity)\<close>
  by (rule VS_split_ownership; simp add: \<phi>expns sep_disj_fun_def share_fun_def; clarify)
  (* subgoal premises prems for a
    by (insert \<open>\<forall>_. _\<close>[THEN spec[where x=a]], cases \<open>x a\<close>; simp add: share_All prems) . *)


lemma VS_divide_ownership:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w FIX x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<longmapsto> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity)\<close>
  unfolding Fix_def
  by (rule VS_split_ownership_identity; simp add: Premise_def)
*)
end

locale share_fiction_for_partial_mapping_resource_nonsepable =
  share_fiction_for_partial_mapping_resource
    Valid Res Resource_Validator INTERPRET Fic
for Valid :: "('key \<Rightarrow> 'val nonsepable option) set"
and Res :: "('RES_N, 'RES::sep_algebra, 'key \<Rightarrow> 'val nonsepable option) Virtual_Datatype.Field"
and Resource_Validator :: "'RES_N \<Rightarrow> 'RES set"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra, 'RES_N \<Rightarrow> 'RES) interp"
and Fic :: "('FIC_N, 'FIC, 'key \<Rightarrow> 'val nonsepable share option) Virtual_Datatype.Field"
begin

lemma \<phi>nonsepable_normalize:
  \<open>(x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some (Nonsepable Identity)))))
 = (nonsepable x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some Identity))))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

end



subsection \<open>Two Level Parital Mapping\<close>

definition \<open>map_fun_at g k f = (\<lambda>x. if x = k then g (f x) else f x)\<close>

lemma map_fun_at_1[simp]: \<open>map_fun_at g k 1 = 1(k := g 1)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp

lemma map_fun_at_const[simp]:
  \<open>map_fun_at (\<lambda>_. u) k f = f(k := u)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp


subsubsection \<open>Locale of Resources\<close>

locale partial_map_resource2 =
  mapping_resource Valid entry Resource_Validator
for Valid :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) set"
and entry :: "('RES_N, 'RES::sep_algebra, 'key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in> Valid)
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> updt (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
       \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := 1(k2 := u)))}\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd)
  subgoal premises prems for x aa proof -
    have [simp]: \<open>aa k k2 = None\<close>
      by (metis (mono_tags, lifting) fun_upd_same prems(9) sep_disj_fun sep_disj_fun_nonsepable(2))
    then have [simp]:
        \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (aa * 1(k := 1(k2 \<mapsto> any)))
            = aa * 1(k := 1(k2 := u))\<close>
      unfolding map_fun_at_def fun_eq_iff times_fun_def
      by simp
    have t1[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(8))
    have t2[simp]: \<open>aa ## 1(k := 1(k2 := u))\<close>
      by (simp add: sep_disj_fun_def)
    have t3[simp]:
      \<open>clean x ## (mk aa * mk (1(k := 1(k2 := u))))\<close>
      by (simp add: fun_1upd_homo)
    have t4:
      \<open>x ## mk (1(k := 1(k2 := u)))\<close>
      by (metis sep_disj_mk sep_disj_multI1 t1 t2 t3)

    show ?thesis
      apply (simp add: prems mk_homo_mult sep_mult_assoc')
      using prems(6) t4 by blast
  qed .


lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in> Valid)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R * \<phi>Res_Spec {mk (1(k := any))}
\<Longrightarrow> updt (\<lambda>f. f(k := 1)) res \<in> \<phi>Res_Spec R\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def mult_strip_inject_011
          proj_homo_mult times_fun_upd )
  subgoal premises prems for x aa proof -
    have \<open>dom (aa k) = {}\<close>
      by (metis Un_Int_eq(3) dom_mult fun_upd_same prems(10) prems(2) sep_disj_fun sep_disj_partial_map_disjoint)
    then have t1[simp]: \<open>(aa * 1(k := any))(k := 1) = aa\<close>
      by (smt (verit, del_insts) Diff_iff dom1_upd dom_1 dom_eq_empty_conv fun_split_1_not_dom1 fun_upd_triv fun_upd_upd insertCI)
    have t2[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(9))
    show ?thesis
      using prems(1) prems(3) prems(5) prems(7) t1 by force
  qed .

abbreviation perm_transformer :: \<open>('key \<Rightarrow> 'key2 \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option)\<close>
  where \<open>perm_transformer \<equiv> (o) ((o) to_share)\<close>
abbreviation \<open>share_fiction \<equiv> raw_basic_fiction (\<F>_functional perm_transformer)\<close>

(*depreciated!*)
(*lemma share_fiction_expn_full':
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := to_share o f))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := f)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011 times_fun)
  subgoal premises prems for res_r y a r
    apply (insert \<open>\<forall>x. a x * _ = _\<close>[THEN spec[where x=k], simplified,
          unfolded to_share_strip_011[where b=f, simplified,
                      OF sep_disj_fun[where x=k, OF \<open>a ## _\<close>, simplified]]])
      apply (clarify)
      subgoal premises prems2 for a' proof -
        have t1: \<open>y = y(k := a') * 1(k := f)\<close>
          unfolding fun_eq_iff times_fun
          apply simp
          by (metis fun_upd_apply mult_1_class.mult_1_right prems2(2) times_fun_def)
        have t2: \<open>y(k := a') ## 1(k := f)\<close>
          using prems2(3) sep_disj_fun_def by fastforce
        show ?thesis
          apply (subst t1)
          apply (clarsimp simp add: times_fine'[OF t2, symmetric] mk_homo_mult mult.assoc[symmetric])
          apply (rule exI[where x="res_r * mk (Fine (y(k := a')))"], simp)
          apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (y(k := a')))"], simp add: prems)
          by (smt (verit, del_insts) mult_1_class.mult_1_right one_fun prems(4) prems2(1))
      qed .
    subgoal premises prems for res_r a fic_r r proof -
      have t1: \<open>a ## 1(k := f)\<close>
        by (metis prems(7) prems(8) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
      have t2: \<open>fic_r ## 1(k := to_share o f)\<close>
        unfolding sep_disj_fun_def
        apply (clarsimp)
        by (metis comp_apply fun_upd_same prems(4) sep_disj_fun_def t1 to_share_funcomp_sep_disj_I)

      show ?thesis
        apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine'[OF t1])
        apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k := f))) "],
                simp add: prems t2)
        by (smt (verit, best) fun_split_1 fun_upd_def fun_upd_same map_option_o_map_upd prems(4) sep_disj_fun t1 t2 times_fun to_share_funcomp_1 to_share_strip_011)
    qed .

lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> 1 \<Znrres> v)))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := 1(k2 \<mapsto> v))))})\<close>
  using share_fiction_expn_full'[where f=\<open>1(k2 \<mapsto> v)\<close>, simplified] .

(*depreciated!*)
lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k k2 = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' mult_strip_inject_011
            proj_homo_mult)
  subgoal premises prems for res_r y a r proof -
    note t1 = \<open>a ## _\<close>[THEN sep_disj_fun[where x=k], simplified,
                 THEN sep_disj_fun[where x=k2], simplified]
    from \<open>\<forall>_. (a * _) _ = _\<close>[THEN spec[where x=k], simplified times_fun, simplified,
          THEN fun_cong[where x=k2],
          simplified times_fun, simplified]
    have t2: \<open>y k k2 = Some v\<close>
      using t1 apply (cases \<open>a k k2\<close>; cases \<open>y k k2\<close>; simp)
      by (metis sep_disj_share share.collapse share.inject times_share)

    then show ?thesis apply (simp add: t2 times_fun)
      by (metis mult_1_class.mult_1_left one_option_def prems(9) sep_disj_fun sep_disj_option_nonsepable(1) t2)
  qed .

lemma
  assumes A: \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))\<close>
  shows share_fiction_partially_implies'[simp]: \<open>!!( get res) k k2 = Some v\<close>
proof -
  from A[THEN share_fiction_partially_implies]
  show ?thesis by fastforce
qed
*)

lemma raw_unit_assertion_implies[simp]:
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k := 1(k2 \<mapsto> v)))}
\<Longrightarrow> get res k k2 = Some v\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011
      proj_homo_mult sep_disj_fun_def times_fun)
  by (metis (full_types) fun_upd_same sep_disj_option_nonsepable(1) times_option(3))

lemma raw_unit_assertion_implies':
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k := f))}
\<Longrightarrow> f \<subseteq>\<^sub>m get res k\<close>
  unfolding \<phi>Res_Spec_mult_homo[symmetric]
  unfolding \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' mult_strip_inject_011)
  subgoal premises prems for x a proof -
    have t1[simp]: \<open>inject a ## inject (1(k := f))\<close>
      by (simp add: prems(7))
    show ?thesis apply (clarsimp simp add: proj_homo_mult[OF t1] sep_disj_fun_def times_fun map_le_def)
      by (metis fun_upd_same mult_1_class.mult_1_right one_option_def prems(7) sep_disj_fun sep_disj_option_nonsepable(1) sep_mult_commute)
  qed .

lemma raw_unit_assertion_implies''[simp]:
  \<open>res \<in> \<phi>Res_Spec R * \<phi>Res_Spec { mk (1(k := f))}
\<Longrightarrow> k2 \<in> dom f
\<Longrightarrow> get res k k2 = f k2\<close>
  using raw_unit_assertion_implies'[unfolded map_le_def]
  by simp


end

subsubsection \<open>Locale For Sharing Interp\<close>

locale share_fiction_for_partial_mapping_resource2 =
   \<phi>resource_sem Resource_Validator
+  R: partial_map_resource2 Valid Res Resource_Validator
+  fictional_project_inject INTERPRET Fic \<open>R.share_fiction\<close>
for Valid :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) set"
and Res :: "('RES_N, 'RES::sep_algebra, 'key \<Rightarrow> 'key2 \<Rightarrow> 'val option) Virtual_Datatype.Field"
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra,'RES_N \<Rightarrow> 'RES) interp"
and Fic :: "('FIC_N,'FIC, 'key \<Rightarrow> 'key2 \<Rightarrow> 'val share option) Virtual_Datatype.Field"
begin

sublocale permission_fiction Valid \<open>R.perm_transformer\<close> by standard  blast

lemma [simp]:
  \<open>R.perm_transformer (1(k := f)) = 1(k := to_share o f)\<close>
  unfolding fun_eq_iff by simp

lemmas partial_implies = partial_implies_raw

lemma partial_implies':
  \<open> Fic_Space r
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k := 1(k2 \<mapsto> Share n v)))
\<Longrightarrow> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v)))))
\<Longrightarrow> R.get res k k2 = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, del_insts) fun_upd_same join_sub_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep times_option(3))

lemma partial_implies'':
  assumes FS: \<open>Fic_Space r\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k := 1(k2 \<mapsto> Share n v)))\<close>
    and A: \<open> res \<in> \<phi>Res_Spec (\<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v)))))\<close>
  shows [simp]: \<open>R.get res k k2 = Some v\<close>
proof -
  from partial_implies'[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

end

end