(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrime
  keywords
    "proc" "rec_proc" "\<phi>cast" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "cast" "requires" "\<Longleftarrow>" "\<Longleftarrow>'" "$"
    "var" "always"  "\<medium_left_bracket>" "\<medium_right_bracket>" "\<Longrightarrow>" "goal" "\<exists>" "heap" "stack"
    "argument" "return" "on" :: quasi_command
  and "\<bullet>" "affirm" :: prf_decl % "proof"
  and "\<phi>processor" "\<phi>reasoner" "setup_\<phi>application_method" :: thy_decl % "ML"
  and (* "\<phi>interface" "\<phi>export_llvm" *) "\<phi>overloads" :: thy_decl
  and "finish" :: "qed" % "proof"
abbrevs
  "!!" = "!!"
  and "<implies>" = "\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s"
  and "<argument>" = "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t"
  and "<subj>" = "\<^bold>s\<^bold>u\<^bold>b\<^bold>j"
  and "<premise>" = "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e"
  and "<simprem>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m"
  and "<param>" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
  and "<label>" = "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l"
  and "<index>" = "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x"
      and "as" = "\<^bold>a\<^bold>s"
      and "<at>" = "\<^bold>a\<^bold>t"
      and "<and>" = "\<^bold>a\<^bold>n\<^bold>d"
      and "in" = "\<^bold>i\<^bold>n"
      and "<with>" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
      and "<facts>" = "\<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "<proc>" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
      and "<func>" = "\<^bold>f\<^bold>u\<^bold>n\<^bold>c"
      and "<map>" = "\<^bold>m\<^bold>a\<^bold>p"
      and "<subty>" = "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e"
      and "<make>" = "\<^bold>m\<^bold>a\<^bold>k\<^bold>e"
      and "<auto>" = "\<^bold>a\<^bold>u\<^bold>t\<^bold>o"
      and "<construct>" = "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t"
      and "<by>" = "\<^bold>b\<^bold>y"
      and "<simplify>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y"
      and "<heap>" = "\<^bold>h\<^bold>e\<^bold>a\<^bold>p"
      and "<stack>" = "\<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k"
      and "<dual>" = "\<^bold>d\<^bold>u\<^bold>a\<^bold>l"
      and "<when>" = "\<^bold>w\<^bold>h\<^bold>e\<^bold>n"
      and "<dest>" = "\<^bold>d\<^bold>e\<^bold>s\<^bold>t"
      and "<try>" = "\<^bold>t\<^bold>r\<^bold>y"
  and "<get>" = "\<^bold>g\<^bold>e\<^bold>t"
  and "<map>" = "\<^bold>m\<^bold>a\<^bold>p"
  and "<field>" = "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d"
  and "<premcollect>" = "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t"
  and "<conv>" = "\<^bold>c\<^bold>o\<^bold>n\<^bold>v"
  and ">->" = "\<Zinj>"
begin

section \<open>Prelude of the Prelude\<close>

subsection \<open>Preliminary settings\<close>

declare Product_Type.prod.case[\<phi>def]

named_theorems useful \<open>theorems that will be inserted in ANY proof environments,
which basically has the same effect as the using command.\<close>

attribute_setup rotated = \<open>Scan.lift (Scan.optional Parse.int 1 -- Scan.optional Parse.int 0) >>
  (fn (k,j) => Thm.rule_attribute [] (fn _ => Thm.permute_prems j k))\<close>
  \<open>Enhanced version of the Pure.rotated\<close>

attribute_setup TRY_THEN = \<open>(Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- Attrib.thm
      >> (fn (i, B) => Thm.rule_attribute [B] (fn _ => fn A => A RSN (i, B) handle THM _ => A)))
    \<close> "resolution with rule, and do nothing if fail"


subsection \<open>Prelude ML programs\<close>

ML_file NuHelp.ML
ML_file \<open>library/NuSimpCongruence.ML\<close>
ML_file \<open>library/cost_net.ML\<close>


subsection \<open>Overload\<close>

ML_file \<open>library/applicant.ML\<close>

attribute_setup \<phi>overload = \<open>Scan.lift (Parse.and_list1 NuApplicant.parser) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuApplicant.overload th) bindings))\<close>

\<phi>overloads D \<open>Destructural cast\<close>


subsection \<open>\<phi> Reasoner\<close>

definition "\<phi>Intro_Rule x = x"
definition "\<phi>Elim_Rule x = x"
definition "\<phi>Application_Rule x = x"

ML_file \<open>library/reasoner.ML\<close>

attribute_setup \<phi>reason =
\<open>let open Args Scan Parse in
  (lift (optional (Parse.int >> ~) ~100) -- option (lift ($$$ "on") |-- term_pattern)
        >> Nu_Reasoner.attr_add_intro)
  || (lift (add |-- (Parse.int >> ~)) -- option (lift ($$$ "on") |-- term_pattern)
        >> Nu_Reasoner.attr_add_intro)
  || (lift del >> K Nu_Reasoner.attr_del_intro)
end\<close>
\<open>Set introduction rules in \<phi> reasonser.
  Syntax: \<phi>intro [add] <spur-of-the-rule> || \<phi>intro del\<close>

attribute_setup \<phi>reasoner_elim =
\<open>(Scan.lift (Parse.int >> ~) >> Nu_Reasoner.attr_add_elim)
  || (Scan.lift (Args.add |-- (Parse.int >> ~)) >> Nu_Reasoner.attr_add_elim)
  || (Scan.lift Args.del >> K Nu_Reasoner.attr_del_elim)\<close>
  \<open>Set elimduction rules in \<phi> reasonser.
  Syntax: \<phi>reasoner_elim [add] <spur-of-the-rule> || \<phi>elim del\<close>


declare conjI[\<phi>reason] TrueI[\<phi>reason 5000 on ?any]

(* ML \<open>Nu_Reasoner.reasoners @{context}\<close>

ML \<open>val th = Goal.init @{cprop "Q \<and> True \<and> A"}
  val th2 = Nu_Reasoner.reason @{context} th\<close> *)


section \<open>Mechanisms - I - Preludes\<close>

subsection \<open>Tags I\<close>

subsubsection \<open>Mode\<close>

typedef mode = "UNIV :: nat set" .. \<comment> \<open>Technical and systematical device.
  They represent no substantial role in the logic but mainly technical usage
    as settings of reasoning rule in the system.\<close>

consts MODE_NORMAL :: mode \<comment> \<open>A generically used tag of the semantic of `default, the most common`.\<close>
consts MODE_SIMP :: mode \<comment> \<open>relating to simplifier or simplification\<close>
consts MODE_COLLECT :: mode \<comment> \<open>relating to collection\<close>

subsubsection \<open>Premise tag \<close>

definition Premise :: "mode \<Rightarrow> bool \<Rightarrow> bool" where [\<phi>def]:"Premise _ x = x"

abbreviation Normal_Premise ("\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e _" [27] 26) where "Normal_Premise \<equiv> Premise MODE_NORMAL"
abbreviation Simp_Premise ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m _" [27] 26) where "Simp_Premise \<equiv> Premise MODE_SIMP"
abbreviation Premise_Collect ("\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t _" [27] 26) where "Premise_Collect \<equiv> Premise MODE_COLLECT"

text \<open>
  The tag represents a necessary premise that must be solved in a rule or a procedure.
  Different mode correspond different strategies in automatic reasoning.
  The \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P\<close> represents a general proof obligation intended to be solved.
  The \<^term>\<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m P\<close> has a systematic sense, which serves as a side condition and
    decides whether an inference rule should be applied.
  The \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t P\<close> represents a conjunction collection of premises.

  Since \<^term>\<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m P\<close> has a systematic sense, the proof of it is attempted by a safe and
    simple tactic the @{method simp}, which terminates in a short time.

  The \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P\<close> is attempted by fully-powered automatic tactic, the @{method auto},
    which is however heavy and consumes a long time sometimes.
  When the automatic solving consumes a lot of time, users can set the auto level down to
    semi-auto (level 1) to suppress the automatic behavior and solve it manually.

  When there is (at least) one \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t Q\<close> premises in the reasoning state (which is a Horn clause),
    the behavior of \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P\<close> changes. The reasoner moves the \<^prop>\<open>P\<close> into \<^prop>\<open>Q\<close>,
    i.e. \<^prop>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t P \<and> Q\<close>, (the latest / nearest \<^prop>\<open>Q\<close> when there are multiple \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t Q\<close>),
    and the proof of P is delayed until Q. The \<^prop>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t P \<and> Q\<close> is also attempted
    automatically by the @{method auto}.
\<close>

lemma Premise_I[intro!]: "P \<Longrightarrow> Premise mode P" unfolding Premise_def by simp
lemma Premise_E: "Premise mode P \<Longrightarrow> P" unfolding Premise_def by simp
lemma [elim!,\<phi>elim]: "Premise mode P \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> C" unfolding Premise_def by simp

lemma Premise_Irew: "(P \<Longrightarrow> C) \<equiv> Trueprop (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<longrightarrow> C)" unfolding Premise_def atomize_imp .

lemma [\<phi>reason 5000]: "Premise mode True" unfolding Premise_def ..
lemma [\<phi>reason 5000]:
  "Premise mode P
  \<Longrightarrow> Premise mode (Premise any_mode P)"
  unfolding Premise_def .

lemma contract_premise_true:
  "(True \<Longrightarrow> Premise mode B) \<equiv> Trueprop (Premise mode B) "
  by simp

lemma contract_premise_imp:
  "(A \<Longrightarrow> Premise mode B) \<equiv> Trueprop (Premise mode (A \<longrightarrow> B)) "
  unfolding Premise_def atomize_imp .

lemma contract_premise_all:
  "(\<And>x. Premise mode (P x)) \<equiv> Trueprop (\<forall>x. Premise mode (P x)) "
  unfolding Premise_def atomize_all .

lemma contract_premcollect:
  "(\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t Q \<Longrightarrow> PROP C) \<equiv> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t P \<and> Q \<Longrightarrow> PROP C)"
  unfolding Premise_def atomize_imp conj_imp .


lemma Premise_refl: "Premise mode (x = x)" unfolding Premise_def by simp

ML \<open>fun single_return tac s =
  Seq.make (fn () => 
    case Seq.chop 2 (tac s)
      of ([s'], _) => SOME (s', Seq.empty)
       | _ => NONE
  )\<close>

\<phi>reasoner Premise_refl 2000 (\<open>Premise mode (x = x)\<close>) = \<open>fn ctxt =>
  single_return (resolve_tac ctxt @{thms Premise_refl} 1)\<close>

subsubsection \<open>Label tag\<close>

datatype label = LABEL_TAG "unit \<Rightarrow> unit"

lemma [cong]: "LABEL_TAG x \<equiv> LABEL_TAG x"  using reflexive .
lemma label_eq: "x = y" for x :: label by (cases x, cases y) auto

syntax "_LABEL_" :: "idt \<Rightarrow> label" ("LABEL _" [0] 1000)
translations "LABEL name" == "CONST LABEL_TAG (\<lambda>name. ())"


subsubsection \<open>Name tag by type\<close>

datatype ('x, 'name) named (infix "named" 30) = tag 'x

text \<open>It is another name tag which tags names in type by free variables, e.g., \<^typ>\<open>(nat \<times> int) named ('name_i \<times> 'name_j)\<close>.
  It is useful for the rewrite and expansion of quantification which retains name information of bound variables,
    e.g. the transformation from \<^prop>\<open>\<forall>(x::(nat \<times> int) named ('i \<times> 'j)). P x\<close> to \<^prop>\<open>\<forall>(i::nat) (j::int). P (tag (i,j))\<close>\<close>

lemma named_forall: "All P \<longleftrightarrow> (\<forall>x. P (tag x))" by (metis named.exhaust)
lemma named_exists: "Ex P \<longleftrightarrow> (\<exists>x. P (tag x))" by (metis named.exhaust)
lemma [simp]: "tag (case x of tag x \<Rightarrow> x) = x" by (cases x) simp
lemma named_All: "(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (tag x))"
proof fix x assume "(\<And>x. PROP P x)" then show "PROP P (tag x)" .
next fix x :: "'a named 'b" assume "(\<And>x. PROP P (tag x))" from \<open>PROP P (tag (case x of tag x \<Rightarrow> x))\<close> show "PROP P x" by simp
qed


subsubsection \<open>Parameter Input\<close>

definition ParamTag :: " 'a \<Rightarrow> bool" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 26) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> True"

text (in std)
 \<open>The \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> indicate \<^term>\<open>x\<close> is a parameter that should be set by user, e.g.,
  \<^prop>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_size \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int value bit_size \<lbrace> A \<longmapsto> B \<rbrace>\<close>.
  The \<phi>-processor `set_param` processes the \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> antecedent.\<close>

lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
lemma [elim!,\<phi>elim]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto
lemma [cong]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<longleftrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" ..


subsubsection \<open>Label Input\<close>

definition LabelTag :: " label \<Rightarrow> bool" ("\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l _" [1000] 26) where "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<equiv> True"

text \<open>The \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> indicate \<^term>\<open>x\<close> is a \<^typ>\<open>label\<close> that should be set by user, e.g.,
  \<^prop>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l name \<Longrightarrow> do_something_relating name\<close>.
  The \<phi>-processor `set_label` processes the \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> antecedent.\<close>

lemma LabelTag: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x" unfolding LabelTag_def ..
lemma [elim!,\<phi>elim]: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<Longrightarrow> C \<Longrightarrow> C" by auto


subsubsection \<open>Explicit name tag\<close>

definition Labelled :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "Labelled name x = x" \<comment>\<open>name tag\<close>

(* consts "named_sugar" :: " 'i_am \<Rightarrow> 'merely \<Rightarrow> 'a_sugar " ("\<ltbrak>_\<rtbrak>. _" [10,15] 14)
translations
  "\<ltbrak>name\<rtbrak>. x \<Ztypecolon> T" == "x \<Ztypecolon> (\<ltbrak>name\<rtbrak>. T)"
  "\<ltbrak>name\<rtbrak>. x" == "CONST Labelled (LABEL name) x" *)

lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..
lemma [simp]: "x \<in> Labelled name S \<longleftrightarrow> x \<in> S" unfolding Labelled_def ..

subsubsection \<open>Hidden name hint\<close>

definition NameHint :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "NameHint name x = x" \<comment>\<open>name tag\<close>
translations "X" <= "CONST NameHint name X"


subsubsection \<open>\<lambda>-Abstraction Tag\<close>

definition "lambda_abstraction" :: " 'a \<Rightarrow> 'b \<Rightarrow> label \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool " ("\<^bold>\<lambda>\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t _ \<^bold>o\<^bold>v\<^bold>e\<^bold>r _ \<^bold>'(_\<^bold>') \<^bold>= _" [1000,1000,11,1000] 10)
  where "lambda_abstraction x Y name Y' \<longleftrightarrow> Y' x = Y"

lemma lambda_abstraction: "lambda_abstraction x (Y' x) name Y'"
  unfolding lambda_abstraction_def ..

\<phi>reasoner lambda_abstraction 1000 ("lambda_abstraction x Y name Y'") = \<open>fn ctxt => fn sequent =>
  let
    val _ $ (_ $ x $ Y $ (_ $ Abs (name,_,_)) $ Var Y'') = Thm.major_prem_of sequent
    val Y' = Abs(name, fastype_of x, abstract_over (x, Y)) |> Thm.cterm_of ctxt
    val sequent = @{thm lambda_abstraction} RS Thm.instantiate (TVars.empty, Vars.make [(Y'',Y')]) sequent
  in
    Seq.single sequent
  end
\<close>

subsubsection \<open>Technical Tags\<close>

datatype uniq_id = UNIQ_ID
  \<comment> \<open>A technical tag that is during the exporting translated to a unique ID.
    It is useful to generate unique name of anonymous functions.\<close>

subsubsection \<open>The Different Tag\<close>

definition Different :: " 'a \<Rightarrow> 'b \<Rightarrow> bool " where "Different A B = True"
  \<comment> \<open>A premise that solved by automatic reasoning only if the term expressions of A and B
  are not alpha-equivalent. It is useful to break up the self-loop. For example,
  while the introduction rule `cast A \<longmapsto> B \<Longrightarrow> cast B \<longmapsto> C \<Longrightarrow> cast A \<longmapsto> C` causes loop if given `cast A \<longmapsto> A`,
  the rule `cast A \<longmapsto> B \<Longrightarrow> Different A B \<Longrightarrow> cast B \<longmapsto> C \<Longrightarrow> cast A \<longmapsto> C` will not.\<close>
lemma Different_I: "Different A B" unfolding Different_def ..

\<phi>reasoner Different -1 ("Different A B") = \<open>let open NuHelp in
  fn _ => fn th =>
  case try Thm.major_prem_of th
    of SOME prem =>
      (case try (dest_monop @{const_name Trueprop} #> dest_binop @{const_name "Different"}) prem
        of SOME (a,b) =>
          if Term.aconv (a,b) then Seq.empty else Seq.single (@{thm Different_I} RS th)
         | _ => Seq.empty)
     | _ => Seq.empty
end\<close>

subsection \<open>Subtype & View Shift\<close>

definition Subty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
  where "(\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P)"

consts SimpleSubty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e _/ \<longmapsto> _)" [13,13] 12)
translations "(\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B)" == "(\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True)"

definition SubtyDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13,13] 12)
  where "SubtyDual A B P B' A' \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P \<and> (\<forall>u. u \<in> B' \<longrightarrow> u \<in> A'))"
  \<comment> \<open>Intuitively, A pair of dual casts A B P B' A' is the one cast A to B to satisfy some constraints
    usually to met the argument cells to be called and the dual one cast the return B' back to A',
    if B' has some correspondence with B, e.g. of the same nu-type. Usually the change between
    B and B' is to alter something of B like to change a field in B instead of destroying and creating
    a totally new B' irrelevant with B.\<close>

consts SimpSubtyDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e _/ \<longmapsto> _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13] 12)
translations
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> A' \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'" == "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'"

definition (in std) Viewshft :: \<open> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> bool \<Rightarrow> bool \<close>
  ("(2\<^bold>v\<^bold>i\<^bold>e\<^bold>w\<^bold>'_\<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
  where \<open>(\<^bold>v\<^bold>i\<^bold>e\<^bold>w\<^bold>_\<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> (\<exists>u. View_Shift v u \<and> u \<in> B \<and> P))\<close>




lemma cast_id[\<phi>reason 2000]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> A" unfolding Subty_def by fast
lemma cast_dual_id[\<phi>reason 2000]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B"
  unfolding SubtyDual_def by (simp add: cast_id)

lemma cast_id_ty[\<phi>reason 2200 on \<dots>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> y \<Ztypecolon> T" unfolding Subty_def by fast

lemma SubtyDual_I:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e B' \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l B' \<longmapsto> A' "
  unfolding SubtyDual_def Subty_def by blast

lemma [\<phi>reason 10]: \<comment> \<open>Fallback\<close>
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l C \<longmapsto> C"
  unfolding Subty_def SubtyDual_def Premise_def by simp

(* abbreviation SimpleSubty :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B) \<equiv> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h True)" *)
(* lemma SubtyE[elim]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Subty_def Inhabited_def by (auto intro: Inhabited_subset)
lemma SubtyI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Subty_def Inhabited_def by auto *)

lemma ie_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> x' \<Ztypecolon> N" unfolding Subty_def by auto
lemma as_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> X' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> X'" .

lemma \<phi>cast_trans:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> (P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q)
    \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Subty_def by auto

lemma \<phi>cast_dual_trans: 
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>d\<^bold>u\<^bold>a\<^bold>l B' \<longmapsto> A'
    \<Longrightarrow> (P1 \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l C' \<longmapsto> B')
    \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l C' \<longmapsto> A'"
  unfolding Subty_def SubtyDual_def by auto


lemma \<phi>cast_intro_frame:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R * U' \<longmapsto> R * U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  unfolding Subty_def pair_forall times_set_def by blast

lemma \<phi>cast_intro_frame_R:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e U' * R \<longmapsto> U * R \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  unfolding Subty_def pair_forall times_set_def by blast

lemma \<phi>cast_dual_intro_frame:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e M * U' \<longmapsto> M * U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l M\<^sub>m * V \<longmapsto> M\<^sub>m * V' "
  unfolding Subty_def SubtyDual_def pair_forall times_set_def by blast

lemma \<phi>cast_dual_intro_frame_R:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e U' * M \<longmapsto> U * M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V * M\<^sub>m \<longmapsto> V' * M\<^sub>m "
  unfolding Subty_def SubtyDual_def pair_forall times_set_def by blast



(* lemma dual_cast_fallback[\<phi>intro']: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B) \<and> (\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e C \<longmapsto> C)" unfolding Subty_def by fast *)


subsection \<open>Tags II\<close>

subsubsection \<open>Auto tag\<close>

(*TODO: do we still need this?*)
definition Auto :: " 'a \<Rightarrow> 'a " where "Auto x = x"

lemma [\<phi>reason]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e Y \<longmapsto> x \<Ztypecolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e Y \<longmapsto> x \<Ztypecolon> Auto T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Auto_def .

lemma Auto_cong: "(x \<Ztypecolon> T) \<equiv> (x' \<Ztypecolon> T') \<Longrightarrow> (x \<Ztypecolon> Auto T) \<equiv> (x' \<Ztypecolon> Auto T')" unfolding atomize_eq Auto_def .
simproc_setup Auto_cong ("x \<Ztypecolon> Auto T") = \<open>K (NuSimpCong.simproc @{thm Auto_cong})\<close>


subsubsection \<open>Argument tag\<close>

definition Argument :: "'a \<Rightarrow> 'a" ("\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _" [11] 10) where "Argument x = x"

lemma Argument_I: "P \<Longrightarrow> Argument P" unfolding Argument_def .

text \<open>Sequent in pattern \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P \<Longrightarrow> PROP Q\<close> hints users to input a theorem \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> P\<close>
  in order to deduce the sequent into \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> PROP Q\<close>, which is processed by the `rule` processor.
  Argument servers as a protector to prevent the unexpected auto-reasoning, e.g., the case for cast where
  the reasoner always attempts to solve an unprotected case premises and `Argument` tagging the Subty premise
  in this case prevent this automatic behavior when expecting user to input the cast rule.\<close>


subsection \<open>Protector\<close> \<comment> \<open>protecting from automatic transformations\<close>

definition Implicit_Protector :: " 'a \<Rightarrow> 'a " ("\<^bold>'( _ \<^bold>')") where "Implicit_Protector x = x"
  \<comment> \<open>The protector inside the construction of a procedure or sub-procedure, which is stripped
    after the construction. In future if the demand is seen, there may be an explicit protector
    declared explicitly by users and will not be stripped automatically.\<close>

lemma [cong]: "\<^bold>( A \<^bold>) = \<^bold>( A \<^bold>)" ..
lemma [\<phi>reason 1000]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e \<^bold>( A \<^bold>) \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Implicit_Protector_def .
lemma [\<phi>reason 1000]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> \<^bold>( B \<^bold>) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Implicit_Protector_def .

definition Protector :: " 'a \<Rightarrow> 'a " ("\<^bold>'(\<^bold>'( _ \<^bold>')\<^bold>')") where "Protector x = x"

lemma Protector_I: "P \<Longrightarrow> \<^bold>(\<^bold>(P\<^bold>)\<^bold>)" unfolding Protector_def .

subsection \<open>Converter\<close>

definition Conv :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v _ = _" [51,51] 50)
  where "Conv origin object \<longleftrightarrow> origin = object"

text \<open>The forward reasoning towards certain object by certain decision procedure. \<close>


subsection \<open>Simplifier\<close>

definition Simplify :: " mode \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool "
  where "Simplify setting result origin \<longleftrightarrow> result = origin"

lemma [cong]: "A = A' \<Longrightarrow> Simplify s x A = Simplify s x A' "
  unfolding Simplify_def by simp

lemma Simplify_I[intro!]: "Simplify s A A" unfolding Simplify_def ..
lemma Simplify_E[elim!]: "Simplify s A B \<Longrightarrow> (A = B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Simplify_def by blast

subsubsection \<open>Default Simplifier\<close>

consts default_simp_setting :: mode

abbreviation Default_Simplify :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y _ : _" [1000,10] 9)
  where "Default_Simplify \<equiv> Simplify default_simp_setting"

\<phi>reasoner \<open>Default_Simplify\<close> 1000 (\<open>Default_Simplify x y\<close>) = \<open>fn ctx =>
  HEADGOAL (asm_simp_tac ctx) THEN
  HEADGOAL (resolve0_tac @{thms Simplify_I})
\<close>


subsubsection \<open>Subty Simplifier\<close>

named_theorems cast_simp
consts cast_simp_setting :: mode

abbreviation Subty_Simplify :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e] _ : _" [1000,10] 9)
  where "Subty_Simplify \<equiv> Simplify cast_simp_setting"

\<phi>reasoner \<open>Subty_Simplify\<close> 1000 (\<open>Subty_Simplify x y\<close>) = \<open>fn ctx =>
  let val ctx = Raw_Simplifier.clear_simpset ctx
          addsimps Named_Theorems.get ctx \<^named_theorems>\<open>cast_simp\<close>
  in HEADGOAL (simp_tac ctx) THEN
     HEADGOAL (resolve0_tac @{thms Simplify_I})
  end
\<close>


subsection \<open>Miscellaneous\<close>

subsubsection \<open>Finalization Rewrites\<close>

named_theorems final_proc_rewrite
  \<open>Rewrite the specification theorem in the end of the construction.
    Theorems should be a meta equition \<^term>\<open>\<equiv>\<close>.\<close>

lemma [final_proc_rewrite]: "f \<then> nop \<equiv> f" and [final_proc_rewrite]: "nop \<then> f \<equiv> f"
  unfolding instr_comp_def nop_def bind_def atomize_eq by auto


section \<open>Syntax\<close>

subsection \<open>Logical Image Models\<close>

text \<open>A set of models having common meanings, useful for representing logical images\<close>

consts val_of :: " 'a \<Rightarrow> 'b "
consts key_of :: " 'a \<Rightarrow> 'b "

datatype ('a, 'b) object (infixr "\<Zinj>" 60) = object (key_of_obj: 'a) (val_of_obj: 'b) (infixr "\<Zinj>" 60)
adhoc_overloading key_of key_of_obj and val_of val_of_obj
declare object.split[split]

lemma object_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<Zinj> x))" by (metis object.exhaust)
lemma object_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<Zinj> x))" by (metis object.exhaust)
lemma object_All[lrep_exps]: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a \<Zinj> b))" 
proof fix a b assume "(\<And>x. PROP P x) " then show "PROP P (a \<Zinj> b)" .
next fix x assume "\<And>a b. PROP P (a \<Zinj> b)"
    from \<open>PROP P (key_of x \<Zinj> val_of x)\<close> show "PROP P x" by simp
qed


section \<open>Elementary \<phi>-Types\<close>

subsection \<open>Separation Conjecture on Pure Heap\<close>


definition \<phi>Prod :: " ('concrete::times, 'abs_a) \<phi> \<Rightarrow> ('concrete, 'abs_b) \<phi> \<Rightarrow> ('concrete, 'abs_a \<times> 'abs_b) \<phi>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b). A a * B b)"

lemma \<phi>Prod_expn[\<phi>expns]:
  "concrete \<in> ((a,b) \<Ztypecolon> A \<^emph> B) \<longleftrightarrow> (\<exists>ca cb. concrete = ca * cb \<and> ca \<in> (a \<Ztypecolon> A) \<and> cb \<in> (b \<Ztypecolon> B))"
  unfolding \<phi>Prod_def \<phi>Type_def times_set_def by simp

lemma \<phi>Prod_inhabited[elim,\<phi>elim]:
  "Inhabited ((x1,x2) \<Ztypecolon> T1 \<^emph> T2) \<Longrightarrow> (Inhabited (x1 \<Ztypecolon> T1) \<Longrightarrow> Inhabited (x2 \<Ztypecolon> T2) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Prod_split: "((a,b) \<Ztypecolon> A \<^emph> B) = (a \<Ztypecolon> A) * (b \<Ztypecolon> B)"
  by (simp add: \<phi>expns set_eq_iff)

lemma (in std) SepNu_to_SepSet: "(OBJ (a,b) \<Ztypecolon> A \<^emph> B) = (OBJ a \<Ztypecolon> A) * (OBJ b \<Ztypecolon> B)"
  by (simp add: \<phi>expns set_eq_iff)

lemma [\<phi>reason on \<open>\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e (?x,?y) \<Ztypecolon> ?N \<^emph> ?M \<longmapsto> (?x',?y') \<Ztypecolon> ?N' \<^emph> ?M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> x' \<Ztypecolon> N' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e y \<Ztypecolon> M \<longmapsto> y' \<Ztypecolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e (x,y) \<Ztypecolon> N \<^emph> M \<longmapsto> (x',y') \<Ztypecolon> N' \<^emph> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2"
  unfolding Subty_def by (simp add: \<phi>expns) blast







(*lemma [simp]: "A \<inter> S \<perpendicular> A \<inter> -S"
  unfolding disjoint_def by auto
lemma heap_split_id: "P h1' h2' \<Longrightarrow> \<exists>h1 h2. h1' ++ h2' = h1 ++ h2 \<and> P h1 h2" by auto
lemma heap_split_by_set: "P (h |` S) (h |` (- S)) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  by (rule exI[of _ "h |` S"], rule exI[of _ "h |` (- S)"])
    (auto simp add: map_add_def option.case_eq_if restrict_map_def disjoint_def disjoint_iff domIff)
lemma heap_split_by_addr_set: "P (h |` (MemAddress ` S)) (h |` (- (MemAddress ` S))) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  using heap_split_by_set .*)




subsection \<open>Subjection : coheres additional proposition\<close>

definition Subjection :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<^bold>s\<^bold>u\<^bold>b\<^bold>j" 13)
  where " (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = {p. p \<in> T \<and> P}"

lemma [\<phi>expns]: "p \<in> (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> p \<in> T \<and> P" unfolding Subjection_def by simp

lemma [\<phi>reason]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Subty_def Premise_def by (simp add: \<phi>expns)

lemma [simp]: "(T \<^bold>s\<^bold>u\<^bold>b\<^bold>j True) = T" unfolding Auto_def by (auto simp add: \<phi>expns)

lemma [simp,cast_simp]: "(R * (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (R * T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)"
  by (simp add: set_eq_iff \<phi>expns) blast

(* declare split_paired_All[simp del] split_paired_Ex[simp del] *)

lemma (in std) Subjection_simp_proc_arg[simp]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> Y \<rbrace> = (P \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<longmapsto> Y \<rbrace>)"
  (* and Subjection_simp_func_arg[simp]: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<lbrace> T \<and>\<^sup>s P \<longmapsto> Y \<rbrace> = (P \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<lbrace> T \<longmapsto> Y \<rbrace>)" *)
  unfolding Auto_def \<phi>Procedure_def by (simp add: \<phi>expns) blast

lemma (in std) [simp]:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P"
  unfolding CurrentConstruction_def Auto_def by (cases s, simp_all add: \<phi>expns pair_All) blast

lemma (in std) [simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> B) \<and> C \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> (B \<and> C)"
  by simp

lemma subj_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<^bold>( T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<^bold>)"
  unfolding Subty_def Premise_def Implicit_Protector_def by simp

context std begin
term \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> (VAL x \<Ztypecolon> T) \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> Z \<rbrace>\<close>
end

ML \<open>Theory.setup (Sign.add_trrules (let open Ast 
      fun nuty x y = Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable x, Variable y]
      fun wrap_ele tm = Appl [Constant \<^const_syntax>\<open>Ele\<close>, tm]
      fun wrap_nuty x y = wrap_ele (nuty x y)
      fun subj x = Appl [Constant \<^const_syntax>\<open>Subjection\<close>, x, Variable "P"]
    in [
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", subj (nuty "x" "T"), Variable "U"],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", subj (wrap_nuty "x" "T"), Variable "U"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", subj (nuty "x" "T")],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", subj (wrap_nuty "x" "T")])
  ] end))\<close>


subsection \<open>Existential Nu-set\<close>

definition ExSet :: " ('c \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "\<exists>*" 10)
  where "ExSet S = {p. (\<exists>c. p \<in> S c)}"
notation ExSet (binder "\<exists>\<^sup>s" 10)

lemma [\<phi>expns]: "p \<in> ExSet S \<longleftrightarrow> (\<exists>c. p \<in> S c)" unfolding ExSet_def by simp

syntax
  "_SetcomprNu" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<^bold>s\<^bold>u\<^bold>b\<^bold>j/ _./ _ " [2,0,2] 2)

translations
  " X \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. P " \<rightleftharpoons> "\<exists>* idts. X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P"
  " X \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. CONST True " \<rightleftharpoons> "\<exists>* idts. X"

ML \<open>Theory.setup (Sign.add_trrules (let open Ast 
      fun nuty x y = Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable x, Variable y]
      fun wrap_ele tm = Appl [Constant \<^const_syntax>\<open>Ele\<close>, tm]
      fun wrap_nuty x y = wrap_ele (nuty x y)
      fun subj x = Appl [Constant \<^syntax_const>\<open>_SetcomprNu\<close>, x, Variable "idts", Variable "P"]
    in [
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", subj (nuty "x" "T"), Variable "U"],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", subj (wrap_nuty "x" "T"), Variable "U"]),
      Syntax.Parse_Print_Rule (
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", subj (nuty "x" "T")],
        Appl [Constant "\<^const>local.\<phi>Procedure", Variable "f", Variable "U", subj (wrap_nuty "x" "T")])
  ] end))\<close>

text (in std)
 \<open>The set of \<phi>-type in an assertion like \<^term>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> T x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Q x \<rbrace>\<close> is represented
  by \<^const>\<open>ExSet\<close> and we show a \<phi>-type \<^term>\<open>S x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x\<close> represents actually all concrete values that
  belongs to \<^term>\<open>S\<close> a set of \<phi>-types (i.e. the union of \<^term>\<open>S\<close>) by following lemma\<close>

lemma " Union { S x |x. P x } = (S x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x) "
  by (simp add: set_eq_iff \<phi>expns) blast


lemma ExSet_pair: "ExSet T = (\<exists>*c1 c2. T (c1,c2) )" by (auto simp add: \<phi>expns)
lemma named_ExSet: "(ExSet T) = (\<exists>*c. T (tag c) )" by (auto simp add: named_exists \<phi>expns)

lemma (in std_sem) [simp]: "p \<in> \<S>  (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> \<S>  (T z) )" by (cases p, simp_all add: \<phi>expns set_eq_iff)
lemma (in std_sem) [simp]: "p \<in> !\<S> (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> !\<S> (T z) )" by (cases p, simp_all add: \<phi>expns set_eq_iff)
lemma (in std) [simp]: "(VAL ExSet T) = (\<exists>*c. VAL T c)" by (simp add: \<phi>expns set_eq_iff) blast
lemma (in std) [simp]: "(OBJ ExSet T) = (\<exists>*c. OBJ T c)" by (simp add: \<phi>expns set_eq_iff)
lemma [simp]: "(ExSet T * R) = (\<exists>* c. T c * R )" by (simp add: \<phi>expns set_eq_iff) blast
lemma [simp,cast_simp]: "(L * ExSet T) = (\<exists>* c. L * T c)" by (simp add: \<phi>expns set_eq_iff) blast

lemma (in std) \<phi>ExTyp_strip:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (ExSet T)) \<equiv> (\<exists>c. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T c)"
  unfolding CurrentConstruction_def atomize_eq by (cases p, simp_all add: \<phi>expns pair_All) blast

lemma [\<phi>reason 200]: "(\<And>c. \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T c \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P c) \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e (ExSet T) \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>c. P c)"
  unfolding Subty_def by (simp add: \<phi>expns) blast

lemma ExTyp_I_\<phi>app: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T c \<longmapsto> (\<exists>*c. T c)"
  unfolding Subty_def by (simp add: \<phi>expns) blast

lemma generalize_\<phi>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m c \<Longrightarrow> \<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l name \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P c
    \<Longrightarrow> lambda_abstraction c (T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P c) name T \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T' \<longmapsto> \<^bold>( ExSet T \<^bold>) "
  unfolding Subty_def Implicit_Protector_def lambda_abstraction_def by (auto simp add: \<phi>expns)


subsection \<open>Identity\<close>

definition Identity :: " ('a,'a) \<phi> " where "Identity x = {x}"

lemma [simp]: "p \<in> (x \<Ztypecolon> Identity) \<longleftrightarrow> p = x" unfolding \<phi>Type_def Identity_def by auto


subsection \<open>Refinement\<close>

definition NuRefine :: " ('a, 'b) \<phi> \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) \<phi> " (infixl "<where>" 80)
  where "(N <where> T) x = {p. (x \<in> T \<and>p \<in> (x \<Ztypecolon> N))}"

lemma NuRefine_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <where> P) \<longleftrightarrow> x \<in> P \<and> p \<in> (x \<Ztypecolon> N)"
  unfolding NuRefine_def \<phi>Type_def by simp

lemma NuRefine_inhabited[elim,\<phi>elim]:
  "Inhabited (x \<Ztypecolon> N <where> P) \<Longrightarrow> (x \<in> P \<Longrightarrow> Inhabited (x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> x' \<Ztypecolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x' \<in> S \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> x' \<Ztypecolon> M' <where> S \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Subty_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 30 on \<open>\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?x \<Ztypecolon> ?T <where> ?S \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P''\<close>, \<phi>overload D]:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T <where> S \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> x \<in> S"
  unfolding Subty_def by (simp add: \<phi>expns) blast

lemma refine_\<phi>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> x \<Ztypecolon> (N <where> P)"
  unfolding Subty_def by (simp add: \<phi>expns) blast


subsection \<open>Down Lifting\<close>

definition DownLift :: "('a, 'b) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<phi>" (infixl "<down-lift>" 80)
  where "DownLift N g x = (g x \<Ztypecolon> N)"

lemma DownLift_expn[simp]: " p \<in> (x \<Ztypecolon> N <down-lift> g) \<longleftrightarrow> p \<in> (g x \<Ztypecolon> N) "
  unfolding DownLift_def \<phi>Type_def by simp

lemma [elim,\<phi>elim]:
  "Inhabited (x \<Ztypecolon> N <down-lift> g) \<Longrightarrow> (Inhabited (g x \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

(* lemma [\<phi>cast_overload E]: " \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N <down-lift> g \<longmapsto> g x \<Ztypecolon> N" unfolding Subty_def by simp *)
lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N <down-lift> g \<longmapsto> x' \<Ztypecolon> N" unfolding Subty_def by (simp add: \<phi>expns) blast

(* lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (g y = x) \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> y \<Ztypecolon> M <down-lift> g"
  unfolding Intro_def Subty_def by (simp add: \<phi>expns) blast
lemma [\<phi>reason, \<phi>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e y \<Ztypecolon> M <down-lift> g \<longmapsto> g y \<Ztypecolon> M"
  unfolding Dest_def Subty_def by (simp add: \<phi>expns) *)

lemma [\<phi>reason]: " \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> y1 \<Ztypecolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> y \<Ztypecolon> M <down-lift> g"
  unfolding Subty_def by (simp add: \<phi>expns) blast
lemma "\<down>lift_\<phi>app": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> y \<Ztypecolon> N <down-lift> g"
  unfolding Subty_def by (simp add: \<phi>expns) blast



subsection \<open>Up Lifting\<close>

definition UpLift :: "('a, 'c) \<phi> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<phi>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> p \<in> (y \<Ztypecolon> N))}"

lemma UpLift_expn[simp]:
  " p \<in> (x \<Ztypecolon> N <up-lift> f) \<longleftrightarrow> (\<exists>y. (f y = x) \<and> p \<in> (y \<Ztypecolon> N))"
  unfolding UpLift_def \<phi>Type_def by auto

lemma UpLift_inhabited[elim,\<phi>elim]:
  "Inhabited (x \<Ztypecolon> N <up-lift> f) \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> Inhabited (y \<Ztypecolon> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) blast

lemma "\<up>lift_\<phi>app":
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> y \<Ztypecolon> M <up-lift> g"
  unfolding Subty_def by (simp add: \<phi>expns) blast
(* lemma [\<phi>overload D]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M <up-lift> g \<longmapsto> (\<exists> \<Ztypecolon> M) "
  unfolding Subty_def by (simp add: \<phi>expns) blast *)

(* lemma [\<phi>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> y \<Ztypecolon> M <up-lift> g"
  unfolding Intro_def Subty_def by (simp add: \<phi>expns) blast *)

lemma [\<phi>reason 130]:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> x' \<Ztypecolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> y \<Ztypecolon> M' <up-lift> g"
  unfolding Subty_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 20]:
  "(\<And> x. y = g x \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P x) \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e y \<Ztypecolon> M <up-lift> g \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>x. y = g x \<and> P x)"
  unfolding Subty_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 150]:
  "(\<And> x. y = g x \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> M \<longmapsto> y' x \<Ztypecolon> M' x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P x)
    \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e y \<Ztypecolon> M <up-lift> g \<longmapsto> (\<exists>*x. y' x \<Ztypecolon> M' x) \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>x. y = g x \<and> P x)"
  unfolding Subty_def by (simp add: \<phi>expns) blast

(* lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e y \<Ztypecolon> M <up-lift> g \<longmapsto> (\<exists>* x. (x \<Ztypecolon> M) \<and>\<^sup>s g x = y)"
  unfolding Dest_def Subty_def by (simp add: \<phi>expns) blast *)

lemma "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> f x \<Ztypecolon> N <up-lift> f" unfolding Subty_def by (simp add: \<phi>expns) blast
lemma "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> N \<longmapsto> f x \<Ztypecolon> N <up-lift> f" unfolding Subty_def by (simp add: \<phi>expns) blast

(* lemma "\<phi>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<phi>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<phi>Equal_def by (auto 0 6) *)


section \<open>Mechanisms - II - Main Parts\<close>

ML_file NuBasics.ML


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

subsubsection \<open>Heap Tail & Frama Rule\<close>

declare mult.assoc[symmetric, cast_simp]


subsection \<open>Reasoning Mutex\<close>

text \<open>A mutex representing a subgoal in the reasoning.
    Once a subgoal \<^term>\<open>G\<close> is solved, the mutex \<^term>\<open>G\<close> is set, so that other branches
      solving the same goal is trimmed.
TODO\<close>

typedef reason_mutex = "UNIV :: nat set" ..

definition NEW_MUTEX :: "reason_mutex \<Rightarrow> bool" where "NEW_MUTEX X = True"
definition MUTEX_ASSERT :: "reason_mutex \<Rightarrow> bool" where "MUTEX_ASSERT X = True"
definition MUTEX_SET :: "reason_mutex \<Rightarrow> bool" where "MUTEX_SET X = True"

lemma [elim!]: "NEW_MUTEX X \<Longrightarrow> C \<Longrightarrow> C" .
lemma [elim!]: "MUTEX_ASSERT X \<Longrightarrow> C \<Longrightarrow> C" .
lemma [elim!]: "MUTEX_SET X \<Longrightarrow> C \<Longrightarrow> C" .

lemma [simp, \<phi>reason]: "NEW_MUTEX X" unfolding NEW_MUTEX_def ..
lemma [simp, \<phi>reason]: "MUTEX_ASSERT X" unfolding MUTEX_ASSERT_def ..
lemma [simp, \<phi>reason]: "MUTEX_SET X" unfolding MUTEX_SET_def ..

text \<open>Once a mutex is set, any \<^prop>\<open>MUTEX_ASSERT X\<close> will fail in the reasoning.\<close>


subsection \<open>Subty Reasoning\<close>


definition Subty_Target :: " 'a \<Rightarrow> 'a "  ("\<medium_left_bracket> _ \<medium_right_bracket>") where "\<medium_left_bracket> x \<medium_right_bracket> = x"
definition Subty_Target2 :: " 'a \<Rightarrow> reason_mutex \<Rightarrow> 'a "  ("\<medium_left_bracket> _ \<medium_right_bracket>: _" [2,1000] 100) where "\<medium_left_bracket> x \<medium_right_bracket>: _ = x"

lemmas cast_def = Subty_Target_def Subty_Target2_def SubtyDual_def Subty_def

(* lemma [\<phi>intro0]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> X \<longmapsto> H' * y \<Ztypecolon> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * y\<^sub>m \<Ztypecolon> Y \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> X \<longmapsto> H' * \<medium_left_bracket> y \<Ztypecolon> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * \<medium_left_bracket> y\<^sub>m \<Ztypecolon> Y \<medium_right_bracket> \<longmapsto> x\<^sub>m \<Ztypecolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Heap_Subty_Goal_def . *)
(* lemma [\<phi>intro0]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B" unfolding SubtyDual_def  by (simp add: cast_id) *)

(* lemma [\<phi>intro 1000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e L * H \<longmapsto> L * H \<^bold>d\<^bold>u\<^bold>a\<^bold>l L * h\<^sub>m \<Ztypecolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> L * h\<^sub>m \<Ztypecolon> H\<^sub>m \<medium_right_bracket>"
  unfolding Heap_Subty_Goal_def using cast_dual_id . *)

subsubsection \<open>Initialization\<close>

lemma [\<phi>reason 2000]:
  "NEW_MUTEX G \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> \<medium_left_bracket> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t True \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding cast_def .

lemma Subty_Reasoning_Init_NoDual[no_atp]:
  "NEW_MUTEX G \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> \<medium_left_bracket> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t True \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Z \<longmapsto> Z \<medium_right_bracket>"
  unfolding cast_def by blast

lemma Subty_Reasoning_Init_Dual[no_atp]:
  "NEW_MUTEX G \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> \<medium_left_bracket> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> Y' \<medium_right_bracket> \<longmapsto> X' \<medium_right_bracket>: G \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t True \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Y' \<longmapsto> X' \<medium_right_bracket>"
  unfolding cast_def by blast

\<phi>reasoner Subty_Reasoning_Init_Dual 1100 (" \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Z \<longmapsto> Z \<medium_right_bracket>")
 = \<open>fn ctxt => fn sequent =>
  let
    val (_ $ (Const (\<^const_name>\<open>Subty_Target\<close>, _) $
            (Const (\<^const_name>\<open>SubtyDual\<close>, _) $ _ $ _ $ _ $ Z $ _)))
        = Thm.major_prem_of sequent
  in
    if is_Var Z
    then Seq.single (@{thm Subty_Reasoning_Init_NoDual} RS sequent)
    else Seq.single (@{thm Subty_Reasoning_Init_Dual} RS sequent)
  end\<close>

subsubsection \<open>Identity Subty\<close>

lemma cast_dual_fallback:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 * \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> 1 * H\<^sub>m \<medium_right_bracket>: G"
unfolding cast_def by blast+

\<phi>reasoner Subty_Reasoning_Dual_Id 3000 ("\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Z \<longmapsto> Z2 \<medium_right_bracket>: G") = \<open>fn ctxt => fn sequent =>
  let
    val (_ $ (_ $ (Const (\<^const_name>\<open>SubtyDual\<close>, _) $ _ $ _ $ _ $ Z $ Z2) $ _))
        = Thm.major_prem_of sequent
    val Z = case Z of (Const (\<^const_name>\<open>Subty_Target\<close>,_) $ Z') => Z'
        | (_ $ _ $ (Const (\<^const_name>\<open>Subty_Target\<close>,_) $ Z')) => Z'
  in
      if is_Var Z orelse Z aconv Z2
      then resolve_tac ctxt @{thms cast_dual_fallback} 1 sequent
      else Seq.empty
  end\<close>

lemma [\<phi>reason 3000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?H \<longmapsto> \<medium_left_bracket> ?H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
      "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> H \<medium_right_bracket> \<medium_right_bracket>: G"
  and [\<phi>reason 3000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?H \<longmapsto> ?R * \<medium_left_bracket> ?H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
      "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> 1 * \<medium_left_bracket> H \<medium_right_bracket> \<medium_right_bracket>: G"
  for H :: \<open>'a::monoid_mult set\<close>
  unfolding cast_def mult_1_left by blast+

(* lemma [\<phi>intro 40]: \<comment> \<open>outro\<close>
    "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
    \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e a \<Zinj> h \<Ztypecolon> H \<longmapsto> H' * a' \<Zinj> x \<Ztypecolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * a' \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<longmapsto> a \<Zinj> h\<^sub>m \<Ztypecolon> H\<^sub>m \<Longrightarrow>
      \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e a \<Zinj> h \<Ztypecolon> H \<longmapsto> H' * \<medium_left_bracket> Ele \<tort_lbrace> a' \<Zinj> x \<Ztypecolon> X \<tort_rbrace> \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * \<medium_left_bracket> a' \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> a \<Zinj> h\<^sub>m \<Ztypecolon> H\<^sub>m \<medium_right_bracket>"
  and [\<phi>intro 40]:
    "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow> 
    \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e a \<Zinj> h \<Ztypecolon> H \<longmapsto> H' * a' \<Zinj> x \<Ztypecolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e a \<Zinj> h \<Ztypecolon> H \<longmapsto> H' * \<medium_left_bracket> a' \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  and [\<phi>intro 70]:
    "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e a \<Zinj> h \<Ztypecolon> H \<longmapsto> a' \<Zinj> x \<Ztypecolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e a \<Zinj> h \<Ztypecolon> H \<longmapsto> 1 * \<medium_left_bracket> a' \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"*)
(*  and [\<phi>intro 70]:
    "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e h \<Ztypecolon> H \<longmapsto> x \<Ztypecolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e h \<Ztypecolon> H \<longmapsto> \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>" 
  unfolding Heap_Subty_Goal_def Separation_emptyL .*)

context std begin

subsubsection \<open>1 Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> X \<heavy_comma> 1 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def mult_1_right .


lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H'\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H'\<^sub>m \<heavy_comma> 1 \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def mult_1_right .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> 1 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def mult_1_right .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> X \<heavy_comma> 1 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def mult_1_right .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> 1 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def mult_1_right .

subsubsection \<open>Pad 1 Holes at left\<close> \<comment> \<open>to standardize\<close>

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> 1 \<heavy_comma> (VAL X) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def mult_1_left .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> 1 \<heavy_comma> (OBJ X) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def mult_1_left .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e 1 \<heavy_comma> (VAL T) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e VAL T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def mult_1_left .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e 1 \<heavy_comma> (OBJ T) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def mult_1_left .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e 1 \<heavy_comma> (VAL T) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e VAL T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def mult_1_left .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e 1 \<heavy_comma> (OBJ T) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def mult_1_left .

subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R * U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R * (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R * U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R * (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?T \<longmapsto> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?U\<^sub>m \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q \<medium_right_bracket> \<longmapsto> ?T'''\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<medium_right_bracket> \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket> \<longmapsto> T\<^sub>m \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket>: G" 
  unfolding cast_def by (simp add: \<phi>expns)

subsubsection \<open>Protector\<close>

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> \<^bold>( U \<^bold>) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Implicit_Protector_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U' \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> \<^bold>( U \<^bold>) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U' \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def Implicit_Protector_def by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U' \<medium_right_bracket> \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> \<^bold>( U' \<^bold>) \<medium_right_bracket> \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def Implicit_Protector_def by (simp add: \<phi>expns)


subsubsection \<open>Existential\<close>

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U c \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> ExSet U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> U c \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<medium_right_bracket> \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> ExSet U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<medium_right_bracket> \<longmapsto> T\<^sub>m \<medium_right_bracket>: G "
  unfolding cast_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?T \<longmapsto> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ExSet ?U\<^sub>m \<medium_right_bracket> \<longmapsto> ?T\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  "(\<And>c. \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m c \<medium_right_bracket> \<longmapsto> T\<^sub>m c \<medium_right_bracket>: G) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ExSet U\<^sub>m \<medium_right_bracket> \<longmapsto> ExSet T\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: \<phi>expns) blast

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> 1 \<heavy_comma> \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<medium_left_bracket> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket> \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> VAL x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> 1 \<heavy_comma> \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<medium_left_bracket> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket> \<Longrightarrow>
  \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsubsection \<open>Value\<close>


lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> (OBJ ?H) \<longmapsto> ?R''' \<heavy_comma> \<medium_left_bracket> VAL ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<heavy_comma> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (OBJ H) \<longmapsto> R' \<heavy_comma> (OBJ H) \<heavy_comma> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G "
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) metis

lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> (VAL ?V) \<longmapsto> ?R''' \<heavy_comma> \<medium_left_bracket> VAL ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e V \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (VAL V) \<longmapsto> R \<heavy_comma> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) metis

lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_comma> (VAL ?X) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R1 \<heavy_comma> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R1 \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2  \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> \<medium_left_bracket> R2 \<heavy_comma> (VAL X) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) metis

lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?H \<longmapsto> \<medium_left_bracket> ?H2 \<heavy_comma> (VAL ?X) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?H\<^sub>m \<longmapsto> ?H'\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H1 \<heavy_comma> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H1 \<longmapsto> \<medium_left_bracket> H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H'\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> \<medium_left_bracket> H2 \<heavy_comma> (VAL X) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H'\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) metis

lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<longmapsto> ?R' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R\<^sub>m \<heavy_comma> (VAL ?X) \<medium_right_bracket> \<longmapsto> ?R'''\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R\<^sub>m \<medium_right_bracket> \<longmapsto> R'\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R\<^sub>m \<heavy_comma> (VAL X) \<medium_right_bracket> \<longmapsto> R'\<^sub>m \<heavy_comma> (VAL X) \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) metis


subsubsection \<open>Object\<close>

lemma [\<phi>reason 100 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> OBJ ?H \<longmapsto> ?R''' * \<medium_left_bracket> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " MUTEX_ASSERT G
  \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ H \<longmapsto> H'\<heavy_comma> OBJ X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> MUTEX_SET G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R\<heavy_comma> OBJ H \<longmapsto> R\<heavy_comma> H'\<heavy_comma> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) (metis append_Nil fun_mult_norm)

lemma [\<phi>reason 70 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> OBJ ?H \<longmapsto> ?R''' \<heavy_comma> \<medium_left_bracket> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]: \<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " MUTEX_ASSERT G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<heavy_comma> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> MUTEX_SET G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> OBJ H \<longmapsto> R' \<heavy_comma> OBJ H \<heavy_comma> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G "
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) (metis fun_mult_norm mult.commute)

lemma [\<phi>reason 10 on \<open>\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ ?a \<Zinj> ?x \<Ztypecolon> ?T \<longmapsto> ?R''' \<heavy_comma> OBJ ?a' \<Zinj> ?x' \<Ztypecolon> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e a \<Zinj> x \<Ztypecolon> T \<longmapsto> a' \<Zinj> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ a \<Zinj> x \<Ztypecolon> T \<longmapsto> 1 \<heavy_comma> OBJ a' \<Zinj> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding cast_def pair_forall by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> VAL ?V \<longmapsto> ?R''' \<heavy_comma> \<medium_left_bracket> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<heavy_comma> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> VAL V \<longmapsto> R' \<heavy_comma> VAL V \<heavy_comma> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) metis 

lemma [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_comma> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " NEW_MUTEX G2 \<Longrightarrow> \<comment> \<open>make a new subgoal \<close>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R1 \<heavy_comma> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>: G2 \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R1 \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> \<medium_left_bracket> R2 \<heavy_comma> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (simp add: \<phi>expns) blast


text \<open>Dual cast of \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> X \<close>. \<close>

lemma [\<phi>reason 100 on
    \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> OBJ ?H \<longmapsto> ?R''' \<heavy_comma> \<medium_left_bracket> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R''\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R2''\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  \<comment> \<open>search the immediate H first\<close>
  " MUTEX_ASSERT G
    \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ H \<longmapsto> H' \<heavy_comma> OBJ a \<Zinj> x \<Ztypecolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_comma> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<longmapsto> OBJ H\<^sub>m
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> OBJ H \<longmapsto> R \<heavy_comma> H' \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R \<heavy_comma> H'\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R \<heavy_comma> OBJ H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  apply (auto simp add: \<phi>expns)
  apply (metis append_Nil fun_mult_norm)
  by (metis append_self_conv2 fun_mult_norm)
  

lemma [\<phi>reason 70
    on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> OBJ ?H \<longmapsto> ?R' \<heavy_comma> \<medium_left_bracket> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "MUTEX_ASSERT G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> OBJ H \<longmapsto> R' \<heavy_comma> OBJ H \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> OBJ H \<heavy_comma> \<medium_left_bracket> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_comma> OBJ H \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  apply (auto simp add: \<phi>expns)
  apply (smt (verit, ccfv_threshold) mult.assoc mult.commute)
  by (metis fun_mult_norm mult.commute)
  
lemma [\<phi>reason 1200
    on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<heavy_comma> VAL ?V \<longmapsto> ?R' \<heavy_comma> \<medium_left_bracket> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "MUTEX_ASSERT G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> VAL V \<longmapsto> R' \<heavy_comma> VAL V \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<medium_left_bracket> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  apply (auto simp add: \<phi>expns)
  apply (metis append.left_neutral append_Cons)
  by (metis Cons_eq_appendI append.left_neutral)
  
(* lemma [\<phi>reason 1200
    on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<longmapsto> ?R' \<heavy_comma> \<medium_left_bracket> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<medium_left_bracket> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "MUTEX_ASSERT G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<medium_left_bracket> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<medium_right_bracket>: G"
  unfolding Subty_Target_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])
*)

lemma [\<phi>reason 30
     on \<open>\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ ?a \<Zinj> ?x \<Ztypecolon> ?T \<longmapsto> ?R \<heavy_comma> OBJ ?a' \<Zinj> ?x' \<Ztypecolon> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R2 \<heavy_comma> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<longmapsto> ?H\<^sub>m\<close>
  ]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ a \<Zinj> x \<Ztypecolon> T \<longmapsto> OBJ a' \<Zinj> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<longmapsto> OBJ H\<^sub>m \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ a \<Zinj> x \<Ztypecolon> T \<longmapsto> 1 \<heavy_comma> OBJ a' \<Zinj> x' \<Ztypecolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<longmapsto> OBJ H\<^sub>m"
  unfolding cast_def by (simp add: pair_forall \<phi>expns) blast

lemma [\<phi>reason 10
    on \<open>\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ ?H \<longmapsto> ?H' \<heavy_comma> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R''' \<heavy_comma> OBJ ?X\<^sub>m \<longmapsto> ?R'''\<^sub>m\<close>
  ]:
  "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ H \<longmapsto> H' \<heavy_comma> OBJ a \<Zinj> x \<Ztypecolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ H \<longmapsto> H' \<heavy_comma> OBJ a \<Zinj> x \<Ztypecolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> OBJ X\<^sub>m \<longmapsto> OBJ X\<^sub>m"
  unfolding cast_def by simp


text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>

lemma [\<phi>reason 100
    on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_comma> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?T \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P''' \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R2\<^sub>m \<heavy_comma> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?T \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>step case 1\<close>
  " MUTEX_ASSERT G
    \<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a\<^sub>m \<comment> \<open> if addresses are matched\<close>
    \<Longrightarrow> NEW_MUTEX G1
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R1 \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x \<Ztypecolon> T \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>d\<^bold>u\<^bold>a\<^bold>l R1\<^sub>m \<heavy_comma> \<medium_left_bracket> OBJ a \<Zinj> x\<^sub>m \<Ztypecolon> T \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G1 \<comment> \<open>do the dual cast\<close>
        \<comment> \<open>the condition requiring match of address here, is a fast maybe positive-false check \<close>
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> NEW_MUTEX G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R1 \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<medium_right_bracket> \<longmapsto> R1\<^sub>m \<medium_right_bracket>: G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> \<medium_left_bracket> R2 \<heavy_comma> OBJ a \<Zinj> x \<Ztypecolon> T \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<heavy_comma> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> T \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Premise_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 70
    on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<longmapsto> \<medium_left_bracket> ?R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R2\<^sub>m \<heavy_comma> OBJ ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>step case 2\<close>
  " MUTEX_ASSERT G \<comment> \<open> if addresses are not matched, or the dual cast fails\<close>
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> NEW_MUTEX G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G2
        \<comment> \<open>pass the return object \<^term>\<open>X\<^sub>m\<close>, and in the new subgoal \<^term>\<open>G2\<close>,
          maybe, the dual cast is still available.\<close>
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<heavy_comma> OBJ X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_comma> OBJ X\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Premise_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 50
    on \<open>\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_comma> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R\<^sub>m \<medium_right_bracket> \<longmapsto> ?R'''\<^sub>m \<medium_right_bracket>: G\<close>
  ]: \<comment> \<open>step case 3\<close>
  " MUTEX_ASSERT G \<comment> \<open> if even all return objects are passed\<close>
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> NEW_MUTEX G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> \<medium_left_bracket> R2 \<heavy_comma> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G2 \<comment> \<open>we give up the dual cast totally\<close>
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> \<medium_left_bracket> R2 \<heavy_comma> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Premise_def by simp

subsubsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> T1 \<heavy_comma> T2 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (T1 \<heavy_comma> T2) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R \<heavy_comma> X1 \<heavy_comma> X2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R \<heavy_comma> (X1 \<heavy_comma> X2) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> T1 \<heavy_comma> T2 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (T1 \<heavy_comma> T2) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G"
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R \<heavy_comma> X1 \<heavy_comma> X2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> \<medium_left_bracket> R \<heavy_comma> (X1 \<heavy_comma> X2) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G"
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R \<heavy_comma> U1 \<heavy_comma> U2 \<longmapsto> U' \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R \<heavy_comma> (U1 \<heavy_comma> U2) \<longmapsto> U' \<medium_right_bracket>: G"
  unfolding mult.assoc[symmetric] .

end

(*
subsection \<open>Scan\<close>

lemma [\<phi>intro 110]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' * \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e L * R \<longmapsto> L * R' * \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding cast_def Intro_def Dest_def pair_forall
  by (metis Separation_assoc Separation_expn)

lemma [\<phi>intro 110]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> R' * \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e L * R \<longmapsto> L * R' * \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding cast_def Intro_def Dest_def pair_forall
  by (metis Separation_assoc Separation_expn)

lemma [\<phi>intro 100]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e L \<longmapsto> L' * \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H * R \<longmapsto> H' * R * \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding Subty_def SubtyDual_def Heap_Subty_Goal_def Intro_def Dest_def
    Separation_comm[of H R] Separation_comm[of H' R]
  by (metis Heap_Divider_exps Separation_assoc)

 






lemma heap_idx_R_dual[\<phi>intro 100]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H' * \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * \<medium_left_bracket> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H * R \<longmapsto> H' * R * \<medium_left_bracket> x \<Ztypecolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m * R * \<medium_left_bracket> x\<^sub>m \<Ztypecolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m * R \<medium_right_bracket>"
  unfolding Subty_def SubtyDual_def Heap_Subty_Goal_def Intro_def Dest_def
    Separation_comm[of H R] Separation_comm[of H\<^sub>m R]
    Separation_comm[of H' R] Separation_comm[of H'\<^sub>m R]
  by (metis Heap_Divider_exps Separation_assoc)




lemma [\<phi>intro 120]:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H1 * x \<Ztypecolon> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>
    \<Longrightarrow> (P1 \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H1 \<longmapsto> H\<^sub>r * h2 \<Ztypecolon> \<medium_left_bracket> H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket>)
    \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e H \<longmapsto> H\<^sub>r * (x, h2) \<Ztypecolon> \<medium_left_bracket> X \<^emph> H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>"
  unfolding Subty_def SubtyDual_def Heap_Subty_Goal_def HeapDivNu_to_SepSet SepNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)
*)
(* lemma [ \<phi>intro -50 ]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> d \<Ztypecolon> D \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> (P \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e d \<Ztypecolon> D \<longmapsto> d' \<Ztypecolon> D' * h \<Ztypecolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<Ztypecolon> I'\<^sub>m * h\<^sub>m \<Ztypecolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> i \<Ztypecolon> I \<medium_right_bracket>)
  \<Longrightarrow> (P \<Longrightarrow> P2 \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e i \<Ztypecolon> I \<longmapsto> x\<^sub>m \<Ztypecolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Anyway)
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> d' \<Ztypecolon> D' * h \<Ztypecolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<Ztypecolon> I'\<^sub>m * h\<^sub>m \<Ztypecolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> x\<^sub>m \<Ztypecolon> T \<medium_right_bracket>"
  unfolding Dest_def Intro_def SubtyDual_def Different_def Heap_Subty_Goal_def Subty_def
  by (auto simp add: Premise_def) *)

(* lemma [ \<phi>intro 50 ]: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> d \<Ztypecolon> D \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> (P \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e d \<Ztypecolon> D \<longmapsto> d' \<Ztypecolon> D' * h \<Ztypecolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<Ztypecolon> I'\<^sub>m * h\<^sub>m \<Ztypecolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> i \<Ztypecolon> I \<medium_right_bracket>)
  \<Longrightarrow> (P \<Longrightarrow> P2 \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e i \<Ztypecolon> I \<longmapsto> x\<^sub>m \<Ztypecolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Anyway)
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> T \<longmapsto> d' \<Ztypecolon> D' * h \<Ztypecolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> P2 \<medium_right_bracket>"
  unfolding Dest_def Intro_def SubtyDual_def Different_def Heap_Subty_Goal_def Subty_def
  by (auto simp add: Premise_def) *)



(* lemma heap_put_this: "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e 1 * x \<Ztypecolon> X \<longmapsto> x \<Ztypecolon> X" unfolding Subty_def Separation_emptyL by simp
lemma "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e s \<Ztypecolon> S * x \<Ztypecolon> X \<longmapsto> s' \<Ztypecolon> S' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e l \<Ztypecolon> L * s \<Ztypecolon> S * x \<Ztypecolon> X \<longmapsto> l \<Ztypecolon> L * s' \<Ztypecolon> S' "
  unfolding Subty_def HeapDivNu_to_SepSet
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)
lemma "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e s \<Ztypecolon> S * x \<Ztypecolon> X \<longmapsto> s' \<Ztypecolon> S' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e (s \<Ztypecolon> S * r \<Ztypecolon> R) * x \<Ztypecolon> X \<longmapsto> s' \<Ztypecolon> S' * r \<Ztypecolon> R "
  unfolding Subty_def HeapDivNu_to_SepSet
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)
*)


(* lemma "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e S \<longmapsto> S' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e L * S \<longmapsto> L * S'"
  unfolding Subty_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq
lemma "\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e S \<longmapsto> S' \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e S * R \<longmapsto> S' * R"
  unfolding Subty_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq *)


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

subsection \<open>Case Analysis\<close>


lemma [\<phi>reason 1000]: "Premise mode (A = B x y) \<Longrightarrow> Premise mode (A = case_prod B (x,y))" by simp
lemma [\<phi>reason 1000]: "Premise mode (A = B x) \<Longrightarrow> Premise mode (A = case_named B (tag x))" by simp
lemma [\<phi>reason 1000]: "Premise mode (A = B a x) \<Longrightarrow> Premise mode (A = case_object B (a \<Zinj> x))" by simp

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

(* lemma [\<phi>reasoner_elim 10002]:
  "CaseSplit (y = case_prod f x) \<Longrightarrow> (\<And>x1 x2. CaseSplit (y = f x1 x2) \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [\<phi>reasoner_elim 10002]:
  "CaseSplit (y = (case x of a \<Zinj> b \<Rightarrow> f a b)) \<Longrightarrow> (\<And>a b. CaseSplit (y = f a b) \<Longrightarrow> C (a \<Zinj> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [\<phi>reasoner_elim 10002]:
  "CaseSplit (y = (case x of tag a \<Rightarrow> f a)) \<Longrightarrow> (\<And>a. CaseSplit (y = f a) \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp*)



subsection \<open>Subty\<close>

lemma (in std) "\<phi>cast":
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket> \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  unfolding CurrentConstruction_def cast_def
  by (cases blk, simp_all add: pair_All \<phi>expns) blast
lemma (in std) "\<phi>cast'":
  "\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket> \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  unfolding cast_def PendingConstruction_def bind_def
  by (cases blk, auto simp add: \<phi>expns LooseStateTy_expn') blast
  
lemma (in std) cast_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e x \<Ztypecolon> X \<longmapsto> x' \<Ztypecolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (VAL x \<Ztypecolon> X) \<longmapsto> R \<heavy_comma> VAL x' \<Ztypecolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e y \<Ztypecolon> Y \<longmapsto> y' \<Ztypecolon> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (OBJ y \<Ztypecolon> Y) \<longmapsto> R \<heavy_comma> OBJ y' \<Ztypecolon> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e VAL x \<Ztypecolon> X \<longmapsto> XX \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (VAL x \<Ztypecolon> X) \<longmapsto> R \<heavy_comma> XX \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e OBJ y \<Ztypecolon> Y \<longmapsto> YY \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<heavy_comma> (OBJ y \<Ztypecolon> Y) \<longmapsto> R \<heavy_comma> YY \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Subty_def Argument_def
  apply (simp_all add: \<phi>expns)
  apply blast
  apply blast
  apply (metis mult.right_neutral)
  by blast


lemma cast_whole_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Subty_def Argument_def by (simp add: \<phi>expns)


  lemma cast_conversion:
  "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<medium_right_bracket>
  \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e R \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding cast_def by blast


subsection \<open>Conversion\<close>

context std begin

definition Conversion ::
     "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'FIC_N,'FIC) comp set \<Rightarrow> ('VAL,'FIC_N,'FIC) comp set \<Rightarrow>
      ('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'FIC_N,'FIC) comp set \<Rightarrow> ('VAL,'FIC_N,'FIC) comp set \<Rightarrow> bool"
    ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n _/ (2\<lbrace> _/ \<longmapsto> _ \<rbrace>)/ \<longmapsto> _/ (2\<lbrace> _/ \<longmapsto> _ \<rbrace>)" [101,2,2,101,2,2] 100)
    where [\<phi>def]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> U \<longmapsto> V \<rbrace> \<longmapsto> g \<lbrace> U' \<longmapsto> V' \<rbrace> \<longleftrightarrow>( \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> V \<rbrace> \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> U' \<longmapsto> V' \<rbrace> )"

lemma \<phi>conversion:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> U \<longmapsto> V \<rbrace> \<longmapsto> f' \<lbrace> U' \<longmapsto> V' \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> V \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U' \<longmapsto> V' \<rbrace>"
  unfolding Conversion_def by blast

lemma [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n ?f \<lbrace> ?U \<longmapsto> ?V \<rbrace> \<longmapsto> ?f'' \<lbrace> ?U'' \<longmapsto> ?V'' \<rbrace>\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> U \<longmapsto> V \<rbrace> \<longmapsto> f \<lbrace> U \<longmapsto> V \<rbrace>" unfolding Conversion_def by blast


lemma [\<phi>reason 0 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n ?f \<lbrace> ?U \<longmapsto> ?V \<rbrace> \<longmapsto> ?f'' \<lbrace> ?U' \<longmapsto> ?V' \<rbrace>\<close>]:
  assumes A: "\<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<medium_right_bracket>" 
  shows "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> U \<longmapsto> V \<rbrace> \<longmapsto> f \<lbrace> U' \<longmapsto> V' \<rbrace>"
proof -
  from A[unfolded Subty_Target_def]
  have B: "\<forall>M. \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e INTERP_COMP (M * U') \<longmapsto> INTERP_COMP (M * U) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold>d\<^bold>u\<^bold>a\<^bold>l INTERP_COMP (M * V) \<longmapsto> INTERP_COMP (M * V') "
    unfolding Subty_def SubtyDual_def pair_forall by (simp add: \<phi>expns) blast
  then show ?thesis
    unfolding cast_def \<phi>def by (metis LooseStateTy_expn')
qed


definition IntroFrameVar ::
  "('VAL,'FIC_N,'FIC) assn \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> ('VAL,'FIC_N,'FIC) assn
\<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> bool" where
  "IntroFrameVar R S'' S' T'' T' \<longleftrightarrow> S'' = (R * S') \<and> T'' = (R * T') "

text \<open>Currently we do not allow \<^term>\<open>(\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n fff \<lbrace> S' \<longmapsto> T' \<rbrace> \<longmapsto> ggg \<lbrace> S \<longmapsto> T\<rbrace>)\<close>\<close>

lemma apply_proc_conv:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
  \<Longrightarrow> IntroFrameVar R S'' S' T'' T'
  \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> S'' \<longmapsto> T'' \<rbrace> \<longmapsto> f \<lbrace> S \<longmapsto> T\<rbrace>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S' \<longmapsto> T' \<rbrace>
  \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Conversion_def IntroFrameVar_def
  using \<phi>Procedure_def \<phi>frame by auto

lemma apply_cast_conv:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
  \<Longrightarrow> IntroFrameVar R S'' S' T'' T'
  \<Longrightarrow> \<medium_left_bracket> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold>d\<^bold>u\<^bold>a\<^bold>l T'' \<longmapsto> T \<medium_right_bracket>
  \<Longrightarrow> \<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e S' \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2
  \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding CurrentConstruction_def PendingConstruction_def cast_def IntroFrameVar_def
  apply (cases blk)
  apply (auto simp add: \<phi>expns)
  by metis


lemma IntroFrameVar_No:
  "IntroFrameVar 1 S' S' T' T' "
  unfolding IntroFrameVar_def by simp

lemma IntroFrameVar_Yes:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e] S'' : R * S' \<Longrightarrow>
   \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e] T'' : R * T' \<Longrightarrow>
   IntroFrameVar R S'' S' T'' T' "
  unfolding IntroFrameVar_def by blast


\<phi>reasoner IntroFrameVar 1000 ("IntroFrameVar R S'' S' T'' T'") = \<open>fn ctxt => fn sequent =>
  let open NuBasics
    val (Const (\<^const_name>\<open>std.IntroFrameVar\<close>, _) $ _ $ _ $ S' $ _ $ _) =
        major_prem_of sequent |> dest_Trueprop
    val tail = strip_separations S' |> last
  in
    if is_Var tail andalso fastype_of tail = \<^typ>\<open>('VAR,'FIC_N,'FIC)assn\<close>
    then Seq.single (@{thm IntroFrameVar_No} RS sequent)
    else Seq.single (@{thm IntroFrameVar_Yes} RS sequent)
  end\<close>


(* theorem apply_proc_conv_complex:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
  \<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e] S'' : Hr ^* S'
  \<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>s\<^bold>u\<^bold>b\<^bold>t\<^bold>y\<^bold>p\<^bold>e] T'' : Hr ^* T'
  \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> S'' \<longmapsto> T'' \<rbrace> \<longmapsto> g \<lbrace> S \<longmapsto> T\<rbrace>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S' \<longmapsto> T' \<rbrace>
  \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  using apply_proc_conv . *)


lemma conversion_trans: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n g \<lbrace> Xg \<longmapsto> Yg \<rbrace> \<longmapsto> h \<lbrace> Xh \<longmapsto> Yh \<rbrace>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> Xf \<longmapsto> Yf \<rbrace> \<longmapsto> g \<lbrace> Xg \<longmapsto> Yg \<rbrace>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<lbrace> Xf \<longmapsto> Yf\<rbrace> \<longmapsto> h \<lbrace> Xh \<longmapsto> Yh \<rbrace>"
  unfolding Conversion_def by blast

end

subsection \<open>Auto construct & destruct\<close>

context std begin

definition MakeTag ::" 'exp \<Rightarrow> 'x \<Rightarrow> 'x " ("(\<^bold>m\<^bold>a\<^bold>k\<^bold>e _/ \<^bold>b\<^bold>y _)" [40,10] 9) where [\<phi>def]:"MakeTag exp x = x"

lemma \<phi>Make_by_proc:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
      \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e exp \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<rbrace>
      \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  for exp :: "'exp"
  unfolding MakeTag_def using \<phi>apply_proc .

end

(* subsection \<open>Index of Member Field\<close>

subsubsection \<open>Definitions\<close>

named_theorems \<phi>index_def

datatype ('a,'b,'x,'y) index = Index (get_idx: "'a \<Rightarrow> 'x") (map_idx: "('x \<Rightarrow> 'y) \<Rightarrow> 'a \<Rightarrow> 'b")
declare  index.split[split] Map'_def[\<phi>index_def]

definition index_here :: "('a,'b,'a,'b) index" where "index_here = Index id id"
definition index_left :: "('a,'b,'x,'y) index \<Rightarrow> ('a \<times> 'r, 'b \<times> 'r, 'x, 'y) index"
  where "index_left adr = (case adr of Index g m \<Rightarrow> Index (g \<circ> fst) (apfst o m))"
definition index_right :: "('a,'b,'x,'y) index \<Rightarrow> ('l \<times> 'a, 'l \<times> 'b, 'x, 'y) index"
  where "index_right adr = (case adr of Index g m \<Rightarrow> Index (g \<circ> snd) (apsnd o m))"


definition AdrGet :: " ('a,'b,'x,'y) index \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<lbrace> _ \<^bold>@ _ \<rbrace>)" [101,4,4] 100)
  where [\<phi>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<lbrace> X \<^bold>@ A \<rbrace> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx adr \<lbrace> A \<longmapsto> X \<rbrace>"
definition AdrMap :: " ('a,'b,'x,'y) index \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> 'y set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<lbrace> _ \<^bold>@ _ \<longmapsto> _ \<^bold>@ _ \<rbrace>)" [101,4,4,4,4] 100)
  where [\<phi>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<rbrace> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx idx \<lbrace> A \<longmapsto> X \<rbrace> \<and>
    (\<forall>f. (\<forall>a. a \<in> X \<longrightarrow> f a \<in> Y) \<longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> map_idx idx f  a \<in> B))"
declare Map_def[\<phi>index_def]

(*definition FieldIndex
    :: " ('a,'a,'ax,'ax) index \<Rightarrow> ('ax::lrep,'bx) \<phi> \<Rightarrow> ('a::lrep,'b) \<phi> \<Rightarrow> ('b \<Rightarrow> 'bx) \<Rightarrow> (('bx \<Rightarrow> 'bx) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>bool"
    ("(2\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<lbrace> _/ \<^bold>@ _ \<rbrace>/ \<^bold>g\<^bold>e\<^bold>t _/ \<^bold>m\<^bold>a\<^bold>p _)" [101,4,4,30,30] 29)
  where [\<phi>index_def]: "FieldIndex idx X A gt mp
      \<longleftrightarrow> (\<forall>a f. \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> \<tort_lbrace>gt a \<Ztypecolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>a \<Ztypecolon> A\<tort_rbrace> \<longmapsto> \<tort_lbrace>f (gt a) \<Ztypecolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>mp f a \<Ztypecolon> A\<tort_rbrace> \<rbrace>)"
*)

subsubsection \<open>Abstraction theorems\<close>

lemma index_here_getter[\<phi>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_@{thmhere \<lbrace> A \<^bold>@ A \<rbrace>"
  unfolding \<phi>index_def  index_here_def by simp
lemma index_here_mapper[\<phi>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<rbrace>"
  unfolding \<phi>index_def  index_here_def by simp
(*lemma index_here_func[\<phi>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t id \<^bold>m\<^bold>a\<^bold>p id"
  unfolding \<phi>index_def  index_here_def by simp
*)


lemma [\<phi>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<rbrace> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<lbrace> X \<^bold>@ (a,r) \<Ztypecolon> (A \<cross_product> R) \<rbrace>"
  unfolding \<phi>index_def index_left_def by (cases idx) (simp add: \<phi>expns)
lemma [\<phi>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<longmapsto> Y \<^bold>@ b \<Ztypecolon> B\<rbrace> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<lbrace> X \<^bold>@ (a,r) \<Ztypecolon> (A \<cross_product> R) \<longmapsto> Y \<^bold>@ (b,r) \<Ztypecolon> (B \<cross_product> R) \<rbrace>"
  unfolding \<phi>index_def index_left_def by (cases idx) (simp add: \<phi>expns)
(*lemma [\<phi>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<lbrace> X \<^bold>@ A \<cross_product> R \<rbrace> \<^bold>g\<^bold>e\<^bold>t g o fst \<^bold>m\<^bold>a\<^bold>p apfst o m"
  unfolding FieldIndex_def \<phi>index_def index_left_def by (cases idx) (simp add: \<phi>expns)
*)

lemma [\<phi>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<rbrace> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<lbrace> X \<^bold>@ (l,a) \<Ztypecolon> (L \<cross_product> A) \<rbrace>"
  unfolding \<phi>index_def index_right_def by (cases f) (simp add: \<phi>expns)
lemma [\<phi>reason]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<longmapsto> Y \<^bold>@ b \<Ztypecolon> B\<rbrace> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ (l,a) \<Ztypecolon> (L \<cross_product> A) \<longmapsto> Y \<^bold>@ (l,b) \<Ztypecolon> (L \<cross_product> B) \<rbrace>"
  unfolding \<phi>index_def index_right_def by (cases idx) (simp add: \<phi>expns)
(*lemma [\<phi>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ R \<cross_product> A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g o snd \<^bold>m\<^bold>a\<^bold>p apsnd o m"
  unfolding FieldIndex_def \<phi>index_def index_right_def by (cases idx) (simp add: \<phi>expns)
*)
subsubsection \<open>Constructors\<close>

lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat) \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_here_def by simp
lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat) \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_here_def by simp

lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_here_def by simp
lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_here_def by simp

lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [(0::nat)] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_here_def by simp
lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [(0::nat)] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<lbrace> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_here_def by simp

lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ (t, a) \<Ztypecolon> (T \<cross_product> A) \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_right_def by (cases idx) (simp add: \<phi>expns)
lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<longmapsto> Y \<^bold>@ b \<Ztypecolon> B \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ (t,a) \<Ztypecolon> (T \<cross_product> A) \<longmapsto> Y \<^bold>@ (t,b) \<Ztypecolon> (T \<cross_product> B) \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_right_def by (cases idx) (simp add: \<phi>expns)
(*lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ R \<cross_product> A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g o snd \<^bold>m\<^bold>a\<^bold>p apsnd o m"
  unfolding MakeTag_def FieldIndex_def \<phi>index_def index_right_def
  by (cases idx) (simp add: \<phi>expns)
*)
lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (Suc i)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ (t, a) \<Ztypecolon> (T \<cross_product> A) \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_right_def by (cases idx) (simp add: \<phi>expns)
lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<longmapsto> Y \<^bold>@ b \<Ztypecolon> B \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (Suc i)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ (t,a) \<Ztypecolon> (T \<cross_product> A) \<longmapsto> Y \<^bold>@ (t,b) \<Ztypecolon> (T \<cross_product> B) \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_right_def by (cases idx) (simp add: \<phi>expns)
(*lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e (Suc i)#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<lbrace> X \<^bold>@ R \<cross_product> A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g o snd \<^bold>m\<^bold>a\<^bold>p apsnd o m"
  unfolding MakeTag_def FieldIndex_def \<phi>index_def index_right_def
  by (cases idx) (simp add: \<phi>expns)
*)

lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<lbrace> X \<^bold>@ (a,t) \<Ztypecolon> (A \<cross_product> L) \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_left_def by (cases idx) (simp add: \<phi>expns)
lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<Ztypecolon> A \<longmapsto> Y \<^bold>@ b \<Ztypecolon> B \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<lbrace> X \<^bold>@ (a,t) \<Ztypecolon> (A \<cross_product> L) \<longmapsto> Y \<^bold>@ (b,t) \<Ztypecolon> (B \<cross_product> L) \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_left_def by (cases idx) (simp add: \<phi>expns)
(*lemma [\<phi>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat)#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<lbrace> X \<^bold>@ A \<cross_product> R \<rbrace> \<^bold>g\<^bold>e\<^bold>t g o fst \<^bold>m\<^bold>a\<^bold>p apfst o m"
  unfolding FieldIndex_def \<phi>index_def index_left_def MakeTag_def
  by (cases idx) (simp add: \<phi>expns)
*)
*)

subsection \<open>Structural Pairs\<close>

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def .


subsection \<open>Convergence Reasoning\<close>

definition "Merge \<equiv> If"
definition "MergeNeg \<equiv> Not"


subsubsection \<open>Identity\<close>

lemma [\<phi>reason 3000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v If ?P ?A ?A'' = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P A A = A"
  unfolding Conv_def using if_cancel .

lemma [\<phi>reason 3000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?A ?A'' = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P A A = A"
  unfolding Conv_def Merge_def using if_cancel .

subsubsection \<open>Fallback\<close>

lemma [\<phi>reason 10 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v If ?P ?A ?B = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P A B = If P A B"
  unfolding Conv_def ..

text \<open>There is no fallback for \<^const>\<open>Merge\<close>. The Merge is not allowed to be fallback\<close>

subsubsection \<open>Ad-hoc rules\<close>

lemma [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?x \<Ztypecolon> ?T1) (?y \<Ztypecolon> ?T2) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P x y = z
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (x \<Ztypecolon> T) (y \<Ztypecolon> T) = (z \<Ztypecolon> T) "
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v If ?P (?a \<Zinj> ?x) (?b \<Zinj> ?y) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P a b = aa
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v If P x y = z
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v If P (a \<Zinj> x) (b \<Zinj> y) = (aa \<Zinj> z)"
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason 3000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P A B = X
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge (MergeNeg (MergeNeg P)) A B = X"
  unfolding MergeNeg_def by simp

lemma [\<phi>reason 2800]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P B A = X
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v If (MergeNeg P) A B = X"
  unfolding MergeNeg_def by force


subsubsection \<open>Subjection\<close>

lemma [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QL) (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QR) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P QL QR = Q
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j QL) (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j QR) = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q)"
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) ?R = ?X\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) R = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longrightarrow> Q)"
  unfolding Conv_def Merge_def by force

lemma [\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?L (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) = ?X\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not>P \<longrightarrow> Q)"
  unfolding Conv_def Merge_def by force

subsubsection \<open>Existential\<close>

lemma [\<phi>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L x) (R x) = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (\<exists>* x. L x) (\<exists>* x. R x) = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff \<phi>expns) force

lemma [\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?L (\<exists>* x. ?R x) = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (R x) = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P  L (\<exists>* x. R x) = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff \<phi>expns) force

lemma [\<phi>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (\<exists>* x. ?L x) ?R = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L x) R = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (\<exists>* x. L x) R = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff \<phi>expns) force

subsubsection \<open>Separations Initialization\<close>

lemma [\<phi>reason 1200]:
  "NEW_MUTEX G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 * L2) (1 * \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 * L2) R = X"
  for X :: \<open>'a::monoid_mult set\<close>
  unfolding Conv_def cast_def mult_1_left . 

subsubsection \<open>Value\<close>

lemma [\<phi>reason 1200 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (VAL ?V1) (VAL ?V2) = ?X\<close>]: 
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P V1 V2 = V
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (VAL V1) (VAL V2) = (VAL V)"
  unfolding Conv_def cast_def Merge_def by force

lemma (in std) [\<phi>reason 1200 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?R1 \<heavy_comma> VAL ?V1) (?N \<heavy_comma> \<medium_left_bracket> ?R2 \<heavy_comma> VAL ?V2 \<medium_right_bracket>) = ?X \<medium_right_bracket>: ?G\<close> ]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P V1 V2 = V
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P R1 (1 \<heavy_comma> \<medium_left_bracket> N \<heavy_comma> R2 \<medium_right_bracket>) = R \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (R1 \<heavy_comma> VAL V1) (N \<heavy_comma> \<medium_left_bracket> R2 \<heavy_comma> VAL V2 \<medium_right_bracket>) = (R \<heavy_comma> VAL V) \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def
  using mult.assoc by fastforce

lemma (in std) [\<phi>reason 1200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (R1 \<heavy_comma> VAL V1) (N \<heavy_comma> OBJ H2 \<heavy_comma> \<medium_left_bracket> R2 \<medium_right_bracket>) = R \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (R1 \<heavy_comma> VAL V1) (N \<heavy_comma> \<medium_left_bracket> R2 \<heavy_comma> OBJ H2 \<medium_right_bracket>) = R \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def
    by (metis mult.assoc OBJ_comm)


subsubsection \<open>Object\<close>

definition EqualAddress :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool "
  where "EqualAddress _ _ = True"

lemma [\<phi>reason]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a1 = a2
   \<Longrightarrow> EqualAddress (a1 \<Zinj> x1 \<Ztypecolon> T1) (a2 \<Zinj> x2 \<Ztypecolon> T2) "
  unfolding EqualAddress_def ..

lemma [\<phi>reason on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (OBJ ?H1) (OBJ ?H2) = ?X\<close> ]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P H1 H2 = H
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (OBJ H1) (OBJ H2) = (OBJ H)"
  unfolding Conv_def Subty_Target_def Merge_def by force

lemma (in std) [\<phi>reason 1200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge (MergeNeg P) (N \<heavy_comma> R \<heavy_comma> VAL V2) (1 \<heavy_comma> \<medium_left_bracket> L \<heavy_comma> OBJ H1\<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<heavy_comma> OBJ H1) (N \<heavy_comma> \<medium_left_bracket> R \<heavy_comma> VAL V2 \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def MergeNeg_def mult_1_left
  by (metis mult.assoc)

lemma (in std) [\<phi>reason 1200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (N \<heavy_comma> R) (1 \<heavy_comma> \<medium_left_bracket> L \<heavy_comma> OBJ H1\<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge (MergeNeg P) (L \<heavy_comma> OBJ H1) (N \<heavy_comma> \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def MergeNeg_def by force

lemma (in std) [\<phi>reason 100 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?L \<heavy_comma> OBJ ?H1) (?N \<heavy_comma> \<medium_left_bracket> ?R \<heavy_comma> OBJ ?H2 \<medium_right_bracket>) = ?X''' \<medium_right_bracket>: ?G\<close>]:
  \<comment> \<open>search the immediate element\<close>
  "MUTEX_ASSERT G
   \<Longrightarrow> EqualAddress H1 H2
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (OBJ H1) (OBJ H2) = H
   \<Longrightarrow> MUTEX_SET G \<comment> \<open>if success, trim all other branches on G\<close>
   \<Longrightarrow> NEW_MUTEX G2
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (1 \<heavy_comma> \<medium_left_bracket> N \<heavy_comma> R \<medium_right_bracket>) = X \<medium_right_bracket>: G2
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<heavy_comma> OBJ H1) (N \<heavy_comma> \<medium_left_bracket> R \<heavy_comma> OBJ H2 \<medium_right_bracket>) = (X \<heavy_comma> H) \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def mult_1_left by (metis mult.assoc)

lemma (in std) [\<phi>reason 70 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?L (?N \<heavy_comma> \<medium_left_bracket> ?R \<heavy_comma> OBJ ?H2 \<medium_right_bracket>) = ?X''' \<medium_right_bracket>: ?G\<close>]:
  \<comment> \<open>search next\<close>
  "MUTEX_ASSERT G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> OBJ H2 \<heavy_comma> \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> R \<heavy_comma> OBJ H2 \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by (metis mult.assoc OBJ_comm)

subsubsection \<open>Unfold\<close>

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> R \<heavy_comma> R1 \<heavy_comma> R2 \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> R \<heavy_comma> (R1 \<heavy_comma> R2) \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by (metis mult.assoc)

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 \<heavy_comma> L2 \<heavy_comma> L3) R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 \<heavy_comma> (L2 \<heavy_comma> L3)) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by (metis mult.assoc)

lemma (in std) [\<phi>reason 2200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> R1 \<heavy_comma> R2 \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> 1 \<heavy_comma> (R1 \<heavy_comma> R2) \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force


subsubsection \<open>Padding 1\<close>

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (1 \<heavy_comma> OBJ L) R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (OBJ L) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (1 \<heavy_comma> VAL L) R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (VAL L) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> 1 \<heavy_comma> VAL V \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> VAL V \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> 1 \<heavy_comma> OBJ V \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> OBJ V \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

subsubsection \<open>Eliminate 1 Hole\<close>

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_comma> \<medium_left_bracket> R \<heavy_comma> 1 \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma (in std) [\<phi>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<heavy_comma> 1) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

subsubsection \<open>Termination\<close>

lemma (in std) [\<phi>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P 1 (1 \<heavy_comma> \<medium_left_bracket> 1 \<medium_right_bracket>) = ?X'' \<medium_right_bracket>: ?G\<close>]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P 1 (1 \<heavy_comma> \<medium_left_bracket> 1 \<medium_right_bracket>) = 1 \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def by force
  

subsection \<open>Convergence\<close>

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


(* subsection \<open>Program Interface\<close> \<comment> \<open>Interfaces exported to target LLVM module\<close>

definition Prog_Interface :: " label \<Rightarrow> 'a itself \<Rightarrow> 'b itself \<Rightarrow> ('a::lrep  \<longmapsto> 'b::lrep) \<Rightarrow> bool"
  where "Prog_Interface _ args rets proc \<longleftrightarrow> True"

lemma Prog_Interface_proc: "TERM proc \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) proc" 
  unfolding Prog_Interface_def ..

lemma Prog_Interface_func:
  "TERM f \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) f" 
  unfolding Prog_Interface_def ..
*)

section \<open>Main implementation of the system\<close>

ML_file \<open>library/application.ML\<close>

ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/procedure.ML"


ML_file NuSys.ML
ML_file "./library/processors.ML"
ML_file "./library/obtain.ML"
ML_file "./library/QuantExpansion.ML"
(* ML_file "./codegen/compilation.ML" *)
ML_file NuToplevel.ML

section \<open>Attributes and Commands\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<phi>instr"}, NuInstructions.list_definitions #> map snd))  \<close>

attribute_setup \<phi>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<phi>-system\<close>

attribute_setup \<phi>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (NuProcessor.get_attr ctx name) (ctx,toks))
  || Scan.lift NuProcessor.process_attr\<close>
  \<open>Evaluate the \<phi>-system process or the process of the given processor on the target theorem\<close>

(* TODO: fix this
method_setup \<phi>reason = \<open>let open Scan Parse in
  (succeed [] || Scan.repeat (Attrib.thms -- Scan.lift Parse.int)) >> (fn ths => fn ctx =>
  Method.SIMPLE_METHOD (Nu_Reasoner.reason_tac (Nu_Reasoner.add_intro_rules ths ctx)))
end\<close> *)

ML \<open>

local open Scan NuToplevel NuSys Parse 
val nustatement = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- opt_attribs -- Scan.repeat1 Parse.propp);
val structured_statement =
  nustatement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));
val statement1 = Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.propp);
val requires_statement = $$$ "requires" |-- Parse.!!! statement1;
val premises_statement = $$$ "premises" |-- Parse.!!! statement1;
val precond_statement = Scan.repeat ((premises_statement >> map (pair NuToplevel.Premise))
                || (requires_statement >> map (pair NuToplevel.Requirement))) >> flat;
val requires_opt1 = Scan.option ($$$ "requires" |-- Parse.term);
val where_statement = Scan.optional ($$$ "where" |--
        Parse.and_list1 (Scan.repeat Args.var --| Parse.$$$ "=" -- Parse.term)) [];
val defines_statement = Scan.optional ($$$ "defines" |-- Parse.!!! statement1) [];
val nu_statements = Parse.for_fixes -- Scan.optional Parse_Spec.includes [] --
           where_statement -- defines_statement  -- precond_statement;

val arg = Parse.term
val proc_head = Parse_Spec.thm_name ":" --
        ((arg --| $$$ "\<longmapsto>" -- arg) || ($$$ "argument" |-- arg --| $$$ "return" -- arg))

in

(* val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>exty_simproc\<close> "setup the pecific simproc for \<^const>\<open>ExTy\<close>"
  (Parse.binding >> NuExTyp.set_simproc_cmd) *)

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((proc_head -- nu_statements) >>
        (fn ((b,(arg,ret)),((((fixes,includes),lets),defs),preconds)) =>  
            (begin_proc_cmd b arg ret fixes includes lets defs preconds)));

val loop_variables = $$$ "var" |-- !!! vars;
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>rec_proc\<close> "begin a recursive procedure construction"
    ((proc_head -- loop_variables -- nu_statements) >>
        (fn (((b,(arg,ret)),vars),((((fixes,includes),lets),defs),preconds)) =>  
            (begin_rec_proc_cmd b arg ret (vars,fixes) includes lets defs preconds)));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>\<phi>cast\<close> "begin a procedure construction"
    ((proc_head -- option ($$$ "and" |-- Parse.term) -- nu_statements) >>
        (fn (((b,(arg,ret)),addtional_prop),((((fixes,includes),lets),defs),preconds)) =>
            (begin_cast_cmd b arg ret addtional_prop fixes includes lets defs preconds)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finish\<close> "Finish the procedure construction"
    (Scan.succeed (Toplevel.end_proof NuToplevel.finish_proc_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<bullet>\<close> "The \<phi>construction"
    (fn toks => (
      Toplevel.proof (Proof.map_context (Config.put Nu_Reasoner.auto_level 2) #>
          NuProcessor.powerful_process (toks @ [Token.eof])),
      if hd toks |> Token.is_eof then [Token.eof] else []))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>affirm\<close> "proof for premise"
    (Scan.succeed (Toplevel.proof' (snd oo NuToplevel.prove_prem)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>processor\<close> "define \<phi>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword || Parse.string)
          -- Parse.nat -- Parse.term -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
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

subsection \<open>Application method\<close>

attribute_setup \<phi>application_method = \<open>Scan.lift (Parse.int -- (Parse.int >> ~)) >> (fn (idx,cost) =>
  Thm.declaration_attribute (fn th => NuApply.update (cost,{thm=th, applicant_idx = idx})))\<close>

declare (in std)
  \<phi>apply_proc[\<phi>application_method 1 100]
  apply_proc_conv[\<phi>application_method 3 -3000]
  "\<phi>cast"[unfolded Subty_Target_def, \<phi>application_method 1 1100]
  apply_cast_conv[\<phi>application_method 3 1000]

(* thm
  "cast"[unfolded Subty_Target_def, OF _ cast_\<phi>app(1)[OF Argument_I], \<phi>application_method 1 1100]
  "cast"[unfolded Subty_Target_def, OF _ cast_\<phi>app(2)[OF Argument_I], \<phi>application_method 1 1100]
  "cast"[unfolded Subty_Target_def, OF _ cast_\<phi>app(3)[OF Argument_I], \<phi>application_method 1 1100]
  "cast"[unfolded Subty_Target_def, OF _ cast_\<phi>app(4)[OF Argument_I], \<phi>application_method 1 1100]
  "cast"[unfolded Subty_Target_def, OF _ cast_conversion[OF _ cast_\<phi>app(1)[OF Argument_I]],
      \<phi>application_method 2 1050]
  "cast"[unfolded Subty_Target_def, OF _ cast_conversion[OF _ cast_\<phi>app(2)[OF Argument_I]],
      \<phi>application_method 2 1050]
  "cast"[unfolded Subty_Target_def, OF _ cast_conversion[OF _ cast_\<phi>app(3)[OF Argument_I]],
      \<phi>application_method 2 1050]
  "cast"[unfolded Subty_Target_def, OF _ cast_conversion[OF _ cast_\<phi>app(4)[OF Argument_I]],
      \<phi>application_method 2 1050]

thm "cast"[unfolded Subty_Target_def, \<phi>application_method 1 1100]
thm "cast"[unfolded Subty_Target_def, OF _ cast_\<phi>app(1)[OF Argument_I], \<phi>application_method 1 1100]

thm "cast"[unfolded Subty_Target_def, OF _ cast_conversion[OF _ cast_\<phi>app(2)[OF Argument_I]],
      \<phi>application_method 2 1050]
*)

(*  
  "cast"[OF _ cast_whole_heap_\<phi>app[OF Argument_I, OF cast_heap_conversion],
      \<phi>application_method 2 1020]*)

(* lemmas apply_func_conv[\<phi>application_method 6 -100]
  = apply_proc_conv_simple[OF _ _ _ _ op_call, rotated 3 1, rotated 1 3] *)

(* consts \<phi>Application_Rewrite :: bool
setup_\<phi>application_method \<open>\<phi>Application_Rewrite\<close> 1000 \<open>PROP P &&& A = B\<close> | \<open>PROP P &&& (A \<equiv> B)\<close> = \<open>
  fn ctx => fn applicants => fn major =>
    let
      fun is_simprule (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _)) = true
          | is_simprule (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _) = true
          | is_simprule _ = false
      val applicants = List.filter (is_simprule o Thm.concl_of) applicants
    in
      if null applicants then Seq.empty else Seq.make (fn () =>
        SOME (Simplifier.simplify (Raw_Simplifier.clear_simpset ctx addsimps applicants) major, Seq.empty))
    end
\<close>*)

subsection \<open>Quantification Expansion\<close>

simproc_setup named_forall_expansion ("All (P :: 'a named 'names \<Rightarrow> bool)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.forall_expansion)\<close>

simproc_setup named_exSet_expansion ("ExSet (P :: 'a named 'names \<Rightarrow> 'b set)") =
  \<open>K (fn ctx => fn cterms => QuantExpansion.simproc_of QuantExpansion.ExNu_expansion ctx cterms)\<close>

simproc_setup named_pureAll_expansion ("Pure.all (P :: 'a named 'names \<Rightarrow> prop)") =
  \<open>K (QuantExpansion.simproc_of QuantExpansion.pure_All_expansion)\<close>

section \<open>Processors\<close>

context std begin

subsection \<open>Controls\<close>

\<phi>processor set_auto_level 10 \<open>PROP P\<close> \<open>(fn ctxt => fn sequent => NuParse.auto_level_force >>
  (fn auto_level' => fn _ => (sequent, Config.put Nu_Reasoner.auto_level auto_level' ctxt)))\<close>

\<phi>processor repeat 12 \<open>PROP P\<close> \<open>let
    fun repeat n f (th,ctx) =
      if n <= 0 then (th,ctx) else repeat (n-1) f (f th ctx)
    fun repeat' n f (th,ctx) =
      if n <= 0 then (th,ctx) else (repeat' (n-1) f (f th ctx) handle _ => (th,ctx))
  in fn ctx => fn th =>
    Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*") >> (fn (tok,n) => fn () =>
        (case Int.fromString n of SOME n => repeat n | _ => repeat' 32)
          (NuProcessor.process_by_input [tok])
          (th,ctx)
    )
  end\<close>

subsection \<open>Constructive\<close>

\<phi>processor accept_call 300 \<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta =>
  Scan.succeed (fn _ => NuSys.accept_proc meta ctx)\<close>

\<phi>processor "apply" 9000 \<open>P\<close> \<open> fn ctx => fn meta => NuApplicant.parser >> (fn binding => fn _ =>
  (NuSys.apply ctx (NuApplicant.applicant_thms ctx binding) meta, ctx))\<close>

\<phi>processor set_param 5000 \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Parse.term >> (fn term => fn _ =>
    (NuSys.set_param_cmd ctx term meta, ctx))\<close>

\<phi>processor set_label 5000 \<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn sequent => Parse.name >> (fn name => fn _ =>
    (NuSys.set_label name sequent, ctx))\<close>

\<phi>processor rule 7100 \<open>P \<Longrightarrow> PROP Q\<close>
  \<open>fn ctx => fn sequent => (NuApplicant.parser -- Parse.opt_attribs) >> (fn (name,attrs) => fn _ =>
    let open NuBasics
    val attrs = map (Attrib.attribute_cmd ctx o Attrib.check_src ctx) attrs
    val ths = NuApplicant.applicant_thms ctx name
    val (ths,ctx) = fold_map (Thm.proof_attributes attrs) ths ctx
    val sequent = perhaps (try (fn th => @{thm Argument_I} RS th)) sequent
    in case Seq.pull (Thm.biresolution NONE false (map (pair false) ths) 1 sequent)
            of SOME (th, _) => (th,ctx)
              | _ => raise THM ("RSN: no unifiers", 1, sequent::ths) end)\<close>

subsubsection \<open>Sub-procedure\<close>

\<phi>processor begin_sub_procedure 7000 \<open>PROP Q\<close> \<open>let open Parse Scan in fn ctx => fn meta =>
  $$$ "\<medium_left_bracket>" |-- optional ($$$ "premises" |-- and_list (binding -- opt_attribs)) [] >> (fn prems => fn () =>
  raise Process_State_Call' ((meta,ctx), NuToplevel.begin_block_cmd prems true)
) end\<close>

\<phi>processor end_sub_procedure 7000 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>let open Parse Scan in fn ctx => fn meta =>
  $$$ "\<medium_right_bracket>" >> (fn x => fn () =>
  raise Process_State_Call' ((meta,ctx), NuToplevel.end_block_cmd true)
) end\<close>

subsubsection \<open>Existential elimination\<close>

\<phi>processor existential_elimination 50 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ExSet T\<close>
  \<open>fn ctxt => fn sequent => Parse.$$$ "\<exists>" |-- Parse.list1 Parse.binding >> (fn insts => fn () =>
      raise Process_State_Call' ((sequent,ctxt), NuObtain.choose insts))\<close>

\<phi>processor auto_existential_elimination 50 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ExSet T\<close>
  \<open>fn ctx => fn meta => Scan.succeed (fn () =>
    raise Process_State_Call' ((meta,ctx), NuObtain.auto_choose))\<close>

subsection \<open>Simplifiers & Resonings\<close>

\<phi>processor \<phi>simplifier 40 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>NuProcessors.simplifier []\<close>
(* \<phi>processor \<phi>simplifier_final 9999 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close> *)

\<phi>processor move_fact 50 \<open>(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P\<close>
\<open>fn ctx => fn sequent => Scan.succeed (fn _ =>
  let
    val de_premise = perhaps (try (fn th => th RS @{thm Premise_E}))
    val facts = Proof_Context.get_thms ctx "\<phi>lemmata"
    val ctx = Proof_Context.put_thms true ("\<phi>lemmata",
        SOME (de_premise (sequent RS @{thm conjunct2}) :: facts) ) ctx
  in
    (sequent RS @{thm conjunct1}, ctx)
  end)\<close>

\<phi>processor set_\<phi>current 100 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
\<open>fn ctx => fn sequent => Scan.succeed (fn _ =>
  let
    val thm = sequent RS @{thm CurrentConstruction_D}
    val ctx = Proof_Context.put_thms true ("\<phi>current", SOME [thm]) ctx
  in
    raise Bypass (SOME(sequent, ctx))
  end)\<close>

\<phi>processor \<phi>reason 1000 \<open>PROP P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn sequent => Scan.succeed (fn _ =>
  let open NuBasics
    val sequent' = Nu_Reasoner.reason ctx sequent
  in case sequent' of SOME sequent' =>
      if Thm.prop_of sequent' = Thm.prop_of sequent
      then raise Bypass (SOME (sequent, ctx))
      else (sequent',ctx)
    | NONE => raise Bypass (SOME (sequent, ctx))
  end)\<close>

\<phi>processor fold 1300 \<open>PROP P\<close> \<open>
  fn ctxt => fn sequent => NuParse.$$$ "fold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (Local_Defs.fold ctxt (Attrib.eval_thms ctxt thms) sequent, ctxt)
)\<close>

\<phi>processor unfold 1300 \<open>PROP P\<close> \<open>
  fn ctxt => fn sequent => NuParse.$$$ "unfold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (Local_Defs.unfold ctxt (Attrib.eval_thms ctxt thms) sequent, ctxt)
)\<close>

\<phi>processor goal 1300 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>
  fn ctxt => fn sequent => Parse.$$$ "goal" >> (fn _ => fn _ =>
    let
      val goal = Proof_Context.get_thm ctxt "\<phi>thesis" |> Drule.dest_term
      val (_,_,desired_nu) = NuBasics.dest_procedure_c goal
      val ty = Thm.typ_of_cterm desired_nu
      val prot = Const (\<^const_name>\<open>Implicit_Protector\<close>, ty --> ty) |> Thm.cterm_of ctxt
      val ctxt = Config.put Nu_Reasoner.auto_level 1 ctxt
      val sequent = NuSys.cast ctxt (Thm.apply prot desired_nu) sequent
    in (sequent, ctxt) end
)\<close>


subsection \<open>Literal operations\<close>

\<phi>processor literal_constructor 9500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.cartouche >> (fn term => fn _ =>
  let val term = Syntax.read_term ctx term |> Thm.cterm_of ctx |> Simplifier.rewrite ctx |> Thm.rhs_of
  in (NuSys.auto_construct ctx term meta, ctx) end)\<close>

end

section \<open>Mechanism III - Additional Parts\<close>

subsection \<open>Variant Cast\<close>

definition Variant_Cast :: "'vars \<Rightarrow> 'a set \<Rightarrow> ('vars \<Rightarrow> 'a set) \<Rightarrow> bool" ("\<^bold>v\<^bold>a\<^bold>r\<^bold>i\<^bold>a\<^bold>n\<^bold>t _ \<^bold>i\<^bold>n _/ \<longmapsto> _" )
  where "Variant_Cast insts X X' \<longleftrightarrow> X = X' insts"

lemma Variant_Cast_I: "X = X' vars \<Longrightarrow> Variant_Cast vars X X' "
  unfolding Variant_Cast_def by auto

lemma Variant_Cast_I_always:
  "X = X' vars \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e always vars \<Longrightarrow>
  Variant_Cast vars X (\<lambda>vars. X' vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j always vars)"
  unfolding Variant_Cast_def Auto_def by (auto simp add: \<phi>expns)

lemma case_prod_expn_I: "A = B x y \<Longrightarrow> A = case_prod B (x,y)" by simp
lemma case_named_expn_I: "A = B x \<Longrightarrow> A = case_named B (tag x)" by simp

ML_file_debug \<open>library/variables_tag.ML\<close>

\<phi>processor vars_by_pattern 110 \<open>Variant_Subty vars X X' \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn meta => 
let open Parse Scan NuHelp NuBasics 
  fun pattern_match ((vars, pattern), always) _ =
    (NuVariablesTag.variables_tag_pattern_match vars pattern always ctx meta, ctx)
  fun var_term (vars, always) _ =
    (NuVariablesTag.variables_tag_terms vars always ctx meta, ctx)
  val none = Scan.succeed []
  val params = (list Parse.params) >> flat
  val syn_pattern_match =
    ($$$ "var" |-- params --| $$$ "in" -- list1 term -- option ($$$ "always" |-- term))
    >> pattern_match
  val syn_nonvar =
    (params -- option ($$$ "always" |-- term))
    >> apfst (fn vars => if null vars then fail ([],[]) else (vars, map (Binding.name_of o #1) vars))
    >> pattern_match
  val syn_var_term = ($$$ "var" |-- list1 term -- Scan.option ($$$ "always" |-- term)) >> var_term
in syn_pattern_match || syn_var_term || syn_nonvar end\<close>

subsection \<open>Reasoners\<close>

ML_file "library/reasoners.ML"

\<phi>reasoner Premise_Collect 10 (\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t P\<close>) = \<open>Nu_Reasoners.premise_collect_tac\<close>
\<phi>reasoner Normal_Premise 10 (\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P\<close>) = \<open>Nu_Reasoners.premise_tac\<close>
\<phi>reasoner Simp_Premise 10 (\<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m P\<close>) = \<open>Nu_Reasoners.asm_simp_tac\<close>


end