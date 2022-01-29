(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrime
  keywords
    "proc" "rec_proc" "\<nu>cast" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "cast" "requires" "\<Longleftarrow>" "\<Longleftarrow>'" "$"
    "var" "always"  "\<medium_left_bracket>" "\<medium_right_bracket>" "\<Longrightarrow>" "goal" "\<exists>" "heap" "stack"
    "argument" "return" "on" :: quasi_command
  and "\<bullet>" "affirm" :: prf_decl % "proof"
  and "\<nu>processor" "\<nu>reasoner" "setup_\<nu>application_method" :: thy_decl % "ML"
  and "\<nu>interface" "\<nu>export_llvm" "\<nu>overloads" :: thy_decl
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
      and "<cast>" = "\<^bold>c\<^bold>a\<^bold>s\<^bold>t"
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
begin

section \<open>Prelude of the Prelude\<close>

subsection \<open>Preliminary settings\<close>

declare Product_Type.prod.case[\<nu>def]

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

attribute_setup \<nu>overload = \<open>Scan.lift (Parse.and_list1 NuApplicant.parser) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuApplicant.overload th) bindings))\<close>

\<nu>overloads D \<open>Destructural cast\<close>


subsection \<open>\<nu> Reasoner\<close>

definition "\<nu>Intro_Rule x = x"
definition "\<nu>Elim_Rule x = x"
definition "\<nu>Application_Rule x = x"

ML_file \<open>library/reasoner.ML\<close>

attribute_setup \<nu>reason =
\<open>let open Args Scan Parse in
  (lift (optional (Parse.int >> ~) ~100) -- option (lift ($$$ "on") |-- term_pattern)
        >> Nu_Reasoner.attr_add_intro)
  || (lift (add |-- (Parse.int >> ~)) -- option (lift ($$$ "on") |-- term_pattern)
        >> Nu_Reasoner.attr_add_intro)
  || (lift del >> K Nu_Reasoner.attr_del_intro)
end\<close>
\<open>Set introduction rules in \<nu> reasonser.
  Syntax: \<nu>intro [add] <spur-of-the-rule> || \<nu>intro del\<close>

attribute_setup \<nu>reasoner_elim =
\<open>(Scan.lift (Parse.int >> ~) >> Nu_Reasoner.attr_add_elim)
  || (Scan.lift (Args.add |-- (Parse.int >> ~)) >> Nu_Reasoner.attr_add_elim)
  || (Scan.lift Args.del >> K Nu_Reasoner.attr_del_elim)\<close>
  \<open>Set elimduction rules in \<nu> reasonser.
  Syntax: \<nu>reasoner_elim [add] <spur-of-the-rule> || \<nu>elim del\<close>


declare conjI[\<nu>reason] TrueI[\<nu>reason 5000 on ?any]

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

definition Premise :: "mode \<Rightarrow> bool \<Rightarrow> bool" where [\<nu>def]:"Premise _ x = x"

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
lemma [elim!,\<nu>elim]: "Premise mode P \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> C" unfolding Premise_def by simp

lemma Premise_Irew: "(P \<Longrightarrow> C) \<equiv> Trueprop (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<longrightarrow> C)" unfolding Premise_def atomize_imp .

lemma [\<nu>reason 5000]: "Premise mode True" unfolding Premise_def ..
lemma [\<nu>reason 5000]:
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

\<nu>reasoner Premise_refl 2000 (\<open>Premise mode (x = x)\<close>) = \<open>fn ctxt =>
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

text \<open>The \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> indicate \<^term>\<open>x\<close> is a parameter that should be set by user, e.g.,
  \<^prop>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_size \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int value bit_size \<blangle> A \<longmapsto> B \<brangle>\<close>.
  The \<nu>-processor `set_param` processes the \<^term>\<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x\<close> antecedent.\<close>

lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto
lemma [cong]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<longleftrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" ..


subsubsection \<open>Label Input\<close>

definition LabelTag :: " label \<Rightarrow> bool" ("\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l _" [1000] 26) where "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<equiv> True"

text \<open>The \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> indicate \<^term>\<open>x\<close> is a \<^typ>\<open>label\<close> that should be set by user, e.g.,
  \<^prop>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l name \<Longrightarrow> do_something_relating name\<close>.
  The \<nu>-processor `set_label` processes the \<^term>\<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x\<close> antecedent.\<close>

lemma LabelTag: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x" unfolding LabelTag_def ..
lemma [elim!,\<nu>elim]: "\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l x \<Longrightarrow> C \<Longrightarrow> C" by auto


subsubsection \<open>Explicit name tag\<close>

definition Labelled :: "label \<Rightarrow> 'a \<Rightarrow> 'a" where "Labelled name x = x" \<comment>\<open>name tag\<close>
consts "named_sugar" :: " 'i_am \<Rightarrow> 'merely \<Rightarrow> 'a_sugar " ("\<ltbrak>_\<rtbrak>. _" [10,15] 14)
translations
  "\<ltbrak>name\<rtbrak>. x \<tycolon> T" == "x \<tycolon> (\<ltbrak>name\<rtbrak>. T)"
  "\<ltbrak>name\<rtbrak>. x" == "CONST Labelled (LABEL name) x"

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

\<nu>reasoner lambda_abstraction 1000 ("lambda_abstraction x Y name Y'") = \<open>fn ctxt => fn sequent =>
  let
    val _ $ (_ $ x $ Y $ (_ $ Abs (name,_,_)) $ Var Y'') = Thm.major_prem_of sequent
    val Y' = Abs(name, fastype_of x, abstract_over (x, Y))
            |> Thm.cterm_of ctxt
    val sequent = @{thm lambda_abstraction} RS Thm.instantiate ([],[(Y'',Y')]) sequent
  in
    Seq.single sequent
  end
\<close>

subsubsection \<open>Technical Tags\<close>

datatype uniq_id = UNIQ_ID
  \<comment> \<open>A technical tag that is during the exporting translated to a unique ID.
    It is useful to generate unique name of anonymous functions.\<close>

subsubsection \<open>Different tag\<close>

definition Different :: " 'a \<Rightarrow> 'b \<Rightarrow> bool " where "Different A B = True"
  \<comment> \<open>A premise that solved by automatic reasoning only if the term expressions of A and B
  are not alpha-equivalent. It is useful to break up the self-loop. For example,
  while the introduction rule `cast A \<longmapsto> B \<Longrightarrow> cast B \<longmapsto> C \<Longrightarrow> cast A \<longmapsto> C` causes loop if given `cast A \<longmapsto> A`,
  the rule `cast A \<longmapsto> B \<Longrightarrow> Different A B \<Longrightarrow> cast B \<longmapsto> C \<Longrightarrow> cast A \<longmapsto> C` will not.\<close>
lemma Different_I: "Different A B" unfolding Different_def ..

\<nu>reasoner Different -1 ("Different A B") = \<open>let open NuHelp in
  fn _ => fn th =>
  case try Thm.major_prem_of th
    of SOME prem =>
      (case try (dest_monop @{const_name Trueprop} #> dest_binop @{const_name "Different"}) prem
        of SOME (a,b) =>
          if Term.aconv (a,b) then Seq.empty else Seq.single (@{thm Different_I} RS th)
         | _ => Seq.empty)
     | _ => Seq.empty
end\<close>

subsection \<open>Cast\<close>

definition Cast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P)"
consts SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _)" [13,13] 12)
translations "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True)"

definition CastDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13,13] 12)
  where "CastDual A B P B' A' \<longleftrightarrow> (\<forall>v. v \<in> A \<longrightarrow> v \<in> B \<and> P \<and> (\<forall>u. u \<in> B' \<longrightarrow> u \<in> A'))"
  \<comment> \<open>Intuitively, A pair of dual casts A B P B' A' is the one cast A to B to satisfy some constraints
    usually to met the argument cells to be called and the dual one cast the return B' back to A',
    if B' has some correspondence with B, e.g. of the same nu-type. Usually the change between
    B and B' is to alter something of B like to change a field in B instead of destroying and creating
    a totally new B' irrelevant with B.\<close>

consts SimpCastDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [13,13,13] 12)
translations
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'"

translations
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B'"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l a' \<tycolon> A' \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<tort_lbrace>a' \<tycolon> A'\<tort_rbrace> \<longmapsto> B'"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> b' \<tycolon> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> \<tort_lbrace>b' \<tycolon> B'\<tort_rbrace>"


lemma cast_id[\<nu>reason 2000]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" unfolding Cast_def by fast
lemma cast_dual_id[\<nu>reason 2000]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B"
  unfolding CastDual_def by (simp add: cast_id)

lemma cast_id_ty[\<nu>reason 2200 on \<dots>]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = y \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> y \<tycolon> T" unfolding Cast_def by fast

lemma CastDual_I:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B' \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l B' \<longmapsto> A' "
  unfolding CastDual_def Cast_def by blast

lemma [\<nu>reason 10]: \<comment> \<open>Fallback\<close>
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l C \<longmapsto> C"
  unfolding Cast_def CastDual_def Premise_def by simp

(* abbreviation SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<equiv> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h True)" *)
(* lemma CastE[elim]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Cast_def Inhabited_def by (auto intro: Inhabited_subset)
lemma CastI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Cast_def Inhabited_def by auto *)

lemma ie_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma as_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> \<tort_lbrace>X'\<tort_rbrace> \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> \<tort_lbrace>X'\<tort_rbrace>" .

lemma cast_trans:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> (P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q)
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def by auto

lemma cast_dual_trans: 
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>d\<^bold>u\<^bold>a\<^bold>l B' \<longmapsto> A'
    \<Longrightarrow> (P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l C' \<longmapsto> B')
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l C' \<longmapsto> A'"
  unfolding Cast_def CastDual_def by auto


lemma cast_intro_frame:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t M \<heavy_asterisk> U' \<longmapsto> M \<heavy_asterisk> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  unfolding Cast_def pair_forall by blast

lemma cast_intro_frame_R:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<heavy_asterisk> M \<longmapsto> U \<heavy_asterisk> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P "
  unfolding Cast_def pair_forall by blast

lemma cast_dual_intro_frame:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t M \<heavy_asterisk> U' \<longmapsto> M \<heavy_asterisk> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l M\<^sub>m \<heavy_asterisk> V \<longmapsto> M\<^sub>m \<heavy_asterisk> V' "
  unfolding Cast_def CastDual_def pair_forall by blast

lemma cast_dual_intro_frame_R:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<heavy_asterisk> M \<longmapsto> U \<heavy_asterisk> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<heavy_asterisk> M\<^sub>m \<longmapsto> V' \<heavy_asterisk> M\<^sub>m "
  unfolding Cast_def CastDual_def pair_forall by blast



(* lemma dual_cast_fallback[\<nu>intro']: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<and> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t C \<longmapsto> C)" unfolding Cast_def by fast *)


subsection \<open>Tags II\<close>

subsubsection \<open>Auto tag\<close>

definition Auto :: " 'a \<Rightarrow> 'a " where "Auto x = x"

lemma [\<nu>reason]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t Y \<longmapsto> x \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Y \<longmapsto> x \<tycolon> Auto T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Auto_def .

lemma Auto_cong: "\<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> T'\<tort_rbrace> \<Longrightarrow> \<tort_lbrace>x \<tycolon> Auto T\<tort_rbrace> \<equiv> \<tort_lbrace>x' \<tycolon> Auto T'\<tort_rbrace>" unfolding atomize_eq Auto_def .
simproc_setup Auto_cong ("\<tort_lbrace>x \<tycolon> Auto T\<tort_rbrace>") = \<open>K (NuSimpCong.simproc @{thm Auto_cong})\<close>


subsubsection \<open>Argument tag\<close>

definition Argument :: "'a \<Rightarrow> 'a" ("\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t _" [11] 10) where "Argument x = x"

lemma Argument_I: "P \<Longrightarrow> Argument P" unfolding Argument_def .

text \<open>Sequent in pattern \<^prop>\<open>\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t P \<Longrightarrow> PROP Q\<close> hints users to input a theorem \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> P\<close>
  in order to deduce the sequent into \<^prop>\<open>A\<^sub>1 \<Longrightarrow> A\<^sub>n \<Longrightarrow> PROP Q\<close>, which is processed by the `rule` processor.
  Argument servers as a protector to prevent the unexpected auto-reasoning, e.g., the case for cast where
  the reasoner always attempts to solve an unprotected case premises and `Argument` tagging the Cast premise
  in this case prevent this automatic behavior when expecting user to input the cast rule.\<close>


subsection \<open>Protector\<close> \<comment> \<open>protecting from automatic transformations\<close>

definition Implicit_Protector :: " 'a \<Rightarrow> 'a " ("\<^bold>'( _ \<^bold>')") where "Implicit_Protector x = x"
  \<comment> \<open>The protector inside the construction of a procedure or sub-procedure, which is stripped
    after the construction. In future if the demand is seen, there may be an explicit protector
    declared explicitly by users and will not be stripped automatically.\<close>

lemma [cong]: "\<^bold>( A \<^bold>) = \<^bold>( A \<^bold>)" ..
lemma [\<nu>reason 1000]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<^bold>( A \<^bold>) \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Implicit_Protector_def .
lemma [\<nu>reason 1000]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<^bold>( B \<^bold>) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Implicit_Protector_def .

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

\<nu>reasoner \<open>Default_Simplify\<close> 1000 (\<open>Default_Simplify x y\<close>) = \<open>fn ctx =>
  HEADGOAL (asm_simp_tac ctx) THEN
  HEADGOAL (resolve0_tac @{thms Simplify_I})
\<close>


subsubsection \<open>Cast Simplifier\<close>

named_theorems cast_simp
consts cast_simp_setting :: mode

abbreviation Cast_Simplify :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>c\<^bold>a\<^bold>s\<^bold>t] _ : _" [1000,10] 9)
  where "Cast_Simplify \<equiv> Simplify cast_simp_setting"

\<nu>reasoner \<open>Cast_Simplify\<close> 1000 (\<open>Cast_Simplify x y\<close>) = \<open>fn ctx =>
  let val ctx = Raw_Simplifier.clear_simpset ctx
          addsimps Named_Theorems.get ctx \<^named_theorems>\<open>cast_simp\<close>
  in HEADGOAL (simp_tac ctx) THEN
     HEADGOAL (resolve0_tac @{thms Simplify_I})
  end
\<close>


subsection \<open>Miscellaneous\<close>

subsubsection \<open>Finalization Rewrites\<close>

named_theorems final_proc_rewrite \<open>rewrite the generated procedure theorem in the final stage\<close>

lemma [final_proc_rewrite]: "f \<then> nop \<equiv> f" and [final_proc_rewrite]: "nop \<then> f \<equiv> f"
  unfolding instr_comp_def nop_def bind_def atomize_eq by auto

(* lemmas [final_proc_rewrite] = WorkingProtector_def *)

section \<open>Syntax\<close>

subsection \<open>Syntax Helper\<close>

ML \<open>
fun parse_typing_ty (Type (\<^type_name>\<open>typing\<close>, [a,b])) = (b, a --> b --> \<^typ>\<open>bool\<close>)
  | parse_typing_ty dummyT = (dummyT, dummyT)
  | parse_typing_ty ty = raise TYPE ("should be a typing type", [ty], [])

fun parse_typing (Free (name, ty)) =
    Const (\<^const_syntax>\<open>typing\<close>, ty) $ Free (name^"\<^sub>x", fst (parse_typing_ty ty))
        $ Free (name^"\<^sub>t\<^sub>y", snd (parse_typing_ty ty))
  | parse_typing (Var ((name,ind), ty)) =
    Const (\<^const_syntax>\<open>typing\<close>, ty) $ Var ((name^"\<^sub>x",ind), fst (parse_typing_ty ty))
        $ Var ((name^"\<^sub>t\<^sub>y", ind), snd (parse_typing_ty ty))
  | parse_typing (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tm $ (Const (\<^type_syntax>\<open>typing\<close>, _) $ tya $ tyb)) =
      let val (const $ tmx $ tmty) = parse_typing tm
      in const $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmx $ tyb)
        $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmty $ (Const (\<^type_syntax>\<open>\<nu>\<close>, dummyT) $ tya $ tyb)) end
  | parse_typing (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tm $ markup) =
      let val (const $ tmx $ tmty) = parse_typing tm
      in const $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmx $ markup)
        $ (Const (\<^syntax_const>\<open>_constrain\<close>, ty) $ tmty $ markup) end
  | parse_typing (tm as Const (\<^const_syntax>\<open>typing\<close>, _) $ _ $ _) = tm
  | parse_typing tm = raise TERM ("should be a NuPrime.typing term", [tm])

fun parse_typing_x tm = (case parse_typing tm of _ $ x $ _ => x)
fun parse_typing_ty tm = (case parse_typing tm of _ $ _ $ ty => ty)
\<close>

syntax "_\<nu>typing" :: " logic \<Rightarrow> logic "
  "_\<nu>typing_x" :: " logic \<Rightarrow> logic "
  "_\<nu>typing_ty" :: " logic \<Rightarrow> logic "
parse_translation \<open>[
  (\<^syntax_const>\<open>_\<nu>typing\<close>, (fn _ => fn [tm] => parse_typing tm)),
  (\<^syntax_const>\<open>_\<nu>typing_x\<close>, (fn _ => fn [tm] => parse_typing_x tm)),
  (\<^syntax_const>\<open>_\<nu>typing_ty\<close>, (fn _ => fn [tm] => parse_typing_ty tm))
]\<close>


subsection \<open>Logical image models\<close>

text \<open>A set of models having common meanings, useful for representing logical images\<close>

consts val_of :: " 'a \<Rightarrow> 'b "
consts key_of :: " 'a \<Rightarrow> 'b "

datatype ('a, 'b) object (infixr "\<R_arr_tail>" 60) = object (key_of_obj: 'a) (val_of_obj: 'b) (infixr "\<R_arr_tail>" 60)
adhoc_overloading key_of key_of_obj and val_of val_of_obj
declare object.split[split]

lemma object_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_All[lrep_exps]: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (a \<R_arr_tail> b))" 
proof fix a b assume "(\<And>x. PROP P x) " then show "PROP P (a \<R_arr_tail> b)" .
next fix x assume "\<And>a b. PROP P (a \<R_arr_tail> b)"
    from \<open>PROP P (key_of x \<R_arr_tail> val_of x)\<close> show "PROP P x" by simp
qed

section \<open>Essential Low Models\<close>

class field = lrep \<comment> \<open>a field in the record tuple\<close>
class field_list = lrep

subsection \<open>Void\<close>

datatype void = void
declare void.split[split]

lemma [simp]: "x = y" for x :: void by (cases x; cases y) fast
lemma void_exists[simp]: "Ex P \<longleftrightarrow> P void" by (metis void.exhaust) 
lemma void_forall[simp]: "Ex P \<longleftrightarrow> P void" by (metis void.exhaust) 

subsubsection \<open>Settings\<close>

instantiation void :: "stack" begin
definition llty_void :: "void itself \<Rightarrow> llty" where "llty_void _ = llty_nil"
definition deepize_void :: "void \<Rightarrow> value" where [simp]: "deepize_void _ = DM_void"
definition stack_deepize_void :: " void \<Rightarrow> stack " where [simp]: "stack_deepize_void _ = stack []"
definition stack_shallowize_void :: " stack \<Rightarrow> void " where [simp]: "stack_shallowize_void _ = void"
instance by standard (auto simp add: deepize_void_def)
end

instantiation void :: field begin instance by standard end
instantiation void :: field_list begin instance by standard end

instantiation void :: zero begin
definition zero_void :: "void" where [simp]: "zero_void = void"
instance by standard
end


subsection \<open>Prod & the pair abstract structure\<close>

instantiation prod :: (field, field_list) field_list begin instance by standard end

instantiation prod :: (zero, zero) zero begin
definition zero_prod :: "'a \<times> 'b" where [simp]: "zero_prod = (0,0)"
instance by standard
end
instantiation prod :: (ceq, ceq) ceq begin
definition ceqable_prod :: "heap \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceqable_prod heap = ceqable heap \<times>\<^sub>r ceqable heap"
lemma [simp]: "ceqable heap (a1,b1) (a2,b2) \<longleftrightarrow> ceqable heap a1 a2 \<and> ceqable heap b1 b2" unfolding ceqable_prod_def by auto
definition ceq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceq_prod = ceq \<times>\<^sub>r ceq"
lemma [simp]: "ceq (a1,b1) (a2,b2) \<longleftrightarrow> ceq a1 a2 \<and> ceq b1 b2" unfolding ceq_prod_def by auto
instance by standard (auto intro: ceq_trans)
end


section \<open>Essential \<nu>-abstractor\<close>

subsection \<open>Separation Conjecture on Pure Heap\<close>

definition HeapSeparation :: " (heap, 'a) \<nu> \<Rightarrow> (heap, 'b) \<nu> \<Rightarrow> (heap, 'a \<times> 'b) \<nu>" (infixr "\<^emph>" 70)
  where "A \<^emph> B = (\<lambda>(a,b) . {h. (\<exists>h2 h1. h = h2 ++ h1 \<and> dom h2 \<perpendicular> dom h1 \<and> (h1 \<nuLinkL> A \<nuLinkR> a) \<and> (h2 \<nuLinkL> B \<nuLinkR> b))})"

lemma [nu_exps]: "h \<nuLinkL> A \<^emph> B \<nuLinkR> (a,b) \<longleftrightarrow>
  (\<exists>h2 h1. h = h2 ++ h1 \<and> dom h2 \<perpendicular> dom h1 \<and> (h1 \<nuLinkL> A \<nuLinkR> a) \<and> (h2 \<nuLinkL> B \<nuLinkR> b))"
  unfolding HeapSeparation_def Refining_def by simp


lemma SepNu_to_SepSet: "(OBJ (a,b) \<tycolon> A \<^emph> B) = (a \<tycolon> A \<heavy_asterisk> b \<tycolon> B)"
  by (simp add: nu_exps set_eq_iff) blast

lemma [simp]: "A \<inter> S \<perpendicular> A \<inter> -S"
  unfolding disjoint_def by auto
lemma heap_split_id: "P h1' h2' \<Longrightarrow> \<exists>h1 h2. h1' ++ h2' = h1 ++ h2 \<and> P h1 h2" by auto
lemma heap_split_by_set: "P (h |` S) (h |` (- S)) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  by (rule exI[of _ "h |` S"], rule exI[of _ "h |` (- S)"])
    (auto simp add: map_add_def option.case_eq_if restrict_map_def disjoint_def disjoint_iff domIff)
lemma heap_split_by_addr_set: "P (h |` (MemAddress ` S)) (h |` (- (MemAddress ` S))) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  using heap_split_by_set .


subsection \<open>Fusion and its derivatives\<close>

subsubsection \<open>Fusion\<close>

definition Fusion :: "('a1,'b1) \<nu> \<Rightarrow> ('a2,'b2) \<nu> \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) \<nu>" (infixr "\<cross_product>" 70) 
  where "Fusion N M x = {(p1,p2). case x of (x1,x2) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)}"

lemma [nu_exps]: "(p1,p2) \<nuLinkL> N \<cross_product> M \<nuLinkR> (x1,x2) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)"
  by (simp add: Fusion_def Refining_def)
lemma [elim,\<nu>elim]: "(x1,x2) \<ratio> N1 \<cross_product> N2 \<Longrightarrow> (x1 \<ratio> N1 \<Longrightarrow> x2 \<ratio> N2 \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (simp add: nu_exps)

lemma [\<nu>reason]: "\<nu>Zero N z1 \<Longrightarrow> \<nu>Zero M z2 \<Longrightarrow> \<nu>Zero (N \<cross_product> M) (z1,z2)" unfolding \<nu>Zero_def by (simp add: nu_exps)

lemma [\<nu>reason on \<open>\<^bold>c\<^bold>a\<^bold>s\<^bold>t (?x,?y) \<tycolon> ?N \<cross_product> ?M \<longmapsto> (?x',?y') \<tycolon> ?N' \<cross_product> ?M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M \<longmapsto> y' \<tycolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (x,y) \<tycolon> N \<cross_product> M \<longmapsto> (x',y') \<tycolon> N' \<cross_product> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2" unfolding Cast_def by (simp add: nu_exps) blast

(* no_notation RepSet ("\<tort_lbrace> _ \<tort_rbrace>" [10] )
syntax "_RepSet" :: "\<nu>typing \<Rightarrow> 'a set"  ("\<tort_lbrace> _ \<tort_rbrace>" [10] )
translations "_RepSet A " \<rightleftharpoons> "CONST RepSet (A)"
term "\<tort_lbrace> a \<tycolon> A\<tort_rbrace> " *)


subsection \<open>Subjection : coheres additional proposition\<close>

definition Subjection :: " 'p set \<Rightarrow> bool \<Rightarrow> 'p set " (infixl "\<^bold>s\<^bold>u\<^bold>b\<^bold>j" 13) where " (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = {p. p \<in> T \<and> P}"
translations "(x \<tycolon> T) \<^bold>s\<^bold>u\<^bold>b\<^bold>j P" \<rightleftharpoons> "\<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<^bold>s\<^bold>u\<^bold>b\<^bold>j P"
lemma [nu_exps]: "p \<in> (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> p \<in> T \<and> P" unfolding Subjection_def by simp

lemma [\<nu>reason]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Premise_def by (simp add: nu_exps)

lemma [simp]: "(T \<^bold>s\<^bold>u\<^bold>b\<^bold>j True) = T" unfolding Auto_def by (auto simp add: nu_exps)
lemma [simp,cast_simp]: "(R \<heavy_asterisk> (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (R \<heavy_asterisk> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)"
  by (simp add: set_eq_iff nu_exps Separation_expn) blast

lemma Subjection_simp_proc_arg[simp]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> Y \<brangle> = (P \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> T \<longmapsto> Y \<brangle>)"
  (* and Subjection_simp_func_arg[simp]: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<blangle> T \<and>\<^sup>s P \<longmapsto> Y \<brangle> = (P \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<blangle> T \<longmapsto> Y \<brangle>)" *)
  unfolding Auto_def Procedure_def by (simp add: nu_exps LooseStateTy_expn') blast

lemma [simp]: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P"
  unfolding CurrentConstruction_def Auto_def by (cases s) (simp_all add: nu_exps pair_All)
lemma [simp]: "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> B) \<and> C \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> (B \<and> C)" by simp

lemma subj_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<^bold>( T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<^bold>)"
  unfolding Cast_def Premise_def Implicit_Protector_def by simp

translations
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> a \<tycolon> A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> B \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> CONST Ele \<tort_lbrace> a \<tycolon> A \<tort_rbrace> \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> B \<brangle>"
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> b \<tycolon> B \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> CONST Ele \<tort_lbrace> b \<tycolon> B \<tort_rbrace> \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<brangle>"


subsection \<open>Existential Nu-set\<close>

definition ExSet :: " ('c \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "\<exists>*" 10)
  where "ExSet S = {p. (\<exists>c. p \<in> S c)}"
notation ExSet (binder "\<exists>\<^sup>s" 10)
translations "\<exists>* idts. x \<tycolon> T" \<rightleftharpoons> "\<exists>* idts. \<tort_lbrace>x \<tycolon> T\<tort_rbrace>"

lemma [nu_exps]: "p \<in> ExSet S \<longleftrightarrow> (\<exists>c. p \<in> S c)" unfolding ExSet_def by simp

lemma ExSet_pair: "ExSet T = (\<exists>*c1 c2. T (c1,c2) )" by (auto simp add: nu_exps)
lemma named_ExSet: "(ExSet T) = (\<exists>*c. T (tag c) )" by (auto simp add: named_exists nu_exps)

lemma [simp]: "p \<in> \<S>  (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> \<S>  (T z) )" by (cases p, simp_all add: nu_exps set_eq_iff)
lemma [simp]: "p \<in> !\<S> (ExSet T) \<longleftrightarrow> (\<exists>z. p \<in> !\<S> (T z) )" by (cases p, simp_all add: nu_exps set_eq_iff)
lemma [simp]: "(VAL ExSet T) = (\<exists>*c. VAL T c)" by (simp add: nu_exps set_eq_iff) blast
lemma [simp]: "(OBJ ExSet T) = (\<exists>*c. OBJ T c)" by (simp add: nu_exps set_eq_iff)
lemma [simp]: "(ExSet T \<heavy_asterisk> R) = (\<exists>* c. T c \<heavy_asterisk> R )" by (simp add: nu_exps set_eq_iff Separation_expn) blast
lemma [simp,cast_simp]: "(L \<heavy_asterisk> ExSet T) = (\<exists>* c. L \<heavy_asterisk> T c)" by (simp add: nu_exps set_eq_iff Separation_expn) blast

lemma ExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (ExSet T)) \<equiv> (\<exists>c. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T c)"
  unfolding CurrentConstruction_def atomize_eq by (cases p, simp_all add: nu_exps pair_All)

lemma [\<nu>reason 200]: "(\<And>c. \<^bold>c\<^bold>a\<^bold>s\<^bold>t T c \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P c) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (ExSet T) \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>c. P c)"
  unfolding Cast_def by (simp add: nu_exps) blast

lemma ExTyp_I_\<nu>app: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t T c \<longmapsto> (\<exists>*c. T c)"
  unfolding Cast_def by (simp add: nu_exps) blast

lemma generalize_\<nu>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m c \<Longrightarrow> \<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l name \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P c
    \<Longrightarrow> lambda_abstraction c (T' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P c) name T \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T' \<longmapsto> \<^bold>( ExSet T \<^bold>) "
  unfolding Cast_def Implicit_Protector_def lambda_abstraction_def by (auto simp add: nu_exps)

syntax
  "_SetcomprNu" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"  ("_ \<^bold>s\<^bold>u\<^bold>b\<^bold>j/ _./ _ " [2,0,2] 2)

translations
  " X \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. P " \<rightleftharpoons> "\<exists>* idts. X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P"
  " X \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. P " <= " \<tort_lbrace> X \<tort_rbrace> \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. P "
  " X \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. CONST True " \<rightleftharpoons> "\<exists>* idts. X"

translations
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> a \<tycolon> A \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. P \<longmapsto> B \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> CONST Ele \<tort_lbrace> a \<tycolon> A \<tort_rbrace> \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. P \<longmapsto> B \<brangle>"
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> b \<tycolon> B \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. Q \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> CONST Ele \<tort_lbrace> b \<tycolon> B \<tort_rbrace> \<^bold>s\<^bold>u\<^bold>b\<^bold>j idts. Q \<brangle>"


lemma " Union { S x |x. P x } = (S x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x) "
  by (simp add: set_eq_iff nu_exps) blast


subsection \<open>Identity\<close>

definition Identity :: " ('a::lrep, 'a) \<nu> " where "Identity x = {x}"
lemma [simp]: "p \<nuLinkL> Identity \<nuLinkR> x \<longleftrightarrow> p = x" unfolding Refining_def Identity_def by auto

subsection \<open>Refinement\<close>

definition NuRefine :: " ('a, 'b) \<nu> \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) \<nu> " (infixl "\<nuRefine>" 80)
  where "(N \<nuRefine> T) x = {p. (x \<in> T \<and>(p \<nuLinkL> N \<nuLinkR> x))}"

notation NuRefine (infixl "<where>" 80)

lemma [simp]: " p \<nuLinkL> N \<nuRefine> P \<nuLinkR> x \<longleftrightarrow> x \<in> P \<and> ( p \<nuLinkL> N \<nuLinkR> x)" unfolding NuRefine_def Refining_def by simp
lemma [elim,\<nu>elim]: " x \<ratio> N \<nuRefine> P \<Longrightarrow> (x \<in> P \<Longrightarrow> x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (simp add: nu_exps)

lemma [\<nu>reason]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x' \<tycolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x' \<in> S \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x' \<tycolon> M' <where> S \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 30 on \<open>\<^bold>c\<^bold>a\<^bold>s\<^bold>t ?x \<tycolon> ?T <where> ?S \<longmapsto> ?Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P''\<close>, \<nu>overload D]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T <where> S \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> x \<in> S"
  unfolding Cast_def by (simp add: nu_exps) blast

lemma refine_\<nu>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x \<tycolon> (N <where> P)"
  unfolding Cast_def by (simp add: nu_exps) blast

(* TODO: TO BE REMOVED *)
abbreviation AutoRefine (infixl "<auto-where>" 80)
  where "AutoRefine N P \<equiv> Auto (NuRefine N P)"

lemma [simp]:"\<tort_lbrace>x \<tycolon> T <auto-where> P \<tort_rbrace> = ((x \<tycolon> T) \<^bold>s\<^bold>u\<^bold>b\<^bold>j (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x \<in> P))"
  unfolding Auto_def Premise_def by (auto simp add: nu_exps)

lemma NuRefine_to_auto:"\<tort_lbrace>x \<tycolon> T <where> P \<tort_rbrace> = \<tort_lbrace>x \<tycolon> T <auto-where> P \<tort_rbrace>" unfolding Auto_def ..

(* lemma [\<nu>intro]: "(x \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuRefine> P \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<and>x \<in> P" unfolding Cast_def by auto
lemma [\<nu>intro]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <where> P \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q" unfolding Cast_def by auto
(* lemma [\<nu>cast_overload E]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> (N \<^bold>w\<^bold>h\<^bold>e\<^bold>r\<^bold>e P) \<longmapsto> x \<tycolon> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h x \<in> P" unfolding Cast_def by auto *)
*)
lemma [\<nu>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e z \<in> S \<Longrightarrow> \<nu>Zero N z \<Longrightarrow> \<nu>Zero (N <where> S) z"
  unfolding \<nu>Zero_def Premise_def by (simp add: nu_exps)
lemma "\<nu>Equal (N <where> P) can_eq eq \<longleftrightarrow> \<nu>Equal N (\<lambda>x y. x \<in> P \<and> y \<in> P \<and> can_eq x y) eq"
  unfolding \<nu>Equal_def by (simp add: nu_exps) blast


subsection \<open>Down Lifting\<close>

definition DownLift :: "('a, 'b) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'c) \<nu>" (infixl "<down-lift>" 80)
  where "DownLift N g x = {p. ( p \<nuLinkL> N \<nuLinkR> g x)}"

lemma [simp]: " p \<nuLinkL> N <down-lift> g \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> N \<nuLinkR> g x"
  unfolding DownLift_def Refining_def by simp
lemma [elim,\<nu>elim]: " x \<ratio> N <down-lift> g \<Longrightarrow> ( g x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (simp add: nu_exps)

(* lemma [\<nu>cast_overload E]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> g x \<tycolon> N" unfolding Cast_def by simp *)
lemma [\<nu>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N <down-lift> g \<longmapsto> x' \<tycolon> N" unfolding Cast_def by (simp add: nu_exps) blast

(* lemma [\<nu>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (g y = x) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M <down-lift> g"
  unfolding Intro_def Cast_def by (simp add: nu_exps) blast
lemma [\<nu>reason, \<nu>overload D]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <down-lift> g \<longmapsto> g y \<tycolon> M"
  unfolding Dest_def Cast_def by (simp add: nu_exps) *)

lemma [\<nu>reason]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y1 \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y1 = g y  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M <down-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast
lemma "\<down>lift_\<nu>app": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e g y = x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> N <down-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast


abbreviation AutoDownLift (infixl "<auto-down-lift>" 80) where "AutoDownLift T f \<equiv> Auto (DownLift T f)"

lemma [simp]:"\<tort_lbrace>x \<tycolon> T <auto-down-lift> f \<tort_rbrace> = \<tort_lbrace> f x \<tycolon> T \<tort_rbrace>" unfolding Auto_def by (auto simp add: nu_exps)


subsection \<open>Up Lifting\<close>

definition UpLift :: "('a, 'c) \<nu> \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('a,'b) \<nu>" (infixl "<up-lift>" 80)
  where "UpLift N f x = {p. (\<exists>y. f y = x \<and> ( p \<nuLinkL> N \<nuLinkR> y))}"

lemma [simp]: " p \<nuLinkL> N <up-lift> f \<nuLinkR> x \<longleftrightarrow> (\<exists>y. (f y = x) \<and> (p \<nuLinkL> N \<nuLinkR> y))"
  unfolding UpLift_def Refining_def by auto
lemma [elim,\<nu>elim]: " x \<ratio> N <up-lift> f \<Longrightarrow> (\<And>y. f y = x \<Longrightarrow> y \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: nu_exps) blast

lemma "\<up>lift_\<nu>app": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m g \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M <up-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast
(* lemma [\<nu>overload D]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M <up-lift> g \<longmapsto> (\<exists> \<tycolon> M) "
  unfolding Cast_def by (simp add: nu_exps) blast *)

(* lemma [\<nu>reason]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M <up-lift> g"
  unfolding Intro_def Cast_def by (simp add: nu_exps) blast *)
lemma [\<nu>reason 130]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> x' \<tycolon> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y = g x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y \<tycolon> M' <up-lift> g"
  unfolding Cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 20]: "(\<And> x. y = g x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P x) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> N \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>x. y = g x \<and> P x)"
  unfolding Cast_def by (simp add: nu_exps) blast
lemma [\<nu>reason 150]:
  "(\<And> x. y = g x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> M \<longmapsto> y' x \<tycolon> M' x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P x)
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> (\<exists>*x. \<tort_lbrace>y' x \<tycolon> M' x\<tort_rbrace> ) \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<exists>x. y = g x \<and> P x)"
  unfolding Cast_def by (simp add: nu_exps) blast

(* lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M <up-lift> g \<longmapsto> (\<exists>* x. (x \<tycolon> M) \<and>\<^sup>s g x = y)"
  unfolding Dest_def Cast_def by (simp add: nu_exps) blast *)

lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> f x \<tycolon> N <up-lift> f" unfolding Cast_def by (simp add: nu_exps) blast
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> f x \<tycolon> N <up-lift> f" unfolding Cast_def by (simp add: nu_exps) blast

lemma "\<nu>Equal (N <up-lift> f) can_eq eq \<longleftrightarrow> \<nu>Equal N (inv_imagep can_eq f) (inv_imagep eq f)"
  unfolding \<nu>Equal_def by (auto 0 6)


subsubsection \<open>Operator Some\<close>

definition NuSome :: " ('a :: lrep, 'b) \<nu> \<Rightarrow> ('a :: lrep, 'b set) \<nu> " ("<some>")
  where "NuSome T S = {p. (\<exists>x. x \<in> S \<and> (p \<nuLinkL> T \<nuLinkR> x)) }"
notation NuSome ("\<^bold>s\<^bold>o\<^bold>m\<^bold>e")

lemma [simp]: "p \<nuLinkL> \<^bold>s\<^bold>o\<^bold>m\<^bold>e T \<nuLinkR> X \<longleftrightarrow> (\<exists>x. x \<in> X \<and> (p \<nuLinkL>T \<nuLinkR> x))" unfolding NuSome_def Refining_def by simp
lemma [elim,\<nu>elim]: "X \<ratio> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e T) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<ratio> T \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by simp blast
(* lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X \<subseteq> X' \<Longrightarrow> [h] \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N) \<longmapsto> X' \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e N)" unfolding Cast_def by (auto 2 3) *)
lemma [\<nu>reason]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> y \<tycolon> M \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<in> Y \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> Y \<tycolon> (\<^bold>s\<^bold>o\<^bold>m\<^bold>e M) \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Cast_def by auto


section \<open>Mechanisms - II - Main Parts\<close>

ML_file NuBasics.ML

subsection \<open>Heap\<close>


definition Void :: "(heap \<times> stack) set" where "Void = { (Map.empty, stack []) }"

lemma "(h,s) \<in> Void \<longleftrightarrow> h = Map.empty \<and> s = stack []" unfolding Void_def by simp

lemma Separation_empty[iff]: "(Void \<heavy_asterisk> H) = H"  "(H \<heavy_asterisk> Void) = H"
  unfolding Void_def set_eq_iff by (simp_all add: nu_exps Separation_expn)


subsubsection \<open>Syntax & Auxiliary\<close>

consts ResourceState :: " heap \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> bool" ("_ \<^bold>a\<^bold>t _ \<^bold>i\<^bold>s _ " [16,16,12] 11)
consts allocated :: " heap \<Rightarrow> 'a \<Rightarrow> bool"

translations "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s x \<tycolon> T" \<rightleftharpoons> "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"

term "ofs + length xs \<le> segment_len base \<and> segment_llty base = LLTY('a::lrep)"
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
  unfolding MemAddrState_def addr_allocated_def by auto (metis \<nu>set_mono domI map_le_def option.sel) *)

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
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<nu>Independent S claim
    \<Longrightarrow> Alive k \<in> claim \<Longrightarrow> MemAddrState (h(k:=None)) addr S"
  unfolding MemAddrState_def \<nu>Independent_def by auto
lemma MemAddrState_retained_S[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<nu>Independent S claim
    \<Longrightarrow> Write k \<in> claim \<Longrightarrow> MemAddrState (h(k \<mapsto> v)) addr S"
  unfolding MemAddrState_def \<nu>Independent_def by auto

*)


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<in> S \<Longrightarrow> h |` S \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> MemAddress a \<notin> S \<Longrightarrow> h |` (- S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)


subsubsection \<open>Heap Tail & Frama Rule\<close>

declare Separation_assoc[cast_simp]


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

lemma [simp, \<nu>reason]: "NEW_MUTEX X" unfolding NEW_MUTEX_def ..
lemma [simp, \<nu>reason]: "MUTEX_ASSERT X" unfolding MUTEX_ASSERT_def ..
lemma [simp, \<nu>reason]: "MUTEX_SET X" unfolding MUTEX_SET_def ..

text \<open>Once a mutex is set, any \<^prop>\<open>MUTEX_ASSERT X\<close> will fail in the reasoning.\<close>


subsection \<open>Cast Reasoning\<close>


definition Cast_Target :: " 'a \<Rightarrow> 'a "  ("\<medium_left_bracket> _ \<medium_right_bracket>") where "\<medium_left_bracket> x \<medium_right_bracket> = x"
definition Cast_Target2 :: " 'a \<Rightarrow> reason_mutex \<Rightarrow> 'a "  ("\<medium_left_bracket> _ \<medium_right_bracket>: _" [2,1000] 100) where "\<medium_left_bracket> x \<medium_right_bracket>: _ = x"

lemmas cast_def = Cast_Target_def Cast_Target2_def CastDual_def Cast_def

(* lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> H' \<heavy_asterisk> y \<tycolon> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> y\<^sub>m \<tycolon> Y \<longmapsto> x\<^sub>m \<tycolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> H' \<heavy_asterisk> \<medium_left_bracket> y \<tycolon> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> y\<^sub>m \<tycolon> Y \<medium_right_bracket> \<longmapsto> x\<^sub>m \<tycolon> X \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  unfolding Heap_Cast_Goal_def . *)
(* lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B" unfolding CastDual_def  by (simp add: cast_id) *)

(* lemma [\<nu>intro 1000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> H \<longmapsto> L \<heavy_asterisk> H \<^bold>d\<^bold>u\<^bold>a\<^bold>l L \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> L \<heavy_asterisk> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>"
  unfolding Heap_Cast_Goal_def using cast_dual_id . *)

subsubsection \<open>Initialization\<close>

lemma [\<nu>reason 2000]:
  "NEW_MUTEX G \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> \<medium_left_bracket> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t True \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding cast_def .

lemma Cast_Reasoning_Init_NoDual[no_atp]:
  "NEW_MUTEX G \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> \<medium_left_bracket> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t True \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Z \<longmapsto> Z \<medium_right_bracket>"
  unfolding cast_def by blast

lemma Cast_Reasoning_Init_Dual[no_atp]:
  "NEW_MUTEX G \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> \<medium_left_bracket> Y \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> Y' \<medium_right_bracket> \<longmapsto> X' \<medium_right_bracket>: G \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t True \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Y' \<longmapsto> X' \<medium_right_bracket>"
  unfolding cast_def by blast

\<nu>reasoner Cast_Reasoning_Init_Dual 1100 (" \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Z \<longmapsto> Z \<medium_right_bracket>")
 = \<open>fn ctxt => fn sequent =>
  let
    val (_ $ (Const (\<^const_name>\<open>Cast_Target\<close>, _) $
            (Const (\<^const_name>\<open>CastDual\<close>, _) $ _ $ _ $ _ $ Z $ _)))
        = Thm.major_prem_of sequent
  in
    if is_Var Z
    then Seq.single (@{thm Cast_Reasoning_Init_NoDual} RS sequent)
    else Seq.single (@{thm Cast_Reasoning_Init_Dual} RS sequent)
  end\<close>

subsubsection \<open>Identity Cast\<close>

lemma cast_dual_fallback:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Void \<heavy_asterisk> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> Void \<heavy_asterisk> H\<^sub>m \<medium_right_bracket>: G"
unfolding cast_def Separation_empty by blast+

\<nu>reasoner Cast_Reasoning_Dual_Id 3000 ("\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Z \<longmapsto> Z2 \<medium_right_bracket>: G") = \<open>fn ctxt => fn sequent =>
  let
    val (_ $ (_ $ (Const (\<^const_name>\<open>CastDual\<close>, _) $ _ $ _ $ _ $ Z $ Z2) $ _))
        = Thm.major_prem_of sequent
    val Z = case Z of (Const (\<^const_name>\<open>Cast_Target\<close>,_) $ Z') => Z'
        | (_ $ _ $ (Const (\<^const_name>\<open>Cast_Target\<close>,_) $ Z')) => Z'
  in
      if is_Var Z orelse Z aconv Z2
      then resolve_tac ctxt @{thms cast_dual_fallback} 1 sequent
      else Seq.empty
  end\<close>

lemma [\<nu>reason 3000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?H \<longmapsto> \<medium_left_bracket> ?H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
      "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> H \<medium_right_bracket> \<medium_right_bracket>: G"
  and [\<nu>reason 3000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?H \<longmapsto> ?R \<heavy_asterisk> \<medium_left_bracket> ?H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
      "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> Void \<heavy_asterisk> \<medium_left_bracket> H \<medium_right_bracket> \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty by blast+

(* lemma [\<nu>intro 40]: \<comment> \<open>outro\<close>
    "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> h \<tycolon> H \<longmapsto> H' \<heavy_asterisk> a' \<R_arr_tail> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> a' \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<longmapsto> a \<R_arr_tail> h\<^sub>m \<tycolon> H\<^sub>m \<Longrightarrow>
      \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> h \<tycolon> H \<longmapsto> H' \<heavy_asterisk> \<medium_left_bracket> Ele \<tort_lbrace> a' \<R_arr_tail> x \<tycolon> X \<tort_rbrace> \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> a' \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> a \<R_arr_tail> h\<^sub>m \<tycolon> H\<^sub>m \<medium_right_bracket>"
  and [\<nu>intro 40]:
    "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow> 
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> h \<tycolon> H \<longmapsto> H' \<heavy_asterisk> a' \<R_arr_tail> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> h \<tycolon> H \<longmapsto> H' \<heavy_asterisk> \<medium_left_bracket> a' \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  and [\<nu>intro 70]:
    "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> h \<tycolon> H \<longmapsto> a' \<R_arr_tail> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> h \<tycolon> H \<longmapsto> Void \<heavy_asterisk> \<medium_left_bracket> a' \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"*)
(*  and [\<nu>intro 70]:
    "\<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t h \<tycolon> H \<longmapsto> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>" 
  unfolding Heap_Cast_Goal_def Separation_emptyL .*)


subsubsection \<open>Void Holes\<close> \<comment> \<open>eliminate Void holes generated during the reasoning \<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> X \<heavy_asterisk> Void \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty  .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H'\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> H'\<^sub>m \<heavy_asterisk> Void \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty  .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> Void \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty  .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> X \<heavy_asterisk> Void \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> Void \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

subsubsection \<open>Pad Void Holes at left\<close> \<comment> \<open>to standardize\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> Void \<heavy_asterisk> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> Void \<heavy_asterisk> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Void \<heavy_asterisk> VAL T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t VAL T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Void \<heavy_asterisk> OBJ T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Void \<heavy_asterisk> VAL T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t VAL T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Void \<heavy_asterisk> OBJ T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ T \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l X' \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def Separation_empty .

subsubsection \<open>Subjection\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   (P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e Q) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> (U \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U\<^sub>m \<longmapsto> T\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?T \<longmapsto> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?U\<^sub>m \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q \<medium_right_bracket> \<longmapsto> ?T'''\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<medium_right_bracket> \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket> \<longmapsto> T\<^sub>m \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<medium_right_bracket>: G" 
  unfolding cast_def by (simp add: nu_exps)

subsubsection \<open>Protector\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> \<^bold>( U \<^bold>) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def Implicit_Protector_def by (simp add: nu_exps)

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U' \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> \<^bold>( U \<^bold>) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U' \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def Implicit_Protector_def by (simp add: nu_exps)

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U' \<medium_right_bracket> \<longmapsto> T' \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> \<^bold>( U' \<^bold>) \<medium_right_bracket> \<longmapsto> T' \<medium_right_bracket>: G"
  unfolding cast_def Implicit_Protector_def by (simp add: nu_exps)


subsubsection \<open>Existential\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U c \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> ExSet U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> U c \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<medium_right_bracket> \<longmapsto> T\<^sub>m \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> ExSet U \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m \<medium_right_bracket> \<longmapsto> T\<^sub>m \<medium_right_bracket>: G "
  unfolding cast_def by (simp add: nu_exps) blast

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?T \<longmapsto> ?U \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ExSet ?U\<^sub>m \<medium_right_bracket> \<longmapsto> ?T\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  "(\<And>c. \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> U\<^sub>m c \<medium_right_bracket> \<longmapsto> T\<^sub>m c \<medium_right_bracket>: G) \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ExSet U\<^sub>m \<medium_right_bracket> \<longmapsto> ExSet T\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def by (simp add: nu_exps) blast

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<nu>intro 1100]: \<comment> \<open>tail the step\<close>
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> Void \<heavy_asterisk> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Void \<heavy_asterisk> \<medium_left_bracket> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket> \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> VAL x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<medium_right_bracket> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<nu>intro 1100]: \<comment> \<open>tail the step\<close>
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> Void \<heavy_asterisk> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Void \<heavy_asterisk> \<medium_left_bracket> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket> \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsubsection \<open>Value\<close>

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> OBJ ?H \<longmapsto> ?R''' \<heavy_asterisk> \<medium_left_bracket> VAL ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> OBJ H \<longmapsto> R' \<heavy_asterisk> OBJ H \<heavy_asterisk> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G "
  unfolding cast_def pair_forall
  by (smt (verit, ccfv_threshold) Separation_assoc Separation_comm(1) Separation_expn_R)

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> VAL ?V \<longmapsto> ?R''' \<heavy_asterisk> \<medium_left_bracket> VAL ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " \<^bold>c\<^bold>a\<^bold>s\<^bold>t V \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> VAL V \<longmapsto> R \<heavy_asterisk> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (metis Separation_expn_V')

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_asterisk> VAL ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R1 \<heavy_asterisk> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R1 \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2  \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> \<medium_left_bracket> R2 \<heavy_asterisk> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>: G"
  unfolding cast_def Separation_expn_V' pair_forall
  by simp blast

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?H \<longmapsto> \<medium_left_bracket> ?H2 \<heavy_asterisk> VAL ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?H\<^sub>m \<longmapsto> ?H'\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H1 \<heavy_asterisk> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H1 \<longmapsto> \<medium_left_bracket> H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H'\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> \<medium_left_bracket> H2 \<heavy_asterisk> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H'\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Separation_expn_V' pair_forall
  by simp blast

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<longmapsto> ?R' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R\<^sub>m \<heavy_asterisk> VAL ?X \<medium_right_bracket> \<longmapsto> ?R'''\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R\<^sub>m \<medium_right_bracket> \<longmapsto> R'\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R\<^sub>m \<heavy_asterisk> VAL X \<medium_right_bracket> \<longmapsto> R'\<^sub>m \<heavy_asterisk> VAL X \<medium_right_bracket>: G"
  unfolding cast_def Separation_expn_V' pair_forall
  by simp blast


subsubsection \<open>Object\<close>

lemma [\<nu>reason 100 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> OBJ ?H \<longmapsto> ?R''' \<heavy_asterisk> \<medium_left_bracket> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " MUTEX_ASSERT G
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ H \<longmapsto> H' \<heavy_asterisk> OBJ X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> MUTEX_SET G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> OBJ H \<longmapsto> R \<heavy_asterisk> H' \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (smt (verit, ccfv_threshold) Separation_assoc Separation_comm(1) Separation_expn_R)

lemma [\<nu>reason 70 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> OBJ ?H \<longmapsto> ?R''' \<heavy_asterisk> \<medium_left_bracket> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]: \<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " MUTEX_ASSERT G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> MUTEX_SET G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> OBJ H \<longmapsto> R' \<heavy_asterisk> OBJ H \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G "
  unfolding cast_def pair_forall
  by (smt (verit, ccfv_threshold) Separation_assoc Separation_comm(1) Separation_expn_R)

lemma [\<nu>reason 10 on \<open>\<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ ?a \<R_arr_tail> ?x \<tycolon> ?T \<longmapsto> ?R''' \<heavy_asterisk> OBJ ?a' \<R_arr_tail> ?x' \<tycolon> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> x \<tycolon> T \<longmapsto> a' \<R_arr_tail> x' \<tycolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ a \<R_arr_tail> x \<tycolon> T \<longmapsto> Void \<heavy_asterisk> OBJ a' \<R_arr_tail> x' \<tycolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding cast_def pair_forall by (simp add: nu_exps)

lemma [\<nu>reason 1200 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> VAL ?V \<longmapsto> ?R''' \<heavy_asterisk> \<medium_left_bracket> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> VAL V \<longmapsto> R' \<heavy_asterisk> VAL V \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding cast_def pair_forall
  by (smt (verit, ccfv_threshold) Separation_assoc Separation_comm(1) Separation_expn_R)

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_asterisk> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<medium_right_bracket>: ?G\<close>]:
  " NEW_MUTEX G2 \<Longrightarrow> \<comment> \<open>make a new subgoal \<close>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R1 \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>: G2 \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R1 \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket>: G \<Longrightarrow>
   \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> \<medium_left_bracket> R2 \<heavy_asterisk> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>: G"
  unfolding cast_def Separation_expn_V' pair_forall
  by simp blast


text \<open>Dual cast of \<^term>\<open>OBJ a \<R_arr_tail> x \<tycolon> X \<close>. \<close>

lemma [\<nu>reason 100 on
    \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> OBJ ?H \<longmapsto> ?R''' \<heavy_asterisk> \<medium_left_bracket> OBJ ?a \<R_arr_tail> ?x \<tycolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R''\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ ?a\<^sub>m \<R_arr_tail> ?x\<^sub>m \<tycolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R2''\<^sub>m \<medium_right_bracket>: ?G\<close>]:
  \<comment> \<open>search the immediate H first\<close>
  " MUTEX_ASSERT G
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ H \<longmapsto> H' \<heavy_asterisk> OBJ a \<R_arr_tail> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<longmapsto> OBJ H\<^sub>m
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> OBJ H \<longmapsto> R \<heavy_asterisk> H' \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R \<heavy_asterisk> H'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R \<heavy_asterisk> OBJ H\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def  pair_forall
  by (smt (verit, ccfv_threshold) Separation_assoc Separation_comm(1) Separation_expn_R)

lemma [\<nu>reason 70
    on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> OBJ ?H \<longmapsto> ?R' \<heavy_asterisk> \<medium_left_bracket> OBJ ?a \<R_arr_tail> ?x \<tycolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ ?a\<^sub>m \<R_arr_tail> ?x\<^sub>m \<tycolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "MUTEX_ASSERT G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> OBJ H \<longmapsto> R' \<heavy_asterisk> OBJ H \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_asterisk> OBJ H \<heavy_asterisk> \<medium_left_bracket> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_asterisk> OBJ H \<medium_right_bracket>: G"
  unfolding Cast_Target_def Cast_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "OBJ H" "\<tort_lbrace>a \<R_arr_tail> x \<tycolon> X\<tort_rbrace>"] Separation_comm(2)[of "OBJ H" "\<tort_lbrace>a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R)

lemma [\<nu>reason 1200
    on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<heavy_asterisk> VAL ?V \<longmapsto> ?R' \<heavy_asterisk> \<medium_left_bracket> OBJ ?a \<R_arr_tail> ?x \<tycolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ ?a\<^sub>m \<R_arr_tail> ?x\<^sub>m \<tycolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "MUTEX_ASSERT G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> VAL V \<longmapsto> R' \<heavy_asterisk> VAL V \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_asterisk> VAL V \<heavy_asterisk> \<medium_left_bracket> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_asterisk> VAL V \<medium_right_bracket>: G"
  unfolding Cast_Target_def Cast_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a \<R_arr_tail> x \<tycolon> X\<tort_rbrace>"] Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  using cast_dual_intro_frame_R by blast

(* lemma [\<nu>reason 1200
    on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<longmapsto> ?R' \<heavy_asterisk> \<medium_left_bracket> OBJ ?a \<R_arr_tail> ?x \<tycolon> ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_asterisk> VAL ?V \<heavy_asterisk> \<medium_left_bracket> OBJ ?a\<^sub>m \<R_arr_tail> ?x\<^sub>m \<tycolon> ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  "MUTEX_ASSERT G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_asterisk> VAL V \<heavy_asterisk> \<medium_left_bracket> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_asterisk> VAL V \<medium_right_bracket>: G"
  unfolding Cast_Target_def Cast_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = Void, unfolded Separation_empty])
*)

lemma [\<nu>reason 30
     on \<open>\<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ ?a \<R_arr_tail> ?x \<tycolon> ?T \<longmapsto> ?R \<heavy_asterisk> OBJ ?a' \<R_arr_tail> ?x' \<tycolon> ?T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R2 \<heavy_asterisk> OBJ ?a\<^sub>m \<R_arr_tail> ?x\<^sub>m \<tycolon> ?X\<^sub>m \<longmapsto> ?H\<^sub>m\<close>
  ]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a' \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> x \<tycolon> T \<longmapsto>  a' \<R_arr_tail> x' \<tycolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<longmapsto> H\<^sub>m \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ a \<R_arr_tail> x \<tycolon> T \<longmapsto> Void \<heavy_asterisk> OBJ a' \<R_arr_tail> x' \<tycolon> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Void \<heavy_asterisk> a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> X\<^sub>m \<longmapsto> OBJ H\<^sub>m"
  unfolding cast_def Separation_empty by (simp add: pair_forall nu_exps)

lemma [\<nu>reason 10
    on \<open>\<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ ?H \<longmapsto> ?H' \<heavy_asterisk> OBJ ?a \<R_arr_tail> ?x \<tycolon> ?X \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R''' \<heavy_asterisk> OBJ ?X\<^sub>m \<longmapsto> ?R'''\<^sub>m\<close>
  ]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ H \<longmapsto> H' \<heavy_asterisk> OBJ a \<R_arr_tail> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ H \<longmapsto> H' \<heavy_asterisk> OBJ a \<R_arr_tail> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l Void \<heavy_asterisk> OBJ X\<^sub>m \<longmapsto> OBJ X\<^sub>m"
  unfolding cast_def Separation_empty by blast


text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<R_arr_tail> x \<tycolon> T\<close>\<close>

lemma [\<nu>reason 100
    on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_asterisk> OBJ ?a \<R_arr_tail> ?x \<tycolon> ?T \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P''' \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R2\<^sub>m \<heavy_asterisk> OBJ ?a\<^sub>m \<R_arr_tail> ?x\<^sub>m \<tycolon> ?T \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>step case 1\<close>
  " MUTEX_ASSERT G
    \<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a = a\<^sub>m \<comment> \<open> if addresses are matched\<close>
    \<Longrightarrow> NEW_MUTEX G1
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R1 \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x \<tycolon> T \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<^bold>d\<^bold>u\<^bold>a\<^bold>l R1\<^sub>m \<heavy_asterisk> \<medium_left_bracket> OBJ a \<R_arr_tail> x\<^sub>m \<tycolon> T \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G1 \<comment> \<open>do the dual cast\<close>
        \<comment> \<open>the condition requiring match of address here, is a fast maybe positive-false check \<close>
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> NEW_MUTEX G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R1 \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<medium_right_bracket> \<longmapsto> R1\<^sub>m \<medium_right_bracket>: G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> \<medium_left_bracket> R2 \<heavy_asterisk> OBJ a \<R_arr_tail> x \<tycolon> T \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<heavy_asterisk> OBJ a\<^sub>m \<R_arr_tail> x\<^sub>m \<tycolon> T \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Premise_def by simp blast

lemma [\<nu>reason 70
    on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<longmapsto> \<medium_left_bracket> ?R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R2\<^sub>m \<heavy_asterisk> OBJ ?X\<^sub>m \<medium_right_bracket> \<longmapsto> ?R\<^sub>m \<medium_right_bracket>: ?G\<close>
  ]: \<comment> \<open>step case 2\<close>
  " MUTEX_ASSERT G \<comment> \<open> if addresses are not matched, or the dual cast fails\<close>
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> NEW_MUTEX G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G2
        \<comment> \<open>pass the return object \<^term>\<open>X\<^sub>m\<close>, and in the new subgoal \<^term>\<open>G2\<close>,
          maybe, the dual cast is still available.\<close>
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> \<medium_left_bracket> R2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R2\<^sub>m \<heavy_asterisk> OBJ X\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<heavy_asterisk> OBJ X\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Premise_def by simp blast

lemma [\<nu>reason 50
    on \<open>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t ?R \<longmapsto> \<medium_left_bracket> ?R2 \<heavy_asterisk> OBJ ?X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> ?R\<^sub>m \<medium_right_bracket> \<longmapsto> ?R'''\<^sub>m \<medium_right_bracket>: G\<close>
  ]: \<comment> \<open>step case 3\<close>
  " MUTEX_ASSERT G \<comment> \<open> if even all return objects are passed\<close>
    \<Longrightarrow> MUTEX_SET G
    \<Longrightarrow> NEW_MUTEX G2
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> \<medium_left_bracket> R2 \<heavy_asterisk> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G2 \<comment> \<open>we give up the dual cast totally\<close>
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> \<medium_left_bracket> R2 \<heavy_asterisk> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<medium_left_bracket> R\<^sub>m \<medium_right_bracket> \<longmapsto> R\<^sub>m \<medium_right_bracket>: G"
  unfolding cast_def Premise_def by simp


subsubsection \<open>Plainize\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> T1 \<heavy_asterisk> T2 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> (T1 \<heavy_asterisk> T2) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding Separation_assoc .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> X1 \<heavy_asterisk> X2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> (X1 \<heavy_asterisk> X2) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>: G"
  unfolding Separation_assoc .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> T1 \<heavy_asterisk> T2 \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> (T1 \<heavy_asterisk> T2) \<longmapsto> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G"
  unfolding Separation_assoc .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> X1 \<heavy_asterisk> X2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> \<medium_left_bracket> R \<heavy_asterisk> (X1 \<heavy_asterisk> X2) \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l U \<longmapsto> U' \<medium_right_bracket>: G"
  unfolding Separation_assoc .

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R \<heavy_asterisk> U1 \<heavy_asterisk> U2 \<longmapsto> U' \<medium_right_bracket>: G
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R \<heavy_asterisk> (U1 \<heavy_asterisk> U2) \<longmapsto> U' \<medium_right_bracket>: G"
  unfolding Separation_assoc .

(*
subsection \<open>Scan\<close>

lemma [\<nu>intro 110]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> R \<longmapsto> L \<heavy_asterisk> R' \<heavy_asterisk> \<medium_left_bracket> VAL X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding cast_def Intro_def Dest_def pair_forall
  by (metis Separation_assoc Separation_expn)

lemma [\<nu>intro 110]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> R' \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> R \<longmapsto> L \<heavy_asterisk> R' \<heavy_asterisk> \<medium_left_bracket> OBJ X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding cast_def Intro_def Dest_def pair_forall
  by (metis Separation_assoc Separation_expn)

lemma [\<nu>intro 100]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<longmapsto> L' \<heavy_asterisk> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<heavy_asterisk> R \<longmapsto> H' \<heavy_asterisk> R \<heavy_asterisk> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def Intro_def Dest_def
    Separation_comm[of H R] Separation_comm[of H' R]
  by (metis Heap_Divider_exps Separation_assoc)

 






lemma heap_idx_R_dual[\<nu>intro 100]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H' \<heavy_asterisk> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> \<medium_left_bracket> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<medium_right_bracket>
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<heavy_asterisk> R \<longmapsto> H' \<heavy_asterisk> R \<heavy_asterisk> \<medium_left_bracket> x \<tycolon> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H'\<^sub>m \<heavy_asterisk> R \<heavy_asterisk> \<medium_left_bracket> x\<^sub>m \<tycolon> X\<^sub>m \<medium_right_bracket> \<longmapsto> H\<^sub>m \<heavy_asterisk> R \<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def Intro_def Dest_def
    Separation_comm[of H R] Separation_comm[of H\<^sub>m R]
    Separation_comm[of H' R] Separation_comm[of H'\<^sub>m R]
  by (metis Heap_Divider_exps Separation_assoc)




lemma [\<nu>intro 120]:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H1 \<heavy_asterisk> x \<tycolon> \<medium_left_bracket> X \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>
    \<Longrightarrow> (P1 \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H1 \<longmapsto> H\<^sub>r \<heavy_asterisk> h2 \<tycolon> \<medium_left_bracket> H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket>)
    \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<longmapsto> H\<^sub>r \<heavy_asterisk> (x, h2) \<tycolon> \<medium_left_bracket> X \<^emph> H2 \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>"
  unfolding Cast_def CastDual_def Heap_Cast_Goal_def HeapDivNu_to_SepSet SepNu_to_SepSet Intro_def Dest_def
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)
*)
(* lemma [ \<nu>intro -50 ]: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d \<tycolon> D \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> (P \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t d \<tycolon> D \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<tycolon> I'\<^sub>m \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> i \<tycolon> I \<medium_right_bracket>)
  \<Longrightarrow> (P \<Longrightarrow> P2 \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t i \<tycolon> I \<longmapsto> x\<^sub>m \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Anyway)
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<tycolon> I'\<^sub>m \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> x\<^sub>m \<tycolon> T \<medium_right_bracket>"
  unfolding Dest_def Intro_def CastDual_def Different_def Heap_Cast_Goal_def Cast_def
  by (auto simp add: Premise_def) *)

(* lemma [ \<nu>intro 50 ]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d \<tycolon> D \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> (P \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t d \<tycolon> D \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<^bold>d\<^bold>u\<^bold>a\<^bold>l i'\<^sub>m \<tycolon> I'\<^sub>m \<heavy_asterisk> h\<^sub>m \<tycolon> \<medium_left_bracket> H\<^sub>m \<medium_right_bracket> \<longmapsto> i \<tycolon> I \<medium_right_bracket>)
  \<Longrightarrow> (P \<Longrightarrow> P2 \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t i \<tycolon> I \<longmapsto> x\<^sub>m \<tycolon> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Anyway)
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> T \<longmapsto> d' \<tycolon> D' \<heavy_asterisk> h \<tycolon> \<medium_left_bracket> H \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> P2 \<medium_right_bracket>"
  unfolding Dest_def Intro_def CastDual_def Different_def Heap_Cast_Goal_def Cast_def
  by (auto simp add: Premise_def) *)



(* lemma heap_put_this: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t Void \<heavy_asterisk> x \<tycolon> X \<longmapsto> x \<tycolon> X" unfolding Cast_def Separation_emptyL by simp
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t s \<tycolon> S \<heavy_asterisk> x \<tycolon> X \<longmapsto> s' \<tycolon> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t l \<tycolon> L \<heavy_asterisk> s \<tycolon> S \<heavy_asterisk> x \<tycolon> X \<longmapsto> l \<tycolon> L \<heavy_asterisk> s' \<tycolon> S' "
  unfolding Cast_def HeapDivNu_to_SepSet
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t s \<tycolon> S \<heavy_asterisk> x \<tycolon> X \<longmapsto> s' \<tycolon> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (s \<tycolon> S \<heavy_asterisk> r \<tycolon> R) \<heavy_asterisk> x \<tycolon> X \<longmapsto> s' \<tycolon> S' \<heavy_asterisk> r \<tycolon> R "
  unfolding Cast_def HeapDivNu_to_SepSet
  by (smt (verit, del_insts) SeparationSet_assoc SeparationSet_comm SeparationSet_def mem_Collect_eq)
*)


(* lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t L \<heavy_asterisk> S \<longmapsto> L \<heavy_asterisk> S'"
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq
lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<heavy_asterisk> R \<longmapsto> S' \<heavy_asterisk> R"
  unfolding Cast_def by (smt (verit, del_insts) Separation_assoc Separation_comm Separation_def mem_Collect_eq *)


(*
subsubsection \<open>Other Reasoning Settings\<close>

lemma [\<nu>intro 14000]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<R_arr_tail> x = a \<R_arr_tail> x' " unfolding Premise_def by simp
(* lemma [\<nu>intro 13500]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<R_arr_tail> x = a' \<R_arr_tail> x' " unfolding Premise_def by simp *)

(*TODO: this rule is too aggressive. Maybe a assumption based flag switch?*)
lemma [\<nu>intro 13000]: "False \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e a \<R_arr_tail> x = a' \<R_arr_tail> x' " unfolding Premise_def by simp
  \<comment> \<open>For any other situation (when a is not alpha equivalent to a'), reasoning is pruned early.
  The proof for \<^term>\<open>a = a'\<close> is always assigned to users, because maintaining the consistency of object identities
    is so essential that users should always keep.\<close>
*)

subsection \<open>Case Analysis\<close>


lemma [\<nu>reason 1000]: "Premise mode (A = B x y) \<Longrightarrow> Premise mode (A = case_prod B (x,y))" by simp
lemma [\<nu>reason 1000]: "Premise mode (A = B x) \<Longrightarrow> Premise mode (A = case_named B (tag x))" by simp
lemma [\<nu>reason 1000]: "Premise mode (A = B a x) \<Longrightarrow> Premise mode (A = case_object B (a \<R_arr_tail> x))" by simp

definition CaseSplit :: "bool \<Rightarrow> bool" where "CaseSplit x = x"
lemma [elim!]: "CaseSplit x \<Longrightarrow> (x \<Longrightarrow> C) \<Longrightarrow> C" unfolding CaseSplit_def .

 lemma [elim!]:
  "y = case_prod f x \<Longrightarrow> (\<And>x1 x2. y = f x1 x2 \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of a \<R_arr_tail> b \<Rightarrow> f a b) \<Longrightarrow> (\<And>a b. y = f a b \<Longrightarrow> C (a \<R_arr_tail> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [elim!]:
  "y = (case x of tag a \<Rightarrow> f a) \<Longrightarrow> (\<And>a. y = f a \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp

(* lemma [\<nu>reasoner_elim 10002]:
  "CaseSplit (y = case_prod f x) \<Longrightarrow> (\<And>x1 x2. CaseSplit (y = f x1 x2) \<Longrightarrow> C (x1,x2)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [\<nu>reasoner_elim 10002]:
  "CaseSplit (y = (case x of a \<R_arr_tail> b \<Rightarrow> f a b)) \<Longrightarrow> (\<And>a b. CaseSplit (y = f a b) \<Longrightarrow> C (a \<R_arr_tail> b)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp
lemma [\<nu>reasoner_elim 10002]:
  "CaseSplit (y = (case x of tag a \<Rightarrow> f a)) \<Longrightarrow> (\<And>a. CaseSplit (y = f a) \<Longrightarrow> C (tag a)) \<Longrightarrow> C x"
  unfolding CaseSplit_def by (cases x) simp*)



subsection \<open>Cast\<close>

lemma "cast": "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket> \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  unfolding CurrentConstruction_def cast_def
  by (cases blk, simp_all add: pair_All nu_exps Separation_expn) blast
lemma "cast'": "\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<medium_right_bracket> \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  unfolding cast_def PendingConstruction_def by (auto 0 6 simp add: Shallowize'_expn)

lemma cast_\<nu>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> x' \<tycolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> VAL x \<tycolon> X \<longmapsto> R \<heavy_asterisk> x' \<tycolon> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> Y \<longmapsto> y' \<tycolon> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> OBJ y \<tycolon> Y \<longmapsto> R \<heavy_asterisk> y' \<tycolon> Y' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t VAL x \<tycolon> X \<longmapsto> XX \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> VAL x \<tycolon> X \<longmapsto> R \<heavy_asterisk> XX \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ y \<tycolon> Y \<longmapsto> YY \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<heavy_asterisk> OBJ y \<tycolon> Y \<longmapsto> R \<heavy_asterisk> YY \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Argument_def
  by (simp_all add: nu_exps Separation_expn) (metis append_Nil stack_inverse values_of_inverse)+

lemma cast_whole_\<nu>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def Argument_def by (simp add: nu_exps)


  lemma cast_conversion:
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<medium_right_bracket>
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t R \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding cast_def by blast


subsection \<open>Conversion\<close>
  
definition Conversion :: "('a::stack \<longmapsto> 'b::stack) \<Rightarrow> (heap\<times>stack) set \<Rightarrow> (heap\<times>stack) set \<Rightarrow>
      ( ('c::stack) \<longmapsto> ('d::stack)) \<Rightarrow> (heap\<times>stack) set \<Rightarrow> (heap\<times>stack) set \<Rightarrow> bool"
    ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)/ \<long_dobule_mapsto> _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)" [101,2,2,101,2,2] 100)
    where [\<nu>def]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> g \<blangle> U' \<longmapsto> V' \<brangle> \<longleftrightarrow>( \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> V' \<brangle> )"

lemma conversion: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f' \<blangle> U' \<longmapsto> V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U' \<longmapsto> V' \<brangle>"
  for f :: " ('a::stack) \<longmapsto> ('b::stack)" and f' :: " ('c::stack) \<longmapsto> ('d::stack)" unfolding Conversion_def by blast

lemma [\<nu>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n ?f \<blangle> ?U \<longmapsto> ?V \<brangle> \<long_dobule_mapsto> ?f'' \<blangle> ?U'' \<longmapsto> ?V'' \<brangle>\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U \<longmapsto> V \<brangle>" unfolding Conversion_def by blast


lemma [\<nu>reason on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n ?f \<blangle> ?U \<longmapsto> ?V \<brangle> \<long_dobule_mapsto> ?f'' \<blangle> ?U' \<longmapsto> ?V' \<brangle>\<close>]:
  assumes A: "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<medium_right_bracket>" 
  shows "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U' \<longmapsto> V' \<brangle>"
proof -
  from A[unfolded Cast_Target_def]
    have "\<forall>M. \<^bold>c\<^bold>a\<^bold>s\<^bold>t Heap' (M \<heavy_asterisk> U') \<longmapsto> Heap' (M \<heavy_asterisk> U) \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold>d\<^bold>u\<^bold>a\<^bold>l Heap' (M \<heavy_asterisk> V) \<longmapsto> Heap' (M \<heavy_asterisk> V') "
    unfolding Cast_def CastDual_def pair_forall by simp blast
  then show ?thesis
    unfolding cast_def \<nu>def by (simp add: nu_exps LooseStateTy_expn') meson
qed


definition IntroFrameVar :: "assn \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> bool" where
  "IntroFrameVar R S'' S' T'' T' \<longleftrightarrow> S'' = (R \<heavy_asterisk> S') \<and> T'' = (R \<heavy_asterisk> T') "

text \<open>Currently we do not allow \<^term>\<open>(\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n fff \<blangle> S' \<longmapsto> T' \<brangle> \<long_dobule_mapsto> ggg \<blangle> S \<longmapsto> T\<brangle>)\<close>\<close>

lemma apply_proc_conv:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
  \<Longrightarrow> IntroFrameVar R S'' S' T'' T'
  \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> S'' \<longmapsto> T'' \<brangle> \<long_dobule_mapsto> f \<blangle> S \<longmapsto> T\<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S' \<longmapsto> T' \<brangle>
  \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def Conversion_def IntroFrameVar_def
  by auto

lemma apply_cast_conv:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
  \<Longrightarrow> IntroFrameVar R S'' S' T'' T'
  \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S \<longmapsto> S'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold>d\<^bold>u\<^bold>a\<^bold>l T'' \<longmapsto> T \<medium_right_bracket>
  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t S' \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2
  \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding  CurrentConstruction_def PendingConstruction_def cast_def IntroFrameVar_def
  apply (cases blk)
  apply (auto simp add: nu_exps)
  by (smt (verit, del_insts) Separation_expn_R Shallowize'_expn)


lemma IntroFrameVar_No:
  "IntroFrameVar Void S' S' T' T' "
  unfolding IntroFrameVar_def by simp

lemma IntroFrameVar_Yes:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>c\<^bold>a\<^bold>s\<^bold>t] S'' : R \<heavy_asterisk> S' \<Longrightarrow>
   \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>c\<^bold>a\<^bold>s\<^bold>t] T'' : R \<heavy_asterisk> T' \<Longrightarrow>
   IntroFrameVar R S'' S' T'' T' "
  unfolding IntroFrameVar_def by blast


\<nu>reasoner IntroFrameVar 1000 ("IntroFrameVar R S'' S' T'' T'") = \<open>fn ctxt => fn sequent =>
  let open NuBasics
    val (Const (\<^const_name>\<open>IntroFrameVar\<close>, _) $ _ $ _ $ S' $ _ $ _) =
        major_prem_of sequent |> dest_Trueprop
    val tail = strip_separations S' |> last
  in
    if is_Var tail andalso fastype_of tail = @{typ assn}
    then Seq.single (@{thm IntroFrameVar_No} RS sequent)
    else Seq.single (@{thm IntroFrameVar_Yes} RS sequent)
  end\<close>


(* theorem apply_proc_conv_complex:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
  \<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>c\<^bold>a\<^bold>s\<^bold>t] S'' : Hr ^\<heavy_asterisk> S'
  \<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>c\<^bold>a\<^bold>s\<^bold>t] T'' : Hr ^\<heavy_asterisk> T'
  \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> S'' \<longmapsto> T'' \<brangle> \<long_dobule_mapsto> g \<blangle> S \<longmapsto> T\<brangle>)
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S' \<longmapsto> T' \<brangle>
  \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  using apply_proc_conv . *)


lemma conversion_trans: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n g \<blangle> Xg \<longmapsto> Yg \<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf \<brangle> \<long_dobule_mapsto> g \<blangle> Xg \<longmapsto> Yg \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf\<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>"
  unfolding Conversion_def by blast


subsection \<open>Auto construct & destruct\<close>

definition MakeTag ::" 'exp \<Rightarrow> 'x \<Rightarrow> 'x " ("(\<^bold>m\<^bold>a\<^bold>k\<^bold>e _/ \<^bold>b\<^bold>y _)" [40,10] 9) where [\<nu>def]:"MakeTag exp x = x"

lemma Make_by_proc:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
      \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e exp \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>
      \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  for exp :: "'exp"
  unfolding MakeTag_def using apply_proc .


subsection \<open>Index for Shallow Representation\<close>

text \<open>Indexes provide the function to access and map the addressed part in a nested structure (e.g. a nested pair @{term "(a,((b,c),d))"}.
  It is achieved by nested composition of address functions. For example "get_at (address_L (address_R address_here))"
  returns @{term b} for the pattern @{term "((a,b),c)"}, and "map_at (address_L (address_R address_here)) f"
  maps a @{term "((a,b),c)"} to @{term "((a, f b),c)"}\<close>

subsubsection \<open>Definitions\<close>

named_theorems \<nu>index_def

datatype ('a,'b,'x,'y) index = Index (get_idx: "'a \<Rightarrow> 'x") (map_idx: "('x \<Rightarrow> 'y) \<Rightarrow> 'a \<Rightarrow> 'b")
declare  index.split[split] Map'_def[\<nu>index_def]

definition index_here :: "('a,'b,'a,'b) index" where "index_here = Index id id"
definition index_left :: "('a,'b,'x,'y) index \<Rightarrow> ('a \<times> 'r, 'b \<times> 'r, 'x, 'y) index"
  where "index_left adr = (case adr of Index g m \<Rightarrow> Index (g \<circ> fst) (apfst o m))"
definition index_right :: "('a,'b,'x,'y) index \<Rightarrow> ('l \<times> 'a, 'l \<times> 'b, 'x, 'y) index"
  where "index_right adr = (case adr of Index g m \<Rightarrow> Index (g \<circ> snd) (apsnd o m))"


definition AdrGet :: " ('a,'b,'x,'y) index \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<blangle> _ \<^bold>@ _ \<brangle>)" [101,4,4] 100)
  where [\<nu>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<blangle> X \<^bold>@ A \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx adr \<blangle> A \<longmapsto> X \<brangle>"
definition AdrMap :: " ('a,'b,'x,'y) index \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> 'y set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<blangle> _ \<^bold>@ _ \<longmapsto> _ \<^bold>@ _ \<brangle>)" [101,4,4,4,4] 100)
  where [\<nu>index_def]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_idx idx \<blangle> A \<longmapsto> X \<brangle> \<and>
    (\<forall>f. (\<forall>a. a \<in> X \<longrightarrow> f a \<in> Y) \<longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> map_idx idx f  a \<in> B))"
declare Map_def[\<nu>index_def]

(*definition FieldIndex
    :: " ('a,'a,'ax,'ax) index \<Rightarrow> ('ax::lrep,'bx) \<nu> \<Rightarrow> ('a::lrep,'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'bx) \<Rightarrow> (('bx \<Rightarrow> 'bx) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>bool"
    ("(2\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x _/ \<blangle> _/ \<^bold>@ _ \<brangle>/ \<^bold>g\<^bold>e\<^bold>t _/ \<^bold>m\<^bold>a\<^bold>p _)" [101,4,4,30,30] 29)
  where [\<nu>index_def]: "FieldIndex idx X A gt mp
      \<longleftrightarrow> (\<forall>a f. \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> \<tort_lbrace>gt a \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> \<tort_lbrace>f (gt a) \<tycolon> X\<tort_rbrace> \<^bold>@ \<tort_lbrace>mp f a \<tycolon> A\<tort_rbrace> \<brangle>)"
*)

translations "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> x \<tycolon> X \<^bold>@ A \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>@ A \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ \<tort_lbrace> a \<tycolon> A\<tort_rbrace> \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ \<tort_lbrace> a \<tycolon> A\<tort_rbrace>  \<longmapsto> Y \<^bold>@ B \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> x \<tycolon> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>@ A  \<longmapsto> Y \<^bold>@ B \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> y \<tycolon> Y \<^bold>@ B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A  \<longmapsto> \<tort_lbrace>y \<tycolon> Y\<tort_rbrace> \<^bold>@ B \<brangle>"
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<brangle>" \<rightleftharpoons> "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A  \<longmapsto> Y \<^bold>@ \<tort_lbrace>b  \<tycolon> B\<tort_rbrace> \<brangle>"


subsubsection \<open>Abstraction theorems\<close>

lemma index_here_getter[\<nu>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>index_def  index_here_def by simp
lemma index_here_mapper[\<nu>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>index_def  index_here_def by simp
(*lemma index_here_func[\<nu>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t id \<^bold>m\<^bold>a\<^bold>p id"
  unfolding \<nu>index_def  index_here_def by simp
*)


lemma [\<nu>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<blangle> X \<^bold>@ (a,r) \<tycolon> (A \<cross_product> R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases idx) (simp add: nu_exps)
lemma [\<nu>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<blangle> X \<^bold>@ (a,r) \<tycolon> (A \<cross_product> R) \<longmapsto> Y \<^bold>@ (b,r) \<tycolon> (B \<cross_product> R) \<brangle>"
  unfolding \<nu>index_def index_left_def by (cases idx) (simp add: nu_exps)
(*lemma [\<nu>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<blangle> X \<^bold>@ A \<cross_product> R \<brangle> \<^bold>g\<^bold>e\<^bold>t g o fst \<^bold>m\<^bold>a\<^bold>p apfst o m"
  unfolding FieldIndex_def \<nu>index_def index_left_def by (cases idx) (simp add: nu_exps)
*)

lemma [\<nu>reason]:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x f \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right f \<blangle> X \<^bold>@ (l,a) \<tycolon> (L \<cross_product> A) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases f) (simp add: nu_exps)
lemma [\<nu>reason]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ (l,a) \<tycolon> (L \<cross_product> A) \<longmapsto> Y \<^bold>@ (l,b) \<tycolon> (L \<cross_product> B) \<brangle>"
  unfolding \<nu>index_def index_right_def by (cases idx) (simp add: nu_exps)
(*lemma [\<nu>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ R \<cross_product> A \<brangle> \<^bold>g\<^bold>e\<^bold>t g o snd \<^bold>m\<^bold>a\<^bold>p apsnd o m"
  unfolding FieldIndex_def \<nu>index_def index_right_def by (cases idx) (simp add: nu_exps)
*)
subsubsection \<open>Constructors\<close>

lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat) \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_here_def by simp
lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat) \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_here_def by simp

lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_here_def by simp
lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_here_def by simp

lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [(0::nat)] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_here_def by simp
lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e [(0::nat)] \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_here_def by simp

lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ (t, a) \<tycolon> (T \<cross_product> A) \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_right_def by (cases idx) (simp add: nu_exps)
lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ (t,a) \<tycolon> (T \<cross_product> A) \<longmapsto> Y \<^bold>@ (t,b) \<tycolon> (T \<cross_product> B) \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_right_def by (cases idx) (simp add: nu_exps)
(*lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ R \<cross_product> A \<brangle> \<^bold>g\<^bold>e\<^bold>t g o snd \<^bold>m\<^bold>a\<^bold>p apsnd o m"
  unfolding MakeTag_def FieldIndex_def \<nu>index_def index_right_def
  by (cases idx) (simp add: nu_exps)
*)
lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (Suc i)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ (t, a) \<tycolon> (T \<cross_product> A) \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_right_def by (cases idx) (simp add: nu_exps)
lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (Suc i)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ (t,a) \<tycolon> (T \<cross_product> A) \<longmapsto> Y \<^bold>@ (t,b) \<tycolon> (T \<cross_product> B) \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_right_def by (cases idx) (simp add: nu_exps)
(*lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e (Suc i)#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_right idx \<blangle> X \<^bold>@ R \<cross_product> A \<brangle> \<^bold>g\<^bold>e\<^bold>t g o snd \<^bold>m\<^bold>a\<^bold>p apsnd o m"
  unfolding MakeTag_def FieldIndex_def \<nu>index_def index_right_def
  by (cases idx) (simp add: nu_exps)
*)

lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<blangle> X \<^bold>@ (a,t) \<tycolon> (A \<cross_product> L) \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_left_def by (cases idx) (simp add: nu_exps)
lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat)#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<blangle> X \<^bold>@ (a,t) \<tycolon> (A \<cross_product> L) \<longmapsto> Y \<^bold>@ (b,t) \<tycolon> (B \<cross_product> L) \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_left_def by (cases idx) (simp add: nu_exps)
(*lemma [\<nu>reason]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e (0::nat)#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_left idx \<blangle> X \<^bold>@ A \<cross_product> R \<brangle> \<^bold>g\<^bold>e\<^bold>t g o fst \<^bold>m\<^bold>a\<^bold>p apfst o m"
  unfolding FieldIndex_def \<nu>index_def index_left_def MakeTag_def
  by (cases idx) (simp add: nu_exps)
*)


subsection \<open>Structural Pairs\<close>

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def .


subsection \<open>Convergence Reasoning\<close>

definition "Merge \<equiv> If"
definition "MergeNeg \<equiv> Not"


subsubsection \<open>Identity\<close>

lemma [\<nu>reason 3000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v If ?P ?A ?A'' = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P A A = A"
  unfolding Conv_def using if_cancel .

lemma [\<nu>reason 3000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?A ?A'' = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P A A = A"
  unfolding Conv_def Merge_def using if_cancel .

subsubsection \<open>Fallback\<close>

lemma [\<nu>reason 10 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v If ?P ?A ?B = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P A B = If P A B"
  unfolding Conv_def ..

text \<open>There is no fallback for \<^const>\<open>Merge\<close>. The Merge is not allowed to be fallback\<close>

subsubsection \<open>Ad-hoc rules\<close>

lemma [\<nu>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P \<tort_lbrace>?x \<tycolon> ?T1\<tort_rbrace> \<tort_lbrace>?y \<tycolon> ?T2\<tort_rbrace> = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P x y = z
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P \<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<tort_lbrace>y \<tycolon> T\<tort_rbrace> = \<tort_lbrace> z \<tycolon> T\<tort_rbrace>"
  unfolding Conv_def Merge_def by force

lemma [\<nu>reason on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v If ?P (?a \<R_arr_tail> ?x) (?b \<R_arr_tail> ?y) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P a b = aa
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v If P x y = z
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v If P (a \<R_arr_tail> x) (b \<R_arr_tail> y) = (aa \<R_arr_tail> z)"
  unfolding Conv_def Merge_def by force

lemma [\<nu>reason 3000]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P A B = X
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge (MergeNeg (MergeNeg P)) A B = X"
  unfolding MergeNeg_def by simp

lemma [\<nu>reason 2800]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P B A = X
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v If (MergeNeg P) A B = X"
  unfolding MergeNeg_def by force


subsubsection \<open>Subjection\<close>

lemma [\<nu>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QL) (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?QR) = ?X\<close>]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v If P QL QR = Q
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j QL) (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j QR) = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q)"
  unfolding Conv_def Merge_def by force

lemma [\<nu>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?L \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) ?R = ?X\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) R = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longrightarrow> Q)"
  unfolding Conv_def Merge_def by force

lemma [\<nu>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?L (?R \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?Q) = ?X\<close>]:
  \<comment> \<open>The fallback if the subjection condition only occurs at one side\<close>
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (R \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) = (X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not>P \<longrightarrow> Q)"
  unfolding Conv_def Merge_def by force

subsubsection \<open>Existential\<close>

lemma [\<nu>reason 2000 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (\<exists>* x. ?L x) (\<exists>* x. ?R x) = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L x) (R x) = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (\<exists>* x. L x) (\<exists>* x. R x) = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff nu_exps) force

lemma [\<nu>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?L (\<exists>* x. ?R x) = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (R x) = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P  L (\<exists>* x. R x) = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff nu_exps) force

lemma [\<nu>reason 1100 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (\<exists>* x. ?L x) ?R = ?X\<close>]:
  "(\<And>x. \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L x) R = X x)
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (\<exists>* x. L x) R = (\<exists>* x. X x)"
  unfolding Conv_def Merge_def by (simp add: set_eq_iff nu_exps) force

subsubsection \<open>Separations Initialization\<close>

lemma [\<nu>reason 1200]:
  "NEW_MUTEX G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 \<heavy_asterisk> L2) (Void \<heavy_asterisk> \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 \<heavy_asterisk> L2) R = X"
  unfolding Conv_def cast_def by force

subsubsection \<open>Value\<close>

lemma [\<nu>reason 1200 on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (VAL ?V1) (VAL ?V2) = ?X\<close>]: 
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P V1 V2 = V
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (VAL V1) (VAL V2) = (VAL V)"
  unfolding Conv_def cast_def Merge_def by force

lemma [\<nu>reason 1200 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?R1 \<heavy_asterisk> VAL ?V1) (?N \<heavy_asterisk> \<medium_left_bracket> ?R2 \<heavy_asterisk> VAL ?V2 \<medium_right_bracket>) = ?X \<medium_right_bracket>: ?G\<close> ]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P V1 V2 = V
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P R1 (Void \<heavy_asterisk> \<medium_left_bracket> N \<heavy_asterisk> R2 \<medium_right_bracket>) = R \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (R1 \<heavy_asterisk> VAL V1) (N \<heavy_asterisk> \<medium_left_bracket> R2 \<heavy_asterisk> VAL V2 \<medium_right_bracket>) = (R \<heavy_asterisk> VAL V) \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def by force

lemma [\<nu>reason 1200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (R1 \<heavy_asterisk> VAL V1) (N \<heavy_asterisk> OBJ H2 \<heavy_asterisk> \<medium_left_bracket> R2 \<medium_right_bracket>) = R \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (R1 \<heavy_asterisk> VAL V1) (N \<heavy_asterisk> \<medium_left_bracket> R2 \<heavy_asterisk> OBJ H2 \<medium_right_bracket>) = R \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def using Separation_comm(2) by force

subsubsection \<open>Object\<close>

definition EqualAddress :: " heap set \<Rightarrow> heap set \<Rightarrow> bool "
  where "EqualAddress _ _ = True"

lemma [\<nu>reason]:
  "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m a1 = a2
   \<Longrightarrow> EqualAddress \<tort_lbrace>a1 \<R_arr_tail> x1 \<tycolon> T1\<tort_rbrace> \<tort_lbrace>a2 \<R_arr_tail> x2 \<tycolon> T2\<tort_rbrace>"
  unfolding EqualAddress_def ..

lemma [\<nu>reason on \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (OBJ ?H1) (OBJ ?H2) = ?X\<close> ]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P H1 H2 = H
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (OBJ H1) (OBJ H2) = (OBJ H)"
  unfolding Conv_def Cast_Target_def Merge_def by force

lemma [\<nu>reason 1200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge (MergeNeg P) (N \<heavy_asterisk> R \<heavy_asterisk> VAL V2) (Void \<heavy_asterisk> \<medium_left_bracket> L \<heavy_asterisk> OBJ H1\<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<heavy_asterisk> OBJ H1) (N \<heavy_asterisk> \<medium_left_bracket> R \<heavy_asterisk> VAL V2 \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def MergeNeg_def by force

lemma [\<nu>reason 1200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (N \<heavy_asterisk> R) (Void \<heavy_asterisk> \<medium_left_bracket> L \<heavy_asterisk> OBJ H1\<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge (MergeNeg P) (L \<heavy_asterisk> OBJ H1) (N \<heavy_asterisk> \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def MergeNeg_def by force

lemma [\<nu>reason 100 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P (?L \<heavy_asterisk> OBJ ?H1) (?N \<heavy_asterisk> \<medium_left_bracket> ?R \<heavy_asterisk> OBJ ?H2 \<medium_right_bracket>) = ?X''' \<medium_right_bracket>: ?G\<close>]:
  \<comment> \<open>search the immediate element\<close>
  "MUTEX_ASSERT G
   \<Longrightarrow> EqualAddress H1 H2
   \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (OBJ H1) (OBJ H2) = H
   \<Longrightarrow> MUTEX_SET G \<comment> \<open>if success, trim all other branches on G\<close>
   \<Longrightarrow> NEW_MUTEX G2
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (Void \<heavy_asterisk> \<medium_left_bracket> N \<heavy_asterisk> R \<medium_right_bracket>) = X \<medium_right_bracket>: G2
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<heavy_asterisk> OBJ H1) (N \<heavy_asterisk> \<medium_left_bracket> R \<heavy_asterisk> OBJ H2 \<medium_right_bracket>) = (X \<heavy_asterisk> H) \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def by force

lemma [\<nu>reason 70 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P ?L (?N \<heavy_asterisk> \<medium_left_bracket> ?R \<heavy_asterisk> OBJ ?H2 \<medium_right_bracket>) = ?X''' \<medium_right_bracket>: ?G\<close>]:
  \<comment> \<open>search next\<close>
  "MUTEX_ASSERT G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> OBJ H2 \<heavy_asterisk> \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> R \<heavy_asterisk> OBJ H2 \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def using Separation_comm(2) by force

subsubsection \<open>Unfold\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> R \<heavy_asterisk> R1 \<heavy_asterisk> R2 \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> R \<heavy_asterisk> (R1 \<heavy_asterisk> R2) \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 \<heavy_asterisk> L2 \<heavy_asterisk> L3) R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L1 \<heavy_asterisk> (L2 \<heavy_asterisk> L3)) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma [\<nu>reason 2200]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> R1 \<heavy_asterisk> R2 \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> Void \<heavy_asterisk> (R1 \<heavy_asterisk> R2) \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force


subsubsection \<open>Padding Void\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (Void \<heavy_asterisk> OBJ L) R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (OBJ L) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (Void \<heavy_asterisk> VAL L) R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (VAL L) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> Void \<heavy_asterisk> VAL V \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> VAL V \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> Void \<heavy_asterisk> OBJ V \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> OBJ V \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

subsubsection \<open>Eliminate Void Hole\<close>

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> R \<medium_right_bracket>) = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L (N \<heavy_asterisk> \<medium_left_bracket> R \<heavy_asterisk> Void \<medium_right_bracket>) = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

lemma [\<nu>reason 2000]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P L R = X \<medium_right_bracket>: G
   \<Longrightarrow> \<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P (L \<heavy_asterisk> Void) R = X \<medium_right_bracket>: G"
  unfolding Conv_def cast_def by force

subsubsection \<open>Termination\<close>

lemma [\<nu>reason 2000 on \<open>\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge ?P Void (Void \<heavy_asterisk> \<medium_left_bracket> Void \<medium_right_bracket>) = ?X'' \<medium_right_bracket>: ?G\<close>]:
  "\<medium_left_bracket> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge P Void (Void \<heavy_asterisk> \<medium_left_bracket> Void \<medium_right_bracket>) = Void \<medium_right_bracket>: G"
  unfolding Conv_def cast_def Merge_def by force
  

subsection \<open>Convergence\<close>

definition SameNuTy :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " where "SameNuTy A B = True"
text \<open>Technical tag for reasoner converges \<nu>-types of two typings.\<close>

lemma [\<nu>reason 2000]: "SameNuTy \<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<tort_lbrace>x' \<tycolon> T\<tort_rbrace>"
  unfolding SameNuTy_def ..

lemma [\<nu>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy B B' \<Longrightarrow> SameNuTy (A \<heavy_asterisk> B) (A' \<heavy_asterisk> B')"
  unfolding SameNuTy_def ..

lemma [\<nu>reason 2000]: "(\<And>x. SameNuTy (A x) (A' x)) \<Longrightarrow> SameNuTy (ExSet A) (ExSet A')"
  unfolding SameNuTy_def ..

lemma [\<nu>reason 2000]: "SameNuTy A A' \<Longrightarrow> SameNuTy (A \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) (A' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)"
  unfolding SameNuTy_def ..

lemma [\<nu>reason 1000]: "SameNuTy A A" \<comment> \<open>The fallback\<close>
  unfolding SameNuTy_def ..


subsection \<open>Program Interface\<close> \<comment> \<open>Interfaces exported to target LLVM module\<close>

definition Prog_Interface :: " label \<Rightarrow> 'a itself \<Rightarrow> 'b itself \<Rightarrow> ('a::lrep  \<longmapsto> 'b::lrep) \<Rightarrow> bool"
  where "Prog_Interface _ args rets proc \<longleftrightarrow> True"

lemma Prog_Interface_proc: "TERM proc \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) proc" 
  unfolding Prog_Interface_def ..

lemma Prog_Interface_func:
  "TERM f \<Longrightarrow> Prog_Interface name TYPE('a::lrep) TYPE('b::lrep) f" 
  unfolding Prog_Interface_def ..

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
ML_file "./codegen/compilation.ML"
ML_file NuToplevel.ML

section \<open>Attributes and Commands\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<nu>instr"}, NuInstructions.list_definitions #> map snd))  \<close>

attribute_setup \<nu>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<nu>-system\<close>

attribute_setup \<nu>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (NuProcessor.get_attr ctx name) (ctx,toks))
  || Scan.lift NuProcessor.process_attr\<close>
  \<open>Evaluate the \<nu>-system process or the process of the given processor on the target theorem\<close>

(* TODO: fix this
method_setup \<nu>reason = \<open>let open Scan Parse in
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

val arg = Parse.term -- Scan.option ($$$ "::" |-- Parse.typ)
val proc_head = Parse_Spec.thm_name ":" --
        ((arg --| $$$ "\<longmapsto>" -- arg) || ($$$ "argument" |-- arg --| $$$ "return" -- arg))

in

(* val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>exty_simproc\<close> "setup the pecific simproc for \<^const>\<open>ExTy\<close>"
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
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>\<nu>cast\<close> "begin a procedure construction"
    ((proc_head -- option ($$$ "and" |-- Parse.term) -- nu_statements) >>
        (fn (((b,(arg,ret)),addtional_prop),((((fixes,includes),lets),defs),preconds)) =>
            (begin_cast_cmd b arg ret addtional_prop fixes includes lets defs preconds)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finish\<close> "Finish the procedure construction"
    (Scan.succeed (Toplevel.end_proof NuToplevel.finish_proc_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<bullet>\<close> "The \<nu>construction"
    (fn toks => (
      Toplevel.proof (Proof.map_context (Config.put Nu_Reasoner.auto_level 2) #>
          NuProcessor.powerful_process (toks @ [Token.eof])),
      if hd toks |> Token.is_eof then [Token.eof] else []))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>affirm\<close> "proof for premise"
    (Scan.succeed (Toplevel.proof' (snd oo NuToplevel.prove_prem)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor\<close> "define \<nu>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword || Parse.string)
          -- Parse.nat -- Parse.term -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
        >> NuProcessor.setup_cmd)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>interface\<close> "declare \<nu>interface"
      (Parse.binding --| $$$ "=" -- Parse.const -- option ($$$ ":" |-- Parse.typ --| $$$ "\<longmapsto>" -- Parse.typ)
        >> (Toplevel.theory o NuProcedure.add_interface_command))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>export_llvm\<close> "export LLVM target"
      (Scan.succeed (Toplevel.theory (NuToplevel.export_LLVM)))

end
\<close>

attribute_setup intro_forall = \<open>Scan.lift (Scan.repeat Args.var) >> (fn tms =>
  Thm.rule_attribute [] (fn ctx => fn th => 
    let open Thm
    val vs = add_vars th []
    val foralls = map (fn tm => case find_first (fn v => #1 (dest_Var (term_of v)) = tm) vs
                  of SOME y => y | _ => error (#1 tm ^ " is not a var ")) tms
    in Drule.forall_intr_list foralls th end)) \<close>

subsection \<open>Application method\<close>

attribute_setup \<nu>application_method = \<open>Scan.lift (Parse.int -- (Parse.int >> ~)) >> (fn (idx,cost) =>
  Thm.declaration_attribute (fn th => NuApply.update (cost,{thm=th, applicant_idx = idx})))\<close>

declare
  apply_proc[\<nu>application_method 1 100]
  apply_proc_conv[\<nu>application_method 3 -3000]
  "cast"[unfolded Cast_Target_def, \<nu>application_method 1 1100]
  apply_cast_conv[\<nu>application_method 3 1000]
thm apply_cast_conv[\<nu>application_method 3 1000]

thm
  "cast"[unfolded Cast_Target_def, OF _ cast_\<nu>app(1)[OF Argument_I], \<nu>application_method 1 1100]
  "cast"[unfolded Cast_Target_def, OF _ cast_\<nu>app(2)[OF Argument_I], \<nu>application_method 1 1100]
  "cast"[unfolded Cast_Target_def, OF _ cast_\<nu>app(3)[OF Argument_I], \<nu>application_method 1 1100]
  "cast"[unfolded Cast_Target_def, OF _ cast_\<nu>app(4)[OF Argument_I], \<nu>application_method 1 1100]
  "cast"[unfolded Cast_Target_def, OF _ cast_conversion[OF _ cast_\<nu>app(1)[OF Argument_I]],
      \<nu>application_method 2 1050]
  "cast"[unfolded Cast_Target_def, OF _ cast_conversion[OF _ cast_\<nu>app(2)[OF Argument_I]],
      \<nu>application_method 2 1050]
  "cast"[unfolded Cast_Target_def, OF _ cast_conversion[OF _ cast_\<nu>app(3)[OF Argument_I]],
      \<nu>application_method 2 1050]
  "cast"[unfolded Cast_Target_def, OF _ cast_conversion[OF _ cast_\<nu>app(4)[OF Argument_I]],
      \<nu>application_method 2 1050]

thm "cast"[unfolded Cast_Target_def, \<nu>application_method 1 1100]
thm "cast"[unfolded Cast_Target_def, OF _ cast_\<nu>app(1)[OF Argument_I], \<nu>application_method 1 1100]

thm "cast"[unfolded Cast_Target_def, OF _ cast_conversion[OF _ cast_\<nu>app(2)[OF Argument_I]],
      \<nu>application_method 2 1050]

(*  
  "cast"[OF _ cast_whole_heap_\<nu>app[OF Argument_I, OF cast_heap_conversion],
      \<nu>application_method 2 1020]*)

(* lemmas apply_func_conv[\<nu>application_method 6 -100]
  = apply_proc_conv_simple[OF _ _ _ _ op_call, rotated 3 1, rotated 1 3] *)

(* consts \<nu>Application_Rewrite :: bool
setup_\<nu>application_method \<open>\<nu>Application_Rewrite\<close> 1000 \<open>PROP P &&& A = B\<close> | \<open>PROP P &&& (A \<equiv> B)\<close> = \<open>
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

subsection \<open>Controls\<close>

\<nu>processor set_auto_level 10 \<open>PROP P\<close> \<open>(fn ctxt => fn sequent => NuParse.auto_level_force >>
  (fn auto_level' => fn _ => (sequent, Config.put Nu_Reasoner.auto_level auto_level' ctxt)))\<close>

\<nu>processor repeat 12 \<open>PROP P\<close> \<open>let
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

\<nu>processor accept_call 300 \<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta =>
  Scan.succeed (fn _ => NuSys.accept_proc meta ctx)\<close>

\<nu>processor "apply" 9000 \<open>P\<close> \<open> fn ctx => fn meta => NuApplicant.parser >> (fn binding => fn _ =>
  (NuSys.apply ctx (NuApplicant.applicant_thms ctx binding) meta, ctx))\<close>

\<nu>processor set_param 5000 \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Parse.term >> (fn term => fn _ =>
    (NuSys.set_param_cmd ctx term meta, ctx))\<close>

\<nu>processor set_label 5000 \<open>\<^bold>l\<^bold>a\<^bold>b\<^bold>e\<^bold>l P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn sequent => Parse.name >> (fn name => fn _ =>
    (NuSys.set_label name sequent, ctx))\<close>

\<nu>processor rule 7100 \<open>P \<Longrightarrow> PROP Q\<close>
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

\<nu>processor begin_sub_procedure 7000 \<open>PROP Q\<close> \<open>let open Parse Scan in fn ctx => fn meta =>
  $$$ "\<medium_left_bracket>" |-- optional ($$$ "premises" |-- and_list (binding -- opt_attribs)) [] >> (fn prems => fn () =>
  raise Process_State_Call' ((meta,ctx), NuToplevel.begin_block_cmd prems true)
) end\<close>

\<nu>processor end_sub_procedure 7000 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>let open Parse Scan in fn ctx => fn meta =>
  $$$ "\<medium_right_bracket>" >> (fn x => fn () =>
  raise Process_State_Call' ((meta,ctx), NuToplevel.end_block_cmd true)
) end\<close>

subsubsection \<open>Existential elimination\<close>

\<nu>processor existential_elimination 50 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ExSet T\<close>
  \<open>fn ctxt => fn sequent => Parse.$$$ "\<exists>" |-- Parse.list1 Parse.binding >> (fn insts => fn () =>
      raise Process_State_Call' ((sequent,ctxt), NuObtain.choose insts))\<close>

\<nu>processor auto_existential_elimination 50 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ExSet T\<close>
  \<open>fn ctx => fn meta => Scan.succeed (fn () =>
    raise Process_State_Call' ((meta,ctx), NuObtain.auto_choose))\<close>

subsection \<open>Simplifiers & Resonings\<close>

\<nu>processor \<nu>simplifier 40 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>NuProcessors.simplifier []\<close>
(* \<nu>processor \<nu>simplifier_final 9999 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close> *)

\<nu>processor move_fact 50 \<open>(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P\<close>
\<open>fn ctx => fn sequent => Scan.succeed (fn _ =>
  let
    val de_premise = perhaps (try (fn th => th RS @{thm Premise_E}))
    val facts = Proof_Context.get_thms ctx "\<nu>lemmata"
    val ctx = Proof_Context.put_thms true ("\<nu>lemmata",
        SOME (de_premise (sequent RS @{thm conjunct2}) :: facts) ) ctx
  in
    (sequent RS @{thm conjunct1}, ctx)
  end)\<close>

\<nu>processor set_\<nu>current 100 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
\<open>fn ctx => fn sequent => Scan.succeed (fn _ =>
  let
    val thm = sequent RS @{thm CurrentConstruction_D}
    val ctx = Proof_Context.put_thms true ("\<nu>current", SOME [thm]) ctx
  in
    raise Bypass (SOME(sequent, ctx))
  end)\<close>

\<nu>processor \<nu>reason 1000 \<open>PROP P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn sequent => Scan.succeed (fn _ =>
  let open NuBasics
    val sequent' = Nu_Reasoner.reason ctx sequent
  in case sequent' of SOME sequent' =>
      if Thm.prop_of sequent' = Thm.prop_of sequent
      then raise Bypass (SOME (sequent, ctx))
      else (sequent',ctx)
    | NONE => raise Bypass (SOME (sequent, ctx))
  end)\<close>

\<nu>processor fold 1300 \<open>PROP P\<close> \<open>
  fn ctxt => fn sequent => NuParse.$$$ "fold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (Local_Defs.fold ctxt (Attrib.eval_thms ctxt thms) sequent, ctxt)
)\<close>

\<nu>processor unfold 1300 \<open>PROP P\<close> \<open>
  fn ctxt => fn sequent => NuParse.$$$ "unfold" |-- Parse.list1 Parse.thm >> (fn thms => fn _ =>
    (Local_Defs.unfold ctxt (Attrib.eval_thms ctxt thms) sequent, ctxt)
)\<close>

\<nu>processor goal 1300 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>
  fn ctxt => fn sequent => Parse.$$$ "goal" >> (fn _ => fn _ =>
    let
      val goal = Proof_Context.get_thm ctxt "\<nu>thesis" |> Drule.dest_term
      val (_,_,desired_nu) = NuBasics.dest_procedure_c goal
      val ty = Thm.typ_of_cterm desired_nu
      val prot = Const (\<^const_name>\<open>Implicit_Protector\<close>, ty --> ty) |> Thm.cterm_of ctxt
      val ctxt = Config.put Nu_Reasoner.auto_level 1 ctxt
      val sequent = NuSys.cast ctxt (Thm.apply prot desired_nu) sequent
    in (sequent, ctxt) end
)\<close>


subsection \<open>Literal operations\<close>

\<nu>processor literal_constructor 9500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.cartouche >> (fn term => fn _ =>
  let val term = Syntax.read_term ctx term |> Thm.cterm_of ctx |> Simplifier.rewrite ctx |> Thm.rhs_of
  in (NuSys.auto_construct ctx term meta, ctx) end)\<close>

section \<open>Mechanism III - Additional Parts\<close>

subsection \<open>Variant Cast\<close>

definition Variant_Cast :: " 'vars \<Rightarrow> assn \<Rightarrow> ('vars \<Rightarrow> assn) \<Rightarrow> bool " ("\<^bold>v\<^bold>a\<^bold>r\<^bold>i\<^bold>a\<^bold>n\<^bold>t _ \<^bold>i\<^bold>n _/ \<longmapsto> _" )
  where "Variant_Cast insts X X' \<longleftrightarrow> X = X' insts"

lemma Variant_Cast_I: "X = X' vars \<Longrightarrow> Variant_Cast vars X X' "
  unfolding Variant_Cast_def by auto

lemma Variant_Cast_I_always:
  "X = X' vars \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e always vars \<Longrightarrow>
  Variant_Cast vars X (\<lambda>vars. X' vars \<^bold>s\<^bold>u\<^bold>b\<^bold>j always vars)"
  unfolding Variant_Cast_def Auto_def by (auto simp add: nu_exps)

lemma case_prod_expn_I: "A = B x y \<Longrightarrow> A = case_prod B (x,y)" by simp
lemma case_named_expn_I: "A = B x \<Longrightarrow> A = case_named B (tag x)" by simp

ML_file_debug \<open>library/variables_tag.ML\<close>

\<nu>processor vars_by_pattern 110 \<open>Variant_Cast vars X X' \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn meta => 
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

\<nu>reasoner Premise_Collect 10 (\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>c\<^bold>o\<^bold>l\<^bold>l\<^bold>e\<^bold>c\<^bold>t P\<close>) = \<open>Nu_Reasoners.premise_collect_tac\<close>
\<nu>reasoner Normal_Premise 10 (\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P\<close>) = \<open>Nu_Reasoners.premise_tac\<close>
\<nu>reasoner Simp_Premise 10 (\<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m P\<close>) = \<open>Nu_Reasoners.asm_simp_tac\<close>


end