theory Phi_Logic_Programming_Reasoner
  imports Main "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  keywords "no" "on" :: quasi_command
    and "\<phi>reasoner" "\<phi>reasoner_ML" :: thy_decl % "ML"
  abbrevs
      "<premise>" = "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e"
  and "<simprem>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m"
  and "<conv>" = "\<^bold>c\<^bold>o\<^bold>n\<^bold>v"
  and "<@GOAL>" = "\<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L"
  and "<action>" = "\<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>>"
begin

chapter \<open>\<phi> Logic Programming Reasoner\<close>

text \<open>This is a reasoner based on logic programming like Prolog.
  A reasoning state is represented as a Horn clause, like
\<^prop>\<open>(Premise1 \<Longrightarrow> Premise2 \<Longrightarrow> Antecedent1)
\<Longrightarrow> (Premise21 \<Longrightarrow> Premise22 \<Longrightarrow> Antecedent2)
\<Longrightarrow> Conclusion\<close>.
  The order of subgoals (like Antecedent1 and Antecedent2 above) is significant.
  A previous subgoal may instantiate schematic variables in later subgoals.
  Therefore, instead of subgoal which implies unorder,
    following logic terminology we call these subgoals \textit{antecedent}.
  The reasoner always processes antecedents in order.
  \<close>


section \<open>Preliminary Configure\<close>

named_theorems useful \<open>theorems that will be *used* in the automatic proving,
          which basically has the same effect as the using command.\<close>

attribute_setup rotated = \<open>Scan.lift (Scan.optional Parse.int 1 -- Scan.optional Parse.int 0) >>
  (fn (k,j) => Thm.rule_attribute [] (fn _ => Thm.permute_prems j k))\<close>
  \<open>Enhanced version of the Pure.rotated\<close>

attribute_setup TRY_THEN = \<open>(Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- Attrib.thm
      >> (fn (i, B) => Thm.rule_attribute [B] (fn _ => fn A => A RSN (i, B) handle THM _ => A)))
    \<close> "resolution with rule, and do nothing if fail"

ML_file \<open>library/cost_net.ML\<close>


section \<open>The Reasoner\<close>


definition "\<phi>Intro_Rule x = x"
definition "\<phi>Elim_Rule x = x"
definition \<r>Feasible :: \<open>bool\<close> where \<open>\<r>Feasible = True\<close>

text \<open>If any deterministic rule (whose priority is greater or equal to 1000),
  has a \<^prop>\<open>\<r>Feasible\<close> antecedent, this rule is conditioned in the case where
  all the previous antecedents are successfully solved.
  It can only be applied if all the antecedents before the \<^prop>\<open>\<r>Feasible\<close>
  are solved successfully.\<close>

ML_file_debug \<open>library/reasoner.ML\<close>

attribute_setup \<phi>reason =
\<open>let open Args Scan Parse 
  fun read_prop_mode mode ctxt = Syntax.read_prop (Proof_Context.set_mode mode ctxt)
  val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
  val prop_pattern = Scan.repeat (Scan.peek (named_term o read_prop_pattern o Context.proof_of))
in
  (lift (option add |-- ((\<^keyword>\<open>!\<close> >> K ~2000000) || optional (Parse.int >> ~) ~100))
      -- (optional (lift ($$$ "on") |-- prop_pattern) []
       -- optional (lift ($$$ "if" |-- $$$ "no") |-- prop_pattern) [])
        >> Nu_Reasoner.attr_add_intro)
  || (lift del >> K Nu_Reasoner.attr_del_intro)
end\<close>
  \<open>Set introduction rules in \<phi> reasonser.
   Syntax: \<phi>intro [add] <priority-of-the-rule> || \<phi>intro del\<close>

attribute_setup \<phi>reason_elim =
\<open>let open Args Scan Parse
  fun read_prop_mode mode ctxt = Syntax.read_prop (Proof_Context.set_mode mode ctxt)
  val read_prop_pattern = read_prop_mode Proof_Context.mode_pattern
  val prop_pattern = Scan.repeat (Scan.peek (named_term o read_prop_pattern o Context.proof_of))
in
  (lift (option add |-- ((\<^keyword>\<open>!\<close> >> K ~2000000) || optional (Parse.int >> ~) ~100))
      -- (optional (lift ($$$ "on") |-- prop_pattern) []
       -- optional (lift ($$$ "no") |-- prop_pattern) [])
        >> Nu_Reasoner.attr_add_elim)
  || (lift del >> K Nu_Reasoner.attr_del_elim)
end\<close>
  \<open>Set elimduction rules in \<phi> reasonser.
  Syntax: \<phi>reasoner_elim [add] <spur-of-the-rule> || \<phi>reasoner_elim del\<close>

method_setup \<phi>reason = \<open>let open Scan Parse in
  Method.sections [
    Args.add >> K (Method.modifier (Nu_Reasoner.attr_add_intro (~100,([],[]))) \<^here>),
    Args.del >> K (Method.modifier  Nu_Reasoner.attr_del_intro \<^here>)
] >> (fn irules => fn ctxt => fn ths => Nu_Reasoner.reason_tac ctxt)
end\<close>

declare conjI[\<phi>reason] TrueI[\<phi>reason]


section \<open>Facilities & Tools\<close>

subsection \<open>General Structures\<close>

subsubsection \<open>Action\<close>

typedecl 'cat action

definition Action_Tag :: \<open>prop \<Rightarrow> 'cat action \<Rightarrow> prop\<close> ("_  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> _" [2,1000] 2)
  where \<open>Action_Tag P A \<equiv> P\<close>

text \<open>\<^prop>\<open>P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> A\<close> is a general way to annotate the rule \<^prop>\<open>P\<close> intends for
  specific usage or purpose of \<^term>\<open>A\<close>.

  The type variable \<^typ>\<open>'cat\<close> in \<^typ>\<open>'cat action\<close> enables to classify actions by classes.
  Then an operation can be designed for any generic action \<^term>\<open>act :: 'ty action\<close> whose
  type \<^typ>\<open>'ty\<close> belongs to certain class.\<close>

lemma Action_Tag_I:
  \<open>P \<Longrightarrow> P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> A\<close>
  unfolding Action_Tag_def .

lemma Conv_Action_Tag_I:
  \<open>X = X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> A\<close>
  unfolding Action_Tag_def ..

subsubsection \<open>Mode\<close>

text \<open>Modes are annotations of the automation. They are typically used specifically to determine
  the modes of the automation method to be applied. For example, see the Premise tag.\<close>

type_synonym mode = \<open>unit action\<close>

consts default :: mode
consts MODE_SIMP :: mode \<comment> \<open>relating to simplifier or simplification\<close>
consts MODE_COLLECT :: mode \<comment> \<open>relating to collection\<close>

subsubsection \<open>Focus\<close>

text \<open>A general technical tag used in the reasoning, usually represents the reasoning
  currently focuses on certain part, certain target.\<close>

definition FOCUS_TAG :: " 'a \<Rightarrow> 'a "  ("\<blangle> _ \<brangle>") where [iff]: "\<blangle> x \<brangle> = x"


subsection \<open>Proof Obligation\<close>

definition Premise :: "mode \<Rightarrow> bool \<Rightarrow> bool" where "Premise _ x = x"

abbreviation Normal_Premise ("\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e _" [27] 26) where "Normal_Premise \<equiv> Premise default"
abbreviation Simp_Premise ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m _" [27] 26) where "Simp_Premise \<equiv> Premise MODE_SIMP"
abbreviation Proof_Obligation ("\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n _" [27] 26) where "Proof_Obligation \<equiv> Premise MODE_COLLECT"

text \<open>
  The tag represents an ordinary proof obligation other than the internal-system terms
    that have a specific meaning and purpose and can be inferred automatically.
  Thus, the tag simply triggers a general prover to attempt to solve it automatically.

  There are multiple strategies to handle them, depending on the difficulty of the problem
    and more specifically the solving time that the situation can afford.

  The \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P\<close> denotes the \<^prop>\<open>P\<close> should be solved by full power, without counting
    the potential very long time of waiting. In the situation, user usually can interrupt
    the computation.

  The \<^term>\<open>\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m P\<close> suits for time-sensible situation because the reasoner only uses
    light-weight strategies to attack the goal, like `clarsimp'. Many reasoning rules use
    this strategy because the time-consuming computation is not affordable during the automatic process.

  The \<^term>\<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n P\<close> is interesting. Once it is presented in a Horn clause, proofs of
    any \<^term>\<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P'\<close> before this tag are delayed until the proof of this tag.
  In fact, proof obligations (\<^prop>\<open>P'\<close>) are moved into \<^term>\<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n P\<close> to be \<^term>\<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n P \<and> P'\<close>
    by using conjuncture.
  This strategy is useful when \<^prop>\<open>P'\<close> has undetermined schematic variables while those
    variables can be determined by later automatic reasoning (by the reasoning of later subgoals in
    the Horn clause but early than the \<^term>\<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n P\<close> tag).

  When the automatic solving consumes a lot of time, users can set the auto level down to
    semi-auto (level 1) to suppress the automatic behavior and solve it manually. (TODO: by which command?)
\<close>

lemma Premise_I[intro!]: "P \<Longrightarrow> Premise mode P" unfolding Premise_def by simp
lemma Premise_D: "Premise mode P \<Longrightarrow> P" unfolding Premise_def by simp
lemma Premise_E[elim!]: "Premise mode P \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> C" unfolding Premise_def by simp

lemma Premise_Irew: "(P \<Longrightarrow> C) \<equiv> Trueprop (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<longrightarrow> C)" unfolding Premise_def atomize_imp .

lemma Premise_True[\<phi>reason 5000]: "Premise mode True" unfolding Premise_def ..
lemma [\<phi>reason 5000]:
  "Premise mode P
  \<Longrightarrow> Premise mode (Premise any_mode P)"
  unfolding Premise_def .


paragraph \<open>Internal Lemmas\<close>

lemma contract_premise_true:
  "(True \<Longrightarrow> Premise mode B) \<equiv> Trueprop (Premise mode B) "
  by simp

lemma contract_premise_imp:
  "(A \<Longrightarrow> Premise mode B) \<equiv> Trueprop (Premise mode (A \<longrightarrow> B)) "
  unfolding Premise_def atomize_imp .

lemma contract_premise_all:
  "(\<And>x. Premise mode (P x)) \<equiv> Trueprop ( Premise mode (\<forall>x. P x)) "
  unfolding Premise_def atomize_all .

lemma Premise_refl[\<phi>reason 2000 on \<open>Premise ?mode (?x = ?x)\<close>
                                   \<open>Premise ?mode (?x = ?var_x)\<close>]:
  "Premise mode (x = x)"
  unfolding Premise_def ..

ML_file \<open>library/PLPR_Syntax.ML\<close>

subsection \<open>Cut\<close>

text \<open>There are three kinds of cuts.
  \<^item> Local Cut : If the priority of a rule is greater (or equal) than 1000, this rule
      is a local cut in the sense the reasoning will not branch but only apply this rule instead
      (apply the rule with maximum priority if there are multiple rules are local cut).
  \<^item> Global Cut : If the priority is greater (or equal) than 1000_000, this rule is
      a global cut that no backtrack will be applied before this.
      It implies some achievement has been reached.
      Thus the reasoner returns the latest global cut point when not all antecedents are solved.
  \<^item> Ultimate Cut i.e. \<r>Success : It represents an ultimate success has been reached in the reasoning,
      so the reasoner terminates and returns the Horn clause triggering \<r>Success.\<close>


definition \<r>Cut :: bool where \<open>\<r>Cut = True\<close>

text \<open>It triggers a (global) reasoning cut.\<close>

lemma [iff, \<phi>reason 1000000]: \<open>\<r>Cut\<close> unfolding \<r>Cut_def ..




definition \<r>Success :: bool where \<open>\<r>Success = True\<close>

lemma \<r>Success_I[iff]: \<open>\<r>Success\<close> unfolding \<r>Success_def ..

text \<open>Terminates the reasoning successfully and immediately\<close>

\<phi>reasoner_ML \<r>Success 10000 (conclusion \<open>\<r>Success\<close>) = \<open>fn (ctxt,sequent) =>
  raise Nu_Reasoner.Success (ctxt, @{thm \<r>Success_I} RS sequent)\<close>





lemma \<r>Feasible_I[iff]: \<open>\<r>Feasible\<close> unfolding \<r>Feasible_def ..

\<phi>reasoner_ML \<r>Feasible 10000 (conclusion \<open>\<r>Feasible\<close>) = \<open>fn (ctxt,sequent) =>
  raise Nu_Reasoner.Success (ctxt, @{thm \<r>Feasible_I} RS sequent)\<close>


subsection \<open>Conversion\<close>

definition Conv :: "'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v _ = _" [51,51] 50)
  where "Conv origin obj \<longleftrightarrow> obj = origin"

text \<open>\<^prop>\<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v A = B \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> Act\<close> indicates the reasoner should convert \<^term>\<open>A\<close> into some \<^term>\<open>B\<close>.
  Specific rules should be configured to reason those goals.\<close>

lemma Conv_cong[cong]:
  \<open>A \<equiv> A' \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v A = B \<equiv> \<^bold>c\<^bold>o\<^bold>n\<^bold>v A' = B\<close>
  by simp

lemma Conv_I: \<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v A = A\<close> unfolding Conv_def ..


subsubsection \<open>Matches\<close>

definition Matches :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where \<open>Matches _ _ = True\<close>

text \<open>In the reasoning, a subgoal \<^prop>\<open>Matches pattern term\<close> is solved iff \<^term>\<open>pattern\<close>
  matches \<^term>\<open>term\<close>. This subgoal is useful to restrict a rule to match certain pattern to be applied.\<close>

lemma Matches_I: \<open>Matches pattern term\<close> unfolding Matches_def ..

\<phi>reasoner_ML Matches 2000 (conclusion \<open>Matches ?pattern ?term\<close>) =
  \<open>fn (ctxt, sequent) =>
    let
      val (\<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Matches\<close>,_) $ pattern $ term))
            = Thm.major_prem_of sequent
    in
      if Pattern.matches (Proof_Context.theory_of ctxt) (pattern, term)
      then Seq.single (ctxt, @{thm Matches_I} RS sequent)
      else Seq.empty
    end\<close>



subsection \<open>Not Match\<close>

lemma NO_MATCH_I: "NO_MATCH A B" unfolding NO_MATCH_def ..

\<phi>reasoner_ML NO_MATCH 0 (conclusion "NO_MATCH ?A ?B") = \<open>
  fn (ctxt,th) =>
  case try Thm.major_prem_of th
    of SOME (\<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>NO_MATCH\<close>, _) $ a $ b)) =>
        if Pattern.matches (Proof_Context.theory_of ctxt) (a,b)
        then Seq.empty
        else Seq.single (ctxt, @{thm NO_MATCH_I} RS th)
     | _ => Seq.empty
\<close>



subsubsection \<open>Subgoal\<close>

typedef "subgoal" = "UNIV :: nat set" ..

consts TOP_GOAL :: "subgoal"
consts NO_GOAL :: "subgoal"

definition SUBGOAL :: "subgoal \<Rightarrow> subgoal \<Rightarrow> bool" where "SUBGOAL ROOT NEW_GOAL = True"
definition CHK_SUBGOAL :: "subgoal \<Rightarrow> bool" \<comment> \<open>Check whether the goal is solved\<close>
  where "CHK_SUBGOAL X = True"
definition SOLVE_SUBGOAL :: "subgoal \<Rightarrow> bool" where "SOLVE_SUBGOAL X = True"

text \<open>The three tags provides a hierarchical subgoal environment.
  \<^prop>\<open>SUBGOAL ROOT NEW_GOAL\<close> creates a new unique subgoal \<^term>\<open>NEW_GOAL\<close> under \<^term>\<open>ROOT\<close>.
    \<^term>\<open>NEW_GOAL\<close> should be a schematic variable to be instantiated by the reasoner.
  \<^prop>\<open>SOLVE_SUBGOAL GOAL\<close> marks the GOAL and all its subgoals solved.
  \<^prop>\<open>CHK_SUBGOAL GOAL\<close> checks whether the GOAL is marked solved. If it is,
    this proposition is rejected to be solved by the reasoner, causing any search path
    assuming this proposition terminates. Therefore, no additional searches
    assuming this proposition will continue once the subgoal is solved.

  Once \<^term>\<open>GOAL\<close> is marked solved. Later \<^prop>\<open>SOLVE_SUBGOAL GOAL\<close> only succeeds on the
    search path which marks this goal. Any branch irrelevant with the point of
    the marking cannot mark the \<^term>\<open>GOAL\<close> again, and \<^prop>\<open>SOLVE_SUBGOAL GOAL\<close>
    fails for them, causing those branches terminate.

  The \<^term>\<open>TOP_GOAL\<close> can never be solved.\<close>

lemma SUBGOAL_I[iff]: "SUBGOAL ROOT NEWGOAL" unfolding SUBGOAL_def ..
lemma CHK_SUBGOAL_I[iff]: "CHK_SUBGOAL X" unfolding CHK_SUBGOAL_def ..
lemma SOLVE_SUBGOAL_I[iff]: "SOLVE_SUBGOAL X" unfolding SOLVE_SUBGOAL_def ..

ML_file \<open>library/Subgoal_Env.ML\<close>

\<phi>reasoner_ML SUBGOAL 2000 (conclusion \<open>SUBGOAL ?ROOT ?NEWGOAL\<close>) = \<open>Subgoal_Env.subgoal\<close>
\<phi>reasoner_ML CHK_SUBGOAL 2000 (conclusion \<open>CHK_SUBGOAL ?GOAL\<close>) = \<open>Subgoal_Env.chk_subgoal\<close>
\<phi>reasoner_ML SOLVE_SUBGOAL 9900 (conclusion \<open>SOLVE_SUBGOAL ?GOAL\<close>) = \<open>Subgoal_Env.solve_subgoal\<close>

lemma [\<phi>reason 3000]: \<open>CHK_SUBGOAL   NO_GOAL\<close> using CHK_SUBGOAL_I   .
lemma [\<phi>reason 9999]: \<open>SOLVE_SUBGOAL NO_GOAL\<close> using SOLVE_SUBGOAL_I .


definition GOAL_CTXT :: "prop \<Rightarrow> subgoal \<Rightarrow> prop"  ("_  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L _" [2,1000] 2)
  where [iff]: "GOAL_CTXT x _ \<equiv> x"



subsection \<open>Simplification & Rewrite\<close>

definition Simplify :: " mode \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[_] _ : _" [10,1000,10] 9)
  where "Simplify setting result origin \<longleftrightarrow> result = origin"

lemma [cong]: "A = A' \<Longrightarrow> Simplify s x A = Simplify s x A' "
  unfolding Simplify_def by simp

lemma Simplify_I[intro!]: "Simplify s A A" unfolding Simplify_def ..
lemma Simplify_E[elim!]: "Simplify s A B \<Longrightarrow> (A = B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Simplify_def by blast


subsubsection \<open>Default Simplifier\<close>

abbreviation Default_Simplify :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y _ : _" [1000,10] 9)
  where "Default_Simplify \<equiv> Simplify default"

\<phi>reasoner Default_Simplify 1000 (conclusion \<open>Default_Simplify ?x ?y\<close>)
  = (simp?, rule Simplify_I)
  
(* \<open>fn ctx =>
  HEADGOAL (asm_simp_tac ctx) THEN
  HEADGOAL (resolve0_tac @{thms Simplify_I})
\<close> *)

subsection \<open>Branch\<close>

definition Branch :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close> (infixr "|||" 3)
  where \<open>Branch A B \<equiv> (\<And>C::prop. (PROP A \<Longrightarrow> PROP C) \<Longrightarrow> (PROP B \<Longrightarrow> PROP C) \<Longrightarrow> PROP C)\<close>

consts BRANCH :: \<open>subgoal \<Rightarrow> subgoal\<close>

text \<open>It triggers divergence in searching, with short-cut.
    Guaranteed by subgoal context, it tries every antecedents from left to right until
      the first success of solving an antecedent, and none of remains are attempted.\<close>

lemma Branch_imp:
  \<open> (PROP A ||| PROP B \<Longrightarrow> PROP C)
 \<equiv> ((PROP A \<Longrightarrow> PROP C) &&& (PROP B \<Longrightarrow> PROP C))\<close>
  unfolding Branch_def proof
  assume X: \<open>(\<And>C. (PROP A \<Longrightarrow> PROP C) \<Longrightarrow> (PROP B \<Longrightarrow> PROP C) \<Longrightarrow> PROP C) \<Longrightarrow> PROP C\<close>
  show \<open>(PROP A \<Longrightarrow> PROP C) &&& (PROP B \<Longrightarrow> PROP C) \<close> proof -
    assume A: \<open>PROP A\<close>
    show \<open>PROP C\<close> proof (rule X)
      fix C :: "prop"
      assume \<open>PROP A \<Longrightarrow> PROP C\<close>
      from this[OF A] show \<open>PROP C\<close> .
    qed
  next assume B: \<open>PROP B\<close>
    show \<open>PROP C\<close> proof (rule X)
      fix C :: "prop"
      assume \<open>PROP B \<Longrightarrow> PROP C\<close>
      from this[OF B] show \<open>PROP C\<close> .
    qed
  qed
next
  assume X: \<open>(PROP A \<Longrightarrow> PROP C) &&& (PROP B \<Longrightarrow> PROP C)\<close>
    and  Y: \<open>\<And>C. (PROP A \<Longrightarrow> PROP C) \<Longrightarrow> (PROP B \<Longrightarrow> PROP C) \<Longrightarrow> PROP C\<close>
  show \<open>PROP C\<close> proof (rule Y)
    assume \<open>PROP A\<close>
    from X[THEN conjunctionD1, OF this] show \<open>PROP C\<close> .
  next
    assume \<open>PROP B\<close>
    from X[THEN conjunctionD2, OF this] show \<open>PROP C\<close> .
  qed
qed

lemma [\<phi>reason 1000]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> PROP A ||| PROP B \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH G)
\<Longrightarrow> PROP A ||| PROP B\<close>
  unfolding GOAL_CTXT_def .

lemma [\<phi>reason on \<open>PROP ?A \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH ?G)\<close> if no \<open>PROP ?X ||| PROP ?Y \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH ?G)\<close>]:
  \<open> PROP A
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP A \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH G)\<close>
  unfolding GOAL_CTXT_def .

lemma [\<phi>reason]:
  \<open> PROP A \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH G)
\<Longrightarrow> PROP A ||| PROP B  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH G)\<close>
  unfolding GOAL_CTXT_def Branch_def
proof -
  assume A: \<open>PROP A\<close>
  show \<open>(\<And>C. (PROP A \<Longrightarrow> PROP C) \<Longrightarrow> (PROP B \<Longrightarrow> PROP C) \<Longrightarrow> PROP C)\<close> proof -
    fix C :: "prop"
    assume A': \<open>PROP A \<Longrightarrow> PROP C\<close>
    show \<open>PROP C\<close> using A'[OF A] .
  qed
qed

lemma [\<phi>reason 10]:
  \<open> PROP B \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH G)
\<Longrightarrow> PROP A ||| PROP B  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L (BRANCH G)\<close>
  unfolding GOAL_CTXT_def Branch_def
proof -
  assume B: \<open>PROP B\<close>
  show \<open>(\<And>C. (PROP A \<Longrightarrow> PROP C) \<Longrightarrow> (PROP B \<Longrightarrow> PROP C) \<Longrightarrow> PROP C)\<close> proof -
    fix C :: "prop"
    assume B': \<open>PROP B \<Longrightarrow> PROP C\<close>
    show \<open>PROP C\<close> using B'[OF B] .
  qed
qed


subsection \<open>Obtain\<close> \<comment> \<open>A restricted version of generalized elimination for existential only\<close>
  \<comment> \<open>Maybe Useless, considering to discard!\<close>

definition Obtain :: \<open>'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where \<open>Obtain x P \<longleftrightarrow> P x\<close>
definition \<open>DO_OBTAIN \<equiv> Trueprop True\<close>

lemma DO_OBTAIN_I: \<open>PROP DO_OBTAIN\<close> unfolding DO_OBTAIN_def ..
lemma Obtain_Framework:
  \<open>PROP Sequent \<Longrightarrow> PROP GE \<Longrightarrow> PROP DO_OBTAIN \<Longrightarrow> PROP Sequent &&& PROP GE\<close>
  using conjunctionI .

lemma Obtain_I:
  \<open>P x \<Longrightarrow> Obtain x P\<close>
  unfolding Obtain_def .

\<phi>reasoner_ML Obtain 1200 (conclusion \<open>Obtain ?x ?P\<close>) = \<open>
fn (ctxt, sequent) =>
  let
    val obtain_goal = Thm.major_prem_of sequent
    fun obtain_goal_vars L (Const (\<^const_name>\<open>Obtain\<close>, _) $ V $ P) = obtain_goal_vars (V::L) P
      | obtain_goal_vars L (\<^const>\<open>Trueprop\<close> $ P) = obtain_goal_vars L P
      | obtain_goal_vars L (Abs (_,_,P)) = obtain_goal_vars L P
      | obtain_goal_vars L _ = L
    fun to_ex_goal (Const (\<^const_name>\<open>Obtain\<close>, Type ("fun", [_, ty])) $ _ $ P)
          = Const (\<^const_name>\<open>Ex\<close>, ty) $ to_ex_goal P
      | to_ex_goal (\<^const>\<open>Trueprop\<close> $ P) = \<^const>\<open>Trueprop\<close> $ to_ex_goal P
      | to_ex_goal (Abs (N,Ty,P)) = Abs (N,Ty, to_ex_goal P)
      | to_ex_goal P = P
    val goal = Thm.trivial (Thm.cterm_of ctxt (to_ex_goal obtain_goal))
    val L = obtain_goal_vars [] obtain_goal
   in
    if forall is_Var L
    then Seq.single (ctxt, goal RS (sequent COMP @{thm Obtain_Framework}))
    else error("asdwh78")
  end
\<close>

\<phi>reasoner_ML DO_OBTAIN 1200 (conclusion \<open>PROP DO_OBTAIN\<close>) = \<open>
fn (ctxt, sequent') => Seq.make (fn _ =>
  let
    val sequent'' = @{thm DO_OBTAIN_I} RS sequent'
    val (sequent, GE') = Conjunction.elim sequent''
    val obtain_goal = Thm.major_prem_of sequent
    fun obtain_goal_vars L (Const (\<^const_name>\<open>Obtain\<close>, _) $ V $ P) = obtain_goal_vars (V::L) P
      | obtain_goal_vars L (\<^const>\<open>Trueprop\<close> $ P) = obtain_goal_vars L P
      | obtain_goal_vars L (Abs (_,_,P)) = obtain_goal_vars L P
      | obtain_goal_vars L _ = L
    fun get_goal (Const (\<^const_name>\<open>Obtain\<close>, _) $ _ $ P) = get_goal P
      | get_goal (Abs (_,_,P)) = get_goal P
      | get_goal (\<^const>\<open>Trueprop\<close> $ P) = get_goal P
      | get_goal P = P
    val L = obtain_goal_vars [] obtain_goal
    val N = length L
    val GE = Tactical.REPEAT_DETERM_N N
                (Thm.biresolution NONE false [(true, @{thm exE})] 1) GE' |> Seq.hd
    val (var_names, ctxt') = Proof_Context.add_fixes
          (map (fn tm => (Binding.name (Term.term_name tm), SOME (fastype_of tm), NoSyn)) L) ctxt
    val vars = map Free (var_names ~~ map Term.fastype_of L)
    val vars_c = map (Thm.cterm_of ctxt') vars
    val assm =
        Term.subst_bounds (vars, get_goal obtain_goal)
          |> Thm.cterm_of ctxt'
    fun export_assm thm = thm
          |> Thm.implies_intr assm
          |> Drule.forall_intr_list vars_c
          |> (fn th => th COMP GE)
    val ([assm_thm], ctxt'') = Assumption.add_assms (fn _ => fn _ => (export_assm, I)) [assm] ctxt'
    val sequent1 = Tactical.REPEAT_DETERM_N N
            (Thm.biresolution NONE false [(true, @{thm Obtain_I})] 1) sequent |> Seq.hd
   in SOME ((ctxt'', assm_thm RS sequent1), Seq.empty)
  end
)\<close>



(* subsection \<open>Generalized Elimination\<close>

definition "\<phi>Generalized_Elimination x = x"

definition \<open>DO_GENERALIZED_ELIMINATION \<equiv> Trueprop True\<close>

lemma DO_GENERALIZED_ELIMINATION_I:
  \<open>PROP DO_GENERALIZED_ELIMINATION\<close>
  unfolding DO_GENERALIZED_ELIMINATION_def ..

lemma Generalized_Elimination_Framework:
  \<open> TERM P
\<Longrightarrow> TERM P \<comment> \<open>Unifies prop in Sequent and that in GE here\<close>
\<Longrightarrow> PROP Sequent
\<Longrightarrow> PROP GE
\<Longrightarrow> PROP DO_GENERALIZED_ELIMINATION
\<Longrightarrow> PROP GE &&& PROP Sequent\<close>
  using Pure.conjunctionI .

ML_file \<open>library/elimination.ML\<close>

*)
subsection \<open>Misc\<close>

subsubsection \<open>Useless Tag\<close>

text \<open>Sometimes, like in a simplification where information are always transformed equally
  (no information loses), some useless information is generated during some procedure.
  These information are necessary technically like for an equality in a simplification rule,
    but are useless for the verification.
  These information can be wrapped by a Useless tag to annotate this.
  In \<phi>-Programming, any extracted lemmas wrapped by this tag will not be added into
    proof environment and dropped simply.\<close>

definition USELESS :: \<open>bool \<Rightarrow> bool\<close> where \<open>USELESS x = x\<close>

lemma [simp]: \<open>USELESS True\<close> unfolding USELESS_def ..


subsubsection \<open>Collect Schematic & Free & other terms\<close> \<comment> \<open>Not Stable!\<close>

paragraph \<open>Schematic\<close>

definition \<open>Collect_Schematic (typ::'a itself) sch Term \<equiv> Trueprop True\<close>

text \<open>It collects all schematic variables matching type \<^typ>\<open>'a\<close> in \<^term>\<open>Term\<close>.
  The return is in form \<^term>\<open>Collect_Schematic TYPE('a) (v1, v2, v3) Term\<close>.
  The matching of \<^typ>\<open>'a\<close> is in the usual way, where only schematic variables but no free variables
    are considered as variables that can match something.\<close>

lemma Collect_Schematic_I: \<open>PROP Collect_Schematic TY sch Term\<close>
  unfolding Collect_Schematic_def ..

\<phi>reasoner_ML Collect_Schematic 1200 (conclusion \<open>PROP Collect_Schematic TYPE(?'a) ?sch ?Term\<close>) = \<open>
  fn (ctxt, sequent) =>
    let
      val (Const (\<^const_name>\<open>Collect_Schematic\<close>, _)
            $ Const (\<^const_name>\<open>Pure.type\<close>, Type(\<^type_name>\<open>itself\<close>, [T])))
            $ _
            $ Term
        = Thm.major_prem_of sequent
      val vs = fold_aterms (fn (v as Var (_, T')) => (fn L =>
                                  if Type.could_match (T,T') then insert (op =) v L else L)
                             | _ => I) Term []
      val vs' = Thm.cterm_of ctxt (HOLogic.mk_tuple vs)
      val idx = Thm.maxidx_of_cterm vs' + 1
      val rule = Drule.infer_instantiate ctxt [(("sch",idx),vs')]
                    (Thm.incr_indexes idx @{thm Collect_Schematic_I})
    in Seq.single (ctxt, rule RS sequent)
    end
\<close>

(*Others, to be done!*)


end