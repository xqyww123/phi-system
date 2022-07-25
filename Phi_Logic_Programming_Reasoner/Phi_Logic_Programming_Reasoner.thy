theory Phi_Logic_Programming_Reasoner
  imports Main "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  keywords "no" "on" :: quasi_command
    and "\<phi>reasoner" "\<phi>reasoner_ML" :: thy_decl % "ML"
  abbrevs
      "<premise>" = "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e"
  and "<simprem>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m"
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
   Syntax: \<phi>intro [add] <spur-of-the-rule> || \<phi>intro del\<close>

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

subsubsection \<open>Mode\<close>

text \<open>Modes are annotations of the automation. They are typically used specifically to determine
  the modes of the automation method to be applied. For example, see the Premise tag.\<close>

typedef mode = "UNIV :: nat set" ..

consts MODE_NORMAL :: mode \<comment> \<open>A generically used tag of the meaning of `default, the most common'.\<close>
consts MODE_SIMP :: mode \<comment> \<open>relating to simplifier or simplification\<close>
consts MODE_COLLECT :: mode \<comment> \<open>relating to collection\<close>

subsubsection \<open>Focus\<close>

text \<open>A general technical tag used in the reasoning, usually represents the reasoning
  currently focuses on certain part, certain target.\<close>

definition FOCUS_TAG :: " 'a \<Rightarrow> 'a "  ("\<blangle> _ \<brangle>") where [iff]: "\<blangle> x \<brangle> = x"


subsection \<open>Proof Obligation\<close>

definition Premise :: "mode \<Rightarrow> bool \<Rightarrow> bool" where "Premise _ x = x"

abbreviation Normal_Premise ("\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e _" [27] 26) where "Normal_Premise \<equiv> Premise MODE_NORMAL"
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

lemma Premise_refl[\<phi>reason 2000 on \<open>Premise ?mode (?x = ?x)\<close>]:
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



subsection \<open>Conversion\<close>

definition Conv :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v _ = _" [51,51] 50)
  where "Conv origin obj \<longleftrightarrow> obj = origin"

text \<open>\<^prop>\<open>\<^bold>c\<^bold>o\<^bold>n\<^bold>v A = B\<close> indicates the reasoner should convert \<^term>\<open>A\<close> into some \<^term>\<open>B\<close>.
  Specific rules should be configured to reason those goals.\<close>



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


definition GOAL_CTXT :: "bool \<Rightarrow> subgoal \<Rightarrow> prop"  ("_  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L _" [2,1000] 2)
  where [iff]: "GOAL_CTXT x _ \<equiv> Trueprop x"


subsection \<open>Simplification & Rewrite\<close>

definition Simplify :: " mode \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[_] _ : _" [10,1000,10] 9)
  where "Simplify setting result origin \<longleftrightarrow> result = origin"

lemma [cong]: "A = A' \<Longrightarrow> Simplify s x A = Simplify s x A' "
  unfolding Simplify_def by simp

lemma Simplify_I[intro!]: "Simplify s A A" unfolding Simplify_def ..
lemma Simplify_E[elim!]: "Simplify s A B \<Longrightarrow> (A = B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Simplify_def by blast


subsubsection \<open>Default Simplifier\<close>

consts default_simp_setting :: mode

abbreviation Default_Simplify :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y _ : _" [1000,10] 9)
  where "Default_Simplify \<equiv> Simplify default_simp_setting"

\<phi>reasoner Default_Simplify 1000 (conclusion \<open>Default_Simplify ?x ?y\<close>)
  = (simp, rule Simplify_I)
  
(* \<open>fn ctx =>
  HEADGOAL (asm_simp_tac ctx) THEN
  HEADGOAL (resolve0_tac @{thms Simplify_I})
\<close> *)






end