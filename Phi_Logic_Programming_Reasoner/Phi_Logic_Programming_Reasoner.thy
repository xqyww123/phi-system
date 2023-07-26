theory Phi_Logic_Programming_Reasoner
  imports PLPR_error_msg "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools" "Phi_Document.Base"
  keywords "except" "@action" :: quasi_command
    and "\<phi>reasoner" "\<phi>reasoner_ML" :: thy_decl % "ML"
    and "print_\<phi>reasoners" :: diag
  abbrevs
      "<premise>" = "\<p>\<r>\<e>\<m>\<i>\<s>\<e>"
  and "<guard>" = "\<g>\<u>\<a>\<r>\<d>"
  and "<condition>" = "\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>"
  and "<@GOAL>" = "@GOAL"
  and "<threshold>" = "\<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d>"
  and "!!" = "!!"
  and "??" = "??"
begin

subsubsection \<open>Prelude Settings\<close>

setup \<open>
let
  val basic_entity = Document_Output.antiquotation_pretty_source_embedded
  fun pretty_term_style ctxt (style, t) = Document_Output.pretty_term ctxt (style t)

  fun typ  mode = Scan.peek (Args.named_typ  o Syntax.read_typ
                                             o Proof_Context.set_mode mode o Context.proof_of)
  fun term mode = Scan.peek (Args.named_term o Syntax.read_term
                                             o Proof_Context.set_mode mode o Context.proof_of)
  fun prop mode = Scan.peek (Args.named_term o Syntax.read_prop
                                             o Proof_Context.set_mode mode o Context.proof_of)


in fn thy => thy
|>  ML_Antiquotation.inline_embedded \<^binding>\<open>pattern\<close>
    (Args.term_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term))
|> ML_Antiquotation.inline_embedded \<^binding>\<open>pattern_prop\<close>
    (prop Proof_Context.mode_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term))
|> ML_Antiquotation.value_embedded \<^binding>\<open>schematic_ctyp\<close> (typ Proof_Context.mode_schematic
      >> (fn T => "Thm.ctyp_of ML_context"  ^ ML_Syntax.atomic (ML_Syntax.print_typ T)))
|> ML_Antiquotation.value_embedded \<^binding>\<open>schematic_cterm\<close> (term Proof_Context.mode_schematic
      >> (fn t => "Thm.cterm_of ML_context" ^ ML_Syntax.atomic (ML_Syntax.print_term t)))
|> ML_Antiquotation.value_embedded \<^binding>\<open>schematic_cprop\<close> (prop Proof_Context.mode_schematic
      >> (fn t => "Thm.cterm_of ML_context" ^ ML_Syntax.atomic (ML_Syntax.print_term t)))
|> basic_entity \<^binding>\<open>schematic_term\<close> (Term_Style.parse -- term Proof_Context.mode_schematic)
                                        pretty_term_style
|> basic_entity \<^binding>\<open>schematic_prop\<close> (Term_Style.parse -- prop Proof_Context.mode_schematic)
                                        pretty_term_style
|> basic_entity \<^binding>\<open>pattern_term\<close> (Term_Style.parse -- term Proof_Context.mode_pattern)
                                        pretty_term_style
|> basic_entity \<^binding>\<open>pattern_prop\<close> (Term_Style.parse -- prop Proof_Context.mode_pattern)
                                        pretty_term_style
end\<close>

ML_file \<open>library/tools/ml_thms.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file_debug \<open>library/helpers.ML\<close>
ML_file \<open>library/tools/Hook.ML\<close>
ML_file \<open>library/handlers.ML\<close>
ML_file_debug \<open>library/pattern_translation.ML\<close>
ML_file \<open>library/tools/simpset.ML\<close>

definition \<r>Guard :: \<open>prop \<Rightarrow> prop\<close> ("\<g>\<u>\<a>\<r>\<d> _" [2] 2) where \<open>\<r>Guard X \<equiv> X\<close>
    \<comment> \<open>If guards of a rule fail, the rule will be considered not appliable, just like the pattern
        mismatch. It makes difference for cut rule and default 'to-be-overrided' rules.
        If the rule is considered not appliable, the cut will not make effect and it will not
        override default 'to-be-overrided' rules. \<close>

typedecl action

definition Action_Tag :: \<open>bool \<Rightarrow> action \<Rightarrow> bool\<close> ("_ @action _" [10,10] 9)
  where \<open>Action_Tag P A \<equiv> P\<close>

lemma Action_Tag_I:
  \<open>P \<Longrightarrow> P @action A\<close>
  unfolding Action_Tag_def .

ML_file_debug \<open>library/reasoner.ML\<close>

lemma \<r>Guard_I[\<phi>reason 1000]: \<open>PROP P \<Longrightarrow> PROP \<r>Guard P\<close> unfolding \<r>Guard_def .

ML \<open>@{thm' equal_elim_rule2} RS @{thm equal_elim_rule2}\<close>

section \<open>Introduction\<close>

text \<open>
  \<phi>-Logic Programming Reasoner is a extensible reasoning engine
  based on logic programming like Prolog.
  It allows arbitrary user reasoners to be integrated freely, and applies them selectively
  by matching the pattern of the goals.

  The reasoning is a depth-first heuristic search guided by \<^emph>\<open>priority\<close> of each branch.
  A reasoning state is represented by a \<^emph>\<open>pair\<close> of \<^verbatim>\<open>Proof.context\<close> and a sequent, of type
  \<^verbatim>\<open>Proof.context * thm\<close>.
  Search branches on a reasoning state are admissible reasoners on the sequent.
  A reasoner is admissible on a sequent if the sequent matches the pattern of the reasoner
  (cf. patterns in \cref{sec:patterns}).

  The reasoning accepts several reasoning states, and outputs \<^emph>\<open>one\<close> reasoning state which is the
  first one satisfies the termination condition, \<^emph>\<open>or\<close> none if every search branches fail.

  The priorities of rules demonstrate which rules are better among admissible reasoners.
  The priority makes sense only locally, among all admissible reasoners on a reasoning state.
  The accumulation of priority values (i.e. the sum of the priority of all applied reasoners) of a
  reasoning state is meaningless and merely for debug-usage.
  Because it is a DFS, the first reached result is the optimal one w.r.t each search branches in a
  greedy sense. (the global maximum is senseless here because the priority accumulation is
  meaningless).

  The sequent of the reasoning state is a Harrop Formula (HF), e.g.,
  \[ \<open>Antecedent1 \<Longrightarrow> Antecedent2 \<Longrightarrow> Conclusion\<close>, \]
  where antecedents represent sub-goals that have to be reasoned \textit{in order}.

  The \xphi-LPR engine reasons antecedents in order, invoking the reasoners that match the pattern
  of the leading antecedent best (cf. Priority).

  An antecedent can be augmented by conditions that can be utilized during the reasoning.
  It can also be universally quantified.
  \[ \<open>(\<And>x. P1 x \<Longrightarrow> P2 x \<Longrightarrow> Conclusion_of_Antecedent1 x) \<Longrightarrow> A2 \<Longrightarrow> C\<close> \]

  A typically reasoner is to deduce the conclusion of the antecedent by applying an introduction
  rule like \<open>A11 x \<Longrightarrow> A12 x \<Longrightarrow> Conclusion_of_Antecedent1 x\<close>, resulting in
  \[ \<open>(\<And>x. P1 x \<Longrightarrow> P2 x \<Longrightarrow> A11 x) \<Longrightarrow> (\<And>x. P11 x \<Longrightarrow> P12 x \<Longrightarrow> A12 x) \<Longrightarrow> A2 \<Longrightarrow> C\<close>. \]

  Then, the engine reasons the currently heading antecedent \<open>(\<And>x. P1 x \<Longrightarrow> P2 x \<Longrightarrow> A11 x)\<close>
  recursively. The antecedent list of a reasoning state resembles a calling stack of usual programs.
  From this perspective, the introduction rule of \<^prop>\<open>Antecedent1\<close> invokes two 'sub-routines'
  (or the reasoners of) \<^prop>\<open>A11\<close> and \<^prop>\<open>A22\<close>.
  \<close>

section \<open>The Engine \& The Concepts\<close>

text \<open>
The engine is implemented in \<^verbatim>\<open>library/reasoner.ML\<close>.

\<^verbatim>\<open>structure Phi_Reasoner = struct

(*Reasoning state*)
type context_state = Proof.context * thm
type name = term (* the name as a term is just for pretty printing *)

val pattern_on_conclusion : term -> pattern
val pattern_on_condition  : term -> pattern

(*A reasoner is a quintuple*)
type reasoner = {
  name: name,
  pos: Position.T,
  pattern: pattern list,
  blacklist: pattern list,
  tactic: context_state -> context_state Seq.seq
}

type priority = int
val add : priority * reasoner -> Context.generic -> Context.generic
val del : name -> Context.generic -> Context.generic
val reason : context_state -> context_state option

val auto_level : int Config.T

exception Success of context_state
exception Global_Cut of context_state

...
end
\<close>\<close>

paragraph \<open>Patterns \label{sec:patterns}\<close>

text \<open>
The \<^bold>\<open>pattern\<close> and the \<^bold>\<open>blacklist\<close> stipulate the range in which a reasoner will be invoked.
A reasoner is invoked iff the antecedent matches at least one pattern in the pattern list and none
  in the blacklist.\<close>

text \<open>
There are two kinds of patterns, that match on conclusion and that on condition, constructed by
\<^verbatim>\<open>pattern_on_conclusion\<close> and \<^verbatim>\<open>pattern_on_conclusion\<close> respectively.
\<close>

text \<open>\<^bold>\<open>Prefix \<^verbatim>\<open>var\<close>\<close>. A schematic variable in a pattern can have name prefix \<^verbatim>\<open>var_\<close>.
In this case, the variable only matches schematic variables.

\<^emph>\<open>Remark\<close>: It is important to write schematic variables in patterns explicitly. The engine
does not convert any free variables to schematic variables implicitly.\<close>


paragraph \<open>Automatic Level\<close> text \<open>by \<^verbatim>\<open>auto_level\<close>
is a general configuration deciding whether the engine applies
  some aggressive tactics that may consume considerable time or never terminate.

There are 3 levels:
\<^enum>[0]: the most safe, which may mean manual mode for some reasoner.
      It does not exclude non-termination or blocking when some tactics are necessary for the
      features. Method @{method simp} and @{method clarify} are acceptable on this level.
\<^enum>[1]: relatively safe automation, where aggressive tactics are forbidden but non-termination is
  still possible. Method @{method auto} is forbidden in this level because it blocks too easily.
\<^enum>[2]: the most powerful automation, where no limitation is imposed on automation strategies.\<close>

paragraph \<open>Priority \label{sec:cut}\<close>

text \<open>

The reasoning is a depth-first search and every reasoner is registered with a priority deciding
the order of attempting the reasoners. Reasoners with higher priority are attempted first.

According to the priority of reasoners, reasoners fall into 3 sorts corresponding to
different pruning optimization strategy.

\<^enum> When the priorities of the candidate reasoners on a certain reasoning state are all less than 1000,
  the reasoning works in the normal behavior where it attempts the highest candidate and once fails
  backtracks to the next candidate.

\<^enum> When the highest priority of the candidates $\geq$ 1000 and $<$ than 1000,000,
  this candidate becomes a \<^emph>\<open>local cut\<close>. The reasoning attempts only the local cut and if it fails,
  no other candidates will be attempted, but the backtrack is still propagated to the upper layer
  (of the search tree).
  Any presence of a candidate with priority $\geq$ 1000, causes the reasoning (at this point)
  is confident (in the sense that no alternative search branch will be attempted).

\<^enum> When the highest priority of the candidates $\geq$ 100,000,
  this candidate becomes a \<^emph>\<open>global cut\<close>, which forgets all the previous search history.
  No backtrack will be propagated to the past before the global cut so it improves the performance.
  Once the reasoning of the branch of the cut fails, the whole reasoning fails.

Reasoners of priority $\geq$ 1000 are named \<^emph>\<open>confident reasoners\<close> and others are
\<^emph>\<open>submissive reasoners\<close>.

\<^emph>\<open>Remark\<close>: a local cut reasoner can throw \<^verbatim>\<open>Global_Cut s\<close> to trigger a global cut with the
  reasoning state \<^verbatim>\<open>s\<close>.

\<close>


paragraph \<open>Termination\<close>

text \<open>The reasoning terminates when:

\<^item> Any reasoning state has no antecedent any more or all its designated leading
    antecedents are solved. This reasoning state is returned.
\<^item> Any reasoner throws \<^verbatim>\<open>Success result\<close>.
\<^item> All accessible search paths are traversed.
\<close>

text \<open>\<open>\<r>Success\<close> is an antecedent that throws \<^verbatim>\<open>Success\<close>.
Therefore it remarks the reasoning is succeeded.
A typical usage of \<open>\<r>Success\<close> is shown in the following sequent,
\[ \<open>A1 \<Longrightarrow> A2 \<Longrightarrow> \<r>Success \<Longrightarrow> P \<Longrightarrow> Q\<close> \]
which expresses the reasoning succeeds after solving \<^prop>\<open>A1\<close>, \<^prop>\<open>A2\<close>, and it outputs
  result \<^prop>\<open>P \<Longrightarrow> Q\<close>.\<close>

text \<open>\<open>Pure.prop P\<close> is helpful to protect remaining antecedents if you only want to reason
  the beginning several antecedents instead of all antecedents, e.g.,
\[ \<open>Solve_A1 \<Longrightarrow> Pure.prop (Protect_A2 \<Longrightarrow> C)\<close> \]\<close>

paragraph \<open>Output\<close>

text \<open>The output reasoning state can be:

\<^item> The first traversed reasoning state that has no antecedent or all the designated leading
    antecedents are solved.
\<^item> The \<^verbatim>\<open>result\<close> threw out by \<^verbatim>\<open>Success result\<close>.

\<close>

text \<open>If none of the above are reached during a reasoning process, the process returns nothing
  (\<^verbatim>\<open>None\<close> or \<^verbatim>\<open>Seq.empty\<close>).
The reasoning only outputs \<^emph>\<open>milestone states\<close> representing the problem is indeed solved partially
instead of any unfinished intermediate reasoning state.
Milestone states are explicitly annotated by user (e.g.,
  by antecedent \<^prop>\<open>\<r>Success\<close> or by setting the priority to 1000,000).
Any other intermediate reasoning state is not considered a successfully finished state
so that is not outputted.\<close>


section \<open>Provide User Reasoners \& Apply the Engine\<close>

text \<open>\xphi-LPR can be augmented by user reasoners.
The system predefines a resolution based reasoner using introducing rules and elimination rules.
Other arbitrary reasoners can also be built from tactics or ML code.\<close>

subsection \<open>Reasoning by Rules\<close>

text \<open>Attributes @{attribute_def \<phi>reason} is provided for introducing resolution rules.

  \begin{matharray}{rcl}
    @{attribute_def \<phi>reason} & : & \<open>attribute\<close>
  \end{matharray}

  \small
  \<^rail>\<open>
    @@{attribute \<phi>reason} (@{syntax add_rule} | 'add' @{syntax add_rule} | 'del')
    ;
    @{syntax_def add_rule}: @{syntax priority}?
    ('for' @{syntax patterns})? ('except' @{syntax blacklist})?
    ;
    @{syntax_def priority}: ((() | '?' | '!' | '!!' | 'default') @{syntax nat})
    ;
    @{syntax_def patterns}: (() + @{syntax term})
    ;
    @{syntax_def blacklist}: (() + @{syntax term})
  \<close>
  \normalsize

\<^descr> @{attribute \<phi>reason}~\<^verbatim>\<open>add\<close> declares reasoning rules used in \<phi>-LPR.
  @{attribute \<phi>reason}~\<^verbatim>\<open>del\<close> removes the reasoning rule.
  If no keyword \<^verbatim>\<open>add\<close> or \<^verbatim>\<open>del\<close> is given, \<^verbatim>\<open>add\<close> is the default option.

\<^descr> The @{syntax patterns} and @{syntax blacklist} are that described in \cref{sec:patterns}.
  For introduction rules, the patterns and the blacklist match only the conclusion of the
  leading antecedent; for elimination rules, they match only the conditions of the
  leading antecedent.

  Patterns can be omitted. For introduction rule, the default pattern is the conclusion
  of the rule; for elimination rule, the default is the first premise.

\<^descr> @{syntax priority} is a natural number together with an option mode description.
  '!' means the rule is a local cut, '!!' is for global cut, '?' for the normal rule with backtrack.
  'default' is for those automatically generated rule able to be override by user easily.
  The default priority is 100 with backtrack.

  Once a rule is declared as 'default', it is only applied when there is no other applicable rules
  of higher priority, even when the application of the rules fails.
  When you declare a rule as 'default', you may ask yourself, if the users provide another rule of
  a higher priority, and the rule fails, is your rule still expected to be applied? If it is true,
  your rule should not be declared as 'default' but just a normal rule with backtrack.
\<close>

text \<open>\<^emph>\<open>Remark\<close>: Rules of priority $\geq$ 1000 are named \<^emph>\<open>confident rules\<close> and others are
\<^emph>\<open>submissive rules\<close>.\<close>

text \<open>\<^emph>\<open>Remark\<close>: Attribute @{attribute \<phi>reason} can be used without any argument.
  \<^verbatim>\<open>[[\<phi>reason]]\<close> denotes \<^verbatim>\<open>[[\<phi>reason add]]\<close> exactly.
  However, the usage of empty arguments is not recommended
  due to technical reasons that in this case of empty argument
  the attribute cannot get the position of the associated reasoning rule, and
  this position is displayed in debug printing.\<close>

paragraph \<open>Example\<close>

declare TrueI[\<phi>reason 1000]

paragraph \<open>\<open>\<r>\<close>Feasible \label{sec:rFeasible}\<close>

text \<open>Cut rules including local cut and global cut are those of priority $\geq$ 1000.
A cut rule can have at most one special \<open>\<r>Guard\<close> antecedent at the leading position,
which determines the condition of the rule to be applied, e.g. the following rule can be applied
only if \<open>A1\<close> and \<open>A2\<close> are solvable.
\[ \<open>\<r>Guard (A1 &&& A2) \<Longrightarrow> A3 \<Longrightarrow> C\<close> \]
It provides a mechanism to constrain semantic conditions of applying the rule,
whereas the pattern matches mentioned earlier are only able to check the syntactical conditions.
\<close>

subsection \<open>Reasoners by Isar Methods and ML code\<close>

text \<open>
There are two commands defining reasoners, respectively by Eisbach expression and by ML code.

  \begin{matharray}{rcl}
    @{command_def \<phi>reasoner} & : & \<open>local_theory \<rightarrow> local_theory\<close>\\
    @{command_def \<phi>reasoner_ML} & : & \<open>local_theory \<rightarrow> local_theory\<close>\\
  \end{matharray}

  \<^rail>\<open>
    @@{command \<phi>reasoner} @{syntax name} @{syntax priority} @{syntax patterns'} '=' @{syntax Eisabach_method}
    ;
    @@{command \<phi>reasoner_ML} @{syntax name} @{syntax priority} @{syntax patterns'} '=' @{syntax ML_code}
    ;
    @{syntax_def patterns'}: '(' (@{syntax term} + '\<bar>') ')'
  \<close>

\<^descr> @{command \<phi>reasoner} defines a reasoner using an Eisabach expression. The Eisabach expression
  defines a proof method in Isabelle/Isar and this proof method is invoked on the leading antecedent
  as a sub-goal when @{syntax patterns'} match.

\<^descr> @{command \<phi>reasoner_ML} defines a reasoner from ML code. The given code should be a ML function
  of type \<^verbatim>\<open>context_state -> context_state Seq.seq\<close>, i.e., a contextual tactic.

\<close>

subsection \<open>Apply the Engine\<close>

text \<open>There are two ways to use the reasoning engine, from ML code by using \<^verbatim>\<open>Phi_Reasoner.reason\<close>,
and as a proof method.\<close>

subsubsection \<open>Proof Method\<close>

text \<open>
There are two commands defining reasoners, respectively by Eisbach expression and by ML code.

  \begin{matharray}{rcl}
    @{method_def \<phi>reason} & : & \<open>method\<close>\\
  \end{matharray}

  \<^rail>\<open>
    @@{method \<phi>reason} ('add' @{syntax thms})? ('del' @{syntax thms})?
  \<close>

\<^descr> @{method \<phi>reason}~\<^verbatim>\<open>add\<close>~\<open>a\<close>~\<^verbatim>\<open>del\<close>~\<open>b\<close>
  applies \<phi>-LPR on the proof state (which is a HHF sequent~\cite{isar-ref}).
  It means subgoals of the proof are regarded as antecedents and \<phi>-LPR reasons them one by one
  in order.

  Optional modifier \<^verbatim>\<open>add\<close>~\<open>a\<close> adds introduction rules \<open>a\<close> temporarily with default patterns
  (the conclusion of the rule) and default priority (100).
  Modifier \<^verbatim>\<open>del\<close>~\<open>b\<close> removes introductions rules \<open>b\<close> temporarily.
  We do not provide modifiers to alter elimination rules now.
\<close>


section \<open>Predefined Antecedents, Reasoners, and Rules\<close>


subsection \<open>Auxiliary Structures\<close>

subsubsection \<open>Isomorphic Atomize\<close>

text \<open>The system \<open>Object_Logic.atomize\<close> and \<open>Object_Logic.rulify\<close> is not isomorphic in the sense
  that for any given rule \<open>R\<close>, \<open>Object_Logic.rulify (Object_Logic.atomize R)\<close> does not exactly
  equal \<open>R\<close>. The section gives a way addressing this issue.\<close>

ML_file \<open>library/iso_atomize.ML\<close>

definition \<open>pure_imp_embed \<equiv> (\<longrightarrow>)\<close>
definition pure_all_embed :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>\<forall>\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>d \<close> 10)
    \<comment> \<open>We give it a binder syntax to prevent eta-contraction which
        deprives names of quantifier variables\<close>
  where \<open>pure_all_embed \<equiv> (All)\<close>
definition \<open>pure_conj_embed \<equiv> (\<and>)\<close>
definition \<open>pure_prop_embed x \<equiv> x\<close>
definition \<open>pure_eq_embed \<equiv> (=)\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(X \<equiv> Y) \<equiv> Trueprop (pure_eq_embed X Y)\<close>
  unfolding pure_eq_embed_def atomize_eq .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(P \<Longrightarrow> Q) \<equiv> Trueprop (pure_imp_embed P Q)\<close>
  unfolding atomize_imp pure_imp_embed_def .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(P &&& Q) \<equiv> Trueprop (pure_conj_embed P Q)\<close>
  unfolding atomize_conj pure_conj_embed_def .

(*TODO: find a way to preserve the name*)
lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(\<And>x. P x) \<equiv> Trueprop (pure_all_embed (\<lambda>x. P x))\<close>
  unfolding atomize_all pure_all_embed_def .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>PROP Pure.prop (Trueprop P) \<equiv> Trueprop (pure_prop_embed P)\<close>
  unfolding Pure.prop_def pure_prop_embed_def .


subsubsection \<open>Action\<close>

text \<open>In the reasoning, antecedents of the same form may have different purposes, e.g.,
  antecedent \<open>P = ?Q\<close> may except a complete simplification or numeric calculation only or any other
  specific conversion. Of different purposes, antecedents are expected to be processed by
  different reasoners. To achieves this, because the engine selects reasoners by syntactic pattern,
  this section proposes a general structure tagging the purpose of antecedents.

The purpose is denoted by \<open>action\<close> type, which is an unspecified type because it serves only for
  syntactic purpose.\<close>

text \<open>
\<open>\<open>P @action A\<close>\<close> tags antecedent \<^prop>\<open>P\<close> by the specific purpose denoted by \<^term>\<open>A\<close>.

  The type variable \<^typ>\<open>'category\<close> enables to classify actions by types and type classes.
  For example, some operation may be designed for any generic action \<open>?act :: (?'ty::cls) action\<close>
  that fall into class \<open>cls\<close>.

\<^emph>\<open>Comment: I am thinking this category type variable is a bad design because the indexing
  data structure (Net) we are using doesn't support type sort, causing this feature is actually
  not indexed at all, causing the reasoning here becomes searching one by one in linear time!
  Maybe classification should be done by some term-level structure. Let's think when have time!\<close>\<close>


lemma Action_Tag_D:
  \<open>P @action A \<Longrightarrow> P\<close>
  unfolding Action_Tag_def .

lemma Conv_Action_Tag_I:
  \<open>X = X @action A\<close>
  unfolding Action_Tag_def ..

ML_file \<open>library/action_tag.ML\<close>

subsubsection \<open>Mode\<close>

text \<open>Modes are general annotations used in various antecedents, which may configure
  for the specific reasoning behavior among slight different options.
  The exact meaning of them depend on the specific antecedent using them.
  An example can be found in \cref{sec:proof-obligation}.\<close>

type_synonym mode = action

text \<open>We provide a serial of predefined modes, which may be commonly useful.\<close>

consts default :: mode
consts MODE_SIMP :: mode \<comment> \<open>relating to simplification\<close>
consts MODE_COLLECT :: mode \<comment> \<open>relating to collection\<close>
consts MODE_AUTO :: \<open>mode \<Rightarrow> mode\<close> \<comment> \<open>something that will be triggered automatically\<close>



subsection \<open>General Rules\<close>

text \<open>\<^bold>\<open>Schematic variables\<close> are able to be instantiated (assigned) by reasoners.
 The instantiation of an schematic variable \<open>?v\<close> updates all the occurrences of \<open>?v\<close> in the
  remaining sequent, and this instantion can be seen as assigning results of the execution of the
  antecedent.
For example,
 \[ \<open>1 + 2 = ?result \<Longrightarrow> Print ?result \<Longrightarrow> Done\<close> \]
  the reasoning of antecedent \<open>1 + 2 = ?result\<close> instantiates \<open>?result\<close> to \<open>3\<close>, and results in
\[ \<open>Print 3 \<Longrightarrow> Done\<close> \]
 If view the antecedent as a program (sub-routine),
 the schematic variables of the antecedent have a meaning of \<^emph>\<open>output\<close>,
 and we name them \<^emph>\<open>output variables\<close>.

The following \<open>Try\<close> antecedent is a such example.\<close>

subsubsection \<open>Try\<close>

definition Try :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> where \<open>Try success_or_fail P = P\<close>

text \<open>
The typical usage is \<open>\<open>Try ?success_or_fail P\<close>\<close>, where
\<open>P\<close> should be an antecedent having some fallback reasoner (not given here),
and \<open>?success_or_fail\<close> is an output variable representing whether the \<open>P\<close> is successfully
deduced \<^emph>\<open>without\<close> using fallback.

A high priority (800) rule reasons \<open>\<open>Try True P\<close>\<close> normally and set the output variable
\<open>success_or_fail\<close> to be true.\<close>

lemma [\<phi>reason 800 for \<open>Try ?S ?P\<close>]:
  \<open> P
\<Longrightarrow> Try True P\<close>
  unfolding Try_def .

text \<open>
Users using \<open>\<open>Try True P\<close>\<close> should provide the fallback rule for their own \<open>P\<close>.
It depends on the application scenario and there is not a general rule for fallback of course.
The fallback rule may has the following form,
\[ \<open> Fallback_of_P \<Longrightarrow> Try False P \<close> \]
\<close>


subsubsection \<open>Compact Representation of Antecedents\<close>

declare conjunctionI[\<phi>reason 1000] conjI[\<phi>reason 1000]
        allI[\<phi>reason 1000] impI[\<phi>reason 1000]
        HOL.refl[\<phi>reason 1000 for \<open>_ = _\<close>]

(*
text \<open>Meta-programming is feasible on \<phi>-LPR.
The reasoning of an antecedent may generate dynamically another antecedent, and assign it to
an output variable of type \<^typ>\<open>bool\<close>.

When multiple antecedents are going to be generated, it is
more efficient to contract them into one antecedent using conjunctions (e.g. \<open>A1 \<and> A2 \<and> A3 \<and> \<cdots>\<close>),
so they can be represented by one output variable of type \<^typ>\<open>bool\<close>.

\<open>(\<and>\<^sub>r)\<close> and \<open>(\<forall>\<^sub>r)\<close> are used to contract antecedents and embed universally quantified variables
respectively.
\<close>

(*TODO: depreciate this!*)
definition Compact_Antecedent :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> (infixr "\<and>\<^sub>\<r>" 35)
  where [iff]: \<open>Compact_Antecedent = (\<and>)\<close>

definition Compact_Forall :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder "\<forall>\<^sub>\<r>" 10)
  where [iff]: \<open>Compact_Forall = All\<close>

text \<open>Assertive rules are given to unfold the compression and reason the antecedents in order.\<close>

lemma [\<phi>reason 1000]:
  \<open>P \<Longrightarrow> Q \<Longrightarrow> P \<and>\<^sub>\<r> Q\<close>
  unfolding Compact_Antecedent_def ..

lemma [\<phi>reason 1000]:
  \<open>(\<And>x. P x) \<Longrightarrow> \<forall>\<^sub>\<r>x. P x\<close>
  unfolding Compact_Forall_def ..
*)


subsubsection \<open>Matches\<close>

text \<open>Antecedent \<^prop>\<open>Matches pattern term\<close> asserts \<^term>\<open>pattern\<close> matches \<^term>\<open>term\<close>;
  \<^prop>\<open>NO_MATCH pattern term\<close> asserts \<^term>\<open>pattern\<close> does not match \<^term>\<open>term\<close>.\<close>

definition Matches :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where \<open>Matches _ _ = True\<close>

lemma Matches_I: \<open>Matches pattern term\<close> unfolding Matches_def ..

\<phi>reasoner_ML Matches 2000 (\<open>Matches ?pattern ?term\<close>) =
  \<open>fn (ctxt, sequent) =>
    let
      val (\<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Matches\<close>,_) $ pattern $ term))
            = Thm.major_prem_of sequent
    in
      if Pattern.matches (Proof_Context.theory_of ctxt) (pattern, term)
      then Seq.single (ctxt, @{thm Matches_I} RS sequent)
      else Seq.empty
    end\<close>

lemma NO_MATCH_I: "NO_MATCH A B" unfolding NO_MATCH_def ..

\<phi>reasoner_ML NO_MATCH !1 ("NO_MATCH ?A ?B") = \<open>
  fn (ctxt,th) =>
  let
    val (\<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>NO_MATCH\<close>, _) $ a $ b)) = Thm.major_prem_of th
  in
    if Pattern.matches (Proof_Context.theory_of ctxt) (a,b)
    then Seq.empty
    else Seq.single (ctxt, @{thm NO_MATCH_I} RS th)
  end
\<close>


subsubsection \<open>Proof By Assumption\<close>

definition By_Assumption :: \<open>prop \<Rightarrow> prop\<close> where \<open>By_Assumption P \<equiv> P\<close>
definition May_By_Assumption :: \<open>prop \<Rightarrow> prop\<close> where \<open>May_By_Assumption P \<equiv> P\<close>

lemma By_Assumption_I: \<open>PROP P \<Longrightarrow> PROP By_Assumption P\<close> unfolding By_Assumption_def .
lemma May_By_Assumption_I: \<open>PROP P \<Longrightarrow> PROP May_By_Assumption P\<close> unfolding May_By_Assumption_def .

\<phi>reasoner_ML By_Assumption 1000 (\<open>PROP By_Assumption _\<close>) = \<open>fn (ctxt,sequent) =>
    HEADGOAL (Tactic.assume_tac ctxt) (@{thm By_Assumption_I} RS sequent)
      |> Seq.map (pair ctxt)
\<close>

\<phi>reasoner_ML May_By_Assumption 1000 (\<open>PROP May_By_Assumption _\<close>) = \<open>fn (ctxt,sequent) =>
  let val sequent' = @{thm May_By_Assumption_I} RS sequent
   in (HEADGOAL (Tactic.assume_tac ctxt) ORELSE Seq.single) sequent'
        |> Seq.map (pair ctxt)
  end
\<close>


subsection \<open>Cut\<close>

text \<open>The cuts have been introduced in \cref{sec:cut}.

Antecedent \<open>\<r>Cut\<close> triggers a global cut.
\<close>

definition \<r>Cut :: bool where \<open>\<r>Cut = True\<close>

lemma [iff, \<phi>reason 1000000]: \<open>\<r>Cut\<close> unfolding \<r>Cut_def ..

text \<open>Antecedent \<open>\<r>Success\<close> terminates the reasoning successfully with the reasoning state as
the result.\<close>

definition \<r>Success :: bool where \<open>\<r>Success = True\<close>
lemma \<r>Success_I: \<open>\<r>Success\<close> unfolding \<r>Success_def ..

declare [[ML_debugger]]

\<phi>reasoner_ML \<r>Success 10000 (\<open>\<r>Success\<close>) = \<open>fn (ctxt,sequent) =>
  raise Phi_Reasoner.Success (ctxt, @{thm \<r>Success_I} RS sequent)\<close>


subsection \<open>Proof Obligation \& Guard of Rule \label{sec:proof-obligation}\<close>

definition Premise :: "mode \<Rightarrow> bool \<Rightarrow> bool" ("\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[_] _ " [1000,27] 26)
  where "Premise mode x \<equiv> x"

abbreviation Normal_Premise ("\<p>\<r>\<e>\<m>\<i>\<s>\<e> _" [27] 26)
  where "Normal_Premise \<equiv> Premise default"
abbreviation Simp_Premise ("\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> _" [27] 26)
  where "Simp_Premise \<equiv> Premise MODE_SIMP"
abbreviation Proof_Obligation ("\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> _" [27] 26)
  where "Proof_Obligation \<equiv> Premise MODE_COLLECT"


text \<open>
  \<^prop>\<open>Premise mode P\<close> represents an ordinary proposition has to be proved during the reasoning.
  There are different modes expressing different roles in the reasoning.

  \<^descr> \<^prop>\<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P\<close> is a \<^emph>\<open>guard\<close> of a rule, which constrains that the rule is appliable only
  when \<^prop>\<open>P\<close> can be solved \<^emph>\<open>automatically\<close> during the reasoning.
  If \<^prop>\<open>P\<close> fails to be solved, even if it is actually valid, the rule will not be applied.
  Therefore, \<^prop>\<open>P\<close> has to be as simple as possible. The tactic used to solve \<^prop>\<open>P\<close> is
  @{method clarsimp}.
  A more powerful tactic like @{method auto} is not adoptable because the tactic must be safe and
  non-blocking commonly.
  A blocking search branch blocks the whole reasoning, which is not acceptable.

  \<^prop>\<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P\<close> is not for proof obligations that are intended to be solved by users.
  It is more like 'controller or switch' of the rules, i.e. \<^emph>\<open>guard\<close>.

  \<^descr> \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close> represents a proof obligation.
  Proof obligations in reasoning rules should be represented by it.

  \<^descr> \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> by contrast
  represents proof obligations \<open>Q\<close> that are ready to be solved by user (or by automatic tools).
\<close>
text \<open>
  The difference between \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> and \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close> is subtle:
  In a reasoning process, many reasoning rules may be applied, which may generate many
  \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close>.
  The engine tries to solve \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close> automatically but if it fails the search branch
  would be stuck. Because the search has not been finished, it is bad to ask users' intervention
  to solve the goal because the search branch may high-likely fail later.
  It is \<^emph>\<open>not ready\<close> for user to solve \<open>P\<close> here, and suggestively \<open>P\<close> should be deferred to
  an ideal moment for user solving obligations.
  This is `ideal moment' is \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close>. If any \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> exists in the antecedents
  of the sequent, the engine contracts \<open>P\<close> into the latest \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close>, e.g., from
  \[ \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> A1 \<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q \<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q' \<Longrightarrow> \<cdots> \<close> \]
  it deduces
  \[ \<open>A1 \<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q \<and> P \<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q' \<Longrightarrow> \<cdots> \<close> \]
  In short, \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> collects obligations generated during a reasoning process,
  and enables user to solve them at an idea moment.

  A typical reasoning request (the initial reasoning state namely the argument of the reasoning
  process) is of the following form,
 \[ \<open>Problem \<Longrightarrow> \<r>Success \<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> Conclusion\<close> \]
  The \<open>True\<close> represents empty collection or none obligation.
  If the reasoning succeeds, it returns sequent in form
 \[ \<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<and> P1 \<and> P2 \<and> \<cdots> \<Longrightarrow> Conclusion\<close> \]
  where \<open>P1, P2, \<cdots>\<close> are obligations generated by reasoning \<open>Problem\<close>.
  And then, user may solve the obligations manually or by automatic tools.

  For antecedent \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close>,
  if there is another \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q'\<close> in the remaining antecedents,
  the reasoner also defer \<open>Q\<close> to \<open>Q'\<close>, just like \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> is a \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q\<close>.

  If no \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q'\<close> exists in the remaining antecedents,
  the reasoner of \<^prop>\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P\<close> and \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> raises
  an error aborting the whole reasoning, because the reasoning request is not configured correctly.

  Semantically, \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> represents a proof obligation \<open>Q\<close> intended to be addressed by
  user. It can be deferred but the reasoner never attempts to solve \<^prop>\<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Q\<close> practically.

  Nonetheless, we still provide tool for reasoning obligations automatically, albeit they have
  to be called separately with the reasoning engine. See \<^verbatim>\<open>auto_obligation_solver\<close> and
  \<^verbatim>\<open>safer_obligation_solver\<close> in \<^file>\<open>library/reasoners.ML\<close>.
\<close>

lemma Premise_I[intro!]: "P \<Longrightarrow> Premise mode P" unfolding Premise_def by simp
lemma Premise_D: "Premise mode P \<Longrightarrow> P" unfolding Premise_def by simp
lemma Premise_E: "Premise mode P \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> C" unfolding Premise_def by simp

lemma [simp]:
  \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> True\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> True\<close>
  unfolding Premise_def by simp+

subsubsection \<open>Implementation of the reasoners\<close>

lemma Premise_True[\<phi>reason 5000]: "Premise mode True" unfolding Premise_def ..

lemma [\<phi>reason 5000]:
  " Premise mode P
\<Longrightarrow> Premise mode (Premise any_mode P)"
  unfolding Premise_def .

(*TODO:
On pattern \<open>Premise ?mode (?x = ?var_x)\<close>, the instantiation in this rule can be aggresive.
Need some way to control it!
*)
lemma Premise_refl[\<phi>reason 2000 for \<open>Premise ?mode (?x = ?x)\<close>
                                    \<open>Premise ?mode (?x = ?var_x)\<close>
                                    \<open>Premise ?mode (?var_x = ?x)\<close>]:
  "Premise mode (x = x)"
  unfolding Premise_def ..

ML \<open>
structure Useful_Thms = Named_Thms (
  val name = \<^binding>\<open>useful\<close>
  val description = "theorems to be inserted in the automatic proving, \
        \having the same effect of using the @{command using} command."
)\<close>

setup \<open>Useful_Thms.setup\<close>

ML_file \<open>library/PLPR_Syntax.ML\<close>

paragraph \<open>Contract Premises for Reporting Obligation\<close>

lemma contract_premise_imp:
  \<open>(P \<Longrightarrow> PROP Waste \<Longrightarrow> Premise mode G) \<equiv> (PROP Waste \<Longrightarrow> Premise mode (P \<longrightarrow> G))\<close>
  unfolding Premise_def by (rule, rule, simp+)

lemma contract_add_additional_prems:
  \<open> Q
\<Longrightarrow> PROP Pure.prop (PROP Waste \<Longrightarrow> Q \<Longrightarrow> PROP P)
\<Longrightarrow> PROP Pure.prop (PROP Waste \<Longrightarrow> PROP P) \<close>
  unfolding Pure.prop_def .

lemma contract_drop_waste:
  \<open> PROP Pure.prop P \<Longrightarrow> PROP Pure.prop (PROP Waste \<Longrightarrow> PROP P) \<close>
  unfolding Pure.prop_def by simp

lemma contract_drop_waste_end:
  \<open> PROP P \<Longrightarrow> PROP Pure.prop P \<close>
  unfolding Pure.prop_def .

lemma contract_obligations:
  "(Premise mode' P \<Longrightarrow> Premise mode Q \<Longrightarrow> PROP C) \<equiv> (Premise mode (P \<and> Q) \<Longrightarrow> PROP C)"
  unfolding Premise_def by rule simp+

lemma contract_premise_all:
  "(\<And>x. Premise mode (P x)) \<equiv> Trueprop ( Premise mode (\<forall>x. P x)) "
  unfolding Premise_def atomize_all .

lemma contract_intro_Ex:
  \<open>(\<And>x. Premise mode (P x) \<Longrightarrow> PROP Q) \<equiv> (Premise mode (Ex P) \<Longrightarrow> PROP Q)\<close>
  for P :: \<open>'a \<Rightarrow> bool\<close>
  unfolding Premise_def
  apply rule
  subgoal premises prems
    using prems(1)[OF someI_ex[OF prems(2)]] .
  subgoal premises prems for x
    using prems(1)[OF exI[where P=P, OF prems(2)]] .
  done

text \<open>PLPR can infer existentially quantified obligation. However, the built-in automation of Isabelle
  seems to be not good for handling them. Therefore we introduce a special existential quantifier
  having the irreversible \<open>\<exists>\<^sub>I\<close> rule configured into the automation, in order to enhance the
  deficiency in Isabelle's automation.\<close>

paragraph \<open>A Special Ex-quantifier Patching the Reasoning\<close>

definition special_Ex (binder "\<exists>\<^sup>\<phi>\<^sup>-\<^sup>L\<^sup>P\<^sup>R" 10)
  where [iff]: \<open>special_Ex \<equiv> Ex\<close>

(*lemma [intro]:
  \<open>P x \<Longrightarrow> special_Ex P\<close>
  unfolding special_Ex_def
  by rule*)

lemma contract_intro_sp_Ex:
  \<open>(\<And>x. Premise mode (P x) \<Longrightarrow> PROP Q) \<equiv> (Premise mode (special_Ex P) \<Longrightarrow> PROP Q)\<close>
  for P :: \<open>'a \<Rightarrow> bool\<close>
  unfolding special_Ex_def
  using contract_intro_Ex .

lemma partition_conj_MM:
  \<open>(A \<and> B) \<and> (C \<and> D) \<equiv> (A \<and> C) \<and> (B \<and> D)\<close>
  unfolding atomize_eq
  by blast

lemma partition_conj_MN:
  \<open>(A \<and> B) \<and> C \<equiv> (A \<and> C) \<and> B\<close>
  unfolding atomize_eq by blast

lemma sp_ex_ex_comm:
  \<open>\<exists>\<^sup>\<phi>\<^sup>-\<^sup>L\<^sup>P\<^sup>R x. \<exists>y. P x y \<equiv> \<exists>y. \<exists>\<^sup>\<phi>\<^sup>-\<^sup>L\<^sup>P\<^sup>R x. P x y\<close>
  unfolding atomize_eq
  by simp blast

ML_file "library/tools/patch_for_Ex.ML"


simproc_setup move_sp_Ex_inside (\<open>\<exists>\<^sup>\<phi>\<^sup>-\<^sup>L\<^sup>P\<^sup>Rf. P f\<close>) = \<open>
  fn _ => fn ctxt => fn ctm =>
    SOME (Conv.changed_conv (Phi_Conv.move_Ex_inside (K Conv.all_conv) ctxt) ctm)
    handle CTERM _ => NONE
\<close>

(*lemmas [simp] =
  HOL.ex_disj_distrib[folded special_Ex_def]
  ex_simps[folded special_Ex_def]
  simp_thms(36, 39-40)[folded special_Ex_def]*)



paragraph \<open>Setup\<close>

ML_file "library/reasoners.ML"

\<phi>reasoner_ML Normal_Premise 10 (\<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> ?P\<close> | \<open>\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> ?P\<close>)
  = \<open>Phi_Reasoners.wrap (Phi_Reasoners.defer_obligation_tac (true,true,~1))\<close>

\<phi>reasoner_ML Simp_Premise 10 (\<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ?P\<close>)
  = \<open>Phi_Reasoners.wrap Phi_Reasoners.safer_obligation_solver\<close>

(* TODO: reenable!
hide_fact contract_premise_imp contract_drop_waste contract_obligations contract_premise_all
          contract_add_additional_prems
*)

subsection \<open>Exhaustive Reasoning\<close>

text \<open>\<phi>-LPR is a priority-guided depth-first reasoner giving the first reached solution.
  This extension enables exhaustive reasoning traverses all branches and combines proof obligations
  for each branch by disjuntion.\<close>

lemma merge_oblg_divergence:
  \<open> PROP Pure.prop (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Pa \<Longrightarrow> C)
\<Longrightarrow> PROP Pure.prop (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Pb \<Longrightarrow> C)
\<Longrightarrow> PROP Pure.prop (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> Pa \<or> Pb \<Longrightarrow> C)\<close>
  unfolding Pure.prop_def Premise_def by blast

ML_file_debug \<open>library/exhaustive.ML\<close>

hide_fact merge_oblg_divergence


subsection \<open>Environment Variables\<close>

definition Push_Envir_Var :: \<open>'name \<Rightarrow> 'a::{} \<Rightarrow> bool\<close>
  where \<open>Push_Envir_Var Name Val \<longleftrightarrow> True\<close>
definition Pop_Envir_Var  :: \<open>'name \<Rightarrow> bool\<close> where \<open>Pop_Envir_Var Name \<longleftrightarrow> True\<close>
definition Get_Envir_Var  :: \<open>'name \<Rightarrow> 'a::{} \<Rightarrow> bool\<close>
  where \<open>Get_Envir_Var Name Return \<longleftrightarrow> True\<close>
definition Get_Envir_Var' :: \<open>'name \<Rightarrow> 'a::{} \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>Get_Envir_Var' Name Default Return \<longleftrightarrow> True\<close>

subsubsection \<open>Implementation\<close>

ML_file \<open>library/envir_var.ML\<close>

lemma Push_Envir_Var_I: \<open>Push_Envir_Var N V\<close> unfolding Push_Envir_Var_def ..
lemma Pop_Envir_Var_I:  \<open>Pop_Envir_Var N\<close>    unfolding Pop_Envir_Var_def  ..
lemma Get_Envir_Var_I : \<open>Get_Envir_Var  N V\<close>   for V :: \<open>'v::{}\<close> unfolding Get_Envir_Var_def  ..
lemma Get_Envir_Var'_I: \<open>Get_Envir_Var' N D V\<close> for V :: \<open>'v::{}\<close> unfolding Get_Envir_Var'_def ..

\<phi>reasoner_ML Push_Envir_Var 1000 (\<open>Push_Envir_Var _ _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ $ (_ $ N $ V) = Thm.major_prem_of sequent
      val _ = if maxidx_of_term V <> ~1
              then warning "PLPR Envir Var: The value to be assigned has schematic variables \
                           \which will not be retained!"
              else ()
   in SOME ((PLPR_Env.push (PLPR_Env.name_of N) V ctxt,
            @{thm Push_Envir_Var_I} RS sequent),
      Seq.empty) end
)\<close>

\<phi>reasoner_ML Pop_Envir_Var 1000 (\<open>Pop_Envir_Var _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ $ (_ $ N) = Thm.major_prem_of sequent
   in SOME ((PLPR_Env.pop (PLPR_Env.name_of N) ctxt, @{thm Pop_Envir_Var_I} RS sequent),
      Seq.empty) end
)\<close>

\<phi>reasoner_ML Get_Envir_Var 1000 (\<open>Get_Envir_Var _ _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ $ (_ $ N $ _) = Thm.major_prem_of sequent
      val idx = Thm.maxidx_of sequent + 1
   in case PLPR_Env.get (PLPR_Env.name_of N) ctxt
        of NONE => Phi_Reasoner.error
                      ("No enviromental variable " ^ PLPR_Env.name_of N ^ " is set")
         | SOME V' =>
            let val V = Thm.incr_indexes_cterm idx (Thm.cterm_of ctxt V')
             in SOME ((ctxt, ( @{thm Get_Envir_Var_I}
                        |> Thm.incr_indexes idx
                        |> Thm.instantiate (TVars.make [((("'v",idx),[]), Thm.ctyp_of_cterm V)],
                                             Vars.make [((("V", idx),Thm.typ_of_cterm V), V)])
                         ) RS sequent),
                    Seq.empty)
            end
  end
)\<close>

\<phi>reasoner_ML Get_Envir_Var' 1000 (\<open>Get_Envir_Var' _ _ _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ $ (_ $ N $ D $ _) = Thm.major_prem_of sequent
      val idx = Thm.maxidx_of sequent + 1
      val V = Thm.cterm_of ctxt (case PLPR_Env.get (PLPR_Env.name_of N) ctxt
                                   of SOME V => V | NONE => D)
                |> Thm.incr_indexes_cterm idx
   in SOME ((ctxt, ( @{thm Get_Envir_Var'_I}
                  |> Thm.incr_indexes idx
                  |> Thm.instantiate (TVars.make [((("'v",idx),[]), Thm.ctyp_of_cterm V)],
                                       Vars.make [((("V", idx),Thm.typ_of_cterm V), V)])
                   ) RS sequent),
      Seq.empty)
  end
)\<close>




subsection \<open>Reasoning Frame\<close>

definition \<open>\<r>BEGIN \<longleftrightarrow> True\<close>
definition \<open>\<r>END \<longleftrightarrow> True\<close>

text \<open>Antecedents \<^prop>\<open>\<r>BEGIN\<close> and \<^prop>\<open>\<r>END\<close> conform a nested reasoning scope
resembling a subroutine for specific reasoning tasks or problems.
\[ \<open>\<dots> \<Longrightarrow> \<r>BEGIN \<Longrightarrow> Nested \<Longrightarrow> Reasoning \<Longrightarrow> \<r>END \<Longrightarrow> \<dots>\<close> \]
The scoped antecedents should be regarded as a \<^emph>\<open>unit antecedent\<close>
invoking a nested \<phi>-LPR reasoning process and returning \<^emph>\<open>only\<close> the first reached solution (
just as the behaviour of \<phi>-LPR engine).
Backtracking passes through the scoped antecedents to the earlier branches but NOT inside the scope.
In addition, cut is confined among the search paths in the scope as a unit.
Because of the cut and the reduced backtrack behavior, the performance is improved.

Sometimes a cut is admissible (green) as an expected behavior among several rules and reasoners
which constitute a loosely-gathered module for a specific problem.
However the cut is still not safe to be used because an external rule using the reasoning module
may demand the behavior of backtracking but the cut inside the module prevents
backtracks in the external rule.
In this case, the reasoning scope is helpful to wrap the loosely-gathered module to be confined
by closing side effects like cuts.

Specifically, any search path that reaches \<^prop>\<open>\<r>BEGIN\<close> opens a new \<^emph>\<open>frame\<close> namely a space
of search paths.
The sub-searches continuing the path and before reaching
the paired \<^prop>\<open>\<r>END\<close> are in this frame.
As \<phi>-LPR works in BFS, a frame can contain another frame just if the search in the frame
encounters another \<^prop>\<open>\<r>BEGIN\<close>.
\[ \<open>\<dots> \<Longrightarrow> \<r>BEGIN \<Longrightarrow> A\<^sub>1 \<Longrightarrow> \<r>BEGIN \<Longrightarrow> A\<^sub>2 \<Longrightarrow> \<r>END \<Longrightarrow> A\<^sub>3 \<Longrightarrow> \<r>END \<Longrightarrow> \<dots>\<close> \]
Once any search path encounters a \<^prop>\<open>\<r>END\<close>, the innermost frame is closed and the sequent of the
search path is returned with dropping all other branches in the frame.
The mechanism checks whether all \<^prop>\<open>\<r>BEGIN\<close> and \<^prop>\<open>\<r>END\<close> are paired.

Any global cut cuts all and only all search branches in the innermost frame to which the cut
belongs. \<^prop>\<open>\<r>Success\<close> is prohibited in the nested scope because we do not know how to process
the remain antecedents after the \<^prop>\<open>\<r>Success\<close> and how to return them into the outer scope.
\<close>

consts \<A>frame :: action

abbreviation \<r>Call :: \<open>bool \<Rightarrow> bool\<close> ("\<r>CALL _" [9] 8)
  where \<open>\<r>Call P \<equiv> P @action \<A>frame\<close>
  \<comment> \<open>Call the antecedent \<^prop>\<open>P\<close> in a frame\<close>

lemma \<r>BEGIN_I: \<open>\<r>BEGIN\<close> unfolding \<r>BEGIN_def ..
lemma \<r>END_I: \<open>\<r>END\<close> unfolding \<r>END_def ..

ML_file \<open>library/nested.ML\<close>

\<phi>reasoner_ML \<r>BEGIN 1000 (\<open>\<r>BEGIN\<close>) = \<open>PLPR_Nested_Reasoning.enter_scope\<close>
\<phi>reasoner_ML \<r>END 1000 (\<open>\<r>END\<close>) = \<open>PLPR_Nested_Reasoning.exit_scope\<close>
\<phi>reasoner_ML \<r>Call 1000 (\<open>\<r>CALL _\<close>) = \<open>PLPR_Nested_Reasoning.call\<close>


subsection \<open>Pruning\<close>

text \<open>At a reasoning state \<open>A\<close>, multiple search branches may be emitted parallel to
find a solution of the antecedent.
A branch may find the solution while other branches from \<open>A\<close> still remain in the search history.
Then the reasoning in DFS manner keeps to solve next antecedent \<open>B\<close> and we assume \<open>B\<close> fails.
The reasoning then backtrack, and redo the search of \<open>A\<close> on remaining branches of \<open>A\<close>.
It is not reasonable because the reasoning is redoing a solved problem on \<open>A\<close>.
To address this, a solution is to prune branches of \<open>A\<close> after \<open>A\<close> succeeds.

In this section we introduce \<open>subgoal\<close> mechanism achieving the pruning.
Each antecedent \<open>A\<close> is tagged with a goal context \<open>G\<close>, as \<open>\<open>A @GOAL G\<close>\<close>.
A reasoning rule may check that the goal \<open>G\<close> has not been solved before doing any substantial
computation, e.g.,
\[ \<open>CHK_SUBGOAL G \<Longrightarrow> Computation \<Longrightarrow> (Ant @GOAL G)\<close> \]
Antecedent \<open>CHK_SUBGOAL G\<close> succeeds only when the goal \<open>G\<close> is not marked solved, \<^emph>\<open>or\<close>, the current
  search branch is the thread that marked \<open>G\<close> solved previously.
When a rule succeeds, the rule may mark the goal \<open>G\<close> solved to prune other branches that check \<open>G\<close>.
\[ \<open>Computation \<Longrightarrow> SOLVE_SUBGOAL G \<Longrightarrow> (Ant @GOAL G)\<close> \]
If a goal \<open>G\<close> has been marked solved, any other antecedent \<open>SOLVE_SUBGOAL G\<close> marking \<open>G\<close> again, will
fail, unless the current search branch is the thread that marked \<open>G\<close> solved previously.

A subgoal is represented by an unspecified type which only has a syntactic effect in the reasoning.\<close>

typedecl "subgoal"

consts subgoal_context :: \<open>subgoal \<Rightarrow> action\<close>

abbreviation GOAL_CTXT :: "bool \<Rightarrow> subgoal \<Rightarrow> bool"  ("_  @GOAL _" [26,1000] 26)
  where "(P @GOAL G) \<equiv> (P @action subgoal_context G)"

definition CHK_SUBGOAL :: "subgoal \<Rightarrow> bool" \<comment> \<open>Check whether the goal is solved\<close>
  where "CHK_SUBGOAL X \<longleftrightarrow> True"
definition SOLVE_SUBGOAL :: "subgoal \<Rightarrow> bool"
  where "SOLVE_SUBGOAL X \<longleftrightarrow> True"

text \<open>Subgoals are hierarchical, having the unique top-most goal named \<open>\<open>TOP_GOAL\<close>\<close>.
New goal contexts are obtained by antecedent \<open>\<open>SUBGOAL G ?G'\<close>\<close> which assigns a new subgoal
under an unsolved \<open>G\<close> to output variable \<open>?G'\<close>.
The reasoning raises an error if \<open>?G'\<close> is not a schematic variable.

\<open>\<open>SOLVE_SUBGOAL G\<close>\<close> marks the goal \<open>G\<close> and all its subgoals solved.
The \<open>TOP_GOAL\<close> can never be solved.\<close>

consts TOP_GOAL :: "subgoal"

definition SUBGOAL :: "subgoal \<Rightarrow> subgoal \<Rightarrow> bool" where "SUBGOAL ROOT NEW_GOAL = True"


subsubsection \<open>Implementation of the Subgoal Reasoners\<close>

lemma SUBGOAL_I[iff]: "SUBGOAL ROOT NEWGOAL" unfolding SUBGOAL_def ..
lemma CHK_SUBGOAL_I[iff]: "CHK_SUBGOAL X" unfolding CHK_SUBGOAL_def ..
lemma SOLVE_SUBGOAL_I[iff]: "SOLVE_SUBGOAL X" unfolding SOLVE_SUBGOAL_def ..

ML_file \<open>library/Subgoal_Env.ML\<close>

\<phi>reasoner_ML SUBGOAL 2000 (\<open>SUBGOAL ?ROOT ?NEWGOAL\<close>) = \<open>Subgoal_Env.subgoal\<close>
\<phi>reasoner_ML CHK_SUBGOAL 2000 (\<open>CHK_SUBGOAL ?GOAL\<close>) = \<open>Subgoal_Env.chk_subgoal\<close>
\<phi>reasoner_ML SOLVE_SUBGOAL 9900 (\<open>SOLVE_SUBGOAL ?GOAL\<close>) = \<open>Subgoal_Env.solve_subgoal\<close>

lemma [\<phi>reason 800 for \<open>Try ?S ?P @GOAL ?G\<close>]:
  \<open> P @GOAL G
\<Longrightarrow> Try True P @GOAL G\<close>
  unfolding Try_def .


subsection \<open>Branch\<close>

text \<open>\<open>A ||| B\<close> is an antecedent way to encode search branch.
Compared with the ordinary approach using multiple submissive rules,
short-cut is featured by using subgoal. It tries each antecedent from left to right until
      the first success of solving an antecedent, and none of the remains are attempted.\<close>

definition Branch :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close> (infixr "|||" 3)
  where \<open>Branch A B \<equiv> (\<And>C. (PROP A \<Longrightarrow> C) \<Longrightarrow> (PROP B \<Longrightarrow> C) \<Longrightarrow> C)\<close>

definition Branch_embed :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Branch_embed A B \<equiv> A \<or> B\<close>

lemma atomize_Branch:
  \<open>Branch (Trueprop A) (Trueprop B) \<equiv> Trueprop (A \<or> B)\<close>
  unfolding Branch_def or_def atomize_eq atomize_imp atomize_all .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>Branch (Trueprop A) (Trueprop B) \<equiv> Trueprop (Branch_embed A B)\<close>
  unfolding Branch_embed_def atomize_Branch .


subsubsection \<open>Implementation\<close>

lemma Branch_L:
  \<open> PROP A
\<Longrightarrow> PROP A ||| PROP B\<close>
  unfolding Action_Tag_def Branch_def
proof -
  assume A: \<open>PROP A\<close>
  show \<open>(\<And>C. (PROP A \<Longrightarrow> C) \<Longrightarrow> (PROP B \<Longrightarrow> C) \<Longrightarrow> C)\<close> proof -
    fix C :: "bool"
    assume A': \<open>PROP A \<Longrightarrow> C\<close>
    show \<open>C\<close> using A'[OF A] .
  qed
qed

lemma Branch_R:
  \<open> PROP B
\<Longrightarrow> PROP A ||| PROP B\<close>
  unfolding Action_Tag_def Branch_def
proof -
  assume B: \<open>PROP B\<close>
  show \<open>(\<And>C. (PROP A \<Longrightarrow> C) \<Longrightarrow> (PROP B \<Longrightarrow> C) \<Longrightarrow> C)\<close> proof -
    fix C :: "bool"
    assume B': \<open>PROP B \<Longrightarrow> C\<close>
    show \<open>C\<close> using B'[OF B] .
  qed
qed

declare [[
    \<phi>reason 1000 Branch_L Branch_R for \<open>PROP ?A ||| PROP ?B\<close>,
    \<phi>reason 1000 HOL.disjI1 HOL.disjI2 for \<open>?A \<or> ?B\<close>
]]

definition Orelse_shortcut (infixr "\<or>\<^sub>c\<^sub>u\<^sub>t" 30) where [iff]: \<open>(\<or>\<^sub>c\<^sub>u\<^sub>t) \<equiv> (\<or>)\<close>

text \<open>\<^prop>\<open>A \<or>\<^sub>c\<^sub>u\<^sub>t B\<close>, if \<^prop>\<open>A\<close> succeeds, \<^prop>\<open>B\<close> will not be attempted in any future backtrack.\<close>


lemma Orelse_shortcut_I1:
  \<open> A
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> A \<or>\<^sub>c\<^sub>u\<^sub>t B \<close>
  by simp

lemma Orelse_shortcut_I2:
  \<open> B
\<Longrightarrow> A \<or>\<^sub>c\<^sub>u\<^sub>t B \<close>
  by simp

\<phi>reasoner_ML Orelse_shortcut 1000 (\<open>_ \<or>\<^sub>c\<^sub>u\<^sub>t _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val (G, goal, ctxt) = Subgoal_Env.allocate_subgoal \<^Const>\<open>TOP_GOAL\<close> ctxt
      val [I1,I2] = map (Thm.instantiate (TVars.empty, Vars.make [((("G",0),\<^typ>\<open>subgoal\<close>),G)]))
                        @{thms' Orelse_shortcut_I1 Orelse_shortcut_I2}
      fun tac sequent0 = Seq.make (fn () =>
        let val sequent = I2 RS sequent0
         in if Subgoal_Env.chk_goal goal
            then NONE
            else case Thm.major_prem_of sequent
              of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Orelse_shortcut\<close>, _) $ _ $ _) =>
                      SOME ((ctxt, I1 RS sequent), tac sequent)
               | _ => SOME ((ctxt, sequent), Seq.empty)
        end)
   in SOME ((ctxt, I1 RS sequent), tac sequent)
  end
)\<close>

hide_fact Orelse_shortcut_I1 Orelse_shortcut_I2

subsection \<open>Simplification \& Rewrite\<close>

text \<open>\<open>\<open>\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode] ?result : term\<close>\<close> is generic antecedent for simplifying \<open>term\<close> in different
  \<open>mode\<close>. The \<open>?result\<close> should be an output variable for the result of the simplification.

  We implement a \<open>default\<close> mode where the system simple-set is used to simplify
  \<open>term\<close>. Users may configure their mode and their reasoner using different simple-set.\<close>

definition Simplify :: " mode \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[_] _ :/ _" [10,1000,10] 9)
  where "Simplify setting result origin \<longleftrightarrow> result = origin"

(* definition Do_Simplificatin :: \<open>'a \<Rightarrow> 'a \<Rightarrow> prop\<close>
  where \<open>Do_Simplificatin result origin \<equiv> (result \<equiv> origin)\<close> *)

lemma Simplify_cong[cong]: "A \<equiv> A' \<Longrightarrow> Simplify s x A \<equiv> Simplify s x A' " by simp

lemma Simplify_D: \<open>Simplify m A B \<Longrightarrow> A = B\<close> unfolding Simplify_def .
lemma Simplify_I: \<open>A = B \<Longrightarrow> Simplify m A B\<close> unfolding Simplify_def .

(* lemma Do_Simplification:
  \<open>PROP Do_Simplificatin A B \<Longrightarrow> Simplify s A B\<close>
  unfolding Do_Simplificatin_def Simplify_def atomize_eq . *)

lemma End_Simplification : \<open>Simplify mode A A\<close> unfolding Simplify_def ..
lemma End_Simplification': \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> A = B \<Longrightarrow> Simplify mode A B\<close>
  unfolding Simplify_def Premise_def atomize_eq .

ML_file \<open>library/simplifier.ML\<close>

hide_fact End_Simplification' End_Simplification

subsubsection \<open>Default Simplifier\<close>

abbreviation Default_Simplify :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> _ : _" [1000,10] 9)
  where "Default_Simplify \<equiv> Simplify default"

\<phi>reasoner_ML Default_Simplify 1000 (\<open>Default_Simplify ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty) I)\<close>


(* subsection \<open>Exhaustive Divergence\<close>

ML_file \<open>library/exhaustive_divergen.ML\<close>

definition \<open>Begin_Exhaustive_Divergence \<longleftrightarrow> True\<close>
definition \<open>  End_Exhaustive_Divergence \<longleftrightarrow> True\<close>
definition [iff]: \<open>Stop_Divergence \<longleftrightarrow> True\<close>

lemma Stop_Divergence_I: \<open>Stop_Divergence\<close> unfolding Stop_Divergence_def ..

lemma Begin_Exhaustive_Divergence_I: \<open>Begin_Exhaustive_Divergence\<close>
  unfolding Begin_Exhaustive_Divergence_def ..

lemma End_Exhaustive_Divergence_I: \<open>End_Exhaustive_Divergence\<close>
  unfolding End_Exhaustive_Divergence_def ..

\<phi>reasoner_ML Begin_Exhaustive_Divergence 1000 (\<open>Begin_Exhaustive_Divergence\<close>)
  = \<open>PLPR_Exhaustive_Divergence.begin Seq.of_list\<close>

\<phi>reasoner_ML Stop_Divergence 1000 (\<open>Stop_Divergence\<close>) =
  \<open>apsnd (fn th => @{thm Stop_Divergence_I} RS th) #> PLPR_Exhaustive_Divergence.stop\<close>

\<phi>reasoner_ML End_Exhaustive_Divergence 1000 (\<open>End_Exhaustive_Divergence\<close>)
  = \<open>PLPR_Exhaustive_Divergence.exit\<close>
*)

subsection \<open>Optimal Solution\<close>

text \<open>\<phi>-LPR is priority-driven DFS searching the first reached solution which may not be the optimal
  one for certain measure. The section gives a way to find out the solution of the minimum cost
  among a given set of candidates.
\<close>

definition Optimum_Solution :: \<open>prop \<Rightarrow> prop\<close> where [iff]: \<open>Optimum_Solution P \<equiv> P\<close>
definition [iff]: \<open>Begin_Optimum_Solution \<longleftrightarrow> True\<close>
definition [iff]: \<open>End_Optimum_Solution \<longleftrightarrow> True\<close>


text \<open>Each individual invocation of \<open>Optimum_Solution P\<close>
invokes an individual instance of the optimal solution reasoning.
The reasoning of \<open>P\<close> is proceeded exhaustively meaning exploring all backtracks except local cuts.
\<close>


paragraph \<open>Candidates\<close>

text \<open>The candidates are all search branches diverged from the antecedents marked by \<close>

(* definition \<r>Choice :: \<open>prop \<Rightarrow> prop\<close> ("\<r>CHOICE _" [3] 2) where \<open>\<r>Choice P \<equiv> P\<close>

lemma \<r>Choice_I: \<open> PROP P \<Longrightarrow> PROP \<r>Choice P\<close> unfolding \<r>Choice_def . *)

text \<open>For the antecedents marked by \<open>\<r>Choice\<close>, the mechanism traverses exhaustively all
combinations of their (direct) solvers, but for other not marked antecedents, the strategy is
not changed and is as greedy as the usual behavior --- returning the first-reached solution
and discarding the others.

As an example, in
\<open>Begin_Optimum_Solution \<Longrightarrow> \<r>Choice A \<Longrightarrow> B \<Longrightarrow> \<r>Choice C \<Longrightarrow> End_Optimum_Solution \<Longrightarrow> \<dots>\<close>,
assuming both \<open>A,B,C\<close> have 2 solvers \<open>A\<^sub>1,A\<^sub>2,B\<^sub>1,B\<^sub>2,C\<^sub>1,C\<^sub>2\<close> and assuming \<open>B\<^sub>1\<close> have higher priority
than \<open>B\<^sub>2\<close> and can success, the mechanism traverses 4 combination of the solvers \<open>A\<^sub>1,C\<^sub>1\<close>,
\<open>A\<^sub>1,C\<^sub>2\<close>, \<open>A\<^sub>2,C\<^sub>1\<close>, \<open>A\<^sub>2,C\<^sub>2\<close>, i.e., only exhaustively on \<open>\<r>Choice\<close>-marked antecedents but still
greedy on others.

Note, even marked by \<open>\<r>Choice\<close>, local cuts are still valid and cuts search branches.
Global cut is disabled during the whole reasoning because it kills other search branches.
\<open>\<r>Success\<close> is available and the mechanism ensures it is always the optimal one invokes the \<open>\<r>Success\<close>.
\<close>

paragraph \<open>Cost\<close>

text \<open>The cost is measured by reports from the following antecedents inserted in the user rules.\<close>

definition Incremental_Cost :: \<open>int \<Rightarrow> bool\<close> where [iff]: \<open>Incremental_Cost _ = True\<close>
definition Threshold_Cost   :: \<open>int \<Rightarrow> bool\<close> ("\<t>\<h>\<r>\<e>\<s>\<h>\<o>\<l>\<d>") where [iff]: \<open>Threshold_Cost   _ = True\<close>

text \<open>The final cost of a reasoning process is the sum of all the reported \<open>Incremental_Cost\<close> or
  the maximum \<open>Threshold_Cost\<close>, the one which is larger.

If the cost of two branches are the same, the first reached one is considered better.
\<close>



subsubsection \<open>Implementation\<close>

definition Optimum_Solution_embed :: \<open>bool \<Rightarrow> bool\<close> where \<open>Optimum_Solution_embed P \<equiv> P\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>Optimum_Solution (Trueprop P) \<equiv> Trueprop (Optimum_Solution_embed P)\<close>
  unfolding Optimum_Solution_embed_def Optimum_Solution_def .

lemma Incremental_Cost_I: \<open>Incremental_Cost X\<close> unfolding Incremental_Cost_def ..

lemma Threshold_Cost_I: \<open>Threshold_Cost X\<close> unfolding Threshold_Cost_def ..

lemma Begin_Optimum_Solution_I: \<open>Begin_Optimum_Solution\<close> unfolding Begin_Optimum_Solution_def ..
lemma End_Optimum_Solution_I: \<open>End_Optimum_Solution\<close> unfolding End_Optimum_Solution_def ..

lemma Do_Optimum_Solution:
  \<open> PROP X
\<Longrightarrow> End_Optimum_Solution
\<Longrightarrow> PROP Optimum_Solution X\<close>
  unfolding Optimum_Solution_def .
                                    
ML_file_debug \<open>library/optimum_solution.ML\<close>

\<phi>reasoner_ML Incremental_Cost 1000 (\<open>Incremental_Cost _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ $ (_ $ N) = Thm.major_prem_of sequent
      val (_, n) = HOLogic.dest_number N
      val sequent' = @{thm Incremental_Cost_I} RS sequent
   in Seq.pull (PLPR_Optimum_Solution.report_cost (n,0) (ctxt,sequent'))
   end
)\<close>

\<phi>reasoner_ML Threshold_Cost 1000 (\<open>Threshold_Cost _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ $ (_ $ N) = Thm.major_prem_of sequent
      val (_, n) = HOLogic.dest_number N
      val sequent' = @{thm Threshold_Cost_I} RS sequent
   in Seq.pull (PLPR_Optimum_Solution.report_cost (0,n) (ctxt,sequent'))
  end
)\<close>

\<phi>reasoner_ML Optimum_Solution 1000 (\<open>PROP Optimum_Solution _\<close>) = \<open>
   apsnd (fn th => @{thm Do_Optimum_Solution} RS th)
#> PLPR_Optimum_Solution.internal_start
\<close>

\<phi>reasoner_ML Begin_Optimum_Solution 1000 (\<open>Begin_Optimum_Solution\<close>) = \<open>
   apsnd (fn th => @{thm Begin_Optimum_Solution_I} RS th)
#> PLPR_Optimum_Solution.internal_start
\<close>

\<phi>reasoner_ML End_Optimum_Solution 1000 (\<open>End_Optimum_Solution\<close>) = \<open>
   apsnd (fn th => @{thm End_Optimum_Solution_I} RS th)
#> PLPR_Optimum_Solution.internal_finish
\<close>

(*\<phi>reasoner_ML \<r>Choice 1000 (\<open>PROP \<r>Choice _\<close>) = \<open>fn (ctxt,sequent) =>
  PLPR_Optimum_Solution.choices (ctxt, @{thm \<r>Choice_I} RS sequent)\<close> *)


subsubsection \<open>Derivations\<close>

definition Optimum_Among :: \<open>prop \<Rightarrow> prop\<close> where \<open>Optimum_Among Candidates \<equiv> Candidates\<close>
  \<comment> \<open>We leave it as a syntax merely\<close>

definition Optimum_Among_embed :: \<open>bool \<Rightarrow> bool\<close> where \<open>Optimum_Among_embed X \<equiv> X\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>Optimum_Among (Trueprop P) \<equiv> Trueprop (Optimum_Among_embed P)\<close>
  unfolding Optimum_Among_embed_def Optimum_Among_def .



subsection \<open>Recursion Guard\<close>

definition \<r>Recursion_Guard :: \<open>'a::{} \<Rightarrow> prop \<Rightarrow> prop\<close> ("\<r>RECURSION'_GUARD'(_')/ _" [2,2] 2)
  where [iff]: \<open>(\<r>RECURSION_GUARD(X) (PROP P)) \<equiv> PROP P\<close>

text \<open>\<^prop>\<open>\<r>RECURSION_GUARD(X) (PROP P)\<close> annotates the reasoning of \<^prop>\<open>P\<close> is about goal \<^term>\<open>X\<close>.
It remembers \<^term>\<open>X\<close> and once in the following reasoning the same goal \<^term>\<open>X\<close> occurs again,
it aborts the search branch because an infinite recursion happens.\<close>

definition \<r>Recursion_Guard_embed :: \<open>'a::{} \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>\<r>Recursion_Guard_embed _ P \<equiv> P\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>\<r>Recursion_Guard X (Trueprop P) \<equiv> Trueprop (\<r>Recursion_Guard_embed X P)\<close>
  unfolding \<r>Recursion_Guard_embed_def \<r>Recursion_Guard_def .

subsubsection \<open>Implementation\<close>

definition \<r>Recursion_Residue :: \<open>'a::{} \<Rightarrow> bool\<close>
  where \<open>\<r>Recursion_Residue _ \<equiv> True\<close>

lemma Do_\<r>Recursion_Guard:
  \<open> PROP P
\<Longrightarrow> \<r>Recursion_Residue X
\<Longrightarrow> \<r>RECURSION_GUARD(X) (PROP P) \<close>
  unfolding \<r>Recursion_Guard_def .

lemma [\<phi>reason 1000]:
  \<open>\<r>Recursion_Residue X\<close>
  unfolding \<r>Recursion_Residue_def ..

ML_file \<open>library/recursion_guard.ML\<close>

\<phi>reasoner_ML \<r>Recursion_Guard 1000 (\<open>\<r>RECURSION_GUARD(?X) (PROP ?P)\<close>) = \<open>PLPR_Recursion_Guard.reason\<close>

hide_fact Do_\<r>Recursion_Guard


subsection \<open>Error Message\<close>

\<phi>reasoner_ML TRACING 1200 (\<open>TRACING ?x\<close>) = \<open>fn (ctxt,sequent) =>
  if Context_Position.is_really_visible ctxt
  then let
         val \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>TRACING\<close> $ text)
               = Thm.major_prem_of sequent
         val str = Text_Encoding.decode_text_str ctxt text
         val _ = tracing str
       in Seq.single (ctxt, @{thm TRACING_I} RS sequent)
       end
  else Seq.empty\<close>

\<phi>reasoner_ML WARNING 1200 (\<open>WARNING ?x\<close>) = \<open>fn (ctxt,sequent) =>
  if Context_Position.is_really_visible ctxt
  then let
         val \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>WARNING\<close> $ text)
               = Thm.major_prem_of sequent
         val str = Text_Encoding.decode_text_str ctxt text
         val _ = warning str
       in Seq.single (ctxt, @{thm WARNING_I} RS sequent)
       end
  else Seq.empty\<close>

\<phi>reasoner_ML FAIL 1200 (\<open>FAIL ?x\<close> | \<open>PROP FAIL' ?x'\<close>) = \<open>fn (ctxt,sequent) =>
  if not (Config.get ctxt PLPR_Exhaustive.PLPR_exhaustive_mode) andalso
     Context_Position.is_really_visible ctxt
  then let
         val text = case Thm.major_prem_of sequent
                      of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>FAIL\<close> $ X) => X
                       | \<^const>\<open>FAIL'\<close> $ X => X
         val str = Text_Encoding.decode_text_str ctxt text
         val _ = warning str
       in Seq.empty
       end
  else Seq.empty\<close>

\<phi>reasoner_ML ERROR 1200 (\<open>ERROR ?x\<close> | \<open>PROP ERROR' ?x'\<close>) = \<open>fn (ctxt,sequent) =>
  let
    val text = case Thm.major_prem_of sequent
                 of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>ERROR\<close> $ X) => X
                  | \<^const>\<open>ERROR'\<close> $ X => X
    val str = Text_Encoding.decode_text_str ctxt text
    val _ = error str
  in Seq.empty
  end\<close>

subsection \<open>Protection against Simplification\<close>

text \<open>Forms of antecedents are significant in \<phi>-LPR reasoning.
  For convenience of reasoning, not all tasks are given a specific predicate constant, especially
  when some tasks can be considered as special cases of or sub-tasks of other tasks.

  Simplification is useful when generating reasoning rules automatically.
  However, simplification also easily destroys the implicitly assumed form of the tasks
  which are not assigned with a specific predicate constants.

  An example of specific predicate constant form:
  \<open>Predicate_Constant param1 param2 param3\<close>
  An example of free form not using a specific predicate constant:
  \<open>A \<longrightarrow> B @action reduction_job\<close>
  where this task assumes a form of \<open>_ \<longrightarrow> _ @action reduction_job\<close> implicitly and the form
  will be destroyed by simplification when \<open>A \<equiv> True\<close>.

  In order to protect those free form of the tasks, this subsection provides a mechanism which
  rewrites the tasks to a form using a specific predicate constant before any simplification,
  and rewrites them back after the simplification, so that their forms are not destroyed during
  the simplification.
\<close>

ML_file \<open>library/tools/simplification_protect.ML\<close>

(*
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

\<phi>reasoner_ML Obtain 1200 (\<open>Obtain ?x ?P\<close>) = \<open>
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

\<phi>reasoner_ML DO_OBTAIN 1200 (\<open>PROP DO_OBTAIN\<close>) = \<open>
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

*)

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


(*
subsection \<open>Misc\<close>
 subsubsection \<open>Collect Schematic \& Free \& other terms\<close> \<comment> \<open>Not Stable!\<close>

paragraph \<open>Schematic\<close>

definition \<open>Collect_Schematic (typ::'a itself) sch Term \<equiv> Trueprop True\<close>

text \<open>It collects all schematic variables matching type \<^typ>\<open>'a\<close> in \<^term>\<open>Term\<close>.
  The return is in form \<^term>\<open>Collect_Schematic TYPE('a) (v1, v2, v3) Term\<close>.
  The matching of \<^typ>\<open>'a\<close> is in the usual way, where only schematic variables but no free variables
    are considered as variables that can match something.\<close>

lemma Collect_Schematic_I: \<open>PROP Collect_Schematic TY sch Term\<close>
  unfolding Collect_Schematic_def ..

\<phi>reasoner_ML Collect_Schematic 1200 (\<open>PROP Collect_Schematic TYPE(?'a) ?sch ?Term\<close>) = \<open>
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
*)
(*Others, to be done!*)


end
