chapter \<open>Semantic Formalization \& Specification\<close>

section \<open>Core Monadic Language\<close>

text \<open>Notions of procedure and control flow combinator, which enable formalizing
most of imperative languages.\<close>

section \<open>Specifications on Fictional \<phi>-SL\<close>

text \<open>\begin{remark}[Source \& Target]
As both ToA and view shift constitutes a morphism,
\[ \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close> \]
\[ \<open>X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close> \]
we name the above \<open>X\<close> and \<open>Y\<close> as \<^emph>\<open>source\<close> and \<^emph>\<open>target\<close> respectively.
We also name the \<open>P\<close> \<^emph>\<open>side fact\<close> as it is a side effect generated during the transformation.
\end{remark}\<close>

text \<open>
\begin{remark}[Multi-Term Form (MTF)]
\[ \<open>(x\<^sub>1 \<Ztypecolon> T\<^sub>1) * \<dots> * (x\<^sub>n \<Ztypecolon> T\<^sub>n) \<^bold>s\<^bold>u\<^bold>b\<^bold>j a\<^sub>1 \<dots> a\<^sub>m. P\<close> \]
We call \<open>x\<^sub>i \<Ztypecolon> T\<^sub>i\<close> for \<open>1 \<le> i \<le> n\<close> an \<^emph>\<open>item\<close> in the MTF.
\end{remark}

\begin{remark}[Simple Multi-Term Form]
We call a MTF that does not have any existence and conjunction as \<^emph>\<open>simple MTF\<close>.
\[ \<open>(x\<^sub>1 \<Ztypecolon> T\<^sub>1) * \<dots> * (x\<^sub>n \<Ztypecolon> T\<^sub>n)\<close> \]
\end{remark}
\<close>



chapter \<open>Integrated Deduction Environment for Certified Programming\<close>

theory Chapter_System
  imports "../IDE_CP"
begin

text \<open>The major component for programming in \<phi>-System is
Integrated Deduction Environment for Certified Programming (IDE-CP).
The environment is an extensible framework targeting on the core monadic language.
Programming features like mutable variable or any specific control flow like branches
are added later to the environment as the framework and the core monadic language is extensible.
The chapter focuses on the core designs of the framework, and leaves
pluggable components to the later chapters. 


The programming in \<phi>-System primarily involves 3 (sorts of) Isar commands:
\<^item> A sort of declaration commands like @{command proc} that declare program elements and perhaps
  instantiates a proof context for certifying the element.
\<^item> Commands @{command \<medium_left_bracket>} and @{command \<medium_right_bracket>} that opens and closes respectively a programming context
  \footnote{Here proof context is that in Isabelle, and programming context is invented by IDE-CP.}
  from a proof context or nestedly from another programming context.
\<^item> Command @{command ";;"} that builds a statement in a programming context.

So the overall structure of the source code is very nature as demonstrated in the following example,
\<close>

(*TODO: give an example*)

text \<open>The source code begins with a declaration (@{command proc} here),
opens and closes programming scope using @{command \<medium_left_bracket>} and @{command \<medium_right_bracket>} just like
the bracket \<^verbatim>\<open>{\<close> and \<^verbatim>\<open>}\<close> in usual languages like C,
and separates statements by @{command ";;"} just like \<^verbatim>\<open>;\<close> in C.

\begin{remarks}
Indeed, the statement text is an argument of the command @{command ";;"}.
There is an implicit @{command ";;"} immediately after @{command \<medium_left_bracket>}
so one can write a statement text following @{command \<medium_left_bracket>} and
makes the source more like @{command ";;"} separates statements or ends a statement
instead of the actual fact that @{command ";;"} leads a statement.
\end{remarks}

IDE-CP is based on the theory of Calculus of Programming (CoP).
We introduce CoP briefly here and highly recommend readers to its paper~\cite{CoP}. 
In CoP, programming is identical to deducing a state sequent.
One may view the state sequent a specialized variant of Hoare triple which specifies and
certifies the returning state of evaluating the current program segment of the on-going
construction, starting from an input state specified by a fixed pre-condition.

Centering on deduction of the state sequent, IDE-CP is an environment
equipped with various mechanical assistance including
automated reasoning, syntax and interactive interface, programming synthesis, and others.

A feature of the IDE-CP is that the state sequent of the programming is instantly
displayed in the output window of Isabelle.
Once can move the cursor onto each statement to inspect the computation state after
executing each statement, which resembles a kind of symbolic execution.
The state involves the value of each variable and the state of resources over the abstraction
lifted by the abstraction relations, i.e., an intuitive and intelligible abstraction enabling
users to grasp the value and the state very easily, such as expressions of natural numbers or lists,
instead of any complicated representation of the concrete computation model.

By inserting @{command ";;"} in a statement to split it into two, one can inspect
the computation state after each operation.
Specifically and recalling @{command ";;"} actually leads a statement,
for a statement \<open>C\<^sub>1 \<cdots> C\<^sub>i C\<^sub>i\<^sub>+\<^sub>1 \<cdots> C\<^sub>n ;;\<close> consisting of \<open>n\<close> operations, by inserting @{command ";;"}
between \<open>C\<^sub>i\<close> and \<open>C\<^sub>i\<^sub>+\<^sub>1\<close> (and moving the cursor before the inserted @{command ";;"})
one can inspect the computation state after evaluating operations \<open>C\<^sub>1 \<cdots> C\<^sub>i\<close>.
We highly recommend users to inspect in this way the change of the state step by step in
our examples, which is very good for understanding the mechanism of the system.

Before we dive into more depth of the system, it is good to clarify from the very beginning that
construction in the system actually involves three modes for constructing respectively
\<^item> procedures
\<^item> view shifts
\<^item> transformations of abstraction (\<phi>-BI implications)
which are both identical in the way of construction and therefore we mainly
discuss using the procedure mode as an exemplar.
The differences in detail are presented in later sections \cref{???} for the construction of
the each element.

For view-shift mode and transformation-of-abstraction mode, the programming or in another word
the construction is a forward deduction applying view-shifts or transformations-of-abstraction
stepwisely from the initial view or the initial abstraction to the destined view or abstraction.
The following example demonstrates the such programming approach\<close>

(*TODO: example*)

text \<open>
After such a brief warm-up, now it is the time to start the journey and it begins from
an overview of the whole mechanism.
%we shall explore mechanisms of the system first.
\<close>

section \<open>Overview of the Mechanism\<close>

text \<open>
Mentioned previously, programming in IDE-CP centers on state sequent.
Because the hypotheses of the state sequent is managed by the system internally, we only
consider its proposition excluding the hypotheses (i.e. \<open>P\<close> in \<open>\<Gamma> \<turnstile> P\<close>) in the manual.

The proposition of the state sequent is represented in Heredity Harrop Formula (HHF) and
the deduction is proceeded in a manner of logic programming
--- antecedents of the state sequent tells users what are the jobs required to do next in order,
and premises of each antecedent give us, figuratively speaking,
available \<^emph>\<open>resources\<close> to complete the job.

To illustrate, a job can be either of
\<^item> a transformation of abstraction demanded to be reasoned, denoted by \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close>
\<^item> a proof obligation intended to be solved by users, denoted by \<open>\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n P\<close>
\<^item> a parameter expected to be given by users, denoted by \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m ?x\<close>
\<^item> a specification of a sub-procedure waiting for users programming it,
  denoted by \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>.
More detailed elucidation are given later in \cref{sec:antecedent-jobs}.

\begin{remark}
Sometimes, we name an antecedent as \<^emph>\<open>antecedent job\<close> to emphasize it is a job expecting
resoners or users to do something.
\end{remark}


Readers who are familiar with Isabelle may remember of another sequent that is also in HHF,
the internal representation of a proof state.
\[ \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<close> \]
Antecedents \<open>\<A> \<equiv> {A\<^sub>i}\<^sub>1\<^sub>\<le>\<^sub>i\<^sub>\<le>\<^sub>n\<close> are subgoals for proving conclusion \<open>C\<close>.
Each antecedent \<open>A\<^sub>i \<equiv> (\<And>x\<^sub>i \<dots> x\<^sub>l. P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>m \<Longrightarrow> G\<^sub>i)\<close> may contains locally fixed variables
\<open>{x\<^sub>k}\<^sub>1\<^sub>\<le>\<^sub>k\<^sub>\<le>\<^sub>l\<close> and premises \<open>{P\<^sub>j}\<^sub>1\<^sub>\<le>\<^sub>j\<^sub>\<le>\<^sub>m\<close> which are available during the proof of the proposition \<open>G\<^sub>i\<close>.

Antecedents \<open>\<A>\<close> in a proof state sequent have the identical interpretation with that in
state sequents during programming.
Indeed, one may even view such proof state sequent as a kind of state sequent in
proof context, and the difference between them two is just how we name them
\footnote{We still need the name of state sequent because there is not the sequent of proof state
in programming context.}.

Declaration commands like @{command proc} and others (except those requiring no proof nor programming)
are indeed specialized proof goal statement like command @{command lemma} and @{command theorem},
which initiates a standard Isabelle proof context having for examples the following proof states
corresponding to the three construction mode,
\[ \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?F \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close> \]
\[ \<open>X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close> \]
\[ \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close> \]
where the only subgoal is exact the desired conclusion,
and the subgoal is meantime also an antecedent job
asking users respectively to program some procedure \<open>?F\<close> satisfying the specification,
to deduce the view shift from \<open>X\<close> to \<open>Y\<close>,
and to transform abstraction \<open>X\<close> to \<open>Y\<close> by forward deduction.

Command @{command \<medium_left_bracket>} addresses the above three kinds of antecedent jobs, which opens a programming
context allowing users to program or to deduce the desired construct.
And the programming is deducing a state sequent.

In the programming, the proposition of a state sequent falls in two sorts of forms:
\<^item> \<^emph>\<open>ready state\<close> like \<^prop>\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t state [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n P\<close> representing the previous construction
  is finished, the computation state is now as specified by \<open>P\<close>, and the system is ready for
  the next construction.
\<^item> \<^emph>\<open>pending state\<close> like \<^prop>\<open>\<A> \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g F \<^bold>o\<^bold>n state [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  is deduced after applying a procedure \<^prop>\<open>\<A> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> P \<longmapsto> Q \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close> on the ready state.
  It represents the application of \<open>F\<close> is pending the finish of antecedent jobs \<open>\<A>\<close>.

\begin{remark}
We reuse the notation of \<^emph>\<open>conjunction of aggreagted antecedents\<close> in \cite{CoP} where
a family \<open>\<A> = {A\<^sub>i}\<^sub>1\<^sub>\<le>\<^sub>i\<^sub>\<le>\<^sub>n\<close> of antecedents in \<open>\<A> \<Longrightarrow> C\<close> denotes nested implications of the antecedents
as \<open>A\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<close>.
\end{remark}

Those antecedent jobs have various functions, like a transformation of abstraction or
a demanded annotation or even another sub-procedure waiting for programming
(cf. control flow combinators).
Once all the pending jobs \<open>\<A>\<close> are finished, meaning state sequent
\<^prop>\<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g F \<^bold>o\<^bold>n state [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close> is deduced, the system accepts the procedure \<open>F\<close>
and deduces the next state sequent in ready form \<^prop>\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t state' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q\<close>.
The \<open>state'\<close> denotes the resulted state of evaluating procedure \<open>F\<close>.

The programming is then essentially a loop of switching between the ready state and the pending
state, where users apply a procedure on a ready state and
finishes the antecedent jobs on the pending state.

At last, @{command \<medium_right_bracket>} closes the programming context, and obtains the resulted
specification theorem for the procedure or the view shift or the transformation.
Then using the theorem, it solves the antecedent which the corresponding @{command \<medium_left_bracket>} targets.

This is the overview of the deductive programming in the logic programming manner.
Next we will dive into specific usages of each command and and each antecedent jobs.
\<close>

section \<open>Overall Structure of Programs\<close>

subsection \<open>Declarative Commands\<close>

subsubsection \<open>Procedure\<close>

subsubsection \<open>Transformation of Abstraction (ToA) \& View Shift\<close>

text \<open>Because their roles are in purely theoretical level serving for proofs and deductions,
instead of any specific program element or pragmatic usage,
therefore we do not involve a specialized command to declare them.
We use standard goal statement commands in Isar directly,
like @{command lemma} and @{command theorem}, where the desired transformation or the view shift
is given in the goal statement directly together with any assumptions as antecedents.\<close>

lemma example:
  assumes A: \<open>x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P\<close>
    and   B: \<open>y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s z \<Ztypecolon> Z \<^bold>a\<^bold>n\<^bold>d Q\<close>
  shows \<open>x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s z \<Ztypecolon> Z \<^bold>a\<^bold>n\<^bold>d P \<and> Q\<close>
  \<medium_left_bracket> A B \<medium_right_bracket>. .

text \<open>Recalling the sequent of the Isar proof state
\<open>x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s z \<Ztypecolon> Z \<^bold>a\<^bold>n\<^bold>d P \<and> Q \<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s z \<Ztypecolon> Z \<^bold>a\<^bold>n\<^bold>d P \<and> Q\<close>
where the only sub-goal is also an antecedent, the sub-goal as an antecedent is opened by
@{command \<medium_left_bracket>} by which we enter the programming mode where we can deduce the transformation
forwardly and stepwisely by applying the transformation \<open>A\<close> first and then \<open>B\<close>.
\<close>
(*Explain \<medium_right_bracket>. and \<medium_right_bracket> and the last . after \<medium_right_bracket>.*)

subsection \<open>Commands Opening and Closing Programming Context\<close>

subsection \<open>The Command Writing Statements\<close>

section \<open>Antecedent Jobs for User Input\<close>

text \<open>Antecedent jobs can be classified in two sorts
\<^item> programming job for user input
\<^item> reasoning job for a specific problem, invoking the related reasoning process\<close>

text \<open>The section introduces the first sort that for user input, and leaves that about
reasoning to \cref{sec:reasoning}.\<close>

subsection \<open>Parameter\<close>

subsection \<open>Rule as an Argument\<close>

subsection \<open>Label of Text\<close>



section \<open>Applying Procedures \& Other Constructs\<close>

paragraph \<open>Procedure\<close>

paragraph \<open>View Shift\<close>

paragraph \<open>Transformation of Abstraction\<close>

paragraph \<open>Meta Operation\<close>
text \<open>is a bundle of operations \<close>

subsubsection \<open>Extend by User Specified Application Method\<close>

section \<open>Program Synthesis\<close>

section \<open>Reasoning \label{sec:reasoning}\<close>


section \<open>Access Value or Variable\<close>

(*Notice*)
text \<open>Internal representation of the values and their names are hidden by default during the
  programming, but you can turn on @{attribute \<phi>display_value_internal_name} to display them.\<close>

text \<open>By default, remaining values in the previous statement will be removed in the successive
  statement. You can turn off @{attribute \<phi>statement_clean_values} to disable this behavior.\<close>


(*Unsorted*)

subsection \<open>Options enabling Expert Display\<close>

text \<open>
\<^descr> @{attribute \<phi>display_value_internal_name} enables the display of internal names of values.
    By turning on this option, values will be displayed as \<^term>\<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[internal] T\<close>
    by contrast to the default display \<^term>\<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close>.
    This \<^term>\<open>internal\<close> is the internal semantic representation of value.
\<^descr> \<phi>display_brk_frame displays the internal and technical separation items for breaking frame.
\<close>

end
