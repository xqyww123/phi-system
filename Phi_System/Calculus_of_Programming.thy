section \<open>Implementation of CoP\<close>

theory Calculus_of_Programming
  imports Spec_Framework
begin

named_theorems \<phi>programming_simps \<open>Simplification rules used in the deductive programming\<close>

subsection \<open>Implementing CoP Sequent\<close>

text \<open>CoP sequent \<open>P | S |- Q\<close> for \<open>S = (C\<^sub>1,v\<^sub>1); \<cdots> ; (C\<^sub>n,v\<^sub>n)\<close> is implemented as
\begin{align*}
& \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s\<^sub>0 [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n P\<close>, \\
& \<open>CodeBlock s\<^sub>0 s\<^sub>1 C\<^sub>1 v\<^sub>1,\<close>         \\
&     \qquad \<open>\<cdots>\<close>                 \\
& \<open>CodeBlock s\<^sub>i\<^sub>-\<^sub>1 s\<^sub>i C\<^sub>i v\<^sub>i,\<close>       \\
&     \qquad \<open>\<cdots>\<close>                 \\
& \<open>CodeBlock s\<^sub>n\<^sub>-\<^sub>1 s\<^sub>n C\<^sub>n v\<^sub>n\<close>        \\
\<open>\<turnstile>\<close> \;&\; \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s\<^sub>n [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q\<close>
\end{align*}
where \<open>s\<^sub>0\<close> denotes the initial state before execution and \<open>s\<^sub>i, v\<^sub>i\<close> denote
respectively the intermediate state after executing procedure \<open>C\<^sub>i\<close> and
the return value of \<open>C\<^sub>i\<close>.
Sequence \<open>{s\<^sub>i}\<^sub>n\<close> therefore links execution of each procedure.
\<open>R\<close> is the frame variable.

[C]-modality \<open>[C]{Q}{E}\<close> is implemented by \<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g C \<^bold>o\<^bold>n s\<^sub>n [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>.

\<close>

text \<open>
In addition, besides programming of procedures,
the system is extended to deduce view shift and transformation of abstraction by programming.

The programming deduction of view shift is also realized using similar structures
(\<open>CurrentConstruction\<close>). Thus we reuse the infrastructures and
give two modes \<open>programming_mode\<close> and \<open>view_shift_mode\<close> to differentiate the two modes.
\<close>

consts programming_mode :: mode
       view_shift_mode  :: mode

context \<phi>spec begin

definition CurrentConstruction :: " mode
                        \<Rightarrow> ('RES_N \<Rightarrow> 'RES)
                        \<Rightarrow> ('FIC_N,'FIC) assn
                        \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> bool "
  where "CurrentConstruction mode s R S \<longleftrightarrow> s \<in> (INTERP_SPEC (R * S))"

abbreviation Programming_CurrentConstruction ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_]/ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _" [1000,1000,11] 10)
  where \<open>Programming_CurrentConstruction \<equiv> CurrentConstruction programming_mode\<close>

abbreviation View_Shift_CurrentConstruction ("\<^bold>v\<^bold>i\<^bold>e\<^bold>w _ [_]/ \<^bold>i\<^bold>s _" [1000,1000,11] 10)
  where \<open>View_Shift_CurrentConstruction \<equiv> CurrentConstruction view_shift_mode\<close>

definition PendingConstruction :: " ('ret,'ex,'RES_N,'RES) proc
                        \<Rightarrow> ('RES_N \<Rightarrow> 'RES)
                        \<Rightarrow> ('FIC_N,'FIC) assn
                        \<Rightarrow> ('ret sem_value \<Rightarrow> ('FIC_N,'FIC) assn)
                        \<Rightarrow> ('ex sem_value \<Rightarrow> ('FIC_N,'FIC) assn)
                        \<Rightarrow> bool "
    ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ [_]/ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _/ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _" [1000,1000,1000,11,11] 10)
    where "PendingConstruction f s R S E \<longleftrightarrow> f s \<subseteq> \<S> (\<lambda>ret. INTERP_SPEC (R * S ret)) (\<lambda>ex. INTERP_SPEC (R * E ex))"

definition \<open>CodeBlock s s' f ret \<longleftrightarrow> Success ret s' \<in> f s\<close>

lemma CurrentConstruction_D: "CurrentConstruction mode s H T \<Longrightarrow> Inhabited T"
  unfolding CurrentConstruction_def Inhabited_def by (clarsimp simp add: \<phi>expns; blast)

end


subsection \<open>Forward Declaration of Reasoner\<close>

text \<open>Before we enter any deep discussion, a \<phi>-LPR reasoner tag for
  Transformation of State Abstraction (ToSA) is required to be declared first.
  Remarked as \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA\<close> or \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA\<close>,
  it annotates the Transformation of Abstraction (ToA) is about (fictional)
  computation state.

  Particularly, reasoner for it
  \<^enum> handles MTF and particularly its leading existential quantification and conjunction
  \<^enum> regards separated \<phi>-types independently and invokes ToA reasoning for each
    destined \<phi>-type. This behavior can be overrode.
\<close>

consts ToSA' :: \<open>bool \<comment> \<open>whether to transform \<phi>-types\<close> \<Rightarrow> mode\<close>

abbreviation \<open>ToSA \<equiv> ToSA' True\<close>

text \<open>The boolean argument indicates whether to attempt transformation of \<phi>-types or keep them
unchanged.

\<^item> In \<open>X\<^sub>1 * \<cdots> * X\<^sub>n \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<^sub>1 * \<cdots> * Y\<^sub>m \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' True\<close>,
  for every desired \<phi>-Type \<^term>\<open>Y\<^sub>i\<close> to be obtained, the reasoner
  tries to for each source \<phi>-Type \<^term>\<open>X\<^sub>j\<close> find a way to cast some several \<^term>\<open>X\<^sub>j\<close> to the
  desired \<^term>\<open>Y\<^sub>i\<close>, by reasoning some rule like \<open>X\<^sub>j * \<cdots> * X\<^sub>j\<^sub>' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<^sub>i\<close>.

\<^item> By contrast, in \<open>X\<^sub>1 * \<cdots> * X\<^sub>n \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<^sub>1 * \<cdots> * Y\<^sub>m \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' False\<close>,
  the reasoner does not reason the conversion between different \<phi>-Types, that is,
  the reasoning success only if for every desired \<phi>-Type \<^term>\<open>Y\<^sub>i\<close> there is another
  \<^term>\<open>X\<^sub>j\<close> that unifies \<^term>\<open>Y\<^sub>i\<close>.
\<close>

lemma (in \<phi>spec)
  [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> ?X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode\<close>]:
  \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode\<close>
  unfolding Action_Tag_def using \<phi>view_refl .


subsection \<open>Rules for Constructing Programs\<close>

context \<phi>spec begin

subsubsection \<open>Construct Procedure\<close>

lemma \<phi>apply_proc:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow>(\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E)"
  unfolding \<phi>Procedure_def CurrentConstruction_def PendingConstruction_def bind_def by (auto 0 5)

lemma
  \<open> (\<exists>s' x. CodeBlock s  s'  f x \<and> CodeBlock s' s'' (g x) y)
\<longleftrightarrow> CodeBlock s  s'' (f \<bind> g) y\<close>
  unfolding CodeBlock_def bind_def
  apply (rule; clarsimp)
  apply blast
  by (case_tac x; clarsimp; blast)


(*Hint: because 
\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 \<longrightarrow> 
  Invalid \<notin> f s \<and> (\<forall>v s'. Exception v s' \<in> f s \<longrightarrow> s' \<in> INTERP_SPEC (R \<heavy_comma> E v))*)

lemma (in \<phi>empty) \<phi>assemble_proc:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1
\<Longrightarrow> (\<And>s' ret. CodeBlock s s' f ret \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (g ret) \<^bold>o\<^bold>n s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<bind> g) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 + E2\<close>
  for E1 :: \<open>'VAL sem_value \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff CodeBlock_def
  apply clarsimp subgoal for s s'
  by (cases s; simp; cases s'; simp add: split_state_All ring_distribs plus_fun) .

lemma \<phi>accept_proc:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> CodeBlock s s' f ret
\<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T ret\<close>
  unfolding PendingConstruction_def bind_def subset_iff CurrentConstruction_def CodeBlock_def
  by blast

(* lemma \<phi>accept_proc: \<comment> \<open>Depreciated!\<close>
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1
\<Longrightarrow> (\<And>s' ret. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T ret \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (g ret) \<^bold>o\<^bold>n s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<bind> g) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 + E2"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff plus_fun_def
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .*)

lemma \<phi>return_when_unreachable:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>_. T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<ggreater> Return (sem_value undefined)) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>_. T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  for f :: \<open>(unreachable, 'ex, 'RES_N, 'RES) proc\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .

lemma \<phi>return_additional_unit:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<bind> (\<lambda>v. Return (\<phi>V_pair v \<phi>V_none))) \<^bold>o\<^bold>n s [R]
        \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>ret. T (\<phi>V_fst ret)) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def \<phi>V_pair_def
    \<phi>V_fst_def \<phi>V_snd_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .

lemma \<phi>return:
  " \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T'
\<Longrightarrow> T' = T ret
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (Return ret) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s 0"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff
  by simp+

lemma \<phi>reassemble_proc_final:
  "(\<And>s H. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> S \<longmapsto> T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<rbrace>"
  unfolding CurrentConstruction_def PendingConstruction_def \<phi>Procedure_def bind_def split_paired_all
  by blast

lemma "\<phi>__Return_rule__":
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_::unit sem_value. Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def Return_def View_Shift_def subset_iff det_lift_def
  by clarsimp

subsubsection \<open>Construct View Shift\<close>

lemma \<phi>make_view_shift:
  \<open> (\<And>s R. \<^bold>v\<^bold>i\<^bold>e\<^bold>w s [R] \<^bold>i\<^bold>s S \<Longrightarrow> (\<^bold>v\<^bold>i\<^bold>e\<^bold>w s [R] \<^bold>i\<^bold>s S' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P))
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding CurrentConstruction_def View_Shift_def
  by (simp add: INTERP_SPEC_subj Subjection_expn)

subsubsection \<open>Construct Implication\<close>

lemma (in -) "\<phi>make_implication":
  \<open>(\<And>x. x \<in> S \<Longrightarrow> x \<in> (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) \<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)


subsubsection \<open>Cast\<close>

lemma "\<phi>cast":
  "CurrentConstruction mode blk H T \<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> CurrentConstruction mode blk H T'"
  unfolding CurrentConstruction_def Imply_def
  by (simp_all add: split_paired_all \<phi>expns) blast

lemma "\<phi>cast_P":
  "CurrentConstruction mode blk H T \<Longrightarrow> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> (CurrentConstruction mode blk H T') \<and> P"
  unfolding CurrentConstruction_def Imply_def
  by (simp_all add: split_paired_all \<phi>expns) blast

lemma \<phi>cast_pending:
  "PendingConstruction f blk H T E \<Longrightarrow> (\<And>x. T x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T' x \<^bold>a\<^bold>n\<^bold>d P) \<Longrightarrow> PendingConstruction f blk H T' E"
  unfolding PendingConstruction_def Imply_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All) meson

lemma \<phi>cast_pending_E:
  "PendingConstruction f blk H T E \<Longrightarrow> (\<And>x. E x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s E' x \<^bold>a\<^bold>n\<^bold>d P) \<Longrightarrow> PendingConstruction f blk H T E'"
  unfolding PendingConstruction_def Imply_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All) meson

lemma \<phi>apply_view_shift_P:
  "CurrentConstruction mode blk R S \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (CurrentConstruction mode blk R S') \<and> P"
  unfolding CurrentConstruction_def View_Shift_def
  by (simp_all add: split_paired_all \<phi>expns)

lemma \<phi>apply_view_shift:
  "CurrentConstruction mode blk R S \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> CurrentConstruction mode blk R S'"
  unfolding CurrentConstruction_def View_Shift_def
  by (simp_all add: split_paired_all \<phi>expns)

lemma "_\<phi>cast_internal_rule_":
  " CurrentConstruction mode blk H T
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> CurrentConstruction mode blk H T'"
  unfolding CurrentConstruction_def GOAL_CTXT_def Imply_def FOCUS_TAG_def
    Action_Tag_def View_Shift_def
  by blast

lemma "_\<phi>cast_internal_rule_'":
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w T v \<longmapsto> T' v \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E"
  unfolding Imply_def PendingConstruction_def bind_def GOAL_CTXT_def
    Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All)

(*TODO: \<Longrightarrow> (\<And>v. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v)*)
lemma "_\<phi>cast_exception_":
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E'"
  unfolding Imply_def PendingConstruction_def bind_def GOAL_CTXT_def
    View_Shift_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All)


lemma "_\<phi>cast_exception_rule_":
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E'"
  using "_\<phi>cast_exception_" .


lemma (in -) "_\<phi>cast_implication_":
  \<open> x \<in> S
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d Any \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> x \<in> T\<close>
  unfolding Action_Tag_def Imply_def by blast

subsubsection \<open>Misc\<close>

paragraph \<open>Inhabitance\<close>

lemma (in -) Implication_Inhabited_rule:
  \<open>x \<in> S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by blast

lemma CurrentConstruction_Inhabited_rule:
  "CurrentConstruction mode s H T \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  using CurrentConstruction_D by blast

paragraph \<open>Rename\<close>

lemma \<phi>rename_proc: "f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>" by fast

lemma \<phi>rename_proc_with_goal:
  \<open>f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> \<R> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  unfolding GOAL_CTXT_def using \<phi>rename_proc .

paragraph \<open>Fact Store\<close>

lemma [simp]:
  "CurrentConstruction mode s H (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> P"
  unfolding CurrentConstruction_def by (simp_all add: \<phi>expns split_paired_all)

lemma [simp]:
  "(CurrentConstruction mode s H T \<and> B) \<and> C \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> (B \<and> C)"
  by simp

declare (in -) Subjection_expn[\<phi>programming_simps]

lemma (in -) [\<phi>programming_simps]:
  \<open>((s \<in> T) \<and> B) \<and> C \<longleftrightarrow> (s \<in> T) \<and> (B \<and> C)\<close>
  by simp

paragraph \<open>Fixing Existentially Quantified Variable\<close>

lemma \<phi>ExTyp_strip:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (ExSet T)) \<equiv> (\<exists>c. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T c)"
  unfolding CurrentConstruction_def atomize_eq by (simp_all add: \<phi>expns split_paired_all)

paragraph \<open>Introducing Existential Quantification\<close>

lemma introduce_Ex:
  \<open>CurrentConstruction mode blk H (S x) \<Longrightarrow> CurrentConstruction mode blk H (ExSet S)\<close>
  using \<phi>cast[OF _ ExSet_imp_I[OF implies_refl]] .

lemma introduce_Ex_pending:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>v. Q x v) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>v. \<exists>*x. Q x v) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  using \<phi>cast_pending[OF _ ExSet_imp_I[OF implies_refl]] .

lemma introduce_Ex_pending_E:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>v. E x v)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>v. \<exists>*x. E x v)\<close>
  using \<phi>cast_pending_E[OF _ ExSet_imp_I[OF implies_refl]] .


paragraph \<open>Normalizing Conjunction in Precondition\<close>

lemma Subjection_simp_proc_arg:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> = (P \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)"
  (* and Subjection_simp_func_arg[simp]: "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<lbrace> T \<and>\<^sup>s P \<longmapsto> Y \<rbrace> = (P \<longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f' \<lbrace> T \<longmapsto> Y \<rbrace>)" *)
  unfolding \<phi>Procedure_def by (simp add: \<phi>expns) blast

lemmas Subjection_simp_proc_arg_metaeq[unfolded atomize_eq[symmetric]] = Subjection_simp_proc_arg

end

subsection \<open>Representation of Value in Assertions\<close>

definition Val :: \<open>'v sem_value \<Rightarrow> ('v, 'a) \<phi> \<Rightarrow> ('x::one, 'a) \<phi>\<close>
  where \<open>Val val T = (\<lambda>x. 1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j dest_sem_value val \<in> (x \<Ztypecolon> T))\<close>

subsubsection \<open>Syntax\<close>

consts anonymous_val :: \<open>'a sem_value\<close>
  \<comment> \<open>Any anonymous_val will be translated into a unique value during the parsing\<close>

syntax val_syntax :: "logic \<Rightarrow> logic" ("\<^bold>v\<^bold>a\<^bold>l _" [18] 17)

setup \<open>(Sign.add_trrules (let open Ast 
    in [
      Syntax.Parse_Rule (
        Appl [Constant \<^syntax_const>\<open>val_syntax\<close>,
                Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable "x", Variable "T"]],
        Appl [Constant \<^const_syntax>\<open>\<phi>Type\<close>, Variable "x",
                Appl [Constant \<^const_syntax>\<open>Val\<close>, Constant \<^const_name>\<open>anonymous_val\<close>, Variable "T"]])
  ] end))\<close>

ML_file \<open>library/procedure_syntax.ML\<close>



end