chapter \<open>Calculus of Programming\<close>

theory Calculus_of_Programming
  imports Spec_Framework IDE_CP_Reasoning1
begin

section \<open>Implementing CoP Sequent\<close>

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

definition CurrentConstruction :: " mode \<Rightarrow> resource \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> bool "
  where "CurrentConstruction mode s R S \<longleftrightarrow> s \<in> (INTERP_SPEC (R * S))"

abbreviation Programming_CurrentConstruction ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_]/ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _" [1000,1000,11] 10)
  where \<open>Programming_CurrentConstruction \<equiv> CurrentConstruction programming_mode\<close>

abbreviation View_Shift_CurrentConstruction ("\<^bold>v\<^bold>i\<^bold>e\<^bold>w _ [_]/ \<^bold>i\<^bold>s _" [1000,1000,11] 10)
  where \<open>View_Shift_CurrentConstruction \<equiv> CurrentConstruction view_shift_mode\<close>

definition PendingConstruction :: " 'ret::VALs proc
                                  \<Rightarrow> resource
                                  \<Rightarrow> assn
                                  \<Rightarrow> ('ret sem \<Rightarrow> assn)
                                  \<Rightarrow> (ABNM \<Rightarrow> assn)
                                  \<Rightarrow> bool "
    ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ [_]/ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n _/ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _" [1000,1000,1000,11,11] 10)
    where "PendingConstruction f s R S E \<longleftrightarrow> f s \<subseteq> \<S> (\<lambda>ret. INTERP_SPEC (R * S ret)) (\<lambda>ex. INTERP_SPEC (R * E ex))"

definition \<open>CodeBlock s s' f ret \<longleftrightarrow> Success ret s' \<in> f s\<close>

lemma CurrentConstruction_D: "CurrentConstruction mode s H T \<Longrightarrow> Inhabited T"
  unfolding CurrentConstruction_def Inhabited_def by (clarsimp simp add: \<phi>expns; blast)

definition ToA_Construction :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> bool\<close> ("\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n'(_') \<^bold>i\<^bold>s _" [11,11] 10)
  where \<open>ToA_Construction = (\<in>)\<close>


section \<open>Rules for Constructing Programs\<close>

subsection \<open>Construct Procedure\<close>

lemma \<phi>apply_proc:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E 
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

lemma \<phi>assemble_proc:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1
\<Longrightarrow> (\<And>s' ret. CodeBlock s s' f ret \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (g ret) \<^bold>o\<^bold>n s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<bind> g) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 + E2\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff CodeBlock_def
  apply clarsimp subgoal for s s'
  by (cases s; simp; cases s'; simp add: split_state_All ring_distribs plus_fun) .

lemma \<phi>accept_proc:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> CodeBlock s s' f ret
\<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T ret\<close>
  unfolding PendingConstruction_def bind_def subset_iff CurrentConstruction_def CodeBlock_def
  by blast

lemma \<phi>accept_proc_optimize_\<phi>V_none:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (Return \<phi>V_none) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>_. T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
  unfolding PendingConstruction_def bind_def subset_iff CurrentConstruction_def Return_def
            det_lift_def
  by simp
  

(* lemma \<phi>accept_proc: \<comment> \<open>Depreciated!\<close>
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1
\<Longrightarrow> (\<And>s' ret. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T ret \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (g ret) \<^bold>o\<^bold>n s' [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<bind> g) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1 + E2"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff plus_fun_def
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .*)

(*
lemma \<phi>return_when_unreachable:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>_. T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<ggreater> Return (sem undefined)) \<^bold>o\<^bold>n s [R] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>_. T) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  for f :: \<open>unreachable proc\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .
*)
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
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> S \<longmapsto> T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E"
  unfolding CurrentConstruction_def PendingConstruction_def \<phi>Procedure_def bind_def split_paired_all
  by blast

lemma "\<phi>__Return_rule__":
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_::unit sem. Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def Return_def View_Shift_def subset_iff det_lift_def
  by clarsimp


subsection \<open>Construct View Shift\<close>

lemma \<phi>make_view_shift:
  \<open> (\<And>s R. \<^bold>v\<^bold>i\<^bold>e\<^bold>w s [R] \<^bold>i\<^bold>s S \<Longrightarrow> (\<^bold>v\<^bold>i\<^bold>e\<^bold>w s [R] \<^bold>i\<^bold>s S' \<^bold>s\<^bold>u\<^bold>b\<^bold>j P))
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding CurrentConstruction_def View_Shift_def
  by (simp add: INTERP_SPEC_subj Subjection_expn)


subsection \<open>Construct Implication\<close>

lemma (in -) "\<phi>make_implication":
  \<open>(\<And>x. \<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s S \<Longrightarrow> \<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def ToA_Construction_def
  by (simp add: \<phi>expns)


subsection \<open>Cast\<close>

lemma \<phi>apply_view_shift:
  " CurrentConstruction mode blk R S
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w S \<longmapsto> S' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> (CurrentConstruction mode blk R S') \<and> P"
  unfolding CurrentConstruction_def View_Shift_def
  by (simp_all add: split_paired_all \<phi>expns)

lemmas \<phi>apply_implication = \<phi>apply_view_shift[OF _ view_shift_by_implication]

lemma \<phi>apply_view_shift_pending:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w T x \<longmapsto> T' x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)
\<Longrightarrow> PendingConstruction f blk H T' E"
  unfolding PendingConstruction_def View_Shift_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All)

lemma \<phi>apply_view_shift_pending_E:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>x. \<^bold>v\<^bold>i\<^bold>e\<^bold>w E x \<longmapsto> E' x \<^bold>w\<^bold>i\<^bold>t\<^bold>h P)
\<Longrightarrow> PendingConstruction f blk H T E'"
  unfolding PendingConstruction_def View_Shift_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All)

lemmas \<phi>apply_implication_pending =
  \<phi>apply_view_shift_pending[OF _ view_shift_by_implication]

lemmas \<phi>apply_implication_pending_E =
  \<phi>apply_view_shift_pending_E[OF _ view_shift_by_implication]

lemma \<phi>apply_implication_impl:
  \<open> \<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s S
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow>(\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s S') \<and> P\<close>
  unfolding ToA_Construction_def Imply_def by blast

lemma "_\<phi>cast_internal_rule_":
  " CurrentConstruction mode blk H T
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action ToSA
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> CurrentConstruction mode blk H T'"
  unfolding CurrentConstruction_def Action_Tag_def Imply_def FOCUS_TAG_def View_Shift_def
  by blast

lemma "_\<phi>cast_internal_rule_'":
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w T v \<longmapsto> T' v \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any @action ToSA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E"
  unfolding Imply_def PendingConstruction_def bind_def Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All)

(*TODO: \<Longrightarrow> (\<And>v. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v)*)
lemma "_\<phi>cast_exception_":
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v @action ToSA)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E'"
  unfolding Imply_def PendingConstruction_def bind_def View_Shift_def
  by (clarsimp simp add: \<phi>expns LooseStateTy_expn' subset_iff split_state_All)


lemma "_\<phi>cast_exception_rule_":
  " \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> (\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w E v \<longmapsto> E' v @action ToSA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E'"
  using "_\<phi>cast_exception_" .


lemma "_\<phi>cast_implication_":
  \<open> \<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s S
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s T \<^bold>a\<^bold>n\<^bold>d Any @action ToSA
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> \<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s T\<close>
  unfolding ToA_Construction_def Action_Tag_def Imply_def by blast


subsection \<open>Finalization Rewrites\<close>

text \<open>Rules showing the obtained procedure is identical to the desired goal
  in the end of the construction.\<close>

consts procedure_simplification :: mode
named_theorems procedure_simps

declare proc_bind_SKIP[procedure_simps]
  proc_bind_SKIP'[procedure_simps]
  proc_bind_assoc[procedure_simps]
  proc_bind_return_none[procedure_simps]

\<phi>reasoner procedure_equivalent 1200 (\<open>Premise procedure_simplification ?P\<close>)
  = (rule Premise_I; simp only: procedure_simps; fail)

\<phi>reasoner procedure_simplification 1200
    (\<open>?Q = ?P @action procedure_simplification\<close>)
  = ((simp only: procedure_simps)?, rule Conv_Action_Tag_I; fail)

lemma "\<phi>__final_proc_rewrite__":
  \<open> f = f' @action procedure_simplification
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f  \<lbrace> P \<longmapsto> Q \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> P \<longmapsto> Q \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  unfolding Action_Tag_def by simp

lemma "\<phi>__final_proc_rewrite__'":
  \<open> f = f' @action procedure_simplification
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f  \<lbrace> P \<longmapsto> Q \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action A
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> P \<longmapsto> Q \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action A\<close>
  unfolding Action_Tag_def by simp


subsection \<open>Misc\<close>

paragraph \<open>Inhabitance\<close>

lemma ToA_Construction_Inhabited_rule:
  \<open>\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding ToA_Construction_def Inhabited_def by blast

lemma CurrentConstruction_Inhabited_rule:
  "CurrentConstruction mode s H T \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  using CurrentConstruction_D by blast

paragraph \<open>Rename\<close>

lemma \<phi>rename_proc: "f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U \<longmapsto> \<R> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> \<R> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E " by fast

lemma \<phi>rename_proc_with_goal:
  \<open>f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U \<longmapsto> \<R> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action A \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> \<R> \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action A\<close>
  unfolding Action_Tag_def using \<phi>rename_proc .

paragraph \<open>Fact Store\<close>

lemma [simp]:
  "CurrentConstruction mode s H (T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> P"
  unfolding CurrentConstruction_def by (simp_all add: \<phi>expns split_paired_all)

lemma [simp]:
  "(CurrentConstruction mode s H T \<and> B) \<and> C \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> (B \<and> C)"
  by simp

declare Subjection_expn[\<phi>programming_simps]

lemma [\<phi>programming_simps]:
  \<open>((\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s T) \<and> B) \<and> C \<longleftrightarrow> (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(x) \<^bold>i\<^bold>s T) \<and> (B \<and> C)\<close>
  by simp

paragraph \<open>Fixing Existentially Quantified Variable\<close>

lemma \<phi>ExTyp_strip:
  "(CurrentConstruction mode p H (ExSet T)) \<equiv> (\<exists>c. CurrentConstruction mode p H (T c))"
  unfolding CurrentConstruction_def atomize_eq by (simp_all add: \<phi>expns split_paired_all)

lemma \<phi>ExTyp_strip_imp:
  \<open>ToA_Construction s (ExSet T) \<equiv> (\<exists>c. ToA_Construction s (T c))\<close>
  unfolding ToA_Construction_def by (simp add: \<phi>expns)

paragraph \<open>Introducing Existential Quantification\<close>

lemma introduce_Ex:
  \<open>CurrentConstruction mode blk H (S x) \<Longrightarrow> CurrentConstruction mode blk H (ExSet S)\<close>
  using \<phi>apply_implication[OF _ ExSet_imp_I[OF implies_refl], THEN conjunct1] .

lemma introduce_Ex_pending:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>v. Q x v) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (\<lambda>v. \<exists>*x. Q x v) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  using \<phi>apply_implication_pending[OF _ ExSet_imp_I[OF implies_refl]] .

lemma introduce_Ex_pending_E:
  \<open> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>v. E x v)
\<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>v. \<exists>*x. E x v)\<close>
  using \<phi>apply_implication_pending_E[OF _ ExSet_imp_I[OF implies_refl]] .

lemma introduce_Ex_ToA:
  \<open> ToA_Construction s (S x)
\<Longrightarrow> ToA_Construction s (ExSet S) \<close>
  using \<phi>ExTyp_strip_imp by fastforce


paragraph \<open>Return\<close>


lemma \<phi>M_Success[intro!]:
  \<open> v \<in> (y \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return (sem v) \<lbrace> X \<longmapsto> \<lambda>u. X\<heavy_comma> y \<Ztypecolon> Val u T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s Any \<close>
  unfolding \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: \<phi>expns)

declare \<phi>M_Success[where X=1, simplified, intro!]

lemma \<phi>M_Success'[intro!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return vs \<lbrace> X vs \<longmapsto> X \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s Any \<close>
  unfolding Return_def \<phi>Procedure_def det_lift_def by (clarsimp simp add: \<phi>expns)


end