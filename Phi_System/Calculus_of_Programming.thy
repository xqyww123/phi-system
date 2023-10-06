chapter \<open>Calculus of Programming\<close>

theory Calculus_of_Programming
  imports Spec_Framework IDE_CP_Reasoning1
  abbrevs "<state>" = "\<s>\<t>\<a>\<t>\<e>"
      and "<results>" = "\<r>\<e>\<s>\<u>\<l>\<t>\<s>"
      and "<in>" = "\<i>\<n>"
      and "<is>" = "\<i>\<s>"
begin

section \<open>Implementing CoP Sequent\<close>

text \<open>CoP sequent \<open>P | S |- Q\<close> for \<open>S = (C\<^sub>1,v\<^sub>1); \<cdots> ; (C\<^sub>n,v\<^sub>n)\<close> is implemented as
\begin{align*}
& \<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> s\<^sub>0 [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> P\<close>, \\
& \<open>CodeBlock s\<^sub>0 s\<^sub>1 C\<^sub>1 v\<^sub>1,\<close>         \\
&     \qquad \<open>\<cdots>\<close>                 \\
& \<open>CodeBlock s\<^sub>i\<^sub>-\<^sub>1 s\<^sub>i C\<^sub>i v\<^sub>i,\<close>       \\
&     \qquad \<open>\<cdots>\<close>                 \\
& \<open>CodeBlock s\<^sub>n\<^sub>-\<^sub>1 s\<^sub>n C\<^sub>n v\<^sub>n\<close>        \\
\<open>\<turnstile>\<close> \;&\; \<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> s\<^sub>n [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Q\<close>
\end{align*}
where \<open>s\<^sub>0\<close> denotes the initial state before execution and \<open>s\<^sub>i, v\<^sub>i\<close> denote
respectively the intermediate state after executing procedure \<open>C\<^sub>i\<close> and
the return value of \<open>C\<^sub>i\<close>.
Sequence \<open>{s\<^sub>i}\<^sub>n\<close> therefore links execution of each procedure.
\<open>R\<close> is the frame variable.

[C]-modality \<open>[C]{Q}{E}\<close> is implemented by \<open>\<p>\<e>\<n>\<d>\<i>\<n>\<g> C \<o>\<n> s\<^sub>n [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Q \<t>\<h>\<r>\<o>\<w>\<s> E\<close>.

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
  where "CurrentConstruction mode s R S \<longleftrightarrow> s \<Turnstile> INTERP_SPEC (R * S)"

abbreviation Programming_CurrentConstruction ("\<c>\<u>\<r>\<r>\<e>\<n>\<t> _ [_]/ \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> _" [1000,1000,11] 10)
  where \<open>Programming_CurrentConstruction \<equiv> CurrentConstruction programming_mode\<close>

abbreviation View_Shift_CurrentConstruction ("\<v>\<i>\<e>\<w> _ [_]/ \<i>\<s> _" [1000,1000,11] 10)
  where \<open>View_Shift_CurrentConstruction \<equiv> CurrentConstruction view_shift_mode\<close>

consts Programming_CurrentConstruction_syntax :: \<open>assn \<Rightarrow> bool\<close> ("\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<s>\<t>\<a>\<t>\<e>: _" [11] 10)
consts View_Shift_CurrentConstruction_syntax :: \<open>assn \<Rightarrow> bool\<close> ("\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<v>\<i>\<e>\<w>: _" [11] 10)

definition PendingConstruction :: " 'ret proc
                                  \<Rightarrow> resource
                                  \<Rightarrow> assn
                                  \<Rightarrow> ('ret \<phi>arg \<Rightarrow> assn)
                                  \<Rightarrow> (ABNM \<Rightarrow> assn)
                                  \<Rightarrow> bool "
    ("\<p>\<e>\<n>\<d>\<i>\<n>\<g> _ \<o>\<n> _ [_]/ \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> _/ \<t>\<h>\<r>\<o>\<w>\<s> _" [1000,1000,1000,11,11] 10)
    where "PendingConstruction f s R S E \<longleftrightarrow> f s \<subseteq> LooseState (\<lambda>ret. INTERP_SPEC (R * S ret)) (\<lambda>ex. INTERP_SPEC (R * E ex))"

consts PendingConstruction_syntax :: \<open>'ret proc \<Rightarrow> ('ret \<phi>arg \<Rightarrow> assn) \<Rightarrow> (ABNM \<Rightarrow> assn) \<Rightarrow> bool\<close>
  ("\<p>\<e>\<n>\<d>\<i>\<n>\<g> \<p>\<r>\<o>\<c> _/ \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> _/ \<t>\<h>\<r>\<o>\<w>\<s> _" [1000,11,11] 10)

translations
  "\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<s>\<t>\<a>\<t>\<e>: S" <= "CONST Programming_CurrentConstruction s R S"
  "\<c>\<u>\<r>\<r>\<e>\<n>\<t> \<v>\<i>\<e>\<w>: S" <= "CONST View_Shift_CurrentConstruction s R S"
  "\<p>\<e>\<n>\<d>\<i>\<n>\<g> \<p>\<r>\<o>\<c> f \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S \<t>\<h>\<r>\<o>\<w>\<s> E" <= "CONST PendingConstruction f s R S E"

definition \<open>CodeBlock s s' f ret \<longleftrightarrow> Success ret s' \<in> f s\<close>

lemma CurrentConstruction_D: "CurrentConstruction mode s H T \<Longrightarrow> Inhabited T"
  unfolding CurrentConstruction_def Inhabited_def Satisfaction_def
  by (clarsimp simp add: INTERP_SPEC set_mult_expn; blast)

definition ToA_Construction :: \<open>'a \<Rightarrow> 'a BI \<Rightarrow> bool\<close> ("\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>'(_') \<i>\<s> _" [11,11] 10)
  where \<open>ToA_Construction = (\<Turnstile>)\<close>


section \<open>Rules for Constructing Programs\<close>

subsection \<open>Construct Procedure\<close>

lemma \<phi>apply_proc:
  "(\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S)
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> S \<longmapsto> T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow>(\<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E)"
  unfolding \<phi>Procedure_def CurrentConstruction_def PendingConstruction_def bind_def Satisfaction_def
  by (auto 0 5)

lemma
  \<open> (\<exists>s' x. CodeBlock s  s'  f x \<and> CodeBlock s' s'' (g x) y)
\<longleftrightarrow> CodeBlock s  s'' (f \<bind> g) y\<close>
  unfolding CodeBlock_def bind_def
  apply (rule; clarsimp)
  apply blast
  by (case_tac x; clarsimp; blast)


(*Hint: because
\<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> U \<t>\<h>\<r>\<o>\<w>\<s> E1 \<longrightarrow>
  Invalid \<notin> f s \<and> (\<forall>v s'. Abnormal v s' \<in> f s \<longrightarrow> s' \<in> INTERP_SPEC (R \<heavy_comma> E v))*)

lemma \<phi>assemble_proc:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E1
\<Longrightarrow> (\<And>s' ret. CodeBlock s s' f ret \<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (g ret) \<o>\<n> s' [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> U \<t>\<h>\<r>\<o>\<w>\<s> E2)
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (f \<bind> g) \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> U \<t>\<h>\<r>\<o>\<w>\<s> E1 + E2\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff CodeBlock_def
  apply clarsimp subgoal for s s'
  by (cases s; simp; cases s'; simp add: split_comp_All ring_distribs plus_fun) .




lemma \<phi>accept_proc:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> CodeBlock s s' f ret
\<Longrightarrow> \<c>\<u>\<r>\<r>\<e>\<n>\<t> s' [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T ret\<close>
  unfolding PendingConstruction_def bind_def subset_iff CurrentConstruction_def CodeBlock_def Satisfaction_def
  by blast

lemma \<phi>accept_proc_optimize_return_v:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (Return v) \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<c>\<u>\<r>\<r>\<e>\<n>\<t> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T v\<close>
  unfolding PendingConstruction_def bind_def subset_iff CurrentConstruction_def Return_def
            det_lift_def Satisfaction_def
  by simp


(* lemma \<phi>accept_proc: \<comment> \<open>Depreciated!\<close>
  " \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E1
\<Longrightarrow> (\<And>s' ret. \<c>\<u>\<r>\<r>\<e>\<n>\<t> s' [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T ret \<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (g ret) \<o>\<n> s' [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> U \<t>\<h>\<r>\<o>\<w>\<s> E2)
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (f \<bind> g) \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> U \<t>\<h>\<r>\<o>\<w>\<s> E1 + E2"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff plus_fun_def
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .*)

(*
lemma \<phi>return_when_unreachable:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. T) \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (f \<ggreater> Return (\<phi>arg undefined)) \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. T) \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  for f :: \<open>unreachable proc\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .
*)
lemma \<phi>return_additional_unit:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (f \<bind> (\<lambda>v. Return (\<phi>V_pair v \<phi>V_none))) \<o>\<n> s [R]
        \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>ret. T (\<phi>V_fst ret)) \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def \<phi>V_pair_def
    \<phi>V_fst_def \<phi>V_snd_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .

lemma \<phi>return:
  " \<c>\<u>\<r>\<r>\<e>\<n>\<t> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T'
\<Longrightarrow> T' = T ret
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> (Return ret) \<o>\<n> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> 0"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff Satisfaction_def
  by simp+

lemma \<phi>reassemble_proc_final:
  "(\<And>s H. \<c>\<u>\<r>\<r>\<e>\<n>\<t> s [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S \<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> g \<o>\<n> s [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> g \<lbrace> S \<longmapsto> T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E"
  unfolding CurrentConstruction_def PendingConstruction_def \<phi>Procedure_def bind_def split_paired_all Satisfaction_def
  by blast

lemma "\<phi>__Return_rule__":
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> Any
\<Longrightarrow> \<p>\<r>\<o>\<c> Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_::unit \<phi>arg. Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def Return_def View_Shift_def subset_iff det_lift_def Satisfaction_def
  by clarsimp

subsection \<open>Construct View Shift\<close>

lemma \<phi>make_view_shift:
  \<open> (\<And>s R. \<v>\<i>\<e>\<w> s [R] \<i>\<s> S \<Longrightarrow> (\<v>\<i>\<e>\<w> s [R] \<i>\<s> S' \<s>\<u>\<b>\<j> P))
\<Longrightarrow> S \<s>\<h>\<i>\<f>\<t>\<s> S' \<w>\<i>\<t>\<h> P\<close>
  unfolding CurrentConstruction_def View_Shift_def Satisfaction_def
  by (simp add: INTERP_SPEC_subj Subjection_expn_set)


subsection \<open>Construct Implication\<close>

lemma "\<phi>make_implication":
  \<open>(\<And>x. \<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S \<Longrightarrow> \<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T \<s>\<u>\<b>\<j> P) \<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> T \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def ToA_Construction_def
  by simp

subsection \<open>Cast\<close>

lemma \<phi>apply_view_shift:
  " CurrentConstruction mode blk R S
\<Longrightarrow> S \<s>\<h>\<i>\<f>\<t>\<s> S' \<w>\<i>\<t>\<h> P
\<Longrightarrow> (CurrentConstruction mode blk R S') \<and> P"
  unfolding CurrentConstruction_def View_Shift_def Satisfaction_def
  by (simp_all add: split_paired_all)

lemmas \<phi>apply_implication = \<phi>apply_view_shift[OF _ view_shift_by_implication]

lemma \<phi>apply_view_shift_pending:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>x. T x \<s>\<h>\<i>\<f>\<t>\<s> T' x \<w>\<i>\<t>\<h> P)
\<Longrightarrow> PendingConstruction f blk H T' E"
  unfolding PendingConstruction_def View_Shift_def Satisfaction_def
  by (clarsimp simp add: LooseState_expn' subset_iff split_comp_All)

lemma \<phi>apply_view_shift_pending_E:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>x. E x \<s>\<h>\<i>\<f>\<t>\<s> E' x \<w>\<i>\<t>\<h> P)
\<Longrightarrow> PendingConstruction f blk H T E'"
  unfolding PendingConstruction_def View_Shift_def Satisfaction_def
  by (clarsimp simp add: LooseState_expn' subset_iff split_comp_All)

lemmas \<phi>apply_implication_pending =
  \<phi>apply_view_shift_pending[OF _ view_shift_by_implication]

lemmas \<phi>apply_implication_pending_E =
  \<phi>apply_view_shift_pending_E[OF _ view_shift_by_implication]

lemma \<phi>ex_quantify_E:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> (E ret)
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. ExSet (\<lambda>x. E x e))\<close>
  using \<phi>apply_implication_pending_E[OF _ ExSet_transformation_I[OF transformation_refl]] .

lemma \<phi>apply_implication_impl:
  \<open> \<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> S
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P
\<Longrightarrow>(\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> S') \<and> P\<close>
  unfolding ToA_Construction_def Transformation_def by blast

lemma "_\<phi>cast_internal_rule_":
  " CurrentConstruction mode blk H T
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> T' \<w>\<i>\<t>\<h> Any @action NToA
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> CurrentConstruction mode blk H T'"
  unfolding Action_Tag_def
  using \<phi>apply_implication by blast


lemma "_\<phi>cast_internal_rule_'":
  " \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> (\<And>v. T v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> T' v \<w>\<i>\<t>\<h> Any @action NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T' \<t>\<h>\<r>\<o>\<w>\<s> E"
  unfolding Action_Tag_def
  using \<phi>apply_implication_pending by blast

lemma "_\<phi>cast_exception_":
  " \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> (\<And>v. E v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> E' v @action NToA)
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E'"
  unfolding Action_Tag_def
  using \<phi>apply_implication_pending_E by blast

lemma "_\<phi>cast_exception_rule_":
  " \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> (\<And>v. E v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> E' v @action NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> T \<t>\<h>\<r>\<o>\<w>\<s> E'"
  using "_\<phi>cast_exception_" .

lemma "_\<phi>cast_implication_":
  \<open> \<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> T \<w>\<i>\<t>\<h> Any @action NToA
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> \<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T\<close>
  unfolding ToA_Construction_def Action_Tag_def Transformation_def by blast

lemma "_\<phi>cast_proc_return_internal_rule_":
  " \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> (\<And>v. Y v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y' v \<w>\<i>\<t>\<h> Any @action NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E"
  unfolding Action_Tag_def
  using \<phi>CONSEQ view_shift_by_implication view_shift_refl by blast

lemma "_\<phi>cast_proc_exception_internal_rule_":
  " \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> (\<And>e. E e \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> E' e \<w>\<i>\<t>\<h> Any @action NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'"
  unfolding Action_Tag_def
  using \<phi>CONSEQ view_shift_by_implication view_shift_refl by blast


subsection \<open>Finalization Rewrites\<close>

text \<open>Rules showing the obtained procedure is identical to the desired goal
  in the end of the construction.\<close>

ML \<open>structure Proc_Monad_SS = Simpset(
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>procedure_simps\<close>
  val comment = "declare the rules for simplifying procedure monad."
  val attribute = NONE
  val post_merging = I
)\<close>

consts procedure_simplification :: mode

lemmas [procedure_simps] =
            proc_bind_SKIP proc_bind_SKIP'
            proc_bind_assoc proc_bind_return_none \<phi>V_simps

\<phi>reasoner_ML procedure_equivalence 1200 (\<open>Premise procedure_simplification ?P\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) Proc_Monad_SS.get' {fix_vars=true}) o snd\<close>

\<phi>reasoner_ML procedure_simplification 1000 (\<open>Simplify procedure_simplification ?x ?y\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) Proc_Monad_SS.get' {fix_vars=true}) o snd\<close>

subsection \<open>Misc\<close>

paragraph \<open>Inhabitance\<close>

lemma ToA_Construction_Inhabited_rule:
  \<open>\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> S \<Longrightarrow> Inhabited S\<close>
  unfolding ToA_Construction_def Inhabited_def by blast

lemma CurrentConstruction_Inhabited_rule:
  "CurrentConstruction mode s H T \<Longrightarrow> Inhabited T"
  using CurrentConstruction_D by blast


paragraph \<open>Fact Store\<close>

lemma [\<phi>programming_simps]:
  "CurrentConstruction mode s H (T \<s>\<u>\<b>\<j> P) \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> P"
  unfolding CurrentConstruction_def by (simp_all add: INTERP_SPEC_subj split_paired_all)

lemma [\<phi>programming_simps]:
  "(CurrentConstruction mode s H T \<and> B) \<and> C \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> (B \<and> C)"
  by simp

lemma [\<phi>programming_simps]:
  \<open>(\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T \<s>\<u>\<b>\<j> P) \<longleftrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T) \<and> P\<close>
  unfolding ToA_Construction_def by simp

lemma [\<phi>programming_simps]:
  \<open>((\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T) \<and> B) \<and> C \<longleftrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(x) \<i>\<s> T) \<and> (B \<and> C)\<close>
  by simp

paragraph \<open>Fixing Existentially Quantified Variable\<close>

lemma \<phi>ExTyp_strip:
  "(CurrentConstruction mode p H (ExSet T)) \<equiv> (\<exists>c. CurrentConstruction mode p H (T c))"
  unfolding CurrentConstruction_def atomize_eq by (simp_all add: INTERP_SPEC_ex split_paired_all)

lemma \<phi>ExTyp_strip_imp:
  \<open>ToA_Construction s (ExSet T) \<equiv> (\<exists>c. ToA_Construction s (T c))\<close>
  unfolding ToA_Construction_def by simp

paragraph \<open>Introducing Existential Quantification\<close>

lemma introduce_Ex:
  \<open>CurrentConstruction mode blk H (S x) \<Longrightarrow> CurrentConstruction mode blk H (ExSet S)\<close>
  using \<phi>apply_implication[OF _ ExSet_transformation_I[OF transformation_refl], THEN conjunct1] .

lemma introduce_Ex_subj:
  \<open>CurrentConstruction mode blk H (S x \<s>\<u>\<b>\<j> Q) \<Longrightarrow> CurrentConstruction mode blk H (ExSet S \<s>\<u>\<b>\<j> Q)\<close>
  by (metis Subjection_True Subjection_cong introduce_Ex)

lemma introduce_Ex_pending:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>v. Q x v) \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>v. \<exists>*x. Q x v) \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  using \<phi>apply_implication_pending[OF _ ExSet_transformation_I[OF transformation_refl]] .

lemma introduce_Ex_pending_E:
  \<open> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Q \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. E x v)
\<Longrightarrow> \<p>\<e>\<n>\<d>\<i>\<n>\<g> f \<o>\<n> blk [H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Q \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. \<exists>*x. E x v)\<close>
  using \<phi>apply_implication_pending_E[OF _ ExSet_transformation_I[OF transformation_refl]] .

lemma introduce_Ex_ToA:
  \<open> ToA_Construction s (S x)
\<Longrightarrow> ToA_Construction s (ExSet S) \<close>
  using \<phi>ExTyp_strip_imp by fastforce

lemma introduce_Ex_ToA_subj:
  \<open> ToA_Construction s (S x \<s>\<u>\<b>\<j> Q)
\<Longrightarrow> ToA_Construction s (ExSet S \<s>\<u>\<b>\<j> Q) \<close>
  by (metis (full_types) Subjection_Flase Subjection_True introduce_Ex_ToA)

lemma introduce_Ex_ToA_subj_P:
  \<open> ToA_Construction s (X \<s>\<u>\<b>\<j> S x)
\<Longrightarrow> ToA_Construction s (X \<s>\<u>\<b>\<j> Ex S) \<close>
  by (metis Subjection_expn ToA_Construction_def)
  


paragraph \<open>Return\<close>


lemma \<phi>M_Success[intro!]: (*depreciated?*)
  \<open> v \<Turnstile> (y \<Ztypecolon> T)
\<Longrightarrow> \<p>\<r>\<o>\<c> Return (\<phi>arg v) \<lbrace> X \<longmapsto> \<lambda>u. X\<heavy_comma> y \<Ztypecolon> Val u T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> Any \<close>
  unfolding \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: Val_expn)

declare \<phi>M_Success[where X=1, simplified, intro!]

lemma \<phi>M_Success'[intro!]:
  \<open> \<p>\<r>\<o>\<c> Return vs \<lbrace> X vs \<longmapsto> X \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> Any \<close>
  unfolding Return_def \<phi>Procedure_def det_lift_def by clarsimp

end