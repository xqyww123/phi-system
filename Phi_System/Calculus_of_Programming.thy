chapter \<open>Calculus of Programming\<close>

theory Calculus_of_Programming
  imports Spec_Framework IDE_CP_Reasoning1
  abbrevs "<state>" = "\<state>"
      and "<results>" = "\<results>"
      and "<in>" = "\<in'>"
      and "<is>" = "\<is>"
begin

section \<open>Implementing CoP Sequent\<close>

text \<open>CoP sequent \<open>P | S |- Q\<close> for \<open>S = (C\<^sub>1,v\<^sub>1); \<cdots> ; (C\<^sub>n,v\<^sub>n)\<close> is implemented as
\begin{align*}
& \<open>\<current> s\<^sub>0 [R] \<results> \<in'> P\<close>, \\
& \<open>Code s\<^sub>0 s\<^sub>1 C\<^sub>1 v\<^sub>1,\<close>         \\
&     \qquad \<open>\<cdots>\<close>                 \\
& \<open>Code s\<^sub>i\<^sub>-\<^sub>1 s\<^sub>i C\<^sub>i v\<^sub>i,\<close>       \\
&     \qquad \<open>\<cdots>\<close>                 \\
& \<open>Code s\<^sub>n\<^sub>-\<^sub>1 s\<^sub>n C\<^sub>n v\<^sub>n\<close>        \\
\<open>\<turnstile>\<close> \;&\; \<open>\<current> s\<^sub>n [R] \<results> \<in'> Q\<close>
\end{align*}
where \<open>s\<^sub>0\<close> denotes the initial state before execution and \<open>s\<^sub>i, v\<^sub>i\<close> denote
respectively the intermediate state after executing procedure \<open>C\<^sub>i\<close> and
the return value of \<open>C\<^sub>i\<close>.
Sequence \<open>{s\<^sub>i}\<^sub>n\<close> therefore links execution of each procedure.
\<open>R\<close> is the frame variable.

[C]-modality \<open>[C]{Q}{E}\<close> is implemented by \<open>\<pending> C \<on> s\<^sub>n [R] \<results> \<in'> Q \<throws> E\<close>.

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
  where "CurrentConstruction mode s R S \<longleftrightarrow> s \<Turnstile> INTERP_SPEC (S * R)"

abbreviation Programming_CurrentConstruction ("(2\<current> _ [_] \<results> \<in'>/ _)" [1000,1000,11] 10)
  where \<open>Programming_CurrentConstruction \<equiv> CurrentConstruction programming_mode\<close>

abbreviation View_Shift_CurrentConstruction ("(2\<view> _ [_] \<is>/ _)" [1000,1000,11] 10)
  where \<open>View_Shift_CurrentConstruction \<equiv> CurrentConstruction view_shift_mode\<close>

consts Programming_CurrentConstruction_syntax :: \<open>assn \<Rightarrow> bool\<close> ("(2\<current> \<state>:/ (\<open>consistent=true\<close>_))" [11] 10)
consts View_Shift_CurrentConstruction_syntax :: \<open>assn \<Rightarrow> bool\<close> ("(2\<current> \<view>:/ _)" [11] 10)

definition PendingConstruction :: " 'ret proc
                                  \<Rightarrow> resource
                                  \<Rightarrow> assn
                                  \<Rightarrow> ('ret \<phi>arg \<Rightarrow> assn)
                                  \<Rightarrow> (ABNM \<Rightarrow> assn)
                                  \<Rightarrow> bool "
    ("\<pending> _ \<on> _ [_]/ \<results> \<in'> _/ \<throws> _" [1000,1000,1000,11,11] 10)
    where "PendingConstruction f s R S E \<longleftrightarrow>
              BI_lift (f s) \<le> LooseState (\<lambda>ret. INTERP_SPEC (S ret * R)) (\<lambda>ex. INTERP_SPEC (E ex * R))"

consts PendingConstruction_syntax :: \<open>'ret proc \<Rightarrow> ('ret \<phi>arg \<Rightarrow> assn) \<Rightarrow> (ABNM \<Rightarrow> assn) \<Rightarrow> bool\<close>
  ("\<pending> \<proc> _/ \<results> \<in'> _/ \<throws> _" [1000,11,11] 10)

translations
  "\<current> \<state>: S" <= "CONST Programming_CurrentConstruction s R S"
  "\<current> \<view>: S" <= "CONST View_Shift_CurrentConstruction s R S"
  "\<pending> \<proc> f \<results> \<in'> S \<throws> E" <= "CONST PendingConstruction f s R S E"

text \<open>The construction state and the pending state carry where the program is, not a
  hypothesis about the program, so neither belongs in a reported proof obligation.
  The patterns must name the real constants: the \<open>\<current> \<state>:\<close> and
  \<open>\<pending> \<proc>\<close> forms above are print-only (note the \<open><=\<close>), and the constants
  they print through occur in no term.\<close>

declare [[\<phi>filter_out_from_obligation_premise \<open>CurrentConstruction mode s R S\<close>
                                                \<open>PendingConstruction f s R S E\<close>]]

definition \<open>Code s s' f ret \<longleftrightarrow> Success ret s' \<in> f s\<close>

lemma CurrentConstruction_D: "CurrentConstruction mode s H T \<Longrightarrow> Satisfiable T"
  unfolding CurrentConstruction_def Satisfiable_def
  by (clarsimp simp add: INTERP_SPEC set_mult_expn, blast)

definition ToA_Construction :: \<open>'a \<Rightarrow> 'a BI \<Rightarrow> bool\<close> ("\<abstraction>'(_') \<is>/ _" [11,11] 10)
  where \<open>ToA_Construction = (\<Turnstile>)\<close>


subsection \<open>Reasoning Configuration\<close>

subsubsection \<open>Simplification\<close>

\<phi>reasoner_ML \<phi>programming_simps (\<open>\<simplify>[programming_mode] _ : _\<close>) =
  \<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
    let val lev = Config.get ctxt Phi_Reasoner.auto_level
     in if lev <= 0
     then SOME ((ctxt, @{thm' Simplify_I} RS sequent), Seq.empty)
     else sequent
        |> PLPR_Simplifier.simplifier (K Seq.empty) (equip_Phi_Programming_Simp lev) {fix_vars=false} ctxt
        |> Seq.map (pair ctxt)
        |> Seq.pull
    end)\<close>

section \<open>Rules for Constructing Programs\<close>

subsection \<open>Construct Procedure\<close>

lemma \<phi>apply_proc:
  "(\<current> blk [R] \<results> \<in'> S)
\<Longrightarrow> \<proc> f \<lbrace> S \<longmapsto> T \<rbrace> \<throws> E
\<Longrightarrow>(\<pending> f \<on> blk [R] \<results> \<in'> T \<throws> E)"
  unfolding \<phi>Procedure_def CurrentConstruction_def PendingConstruction_def bind_def Satisfaction_def
  by (simp add: mult.commute)

lemma
  \<open> (\<exists>s' x. Code s  s'  f x \<and> Code s' s'' (g x) y)
\<longleftrightarrow> Code s  s'' (f \<bind> g) y\<close>
  unfolding Code_def bind_def
  apply (rule; clarsimp)
  apply blast
  by (case_tac x; clarsimp; blast)


(*Hint: because
\<pending> f \<on> s [R] \<results> \<in'> U \<throws> E1 \<longrightarrow>
  Invalid \<notin> f s \<and> (\<forall>v s'. Abnormal v s' \<in> f s \<longrightarrow> s' \<in> INTERP_SPEC (R \<heavy_comma> E v))*)

lemma \<phi>assemble_proc:
  \<open> \<pending> f \<on> s [R] \<results> \<in'> T \<throws> E1
\<Longrightarrow> (\<And>s' ret. Code s s' f ret \<Longrightarrow> \<pending> (g ret) \<on> s' [R] \<results> \<in'> U \<throws> E2)
\<Longrightarrow> \<pending> (f \<bind> g) \<on> s [R] \<results> \<in'> U \<throws> E1 + E2\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def less_eq_BI_iff Code_def
  apply clarsimp subgoal for s s'
  by (cases s; simp; cases s'; simp add: split_comp_All ring_distribs plus_fun) .




lemma \<phi>accept_proc:
  \<open> \<pending> f \<on> s [R] \<results> \<in'> T \<throws> E
\<Longrightarrow> Code s s' f ret
\<Longrightarrow> \<current> s' [R] \<results> \<in'> T ret\<close>
  unfolding PendingConstruction_def bind_def less_eq_BI_iff CurrentConstruction_def Code_def
  by blast

lemma \<phi>accept_proc_optimize_return_v:
  \<open> \<pending> (Return v) \<on> s [R] \<results> \<in'> T \<throws> E
\<Longrightarrow> \<current> s [R] \<results> \<in'> T v\<close>
  unfolding PendingConstruction_def bind_def less_eq_BI_iff CurrentConstruction_def Return_def det_lift_def
  by simp


(* lemma \<phi>accept_proc: \<comment> \<open>Depreciated!\<close>
  " \<pending> f \<on> s [R] \<results> \<in'> T \<throws> E1
\<Longrightarrow> (\<And>s' ret. \<current> s' [R] \<results> \<in'> T ret \<Longrightarrow> \<pending> (g ret) \<on> s' [R] \<results> \<in'> U \<throws> E2)
\<Longrightarrow> \<pending> (f \<bind> g) \<on> s [R] \<results> \<in'> U \<throws> E1 + E2"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def subset_iff plus_fun_def
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .*)

(*
lemma \<phi>return_when_unreachable:
  \<open> \<pending> f \<on> s [R] \<results> \<in'> (\<lambda>_. T) \<throws> E
\<Longrightarrow> \<pending> (f \<then> Return (\<phi>arg undefined)) \<on> s [R] \<results> \<in'> (\<lambda>_. T) \<throws> E\<close>
  for f :: \<open>unreachable proc\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def subset_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .
*)
lemma \<phi>return_additional_unit:
  \<open> \<pending> f \<on> s [R] \<results> \<in'> T \<throws> E
\<Longrightarrow> \<pending> (f \<bind> (\<lambda>v. Return (\<phi>V_pair v \<phi>V_none))) \<on> s [R]
        \<results> \<in'> (\<lambda>ret. T (\<phi>V_fst ret)) \<throws> E\<close>
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def \<phi>V_pair_def
    \<phi>V_fst_def \<phi>V_snd_def det_lift_def less_eq_BI_iff
  apply clarsimp subgoal for s' s'' by (cases s'; simp; cases s''; simp add: ring_distribs; blast) .

lemma \<phi>return:
  " \<current> s [R] \<results> \<in'> T'
\<Longrightarrow> T' = T ret
\<Longrightarrow> \<pending> (Return ret) \<on> s [R] \<results> \<in'> T \<throws> 0"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def Return_def det_lift_def less_eq_BI_iff
  by simp+

lemma \<phi>reassemble_proc_final:
  "(\<And>s H. \<current> s [H] \<results> \<in'> S \<Longrightarrow> \<pending> g \<on> s [H] \<results> \<in'> T \<throws> E)
\<Longrightarrow> \<proc> g \<lbrace> S \<longmapsto> T \<rbrace> \<throws> E"
  unfolding CurrentConstruction_def PendingConstruction_def \<phi>Procedure_def bind_def split_paired_all
  by (simp add: mult.commute)

lemma "\<phi>__Return_rule__":
  \<open> X \<shifts> Y \<with> Any
\<Longrightarrow> \<proc> Return \<phi>V_none \<lbrace> X \<longmapsto> \<lambda>_::unit \<phi>arg. Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def Return_def View_Shift_def less_eq_BI_iff det_lift_def
  by clarsimp

subsection \<open>Construct View Shift\<close>

lemma \<phi>make_view_shift:
  \<open> (\<And>s R. \<view> s [R] \<is> S \<Longrightarrow> (\<view> s [R] \<is> S' \<subj> P))
\<Longrightarrow> S \<shifts> S' \<with> P\<close>
  unfolding CurrentConstruction_def View_Shift_def
  by (simp add: INTERP_SPEC_subj)


subsection \<open>Construct Implication\<close>

lemma "\<phi>make_implication":
  \<open>(\<And>x. \<abstraction>(x) \<is> S \<Longrightarrow> \<abstraction>(x) \<is> T \<subj> P) \<Longrightarrow> S \<transforms> T \<with> P\<close>
  unfolding Transformation_def ToA_Construction_def
  by simp

subsection \<open>Cast\<close>

lemma \<phi>apply_view_shift:
  " CurrentConstruction mode blk R S
\<Longrightarrow> S \<shifts> S' \<with> P
\<Longrightarrow> (CurrentConstruction mode blk R S') \<and> P"
  unfolding CurrentConstruction_def View_Shift_def
  by (simp_all add: split_paired_all)

lemmas \<phi>apply_implication = \<phi>apply_view_shift[OF _ view_shift_by_implication]

lemma \<phi>apply_view_shift_pending:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>x. T x \<shifts> T' x \<with> P)
\<Longrightarrow> PendingConstruction f blk H T' E"
  unfolding PendingConstruction_def View_Shift_def
  by (clarsimp simp add: LooseState_expn' less_eq_BI_iff split_comp_All)

lemma \<phi>apply_view_shift_pending_E:
  " PendingConstruction f blk H T E
\<Longrightarrow> (\<And>x. E x \<shifts> E' x \<with> P)
\<Longrightarrow> PendingConstruction f blk H T E'"
  unfolding PendingConstruction_def View_Shift_def
  by (clarsimp simp add: LooseState_expn' less_eq_BI_iff split_comp_All)

lemmas \<phi>apply_implication_pending =
  \<phi>apply_view_shift_pending[OF _ view_shift_by_implication]

lemmas \<phi>apply_implication_pending_E =
  \<phi>apply_view_shift_pending_E[OF _ view_shift_by_implication]

lemma \<phi>ex_quantify_E:
  \<open> \<pending> f \<on> blk [H] \<results> \<in'> T \<throws> (E ret)
\<Longrightarrow> \<pending> f \<on> blk [H] \<results> \<in'> T \<throws> (\<lambda>e. ExBI (\<lambda>x. E x e))\<close>
  using \<phi>apply_implication_pending_E[OF _ ExBI_transformation_I[OF transformation_refl]] .

lemma \<phi>apply_implication_impl:
  \<open> \<abstraction>(s) \<is> S
\<Longrightarrow> S \<transforms> S' \<with> P
\<Longrightarrow>(\<abstraction>(s) \<is> S') \<and> P\<close>
  unfolding ToA_Construction_def Transformation_def by blast

lemma "_\<phi>cast_internal_rule_":
  " CurrentConstruction mode blk H T
\<Longrightarrow> T \<transforms> T' \<with> Any
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> CurrentConstruction mode blk H T'"
  unfolding Action_Tag_def
  using \<phi>apply_implication by blast


lemma "_\<phi>cast_internal_rule_'":
  " \<pending> f \<on> blk [H] \<results> \<in'> T \<throws> E
\<Longrightarrow> (\<And>v. T v \<transforms> T' v \<with> Any)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> \<pending> f \<on> blk [H] \<results> \<in'> T' \<throws> E"
  unfolding Action_Tag_def
  using \<phi>apply_implication_pending by blast

lemma "_\<phi>cast_exception_":
  " \<pending> f \<on> blk [H] \<results> \<in'> T \<throws> E
\<Longrightarrow> (\<And>v. E v \<transforms> E' v)
\<Longrightarrow> \<pending> f \<on> blk [H] \<results> \<in'> T \<throws> E'"
  unfolding Action_Tag_def
  using \<phi>apply_implication_pending_E by blast

lemma "_\<phi>cast_exception_rule_":
  " \<pending> f \<on> blk [H] \<results> \<in'> T \<throws> E
\<Longrightarrow> (\<And>v. E v \<transforms> E' v)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> \<pending> f \<on> blk [H] \<results> \<in'> T \<throws> E'"
  using "_\<phi>cast_exception_" .

lemma "_\<phi>cast_implication_":
  \<open> \<abstraction>(x) \<is> S
\<Longrightarrow> S \<transforms> T \<with> Any
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> \<abstraction>(x) \<is> T\<close>
  unfolding ToA_Construction_def Action_Tag_def Transformation_def by blast

lemma "_\<phi>cast_proc_return_internal_rule_":
  " \<proc> f \<lbrace> X \<longmapsto> Y \<rbrace> \<throws> E
\<Longrightarrow> (\<And>v. Y v \<transforms> Y' v \<with> Any)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> \<proc> f \<lbrace> X \<longmapsto> Y' \<rbrace> \<throws> E"
  unfolding Action_Tag_def
  using \<phi>CONSEQ view_shift_by_implication view_shift_refl by blast

lemma "_\<phi>cast_proc_exception_internal_rule_":
  " \<proc> f \<lbrace> X \<longmapsto> Y \<rbrace> \<throws> E
\<Longrightarrow> (\<And>e. E e \<transforms> E' e \<with> Any)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> \<proc> f \<lbrace> X \<longmapsto> Y \<rbrace> \<throws> E'"
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

consts procedure_ss :: mode

lemmas [procedure_simps] =
            proc_bind_SKIP proc_bind_SKIP'
            proc_bind_assoc proc_bind_return_none \<phi>V_simps

\<phi>reasoner_ML procedure_equivalence 1200 (\<open>Premise procedure_ss ?P\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) Proc_Monad_SS.get' {fix_vars=false}) o snd\<close>

\<phi>reasoner_ML procedure_ss 1000 (\<open>Simplify procedure_ss ?x ?y\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) Proc_Monad_SS.get' {fix_vars=true}) o snd\<close>

subsection \<open>Misc\<close>

paragraph \<open>Inhabitance\<close>

lemma ToA_Construction_Satisfiable_rule:
  \<open>\<abstraction>(x) \<is> S \<Longrightarrow> Satisfiable S\<close>
  unfolding ToA_Construction_def Satisfiable_def by blast

lemma CurrentConstruction_Satisfiable_rule:
  "CurrentConstruction mode s H T \<Longrightarrow> Satisfiable T"
  using CurrentConstruction_D by blast


paragraph \<open>Fact Store\<close>

lemma [\<phi>programming_simps]:
  "CurrentConstruction mode s H (T \<subj> P) \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> P"
  unfolding CurrentConstruction_def
  by (simp_all add: INTERP_SPEC_subj split_paired_all)

lemma [\<phi>programming_simps]:
  "(CurrentConstruction mode s H T \<and> B) \<and> C \<longleftrightarrow> (CurrentConstruction mode s H T) \<and> (B \<and> C)"
  by simp

lemma [\<phi>programming_simps]:
  \<open>(\<abstraction>(x) \<is> T \<subj> P) \<longleftrightarrow> (\<abstraction>(x) \<is> T) \<and> P\<close>
  unfolding ToA_Construction_def by simp

lemma [\<phi>programming_simps]:
  \<open>((\<abstraction>(x) \<is> T) \<and> B) \<and> C \<longleftrightarrow> (\<abstraction>(x) \<is> T) \<and> (B \<and> C)\<close>
  by simp

paragraph \<open>Fixing Existentially Quantified Variable\<close>

lemma \<phi>ExTyp_strip:
  "(CurrentConstruction mode p H (\<exists>*c. T c)) \<equiv> (\<exists>c. CurrentConstruction mode p H (T c))"
  unfolding CurrentConstruction_def atomize_eq
  by (simp_all add: INTERP_SPEC_ex split_paired_all)

lemma \<phi>ExTyp_strip_imp:
  \<open>ToA_Construction s (\<exists>*c. T c) \<equiv> (\<exists>c. ToA_Construction s (T c))\<close>
  unfolding ToA_Construction_def by simp

paragraph \<open>Introducing Existential Quantification\<close>

lemma introduce_Ex:
  \<open>CurrentConstruction mode blk H (S x) \<Longrightarrow> CurrentConstruction mode blk H (ExBI S)\<close>
  using \<phi>apply_implication[OF _ ExBI_transformation_I[OF transformation_refl], THEN conjunct1] .

lemma introduce_Ex_subj:
  \<open>CurrentConstruction mode blk H (S x \<subj> Q) \<Longrightarrow> CurrentConstruction mode blk H (ExBI S \<subj> Q)\<close>
  by (metis Subjection_True Subjection_cong introduce_Ex)

lemma introduce_Ex_pending:
  \<open> \<pending> f \<on> blk [H] \<results> \<in'> (\<lambda>v. Q x v) \<throws> E
\<Longrightarrow> \<pending> f \<on> blk [H] \<results> \<in'> (\<lambda>v. \<exists>*x. Q x v) \<throws> E\<close>
  using \<phi>apply_implication_pending[OF _ ExBI_transformation_I[OF transformation_refl]] .

lemma introduce_Ex_pending_E:
  \<open> \<pending> f \<on> blk [H] \<results> \<in'> Q \<throws> (\<lambda>v. E x v)
\<Longrightarrow> \<pending> f \<on> blk [H] \<results> \<in'> Q \<throws> (\<lambda>v. \<exists>*x. E x v)\<close>
  using \<phi>apply_implication_pending_E[OF _ ExBI_transformation_I[OF transformation_refl]] .

lemma introduce_Ex_ToA:
  \<open> ToA_Construction s (S x)
\<Longrightarrow> ToA_Construction s (ExBI S) \<close>
  using \<phi>ExTyp_strip_imp by fastforce

lemma introduce_Ex_ToA_subj:
  \<open> ToA_Construction s (S x \<subj> Q)
\<Longrightarrow> ToA_Construction s (ExBI S \<subj> Q) \<close>
  by (metis (full_types) Subjection_Flase Subjection_True introduce_Ex_ToA)

lemma introduce_Ex_ToA_subj_P:
  \<open> ToA_Construction s (X \<subj> S x)
\<Longrightarrow> ToA_Construction s (X \<subj> Ex S) \<close>
  by (metis Subjection_expn ToA_Construction_def)
  


paragraph \<open>Return\<close>


lemma \<phi>M_Success[intro!]: (*deprecated?*)
  \<open> v \<Turnstile> (y \<Ztypecolon> T)
\<Longrightarrow> \<proc> Return (\<phi>arg v) \<lbrace> X \<longmapsto> \<lambda>u. y \<Ztypecolon> Val u T\<heavy_comma> X \<rbrace> \<throws> Any \<close>
  unfolding \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: Val_def \<phi>Type_def less_eq_BI_iff)

lemma \<phi>M_Success_P:
  \<open> v \<Turnstile> (y \<Ztypecolon> T)
\<Longrightarrow> P (\<phi>arg v)
\<Longrightarrow> \<proc> Return (\<phi>arg v) \<lbrace> X \<longmapsto> \<lambda>u. y \<Ztypecolon> Val u T\<heavy_comma> X \<subj> P u \<rbrace> \<throws> Any \<close>
  unfolding \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: Val_def \<phi>Type_def INTERP_SPEC_subj less_eq_BI_iff)

declare \<phi>M_Success[where X=1, simplified, intro!]

lemma \<phi>M_Success'[intro!]:
  \<open> \<proc> Return vs \<lbrace> X vs \<longmapsto> X \<rbrace> \<throws> Any \<close>
  unfolding Return_def \<phi>Procedure_def det_lift_def less_eq_BI_iff by clarsimp

hide_const (open) Code

end