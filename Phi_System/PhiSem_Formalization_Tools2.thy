theory PhiSem_Formalization_Tools2
  imports IDE_CP
  keywords ":=" :: quasi_command
begin

section \<open>Tools for Formalizing Instructions\<close>

named_theorems discharging_semantic_debt
  \<open>Theorems that discharges or helps to discharge the debt axioms for semantic formalization.\<close>

subsection \<open>Elementary Constructions for Formalizing Instructions\<close>

definition \<open>\<phi>literal = \<phi>arg\<close>

definition \<phi>M_assert :: \<open>bool \<Rightarrow> unit proc\<close>
  where \<open>\<phi>M_assert P = (\<lambda>s. if P then Return \<phi>V_none s else {Invalid})\<close>

definition \<phi>M_assume :: \<open>bool \<Rightarrow> unit proc\<close>
  where \<open>\<phi>M_assume P = (\<lambda>s. if P then Return \<phi>V_none s else {AssumptionBroken})\<close>

definition \<phi>M_getV_raw :: \<open>(VAL \<Rightarrow> 'v) \<Rightarrow> VAL \<phi>arg \<Rightarrow> ('v \<Rightarrow> 'y proc) \<Rightarrow> 'y proc\<close>
  where \<open>\<phi>M_getV_raw VDT_dest v F = F (VDT_dest (\<phi>arg.dest v))\<close>

definition \<phi>M_getV :: \<open>TY \<Rightarrow> (VAL \<Rightarrow> 'v) \<Rightarrow> VAL \<phi>arg \<Rightarrow> ('v \<Rightarrow> 'y proc) \<Rightarrow> 'y proc\<close>
  where \<open>\<phi>M_getV TY VDT_dest v F =
    (\<phi>M_assert (\<phi>arg.dest v \<in> Well_Type TY) \<ggreater> F (VDT_dest (\<phi>arg.dest v)))\<close>

definition \<phi>M_caseV :: \<open>(VAL \<phi>arg \<Rightarrow> ('vr,'ret) proc') \<Rightarrow> (VAL \<times> 'vr::FIX_ARITY_VALs,'ret) proc'\<close>
  where \<open>\<phi>M_caseV F = (\<lambda>arg. case arg of \<phi>arg (a1,a2) \<Rightarrow> F (\<phi>arg a1) (\<phi>arg a2))\<close>


lemma Valid_Proc_\<phi>M_assert[intro!, \<phi>reason 1200]:
  \<open>Valid_Proc (\<phi>M_assert P)\<close>
  unfolding Valid_Proc_def \<phi>M_assert_def Return_def det_lift_def
  by clarsimp

lemma Valid_Proc_\<phi>M_assume[intro!, \<phi>reason 1200]:
  \<open>Valid_Proc (\<phi>M_assume P)\<close>
  unfolding Valid_Proc_def \<phi>M_assume_def Return_def det_lift_def
  by clarsimp

lemma Valid_Proc_\<phi>M_getV_raw[intro!, \<phi>reason 1200]:
  \<open> (\<And>v. Valid_Proc (F v))
\<Longrightarrow> Valid_Proc (\<phi>M_getV_raw VDF v F)\<close>
  unfolding Valid_Proc_def \<phi>M_getV_raw_def
  by blast

(*to depreciate the above!*)

subsection \<open>Basic Rules\<close>

declare \<phi>SEQ[intro!]

lemma \<phi>M_assert[intro!]:
  \<open>(Inhabited X \<Longrightarrow> P) \<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_assert P \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>M_assert_def
  by (rule \<phi>Inhabited; simp; rule)

lemma semantic_assert_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_assert P \<lbrace> X \<longmapsto> \<lambda>_. X \<rbrace>\<close>
  unfolding \<phi>M_assert_def Premise_def
  by (simp; rule)

lemma \<phi>M_assert_True[simp]:
  \<open>\<phi>M_assert True = Return \<phi>V_none\<close>
  unfolding \<phi>M_assert_def by simp

lemma \<phi>M_assert':
  \<open>P \<Longrightarrow> Q (F args) \<Longrightarrow> Q ((\<phi>M_assert P \<ggreater> F) args)\<close>
  unfolding \<phi>M_assert_def bind_def Return_def det_lift_def by simp

lemma \<phi>M_assume[intro!]:
  \<open>(P \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E) \<Longrightarrow> \<p>\<r>\<o>\<c> (\<phi>M_assume P \<ggreater> F) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>Procedure_def \<phi>M_assume_def bind_def Return_def det_lift_def
  by clarsimp

lemma \<phi>M_assume1[intro!]:
  \<open>\<p>\<r>\<o>\<c> (\<phi>M_assume P) \<lbrace> Void \<longmapsto> Void \<s>\<u>\<b>\<j> P \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>M_assume_def \<phi>Procedure_def bind_def Return_def det_lift_def
  by clarsimp

lemma semantic_assumption_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> P
\<Longrightarrow> \<p>\<r>\<o>\<c> (\<phi>M_assume P) \<lbrace> Void \<longmapsto> Void \<s>\<u>\<b>\<j> P \<rbrace> \<close>
  using \<phi>M_assume1 .

lemma \<phi>M_tail_left:  \<open>\<p>\<r>\<o>\<c> F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_tail_right: \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> \<lambda>v. 1 \<heavy_comma> Y v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_tail_right_right: \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> \<lambda>v. Y v\<heavy_comma> 1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_shrink_left:  \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> 1\<heavy_comma> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp
lemma \<phi>M_shrink_right[intro!]: \<open>\<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<longmapsto> \<lambda>v. 1\<heavy_comma> Y v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close> by simp

lemma \<phi>M_getV_raw[intro!]:
   \<open>(v \<Turnstile> (x \<Ztypecolon> A) \<Longrightarrow> \<p>\<r>\<o>\<c> F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  )
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_getV_raw VDT_dest (\<phi>arg v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (\<phi>arg v) A \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>M_getV_raw_def Premise_def
  by (clarsimp simp add: Val.unfold norm_precond_conj)

declare \<phi>M_getV_raw[where X=1, simplified, intro!]

lemma \<phi>M_getV[intro!]:
   \<open>(v \<Turnstile> (x \<Ztypecolon> A) \<Longrightarrow> <\<phi>expn> v \<in> Well_Type TY)
\<Longrightarrow> (v \<Turnstile> (x \<Ztypecolon> A) \<Longrightarrow> \<p>\<r>\<o>\<c> F (VDT_dest v) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  )
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_getV TY VDT_dest (\<phi>arg v) F \<lbrace> X\<heavy_comma> x \<Ztypecolon> Val (\<phi>arg v) A \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>M_getV_def Premise_def
  by (clarsimp simp add: Val.unfold norm_precond_conj)

declare \<phi>M_getV[where X=1, simplified, intro!]

lemma \<phi>M_caseV[intro!]:
  \<open> \<p>\<r>\<o>\<c> F va vb \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_caseV F (\<phi>V_pair va vb) \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>M_caseV_def \<phi>V_pair_def by simp

(*to depreciate the above!*)


lemma "__Return_rule__":
  \<open> \<p>\<r>\<o>\<c> Return v \<lbrace> X v \<longmapsto> X \<rbrace> \<close>
  unfolding \<phi>Procedure_def det_lift_def Return_def
  by clarsimp

lemma semantic_return_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> (v \<Turnstile> (y \<Ztypecolon> T))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<Turnstile> (y \<Ztypecolon> T)
\<Longrightarrow> \<p>\<r>\<o>\<c> Return (\<phi>arg v) \<lbrace> X \<longmapsto> \<lambda>u. X\<heavy_comma> y \<Ztypecolon> Val u T \<rbrace> \<close>
  unfolding Premise_def \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: Val.unfold)

lemma semantic_literal_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> (v \<Turnstile> (y \<Ztypecolon> T))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<Turnstile> (y \<Ztypecolon> T)
\<Longrightarrow> Void \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Val (\<phi>literal v) T \<close>
  unfolding Premise_def Transformation_def \<phi>literal_def
  by clarsimp

lemma semantic_local_value_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> TY
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_assert (\<phi>arg.dest v \<in> Well_Type TY) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<longmapsto> \<lambda>_. Void \<s>\<u>\<b>\<j> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T) \<rbrace>\<close>
  unfolding \<phi>M_assert_def Premise_def \<phi>SemType_def subset_iff \<phi>Procedure_def det_lift_def Return_def
  by (clarsimp simp add: Val.unfold INTERP_SPEC Satisfaction_def Subjection_expn_set)

lemma semantic_local_value_nochk_\<phi>app:
  \<open> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T) \<close>
  unfolding Transformation_def
  by clarsimp

subsection \<open>Synthesis of Literal Value\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<v>\<a>\<l>[\<phi>literal _] ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ @action synthesis\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<v>\<a>\<l>[\<phi>literal _] ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ @action synthesis\<close>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> \<v>\<a>\<l>[\<phi>literal _]  _ \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ @action synthesis\<close>    (500) ]]

lemma "_synthesis_literal_":
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> const \<Ztypecolon> \<v>\<a>\<l>[\<phi>literal v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> Return (\<phi>literal v) \<lbrace> R \<longmapsto> \<lambda>ret. const \<Ztypecolon> \<v>\<a>\<l>[ret] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<rbrace> @action synthesis\<close>
  unfolding Action_Tag_def Premise_def \<phi>Procedure_def det_lift_def Return_def \<phi>literal_def Transformation_def
  by (clarsimp simp add: Val.unfold INTERP_SPEC_subj Subjection_expn_set INTERP_SPEC, blast)


subsection \<open>Drop & Duplicate Value\<close>

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> Val ?raw ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action action_dup\<close>]:
  \<open>x \<Ztypecolon> Val raw T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Val raw T \<heavy_comma> x \<Ztypecolon> Val raw T @action action_dup\<close>
  unfolding Transformation_def Action_Tag_def
  by (clarsimp simp add: Val.unfold INTERP_SPEC Satisfaction_def Subjection_expn_set)

lemma [\<phi>reason 1200 for \<open>?R \<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action action_drop\<close>]:
  \<open>Void \<heavy_comma> x \<Ztypecolon> Val raw T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Void @action action_drop\<close>
  unfolding Transformation_def Action_Tag_def
  by (clarsimp simp add: Val.unfold)


subsection \<open>Abnormal\<close>

definition throw :: \<open>ABNM \<Rightarrow> 'ret proc\<close>
  where \<open>throw raw = det_lift (Abnormal raw)\<close>

lemma throw_reduce_tail[procedure_simps,simp]:
  \<open>(throw any \<ggreater> f) = throw any\<close>
  unfolding throw_def bind_def det_lift_def by simp

lemma "__throw_rule__"[intro!]:
  \<open> (\<And>a. X a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' a)
\<Longrightarrow> \<p>\<r>\<o>\<c> (throw excep :: 'ret proc) \<lbrace> X excep \<longmapsto> Any \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> X'\<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Transformation_def
  by (clarsimp simp add: INTERP_SPEC; metis)

lemma throw_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> excep
\<Longrightarrow> lambda_abstraction excep XX X
\<Longrightarrow> (\<And>v. Remove_Values (X v) (X' v))
\<Longrightarrow> \<p>\<r>\<o>\<c> throw excep \<lbrace> XX \<longmapsto> 0 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> X' \<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Remove_Values_def Transformation_def
            lambda_abstraction_def
  by (clarsimp simp add: INTERP_SPEC, metis)

definition op_try :: "'ret proc \<Rightarrow> (ABNM \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc"
  where \<open>op_try f g s = \<Union>((\<lambda>y. case y of Success x s' \<Rightarrow> {Success x s'}
                                       | Abnormal v s' \<Rightarrow> g v s'
                                       | AssumptionBroken \<Rightarrow> {AssumptionBroken}
                                       | NonTerm \<Rightarrow> {NonTerm}
                                       | Invalid \<Rightarrow> {Invalid}) ` f s)\<close>

lemma "__op_try__"[intro!]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. E v)
\<Longrightarrow> (\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 )
\<Longrightarrow> \<p>\<r>\<o>\<c> op_try f g \<lbrace> X \<longmapsto> \<lambda>v. Y1 v + Y2 v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2  \<close>
  unfolding op_try_def \<phi>Procedure_def subset_iff
  apply clarsimp subgoal for comp R x s
    apply (cases s; simp; cases x; clarsimp simp add: INTERP_SPEC set_mult_expn ring_distribs)
    subgoal premises prems for a b u v
      using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
      by (metis (no_types, lifting) INTERP_SPEC LooseState_expn(1) prems(3) prems(6) prems(7) prems(8) prems(9) sep_conj_expn)
    subgoal premises prems for a b c d u v2 proof -
      have \<open>Abnormal a b \<in> LooseState (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Success c d \<in> LooseState (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E2 v))\<close>
        using prems(2)[of a, THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_SPEC prems(4) sep_conj_expn)
      note this[simplified]
      then show ?thesis
        by (metis INTERP_SPEC prems(11) sep_conj_expn)
    qed
    subgoal premises prems for a b c d u v proof -
      have \<open>Abnormal a b \<in> LooseState (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Abnormal c d \<in> LooseState (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E2 v))\<close>
        using prems(2)[THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_SPEC prems(4) sep_conj_expn)
      note this[simplified]
      then show ?thesis
        by (simp add: INTERP_SPEC set_mult_expn)
    qed
     apply (smt (z3) INTERP_SPEC LooseState_expn(2) LooseState_expn(3) sep_conj_expn)
    by blast .

definition "Union_the_Same_Or_Arbitrary_when_Var Z X Y \<longleftrightarrow> (\<forall>v. (Z::'v \<Rightarrow> 'a set) v = X v + Y v)"

lemma Union_the_Same_Or_Arbitrary_when_Var__the_Same:
  \<open>Union_the_Same_Or_Arbitrary_when_Var Z Z Z\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by simp

lemma Union_the_Same_Or_Arbitrary_when_Var__Arbitrary:
  \<open>Union_the_Same_Or_Arbitrary_when_Var (\<lambda>v. X v + Y v) X Y\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by blast

\<phi>reasoner_ML Union_the_Same_Or_Arbitrary_when_Var 1200 (\<open>Union_the_Same_Or_Arbitrary_when_Var ?Z ?X ?Y\<close>) = \<open>
fn (_, (ctxt,sequent)) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Union_the_Same_Or_Arbitrary_when_Var\<close>, _)
          $ Z $ _ $ _) = Thm.major_prem_of sequent
  in (ctxt,
        (if is_Var (Term.head_of (Envir.beta_eta_contract Z))
         then @{thm Union_the_Same_Or_Arbitrary_when_Var__Arbitrary}
         else @{thm Union_the_Same_Or_Arbitrary_when_Var__the_Same})
        RS sequent) |> Seq.single
  end
\<close>

proc (nodef) try'':
  assumes F: \<open>\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  assumes G: \<open>(\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE2 )\<close>
  input  X
    output YY
  throws EE2
  \<medium_left_bracket> apply_rule "__op_try__"
    F
    G
  \<medium_right_bracket> .

proc (nodef) try':
  assumes A: \<open>Union_the_Same_Or_Arbitrary_when_Var Z Y1 Y2\<close>
  assumes F: \<open>\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  assumes G: \<open>\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 \<close>
  input  X
    output Z
  throws E2
  \<medium_left_bracket> apply_rule "__op_try__" F G
    unfold A[unfolded Union_the_Same_Or_Arbitrary_when_Var_def, THEN spec, symmetric]
  \<medium_right_bracket>.





end
