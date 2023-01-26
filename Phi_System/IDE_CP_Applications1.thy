chapter \<open>IDE-CP Functions \& Applications - Part I\<close>

text \<open>In this part, we build simple applications based on IDE-CP directly, without too much
  advanced reasoning processes.\<close>

theory IDE_CP_Applications1
  imports IDE_CP_Core
  keywords "val" :: quasi_command
  abbrevs "<vals>" = "\<^bold>v\<^bold>a\<^bold>l\<^bold>s"
begin

section \<open>Build Elements of Actions\<close>

subsubsection \<open>Actions only for implication only\<close>

consts transformation :: \<open>'a action \<Rightarrow> 'a action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action transformation _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action transformation _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action transformation _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action transformation _\<close>
]]

lemma [\<phi>reason 1010]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action transformation action\<close>
  unfolding Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action transformation action\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Implication Fallback of View Shift\<close>

consts fallback_to_imp :: \<open>'a action \<Rightarrow> 'a action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action fallback_to_imp _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action fallback_to_imp _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action fallback_to_imp _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action fallback_to_imp _\<close>
]]

lemma [\<phi>reason 30]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action fallback_to_imp action\<close>
  unfolding Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 100]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action fallback_to_imp action\<close>
  unfolding Action_Tag_def .


subsubsection \<open>Actions for \<open>\<exists>\<and>\<close>-free MTF\<close>

consts simple_MTF :: \<open>'a action \<Rightarrow> 'a action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action simple_MTF _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action simple_MTF _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action simple_MTF _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action simple_MTF _\<close>
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1010]:
  \<open> (Q \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A)
\<Longrightarrow> X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A\<close>
  unfolding Action_Tag_def Imply_def
  by (simp add: Subjection_expn, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y x \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A)
\<Longrightarrow> ExSet X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ExSet Y \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A\<close>
  unfolding Action_Tag_def Imply_def
  by (simp add: ExSet_expn, blast)

paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> (Q \<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A)
\<Longrightarrow> X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: \<phi>expns, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y x \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A)
\<Longrightarrow> ExSet X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ExSet Y \<^bold>a\<^bold>n\<^bold>d P @action simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

paragraph \<open>Finish\<close>

lemma [\<phi>reason 1000]:
  \<open> XXX @action A
\<Longrightarrow> XXX @action simple_MTF A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for the leading item only\<close>

consts leading_item' :: \<open>'a action \<Rightarrow> 'a action\<close>

abbreviation \<open>leading_item A \<equiv> simple_MTF (leading_item' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action leading_item' _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action leading_item' _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action leading_item' _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action leading_item' _\<close>
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1010]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> R * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * Y \<^bold>a\<^bold>n\<^bold>d P @action leading_item' A\<close>
  unfolding Action_Tag_def
  using implies_left_prod .

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action leading_item' A\<close>
  unfolding Action_Tag_def .

paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> R\<heavy_comma> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R\<heavy_comma> Y \<^bold>a\<^bold>n\<^bold>d P @action leading_item' A\<close>
  unfolding Action_Tag_def
  using \<phi>view_shift_intro_frame .

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action leading_item' A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions of multi-arity\<close>

text \<open>for transformations containing remainder, of form \<open>?R\<heavy_comma> X \<longmapsto> ?R\<heavy_comma> Y\<close>
  so padding Void is required when there is only one item.\<close>

consts multi_arity' :: \<open>'a action \<Rightarrow> 'a action\<close>

abbreviation \<open>multi_arity A \<equiv> simple_MTF (multi_arity' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action multi_arity' _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action multi_arity' _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action multi_arity' _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action multi_arity' _\<close>
]]

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?Y1\<heavy_comma> ?Y2 \<^bold>a\<^bold>n\<^bold>d ?P @action multi_arity' ?A\<close>]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Void\<heavy_comma> Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action multi_arity' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y1\<heavy_comma> ?Y2 \<^bold>a\<^bold>n\<^bold>d ?P @action multi_arity' ?A\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Void\<heavy_comma> Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action multi_arity' A\<close>
  unfolding Action_Tag_def .


subsubsection \<open>Structural\<close>

consts structural :: \<open>'a action \<Rightarrow> 'a action\<close>
consts structural_1_2 :: \<open>'a action \<Rightarrow> 'a action\<close>
consts structural_2_1 :: \<open>'a action \<Rightarrow> 'a action\<close>

text \<open>
\<^descr> \<^const>\<open>structural\<close> structural homomorphism in shape:
  \<open> X \<longmapsto> Y \<Longrightarrow> C(X) \<longmapsto> C(Y) \<close>
  typically used in containers.

\<^descr> \<^const>\<open>structural_1_2\<close> structural homomorphism in shape:
  \<open> X \<longmapsto> Y * Z \<Longrightarrow> C(X) \<longmapsto> C(Y) * C(Z) \<close>

\<^descr> \<^const>\<open>structural_2_1\<close> structural homomorphism in shape:
  \<open> X * Y \<longmapsto> Z \<Longrightarrow> C(X) * C(Y) \<longmapsto> C(Z) \<close>
\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural _\<close>
  and \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_2_1 _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_2_1 _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_2_1 _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_2_1 _\<close>
  and \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_1_2 _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_1_2 _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_1_2 _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action structural_1_2 _\<close>
]]

paragraph \<open>Fallbacks\<close>

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action structural A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action structural_1_2 A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action structural_2_1 A\<close>
  unfolding Action_Tag_def .

section \<open>Basic Applications\<close>

subsection \<open>Key Applications\<close>

lemma assert_\<phi>app:
  \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m Y \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d Any @action ToSA \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<close>
  unfolding Action_Tag_def
  using implies_weaken by blast

lemma transform_by_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Argument_def .

lemma is_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> x \<Ztypecolon> N \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s x' \<Ztypecolon> N" using view_shift_id by force
lemma as_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X' \<Longrightarrow> x \<Ztypecolon> N \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s X' \<Longrightarrow> x \<Ztypecolon> N \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s X'"  by blast 

lemma view_shift_whole_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Argument_def .


subsection \<open>Case Analysis\<close>

consts action_case :: \<open>unit action\<close>

lemma cases_\<phi>app: \<open>PROP Call_Action action_case\<close> ..

declare [[ \<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action action_case\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action action_case\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action action_case\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action action_case\<close>
]]

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB
\<Longrightarrow> B + A \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB \<or> PA @action action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_VS .

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB
\<Longrightarrow> B + A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB \<or> PA @action action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_IMP .


subsection \<open>Construct \& Destruct \<open>\<phi>\<close>-Type\<close>

lemma destruct\<phi>_\<phi>app:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y D: T x
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s D\<close>
  unfolding Simplify_def \<phi>Type_def by (simp add: implies_refl)

lemma construct\<phi>_1_\<phi>app:
  \<open> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y X: T x
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action ToSA
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by simp

lemma construct\<phi>_\<phi>app:
  \<open> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y X: T x
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' * X @action ToSA
\<Longrightarrow> S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S' * (x \<Ztypecolon> T)\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by simp



subsection \<open>Transformation from \& to Identity\<close>

consts to_Identity   :: \<open>unit action\<close>
       from_Identity :: \<open>unit action\<close>

lemma to_Identity_\<phi>app:
  \<open>PROP Call_Action (transformation (leading_item (structural to_Identity)))\<close> ..

lemma from_Identity_\<phi>app:
  \<open>PROP Call_Action (transformation (leading_item (structural from_Identity)))\<close> ..

declare [[ \<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y @action from_Identity\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d _ @action from_Identity\<close>
  and \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y @action to_Identity\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d _ @action to_Identity\<close> ]]


subsection \<open>Duplicate \& Shrink\<close>

consts action_dup    :: \<open>unit action\<close>
       action_shrink :: \<open>unit action\<close>
       action_drop   :: \<open>unit action\<close>

lemma dup_\<phi>app:
  \<open>PROP Call_Action (transformation (leading_item (structural_1_2 action_dup)))\<close> ..

lemma shrink_\<phi>app:
  \<open>PROP Call_Action (transformation (multi_arity (structural_2_1 action_shrink)))\<close> ..

lemma drop_\<phi>app:
  \<open>PROP Call_Action (fallback_to_imp (multi_arity action_drop))\<close> ..

(*subsection \<open>Simplification as an Action\<close>

consts action_simplify :: \<open>unit action\<close>

lemma simplify_\<phi>app:
  \<open>PROP Call_Action (transformation (simple_MTF ))\<close> *)


end