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

consts \<A>_transformation :: \<open>'a action \<Rightarrow> 'a action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_transformation _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_transformation _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_transformation _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_transformation _\<close>
]]

lemma [\<phi>reason 1010]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1100]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_implication by blast

lemma [\<phi>reason 1100]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s X))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def ToA_Construction_def
  by blast


subsubsection \<open>View Shift\<close>

consts \<A>_view_shift_or_imp :: \<open>'a action \<Rightarrow> 'a action\<close>

lemma [\<phi>reason 1100]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s X))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> (\<^bold>a\<^bold>b\<^bold>s\<^bold>t\<^bold>r\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n(s) \<^bold>i\<^bold>s Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def ToA_Construction_def
  by blast

lemma do_\<A>_view_shift_or_imp_VS:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift by blast

lemma do_\<A>_view_shift_or_imp_VS_degrade:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_implication by blast

declare [[\<phi>reason 1100 do_\<A>_view_shift_or_imp_VS do_\<A>_view_shift_or_imp_VS_degrade
      for \<open>PROP Do_Action (\<A>_view_shift_or_imp ?action)
                (Trueprop (CurrentConstruction ?mode ?s ?H ?X))
                ?Result\<close>]]

hide_fact do_\<A>_view_shift_or_imp_VS do_\<A>_view_shift_or_imp_VS_degrade

subsubsection \<open>Nap, a space for injection\<close>

consts \<A>nap :: \<open>'a action \<Rightarrow> 'a action\<close>

lemma [\<phi>reason 10]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>nap A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for \<open>\<exists>\<and>\<close>-free MTF\<close>

consts \<A>_simple_MTF :: \<open>'a action \<Rightarrow> 'a action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_simple_MTF _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_simple_MTF _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_simple_MTF _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_simple_MTF _\<close>
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1010]:
  \<open> (Q \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Imply_def
  by (simp add: Subjection_expn, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y x \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ExSet Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Imply_def
  by (simp add: ExSet_expn, blast)

paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> (Q \<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: \<phi>expns, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y x \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ExSet Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

paragraph \<open>Finish\<close>

lemma [\<phi>reason 1000]:
  \<open> XXX @action A
\<Longrightarrow> XXX @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for the leading item only\<close>

consts \<A>_leading_item' :: \<open>'a action \<Rightarrow> 'a action\<close>

abbreviation \<open>\<A>_leading_item A \<equiv> \<A>_simple_MTF (\<A>_leading_item' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_leading_item' _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_leading_item' _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_leading_item' _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_leading_item' _\<close>
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1010]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> R * X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R * Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using implies_left_prod .

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> R\<heavy_comma> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R\<heavy_comma> Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using \<phi>view_shift_intro_frame .

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions of multi-arity\<close>

text \<open>for transformations containing remainder, of form \<open>?R\<heavy_comma> X \<longmapsto> ?R\<heavy_comma> Y\<close>
  so padding Void is required when there is only one item.\<close>

consts \<A>_multi_arity' :: \<open>'a action \<Rightarrow> 'a action\<close>

abbreviation \<open>multi_arity A \<equiv> \<A>_simple_MTF (\<A>_multi_arity' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_multi_arity' _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_multi_arity' _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_multi_arity' _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_multi_arity' _\<close>
]]

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?Y1\<heavy_comma> ?Y2 \<^bold>a\<^bold>n\<^bold>d ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Void\<heavy_comma> Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y \<^bold>a\<^bold>n\<^bold>d ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?Y1\<heavy_comma> ?Y2 \<^bold>a\<^bold>n\<^bold>d ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Void\<heavy_comma> Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action A
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def .


subsubsection \<open>Structural\<close>

consts \<A>_structural :: \<open>'a action \<Rightarrow> 'a action\<close>
consts \<A>_structural_1_2 :: \<open>'a action \<Rightarrow> 'a action\<close>
consts \<A>_structural_2_1 :: \<open>'a action \<Rightarrow> 'a action\<close>

text \<open>
\<^descr> \<^const>\<open>\<A>_structural\<close> \<A>_structural homomorphism in shape:
  \<open> X \<longmapsto> Y \<Longrightarrow> C(X) \<longmapsto> C(Y) \<close>
  typically used in containers.

\<^descr> \<^const>\<open>\<A>_structural_1_2\<close> \<A>_structural homomorphism in shape:
  \<open> X \<longmapsto> Y * Z \<Longrightarrow> C(X) \<longmapsto> C(Y) * C(Z) \<close>

\<^descr> \<^const>\<open>\<A>_structural_2_1\<close> \<A>_structural homomorphism in shape:
  \<open> X * Y \<longmapsto> Z \<Longrightarrow> C(X) * C(Y) \<longmapsto> C(Z) \<close>
\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural _\<close>
  and \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_2_1 _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_2_1 _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_2_1 _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_2_1 _\<close>
  and \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_1_2 _\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_1_2 _\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_1_2 _\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_structural_1_2 _\<close>
]]

paragraph \<open>Fallbacks\<close>

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>_structural A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>_structural_1_2 A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 30]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>_structural_2_1 A\<close>
  unfolding Action_Tag_def .

section \<open>Basic Applications\<close>

subsection \<open>Conversion\<close>

lemma is_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> N" using implies_refl by force

lemma assert_\<phi>app:
  \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m Y \<Longrightarrow> \<^bold>d\<^bold>o X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d Any @action ToSA \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<close>
  unfolding Action_Tag_def Do_def
  using implies_weaken by blast

subsubsection \<open>As\<close>

consts "as" :: \<open>'a set \<Rightarrow> unit action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action as ?T\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action as ?T\<close>]]

abbreviation \<open>\<A>_transform_to_be S \<equiv> \<A>_leading_item (\<A>nap (as S)) \<close>

lemma as_\<phi>app:
  " \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m S
\<Longrightarrow> \<^bold>d\<^bold>o x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P @action \<A>_transform_to_be S
\<Longrightarrow> x \<Ztypecolon> N \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Do_def Action_Tag_def . 

lemma [\<phi>reason 10]:
  \<open> (x \<Ztypecolon> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S
\<Longrightarrow> (x \<Ztypecolon> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s S @action as S\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>Fail to transform\<close> X \<open>to\<close> S)
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action as S\<close>
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 5000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X @action as X\<close>
  unfolding Action_Tag_def using implies_refl .


subsubsection \<open>To\<close>

consts to :: \<open>('a,'b) \<phi> \<Rightarrow> unit action\<close>

abbreviation \<open>\<A>_transform_to T \<equiv> \<A>_leading_item (\<A>nap (to T)) \<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to ?T\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action to ?T\<close>]]

lemma to_\<phi>app:
  \<open> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m T
\<Longrightarrow> \<^bold>d\<^bold>o X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action \<A>_transform_to T
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Do_def Action_Tag_def .

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>Fail to transform\<close> X \<open>to \<phi>-type\<close> T)
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action to T\<close>
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 5000]:
  \<open> (x \<Ztypecolon> T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (x \<Ztypecolon> T) @action to T\<close>
  unfolding Action_Tag_def using implies_refl .


subsection \<open>Case Analysis\<close>

consts \<A>_action_case :: \<open>unit action\<close>

lemma cases_\<phi>app: \<open>PROP Call_Action (\<A>_view_shift_or_imp \<A>_action_case)\<close> ..

declare [[ \<phi>reason_default_pattern
      \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_action_case\<close> \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_action_case\<close>
  and \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_action_case\<close> \<Rightarrow> \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s  _ \<^bold>a\<^bold>n\<^bold>d _ @action \<A>_action_case\<close>
]]

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB
\<Longrightarrow> B + A \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_VS .

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB
\<Longrightarrow> B + A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d PB \<or> PA @action \<A>_action_case\<close>
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


subsection \<open>Duplicate \& Shrink\<close>

consts action_dup    :: \<open>unit action\<close>
       action_shrink :: \<open>unit action\<close>
       action_drop   :: \<open>unit action\<close>

lemma dup_\<phi>app:
  \<open>PROP Call_Action (\<A>_transformation (\<A>_leading_item (\<A>_structural_1_2 action_dup)))\<close> ..

lemma shrink_\<phi>app:
  \<open>PROP Call_Action (\<A>_transformation (multi_arity (\<A>_structural_2_1 action_shrink)))\<close> ..

lemma drop_\<phi>app:
  \<open>PROP Call_Action (\<A>_view_shift_or_imp (multi_arity action_drop))\<close> ..

(*subsection \<open>Simplification as an Action\<close>

consts action_simplify :: \<open>unit action\<close>

lemma simplify_\<phi>app:
  \<open>PROP Call_Action (\<A>_transformation (\<A>_simple_MTF ))\<close> *)


end