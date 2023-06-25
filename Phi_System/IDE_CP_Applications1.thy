chapter \<open>IDE-CP Functions \& Applications - Part I\<close>

text \<open>In this part, we build simple applications based on IDE-CP directly, without too much
  advanced reasoning processes.\<close>

theory IDE_CP_Applications1
  imports Phi_Type_Algebra
  keywords "val" :: quasi_command
  abbrevs "<vals>" = "\<v>\<a>\<l>s"
begin

section \<open>Build Elements of Actions\<close>

subsubsection \<open>Actions only for implication only\<close>

consts \<A>_transformation :: \<open>action \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_transformation _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_transformation _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_transformation _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_transformation _\<close>    (100)
]]

lemma [\<phi>reason 1010]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action action
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action action
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1100]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_implication by blast

lemma [\<phi>reason 1100]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def ToA_Construction_def
  by blast


subsubsection \<open>View Shift\<close>

consts \<A>_view_shift_or_imp :: \<open>action \<Rightarrow> action\<close>

lemma [\<phi>reason 1100]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Imply_def ToA_Construction_def
  by blast

lemma do_\<A>_view_shift_or_imp_VS:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift by blast

lemma do_\<A>_view_shift_or_imp_VS_degrade:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_implication by blast

declare [[\<phi>reason 1100 do_\<A>_view_shift_or_imp_VS do_\<A>_view_shift_or_imp_VS_degrade
      for \<open>PROP Do_Action (\<A>_view_shift_or_imp ?action)
                (Trueprop (CurrentConstruction ?mode ?s ?H ?X))
                ?Result\<close>]]

hide_fact do_\<A>_view_shift_or_imp_VS do_\<A>_view_shift_or_imp_VS_degrade

subsubsection \<open>Nap, a space for injection\<close>

consts \<A>nap :: \<open>action \<Rightarrow> action\<close>

lemma [\<phi>reason 10]:
  \<open> P @action A
\<Longrightarrow> P @action \<A>nap A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for \<open>\<exists>\<and>\<close>-free MTF\<close>

consts \<A>_simple_MTF :: \<open>action \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_simple_MTF _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_simple_MTF _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_simple_MTF _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_simple_MTF _\<close>    (100)
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1010]:
  \<open> (Q \<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<s>\<u>\<b>\<j> Q \<a>\<n>\<d> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Imply_def
  by (simp add: Subjection_expn, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y x \<a>\<n>\<d> P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ExSet Y \<a>\<n>\<d> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Imply_def
  by (simp add: ExSet_expn, blast)

paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> (Q \<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<s>\<h>\<i>\<f>\<t>\<s> Y \<s>\<u>\<b>\<j> Q \<a>\<n>\<d> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: \<phi>expns, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<s>\<h>\<i>\<f>\<t>\<s> Y x \<a>\<n>\<d> P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<s>\<h>\<i>\<f>\<t>\<s> ExSet Y \<a>\<n>\<d> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

paragraph \<open>Finish\<close>

lemma [\<phi>reason 1000]:
  \<open> XXX @action A
\<Longrightarrow> XXX @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for the leading item only\<close>

consts \<A>_leading_item' :: \<open>action \<Rightarrow> action\<close>

abbreviation \<open>\<A>_leading_item A \<equiv> \<A>_simple_MTF (\<A>_leading_item' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_leading_item' _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_leading_item' _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_leading_item' _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_leading_item' _\<close>    (100)
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1050]:
  \<open> ERROR TEXT(\<open>There is no item!\<close>)
\<Longrightarrow> TECHNICAL X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Any \<a>\<n>\<d> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 1050]:
  \<open> ERROR TEXT(\<open>There is no item!\<close>)
\<Longrightarrow> Void \<i>\<m>\<p>\<l>\<i>\<e>\<s> Any \<a>\<n>\<d> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def by blast


lemma [\<phi>reason 1020]:
  \<open> R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' \<a>\<n>\<d> P @action \<A>_leading_item' A
\<Longrightarrow> R * (TECHNICAL X) \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' * (TECHNICAL X) \<a>\<n>\<d> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def
  using implies_right_prod .

lemma [\<phi>reason 1010]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> R * X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * Y \<a>\<n>\<d> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using implies_left_prod .

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Q @action A
\<Longrightarrow> X \<s>\<u>\<b>\<j> P \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<s>\<u>\<b>\<j> P \<a>\<n>\<d> Q @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def Imply_def
  by (clarsimp simp add: Subjection_expn)


paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> R\<heavy_comma> X \<s>\<h>\<i>\<f>\<t>\<s> R\<heavy_comma> Y \<a>\<n>\<d> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using \<phi>view_shift_intro_frame .

lemma [\<phi>reason 1000]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> Q @action A
\<Longrightarrow> X \<s>\<u>\<b>\<j> P \<s>\<h>\<i>\<f>\<t>\<s> Y \<s>\<u>\<b>\<j> P \<a>\<n>\<d> Q @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: \<phi>expns, blast)


subsubsection \<open>Actions of multi-arity\<close>

text \<open>for transformations containing remainder, of form \<open>?R\<heavy_comma> X \<longmapsto> ?R\<heavy_comma> Y\<close>
  so padding Void is required when there is only one item.\<close>

consts \<A>_multi_arity' :: \<open>action \<Rightarrow> action\<close>

abbreviation \<open>multi_arity A \<equiv> \<A>_simple_MTF (\<A>_multi_arity' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_multi_arity' _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_multi_arity' _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_multi_arity' _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_multi_arity' _\<close>    (100)
]]

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<a>\<n>\<d> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y1\<heavy_comma> ?Y2 \<a>\<n>\<d> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Void\<heavy_comma> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y1\<heavy_comma> ?Y2 \<a>\<n>\<d> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Void\<heavy_comma> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action A
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def .


subsubsection \<open>Structural\<close>

consts \<A>_structural :: \<open>action \<Rightarrow> action\<close>
consts \<A>_structural_1_2 :: \<open>action \<Rightarrow> action\<close>
consts \<A>_structural_2_1 :: \<open>action \<Rightarrow> action\<close>

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
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural _\<close>     (100)
  and \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_2_1 _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_2_1 _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_2_1 _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_2_1 _\<close>     (100)
  and \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_1_2 _\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_1_2 _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_1_2 _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<a>\<n>\<d> _ @action \<A>_structural_1_2 _\<close>     (100)
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

paragraph \<open>Default rules\<close>

lemma (in Transformation_Functor_L)
      [\<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<s>\<u>\<b>\<j> y. _ @action \<A>_structural _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>_structural Act)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. \<forall>b. g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using transformation .

lemma (in Functional_Transformation_Functor_L)
      [\<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ @action \<A>_structural _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f a \<Ztypecolon> U \<a>\<n>\<d> P a @action \<A>_structural Act)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. f a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> func_mapper f x \<Ztypecolon> Fb U \<a>\<n>\<d> pred_mapper P x @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .



section \<open>Basic Applications\<close>

subsection \<open>Conversion\<close>

lemma is_\<phi>app: "\<p>\<a>\<r>\<a>\<m> x' \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x = x' \<Longrightarrow> x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> N"
  unfolding Premise_def using implies_refl by force

lemma assert_\<phi>app:
  \<open>\<p>\<a>\<r>\<a>\<m> Y \<Longrightarrow> \<^bold>d\<^bold>o X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Any @action ToSA \<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y\<close>
  unfolding Action_Tag_def Do_def
  using implies_weaken by blast

subsubsection \<open>As\<close>

consts "as" :: \<open>'a set \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action as ?T\<close> \<Rightarrow> \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action as ?T\<close> (100)
]]

abbreviation \<open>\<A>_transform_to_be S \<equiv> \<A>_leading_item (\<A>nap (as S)) \<close>

lemma as_\<phi>app:
  " \<p>\<a>\<r>\<a>\<m> S
\<Longrightarrow> \<^bold>d\<^bold>o x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> X' \<a>\<n>\<d> P @action \<A>_transform_to_be S
\<Longrightarrow> x \<Ztypecolon> N \<i>\<m>\<p>\<l>\<i>\<e>\<s> X' \<a>\<n>\<d> P"
  unfolding Do_def Action_Tag_def .

lemma [\<phi>reason 10]:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> S \<a>\<n>\<d> P
\<Longrightarrow> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> S \<a>\<n>\<d> P @action as S\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1]:
  \<open> ERROR TEXT(\<open>Fail to transform\<close> X \<open>to\<close> S)
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action as S\<close>
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 5000]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action as X\<close>
  unfolding Action_Tag_def using implies_refl .

lemma (in Transformation_Functor_L)
      [\<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<s>\<u>\<b>\<j> y. _ @action as _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action as Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a\<in>D x. \<forall>b. g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action as Z \<close>
  unfolding Action_Tag_def
  using transformation .

lemma (in Functional_Transformation_Functor_L)
      [\<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ @action as _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f a \<Ztypecolon> U \<a>\<n>\<d> P a @action as Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a\<in>D x. f a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> func_mapper f x \<Ztypecolon> Fb U \<a>\<n>\<d> pred_mapper P x @action as Z \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .


subsubsection \<open>To\<close>

consts to :: \<open>('a,'b) \<phi> \<Rightarrow> action\<close>
consts RAW :: \<open>('a,'b) \<phi>\<close> \<comment> \<open>destruct\<close>

abbreviation \<open>\<A>_transform_to T \<equiv> \<A>_leading_item (\<A>nap (to T)) \<close>

term \<open>ERROR TEXT(\<open>asda\<close>)\<close>

declare [[\<phi>reason_default_pattern
    \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to ?T\<close> \<Rightarrow> \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action to ?T\<close> (100)
and \<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?U \<a>\<n>\<d> _ @action to ?T\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Bad form of the To transformation\<close> (?y \<Ztypecolon> ?U) \<open>should be a set. Use\<close> (y \<Ztypecolon> ?U \<s>\<u>\<b>\<j> y. y = ?y) \<open>instead\<close>)\<close> (1000)
]]

lemma to_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> T
\<Longrightarrow> \<^bold>d\<^bold>o X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_transform_to T
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  unfolding Do_def Action_Tag_def .

lemma destruct_\<phi>app:
  \<open> \<^bold>d\<^bold>o X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action \<A>_transform_to RAW
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  unfolding Do_def Action_Tag_def .

lemma [\<phi>reason 1]:
  \<open> ERROR TEXT(\<open>Fail to transform\<close> X \<open>to \<phi>-type\<close> T)
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action to T\<close>
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 5]:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y' \<Ztypecolon> U) \<a>\<n>\<d> P
\<Longrightarrow> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. y = y') \<a>\<n>\<d> P @action to U\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 5000]:
  \<open> (x \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (x' \<Ztypecolon> T \<s>\<u>\<b>\<j> x'. x' = x) @action to T\<close>
  unfolding Action_Tag_def by simp

lemma (in Transformation_Functor_L)
      [\<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<s>\<u>\<b>\<j> y. _ @action to _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a\<in>D x. \<forall>b. g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fb Z) \<close>
  unfolding Action_Tag_def
  using transformation .

lemma (in Functional_Transformation_Functor_L)
      [\<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ @action to _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f a \<Ztypecolon> U \<a>\<n>\<d> P a @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a\<in>D x. f a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<i>\<m>\<p>\<l>\<i>\<e>\<s> func_mapper f x \<Ztypecolon> Fb U \<a>\<n>\<d> pred_mapper P x @action to (Fb Z) \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .


subsection \<open>Case Analysis\<close>

consts \<A>_action_case :: \<open>action\<close>
       \<A>_action_case_on :: \<open>action\<close>

lemma cases_\<phi>app: \<open>PROP Call_Action (\<A>_view_shift_or_imp \<A>_action_case)\<close> ..
lemma cases_on_\<phi>app: \<open>PROP Call_Action (\<A>_view_shift_or_imp \<A>_action_case_on)\<close> ..

declare [[ \<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_action_case\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_action_case\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_action_case\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_action_case\<close>    (100)
  and \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_action_case_on\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_action_case_on\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_action_case_on\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<a>\<n>\<d> _ @action \<A>_action_case_on\<close>    (100)
]]

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> PB
\<Longrightarrow> B + A \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_VS .

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> PB
\<Longrightarrow> B + A \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_IMP .

lemma [\<phi>reason 1000]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<s>\<h>\<i>\<f>\<t>\<s> Ya \<a>\<n>\<d> PA)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> \<not> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Yb \<a>\<n>\<d> PB)
\<Longrightarrow> If P Ya Yb \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y @action invoke_branch_convergence
\<Longrightarrow> If P A B \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> If P PA PB @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def Premise_def
  apply (cases P; simp)
  using \<phi>view_trans view_shift_by_implication apply fastforce
  using View_Shift_def view_shift_by_implication by force

lemma [\<phi>reason 1000]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<i>\<m>\<p>\<l>\<i>\<e>\<s> Ya \<a>\<n>\<d> PA)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> \<not> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Yb \<a>\<n>\<d> PB)
\<Longrightarrow> \<^bold>d\<^bold>o If P Ya Yb \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y @action invoke_branch_convergence
\<Longrightarrow> If P A B \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> If P PA PB @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def Premise_def
  apply (cases P; simp)
  using implies_trans apply fastforce
  using implies_trans by fastforce


(*lemma [\<phi>reason 1000]:
  \<open> \<p>\<a>\<r>\<a>\<m> P
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> PA)
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> PB
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<a>\<n>\<d> PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_VS . *)


subsection \<open>Construct \& Destruct \<open>\<phi>\<close>-Type by Definition\<close>

consts \<A>_construct\<phi> :: \<open>'a set \<Rightarrow> action\<close>
       \<A>_destruct\<phi>  :: \<open>('a,'b) \<phi> \<Rightarrow> action\<close>

declare [[ \<phi>reason_default_pattern
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_construct\<phi> ?S\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_construct\<phi> ?S\<close>    (100)
  and \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_destruct\<phi> ?T\<close> \<Rightarrow>
      \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_destruct\<phi> ?T\<close>    (100)
]]

lemma destruct\<phi>_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> T'
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> D \<a>\<n>\<d> P @action \<A>_destruct\<phi> T'
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> D \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def .

consts \<A>_construct\<phi>_ToSA :: \<open>'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> action\<close>

lemma [\<phi>reason 1 for \<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_construct\<phi>_ToSA _ _\<close>]:
  \<open> ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> P @action \<A>_construct\<phi>_ToSA x T\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1100 for \<open>?S \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_construct\<phi>_ToSA _ _\<close>]:
  \<open> ((X \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T \<a>\<n>\<d> P @action \<A>_construct\<phi> (x \<Ztypecolon> T)
&&&   S \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P @action ToSA))
||| ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T \<a>\<n>\<d> P @action \<A>_construct\<phi>_ToSA x T\<close>
  unfolding Action_Tag_def Do_def atomize_conj atomize_Branch
  using implies_trans by fastforce

lemma [\<phi>reason 1110 for \<open>(?S::'a::sep_magma set) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_construct\<phi>_ToSA _ _\<close>]:
  \<open> (X \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T \<a>\<n>\<d> P @action \<A>_construct\<phi> (x \<Ztypecolon> T)
&&&  S \<i>\<m>\<p>\<l>\<i>\<e>\<s> (if single then X else X \<r>\<e>\<m>\<a>\<i>\<n>\<s> S') \<a>\<n>\<d> P @action ToSA)
||| ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> (if single then x \<Ztypecolon> T else x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> S') \<a>\<n>\<d> P @action \<A>_construct\<phi>_ToSA x T\<close>
  for S :: \<open>'a::sep_magma set\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def Do_def atomize_conj atomize_Branch
  apply (cases single; simp)
  using implies_trans apply fastforce
  using implies_left_prod implies_trans by fastforce

lemma construct\<phi>_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> (x \<Ztypecolon> T)
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> P @action \<A>_construct\<phi>_ToSA x T
\<Longrightarrow> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> P \<close>
  unfolding Action_Tag_def Do_def .

consts mode_\<phi>defs :: \<open>action\<close>

abbreviation Unfold_\<phi>Defs :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] _ : _" [1000,10] 9)
  where "Unfold_\<phi>Defs \<equiv> Simplify mode_\<phi>defs"

lemma [\<phi>reason 10 for \<open>?x \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _ @action \<A>_destruct\<phi> _\<close>]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] D: T x
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> D @action \<A>_destruct\<phi> T\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by (simp add: implies_refl)

lemma [\<phi>reason 10]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] X: T x
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T @action \<A>_construct\<phi> (x \<Ztypecolon> T)\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by (simp add: implies_refl)


ML \<open>
structure PhiDef_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>\<phi>defs\<close>
  val comment = "Rules to expand definitions of \<phi>-Type"
)\<close>

\<phi>reasoner_ML Unfold_\<phi>Defs 1000 (\<open>Unfold_\<phi>Defs ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_by_ss' PhiDef_SS.get'\<close>

declare prod.case[\<phi>defs]



subsection \<open>Duplicate \& Shrink\<close>

consts action_dup    :: \<open>action\<close>
       action_shrink :: \<open>action\<close>
       action_drop   :: \<open>action\<close>

lemma dup_\<phi>app:
  \<open>PROP Call_Action (\<A>_transformation (\<A>_leading_item (\<A>_structural_1_2 action_dup)))\<close> ..

lemma shrink_\<phi>app:
  \<open>PROP Call_Action (\<A>_transformation (multi_arity (\<A>_structural_2_1 action_shrink)))\<close> ..

lemma drop_\<phi>app:
  \<open>PROP Call_Action (\<A>_view_shift_or_imp (multi_arity action_drop))\<close> ..

(*subsection \<open>Simplification as an Action\<close>

consts action_simplify :: \<open>action\<close>

lemma simplify_\<phi>app:
  \<open>PROP Call_Action (\<A>_transformation (\<A>_simple_MTF ))\<close> *)

subsection \<open>Transformation\<close>

consts find_source_object :: action

declare [[\<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?U \<a>\<n>\<d> _ find_source_object\<close> \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?U \<a>\<n>\<d> _ find_source_object\<close> (100) ]]

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>cannot find a source object\<close> x \<open>enabling transformation\<close> (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> T \<a>\<n>\<d> P))
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action find_source_object\<close>
  unfolding Action_Tag_def
  by simp


end
