chapter \<open>IDE-CP Functions \& Applications - Part I\<close>

text \<open>In this part, we build simple applications based on IDE-CP directly, without too much
  advanced reasoning processes.\<close>

theory IDE_CP_Applications1
  imports IDE_CP_Core Phi_Algebras.Map_of_Tree
  keywords "val" :: quasi_command
  abbrevs "<vals>" = "\<v>\<a>\<l>s"
      and "<for>" = "\<f>\<o>\<r>"
      and "<split>" = "\<s>\<p>\<l>\<i>\<t>"
begin

section \<open>Build Elements of Actions\<close>

subsubsection \<open>Actions only for implication only\<close>

consts \<A>_transformation :: \<open>action \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_transformation _\<close>    (100)
]]

lemma [\<phi>reason 1010]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transformation action\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1100]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_implication by blast

lemma [\<phi>reason 1100]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_transformation action)
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Transformation_def ToA_Construction_def
  by blast


subsubsection \<open>View Shift\<close>

consts \<A>_view_shift_or_imp :: \<open>action \<Rightarrow> action\<close>

lemma [\<phi>reason 1100]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<a>\<b>\<s>\<t>\<r>\<a>\<c>\<t>\<i>\<o>\<n>(s) \<i>\<s> Y) \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Transformation_def ToA_Construction_def
  by blast

lemma do_\<A>_view_shift_or_imp_VS:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action action
\<Longrightarrow> PROP Do_Action (\<A>_view_shift_or_imp action)
      (Trueprop (CurrentConstruction mode s H X))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> CurrentConstruction mode s H Y \<and> P )\<close>
  unfolding Do_Action_def Action_Tag_def Action_Tag_def
  using \<phi>apply_view_shift by blast

lemma do_\<A>_view_shift_or_imp_VS_degrade:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action action
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
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_simple_MTF _\<close>    (100)
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1010]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y x \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp, blast)

paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<s>\<h>\<i>\<f>\<t>\<s> Y \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: INTERP_SPEC_subj, blast)

lemma [\<phi>reason 1010]:
  \<open> (\<And>x. X x \<s>\<h>\<i>\<f>\<t>\<s> Y x \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A)
\<Longrightarrow> ExSet X \<s>\<h>\<i>\<f>\<t>\<s> ExSet Y \<w>\<i>\<t>\<h> P @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (clarsimp simp add: INTERP_SPEC_ex, metis)

paragraph \<open>Finish\<close>

lemma [\<phi>reason 1000]:
  \<open> XXX @action A
\<Longrightarrow> XXX @action \<A>_simple_MTF A\<close>
  unfolding Action_Tag_def .

subsubsection \<open>Actions for the leading item only\<close>

consts \<A>_leading_item' :: \<open>action \<Rightarrow> action\<close>

abbreviation \<open>\<A>_leading_item A \<equiv> \<A>_simple_MTF (\<A>_leading_item' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_leading_item' _\<close>    (100)
]]

paragraph \<open>Implication\<close>

lemma [\<phi>reason 1050]:
  \<open> ERROR TEXT(\<open>There is no item!\<close>)
\<Longrightarrow> TECHNICAL X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Any \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 1050]:
  \<open> ERROR TEXT(\<open>There is no item!\<close>)
\<Longrightarrow> Void \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Any \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def by blast


lemma [\<phi>reason 1020]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A
\<Longrightarrow> R * (TECHNICAL X) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * (TECHNICAL X) \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def
  using implies_right_prod .

lemma [\<phi>reason 1010]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using implies_left_prod .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action A
\<Longrightarrow> X \<s>\<u>\<b>\<j> P \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp


paragraph \<open>View Shift\<close>

lemma [\<phi>reason 1010]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> R\<heavy_comma> X \<s>\<h>\<i>\<f>\<t>\<s> R\<heavy_comma> Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def
  using \<phi>view_shift_intro_frame .

lemma [\<phi>reason 1000]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> Q @action A
\<Longrightarrow> X \<s>\<u>\<b>\<j> P \<s>\<h>\<i>\<f>\<t>\<s> Y \<s>\<u>\<b>\<j> P \<w>\<i>\<t>\<h> Q @action \<A>_leading_item' A\<close>
  unfolding Action_Tag_def View_Shift_def
  by (simp add: INTERP_SPEC_subj, blast)


subsubsection \<open>Actions for every \<phi>-type item\<close>

consts \<A>_every_item' :: \<open>action \<Rightarrow> action\<close>

abbreviation \<open>\<A>_every_item A \<equiv> \<A>_simple_MTF (\<A>_every_item' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_every_item' _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_every_item' _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_every_item' _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_every_item' _\<close>    (100)
]]


paragraph \<open>Implication\<close>

lemma [\<phi>reason 1050]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_every_item' A
\<Longrightarrow> X \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P @action \<A>_every_item' A\<close>
  unfolding Action_Tag_def
  using Subjection_transformation .

lemma [\<phi>reason 1050]:
  \<open> (\<And>c. X c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y c \<w>\<i>\<t>\<h> P @action \<A>_every_item' A)
\<Longrightarrow> ExSet X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet Y \<w>\<i>\<t>\<h> P @action \<A>_every_item' A\<close>
  unfolding Action_Tag_def
  using ExSet_transformation .

lemma [\<phi>reason 1050]:
  \<open> R * X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * Y \<w>\<i>\<t>\<h> P @action \<A>_every_item' A
\<Longrightarrow> R * (X \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * (Y \<s>\<u>\<b>\<j> Q) \<w>\<i>\<t>\<h> P @action \<A>_every_item' A\<close>
  unfolding Action_Tag_def
  by (simp add: Subjection_transformation)

lemma [\<phi>reason 1050]:
  \<open> (\<And>c. R * X c \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * Y c \<w>\<i>\<t>\<h> P @action \<A>_every_item' A)
\<Longrightarrow> R * ExSet X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * ExSet Y \<w>\<i>\<t>\<h> P @action \<A>_every_item' A\<close>
  unfolding Action_Tag_def
  by (simp add: ExSet_transformation)

lemma [\<phi>reason 1050]:
  \<open> TECHNICAL X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action \<A>_every_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def Technical_def by simp

lemma [\<phi>reason 1020]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> P @action \<A>_every_item' A
\<Longrightarrow> R * (TECHNICAL X) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * (TECHNICAL X) \<w>\<i>\<t>\<h> P @action \<A>_every_item' A\<close>
  \<comment> \<open>Never bind technical items\<close>
  unfolding Action_Tag_def
  using implies_right_prod .

lemma [\<phi>reason 1010]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> Q @action \<A>_every_item' A
\<Longrightarrow> R * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * Y \<w>\<i>\<t>\<h> P \<and> Q @action \<A>_every_item' A\<close>
  unfolding Action_Tag_def
  using implies_prod_bi_prod .

lemma [\<phi>reason 1005]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_every_item' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action \<A>_every_item' A\<close>
  unfolding Action_Tag_def by simp


subsubsection \<open>Actions of multi-arity\<close>

text \<open>for transformations containing remainder, of form \<open>?R\<heavy_comma> X \<longmapsto> ?R\<heavy_comma> Y\<close>
  so padding Void is required when there is only one item.\<close>

consts \<A>_multi_arity' :: \<open>action \<Rightarrow> action\<close>

abbreviation \<open>multi_arity A \<equiv> \<A>_simple_MTF (\<A>_multi_arity' A)\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_multi_arity' _\<close>    (100)
]]

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<s>\<h>\<i>\<f>\<t>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> ?Y1\<heavy_comma> ?Y2 \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Void\<heavy_comma> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1010 except \<open>?X1\<heavy_comma> ?X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> Void\<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1010 except \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y1\<heavy_comma> ?Y2 \<w>\<i>\<t>\<h> ?P @action \<A>_multi_arity' ?A\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Void\<heavy_comma> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_multi_arity' A\<close>
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
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural _\<close>     (100)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_2_1 _\<close>     (100)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_structural_1_2 _\<close>     (100)
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

subsection \<open>Is \& Assert\<close>

lemma is_\<phi>app: "\<p>\<a>\<r>\<a>\<m> x' \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x = x' \<Longrightarrow> x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> N"
  unfolding Premise_def using implies_refl by force

lemma assert_\<phi>app:
  \<open>\<p>\<a>\<r>\<a>\<m> Y \<Longrightarrow> \<^bold>d\<^bold>o X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Any @action ToSA \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<close>
  unfolding Action_Tag_def Do_def
  using implies_weaken by blast

subsection \<open>As\<close>

consts "as" :: \<open>'a set \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action as ?T\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action as ?T\<close> (100)
]]

abbreviation \<open>\<A>_transform_to_be S \<equiv> \<A>_leading_item (\<A>nap (as S)) \<close>

lemma as_\<phi>app:
  " \<p>\<a>\<r>\<a>\<m> S
\<Longrightarrow> \<^bold>d\<^bold>o x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' \<w>\<i>\<t>\<h> P @action \<A>_transform_to_be S
\<Longrightarrow> x \<Ztypecolon> N \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' \<w>\<i>\<t>\<h> P"
  unfolding Do_def Action_Tag_def .

lemma [\<phi>reason 10]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S \<w>\<i>\<t>\<h> P @action as S\<close>
  unfolding Action_Tag_def .

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>Fail to transform\<close> X \<open>to\<close> S)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action as S\<close>
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 5000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action as X\<close>
  unfolding Action_Tag_def using implies_refl .



subsection \<open>To\<close>

consts to :: \<open>('a,'b) \<phi> \<Rightarrow> action\<close>
       RAW :: \<open>('a,'b) \<phi>\<close> \<comment> \<open>destruct whom TODO! WIP!\<close>
       \<A>subst :: \<open>('a,'b) \<phi> \<Rightarrow> ('c,'d) \<phi> \<Rightarrow> ('c,'d) \<phi>\<close> (infixl "\<f>\<o>\<r>" 10)
          \<comment> \<open>\<^term>\<open>to (A \<f>\<o>\<r> B)\<close> means, substitute A for B\<close>
       \<A>split :: \<open>('a,'b) \<phi> \<Rightarrow> ('a,'b) \<phi>\<close> ("\<s>\<p>\<l>\<i>\<t>")
       \<A>\<T>split_step :: \<open>action\<close>

abbreviation \<open>\<A>_transform_to T \<equiv> \<A>_leading_item (\<A>nap (to T)) \<close>

declare [[\<phi>reason_default_pattern
    \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. ?R y) \<w>\<i>\<t>\<h> ?P @action to ?T\<close> \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to ?T\<close> (100)
and \<open>?X @action to ?A\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Bad form: \<close> (?X @action to ?A) \<newline>
                                      \<open>Expect: \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> ?Y \<s>\<u>\<b>\<j> y. ?r y) @action to _\<close>\<close>)\<close> (1)
and \<open>x \<Ztypecolon> ?T \<s>\<u>\<b>\<j> x. ?rel x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. _ @action \<A>\<T>split_step\<close> \<Rightarrow>
    \<open>x \<Ztypecolon> ?T \<s>\<u>\<b>\<j> x. ?rel x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> _ \<s>\<u>\<b>\<j> y. _ \<w>\<i>\<t>\<h> _ @action \<A>\<T>split_step\<close> (100)
and \<open>?X @action \<A>\<T>split_step\<close> \<Rightarrow> \<open>ERROR TEXT(\<open>Bad form: \<close> (?X @action \<A>\<T>split_step))\<close> (1)
]]

lemma [cong]:
  \<open> X \<equiv> X'
\<Longrightarrow> U \<equiv> U'
\<Longrightarrow> r \<equiv> r'
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y) @action to A
 \<equiv> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U' \<s>\<u>\<b>\<j> y. r' y) @action to A\<close>
  by simp

lemma [cong]:
  \<open> T \<equiv> T'
\<Longrightarrow> f \<equiv> f'
\<Longrightarrow> U \<equiv> U'
\<Longrightarrow> g \<equiv> g'
\<Longrightarrow> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. f x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. g y @action \<A>\<T>split_step
 \<equiv> x \<Ztypecolon> T' \<s>\<u>\<b>\<j> x. f' x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U' \<s>\<u>\<b>\<j> y. g' y @action \<A>\<T>split_step\<close>
  by simp

lemma to_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> T
\<Longrightarrow> \<^bold>d\<^bold>o X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transform_to T
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Do_def Action_Tag_def .

lemma destruct_\<phi>app:
  \<open> \<^bold>d\<^bold>o X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>_transform_to RAW
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Do_def Action_Tag_def .

lemma [\<phi>reason 0 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to _\<close>]:
  \<open> FAIL TEXT(\<open>Fail to transform\<close> X \<open>to\<close> T)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action to T\<close>
  unfolding Action_Tag_def by blast
 
lemma [\<phi>reason default 1]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y' \<Ztypecolon> U) \<w>\<i>\<t>\<h> P
\<Longrightarrow> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. y = y') \<w>\<i>\<t>\<h> P @action to U\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 5000]:
  \<open> (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x' \<Ztypecolon> T \<s>\<u>\<b>\<j> x'. x' = x) @action to T\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> \<s>\<u>\<b>\<j> x. x = () @action to Target \<close>
  unfolding Action_Tag_def by simp


subsubsection \<open>Termination\<close>

lemma ToA_trivial:
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<s>\<u>\<b>\<j> x'. x' = x @action to any\<close>
  unfolding Action_Tag_def by simp

\<phi>reasoner_ML \<A>subst 10000 (\<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (_ \<f>\<o>\<r> _)\<close>) = \<open>
Phi_Help.lambda_normalization_ctac (fn (ctxt,sequent) => Seq.make (fn () =>
  case Thm.major_prem_of sequent
    of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Action_Tag\<close>, _)
            $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ _ $ _)
            $ (Const(\<^const_name>\<open>to\<close>, _) $ (Const(\<^const_name>\<open>\<A>subst\<close>, _) $ _ $ T)))
      => if exists_subterm (fn tm => tm aconv T) X
         then NONE
         else SOME ((ctxt, @{thm' ToA_trivial} RS sequent), Seq.empty)
     | _ => raise TERM ("", [])
))\<close>

\<phi>reasoner_ML \<A>subst 10000 (\<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (\<s>\<p>\<l>\<i>\<t> _)\<close>) = \<open>
Phi_Help.lambda_normalization_ctac (fn (ctxt,sequent) => Seq.make (fn () =>
  case Thm.major_prem_of sequent
    of _ (*Trueprop*) $ (Const(\<^const_name>\<open>Action_Tag\<close>, _)
            $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ _ $ _)
            $ (Const(\<^const_name>\<open>to\<close>, _) $ (Const(\<^const_name>\<open>\<A>split\<close>, _) $ T)))
      => if exists_subterm (fn tm => tm aconv T) X
         then NONE
         else SOME ((ctxt, @{thm' ToA_trivial} RS sequent), Seq.empty)
     | _ => raise TERM ("", [])
))\<close>

hide_fact ToA_trivial

lemma [\<phi>reason default 10 for \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action to (_ \<f>\<o>\<r> _)\<close> ]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. g y
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. g y @action to (U \<f>\<o>\<r> T) \<close>
  unfolding Action_Tag_def .


subsubsection \<open>Product\<close>

(* \<open>to\<close> is for single \<phi>-type item!

lemma prod_transform_to1:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action to T
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action to U
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action to (T \<^emph> U)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

lemma prod_transform_to2:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action to U
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action to T
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action to (T \<^emph> U)\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)

declare [[\<phi>reason 1200 prod_transform_to1 prod_transform_to2
      for \<open>?A * ?B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (?T \<^emph> ?U)\<close>]]

hide_fact prod_transform_to1 prod_transform_to2

lemma [\<phi>reason 1100]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action to T
\<Longrightarrow> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q @action to T
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q @action to T\<close>
  unfolding Action_Tag_def
  by (meson implies_left_prod implies_right_prod implies_trans)
*)

lemma Prod_transform_to1:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' \<w>\<i>\<t>\<h> P @action to A
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' \<w>\<i>\<t>\<h> Q @action to B
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') \<w>\<i>\<t>\<h> P \<and> Q @action to (A \<^emph> B)\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)

lemma Prod_transform_to2:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' \<w>\<i>\<t>\<h> P @action to B
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' \<w>\<i>\<t>\<h> Q @action to A
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') \<w>\<i>\<t>\<h> P \<and> Q @action to (A \<^emph> B)\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)

declare [[\<phi>reason 1200 Prod_transform_to1 Prod_transform_to2
      for \<open>_ \<Ztypecolon> (?T \<^emph> ?U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (?A \<^emph> ?B)\<close>]]

hide_fact Prod_transform_to1 Prod_transform_to2

lemma [\<phi>reason 1100]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' \<w>\<i>\<t>\<h> P @action to Target
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' \<w>\<i>\<t>\<h> Q @action to Target
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') \<w>\<i>\<t>\<h> P \<and> Q @action to Target\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)


lemma [\<phi>reason 1210 for \<open>_ \<Ztypecolon> _ \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to ( _ \<f>\<o>\<r> _ \<^emph> _) \<close>]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<s>\<u>\<b>\<j> x'. ra x' \<w>\<i>\<t>\<h> P @action to (T' \<f>\<o>\<r> T)
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<s>\<u>\<b>\<j> y'. rb y' \<w>\<i>\<t>\<h> Q @action to (U' \<f>\<o>\<r> U)
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xy' \<Ztypecolon> (T' \<^emph> U') \<s>\<u>\<b>\<j> xy'. ra (fst xy') \<and> rb (snd xy') \<w>\<i>\<t>\<h> P \<and> Q
    @action to (T' \<^emph> U' \<f>\<o>\<r> T \<^emph> U)\<close>
  unfolding Action_Tag_def Transformation_def
  by (cases x; simp; blast)

lemma [\<phi>reason 1210 for \<open>_ \<Ztypecolon> _ \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action to (\<s>\<p>\<l>\<i>\<t> (_ \<^emph> _))\<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> (T \<^emph> U) \<s>\<u>\<b>\<j> x'. x' = x @action to (\<s>\<p>\<l>\<i>\<t> (T \<^emph> U)) \<close>
  unfolding Action_Tag_def Transformation_def
  by simp


subsubsection \<open>To Itself\<close>

lemma [\<phi>reason default 2]:
  \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> v \<Ztypecolon> Itself \<s>\<u>\<b>\<j> v. v \<in> (x \<Ztypecolon> T) @action to Itself\<close>
  unfolding Action_Tag_def Transformation_def
  by simp

lemma [\<phi>reason 1200]:
  \<open>() \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> x. x = 1 @action to Itself\<close>
  unfolding Action_Tag_def Transformation_def \<phi>None_expn
  by simp

lemma [\<phi>reason 1200]:
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> x. ra x @action to Itself
\<Longrightarrow> snd x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> x. rb x @action to Itself
\<Longrightarrow> x \<Ztypecolon> T \<^emph> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> x. (\<exists>b a. x = b * a \<and> b ## a \<and> rb b \<and> ra a) @action to Itself \<close>
  unfolding Action_Tag_def Transformation_def \<phi>None_expn
  by (cases x; simp; blast)


subsection \<open>Case Analysis\<close>

consts \<A>_action_case :: \<open>action\<close>
       \<A>_action_case_on :: \<open>action\<close>

lemma cases_\<phi>app: \<open>PROP Call_Action (\<A>_view_shift_or_imp \<A>_action_case)\<close> ..
lemma cases_on_\<phi>app: \<open>PROP Call_Action (\<A>_view_shift_or_imp \<A>_action_case_on)\<close> ..

declare [[ \<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case\<close>    (100)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case_on\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case_on\<close>    (100)
  and \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case_on\<close> \<Rightarrow>
      \<open>?X \<s>\<h>\<i>\<f>\<t>\<s>  _ \<w>\<i>\<t>\<h> _ @action \<A>_action_case_on\<close>    (100)
]]

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PB
\<Longrightarrow> B + A \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_VS .

lemma [\<phi>reason 1000]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> PA
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> PB
\<Longrightarrow> B + A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_IMP .

lemma [\<phi>reason 1000]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<s>\<h>\<i>\<f>\<t>\<s> Ya \<w>\<i>\<t>\<h> PA)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> \<not> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Yb \<w>\<i>\<t>\<h> PB)
\<Longrightarrow> If P Ya Yb \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action invoke_branch_convergence
\<Longrightarrow> If P A B \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> If P PA PB @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def Premise_def
  apply (cases P; simp)
  using \<phi>view_trans view_shift_by_implication apply fastforce
  using View_Shift_def view_shift_by_implication by force

lemma [\<phi>reason 1000]:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<w>\<i>\<t>\<h> PA)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> \<not> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<w>\<i>\<t>\<h> PB)
\<Longrightarrow> \<^bold>d\<^bold>o If P Ya Yb \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action invoke_branch_convergence
\<Longrightarrow> If P A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> If P PA PB @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def Premise_def
  apply (cases P; simp)
  using implies_trans apply fastforce
  using implies_trans by fastforce


(*lemma [\<phi>reason 1000]:
  \<open> \<p>\<a>\<r>\<a>\<m> P
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PA)
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PB
\<Longrightarrow> X \<s>\<h>\<i>\<f>\<t>\<s> Y \<w>\<i>\<t>\<h> PB \<or> PA @action \<A>_action_case\<close>
  unfolding Argument_def Action_Tag_def using \<phi>CASE_VS . *)


subsection \<open>Construct \& Destruct \<open>\<phi>\<close>-Type by Definition\<close>

consts \<A>_construct\<phi> :: \<open>'a set \<Rightarrow> action\<close>
       \<A>_destruct\<phi>  :: \<open>('a,'b) \<phi> \<Rightarrow> action\<close>

declare [[ \<phi>reason_default_pattern
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi> ?S\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi> ?S\<close>    (100)
  and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_destruct\<phi> ?T\<close> \<Rightarrow>
      \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_destruct\<phi> ?T\<close>    (100)
]]

lemma destruct\<phi>_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> T'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> D \<w>\<i>\<t>\<h> P @action \<A>_destruct\<phi> T'
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> D \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def .

consts \<A>_construct\<phi>_ToSA :: \<open>'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> action\<close>

lemma [\<phi>reason 1 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi>_ToSA _ _\<close>]:
  \<open> ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_ToSA x T\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1100 for \<open>?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi>_ToSA _ _\<close>]:
  \<open> ((X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi> (x \<Ztypecolon> T)
&&&   S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P @action ToSA))
||| ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_ToSA x T\<close>
  unfolding Action_Tag_def Do_def atomize_conj atomize_Branch
  using implies_trans by fastforce

lemma [\<phi>reason 1110 for \<open>(?S::'a::sep_magma set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_construct\<phi>_ToSA _ _\<close>]:
  \<open> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi> (x \<Ztypecolon> T)
&&&  S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if single then X else X \<r>\<e>\<m>\<a>\<i>\<n>\<s> S') \<w>\<i>\<t>\<h> P @action ToSA)
||| ERROR TEXT(\<open>Fail to construct\<close> (x \<Ztypecolon> T) \<open>from definition\<close>)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if single then x \<Ztypecolon> T else x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> S') \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_ToSA x T\<close>
  for S :: \<open>'a::sep_magma set\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def Do_def atomize_conj atomize_Branch
  apply (cases single; simp)
  using implies_trans apply fastforce
  using implies_left_prod implies_trans by fastforce

lemma construct\<phi>_\<phi>app:
  \<open> \<p>\<a>\<r>\<a>\<m> (x \<Ztypecolon> T)
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P @action \<A>_construct\<phi>_ToSA x T
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def Do_def .

consts mode_\<phi>defs :: \<open>action\<close>

abbreviation Unfold_\<phi>Defs :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] _ : _" [1000,10] 9)
  where "Unfold_\<phi>Defs \<equiv> Simplify mode_\<phi>defs"

lemma [\<phi>reason 10 for \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>_destruct\<phi> _\<close>]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] D: T x
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> D @action \<A>_destruct\<phi> T\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by simp

lemma [\<phi>reason 10]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>\<d>\<e>\<f>\<s>] X: T x
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T @action \<A>_construct\<phi> (x \<Ztypecolon> T)\<close>
  unfolding Action_Tag_def Simplify_def \<phi>Type_def by simp


ML \<open>
structure PhiDef_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>\<phi>defs\<close>
  val comment = "Rules to expand definitions of \<phi>-Type"
)\<close>

\<phi>reasoner_ML Unfold_\<phi>Defs 1000 (\<open>Unfold_\<phi>Defs ?X' ?X\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' PhiDef_SS.get')\<close>

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
      \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _ find_source_object\<close> \<Rightarrow> \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _ find_source_object\<close> (100) ]]

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>cannot find a source object\<close> x \<open>enabling transformation\<close> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<w>\<i>\<t>\<h> P))
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action find_source_object\<close>
  unfolding Action_Tag_def
  by simp


end
