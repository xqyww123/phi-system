theory Phi_Algebra_Set
  imports Algebras
begin

subsection \<open>Separation Closed Set\<close>

definition One_in_Set :: \<open>'a::one set \<Rightarrow> bool\<close>
  where \<open>One_in_Set S \<longleftrightarrow> 1 \<in> S\<close>

definition Sep_Closed :: \<open>'a::sep_magma set \<Rightarrow> bool\<close>
  where \<open>Sep_Closed S \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> x \<in> S \<and> y \<in> S \<longrightarrow> (x * y) \<in> S)\<close>

lemma Sep_Closed_inter:
  \<open>Sep_Closed S1 \<Longrightarrow> Sep_Closed S2 \<Longrightarrow> Sep_Closed (S1 \<inter> S2)\<close>
  unfolding Sep_Closed_def by blast

lemma One_in_Set_inter:
  \<open>One_in_Set S1 \<Longrightarrow> One_in_Set S2 \<Longrightarrow> One_in_Set (S1 \<inter> S2)\<close>
  unfolding One_in_Set_def by blast

lemma Sep_Closed_UNIV[simp]:
  \<open>Sep_Closed UNIV\<close>
  unfolding Sep_Closed_def by simp

lemma One_in_Set_UNIV[simp]:
  \<open>One_in_Set UNIV\<close>
  unfolding One_in_Set_def by simp

typedef (overloaded) ('a::sep_magma_1) sep_closed_set
    = \<open>Collect (Sep_Closed::'a set \<Rightarrow> bool) \<inter> Collect One_in_Set\<close>
  morphisms dest_sep_closed_set sep_closed_set
  unfolding Sep_Closed_def One_in_Set_def by blast

setup_lifting type_definition_sep_closed_set

lift_definition sep_closed_member :: \<open>'a::sep_magma_1 \<Rightarrow> 'a sep_closed_set \<Rightarrow> bool\<close> (infix "\<in>\<^sub>S" 50)
  is \<open>\<lambda>x S. x \<in> S\<close> .

lemma in_sep_closed_set[simp]:
  \<open>Sep_Closed S \<Longrightarrow> One_in_Set S \<Longrightarrow> x \<in>\<^sub>S sep_closed_set S \<longleftrightarrow> x \<in> S\<close>
  unfolding sep_closed_member_def
  by (simp add: sep_closed_set_inverse)

lemma one_in_sep_closed_set[simp]:
  \<open>1 \<in>\<^sub>S S\<close> for S :: \<open>'a::sep_magma_1 sep_closed_set\<close>
  by (transfer; simp add: One_in_Set_def)

lemma mult_in_sep_closed_set[simp]:
  \<open>x ## y \<Longrightarrow> x \<in>\<^sub>S S \<and> y \<in>\<^sub>S S \<longrightarrow> x * y \<in>\<^sub>S S\<close> for S :: \<open>'a::sep_algebra sep_closed_set\<close>
  by (transfer; simp add: Sep_Closed_def)

lift_definition sep_closed_inter :: \<open>'a::sep_magma_1 sep_closed_set \<Rightarrow> 'a sep_closed_set \<Rightarrow> 'a sep_closed_set\<close> (infixl "\<inter>\<^sub>S" 65)
  is \<open>\<lambda>S1 S2. S1 \<inter> S2\<close>
  by (clarsimp simp add: Sep_Closed_def One_in_Set_def; blast)

definition sep_closed_image :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> 'a sep_closed_set \<Rightarrow> 'b sep_closed_set\<close> (infixr "`\<^sub>S" 90)
  where \<open>(f `\<^sub>S S) = sep_closed_set (f ` dest_sep_closed_set S) \<close>

(*
definition Homo_Sep_Closed :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> bool\<close>
  where \<open>Homo_Sep_Closed f \<longleftrightarrow> (\<forall>S. Sep_Closed S \<longrightarrow> Sep_Closed (f ` S))\<close>

lemma in_image_sep_closed[simp]:
  \<open>Homo_Sep_Closed f \<Longrightarrow> x \<in>\<^sub>S f `\<^sub>S S \<longleftrightarrow> (\<exists>x'. x = f x' \<and> x' \<in>\<^sub>S S)\<close>
  by (smt (verit, del_insts) Homo_Sep_Closed_def  dest_sep_closed_set dest_sep_closed_set_inverse image_iff in_sep_closed_set mem_Collect_eq sep_closed_image_def)
*)

subsubsection \<open>Common Sep-Closed Sets\<close>

lemma sep_closed_partial_map[simp]:
  \<open>Sep_Closed {vars. finite (dom vars)}\<close>
  unfolding Sep_Closed_def
  by (clarsimp simp add: dom_mult)

lemma sep_closed_partial_map1[simp]:
  \<open>Sep_Closed {h::'a \<Rightarrow> 'b :: sep_no_inverse. finite (dom1 h)}\<close> 
  unfolding Sep_Closed_def
  by (clarsimp simp add: dom1_mult)

lemma Sep_Closed_pointwise:
  \<open> (\<forall>k. P k 1)
\<Longrightarrow> (\<forall>k x y. x ## y \<longrightarrow> P k x \<and> P k y \<longrightarrow> P k (x * y))
\<Longrightarrow>   Sep_Closed {f. \<forall>k. P k (f k) }\<close>
  unfolding Sep_Closed_def
  by (simp add: times_fun; blast)


subsection \<open>Separation Homo Set\<close>

definition Sep_Homo :: \<open>'a::sep_magma_1 set \<Rightarrow> bool\<close>
  where \<open>Sep_Homo S \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> (x * y) \<in> S \<longleftrightarrow> x \<in> S \<and> y \<in> S) \<and> 1 \<in> S\<close>

lemma Sep_Homo_inter:
  \<open>Sep_Homo S1 \<Longrightarrow> Sep_Homo S2 \<Longrightarrow> Sep_Homo (S1 \<inter> S2)\<close>
  unfolding Sep_Homo_def by blast

lemma Sep_Homo_UNIV[simp]:
  \<open>Sep_Homo UNIV\<close>
  unfolding Sep_Homo_def by simp

typedef (overloaded) ('a::sep_magma_1) sep_homo_set = \<open>Collect (Sep_Homo::'a set \<Rightarrow> bool)\<close>
  morphisms dest_sep_homo_set sep_homo_set
  unfolding Sep_Homo_def by blast

setup_lifting type_definition_sep_homo_set

lift_definition sep_homo_member :: \<open>'a::sep_magma_1 \<Rightarrow> 'a sep_homo_set \<Rightarrow> bool\<close> (infix "\<in>\<^sub>S\<^sub>H" 50)
  is \<open>\<lambda>x S. x \<in> S\<close> .

lemma in_sep_homo_set[simp]:
  \<open>Sep_Homo S \<Longrightarrow> x \<in>\<^sub>S\<^sub>H sep_homo_set S \<longleftrightarrow> x \<in> S\<close>
  unfolding sep_homo_member_def
  by (simp add: sep_homo_set_inverse)

lemma one_in_sep_homo_set[simp]:
  \<open>1 \<in>\<^sub>S\<^sub>H S\<close> for S :: \<open>'a::sep_magma_1 sep_homo_set\<close>
  by (transfer; simp add: Sep_Homo_def)

lemma mult_in_sep_homo_set[simp]:
  \<open>x ## y \<Longrightarrow> x * y \<in>\<^sub>S\<^sub>H S \<longleftrightarrow> x \<in>\<^sub>S\<^sub>H S \<and> y \<in>\<^sub>S\<^sub>H S\<close> for S :: \<open>'a::sep_algebra sep_homo_set\<close>
  by (transfer; simp add: Sep_Homo_def)

lift_definition sep_homo_inter :: \<open>'a::sep_magma_1 sep_homo_set \<Rightarrow> 'a sep_homo_set \<Rightarrow> 'a sep_homo_set\<close> (infixl "\<inter>\<^sub>S\<^sub>H" 65)
  is \<open>\<lambda>S1 S2. S1 \<inter> S2\<close>
  by (clarsimp simp add: Sep_Homo_def; blast)

definition sep_homo_image :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> 'a sep_homo_set \<Rightarrow> 'b sep_homo_set\<close> (infixr "`\<^sub>S\<^sub>H" 90)
  where \<open>(f `\<^sub>S\<^sub>H S) = sep_homo_set (f ` dest_sep_homo_set S) \<close>

definition Homo_Sep_Homo :: \<open>('a::sep_algebra \<Rightarrow> 'b::sep_algebra) \<Rightarrow> bool\<close>
  where \<open>Homo_Sep_Homo f \<longleftrightarrow> (\<forall>S. Sep_Homo S \<longrightarrow> Sep_Homo (f ` S))\<close>

lemma in_image_sep_homo[simp]:
  \<open>Homo_Sep_Homo f \<Longrightarrow> x \<in>\<^sub>S\<^sub>H f `\<^sub>S\<^sub>H S \<longleftrightarrow> (\<exists>x'. x = f x' \<and> x' \<in>\<^sub>S\<^sub>H S)\<close>
  by (smt (verit, best) Homo_Sep_Homo_def dest_sep_homo_set dest_sep_homo_set_inverse image_iff in_sep_homo_set mem_Collect_eq sep_homo_image_def)
  
subsubsection \<open>Common Sep-Homo Sets\<close>

lemma sep_homo_partial_map[simp]:
  \<open>Sep_Homo {vars. finite (dom vars)}\<close>
  unfolding Sep_Homo_def
  by (clarsimp simp add: dom_mult)

lemma sep_homo_partial_map1[simp]:
  \<open>Sep_Homo {h::'a \<Rightarrow> 'b :: sep_no_inverse. finite (dom1 h)}\<close> 
  unfolding Sep_Homo_def
  by (clarsimp simp add: dom1_mult)

lemma Sep_Homo_pointwise:
  \<open> (\<forall>k. P k 1)
\<Longrightarrow> (\<forall>k x y. x ## y \<longrightarrow> P k (x * y) \<longleftrightarrow> P k x \<and> P k y)
\<Longrightarrow>   Sep_Homo {f. \<forall>k. P k (f k) }\<close>
  unfolding Sep_Homo_def
  by (simp add: times_fun; blast)



end