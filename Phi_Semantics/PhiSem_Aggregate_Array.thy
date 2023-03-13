theory PhiSem_Aggregate_Array
  imports PhiSem_Aggregate_Base
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype array_ty =
  array   :: \<open>'self \<times> nat\<close>

debt_axiomatization T_array :: \<open>(TY \<times> nat) type_entry\<close>
  where array_ty_ax: \<open>array_ty TY_CONS_OF T_array\<close>

interpretation array_ty TY_CONS_OF _ _ T_array using array_ty_ax .

hide_fact array_ty_ax

abbreviation \<open>array N T \<equiv> array.mk (T,N)\<close>


subsubsection \<open>Value\<close>

virtual_datatype array_val =
  V_array   :: \<open>'self list\<close>

debt_axiomatization V_array :: \<open>(VAL list) value_entry\<close>
  where array_val_ax: \<open>array_val VAL_CONS_OF V_array\<close>

interpretation array_val VAL_CONS_OF _ _ V_array using array_val_ax .

hide_fact array_val_ax


subsection \<open>Semantics\<close>

debt_axiomatization
        WT_arr[simp]: \<open>Well_Type (array n t) = { V_array.mk vs |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs }\<close>
  and   zero_arr[simp]: \<open>Zero (array N T)  = map_option (\<lambda>z. V_array.mk (replicate N z)) (Zero T)\<close>
  and   idx_step_type_arr [eval_semantic_index] : \<open>i \<le> N \<Longrightarrow> idx_step_type i (array N T) = T\<close>
  and   valid_idx_step_arr[eval_semantic_index] : \<open>valid_idx_step (array N T) i \<longleftrightarrow> i < N\<close>
  and   idx_step_value_arr[eval_semantic_index] : \<open>idx_step_value i (V_array.mk vs) = vs!i\<close>
  and   idx_step_mod_value_arr : \<open>idx_step_mod_value i f (V_array.mk vs) = V_array.mk (vs[i := f (vs!i)])\<close>

lemma list_all_replicate:
  \<open>list_all P (replicate n x) \<longleftrightarrow> n = 0 \<or> P x\<close>
  by (induct n; simp; blast)

(*lemma Valid_Type_\<tau>Array[simp]:
  \<open>Valid_Type (array n T) \<longleftrightarrow> Valid_Type T\<close>
  by (simp add: Inhabited_def;
      meson length_replicate list_all_replicat)*)


section \<open>\<phi>Type\<close>

definition Array :: "nat \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a list) \<phi>"
  where \<open>Array N T = (\<lambda>l. { V_array.mk vs |vs. length l = N \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l  })\<close>

lemma Array_expns[\<phi>expns]:
  \<open>v \<in> (l \<Ztypecolon> Array N T) \<longleftrightarrow>
    (\<exists>vs. length l = N \<and> v = V_array.mk vs \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l )\<close>
  unfolding Array_def \<phi>Type_def by simp blast

lemma Array_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open> Inhabited (l \<Ztypecolon> Array N T)
\<Longrightarrow> (length l = N \<Longrightarrow> (\<And>i. i < length l \<Longrightarrow> Inhabited (l!i \<Ztypecolon> T)) \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns list_all2_conv_all_nth) blast

lemma Array_semty[\<phi>reason 1000]:
  \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY) \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> Array N T) (array N TY)\<close>
  by (clarsimp simp add: \<phi>expns list_all_length list_all2_conv_all_nth \<phi>SemType_def subset_iff
          Inhabited_def, blast)

lemma Array_zero[\<phi>reason 1000]:
  \<open>\<phi>Zero TY T zero \<Longrightarrow> \<phi>\<phi>SemType T TY \<Longrightarrow> \<phi>Zero (array N TY) (Array N T) (replicate N zero)\<close>
  unfolding \<phi>Zero_def
  by (clarsimp simp add: \<phi>expns list_all2_conv_all_nth Inhabited_def image_iff; blast)


section \<open>Reasoning\<close>

subsection \<open>Index to Fields of Structures\<close>


lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
\<Longrightarrow> \<phi>Index_getter (i # idx) (Array N X) Y (\<lambda>l. f (l!i))\<close>
  unfolding \<phi>Index_getter_def Premise_def
  by (clarsimp simp add: \<phi>expns idx_step_value_arr list_all2_conv_all_nth)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_mapper idx X X Y Y' f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
\<Longrightarrow> \<phi>Index_mapper (i # idx) (Array N X) (Array N X) Y Y' (\<lambda>g l. l[i := f g (l!i)])\<close>
  unfolding \<phi>Index_mapper_def Premise_def
  by (clarsimp simp add: \<phi>expns idx_step_mod_value_arr list_all2_conv_all_nth nth_list_update)




end