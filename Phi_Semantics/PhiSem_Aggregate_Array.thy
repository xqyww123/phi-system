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

interpretation array_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_array using array_ty_ax .

hide_fact array_ty_ax

abbreviation \<open>array N T \<equiv> array.mk (T,N)\<close>



subsubsection \<open>Value\<close>

virtual_datatype array_val =
  V_array   :: \<open>'self list\<close>

debt_axiomatization V_array :: \<open>(VAL list) value_entry\<close>
  where array_val_ax: \<open>array_val VAL_CONS_OF V_array\<close>

interpretation array_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_array using array_val_ax .

hide_fact array_val_ax


subsection \<open>Semantics\<close>

debt_axiomatization
        WT_arr[simp]: \<open>Well_Type (array n t) = { V_array.mk vs |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs }\<close>
  and   zero_arr[simp]: \<open>Zero (array N T)  = map_option (\<lambda>z. V_array.mk (replicate N z)) (Zero T)\<close>
  and   idx_step_type_arr [eval_aggregate_path] : \<open>i < N \<Longrightarrow> idx_step_type (AgIdx_N i) (array N T) = T\<close>
  and   valid_idx_step_arr[eval_aggregate_path] : \<open>valid_idx_step (array N T) j \<longleftrightarrow> j \<in> {AgIdx_N i | i. i < N}\<close>
  and   idx_step_value_arr[eval_aggregate_path] : \<open>idx_step_value (AgIdx_N i) (V_array.mk vs) = vs!i\<close>
  and   idx_step_mod_value_arr : \<open>idx_step_mod_value (AgIdx_N i) f (V_array.mk vs) = V_array.mk (vs[i := f (vs!i)])\<close>

lemma list_all_replicate[simp]:
  \<open>list_all P (replicate n x) \<longleftrightarrow> n = 0 \<or> P x\<close>
  by (induct n; simp; blast)

(*lemma Valid_Type_\<tau>Array[simp]:
  \<open>Valid_Type (array n T) \<longleftrightarrow> Valid_Type T\<close>
  by (simp add: Inhabited_def;
      meson length_replicate list_all_replicat)*)

section \<open>\<phi>Type\<close>

declare [[\<phi>trace_reasoning = 0]]


\<phi>type_def Array :: "nat \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a list) \<phi>"
  where \<open>l \<Ztypecolon> Array N T \<equiv> V_array.mk vs \<Ztypecolon> Itself \<s>\<u>\<b>\<j> vs. length l = N \<and> list_all2 (\<lambda>v x. v \<Turnstile> (x \<Ztypecolon> T)) vs l\<close>
  deriving \<open>Abstract_Domain\<^sub>L T P
        \<Longrightarrow> Abstract_Domain\<^sub>L (Array N T) (\<lambda>x. length x = N \<and> list_all P x) \<close>
          (tactic: clarsimp ; subgoal' for x \<open>induct x arbitrary: N\<close>)
       and \<open>Abstract_Domain T P
        \<Longrightarrow> Abstract_Domain (Array N T) (\<lambda>x. length x = N \<and> list_all P x) \<close>
       and \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (Array N T) (list_all2 eq)\<close>
       and Transformation_Functor
           (tactic: clarsimp ; subgoal' for g x xb \<open>induct x arbitrary: xb xa N Na; auto simp add: list_all2_Cons2\<close>)
       and Functional_Transformation_Functor
       and \<open>Functionality T D
        \<Longrightarrow> Functionality (Array N T) (\<lambda>l. length l = N \<and> list_all D l)\<close>
           notes list_all2_conv_all_nth[simp] list_all_length[simp]
       and \<open>Is_Aggregate (Array N T)\<close>
       and \<open>\<forall>a \<in> set x. \<phi>SemType (a \<Ztypecolon> T) TY \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> Array N T) (array N TY)\<close>
       and \<open>Semantic_Zero_Val TY T zero \<Longrightarrow> Semantic_Zero_Val (array N TY) (Array N T) (replicate N zero)\<close>
           notes list_all2_conv_all_nth[simp] list_all_length[simp]



section \<open>Reasoning\<close>

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i < N
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N i) (array N TY) TY \<close>
  unfolding is_valid_step_idx_of_def Premise_def
  by (simp add: valid_idx_step_arr idx_step_type_arr)

subsection \<open>Index to Fields of Structures\<close>

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter idx X Y f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N i # idx) (Array N X) Y (\<lambda>l. f (l!i))\<close>
  unfolding \<phi>Aggregate_Getter_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp simp add: idx_step_value_arr list_all2_conv_all_nth)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper idx X X Y Y' f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N i # idx) (Array N X) (Array N X) Y Y' (\<lambda>g l. l[i := f g (l!i)])\<close>
  unfolding \<phi>Aggregate_Mapper_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp simp add: idx_step_mod_value_arr list_all2_conv_all_nth nth_list_update)




end