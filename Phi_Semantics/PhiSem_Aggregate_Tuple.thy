theory PhiSem_Aggregate_Tuple
  imports PhiSem_Aggregate_Base
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype tuple_ty =
  tup     :: \<open>'self list\<close>

debt_axiomatization T_tup :: \<open>TY list type_entry\<close>
  where tuple_ty_ax: \<open>tuple_ty TY_CONS_OF T_tup\<close>

interpretation tuple_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_tup using tuple_ty_ax .

(*TODO: intergrate automatic hidding into the automation command*)
hide_fact tuple_ty_ax

subsubsection \<open>Value\<close>

virtual_datatype tuple_val =
  V_tup     :: \<open>'self list\<close>

debt_axiomatization V_tup :: \<open>VAL list value_entry\<close>
  where tuple_val_ax: \<open>tuple_val VAL_CONS_OF V_tup\<close>

interpretation tuple_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_tup
  using tuple_val_ax .

hide_fact tuple_val_ax

abbreviation \<open>tup \<equiv> tup.mk\<close>

term \<open>tuple(a, b, c, d)\<close>

subsection \<open>Semantics\<close>

debt_axiomatization
        WT_tup[simp]: \<open>Well_Type (tup ts)  = { V_tup.mk vs       |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
  and   zero_tup[simp]: \<open>Zero (tup Ts)     = map_option V_tup.mk (those (map Zero Ts))\<close>
  and   V_tup_sep_disj_R[simp]: \<open>V_tup.mk l1 ## vl2 \<longleftrightarrow> (\<exists>l2. vl2 = V_tup.mk l2)\<close>
  and   V_tup_sep_disj_L[simp]: \<open>vl1 ## V_tup.mk l2 \<longleftrightarrow> (\<exists>l1. vl1 = V_tup.mk l1)\<close>
  and   V_tup_mult    : \<open>V_tup.mk l1 * V_tup.mk l2 = V_tup.mk (l2 @ l1)\<close>
  and   idx_step_type_tup [eval_aggregate_path] : \<open>i < length tys \<Longrightarrow> idx_step_type (AgIdx_N i) (tup tys) = tys!i \<close>
  and   valid_idx_step_tup[eval_aggregate_path] : \<open>valid_idx_step (tup tys) j \<longleftrightarrow> j \<in> {AgIdx_N i | i. i < length tys}\<close>
  and   idx_step_value_tup[eval_aggregate_path] : \<open>idx_step_value (AgIdx_N i) (V_tup.mk vs) = vs!i\<close>
  and   idx_step_mod_value_tup : \<open>idx_step_mod_value (AgIdx_N i) f (V_tup.mk vs) = V_tup.mk (vs[i := f (vs!i)])\<close>

lemma V_tup_mult_cons:
  \<open>NO_MATCH vs ([]::VAL list) \<Longrightarrow> V_tup.mk (v#vs) = V_tup.mk vs * V_tup.mk [v]\<close>
  using V_tup_mult by simp

lemma list_all_replicate:
  \<open>list_all P (replicate n x) \<longleftrightarrow> n = 0 \<or> P x\<close>
  by (induct n; simp; blast)

(* lemma Valid_Type_\<tau>Tuple[simp]:
  \<open>Valid_Type (tup Ts) \<longleftrightarrow> list_all Valid_Type Ts\<close>
  unfolding Inhabited_def
  by (simp; induct Ts; simp add: list_all2_Cons1) *)

section \<open>\<phi>Type\<close>

subsection \<open>Empty Tuple\<close>

definition Empty_Tuple :: \<open>(VAL, unit) \<phi>\<close>
  where \<open>Empty_Tuple x = { V_tup.mk [] }\<close>

\<phi>adhoc_overloading \<phi>_Empty_Tuple_sugar Empty_Tuple

lemma EmptyTuple_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> Empty_Tuple) \<longleftrightarrow> p = V_tup.mk []\<close>
  unfolding Empty_Tuple_def \<phi>Type_def by simp

subsection \<open>Field\<close>

definition Tuple_Field :: "(VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>"
  where "Tuple_Field T x = { V_tup.mk [v] |v. v \<in> T x }"

syntax "\<phi>_tuple_" :: \<open>logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_")

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_tuple_ X))" \<rightleftharpoons> "CONST Tuple_Field X"

lemma Tuple_Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<lbrace> T \<rbrace>) \<longleftrightarrow> (\<exists>v. p = V_tup.mk [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding Tuple_Field_def \<phi>Type_def by simp

lemma Tuple_Field_inhabited[elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> \<lbrace> T \<rbrace>) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Empty_Tuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> Empty_Tuple \<^emph> \<lbrace> T \<rbrace>) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  \<open>((a,()) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> Empty_Tuple) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding set_eq_iff
  apply (clarsimp; rule; clarsimp simp add: \<phi>expns V_tup_mult)
  apply (metis V_tup_mult append_Nil)
  apply (clarsimp; rule; clarsimp simp add: \<phi>expns V_tup_mult)
  by (metis V_tup_mult append.right_neutral)

lemma Tuple_Field_zero  [\<phi>reason 1000]:
  \<open>\<phi>Zero ty T x \<Longrightarrow> \<phi>Zero (tup [ty]) \<lbrace> T \<rbrace> x \<close>
  unfolding \<phi>Zero_def by (clarsimp simp add: \<phi>expns)

lemma Tuple_Field_zeros [\<phi>reason 1000]:
  \<open>\<phi>Zero ty T x
    \<Longrightarrow> \<phi>Zero (tup tys) Ts xs
    \<Longrightarrow> \<phi>Zero (tup (ty#tys)) (\<lbrace> T \<rbrace> \<^emph> Ts) (x,xs) \<close>
  unfolding \<phi>Zero_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult_cons image_iff)
  using V_tup_sep_disj_L by blast

lemma Tuple_Field_semty[\<phi>reason 1000]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<lbrace> T \<rbrace>) (tup [TY])\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp simp add: \<phi>expns)

lemma Tuple_Field_semtys[\<phi>reason 1000]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (xs \<Ztypecolon> Ts) (tup TYs)
\<Longrightarrow> \<phi>SemType ((x,xs) \<Ztypecolon> (\<lbrace> T \<rbrace> \<^emph> Ts)) (tup (TY#TYs))\<close>
  unfolding \<phi>SemType_def subset_iff
  apply (clarsimp simp add: \<phi>expns)
  by (metis V_tup_mult append.left_neutral append_Cons list.rel_inject(2))



section \<open>Reasoning\<close>

subsection \<open>Show validity of an index for a type\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 1200]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i < length Tys
\<Longrightarrow> Simplify eval_aggregate_path Ty (Tys!i) 
\<Longrightarrow> valid_index Ty L
\<Longrightarrow> valid_index (tup Tys) (AgIdx_N i # L)\<close>
  unfolding Premise_def Simplify_def
  by (simp add: valid_idx_step_tup idx_step_type_tup)

subsection \<open>Index\<close>

lemma idx_step_value_V_tup_suc:
  \<open>idx_step_value (AgIdx_N (Suc i)) (V_tup.mk (va # vs)) = idx_step_value (AgIdx_N i) (V_tup.mk vs)\<close>
  by (simp add: idx_step_value_tup)

lemma idx_step_mod_value_V_tup_suc:
  \<open>idx_step_mod_value (AgIdx_N (Suc i)) g (V_tup.mk (va # vs)) = idx_step_mod_value (AgIdx_N i) g (V_tup.mk vs) * V_tup.mk [va]\<close>
  by (metis NO_MATCH_I V_tup_mult_cons idx_step_mod_value_tup list_update_code(3) nth_Cons_Suc)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_getter (AgIdx_N i # idx) X Y f
\<Longrightarrow> \<phi>Index_getter (AgIdx_N (Suc i) # idx) (\<lbrace> T \<rbrace> \<^emph> X) Y (f o snd)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_V_tup_suc)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (AgIdx_N 0 # idx) \<lbrace> X \<rbrace> Y f\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (AgIdx_N 0 # idx) (\<lbrace> X \<rbrace> \<^emph> R) Y (f o fst)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_mapper (AgIdx_N i # idx) X X' Y Y' f
\<Longrightarrow> \<phi>Index_mapper (AgIdx_N (Suc i) # idx) (\<lbrace> T \<rbrace> \<^emph> X) (\<lbrace> T \<rbrace> \<^emph> X') Y Y' (apsnd o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_V_tup_suc)
  by (metis V_tup_sep_disj_R idx_step_mod_value_tup)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Index_mapper (AgIdx_N 0 # idx) \<lbrace> X \<rbrace> \<lbrace> X' \<rbrace> Y Y' f\<close>
  unfolding \<phi>Index_mapper_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)

lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Index_mapper (AgIdx_N 0 # idx) (\<lbrace> X \<rbrace> \<^emph> R) (\<lbrace> X' \<rbrace> \<^emph> R) Y Y' (apfst o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)
  by (metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L)

end