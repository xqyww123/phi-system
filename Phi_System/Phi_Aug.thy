theory Phi_Aug \<comment> \<open>Augmenting to the Standard Library\<close>
  imports Main
begin

section \<open>List\<close>

subsection \<open>Length Preserving Map\<close>

definition length_preserving_map :: \<open>('a list \<Rightarrow> 'a list) \<Rightarrow> bool\<close>
  where \<open>length_preserving_map f \<longleftrightarrow> (\<forall>l. length (f l) = length l)\<close>

lemma length_preserving_map__map[simp, intro!]:
  \<open> length_preserving_map (map f) \<close>
  unfolding length_preserving_map_def
  by simp 

lemma length_preserving_map__id[simp, intro!]:
  \<open> length_preserving_map id \<close>
  unfolding length_preserving_map_def by simp

lemma length_preserving_map__id'[simp, intro!]:
  \<open> length_preserving_map (\<lambda>x. x) \<close>
  unfolding length_preserving_map_def by simp

lemma length_preserving_map__funcomp[simp, intro!]:
  \<open> length_preserving_map f
\<Longrightarrow> length_preserving_map g
\<Longrightarrow> length_preserving_map (f o g) \<close>
  unfolding length_preserving_map_def
  by clarsimp

subsection \<open>Mapping at a single element\<close>

definition list_upd_map :: \<open>nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where \<open>list_upd_map i f l = l[i := f (l ! i)]\<close>

lemma length_preserving_map__list_upd_map [simp, intro!]:
  \<open> length_preserving_map (list_upd_map i f) \<close>
  unfolding length_preserving_map_def list_upd_map_def
  by force

lemma list_upd_map_const_f[simp]:
  \<open> list_upd_map i (\<lambda>x. v) xs = xs[i := v] \<close>
  unfolding list_upd_map_def ..


subsection \<open>Mapping Prefix / Suffix\<close>

definition sublist_map_L :: \<open>nat \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  \<comment> \<open>applies on the left N elements\<close>
  where \<open>sublist_map_L N f l = f (take N l) @ drop N l\<close>

definition sublist_map_R :: \<open>nat \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  \<comment> \<open>applies on the right (len-N) elements\<close>
  where \<open>sublist_map_R N f l = take N l @ f (drop N l)\<close>

lemma length_preserving_map__sublist_map_R [simp, intro!]:
  \<open> length_preserving_map f
\<Longrightarrow> length_preserving_map (sublist_map_R N f) \<close>
  unfolding length_preserving_map_def sublist_map_R_def
  by (clarify, simp)

lemma length_preserving_map__sublist_map_L [simp, intro!]:
  \<open> length_preserving_map f
\<Longrightarrow> length_preserving_map (sublist_map_L N f) \<close>
  unfolding length_preserving_map_def
  by (clarify, simp add: sublist_map_L_def)

lemma sublist_map_L_id[simp]:
  \<open> sublist_map_L N id = id \<close>
  unfolding fun_eq_iff sublist_map_L_def
  by clarsimp

lemma sublist_map_L_id'[simp]:
  \<open> sublist_map_L N (\<lambda>x. x) = (\<lambda>x. x) \<close>
  unfolding fun_eq_iff sublist_map_L_def
  by clarsimp

lemma sublist_map_R_id[simp]:
  \<open> sublist_map_R N id = id \<close>
  unfolding sublist_map_R_def fun_eq_iff
  by clarsimp

lemma sublist_map_R_id'[simp]:
  \<open> sublist_map_R N (\<lambda>x. x) = (\<lambda>x. x) \<close>
  unfolding sublist_map_R_def fun_eq_iff
  by clarsimp

lemma sublist_map_L_sublist_map_L[simp]:
  \<open> M \<le> N
\<Longrightarrow> sublist_map_L N (sublist_map_L M f) = sublist_map_L M f \<close>
  unfolding sublist_map_L_def
  by (clarsimp, metis (no_types, opaque_lifting) append_take_drop_id diff_add drop_drop take_drop)

lemma sublist_map_L_funcomp[simp]:
  \<open> length_preserving_map f
\<Longrightarrow> length_preserving_map g
\<Longrightarrow> sublist_map_L N (f o g) = sublist_map_L N f o sublist_map_L N g \<close>
  unfolding sublist_map_L_def fun_eq_iff length_preserving_map_def
  by (clarsimp simp add: min_def)

lemma sublist_map_R_sublist_map_R[simp]:
  \<open> sublist_map_R N (sublist_map_R M f) = sublist_map_R (N+M) f \<close>
  unfolding sublist_map_R_def
  by (clarsimp, metis add.commute append_assoc take_add)

lemma sublist_map_R_funcomp[simp]:
  \<open> length_preserving_map f
\<Longrightarrow> length_preserving_map g
\<Longrightarrow> sublist_map_R N (f o g) = sublist_map_R N f o sublist_map_R N g \<close>
  unfolding sublist_map_R_def length_preserving_map_def fun_eq_iff
  by (clarsimp, metis (no_types, opaque_lifting) append_Nil append_take_drop_id cancel_comm_monoid_add_class.diff_cancel diff_le_self drop_all list.size(3) min_def take0)

lemma sublist_map_L_at_i[simp]:
  \<open> i < N
\<Longrightarrow> sublist_map_L N (list_upd_map i f) = list_upd_map i f\<close>
  unfolding fun_eq_iff sublist_map_L_def list_upd_map_def
  by (clarsimp, metis append_take_drop_id drop_update_cancel take_update_swap)

lemma sublist_map_R_at_i[simp]:
  \<open> sublist_map_R N (list_upd_map i f) = list_upd_map (N+i) f\<close>
  unfolding fun_eq_iff sublist_map_R_def list_upd_map_def
  by (clarsimp,
      smt (verit) add_diff_cancel_left' append_take_drop_id drop_all length_take less_or_eq_imp_le linorder_not_less list_update_append list_update_nonempty min.absorb4 min_less_iff_conj not_add_less1 nth_drop)



end