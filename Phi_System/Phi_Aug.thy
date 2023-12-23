theory Phi_Aug \<comment> \<open>Augmenting to the Standard Library\<close>
  imports Main
begin

section \<open>List\<close>

subsection \<open>Combinators\<close>

lemma fun_comp_intr_left[no_atp]:
  \<open>f = g \<Longrightarrow> x o f = x o g\<close>
  by simp

setup \<open>Sign.mandatory_path "comb"\<close>

definition \<open>K x = (\<lambda>_. x)\<close> \<comment> \<open>to improve the performance as any lambda expression \<open>\<lambda>_. x\<close> is not
  cached within the internal system of Isabelle.\<close>

lemma K_app[simp]:
  \<open> comb.K x y = x \<close>
  unfolding comb.K_def ..

lemma K_comp[simp]:
  \<open> comb.K x o f = comb.K x \<close>
  unfolding fun_eq_iff comb.K_def
  by simp

lemmas K_comp'[simp] = comb.K_comp[THEN fun_comp_intr_left, folded comp_assoc]
  

setup \<open>Sign.parent_path\<close>

subsection \<open>Length Preserving Map\<close>

definition length_preserving_map :: \<open>'a list set \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> bool\<close>
  where \<open>length_preserving_map D f \<longleftrightarrow> (\<forall>l \<in> D. length (f l) = length l)\<close>

lemma length_preserving_map__map[simp, intro!]:
  \<open> length_preserving_map D (map f) \<close>
  unfolding length_preserving_map_def
  by simp 

lemma length_preserving_map__id[simp, intro!]:
  \<open> length_preserving_map D id \<close>
  unfolding length_preserving_map_def by simp

lemma length_preserving_map__id'[simp, intro!]:
  \<open> length_preserving_map D (\<lambda>x. x) \<close>
  unfolding length_preserving_map_def by simp

lemma length_preserving_map__funcomp[simp, intro!]:
  \<open> length_preserving_map (g ` D) f
\<Longrightarrow> length_preserving_map D g
\<Longrightarrow> length_preserving_map D (f o g) \<close>
  unfolding length_preserving_map_def
  by clarsimp

lemma length_preserving_map_comb_K[simp, intro!]:
  \<open> length_preserving_map D (comb.K xs) = (\<forall>x\<in>D. length xs = length x) \<close> 
  unfolding length_preserving_map_def
  by clarsimp


subsection \<open>Mapping at a single element\<close>

definition list_upd_map :: \<open>nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where \<open>list_upd_map i f l = l[i := f (l ! i)]\<close>

lemma length_preserving_map__list_upd_map [simp, intro!]:
  \<open> length_preserving_map D (list_upd_map i f) \<close>
  unfolding length_preserving_map_def list_upd_map_def
  by force

lemma list_upd_map_const_f[simp]:
  \<open> list_upd_map i (\<lambda>x. v) xs = xs[i := v] \<close>
  unfolding list_upd_map_def ..

lemma list_upd_map_0_eval[simp]:
  \<open> list_upd_map 0 f (h # l) = (f h # l) \<close>
  unfolding list_upd_map_def
  by simp

lemma list_upd_map_N_eval[simp]:
  \<open> list_upd_map (numeral n) f (h # l) = (h # list_upd_map (numeral n - 1) f l) \<close>
  unfolding list_upd_map_def
  by simp

lemma list_upd_map_Suc_eval[simp]:
  \<open> list_upd_map (Suc n) f (h # l) = (h # list_upd_map n f l) \<close>
  unfolding list_upd_map_def
  by simp

lemma length_list_upd_map[iff]:
  \<open> length (list_upd_map i f l) = length l \<close>
  unfolding list_upd_map_def
  by clarsimp

lemma take_list_upd_map_le[simp]:
  \<open> i \<le> j
\<Longrightarrow> take j (list_upd_map i f l) = list_upd_map i f (take j l) \<close>
  unfolding list_upd_map_def
  by (metis nth_take order_le_imp_less_or_eq take_update_cancel take_update_swap)

lemma take_list_upd_map_gt[simp]:
  \<open> j < i
\<Longrightarrow> take j (list_upd_map i f l) = take j l \<close>
  unfolding list_upd_map_def
  by simp

lemma drop_list_upd_map_lt[simp]:
  \<open> i < j
\<Longrightarrow> drop j (list_upd_map i f l) = drop j l \<close>
  unfolding list_upd_map_def
  by simp

lemma drop_list_upd_map_ge[simp]:
  \<open> j \<le> i
\<Longrightarrow> drop j (list_upd_map i f l) = list_upd_map (i-j) f (drop j l) \<close>
  unfolding list_upd_map_def
  by (metis Nat.add_diff_assoc add_diff_cancel_left' drop_all drop_update_swap length_list_update less_imp_le_nat linorder_not_le nth_drop)
  


subsection \<open>Mapping Prefix / Suffix\<close>

definition sublist_map_L :: \<open>nat \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  \<comment> \<open>applies on the left N elements\<close>
  where \<open>sublist_map_L N f l = f (take N l) @ drop N l\<close>

definition sublist_map_R :: \<open>nat \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  \<comment> \<open>applies on the right (len-N) elements\<close>
  where \<open>sublist_map_R N f l = take N l @ f (drop N l)\<close>

lemma length_preserving_map__sublist_map_R [simp, intro!]:
  \<open> length_preserving_map (drop N ` D) f
\<Longrightarrow> length_preserving_map D (sublist_map_R N f) \<close>
  unfolding length_preserving_map_def sublist_map_R_def
  by (clarify, simp)

lemma length_preserving_map__sublist_map_L [simp, intro!]:
  \<open> length_preserving_map (take N ` D) f
\<Longrightarrow> length_preserving_map D (sublist_map_L N f) \<close>
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
  \<open> length_preserving_map UNIV f
\<Longrightarrow> length_preserving_map UNIV g
\<Longrightarrow> sublist_map_L N (f o g) = sublist_map_L N f o sublist_map_L N g \<close>
  unfolding sublist_map_L_def fun_eq_iff length_preserving_map_def
  by (clarsimp simp add: min_def)

lemma sublist_map_R_sublist_map_R[simp]:
  \<open> sublist_map_R N (sublist_map_R M f) = sublist_map_R (N+M) f \<close>
  unfolding sublist_map_R_def
  by (clarsimp, metis add.commute append_assoc take_add)

lemma sublist_map_R_funcomp[simp]:
  \<open> length_preserving_map UNIV f
\<Longrightarrow> length_preserving_map UNIV g
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



section \<open>Option\<close>

definition zip_option :: \<open>'a option \<times> 'b option \<Rightarrow> ('a \<times> 'b) option\<close>
  where \<open>zip_option xy = (case xy of (Some x, Some y) \<Rightarrow> Some (x,y)
                                   | _ \<Rightarrow> None)\<close>

lemma zip_option_simps[iff]:
  \<open> zip_option (Some a, Some b) = Some (a,b) \<close>
  \<open> zip_option (x, None) = None \<close>
  \<open> zip_option (None, y) = None \<close>
  unfolding zip_option_def
  by (simp_all, cases x, simp+)


section \<open>Partial Map\<close>

definition zip_partial_map :: \<open>('a \<rightharpoonup> 'b) \<times> ('a \<rightharpoonup> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b \<times> 'c)\<close>
  where \<open>zip_partial_map x = (case x of (f,g) \<Rightarrow> (\<lambda>k. zip_option (f k, g k)))\<close>

definition unzip_partial_map :: \<open>('a \<rightharpoonup> 'b \<times> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b) \<times> ('a \<rightharpoonup> 'c)\<close>
  where \<open>unzip_partial_map x = (map_option fst o x, map_option snd o x)\<close>

lemma unzip_zip_partial_map[iff]:
  \<open> dom (fst x) = dom (snd x)
\<Longrightarrow> unzip_partial_map (zip_partial_map x) = x \<close>
  unfolding unzip_partial_map_def zip_partial_map_def
  by (cases x; clarsimp simp: fun_eq_iff zip_option_def split: option.split; metis domIff)

end