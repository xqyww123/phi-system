theory Map_of_Tree
  imports Main Fictional_Algebra
begin

section \<open>Map Representation of a Tree\<close>

text \<open>This section presents a representation of tree using the mapping from path to value,
    typically of type \<^typ>\<open>nat list \<Rightarrow> 'x\<close>.
  Basic operations include `push_map` and `pull_map` which put a sub-tree onto certain location
    and fetch a sub-tree at certain location respectively.
  It also includes scalar operation `share` which may be used to get sub-permission copies.\<close>

subsection \<open>Push a map to a location\<close>

definition push_map :: \<open>'a list \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> ('a list \<Rightarrow> 'b::one)\<close>
  where \<open>push_map idx f = (\<lambda>x. if take (length idx) x = idx then f (drop (length idx) x) else 1 )\<close>

lemma push_map_unit[simp]:
  \<open>push_map ia (1(ib := x)) = 1(ia@ib := x)\<close>
  unfolding push_map_def
  by (simp add: fun_eq_iff, metis append_eq_conv_conj)

lemma push_map_push_map:
  \<open>push_map ia (push_map ib f) = push_map (ia@ib) f\<close>
  unfolding push_map_def fun_eq_iff
  by (smt (verit, ccfv_threshold) add.commute append_eq_append_conv append_eq_conv_conj drop_drop length_append take_add take_drop)

lemma push_map_distrib_mult:
  \<open>push_map idx f * push_map idx g = push_map idx (f * g)\<close>
  for f :: \<open>'a list \<Rightarrow> 'b::monoid_mult\<close>
  unfolding push_map_def fun_eq_iff times_fun_def by simp

lemma push_map_distrib_map_add:
  \<open>push_map idx (f ++ g) = push_map idx f ++ push_map idx g\<close>
  unfolding push_map_def fun_eq_iff map_add_def by simp

lemma push_map_sep_disj[simp]:
  \<open>push_map idx a ## push_map idx b \<longleftrightarrow> a ## b\<close>
  for a :: \<open>'k list \<Rightarrow> 'v::sep_disj_one\<close>
  unfolding sep_disj_fun_def push_map_def apply simp
  by (metis append_eq_conv_conj)

lemma push_map_eq_1[simp]:
  \<open>push_map idx f = 1 \<longleftrightarrow> f = 1\<close>
  unfolding push_map_def fun_eq_iff by simp (metis append_eq_conv_conj)

lemma push_map_1[simp]:
  \<open>push_map idx 1 = 1\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_mult_nil[simp]:
  \<open>push_map [] f = f\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma share_push_map:
  \<open>share n (push_map idx f) = push_map idx (share n f)\<close>
  for f :: \<open>'a list \<Rightarrow> 'b :: share_one\<close>
  unfolding push_map_def fun_eq_iff share_fun_def by simp

lemma (in homo_one) push_map_homo:
  \<open>\<phi> o (push_map idx f) = push_map idx (\<phi> o f)\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_to_share:
  \<open>push_map idx (to_share o f) = to_share o (push_map idx f)\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_dom_eq[simp]:
  \<open>dom (push_map idx f) = dom (push_map idx g) \<longleftrightarrow> dom f = dom g\<close>
  unfolding dom_def fun_eq_iff push_map_def set_eq_iff apply simp
  by (metis (full_types) append_eq_conv_conj)


subsection \<open>Pull a map at a location\<close>

definition pull_map :: \<open>'a list \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> ('a list \<Rightarrow> 'b)\<close>
  where \<open>pull_map idx f = (\<lambda>x. f (idx@x))\<close>

lemma pull_map_unit[simp]:
  \<open>pull_map ia (1((ia@ib) := x)) = 1(ib := x)\<close>
  unfolding pull_map_def by (simp add: fun_eq_iff)

lemma pull_push_map[simp]:
  \<open>pull_map idx (push_map idx f) = f\<close>
  unfolding pull_map_def push_map_def fun_eq_iff by simp

lemma push_pull_map:
  \<open>push_map idx (pull_map idx f) \<subseteq>\<^sub>m f\<close>
  unfolding pull_map_def push_map_def map_le_def dom_def
  by simp (metis append_take_drop_id)

lemma pull_map_1[simp]:
  \<open>pull_map idx 1 = 1\<close> 
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_0[simp]:
  \<open>pull_map idx 0 = 0\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_nil[simp]:
  \<open>pull_map [] f = f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_pull_map[simp]:
  \<open>pull_map a (pull_map b f) = pull_map (b@a) f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_cons:
  \<open>pull_map a (pull_map [b] f) = pull_map (b#a) f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_funcomp:
  \<open>\<phi> 1 = 1 \<Longrightarrow> \<phi> o (pull_map idx f) = pull_map idx (\<phi> o f)\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_homo_mult:
  \<open>pull_map idx (f * g) = pull_map idx f * pull_map idx g\<close>
  unfolding pull_map_def fun_eq_iff
  by (simp add: times_fun)

lemma pull_map_to_share:
  \<open>pull_map idx (to_share o f) = to_share o (pull_map idx f)\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_share:
  \<open>pull_map idx (share n f) = share n (pull_map idx f)\<close>
  unfolding pull_map_def fun_eq_iff share_fun_def by simp

lemma pull_map_sep_disj[simp]:
  \<open>f ## g \<Longrightarrow> pull_map idx f ## pull_map idx g\<close>
  unfolding pull_map_def sep_disj_fun_def by simp


subsection \<open>Tree Node\<close>

definition node :: \<open>(nat list \<Rightarrow> 'b) list \<Rightarrow> nat list \<Rightarrow> 'b::one\<close>
  \<comment> \<open>A tree node of children L\<close>
  where \<open>node L = (\<lambda>idx. case idx of i#idx' \<Rightarrow> (if i < length L then (L!i) idx' else 1) | _ \<Rightarrow> 1)\<close>

lemma share_node:
  \<open>share n (node L) = node (map (share n) L)\<close>
  for L :: \<open>(nat list \<Rightarrow> 'a::share_one) list\<close>
  unfolding node_def fun_eq_iff by (simp add: share_fun_def split: list.split)

lemma pull_map_node:
  \<open>pull_map (i#idx) (node L) = (if i < length L then pull_map idx (L!i) else 1)\<close>
  unfolding node_def pull_map_def fun_eq_iff by simp




end