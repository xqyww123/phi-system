theory PhiEx_BinTree_AbstModel
  imports Phi_System.IDE_CP_Core
          "HOL-Data_Structures.Tree_Map"
begin

section \<open>Common Operations\<close>

declare tree.rel_eq[simp]

declare [[ type_property tree
    selectors = [[], [left, "value", right]]
]]

lemma rel_tree_Leaf[\<phi>deriver_simps, iff]:
  \<open> rel_tree R \<langle>\<rangle> tree \<longleftrightarrow> tree = \<langle>\<rangle> \<close>
  \<open> rel_tree R tree' \<langle>\<rangle> \<longleftrightarrow> tree' = \<langle>\<rangle> \<close>
  by (auto_sledgehammer, auto_sledgehammer)

lemma rel_tree_Node1[\<phi>deriver_simps]:
  \<open> NO_MATCH \<langle>L', y, R'\<rangle> tree
\<Longrightarrow> rel_tree r \<langle>L, x, R\<rangle> tree \<longleftrightarrow> (\<exists>L' y R'. tree = \<langle>L', y, R'\<rangle> \<and> rel_tree r L L' \<and> r x y \<and> rel_tree r R R') \<close>
  by auto_sledgehammer

lemma rel_tree__pred_tree:
  \<open>rel_tree R x y \<Longrightarrow> pred_tree (\<lambda>x. \<exists>y. R x y) x\<close>
  by (induct x arbitrary: y; auto_sledgehammer)

lemma rel_tree_domain_eq:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> fst ` set_tree x = fst ` set_tree y \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1; auto_sledgehammer)

lemma rel_tree_self_map:
  \<open> \<forall>a \<in> set_tree x. R a (f a)
\<Longrightarrow> rel_tree R x (map_tree f x) \<close>
  by (induct x; auto_sledgehammer)

lemma rel_tree_height:
  \<open> rel_tree R x y
\<Longrightarrow> height x = height y \<close>
  by (induct x arbitrary: y; auto simp: rel_tree_Node1)

lemma AList_Upd_map_of_is_Map_map_of[iff]:
  \<open>map_of l = Map.map_of l\<close>
  by (induct l; auto)

section \<open>inorder\<close>

lemma rel_tree_implies_list_all2:
  \<open> rel_tree r x y \<Longrightarrow> list_all2 r (inorder x) (inorder y) \<close>
  by (induct x arbitrary: y; auto_sledgehammer)

lemma rel_tree__map_fst_eq:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> map fst (inorder x) = map fst (inorder y) \<close>
  by (induct x arbitrary: y;  auto_sledgehammer)

lemma sorted1_inorder_map_tree[iff]:
  \<open>sorted1 (inorder (map_tree (\<lambda>(k, v). (k, f k v)) tree)) \<longleftrightarrow> sorted1 (inorder tree)\<close>
  by auto_sledgehammer


section \<open>tree_domain_distinct\<close>

primrec tree_domain_distinct :: \<open>('k \<times> 'v) tree \<Rightarrow> bool\<close>
  where \<open>tree_domain_distinct \<langle>\<rangle> = True \<close>
      | \<open>tree_domain_distinct \<langle>L, x, R\<rangle> = (fst ` set_tree L \<inter> fst ` set_tree R = {} \<and>
                                           fst x \<notin> fst ` set_tree L \<and> fst x \<notin> fst ` set_tree R \<and>
                                           tree_domain_distinct L \<and> tree_domain_distinct R)\<close>

lemma tree_domain_distinct_map[iff]:
  \<open>tree_domain_distinct (Tree.tree.map_tree (\<lambda>(k, v). (k, f k v)) tree) \<longleftrightarrow> tree_domain_distinct tree\<close>
  by (induct tree; auto_sledgehammer)

lemma tree_domain_distinct__set_tree_inj:
  \<open> tree_domain_distinct tree
\<Longrightarrow> (k, v\<^sub>1) \<in> tree.set_tree tree
\<Longrightarrow> (k, v\<^sub>2) \<in> tree.set_tree tree
\<Longrightarrow> v\<^sub>1 = v\<^sub>2 \<close>
  by (induct tree; auto_sledgehammer)

lemma rel_tree_domain_distinct:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> tree_domain_distinct x \<longleftrightarrow> tree_domain_distinct y \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1; auto_sledgehammer)

section \<open>sorted\<close>

lemma tree_sorted1_inorder_implies_domain_distinct[simp]:
  \<open>sorted1(inorder tree) \<Longrightarrow> tree_domain_distinct tree\<close>
  by (induct tree; auto_sledgehammer)

lemma sorted1_left_tree_lt_node_value:
  \<open> sorted1 (inorder tree)
\<Longrightarrow> (k,v) \<in> set_tree (left tree)
\<Longrightarrow> k < fst (value tree) \<close>
  by (cases tree; auto_sledgehammer)

lemma sorted1_right_tree_gt_node_value:
  \<open> sorted1 (inorder tree)
\<Longrightarrow> (k,v) \<in> set_tree (right tree)
\<Longrightarrow> fst (value tree) < k \<close>
  by (cases tree; auto_sledgehammer)



section \<open>Lookup\<close>

primrec lookup_tree :: \<open>('k \<times> 'v) tree \<Rightarrow> 'k \<rightharpoonup> 'v\<close>
  where \<open>lookup_tree \<langle>\<rangle> = Map.empty\<close>
      | \<open>lookup_tree \<langle>L, x, R\<rangle> = (lookup_tree L ++ lookup_tree R)(fst x \<mapsto> snd x) \<close>

lemma dom_lookup_tree[iff]:
  \<open> dom (lookup_tree tree) = fst ` set_tree tree \<close>
  by (induct tree; auto_sledgehammer)

lemma lookup_tree_eq_empty:
  \<open> lookup_tree tree = Map.empty \<longleftrightarrow> tree = \<langle>\<rangle> \<close>
  by (induct tree; auto_sledgehammer)

lemma lookup_tree_by_set_distinct[simp]:
  \<open> tree_domain_distinct tree
\<Longrightarrow> lookup_tree tree k = Some v \<longleftrightarrow> (k, v) \<in> tree.set_tree tree\<close>
  by (induct tree; auto_sledgehammer)

lemma rel_map_lookup_by_rel_tree:
  \<open> rel_tree (\<lambda>a b. fst a = fst b \<and> r (snd a) (snd b)) x y
\<Longrightarrow> tree_domain_distinct x
\<Longrightarrow> rel_map r (lookup_tree x) (lookup_tree y) \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_fun_def rel_tree_Node1 split: option.split; auto_sledgehammer)

lemma rel_map_lookup_by_rel_tree2:
  \<open> rel_tree (\<lambda>a b. fst a = fst b \<and> r (snd (snd a)) (snd (snd b))) x y
\<Longrightarrow> tree_domain_distinct x
\<Longrightarrow> rel_map r (map_option snd o lookup_tree x) (map_option snd o lookup_tree y) \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_fun_def rel_tree_Node1 split: option.split; auto_sledgehammer)

lemma lookup_tree_map_tree[simp]:
  \<open> tree_domain_distinct tree
\<Longrightarrow> lookup_tree (map_tree (\<lambda>(k, v). (k, f k v)) tree) = (\<lambda>k. map_option (f k) (lookup_tree tree k)) \<close>
  unfolding fun_eq_iff
  by (induct tree; auto_sledgehammer)

lemma lookup_tree_map_tree2[simp]:
  \<open> tree_domain_distinct tree
\<Longrightarrow> lookup_tree (map_tree (\<lambda>(k, h, v). (k, f k h v)) tree) = (\<lambda>k. map_option (case_prod (f k)) (lookup_tree tree k)) \<close>
  using lookup_tree_map_tree[where f=\<open>case_prod o f\<close>, simplified]
  by (simp add: case_prod_beta')





end