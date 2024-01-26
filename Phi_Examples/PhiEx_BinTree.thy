theory PhiEx_BinTree
  imports Phi_Semantics.PhiSem_C
          "HOL-Data_Structures.Tree_Map"
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

section \<open>Abstract Model\<close>

subsection \<open>Common Operations\<close>

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

lemma rel_tree_conj_split:
  \<open> rel_tree (\<lambda>a b. R1 a b \<and> R2 a b) x y \<longleftrightarrow> rel_tree R1 x y \<and> rel_tree R2 x y \<close>
  by (induct x arbitrary: y; auto_sledgehammer)

lemma rel_tree_eq_norm:
  \<open> rel_tree (\<lambda>a b. f b = g a) x y \<longleftrightarrow> rel_tree (\<lambda>a b. g a = f b) x y \<close>
  by auto_sledgehammer

subsection \<open>tree_domain_distinct\<close>

primrec lookup_tree :: \<open>('k \<times> 'v) tree \<Rightarrow> 'k \<rightharpoonup> 'v\<close>
  where \<open>lookup_tree \<langle>\<rangle> = Map.empty\<close>
      | \<open>lookup_tree \<langle>L, x, R\<rangle> = (lookup_tree L ++ lookup_tree R)(fst x \<mapsto> snd x) \<close>


primrec tree_domain_distinct :: \<open>('k \<times> 'v) tree \<Rightarrow> bool\<close>
  where \<open>tree_domain_distinct \<langle>\<rangle> = True \<close>
      | \<open>tree_domain_distinct \<langle>L, x, R\<rangle> = (dom (lookup_tree L) \<inter> dom (lookup_tree R) = {} \<and>
                                           fst x \<notin> dom (lookup_tree L) \<and> fst x \<notin> dom (lookup_tree R) \<and>
                                           tree_domain_distinct L \<and> tree_domain_distinct R)\<close>

primrec sorted_lookup_tree :: \<open>('k::order \<times> 'v) tree \<Rightarrow> bool\<close>
  where \<open>sorted_lookup_tree \<langle>\<rangle> = True\<close>
      | \<open>sorted_lookup_tree \<langle>L, x, R\<rangle> \<longleftrightarrow> (\<forall>k \<in> dom (lookup_tree L). k < fst x) \<and>
                                         (\<forall>k \<in> dom (lookup_tree R). fst x < k) \<and>
                                         sorted_lookup_tree L \<and> sorted_lookup_tree R \<close>


lemma lookup_tree_map_tree[simp]:
  \<open>lookup_tree (map_tree (\<lambda>(k, v). (k, f k v)) tree) = (\<lambda>k. map_option (f k) (lookup_tree tree k)) \<close>
  unfolding fun_eq_iff
  by (induct tree; auto_sledgehammer)

lemma tree_domain_distinct_map[iff]:
  \<open>tree_domain_distinct (Tree.tree.map_tree (\<lambda>(k, v). (k, f k v)) tree) \<longleftrightarrow> tree_domain_distinct tree\<close>
  by (induct tree; auto simp: set_eq_iff dom_def)


lemma rel_tree_domain_eq:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> dom (lookup_tree x) = dom (lookup_tree y) \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1 dom_def map_add_def split: option.split; auto_sledgehammer)

lemma sorted_lookup_tree_rel:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> sorted_lookup_tree x \<longleftrightarrow> sorted_lookup_tree y \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1 split: option.split; auto_sledgehammer)

lemma rel_tree_domain_distinct:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> tree_domain_distinct x \<longleftrightarrow> tree_domain_distinct y \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1 dom_def; auto_sledgehammer)

lemma sorted1_inorder_map_tree[iff]:
  \<open>sorted_lookup_tree (map_tree (\<lambda>(k, v). (k, f k v)) tree) \<longleftrightarrow> sorted_lookup_tree tree\<close>
  by (induct tree; auto_sledgehammer)

subsection \<open>sorted\<close>

lemma tree_sorted_implies_domain_distinct[simp]:
  \<open>sorted_lookup_tree tree \<Longrightarrow> tree_domain_distinct tree\<close>
  by (induct tree; auto_sledgehammer)

lemma lookup_tree_eq_empty:
  \<open> lookup_tree tree = Map.empty \<longleftrightarrow> tree = \<langle>\<rangle> \<close>
  by (induct tree; auto_sledgehammer)

lemma lookup_tree_by_set_distinct[simp]:
  \<open> tree_domain_distinct tree
\<Longrightarrow> (k, v) \<in> tree.set_tree tree \<longleftrightarrow> lookup_tree tree k = Some v\<close>
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

lemma lookup_tree_map_tree2[simp]:
  \<open> lookup_tree (map_tree (\<lambda>(k, h, v). (k, f k h v)) tree) = (\<lambda>k. map_option (case_prod (f k)) (lookup_tree tree k)) \<close>
  using lookup_tree_map_tree[where f=\<open>case_prod o f\<close>]
  by (simp add: case_prod_beta')

lemma sorted_lookup_map_tree2[simp]:
  \<open> sorted_lookup_tree (map_tree (\<lambda>(k, h, v). (k, f k h v)) tree) \<longleftrightarrow> sorted_lookup_tree tree \<close>
  using sorted1_inorder_map_tree[where f=\<open>case_prod o f\<close>]
  by (simp add: case_prod_beta')

lemma lookup_left_children:
  \<open> sorted_lookup_tree tree
\<Longrightarrow> lookup_tree (left tree) = lookup_tree tree |` {x. x < fst (value tree)} \<close>
  \<comment> \<open>this value is the value of the root node\<close>
  by (induct tree; auto simp: fun_eq_iff restrict_map_def; auto_sledgehammer)

lemma lookup_right_children:
  \<open> sorted_lookup_tree tree
\<Longrightarrow> lookup_tree (right tree) = lookup_tree tree |` {x. fst (value tree) < x} \<close>
  by (induct tree; auto simp: fun_eq_iff restrict_map_def; auto_sledgehammer)



subsection \<open>Insert Tree\<close>

primrec insert_tree :: \<open>'k::linorder \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) tree \<Rightarrow> ('k \<times> 'v) tree\<close>
  where \<open>insert_tree k v \<langle>\<rangle> = \<langle>\<langle>\<rangle>, (k,v), \<langle>\<rangle>\<rangle>\<close>
      | \<open>insert_tree k v \<langle>L, x, R\<rangle> = (if k < fst x then \<langle>insert_tree k v L, x, R\<rangle>
                                     else if k = fst x then \<langle>L, (k,v), R\<rangle>
                                     else \<langle>L, x, insert_tree k v R\<rangle> ) \<close>

lemma lookup_tree_insert_tree[simp]:
  \<open> sorted_lookup_tree tree
\<Longrightarrow> lookup_tree (insert_tree k v tree) = (lookup_tree tree)(k \<mapsto> v)\<close>
  by (induct tree; auto simp: fun_eq_iff map_add_def split: option.split; auto_sledgehammer)

lemma insert_tree_sorted[simp]:
  \<open> sorted_lookup_tree tree
\<Longrightarrow> sorted_lookup_tree (insert_tree k v tree) \<close>
  by (induct tree; auto_sledgehammer)

lemma insert_tree_not_Leaf[simp]:
  \<open>insert_tree k v tree \<noteq> \<langle>\<rangle>\<close>
  by (induct tree; auto_sledgehammer)










section \<open>Verifying the Concrete Programs\<close>


abbreviation \<open>\<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {left: \<p>\<t>\<r>, data: TY, right: \<p>\<t>\<r>} \<close>
abbreviation \<open>\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {k: TY\<^sub>K, v: TY\<^sub>V}\<close>
abbreviation \<open>\<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V \<equiv> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<close>

\<phi>reasoner_group BinTree = (100,[0,9999]) \<open>derived reasoning rules of BinTree\<close>
            and Bin_Search_Tree = (100,[0,9999]) \<open>derived reasoning rules of Bin_Search_Tree\<close>
            and AVL_Tree = (100,[0,9999]) \<open>derived reasoning rules of AVL_Tree\<close>

declare [[collect_reasoner_statistics BinTree start,
         \<phi>LPR_collect_statistics derivation start]]
 

\<phi>type_def BinTree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x tree) \<phi>\<close>
  where \<open> (Leaf \<Ztypecolon> BinTree addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0) \<close>
      | \<open> (\<langle>L, x, R\<rangle> \<Ztypecolon> BinTree addr TY T) =
          ((addr\<^sub>L, x, addr\<^sub>R) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> left: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY, data: T, right: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY \<rbrace>\<heavy_comma>
            L \<Ztypecolon> BinTree addr\<^sub>L TY T\<heavy_comma>
            R \<Ztypecolon> BinTree addr\<^sub>R TY T
            \<s>\<u>\<b>\<j> addr\<^sub>L addr\<^sub>R. \<top> )\<close>
   deriving Basic
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (BinTree addr TY T) (\<lambda>x. pred_tree P x \<and> (x = Leaf \<longleftrightarrow> addr = 0)) \<close>
       and \<open>Identity_Elements\<^sub>E (BinTree addr TY T) (\<lambda>l. addr = 0 \<and> l = Leaf)\<close>  
       and \<open>Identity_Elements\<^sub>I (BinTree addr TY T) (\<lambda>l. l = Leaf) (\<lambda>l. addr = 0)\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (BinTree addr TY) (BinTree addr' TY') T U set_tree (\<lambda>_. UNIV) rel_tree\<close>
           (arbitrary: addr')
       and Functional_Transformation_Functor

declare [[collect_reasoner_statistics BinTree stop,
         \<phi>LPR_collect_statistics derivation stop]]

ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %BinTree})) "derivation"\<close>

declare [[collect_reasoner_statistics Bin_Search_Tree start,
         \<phi>LPR_collect_statistics derivation start]]



\<phi>type_def Bin_Search_Tree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> (VAL, 'k::linorder) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi>\<close>
  where \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V \<equiv> tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>
                                       \<s>\<u>\<b>\<j> tree. f = lookup_tree tree \<and> sorted_lookup_tree tree \<close>
  deriving \<open> Abstract_Domain\<^sub>L K P\<^sub>K
         \<Longrightarrow> Abstract_Domain V P\<^sub>V
         \<Longrightarrow> Abstract_Domain (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>
            (tactic: clarsimp, subgoal' for tree x y \<open>induct tree arbitrary: x\<close>)
       and \<open> Identity_Elements\<^sub>E (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>l. addr = 0 \<and> l = Map.empty) \<close>
       and \<open> Identity_Elements\<^sub>I (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>l. l = Map.empty) (\<lambda>l. addr = 0) \<close>
       and \<open> Object_Equiv V eq
         \<Longrightarrow> Object_Equiv (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. eq (the (f k)) (the (g k))) ) \<close>  
            (tactic: clarsimp, 
                     rule exI[where x=\<open>\<lambda>_ g x. map_tree (\<lambda>(k,_). (k, the (g k))) x\<close>],
                     auto intro!: rel_tree_self_map simp: fun_eq_iff)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY\<^sub>K' = TY\<^sub>K \<and> TY\<^sub>V' = TY\<^sub>V \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) (Bin_Search_Tree addr' TY\<^sub>K' TY\<^sub>V' K) T U ran (\<lambda>_. UNIV) rel_map \<close>
            (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ _ y. y\<close>], clarsimp simp: rel_tree_eq_norm rel_tree_conj_split)
       and \<open>Functional_Transformation_Functor (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) T U ran (\<lambda>_. UNIV)
                                              (\<lambda>_ P f. \<forall>x \<in> dom f. P (the (f x))) (\<lambda>f _ x. map_option f o x) \<close>


declare [[collect_reasoner_statistics Bin_Search_Tree stop,
         \<phi>LPR_collect_statistics derivation stop]]

ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %Bin_Search_Tree})) "derivation"\<close>

primrec AVL_invar
  where \<open>AVL_invar \<langle>\<rangle> \<longleftrightarrow> True\<close>
      | \<open>AVL_invar \<langle>L, x, R\<rangle> \<longleftrightarrow> (height L \<le> height R + 1) \<and> (height R \<le> height L + 1) \<and>
                                      AVL_invar L \<and> AVL_invar R \<and> (fst (snd x) = height \<langle>L, x, R\<rangle>)\<close>

lemma Object_Equiv_of_AVL_tree_invar:
  \<open> AVL_invar xa
\<Longrightarrow> AVL_invar (Tree.tree.map_tree (\<lambda>(k, (h,v)). (k, (h, the (y k)))) xa)  \<close>
  by (induct xa arbitrary: y; auto_sledgehammer)

lemma rel_tree__AVL_tree_invar:
  \<open> rel_tree (\<lambda>a b. fst (snd a) = fst (snd b)) x y
\<Longrightarrow> AVL_invar x \<longleftrightarrow> AVL_invar y \<close>
  by (induct x arbitrary: y; auto simp: rel_tree_Node1; auto_sledgehammer)


abbreviation \<open>\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V \<equiv> \<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K (\<s>\<t>\<r>\<u>\<c>\<t> {height: \<a>\<i>\<n>\<t>, v: TY\<^sub>V})\<close>
abbreviation \<open>\<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V \<equiv> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<close>

declare [[collect_reasoner_statistics AVL_Tree start,
         \<phi>LPR_collect_statistics derivation start]]


\<phi>type_def AVL_Tree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> (VAL, 'k::linorder) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi>\<close>
  where \<open>f \<Ztypecolon> AVL_Tree addr TY\<^sub>K TY\<^sub>V K V \<equiv> tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>
                                     \<s>\<u>\<b>\<j> tree. f = map_option snd o lookup_tree tree
                                             \<and> sorted_lookup_tree tree \<and> AVL_invar tree \<close>
  deriving \<open> Abstract_Domain\<^sub>L K P\<^sub>K
         \<Longrightarrow> Abstract_Domain V P\<^sub>V
         \<Longrightarrow> Abstract_Domain (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>
            (tactic: clarsimp, subgoal' for tree x h y \<open>
              induct tree arbitrary: x\<close>)
       and \<open> Identity_Elements\<^sub>E (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>l. addr = 0 \<and> l = Map.empty) \<close>
       and \<open> Identity_Elements\<^sub>I (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>l. l = Map.empty) (\<lambda>l. addr = 0) \<close>
       and \<open> Object_Equiv V eq
         \<Longrightarrow> Object_Equiv (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. eq (the (f k)) (the (g k))) ) \<close>  
            (tactic: clarsimp, 
                     rule exI[where x=\<open>\<lambda>_ g x. map_tree (\<lambda>(k,h,_). (k, h, the (g k))) x\<close>],
                     auto simp: fun_eq_iff intro!: rel_tree_self_map)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY\<^sub>K' = TY\<^sub>K \<and> TY\<^sub>V' = TY\<^sub>V \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (AVL_Tree addr TY\<^sub>K TY\<^sub>V K) (AVL_Tree addr' TY\<^sub>K' TY\<^sub>V' K) T U ran (\<lambda>_. UNIV) rel_map \<close>
            (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ _ y. y\<close>], clarsimp simp: rel_tree_conj_split rel_tree_eq_norm)
       and \<open>Functional_Transformation_Functor (AVL_Tree addr TY\<^sub>K TY\<^sub>V K) (AVL_Tree addr TY\<^sub>K TY\<^sub>V K) T U ran (\<lambda>_. UNIV)
                                              (\<lambda>_ P f. \<forall>x \<in> dom f. P (the (f x))) (\<lambda>f _ x. map_option f o x) \<close>



declare [[collect_reasoner_statistics AVL_Tree stop,
         \<phi>LPR_collect_statistics derivation stop]]

ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %AVL_Tree})) "derivation"\<close>

declare [[auto_sledgehammer_params = "try0 = false"]]
  \<comment> \<open>For some reason I don't know, Sledgehammer fails silently (with throwing an Interrupt exception)
      when \<open>try0\<close> --- reconstructing proofs using classical tactics --- is enabled.
      Anyway, it is an engineering problem due to some bug in our system or Sledgehammer, so we don't
      count it into our statistics.\<close>

declare [[\<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics,
          recording_timing_of_semantic_operation,
          \<phi>async_proof = true]]

context
  fixes K :: \<open>(VAL, 'k::linorder) \<phi>\<close>
    and V :: \<open>(VAL, 'v) \<phi>\<close>
    and TY\<^sub>K TY\<^sub>V :: TY
    and CMP Eq :: \<open>VAL \<phi>arg \<Rightarrow> VAL \<phi>arg \<Rightarrow> VAL proc\<close>
    and zero\<^sub>K :: 'k
    and zero\<^sub>V :: 'v
  assumes cmp: \<open>\<And>k\<^sub>1 k\<^sub>2 u v. \<p>\<r>\<o>\<c> CMP u v \<lbrace> k\<^sub>1 \<Ztypecolon> \<v>\<a>\<l>[u] K\<heavy_comma> k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l>[v] K \<longmapsto> k\<^sub>1 < k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>
      and eq : \<open>\<And>k\<^sub>1 k\<^sub>2 u v. \<p>\<r>\<o>\<c> Eq u v \<lbrace> k\<^sub>1 \<Ztypecolon> \<v>\<a>\<l>[u] K\<heavy_comma> k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l>[v] K \<longmapsto> k\<^sub>1 = k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>  
      and [\<phi>reason add]: \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> K) TY\<^sub>K)\<close>
      and [\<phi>reason add]: \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> V) TY\<^sub>V)\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY\<^sub>K K zero\<^sub>K\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY\<^sub>V V zero\<^sub>V\<close>
begin

 
proc lookup_bintree:
  input  \<open>tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  premises \<open>k \<in> dom (lookup_tree tree) \<and> sorted_lookup_tree tree\<close>
  output \<open>tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          the (lookup_tree tree k) \<Ztypecolon> \<v>\<a>\<l> V\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer ;;
  to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R ;;   \<comment> \<open>TODO: fix quantifier names\<close>

  val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! ;;
  if (eq ($k', $k)) \<medium_left_bracket>
    val ret \<leftarrow> $addr \<tribullet> data \<tribullet> v ! ;;
    \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
    return ($ret)
  \<medium_right_bracket>
  \<medium_left_bracket>
    if (cmp ($k, $k')) \<medium_left_bracket>
      lookup_bintree ($addr \<tribullet> left  !, $k) \<rightarrow> val ret ;;
      \<open>BinTree a\<^sub>R _ _\<close> \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
      return ($ret)
    \<medium_right_bracket> \<medium_left_bracket> 
      lookup_bintree ($addr \<tribullet> right !, $k) \<rightarrow> val ret ;;
      \<open>BinTree a\<^sub>R _ _\<close> \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
      return ($ret)
    \<medium_right_bracket> ;;
  \<medium_right_bracket>
\<medium_right_bracket> .

proc (nodef) lookup_bst:
  input  \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  premises \<open>k \<in> dom f\<close>
  output \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> the (f k) \<Ztypecolon> \<v>\<a>\<l> V\<close>
  is [recursive]
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  lookup_bintree ($addr, $k)
  \<open>f \<Ztypecolon> MAKE _ (Bin_Search_Tree addr _ _ _ _)\<close>
\<medium_right_bracket> .


proc defined_bintree:
  input  \<open>tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  premises \<open>sorted_lookup_tree tree\<close>
  output \<open>tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          k \<in> dom (lookup_tree tree) \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    return (False) 
  \<medium_right_bracket> \<medium_left_bracket>
    obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer ;;
    to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R ;;

    val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! ;;
    if (eq ($k', $k)) \<medium_left_bracket>
      \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
      return (True)
    \<medium_right_bracket>
    \<medium_left_bracket>
      if (cmp ($k, $k')) \<medium_left_bracket>
        val ret \<leftarrow> defined_bintree ($addr \<tribullet> left  !, $k) ;;
        \<open>BinTree a\<^sub>R _ _\<close> \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
        return ($ret)
      \<medium_right_bracket> \<medium_left_bracket> 
        val ret \<leftarrow> defined_bintree ($addr \<tribullet> right !, $k) ;;
        \<open>BinTree a\<^sub>R _ _\<close> \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
        return ($ret)
      \<medium_right_bracket> ;;
    \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .


proc (nodef) defined_bst:
  input  \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  output \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> k \<in> dom f \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  is [recursive]
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  defined_bintree ($addr, $k)
  \<open>f \<Ztypecolon> MAKE _ (Bin_Search_Tree addr _ _ _ _)\<close>
\<medium_right_bracket> .





abbreviation \<open>Bst_Node \<equiv> \<lbrace>
                            left: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V),
                            data: \<lbrace> k: K, v: V \<rbrace>,
                            right: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V)
                          \<rbrace> \<close>



proc insert_bintree:
  input  \<open>tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> V\<close>
  output \<open>insert_tree k v tree \<Ztypecolon> BinTree addr' (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
      val ret \<leftarrow> calloc_1 \<open>Bst_Node\<close> ;;
      $ret \<tribullet> data \<tribullet> k := $k ;;
      $ret \<tribullet> data \<tribullet> v := $v ;;
      \<open>\<langle>\<langle>\<rangle>, (k,v), \<langle>\<rangle>\<rangle> \<Ztypecolon> MAKE 1 (BinTree addrb (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>)\<close> ;;
      return ($ret)
  \<medium_right_bracket> \<medium_left_bracket>
      obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer ;;
      to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R ;;

      val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! ;;
      if (eq ($k', $k)) \<medium_left_bracket>
          $addr \<tribullet> data \<tribullet> v := $v ;;
          \<open>MAKE 1 (BinTree addr _ _)\<close> certified by (instantiate \<open>(k,v)\<close>, auto_sledgehammer) ;;
          return ($addr)
      \<medium_right_bracket> \<medium_left_bracket>
          if (cmp ($k, $k')) \<medium_left_bracket>
              insert_bintree ($addr \<tribullet> left !, $k, $v) \<rightarrow> val a\<^sub>L' ;;
              $addr \<tribullet> left := $a\<^sub>L' ;;
              \<open>BinTree a\<^sub>R _ _\<close> \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
              return ($addr)
          \<medium_right_bracket> \<medium_left_bracket>
              insert_bintree ($addr \<tribullet> right !, $k, $v) \<rightarrow> val a\<^sub>R' ;;
              $addr \<tribullet> right := $a\<^sub>R' ;;
              \<open>MAKE 1 (BinTree addr _ _)\<close> ;;
              return ($addr)
          \<medium_right_bracket>
      \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .


proc (nodef) insert_bst:
  input  \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
          v \<Ztypecolon> \<v>\<a>\<l> V\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> Bin_Search_Tree addr' TY\<^sub>K TY\<^sub>V K V\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  insert_bintree ($addr, $k, $v)
  \<open>f(k \<mapsto> v) \<Ztypecolon> MAKE _ (Bin_Search_Tree addr' TY\<^sub>K TY\<^sub>V K V)\<close>
\<medium_right_bracket> .





proc Max:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>max x y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  if ($x < $y) \<medium_left_bracket> $y \<medium_right_bracket> \<medium_left_bracket> $x \<medium_right_bracket>
\<medium_right_bracket> .



proc height_of:
  input  \<open>tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<close>
  premises \<open>AVL_invar tree\<close>
  output \<open>tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
          height tree \<Ztypecolon> \<v>\<a>\<l> \<nat> \<close>
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
      return (0)
  \<medium_right_bracket> \<medium_left_bracket>
      obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer ;;
      to \<open>OPEN 1 _\<close> ;;
      $addr \<tribullet> data \<tribullet> v \<tribullet> height ! \<rightarrow> val ret ;;
      \<open>tree \<Ztypecolon> MAKE 1 (BinTree addr _ _)\<close> ;;
      return ($ret)
  \<medium_right_bracket>
\<medium_right_bracket> .


lemma stupid[simp]:
  \<open>snd (snd x) = snd (snd y) \<and> fst (snd x) = fst (snd y) \<and> fst x = fst y \<longleftrightarrow> x = y\<close>
  by auto_sledgehammer


proc maintain_i:
  input  \<open>\<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> \<Ztypecolon> BinTree a\<^sub>D (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
          a\<^sub>D \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<close>
  premises \<open>sorted_lookup_tree (\<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle>) \<and>
            AVL_invar B \<and> AVL_invar E \<and>
            height E \<le> height B + 2 \<and> height B \<le> height E + 2 \<close>
  output \<open>tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr tree. map_option snd o lookup_tree tree = map_option snd o lookup_tree \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> \<and>
                         AVL_invar tree \<and> sorted_lookup_tree tree \<and>
                        (height tree = height \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> \<or> height tree = height \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> - 1) \<and>
                        (height E \<le> height B + 1 \<and> height B \<le> height E + 1 \<longrightarrow> height tree = height \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle>)\<close>
  is [routine]
\<medium_left_bracket>

  to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>B, a\<^sub>E ;;                                                             (*for reasoning, \<Omega>*)

  val B \<leftarrow> $a\<^sub>D \<tribullet> left ! ;;
  val E \<leftarrow> $a\<^sub>D \<tribullet> right ! ;;
  val H\<^sub>B \<leftarrow> height_of ($B) ;;
  val H\<^sub>E \<leftarrow> height_of ($E) ;;

  if ($H\<^sub>B = $H\<^sub>E + 2) \<medium_left_bracket>
      obtain A k\<^sub>B h\<^sub>B v\<^sub>B C where B[simp]: \<open>B = \<langle>A, (k\<^sub>B, h\<^sub>B, v\<^sub>B), C\<rangle>\<close> by auto_sledgehammer ;; (*this line and the*)
      \<open>BinTree a\<^sub>B _ _\<close> to \<open>OPEN 1 _\<close> \<exists>t\<^sub>2, a\<^sub>A, a\<^sub>C ;;                                        (*next line, for reasoning, one \<Omega>*)

      val A \<leftarrow> $B \<tribullet> left ! ;;
      val C \<leftarrow> $B \<tribullet> right ! ;;
      val H\<^sub>A \<leftarrow> height_of ($A) ;;
      val H\<^sub>C \<leftarrow> height_of ($C) ;;

      if ($H\<^sub>C \<le> $H\<^sub>A) \<medium_left_bracket>

          $a\<^sub>D \<tribullet> left := $C ;;
          val H\<^sub>D' \<leftarrow> Max($H\<^sub>C, $H\<^sub>E) + 1 ;;
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' ;;
          $B \<tribullet> right := $a\<^sub>D ;;
          $B \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>A, $H\<^sub>D') + 1 ;;

          \<open>BinTree a\<^sub>C _ _\<close> \<open>BinTree a\<^sub>E _ _\<close> \<open>MAKE 1 (BinTree a\<^sub>D _ _)\<close> ;;                 (*for reasoning, \<Omega>*)
          \<open>MAKE 1 (BinTree a\<^sub>B _ _)\<close> ;;                                                  (*for reasoning, \<Omega>*)
 
          return ($B) certified by (auto simp add: fun_eq_iff map_add_def split: option.split; auto_sledgehammer) (*Tac-1n-2m*)
      \<medium_right_bracket>
      \<medium_left_bracket>
          obtain C\<^sub>L k\<^sub>C h\<^sub>C v\<^sub>C C\<^sub>R where C[simp]: \<open>C = \<langle>C\<^sub>L, (k\<^sub>C, h\<^sub>C, v\<^sub>C), C\<^sub>R\<rangle>\<close> by auto_sledgehammer ;;  (*this line and the next*)
          \<open>BinTree a\<^sub>C _ _\<close> to \<open>OPEN 1 _\<close> \<exists>t\<^sub>3, a\<^sub>C\<^sub>L, a\<^sub>C\<^sub>R ;;                                           (*line, for reasoning, one \<Omega>*)

          val C\<^sub>L \<leftarrow> $C \<tribullet> left ! ;;
          val C\<^sub>R \<leftarrow> $C \<tribullet> right ! ;;
          $B \<tribullet> right := $C\<^sub>L ;;
          val H\<^sub>B' \<leftarrow> Max($H\<^sub>A, height_of($C\<^sub>L)) + 1 ;;
          $B \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>B';;
          $a\<^sub>D \<tribullet> left := $C \<tribullet> right ! ;;
          val H\<^sub>D' \<leftarrow> Max($H\<^sub>E, height_of($C\<^sub>R)) + 1 ;;
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' ;;
          $C \<tribullet> left := $B ;;
          $C \<tribullet> right := $a\<^sub>D ;;
          $C \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>B', $H\<^sub>D') + 1 ;;

          \<open>BinTree a\<^sub>A _ _\<close> \<open>BinTree a\<^sub>C\<^sub>L _ _\<close> \<open>MAKE 1 (BinTree a\<^sub>B _ _)\<close> ;;         (*for reasoning, \<Omega>*)
          \<open>BinTree a\<^sub>C\<^sub>R _ _\<close> \<open>BinTree a\<^sub>E _ _\<close> \<open>MAKE 1 (BinTree a\<^sub>D _ _)\<close> ;;         (*for reasoning, \<Omega>*)
          \<open>MAKE 1 (BinTree a\<^sub>C _ _)\<close> ;;                                           (*for reasoning, \<Omega>*)

          holds_fact t1[useful]: \<open>k\<^sub>B < k\<^sub>D\<close>  ;;                                    (*for proof, Tac-s*)

          return ($C) certified by (auto simp: map_add_def fun_eq_iff split: option.split; auto_sledgehammer)  (*Tac-1n-3m*)
                                        
    \<medium_right_bracket>
  \<medium_right_bracket>
  \<medium_left_bracket>
    if ($H\<^sub>E = $H\<^sub>B + 2) \<medium_left_bracket>

      obtain F k\<^sub>E h\<^sub>E v\<^sub>E G where E[simp]: \<open>E = \<langle>F, (k\<^sub>E, h\<^sub>E, v\<^sub>E), G\<rangle>\<close> by auto_sledgehammer ;; (*for reasoning, \<Omega>*)
      \<open>BinTree a\<^sub>E _ _\<close> to \<open>OPEN 1 _\<close> \<exists>t\<^sub>2, a\<^sub>F, a\<^sub>G ;;
  
      val F \<leftarrow> $E \<tribullet> left ! ;;
      val G \<leftarrow> $E \<tribullet> right ! ;;
      val H\<^sub>F \<leftarrow> height_of ($F) ;;
      val H\<^sub>G \<leftarrow> height_of ($G) ;;

      if ($H\<^sub>F \<le> $H\<^sub>G) \<medium_left_bracket>

          $a\<^sub>D \<tribullet> right := $F ;;
          val H\<^sub>D' \<leftarrow> Max($H\<^sub>B, $H\<^sub>F) + 1 ;;
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' ;;
          $E \<tribullet> left := $a\<^sub>D ;;
          $E \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>D', $H\<^sub>G) + 1 ;;

          \<open>BinTree a\<^sub>B _ _\<close> \<open>BinTree a\<^sub>F _ _\<close> \<open>MAKE 1 (BinTree a\<^sub>D _ _)\<close> ;;                 (*for reasoning, \<Omega>*)
          \<open>BinTree a\<^sub>G _ _\<close> \<open>MAKE 1 (BinTree a\<^sub>E _ _)\<close> ;;                                  (*for reasoning, \<Omega>*)

          return ($E) certified by (auto simp: map_add_def fun_eq_iff split: option.split; auto_sledgehammer)  (*Tac-1n-3m*)

      \<medium_right_bracket>
      \<medium_left_bracket>
          obtain F\<^sub>L k\<^sub>F h\<^sub>F v\<^sub>F F\<^sub>R where F[simp]: \<open>F = \<langle>F\<^sub>L, (k\<^sub>F, h\<^sub>F, v\<^sub>F), F\<^sub>R\<rangle>\<close> by auto_sledgehammer ;;
          \<open>BinTree a\<^sub>F _ _\<close> to \<open>OPEN 1 _\<close> \<exists>t\<^sub>4, a\<^sub>F\<^sub>L, a\<^sub>F\<^sub>R ;;

          val F\<^sub>L \<leftarrow> $F \<tribullet> left ! ;;
          val F\<^sub>R \<leftarrow> $F \<tribullet> right ! ;;
          $a\<^sub>D \<tribullet> right := $F\<^sub>L ;;
          val H\<^sub>D' \<leftarrow> Max ($H\<^sub>B, height_of ($F\<^sub>L)) + 1 ;;
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' ;;
          $E \<tribullet> left := $F\<^sub>R ;;
          val H\<^sub>E' \<leftarrow> Max (height_of ($F\<^sub>R), $H\<^sub>G) + 1 ;;
          $E \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>E' ;;
          $F \<tribullet> left := $a\<^sub>D ;;
          $F \<tribullet> right := $E ;;
          $F \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>D', $H\<^sub>E') + 1;;

          \<open>BinTree a\<^sub>B _ _\<close> \<open>BinTree a\<^sub>F\<^sub>L _ _\<close> \<open>MAKE 1 (BinTree a\<^sub>D _ _)\<close> ;;
          \<open>BinTree a\<^sub>F\<^sub>R _ _\<close> \<open>BinTree a\<^sub>G _ _\<close> \<open>MAKE 1 (BinTree a\<^sub>E _ _)\<close> ;;
          \<open>MAKE 1 (BinTree a\<^sub>F _ _)\<close> ;;

          return ($F) certified by (clarsimp, rule,
                                    ((auto simp: map_add_def fun_eq_iff split: option.split)[1]; auto_sledgehammer),
                                    auto; auto_sledgehammer)                          (*Tac-4n-3m*)
      \<medium_right_bracket>
    \<medium_right_bracket>
    \<medium_left_bracket>
      $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := Max (height_of ($a\<^sub>D \<tribullet> left !), height_of ($a\<^sub>D \<tribullet> right !)) + 1  ;;
      \<open>MAKE 1 (BinTree a\<^sub>D _ _)\<close> ;;
      return ($a\<^sub>D)
    \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .

abbreviation \<open>Avl_Node \<equiv> \<lbrace>
                            left: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V),
                            data: \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>,
                            right: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V)
                          \<rbrace> \<close>

proc insert_avl_i:
  input  \<open>tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
          v \<Ztypecolon> \<v>\<a>\<l> V\<close>
  premises \<open>sorted_lookup_tree tree \<and> AVL_invar tree \<close>
  output \<open>tree' \<Ztypecolon> BinTree addr' (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr' tree'.
          map_option snd o lookup_tree tree' = (map_option snd o lookup_tree tree)(k \<mapsto> v) \<and>
          sorted_lookup_tree tree' \<and> AVL_invar tree' \<and>
          (height tree' = height tree \<or> height tree' = height tree + 1) \<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>

  if \<open>$addr = 0\<close> \<medium_left_bracket>
      val ret \<leftarrow> calloc_1 \<open>Avl_Node\<close> ;;
      $ret \<tribullet> data \<tribullet> k := $k ;;
      $ret \<tribullet> data \<tribullet> v \<tribullet> v := $v ;;
      $ret \<tribullet> data \<tribullet> v \<tribullet> height := 1 ;;
      \<open>\<langle>\<langle>\<rangle>, (k,1,v), \<langle>\<rangle>\<rangle> \<Ztypecolon> MAKE 1 (BinTree addrb (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>)\<close> ;;
      return ($ret)
  \<medium_right_bracket>
  \<medium_left_bracket>
      obtain L k' h' v' R where tree_def[simp]: \<open>tree = \<langle>L, (k', h', v'), R\<rangle>\<close> by auto_sledgehammer ;;
      to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R ;;

      val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! ;;
      if (eq ($k', $k)) \<medium_left_bracket>
        $addr \<tribullet> data \<tribullet> v \<tribullet> v := $v ;;
        \<open>MAKE 1 (BinTree addr _ _)\<close>  ;;
        return ($addr)
      \<medium_right_bracket> \<medium_left_bracket>
        if (cmp ($k, $k')) \<medium_left_bracket>
            insert_avl_i ($addr \<tribullet> left !, $k, $v) \<rightarrow> val a\<^sub>L' ;;
            $addr \<tribullet> left := $a\<^sub>L' ;;
            \<open>BinTree a\<^sub>R _ _\<close> \<open>MAKE 1 (BinTree addr _ _)\<close>  ;;
            return (maintain_i ($addr))
        \<medium_right_bracket>
        \<medium_left_bracket>
            insert_avl_i ($addr \<tribullet> right !, $k, $v) \<rightarrow> val a\<^sub>R' ;;
            $addr \<tribullet> right := $a\<^sub>R' ;;
            \<open>MAKE 1 (BinTree addr _ _)\<close> ;;

            return (maintain_i ($addr))
        \<medium_right_bracket>
      \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc (nodef) insert_avl:
  input  \<open>f \<Ztypecolon> AVL_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
          v \<Ztypecolon> \<v>\<a>\<l> V\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> AVL_Tree addr' TY\<^sub>K TY\<^sub>V K V\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  insert_avl_i ($addr, $k, $v)
  \<open>f(k \<mapsto> v) \<Ztypecolon> MAKE _ (AVL_Tree addr' TY\<^sub>K TY\<^sub>V K V)\<close>
\<medium_right_bracket> .

end


declare [[\<phi>LPR_collect_statistics program stop,
          collecting_subgoal_statistics=false,
          recording_timing_of_semantic_operation = false,
          \<phi>async_proof = true]]





end