theory Binary_Trees
  imports Phi_Semantics.PhiSem_C
          "HOL-Data_Structures.Tree_Map"
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

section \<open>Abstract Model\<close>

subsection \<open>Common Operations\<close>

declare tree.rel_eq[simp]

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

\<phi>type_def BinTree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x tree) \<phi>\<close>
  where \<open> (Leaf \<Ztypecolon> BinTree addr TY T)     = (Void \<s>\<u>\<b>\<j> addr = 0) \<close>
      | \<open> (\<langle>L, x, R\<rangle> \<Ztypecolon> BinTree addr TY T) =
                (L \<Ztypecolon> BinTree addr\<^sub>L TY T\<heavy_comma>
                 R \<Ztypecolon> BinTree addr\<^sub>R TY T\<heavy_comma>
                 (addr\<^sub>L, x, addr\<^sub>R) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> left: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY, data: T, right: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY \<rbrace> 
                \<s>\<u>\<b>\<j> addr\<^sub>L addr\<^sub>R. \<top> )\<close>

   deriving Basic
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (BinTree addr TY T) (\<lambda>x. pred_tree P x \<and> (x = Leaf \<longleftrightarrow> addr = 0)) \<close>
       and \<open>Identity_Elements\<^sub>E (BinTree addr TY T) (\<lambda>l. addr = 0 \<and> l = Leaf)\<close>  
       and \<open>Identity_Elements\<^sub>I (BinTree addr TY T) (\<lambda>l. l = Leaf) (\<lambda>l. addr = 0)\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (BinTree addr TY) (BinTree addr' TY') T U set_tree (\<lambda>_. UNIV) rel_tree\<close>
           (arbitrary: addr')
       and Functional_Transformation_Functor

declare [[ML_print_depth = 100]]

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
       and \<open>Functional_Transformation_Functor (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) T U ran (\<lambda>_. UNIV)
                                              (\<lambda>_ P f. \<forall>x \<in> dom f. P (the (f x))) (\<lambda>f _ x. map_option f o x) \<close>


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
 


declare [[ML_print_depth = 100]]

abbreviation \<open>\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V \<equiv> \<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K (\<s>\<t>\<r>\<u>\<c>\<t> {height: \<a>\<i>\<n>\<t>, v: TY\<^sub>V})\<close>
abbreviation \<open>\<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V \<equiv> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<close>


\<phi>type_def AVL_Tree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> (VAL, 'k::linorder) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi>\<close>
  where \<open>f \<Ztypecolon> AVL_Tree addr TY\<^sub>K TY\<^sub>V K V \<equiv> tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>
                                     \<s>\<u>\<b>\<j> tree. f = map_option snd o lookup_tree tree
                                             \<and> sorted_lookup_tree tree \<and> AVL_invar tree \<close>
  deriving \<open> Abstract_Domain\<^sub>L K P\<^sub>K
         \<Longrightarrow> Abstract_Domain V P\<^sub>V
         \<Longrightarrow> Abstract_Domain (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>
            (tactic: clarsimp, subgoal' for tree x h y \<open>induct tree arbitrary: x\<close>)
       and \<open> Identity_Elements\<^sub>E (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>l. addr = 0 \<and> l = Map.empty) \<close>
       and \<open> Identity_Elements\<^sub>I (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>l. l = Map.empty) (\<lambda>l. addr = 0) \<close>
       and \<open> Object_Equiv V eq
         \<Longrightarrow> Object_Equiv (AVL_Tree addr TY\<^sub>K TY\<^sub>V K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. eq (the (f k)) (the (g k))) ) \<close>  
            (tactic: clarsimp, 
                     rule exI[where x=\<open>\<lambda>_ g x. map_tree (\<lambda>(k,h,_). (k, h, the (g k))) x\<close>],
                     auto simp: fun_eq_iff intro!: rel_tree_self_map)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY\<^sub>K' = TY\<^sub>K \<and> TY\<^sub>V' = TY\<^sub>V \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (AVL_Tree addr TY\<^sub>K TY\<^sub>V K) (AVL_Tree addr' TY\<^sub>K' TY\<^sub>V' K) T U ran (\<lambda>_. UNIV) rel_map \<close>
       and \<open> Functional_Transformation_Functor (AVL_Tree addr TY\<^sub>K TY\<^sub>V K) (AVL_Tree addr TY\<^sub>K TY\<^sub>V K) T U ran (\<lambda>_. UNIV)
                                               (\<lambda>_ P f. \<forall>x \<in> dom f. P (the (f x))) (\<lambda>f _ x. map_option f o x) \<close>



declare [[auto_sledgehammer_params = "try0 = false"]]
  \<comment> \<open>For some reason I don't know, Sledgehammer fails silently (with throwing an Interrupt exception)
      when \<open>try0\<close> --- reconstructing proofs using classical tactics --- is enabled.
      Anyway, it is an engineering problem due to some bug in our system or Sledgehammer, so we don't
      count this line into our statistics in the paper.\<close>


context
  fixes K :: \<open>(VAL, 'k::linorder) \<phi>\<close>                  \<comment> \<open>we provide a generic verification\<close>
    and V :: \<open>(VAL, 'v) \<phi>\<close>
    and TY\<^sub>K TY\<^sub>V :: TY
    and CMP Eq :: \<open>VAL \<phi>arg \<Rightarrow> VAL \<phi>arg \<Rightarrow> VAL proc\<close>
    and zero\<^sub>K :: 'k
    and zero\<^sub>V :: 'v
  assumes cmp: \<open>\<And>k\<^sub>1 k\<^sub>2 u v. \<p>\<r>\<o>\<c> CMP u v \<lbrace> k\<^sub>1 \<Ztypecolon> \<v>\<a>\<l>[u] K\<heavy_comma> k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l>[v] K \<longmapsto> k\<^sub>1 < k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>
      and eq : \<open>\<And>k\<^sub>1 k\<^sub>2 u v. \<p>\<r>\<o>\<c> Eq u v \<lbrace> k\<^sub>1 \<Ztypecolon> \<v>\<a>\<l>[u] K\<heavy_comma> k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l>[v] K \<longmapsto> k\<^sub>1 = k\<^sub>2 \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>  
      and [\<phi>reason add]: \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> K) TY\<^sub>K)\<close>  \<comment> \<open>specify the semantic type of K\<close>
      and [\<phi>reason add]: \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> V) TY\<^sub>V)\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY\<^sub>K K zero\<^sub>K\<close>  \<comment> \<open>specify the semantic zero value of K\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY\<^sub>V V zero\<^sub>V\<close>
begin

 
proc lookup_bintree:
  input    \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
            tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<close>
  premises \<open>k \<in> dom (lookup_tree tree) \<and> sorted_lookup_tree tree\<close>
  output   \<open>tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
            the (lookup_tree tree k) \<Ztypecolon> \<v>\<a>\<l> V\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer \<semicolon>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>L, a\<^sub>R \<semicolon>

  val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! \<semicolon>
  if (eq ($k', $k)) \<medium_left_bracket>
    val ret \<leftarrow> $addr \<tribullet> data \<tribullet> v ! \<semicolon>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
    return ($ret)
  \<medium_right_bracket>
  \<medium_left_bracket>
    if (cmp ($k, $k')) \<medium_left_bracket>
      lookup_bintree ($addr \<tribullet> left  !, $k) \<rightarrow> val ret \<semicolon>
      \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
      return ($ret)
    \<medium_right_bracket> \<medium_left_bracket> 
      lookup_bintree ($addr \<tribullet> right !, $k) \<rightarrow> val ret \<semicolon>
      \<open>BinTree a\<^sub>L _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
      return ($ret)
    \<medium_right_bracket> \<semicolon>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc (nodef) lookup_bst:
  input    \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma> f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<close>
  premises \<open>k \<in> dom f\<close>
  output   \<open>the (f k) \<Ztypecolon> \<v>\<a>\<l> V\<heavy_comma> f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<close>
  unfolding Bin_Search_Tree.unfold
\<medium_left_bracket>
  lookup_bintree ($addr, $k)
\<medium_right_bracket> .


proc defined_bintree:
  input    \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
            tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<close>
  premises \<open>sorted_lookup_tree tree\<close>
  output   \<open>k \<in> dom (lookup_tree tree) \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma>
            tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    return (False) 
  \<medium_right_bracket> \<medium_left_bracket>
    obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer \<semicolon>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>L, a\<^sub>R \<semicolon>

    val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! \<semicolon>
    if (eq ($k', $k)) \<medium_left_bracket>
      \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
      return (True)
    \<medium_right_bracket>
    \<medium_left_bracket>
      if (cmp ($k, $k')) \<medium_left_bracket>
        val ret \<leftarrow> defined_bintree ($addr \<tribullet> left  !, $k) \<semicolon>
        \<open>BinTree a\<^sub>L _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
        return ($ret)
      \<medium_right_bracket> \<medium_left_bracket> 
        val ret \<leftarrow> defined_bintree ($addr \<tribullet> right !, $k) \<semicolon>
        \<open>BinTree a\<^sub>L _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
        return ($ret)
      \<medium_right_bracket> \<semicolon>
    \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .


proc (nodef) defined_bst:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma> f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<close>
  output \<open>k \<in> dom f \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<close>
  unfolding Bin_Search_Tree.unfold
\<medium_left_bracket>
  defined_bintree ($addr, $k)
\<medium_right_bracket> .



abbreviation \<open>Bst_Node \<equiv> \<lbrace>
                            left: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V),
                            data: \<lbrace> k: K, v: V \<rbrace>,
                            right: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V)
                          \<rbrace> \<close>

proc insert_bintree:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> V\<heavy_comma>
          tree \<Ztypecolon> BinTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace> \<close>
  output \<open>insert_tree k v tree \<Ztypecolon> BinTree addr' (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
      val ret \<leftarrow> calloc1 \<open>Bst_Node\<close> \<semicolon>
      $ret \<tribullet> data \<tribullet> k := $k \<semicolon>
      $ret \<tribullet> data \<tribullet> v := $v \<semicolon>
      \<m>\<a>\<k>\<e>\<s>(1) \<open>\<langle>\<langle>\<rangle>, (k,v), \<langle>\<rangle>\<rangle> \<Ztypecolon> BinTree addrb (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<close> \<semicolon>
      return ($ret)
  \<medium_right_bracket> \<medium_left_bracket>
      obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer \<semicolon>
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>L, a\<^sub>R \<semicolon>

      val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! \<semicolon>
      if (eq ($k', $k)) \<medium_left_bracket>
          $addr \<tribullet> data \<tribullet> v := $v \<semicolon>
          \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> certified by (instantiate \<open>(k,v)\<close>, auto_sledgehammer) \<semicolon>
          return ($addr)
      \<medium_right_bracket> \<medium_left_bracket>
          if (cmp ($k, $k')) \<medium_left_bracket>
              insert_bintree ($addr \<tribullet> left !, $k, $v) \<rightarrow> val a\<^sub>L' \<semicolon>
              $addr \<tribullet> left := $a\<^sub>L' \<semicolon>
              \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
              return ($addr)
          \<medium_right_bracket> \<medium_left_bracket>
              insert_bintree ($addr \<tribullet> right !, $k, $v) \<rightarrow> val a\<^sub>R' \<semicolon>
              $addr \<tribullet> right := $a\<^sub>R' \<semicolon>
              \<open>BinTree a\<^sub>L _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
              return ($addr)
          \<medium_right_bracket>
      \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .


proc (nodef) insert_bst:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
          v \<Ztypecolon> \<v>\<a>\<l> V\<heavy_comma>
          f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<close>
  output \<open>f(k \<mapsto> v) \<Ztypecolon> Bin_Search_Tree addr' TY\<^sub>K TY\<^sub>V K V\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
  unfolding Bin_Search_Tree.unfold
\<medium_left_bracket>
  insert_bintree ($addr, $k, $v)
\<medium_right_bracket> .


proc Max:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>max x y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  if ($x < $y) \<medium_left_bracket> $y \<medium_right_bracket> \<medium_left_bracket> $x \<medium_right_bracket>
\<medium_right_bracket> .


proc height_of:
  input    \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
            tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<close>
  premises \<open>AVL_invar tree\<close>
  output   \<open>tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
            height tree \<Ztypecolon> \<v>\<a>\<l> \<nat> \<close>
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
      return (0)
  \<medium_right_bracket> \<medium_left_bracket>
      obtain L node R where tree_def[simp]: \<open>tree = \<langle>L, node, R\<rangle>\<close> by auto_sledgehammer \<semicolon>
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
      $addr \<tribullet> data \<tribullet> v \<tribullet> height ! \<rightarrow> val ret \<semicolon>
      \<m>\<a>\<k>\<e>\<s>(1) \<open>tree \<Ztypecolon> BinTree addr _ _\<close> \<semicolon>
      return ($ret)
  \<medium_right_bracket>
\<medium_right_bracket> .


proc maintain_i:
  input    \<open>\<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> \<Ztypecolon> BinTree a\<^sub>D (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
            a\<^sub>D \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<close>

  premises \<open>sorted_lookup_tree (\<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle>) \<and>
            AVL_invar B \<and> AVL_invar E \<and>
            height E \<le> height B + 2 \<and> height B \<le> height E + 2 \<close>

  output   \<open>tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<heavy_comma>
            addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
            \<s>\<u>\<b>\<j> addr tree. map_option snd o lookup_tree tree = map_option snd o lookup_tree \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> \<and>
                           AVL_invar tree \<and> sorted_lookup_tree tree \<and>
                          (height tree = height \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> \<or> height tree = height \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle> - 1) \<and>
                          (height E \<le> height B + 1 \<and> height B \<le> height E + 1 \<longrightarrow> height tree = height \<langle>B, (k\<^sub>D, h\<^sub>D, v\<^sub>D), E\<rangle>)\<close>
  is [routine]

\<medium_left_bracket>

  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>OPEN 1 _\<close> \<exists>a\<^sub>B, a\<^sub>E \<semicolon>                                                 (*for reasoning, \<Omega>*)

  val B \<leftarrow> $a\<^sub>D \<tribullet> left ! \<semicolon>
  val E \<leftarrow> $a\<^sub>D \<tribullet> right ! \<semicolon>
  val H\<^sub>B \<leftarrow> height_of ($B) \<semicolon>
  val H\<^sub>E \<leftarrow> height_of ($E) \<semicolon>

  if ($H\<^sub>B = $H\<^sub>E + 2) \<medium_left_bracket>
      obtain A k\<^sub>B h\<^sub>B v\<^sub>B C where B[simp]: \<open>B = \<langle>A, (k\<^sub>B, h\<^sub>B, v\<^sub>B), C\<rangle>\<close> by auto_sledgehammer \<semicolon> (*this line and the*)
      \<open>BinTree a\<^sub>B _ _\<close> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>A, a\<^sub>C \<semicolon>                                        (*next line, for reasoning, one \<Omega>*)

      val A \<leftarrow> $B \<tribullet> left ! \<semicolon>
      val C \<leftarrow> $B \<tribullet> right ! \<semicolon>
      val H\<^sub>A \<leftarrow> height_of ($A) \<semicolon>
      val H\<^sub>C \<leftarrow> height_of ($C) \<semicolon>

      if ($H\<^sub>C \<le> $H\<^sub>A) \<medium_left_bracket>

          $a\<^sub>D \<tribullet> left := $C \<semicolon>
          val H\<^sub>D' \<leftarrow> Max($H\<^sub>C, $H\<^sub>E) + 1 \<semicolon>
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' \<semicolon>
          $B \<tribullet> right := $a\<^sub>D \<semicolon>
          $B \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>A, $H\<^sub>D') + 1 \<semicolon>

          \<open>BinTree a\<^sub>E _ _\<close> \<open>BinTree a\<^sub>C _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>D _ _\<close> \<semicolon>                 (*for reasoning, \<Omega>*)
          \<open>BinTree a\<^sub>A _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>B _ _\<close> \<semicolon>                                                  (*for reasoning, \<Omega>*)
 
          return ($B) certified by (auto simp add: fun_eq_iff map_add_def split: option.split; auto_sledgehammer) (*Tac-1n-2m*)
      \<medium_right_bracket>
      \<medium_left_bracket>
          obtain C\<^sub>L k\<^sub>C h\<^sub>C v\<^sub>C C\<^sub>R where C[simp]: \<open>C = \<langle>C\<^sub>L, (k\<^sub>C, h\<^sub>C, v\<^sub>C), C\<^sub>R\<rangle>\<close> by auto_sledgehammer \<semicolon>  (*this line and the next*)
          \<open>BinTree a\<^sub>C _ _\<close> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>C\<^sub>L, a\<^sub>C\<^sub>R \<semicolon>                                           (*line, for reasoning, one \<Omega>*)

          val C\<^sub>L \<leftarrow> $C \<tribullet> left ! \<semicolon>
          val C\<^sub>R \<leftarrow> $C \<tribullet> right ! \<semicolon>
          $B \<tribullet> right := $C\<^sub>L \<semicolon>
          val H\<^sub>B' \<leftarrow> Max($H\<^sub>A, height_of($C\<^sub>L)) + 1 \<semicolon>
          $B \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>B'\<semicolon>
          $a\<^sub>D \<tribullet> left := $C \<tribullet> right ! \<semicolon>
          val H\<^sub>D' \<leftarrow> Max($H\<^sub>E, height_of($C\<^sub>R)) + 1 \<semicolon>
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' \<semicolon>
          $C \<tribullet> left := $B \<semicolon>
          $C \<tribullet> right := $a\<^sub>D \<semicolon>
          $C \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>B', $H\<^sub>D') + 1 \<semicolon>

          \<open>BinTree a\<^sub>E _ _\<close> \<open>BinTree a\<^sub>C\<^sub>R _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>D _ _\<close> \<semicolon>         (*for reasoning, \<Omega>*)
          \<open>BinTree a\<^sub>C\<^sub>L _ _\<close> \<open>BinTree a\<^sub>A _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>B _ _\<close> \<semicolon>         (*for reasoning, \<Omega>*)
          \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>C _ _\<close> \<semicolon>                                           (*for reasoning, \<Omega>*)

          holds_fact t1[useful]: \<open>k\<^sub>B < k\<^sub>D\<close>  \<semicolon>                                    (*for proof, Tac-s*)

          return ($C) certified by (auto simp: map_add_def fun_eq_iff split: option.split; auto_sledgehammer)  (*Tac-1n-3m*)
    \<medium_right_bracket>
  \<medium_right_bracket>
  \<medium_left_bracket>
    if ($H\<^sub>E = $H\<^sub>B + 2) \<medium_left_bracket>

      obtain F k\<^sub>E h\<^sub>E v\<^sub>E G where E[simp]: \<open>E = \<langle>F, (k\<^sub>E, h\<^sub>E, v\<^sub>E), G\<rangle>\<close> by auto_sledgehammer \<semicolon> (*for reasoning, \<Omega>*)
      \<open>BinTree a\<^sub>E _ _\<close> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>F, a\<^sub>G \<semicolon>
  
      val F \<leftarrow> $E \<tribullet> left ! \<semicolon>
      val G \<leftarrow> $E \<tribullet> right ! \<semicolon>
      val H\<^sub>F \<leftarrow> height_of ($F) \<semicolon>
      val H\<^sub>G \<leftarrow> height_of ($G) \<semicolon>

      if ($H\<^sub>F \<le> $H\<^sub>G) \<medium_left_bracket>

          $a\<^sub>D \<tribullet> right := $F \<semicolon>
          val H\<^sub>D' \<leftarrow> Max($H\<^sub>B, $H\<^sub>F) + 1 \<semicolon>
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' \<semicolon>
          $E \<tribullet> left := $a\<^sub>D \<semicolon>
          $E \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>D', $H\<^sub>G) + 1 \<semicolon>

          \<open>BinTree a\<^sub>F _ _\<close> \<open>BinTree a\<^sub>B _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>D _ _\<close> \<semicolon>                 (*for reasoning, \<Omega>*)
          \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>E _ _\<close> \<semicolon>                                  (*for reasoning, \<Omega>*)

          return ($E) certified by (auto simp: map_add_def fun_eq_iff split: option.split; auto_sledgehammer)  (*Tac-1n-3m*)
      \<medium_right_bracket>
      \<medium_left_bracket>
          obtain F\<^sub>L k\<^sub>F h\<^sub>F v\<^sub>F F\<^sub>R where F[simp]: \<open>F = \<langle>F\<^sub>L, (k\<^sub>F, h\<^sub>F, v\<^sub>F), F\<^sub>R\<rangle>\<close> by auto_sledgehammer \<semicolon>
          \<open>BinTree a\<^sub>F _ _\<close> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>F\<^sub>L, a\<^sub>F\<^sub>R \<semicolon>

          val F\<^sub>L \<leftarrow> $F \<tribullet> left ! \<semicolon>
          val F\<^sub>R \<leftarrow> $F \<tribullet> right ! \<semicolon>
          $a\<^sub>D \<tribullet> right := $F\<^sub>L \<semicolon>
          val H\<^sub>D' \<leftarrow> Max ($H\<^sub>B, height_of ($F\<^sub>L)) + 1 \<semicolon>
          $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>D' \<semicolon>
          $E \<tribullet> left := $F\<^sub>R \<semicolon>
          val H\<^sub>E' \<leftarrow> Max (height_of ($F\<^sub>R), $H\<^sub>G) + 1 \<semicolon>
          $E \<tribullet> data \<tribullet> v \<tribullet> height := $H\<^sub>E' \<semicolon>
          $F \<tribullet> left := $a\<^sub>D \<semicolon>
          $F \<tribullet> right := $E \<semicolon>
          $F \<tribullet> data \<tribullet> v \<tribullet> height := Max($H\<^sub>D', $H\<^sub>E') + 1\<semicolon>

          \<open>BinTree a\<^sub>G _ _\<close> \<open>BinTree a\<^sub>F\<^sub>R _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>E _ _\<close> \<semicolon>
          \<open>BinTree a\<^sub>F\<^sub>L _ _\<close> \<open>BinTree a\<^sub>B _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>D _ _\<close> \<semicolon>
          \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>F _ _\<close> \<semicolon>

          return ($F) certified by (clarsimp, rule,
                                    ((auto simp: map_add_def fun_eq_iff split: option.split)[1]; auto_sledgehammer),
                                    auto; auto_sledgehammer)                          (*Tac-4n-3m*)
      \<medium_right_bracket>
    \<medium_right_bracket>
    \<medium_left_bracket>
      $a\<^sub>D \<tribullet> data \<tribullet> v \<tribullet> height := Max (height_of ($a\<^sub>D \<tribullet> left !), height_of ($a\<^sub>D \<tribullet> right !)) + 1  \<semicolon>
      \<open>BinTree a\<^sub>B _ _ \<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree a\<^sub>D _ _\<close> \<semicolon>
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
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
          v \<Ztypecolon> \<v>\<a>\<l> V\<heavy_comma>
          tree \<Ztypecolon> BinTree addr (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<close>

  premises \<open>sorted_lookup_tree tree \<and> AVL_invar tree \<close>

  output \<open>addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<a>\<v>\<l>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          tree' \<Ztypecolon> BinTree addr' (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>
          \<s>\<u>\<b>\<j> addr' tree'.
          map_option snd o lookup_tree tree' = (map_option snd o lookup_tree tree)(k \<mapsto> v) \<and>
          sorted_lookup_tree tree' \<and> AVL_invar tree' \<and>
          (height tree' = height tree \<or> height tree' = height tree + 1) \<close>

  is [recursive]
  is [routine]

\<medium_left_bracket>

  if \<open>$addr = 0\<close> \<medium_left_bracket>
      val ret \<leftarrow> calloc1 \<open>Avl_Node\<close> \<semicolon>
      $ret \<tribullet> data \<tribullet> k := $k \<semicolon>
      $ret \<tribullet> data \<tribullet> v \<tribullet> v := $v \<semicolon>
      $ret \<tribullet> data \<tribullet> v \<tribullet> height := 1 \<semicolon>
      \<m>\<a>\<k>\<e>\<s>(1) \<open>\<langle>\<langle>\<rangle>, (k,1,v), \<langle>\<rangle>\<rangle> \<Ztypecolon> BinTree addrb (\<a>\<v>\<l>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: \<lbrace> height: \<nat>, v: V \<rbrace> \<rbrace>\<close> \<semicolon>
      return ($ret)
  \<medium_right_bracket>
  \<medium_left_bracket>
      obtain L k' h' v' R where tree_def[simp]: \<open>tree = \<langle>L, (k', h', v'), R\<rangle>\<close> by auto_sledgehammer \<semicolon>
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<exists>a\<^sub>L, a\<^sub>R \<semicolon>

      val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! \<semicolon>
      if (eq ($k', $k)) \<medium_left_bracket>
        $addr \<tribullet> data \<tribullet> v \<tribullet> v := $v \<semicolon>
        \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close>  \<semicolon>
        return ($addr)
      \<medium_right_bracket> \<medium_left_bracket>
        if (cmp ($k, $k')) \<medium_left_bracket>
            insert_avl_i ($addr \<tribullet> left !, $k, $v) \<rightarrow> val a\<^sub>L' \<semicolon>
            $addr \<tribullet> left := $a\<^sub>L' \<semicolon>
            \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>
            return (maintain_i ($addr))
        \<medium_right_bracket>
        \<medium_left_bracket>
            insert_avl_i ($addr \<tribullet> right !, $k, $v) \<rightarrow> val a\<^sub>R' \<semicolon>
            $addr \<tribullet> right := $a\<^sub>R' \<semicolon>
            \<open>BinTree a\<^sub>L _ _\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>BinTree addr _ _\<close> \<semicolon>

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
  unfolding AVL_Tree.unfold
\<medium_left_bracket>
  insert_avl_i ($addr, $k, $v)
\<medium_right_bracket> .


text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm lookup_bintree_\<phi>app
thm lookup_bst_\<phi>app
thm defined_bintree_\<phi>app
thm defined_bst_\<phi>app
thm insert_bintree_\<phi>app
thm insert_bst_\<phi>app
thm insert_bintree_\<phi>app
thm height_of_\<phi>app
thm maintain_i_\<phi>app
thm insert_avl_i_\<phi>app
thm insert_avl_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm lookup_bintree_def
thm defined_bintree_def
thm insert_bintree_def
thm insert_bintree_def
thm height_of_def
thm maintain_i_def
thm insert_avl_i_def

end

end