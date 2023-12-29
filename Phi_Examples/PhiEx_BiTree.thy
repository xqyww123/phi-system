theory PhiEx_BiTree
  imports Phi_Semantics.PhiSem_C
          "HOL-Data_Structures.Tree_Map"
begin

abbreviation \<open>\<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {left: \<p>\<t>\<r>, data: TY, right: \<p>\<t>\<r>} \<close>
abbreviation \<open>\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {k: TY\<^sub>K, v: TY\<^sub>V}\<close>
abbreviation \<open>\<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V \<equiv> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<close>

thm \<phi>constraint_expansion

lemma rel_tree_Leaf[\<phi>constraint_expansion, iff]:
  \<open> rel_tree R \<langle>\<rangle> tree \<longleftrightarrow> tree = \<langle>\<rangle> \<close>
  \<open> rel_tree R tree' \<langle>\<rangle> \<longleftrightarrow> tree' = \<langle>\<rangle> \<close>
  by (metis tree.rel_sel)+

lemma rel_tree_Node1[\<phi>constraint_expansion]:
  \<open> NO_MATCH \<langle>L', y, R'\<rangle> tree
\<Longrightarrow> rel_tree r \<langle>L, x, R\<rangle> tree \<longleftrightarrow> (\<exists>L' y R'. tree = \<langle>L', y, R'\<rangle> \<and> rel_tree r L L' \<and> r x y \<and> rel_tree r R R') \<close>
  using Tree.tree.rel_cases by fastforce


lemma rel_tree__pred_tree:
  \<open>rel_tree R x y \<Longrightarrow> pred_tree (\<lambda>x. \<exists>y. R x y) x\<close>
  by (induct x arbitrary: y; auto_sledgehammer)

setup \<open>Context.theory_map (Phi_Type_Derivers.Expansion.map (fn ctxt =>
          ctxt addsimps @{thms' rel_tree_Leaf rel_tree_Node1}))\<close>

thm tree.rel_sel












declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def BiTree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x tree) \<phi>\<close>
  where \<open> (Leaf \<Ztypecolon> BiTree addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0) \<close>
      | \<open> (\<langle>L, x, R\<rangle> \<Ztypecolon> BiTree addr TY T) =
          ((addr\<^sub>L, x, addr\<^sub>R) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> left: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY, data: T, right: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY \<rbrace>\<heavy_comma>
            L \<Ztypecolon> BiTree addr\<^sub>L TY T\<heavy_comma>
            R \<Ztypecolon> BiTree addr\<^sub>R TY T
            \<s>\<u>\<b>\<j> addr\<^sub>L addr\<^sub>R. \<top> )\<close>
   deriving Basic
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (BiTree addr TY T) (\<lambda>x. pred_tree P x \<and> (x = Leaf \<longleftrightarrow> addr = 0)) \<close>
       and \<open>Identity_Elements\<^sub>E (BiTree addr TY T) (\<lambda>l. addr = 0 \<and> l = Leaf)\<close>  
       and \<open>Identity_Elements\<^sub>I (BiTree addr TY T) (\<lambda>l. l = Leaf) (\<lambda>l. addr = 0)\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (BiTree addr TY) (BiTree addr' TY') T U set_tree (\<lambda>_. UNIV) rel_tree\<close>
           (arbitrary: addr')
       and Functional_Transformation_Functor


primrec lookup_tree :: \<open>('k \<times> 'v) tree \<Rightarrow> 'k \<rightharpoonup> 'v\<close>
  where \<open>lookup_tree \<langle>\<rangle> = Map.empty\<close>
      | \<open>lookup_tree \<langle>L, x, R\<rangle> = (lookup_tree L ++ lookup_tree R)(fst x \<mapsto> snd x) \<close>

lemma dom_lookup_tree[iff]:
  \<open> dom (lookup_tree tree) = fst ` set_tree tree \<close>
  by (induct tree; auto_sledgehammer)

primrec tree_domain_distinct :: \<open>('k \<times> 'v) tree \<Rightarrow> bool\<close>
  where \<open>tree_domain_distinct \<langle>\<rangle> = True \<close>
      | \<open>tree_domain_distinct \<langle>L, x, R\<rangle> = (fst ` set_tree L \<inter> fst ` set_tree R = {} \<and>
                                           fst x \<notin> fst ` set_tree L \<and> fst x \<notin> fst ` set_tree R \<and>
                                           tree_domain_distinct L \<and> tree_domain_distinct R)\<close>




lemma lookup_tree_eq_empty:
  \<open> lookup_tree tree = Map.empty \<longleftrightarrow> tree = \<langle>\<rangle> \<close>
  by (induct tree; auto_sledgehammer)

lemma tree_domain_distinct_map[iff]:
  \<open>tree_domain_distinct (Tree.tree.map_tree (\<lambda>(k, v). (k, f k v)) tree) \<longleftrightarrow> tree_domain_distinct tree\<close>
  by (induct tree; auto_sledgehammer)

lemma lookup_tree_by_set_distinct:
  \<open> (k, v) \<in> Tree.tree.set_tree tree
\<Longrightarrow> tree_domain_distinct tree
\<Longrightarrow> lookup_tree tree k = Some v \<close>
  by (induct tree; auto_sledgehammer)

lemma rel_tree_domain_eq:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> fst ` set_tree x = fst ` set_tree y \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1; auto_sledgehammer)

lemma rel_tree_domain_distinct:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> tree_domain_distinct x \<longleftrightarrow> tree_domain_distinct y \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1; auto_sledgehammer)

lemma rel_tree_implies_list_all2:
  \<open> rel_tree r x y \<Longrightarrow> list_all2 r (inorder x) (inorder y) \<close>
  by (induct x arbitrary: y; auto;
      smt (verit, del_insts) Tree.tree.distinct(2) Tree.tree.inject Tree.tree.rel_cases append_Cons append_Nil inorder.simps(2) list.rel_intros(2) list_all2_appendI)


lemma rel_tree__map_fst_eq:
  \<open> rel_tree (\<lambda>a b. fst a = fst b) x y
\<Longrightarrow> map fst (inorder x) = map fst (inorder y) \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_tree_Node1; auto_sledgehammer)


lemma rel_map_lookup_by_rel_tree:
  \<open> rel_tree (\<lambda>a b. fst a = fst b \<and> r (snd a) (snd b)) x y
\<Longrightarrow> tree_domain_distinct x
\<Longrightarrow> rel_map r (lookup_tree x) (lookup_tree y) \<close>
  by (induct x arbitrary: y; auto simp: set_eq_iff rel_fun_def rel_tree_Node1 split: option.split; auto_sledgehammer)

(*
primrec sorted_tree :: "('a \<Rightarrow> 'k::ord) => 'a tree => bool"
  where "sorted_tree h \<langle>\<rangle> = True"
      | "sorted_tree h \<langle>L, x, R\<rangle> = 
          (sorted_tree h L \<and>
           (\<forall>l \<in> set_tree L. h l < h x) \<and>
           (\<forall>r \<in> set_tree R. h x < h r) \<and>
           sorted_tree h R)"
*)

term cmp
term lookup
term map_of

lemma AList_Upd_map_of_is_Map_map_of[iff]:
  \<open>map_of l = Map.map_of l\<close>
  by (induct l; auto)
(*
lemma dom_lookup_tree_map[iff]:
  \<open> dom (lookup_tree (map_tree (\<lambda>(k,v). (k, f k v)) tree)) = dom (lookup_tree tree) \<close>
  by (induct tree; auto_sledgehammer)*)


lemma Object_Equive_of_Bin_Search_Tree:
  \<open> fst ` Tree.tree.set_tree xa = dom y \<Longrightarrow>
     tree_domain_distinct xa \<Longrightarrow>
    y = lookup_tree (Tree.tree.map_tree (\<lambda>(k, _). (k, the (y k))) xa) \<close>
  apply (induct xa arbitrary: y, auto_sledgehammer,
         auto simp: fun_eq_iff set_eq_iff map_add_def image_Un Ball_def split: option.split if_split)
  apply (metis domIff insertI1 option.exhaust_sel)
  subgoal premises prems for xa1 a xa2 y x
    apply (cases \<open>x \<in> fst ` set_tree xa1\<close>)
    subgoal premises prems2 proof -
      have t2: \<open>Tree.tree.map_tree (\<lambda>(k, _). (k, the ((y |` (fst ` set_tree xa1)) k))) xa1 =
                Tree.tree.map_tree (\<lambda>(k, _). (k, the (y k))) xa1\<close>
        by (rule tree.map_cong0, auto_sledgehammer)
      have \<open>y x = (y |` (fst ` set_tree xa1)) x\<close>
        unfolding restrict_map_def
        by auto_sledgehammer
      also have  \<open>\<dots> = lookup_tree (Tree.tree.map_tree (\<lambda>(k, _). (k, the ((y |` (fst ` set_tree xa1)) k))) xa1) x\<close>
        by (rule prems(1)[THEN spec]; auto_sledgehammer)
      finally show ?thesis by auto_sledgehammer
    qed by auto_sledgehammer
  apply auto_sledgehammer

  subgoal premises prems for xa1 a xa2 y x x2
    apply (cases \<open>x \<in> dom (lookup_tree xa2)\<close>)
    subgoal premises prems2 proof -
      have t2: \<open>Tree.tree.map_tree (\<lambda>(k, _). (k, the ((y |` (fst ` set_tree xa2)) k))) xa2 =
                Tree.tree.map_tree (\<lambda>(k, _). (k, the (y k))) xa2\<close>
        by (rule tree.map_cong0, auto_sledgehammer)
      have \<open>y x = (y |` (fst ` set_tree xa2)) x\<close>
        unfolding restrict_map_def
        by auto_sledgehammer
      also have  \<open>\<dots> = lookup_tree (Tree.tree.map_tree (\<lambda>(k, _). (k, the ((y |` (fst ` set_tree xa2)) k))) xa2) x\<close>
        by (rule prems(2)[THEN spec]; auto_sledgehammer)
      finally show ?thesis by auto_sledgehammer
    qed by auto_sledgehammer .

lemma rel_tree_self_map:
  \<open> \<forall>a \<in> set_tree x. R a (f a)
\<Longrightarrow> rel_tree R x (map_tree f x) \<close>
  by (induct x; auto)


declare rel_fun_eq[iff]





lemma tree_sorted1_inorder_implies_domain_distinct:
  \<open>sorted1(inorder tree) \<Longrightarrow> tree_domain_distinct tree\<close>
  by (induct tree; auto_sledgehammer)

lemma sorted1_inorder_map_tree[iff]:
  \<open>sorted1 (inorder (map_tree (\<lambda>(k, v). (k, f k v)) tree)) \<longleftrightarrow> sorted1 (inorder tree)\<close>
  by auto_sledgehammer









   
\<phi>type_def Bin_Search_Tree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> (VAL, 'k::linorder) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi>\<close>
  where \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V \<equiv> tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>
                                       \<s>\<u>\<b>\<j> tree. f = lookup_tree tree \<and> sorted1(inorder tree)\<close>
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
                     auto simp: Object_Equive_of_Bin_Search_Tree)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY\<^sub>K' = TY\<^sub>K \<and> TY\<^sub>V' = TY\<^sub>V \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) (Bin_Search_Tree addr' TY\<^sub>K' TY\<^sub>V' K) T U ran (\<lambda>_. UNIV) rel_map \<close>
            (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ _ y. y\<close>])
       and \<open>Functional_Transformation_Functor (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) (Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K) T U ran (\<lambda>_. UNIV)
                                              (\<lambda>_ P f. \<forall>x \<in> dom f. P (the (f x))) (\<lambda>f _ x. map_option f o x) \<close>






lemma lookup_left_children:
  \<open> sorted1 (inorder tree)
\<Longrightarrow> lookup_tree (left tree) = lookup_tree tree |` {x. x < fst (value tree)} \<close>
  \<comment> \<open>this value is the value of the root node\<close>
  by (induct tree; auto simp: fun_eq_iff restrict_map_def; auto_sledgehammer)

lemma lookup_right_children:
  \<open> sorted1 (inorder tree)
\<Longrightarrow> lookup_tree (right tree) = lookup_tree tree |` {x. fst (value tree) < x} \<close>
  by (induct tree; auto simp: fun_eq_iff restrict_map_def; auto_sledgehammer)


declare [[auto_sledgehammer_params = "try0 = false"]]
  \<comment> \<open>For some reason I don't know, sledgehammer fails silently (with throwing an Interrupt exception)
      when \<open>try0\<close> --- reconstructing proofs using classical tactics --- is enabled.\<close>



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
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY\<^sub>K K zero\<^sub>K\<close> \<comment> \<open>TODO: remove this once our semantics has non-deterministic \<open>malloc\<close>\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY\<^sub>V V zero\<^sub>V\<close> \<comment> \<open>TODO: remove this once our semantics has non-deterministic \<open>malloc\<close>\<close>
begin


proc lookup_bintree:
  input  \<open>tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  premises \<open>k \<in> dom (lookup_tree tree) \<and> sorted1(inorder tree)\<close>
  output \<open>tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          the (lookup_tree tree k) \<Ztypecolon> \<v>\<a>\<l> V\<close>
  is [recursive tree addr]
  is [routine]
\<medium_left_bracket>
  to \<open>OPEN 1 _\<close> certified by (of_tac \<open>left tree\<close> \<open>value tree\<close> \<open>right tree\<close>, auto_sledgehammer) ;; \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R, N\<^sub>k, N\<^sub>v  \<comment> \<open>TODO: fix quantifier names\<close>
  
  val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! ;;
  if (eq ($k', $k)) \<medium_left_bracket>
    val ret \<leftarrow> $addr \<tribullet> data \<tribullet> v ! ;;
    \<open> _ \<Ztypecolon> MAKE 1 (BiTree addr _ _)\<close> certified by (of_tac \<open>(N\<^sub>k,N\<^sub>v)\<close>, auto_sledgehammer) ;;
    return ($ret)
  \<medium_right_bracket>
  \<medium_left_bracket>
    if (cmp ($k, $k'))
    \<medium_left_bracket> lookup_bintree ($addr \<tribullet> left  !, $k) \<medium_right_bracket>
    \<medium_left_bracket> lookup_bintree ($addr \<tribullet> right !, $k) \<medium_right_bracket> \<rightarrow> val ret ;;
    \<open>BiTree a\<^sub>R _ _\<close> \<open> _ \<Ztypecolon> MAKE 1 (BiTree addr _ _)\<close> certified by (of_tac \<open>(N\<^sub>k,N\<^sub>v)\<close>, auto_sledgehammer) ;;
    return ($ret)
  \<medium_right_bracket>
\<medium_right_bracket> .


proc (nodef) lookup_bst:
  input  \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  premises \<open>k \<in> dom f\<close>
  output \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> the (f k) \<Ztypecolon> \<v>\<a>\<l> V\<close>
  is [recursive f addr]
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  lookup_bintree ($addr, $k) \<rightarrow> val ret ;;
  \<open>f \<Ztypecolon> MAKE _ (Bin_Search_Tree addr _ _ _ _)\<close> ;;
  $ret
\<medium_right_bracket> .


proc has_key_bintree:
  input  \<open>tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  premises \<open>sorted1(inorder tree)\<close>
  output \<open>tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          k \<in> dom (lookup_tree tree) \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  is [recursive tree addr]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    return (False)
  \<medium_right_bracket>
  \<medium_left_bracket>
    to \<open>OPEN 1 _\<close> certified by (of_tac \<open>left tree\<close> \<open>value tree\<close> \<open>right tree\<close>, auto_sledgehammer) ;; \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R, N\<^sub>k, N\<^sub>v

    val k' \<leftarrow> $addr \<tribullet> data \<tribullet> k ! ;;
    if (eq ($k', $k)) \<medium_left_bracket>
      True
    \<medium_right_bracket> \<medium_left_bracket> 
      if (cmp ($k, $k'))
      \<medium_left_bracket> has_key_bintree ($addr \<tribullet> left  !, $k) \<medium_right_bracket>
      \<medium_left_bracket> has_key_bintree ($addr \<tribullet> right !, $k) \<medium_right_bracket>
    \<medium_right_bracket> \<rightarrow> val ret ;;

    \<open>BiTree a\<^sub>R _ _\<close> \<open> _ \<Ztypecolon> MAKE 1 (BiTree addr _ _)\<close> certified by (of_tac \<open>(N\<^sub>k,N\<^sub>v)\<close>, auto_sledgehammer) ;; 
    return ($ret)
  \<medium_right_bracket> ;;
\<medium_right_bracket> .


proc has_key_bst:
  input  \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> K\<close>
  output \<open>f \<Ztypecolon> Bin_Search_Tree addr TY\<^sub>K TY\<^sub>V K V\<heavy_comma> k \<in> dom f \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  has_key_bintree ($addr, $k) \<rightarrow> val ret ;;
  \<open>f \<Ztypecolon> MAKE _ (Bin_Search_Tree addr _ _ _ _)\<close>
  $ret
\<medium_right_bracket> .




primrec insert_tree :: \<open>'k::linorder \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) tree \<Rightarrow> ('k \<times> 'v) tree\<close>
  where \<open>insert_tree k v \<langle>\<rangle> = \<langle>\<langle>\<rangle>, (k,v), \<langle>\<rangle>\<rangle>\<close>
      | \<open>insert_tree k v \<langle>L, x, R\<rangle> = (if k < fst x then \<langle>insert_tree k v L, x, R\<rangle>
                                     else if k = fst x then \<langle>L, (k,v), R\<rangle>
                                     else \<langle>L, x, insert_tree k v R\<rangle> ) \<close>


abbreviation \<open>Bst_Node \<equiv> \<lbrace>
                            left: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V),
                            data: \<lbrace> k: K, v: V \<rbrace>,
                            right: \<Pp>\<t>\<r> \<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V)
                          \<rbrace> \<close>





proc insert_bintree:
  input  \<open>tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V\<heavy_comma>
          k \<Ztypecolon> \<v>\<a>\<l> K\<heavy_comma>
          v \<Ztypecolon> \<v>\<a>\<l> V\<close>
  output \<open>insert_tree k v tree \<Ztypecolon> BiTree addr' (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    calloc_1 \<open>Bst_Node\<close> \<rightarrow> val ret;;
      note [[\<phi>trace_reasoning = 2]] ;;
return ($ret)

    thm return_\<phi>app












definition \<open>right_rotate tree = (case tree of \<langle>\<langle>A, B, C\<rangle>, D, E\<rangle> \<Rightarrow> \<langle>A, B, \<langle>C, D, E\<rangle>\<rangle> )\<close>
definition \<open>can_right_rotate tree = (case tree of \<langle>\<langle>A, B, C\<rangle>, D, E\<rangle> \<Rightarrow> True | _ \<Rightarrow> False)\<close>
definition \<open>left_rotate tree = (case tree of \<langle>A, B, \<langle>C, D, E\<rangle>\<rangle> \<Rightarrow> \<langle>\<langle>A, B, C\<rangle>, D, E\<rangle> )\<close>
definition \<open>can_left_rotate tree = (case tree of \<langle>A, B, \<langle>C, D, E\<rangle>\<rangle> \<Rightarrow> True | _ \<Rightarrow> False)\<close>

lemma right_rotate_simp[simp]:
  \<open> right_rotate \<langle>\<langle>A, B, C\<rangle>, D, E\<rangle> = \<langle>A, B, \<langle>C, D, E\<rangle>\<rangle> \<close>
  unfolding right_rotate_def by simp

lemma left_rotate_simp[simp]:
  \<open> left_rotate \<langle>A, B, \<langle>C, D, E\<rangle>\<rangle> = \<langle>\<langle>A, B, C\<rangle>, D, E\<rangle> \<close>
  unfolding left_rotate_def by simp












term left

proc right_Rotate:
  input \<open>tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V \<close>
  premises \<open>can_right_rotate tree\<close>
  output \<open>right_rotate tree \<Ztypecolon> BiTree addr' (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace> \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  from \<open>can_right_rotate tree\<close>[unfolded can_right_rotate_def]
  obtain A B C D E where open_tree: \<open>tree = \<langle>\<langle>A, B, C\<rangle>, D, E\<rangle>\<close> by auto_sledgehammer ;;
  
  unfold open_tree to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R ;;
  \<open>BiTree a\<^sub>L _ _\<close> to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>L\<^sub>L, a\<^sub>L\<^sub>R ;;

  $addr \<tribullet> left ! \<rightarrow> val B ;;
  $addr \<tribullet> left := $B \<tribullet> right ! ;;
  $B \<tribullet> right := $addr ;;

  \<open>BiTree a\<^sub>R _ _\<close> \<open>_ \<Ztypecolon> MAKE 1 (BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>)\<close> ;;
  \<open>_ \<Ztypecolon> MAKE 1 (BiTree a\<^sub>L (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>)\<close>
\<medium_right_bracket> .


proc left_Rotate:
  input \<open>tree \<Ztypecolon> BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<b>\<s>\<t>_\<n>\<o>\<d>\<e> TY\<^sub>K TY\<^sub>V \<close>
  premises \<open>can_left_rotate tree\<close>
  output \<open>left_rotate tree \<Ztypecolon> BiTree addr' (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace> \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  from \<open>can_left_rotate tree\<close>[unfolded can_right_rotate_def]
  obtain A B C D E where open_tree: \<open>tree = \<langle>A, B, \<langle>C, D, E\<rangle>\<rangle>\<close> by auto_sledgehammer ;;

  unfold open_tree to \<open>OPEN 1 _\<close> \<exists>t\<^sub>1, a\<^sub>L, a\<^sub>R ;;
  \<open>BiTree a\<^sub>R _ _\<close> to \<open>OPEN 1 _\<close> \<exists>t\<^sub>2, a\<^sub>R\<^sub>L, a\<^sub>R\<^sub>R ;;

  $addr \<tribullet> right ! \<rightarrow> val D ;;
  $addr \<tribullet> right := $D \<tribullet> left ! ;;
  $D \<tribullet> left := $addr ;;

  \<open>BiTree a\<^sub>L _ _\<close> \<open>BiTree a\<^sub>R\<^sub>L _ _\<close> \<open>_ \<Ztypecolon> MAKE 1 (BiTree addr (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>)\<close> ;;
  \<open>BiTree a\<^sub>R\<^sub>R _ _\<close> \<open>_ \<Ztypecolon> MAKE 1 (BiTree a\<^sub>R (\<k>\<v>_\<p>\<a>\<i>\<r> TY\<^sub>K TY\<^sub>V) \<lbrace> k: K, v: V \<rbrace>)\<close>
\<medium_right_bracket> .










end

end