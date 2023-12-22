theory PhiEx_BiTree
  imports Phi_Semantics.PhiSem_C
          "HOL-Data_Structures.Tree_Map"
begin

abbreviation \<open>\<t>\<r>\<e>\<e>_\<n>\<o>\<d>\<e> TY \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {left: \<p>\<t>\<r>, data: TY, right: \<p>\<t>\<r>} \<close>

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
            R \<Ztypecolon> BiTree addr\<^sub>L TY T
            \<s>\<u>\<b>\<j> addr\<^sub>L addr\<^sub>R. \<top> )\<close>
   deriving Basic
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (BiTree addr TY T) (\<lambda>x. pred_tree P x \<and> (x = Leaf \<longleftrightarrow> addr = 0)) \<close>
       and \<open>Identity_Elements\<^sub>E (BiTree addr TY T) (\<lambda>l. addr = 0 \<and> l = Leaf)\<close>  
       and \<open>Identity_Elements\<^sub>I (BiTree addr TY T) (\<lambda>l. l = Leaf) (\<lambda>l. addr = 0)\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (BiTree addr TY) (BiTree addr' TY') T U set_tree (\<lambda>_. UNIV) rel_tree\<close>
           (arbitrary: addr')
       and Functional_Transformation_Functor


term Map.empty
term \<open>()\<close>

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




lemma
  \<open> P (if C then x else y) \<longleftrightarrow> (C \<longrightarrow> P x) \<and> (\<not> C \<longrightarrow> P y)\<close>
  





lemma Object_Equive_of_Lookup_Tree:
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











  
\<phi>type_def Lookup_Tree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'k::linorder) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi>\<close>
  where \<open>f \<Ztypecolon> Lookup_Tree addr TY K V \<equiv> tree \<Ztypecolon> BiTree addr TY \<lbrace> k: K, v: V \<rbrace>
                                       \<s>\<u>\<b>\<j> tree. f = lookup_tree tree \<and> tree_domain_distinct tree\<close>
  deriving \<open> Abstract_Domain\<^sub>L K P\<^sub>K
         \<Longrightarrow> Abstract_Domain V P\<^sub>V
         \<Longrightarrow> Abstract_Domain (Lookup_Tree addr TY K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>
            (tactic: clarsimp, subgoal' for tree x y \<open>induct tree arbitrary: x\<close>)
       and \<open>Identity_Elements\<^sub>E (Lookup_Tree addr TY K V) (\<lambda>l. addr = 0 \<and> l = Map.empty)\<close> 
       and \<open>Identity_Elements\<^sub>I (Lookup_Tree addr TY K V) (\<lambda>l. l = Map.empty) (\<lambda>l. addr = 0)\<close>
       and \<open> Object_Equiv V eq
         \<Longrightarrow> Object_Equiv (Lookup_Tree addr TY K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. eq (the (f k)) (the (g k))) ) \<close>  
            (tactic: clarsimp, 
                     rule exI[where x=\<open>\<lambda>_ g x. map_tree (\<lambda>(k,_). (k, the (g k))) x\<close>],
                     auto simp: Object_Equive_of_Lookup_Tree)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (Lookup_Tree addr TY K) (Lookup_Tree addr' TY' K) T U ran (\<lambda>_. UNIV) rel_map \<close>
            (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ _ y. y\<close>])
       and \<open>Functional_Transformation_Functor (Lookup_Tree addr TY K) (Lookup_Tree addr TY K) T U ran (\<lambda>_. UNIV)
                                              (\<lambda>_ P f. \<forall>x \<in> dom f. P (the (f x))) (\<lambda>f _ x. map_option f o x) \<close>






term \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
              \<Longrightarrow> Transformation_Functor (Lookup_Tree addr TY K) (Lookup_Tree addr' TY' K) T U ran (\<lambda>_. UNIV) rel_map \<close>

term \<open> Object_Equiv V eq
         \<Longrightarrow> Object_Equiv (Lookup_Tree addr TY K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. eq (the (f k)) (the (g k))) ) \<close>


term \<open>Identity_Elements\<^sub>I (Lookup_Tree addr TY K V) (\<lambda>l. l = Map.empty) (\<lambda>l. addr = 0)\<close>

term \<open>Identity_Elements\<^sub>E (Lookup_Tree addr TY K V) (\<lambda>l. addr = 0 \<and> l = Map.empty)\<close>

(* tactic \<open>Simplifier.asm_full_simp_tac (Config.put Simplifier.simp_trace true
        (Config.put Simplifier.simp_trace_depth_limit 5 \<^context>)) 1 o @{print}\<close> *)
term \<open> Abstract_Domain\<^sub>L K P\<^sub>K
         \<Longrightarrow> Abstract_Domain V P\<^sub>V
         \<Longrightarrow> Abstract_Domain (Lookup_Tree addr TY K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>





term set_tree
term \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
              \<Longrightarrow>Transformation_Functor (BiTree addr TY) (BiTree addr' TY') T U set_tree (\<lambda>_. UNIV) rel_tree\<close>


term \<open>Identity_Elements\<^sub>I (BiTree addr TY T) (\<lambda>l. l = Leaf) (\<lambda>l. addr = 0)\<close>
term \<open>Identity_Elements\<^sub>E (BiTree addr TY T) (\<lambda>l. addr = 0 \<and> l = Leaf)\<close>
term rel_tree
term \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (BiTree addr TY T) (\<lambda>x. pred_tree P x \<and> (x = Leaf \<longleftrightarrow> addr = 0)) \<close>


\<phi>type_def Linked_Lst :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>(x#ls \<Ztypecolon> Linked_Lst addr TY T) =
        ((nxt, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> nxt: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Linked_Lst nxt TY T
         \<s>\<u>\<b>\<j> nxt. \<top>)\<close> 
     deriving Basic
          and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst addr TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = 0)) \<close>
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr TY T) (\<lambda>l. l = []) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
              \<Longrightarrow> Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr' TY') T U set (\<lambda>_. UNIV) list_all2 \<close> 
            (arbitrary: addr')
          and Functional_Transformation_Functor

 

end