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


\<phi>type_def Lookup_Tree :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'k::linorder) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi>\<close>
  where \<open>f \<Ztypecolon> Lookup_Tree addr TY K V \<equiv> tree \<Ztypecolon> BiTree addr TY \<lbrace> k: K, v: V \<rbrace> \<s>\<u>\<b>\<j> tree. f = lookup tree\<close>
  








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