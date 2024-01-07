theory PhiEx_Lookup
  imports Phi_Semantics.PhiSem_C
begin

typ \<open>('a,'b) fmap\<close>


term rel_prod

lemma rel_map_map_of__list_all2:
  \<open> list_all2 (rel_prod (=) R) x y
\<Longrightarrow> rel_map R (map_of x) (map_of y) \<close>
  by (induct x arbitrary: y; auto_sledgehammer)


declare list.pred_True[simp]
 
\<phi>type_def Lookup_Array :: \<open> logaddr \<Rightarrow> (VAL, 'k) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi> \<close>
  where \<open> f \<Ztypecolon> Lookup_Array addr K V \<equiv> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<Aa>\<r>\<r>\<a>\<y>[n] \<lbrace> k: K, v: V \<rbrace> \<s>\<u>\<b>\<j> l n. f = map_of l \<and> n = length l \<and> distinct (map fst l)\<close>
  deriving \<open> Abstract_Domain\<^sub>L K P\<^sub>K
         \<Longrightarrow> Abstract_Domain V P\<^sub>V
         \<Longrightarrow> Abstract_Domain (Lookup_Array addr K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>
       and \<open> Object_Equiv V eq
         \<Longrightarrow> Object_Equiv (Lookup_Array addr K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. eq (the (f k)) (the (g k))) ) \<close>
            (tactic: clarsimp,
                     rule exI[where x=\<open>\<lambda>_ g x. map (\<lambda>(k,_). (k, the (g k))) x\<close>],
                     auto simp: list_all2_conv_all_nth Ball_def,
                     subgoal' for y x \<open>rule ext, induct x arbitrary: y\<close>)
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> addr' = addr \<and> K' = K
        \<Longrightarrow> Transformation_Functor (Lookup_Array addr K) (Lookup_Array addr' K') T U ran (\<lambda>_. UNIV) rel_map \<close>
            (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ _ y. y\<close>], auto simp: list_all2_conv_all_nth)
      and \<open>Functional_Transformation_Functor (Lookup_Array addr K) (Lookup_Array addr K) T U ran (\<lambda>_. UNIV)
                                             (\<lambda>_ P f. \<forall>x \<in> dom f. P (the (f x))) (\<lambda>f _ x. map_option f o x) \<close>
      and Identity_Elements

term \<open>Identity_Elements\<^sub>I (Lookup_Array addr K V)
                         (\<lambda>f. f = Map.empty) \<close>



(* \<open>Separation_Homo\<^sub>I (Lookup_Array addr K) (Lookup_Array addr K) (Lookup_Array addr K) T U
                       {(f,g). dom f = dom g } zip_partial_map \<close>
  notes dom_map_of_conv_image_fst[simp] t1[simp]

*)


term \<open>(\<forall>x \<in> dom f. P (the (f x)))\<close>
term pred_fun
term Finite_Map.fun.Finite_Map.fmap.fun.map_fun


term \<open>Transformation_Functor (Lookup_Array addr K) (Lookup_Array addr K) T U ran (\<lambda>_. UNIV) (rel_fun (=) o rel_option) \<close>

term \<open>rel_fun (=) o rel_option\<close>
term \<open>rel_option\<close>

term rel_map
thm  list_all2_reduct_rel




lemma
  \<open> (rel_fun (=) o rel_option) (=) = (=) \<close>
  unfolding fun_eq_iff
  apply clarsimp
  by (simp add: option.rel_eq rel_fun_eq_rel)

term \<open>Functionality K \<close>
term \<open>Functionality K F\<^sub>K
  \<Longrightarrow> Object_Equiv V eq
  \<Longrightarrow> Object_Equiv (Lookup_Array addr K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. F\<^sub>K k \<and> eq (the (f k)) (the (g k))) )\<close>

thm image_iff

lemma
  \<open> dom (map_of xa) = dom y \<Longrightarrow>
     \<forall>k\<in>dom y. eq (the (map_of xa k)) (the (y k)) \<Longrightarrow>
     \<forall>x. eq x x \<Longrightarrow>
     \<forall>x y. eq x y \<longrightarrow> Inhabited (x \<Ztypecolon> V) \<longrightarrow> Inhabited (y \<Ztypecolon> V) \<Longrightarrow>
     distinct (map fst xa) \<Longrightarrow>
     memaddr.blk addr \<noteq> Null \<Longrightarrow>
     list_all (\<lambda>x. Inhabited (snd x \<Ztypecolon> V) \<and> Inhabited (fst x \<Ztypecolon> K)) xa \<Longrightarrow>
     list_all2 (\<lambda>x y. eq (snd x) (snd y) \<and> fst x = fst y) xa (map (\<lambda>(k, _). (k, the (y k))) xa) \<close>
  apply (auto simp: list_all2_conv_all_nth)
  apply (smt (verit, ccfv_SIG) Some_eq_map_of_iff case_prod_beta' domI nth_mem old.prod.inject option.sel surjective_pairing)
  by (simp add: case_prod_unfold)

term map_of
term dom

thm map_of_map

term \<open> Abstract_Domain\<^sub>L K P\<^sub>K
   \<Longrightarrow> Abstract_Domain V P\<^sub>V
   \<Longrightarrow> Abstract_Domain (Lookup_Array addr K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>

end