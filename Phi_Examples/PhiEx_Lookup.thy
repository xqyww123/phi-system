theory PhiEx_Lookup
  imports Phi_Semantics.PhiSem_C
begin

typ \<open>('a,'b) fmap\<close>

declare [[\<phi>trace_reasoning = 3]]
 
\<phi>type_def Lookup_Array :: \<open> logaddr \<Rightarrow> (VAL, 'k) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (fiction, 'k \<rightharpoonup> 'v) \<phi> \<close>
  where \<open> f \<Ztypecolon> Lookup_Array addr K V \<equiv> l \<Ztypecolon> \<m>\<e>\<m>[addr] \<Aa>\<r>\<r>\<a>\<y>[n] \<lbrace> k: K, v: V \<rbrace> \<s>\<u>\<b>\<j> l n. f = map_of l \<and> n = length l\<close>
  deriving(* \<open> Abstract_Domain\<^sub>L K P\<^sub>K
         \<Longrightarrow> Abstract_Domain V P\<^sub>V
         \<Longrightarrow> Abstract_Domain (Lookup_Array addr K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>
       and*) \<open> Functionality K F\<^sub>K
         \<Longrightarrow> Object_Equiv V eq
         \<Longrightarrow> Object_Equiv (Lookup_Array addr K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. F\<^sub>K k \<and> eq (the (f k)) (the (g k))) ) \<close>

term \<open>Functionality K \<close>
term \<open>Functionality K F\<^sub>K
  \<Longrightarrow> Object_Equiv V eq
  \<Longrightarrow> Object_Equiv (Lookup_Array addr K V) (\<lambda>f g. dom f = dom g \<and> (\<forall>k \<in> dom f. F\<^sub>K k \<and> eq (the (f k)) (the (g k))) )\<close>

term map_of
term dom

term \<open> Abstract_Domain\<^sub>L K P\<^sub>K
   \<Longrightarrow> Abstract_Domain V P\<^sub>V
   \<Longrightarrow> Abstract_Domain (Lookup_Array addr K V) (\<lambda>f. \<forall>x. x \<in> dom f \<and> P\<^sub>K x \<longrightarrow> P\<^sub>V (the (f x))) \<close>

end