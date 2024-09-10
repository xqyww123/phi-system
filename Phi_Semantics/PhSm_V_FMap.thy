chapter \<open>Value model of Finite Map\<close>

theory PhSm_V_FMap
  imports PhiSem_Aggregate_Base
  abbrevs "<map>" = "\<m>\<a>\<p>"
begin

section \<open>Semantics\<close>



debt_axiomatization \<m>\<a>\<p> :: \<open>TY \<Rightarrow> TY \<Rightarrow> TY\<close> ("\<m>\<a>\<p> [_,_]")
                and \<m>\<a>\<p>_rep  :: \<open>(VAL,VAL) fmap \<Rightarrow> VAL\<close>
                and \<m>\<a>\<p>_dest :: \<open>VAL \<Rightarrow> (VAL,VAL) fmap\<close>
  where \<m>\<a>\<p>_dest_rep[simp] : \<open>\<m>\<a>\<p>_dest (\<m>\<a>\<p>_rep vs) = vs\<close>
    and \<m>\<a>\<p>_eq_\<p>\<o>\<i>\<s>\<o>\<n>[simp] : \<open>\<m>\<a>\<p>[T,U] = \<p>\<o>\<i>\<s>\<o>\<n> \<longleftrightarrow> T = \<p>\<o>\<i>\<s>\<o>\<n> \<or> U = \<p>\<o>\<i>\<s>\<o>\<n>\<close>
    and \<m>\<a>\<p>_WT             : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<Longrightarrow> 
                              Well_Type \<m>\<a>\<p>[T,U] = { \<m>\<a>\<p>_rep f |f.
                                    fmpred (\<lambda>k v. k \<in> Well_Type T \<and> v \<in> Well_Type U) f }\<close>
    and \<m>\<a>\<p>_WT_uniq        : \<open>\<m>\<a>\<p>_rep f \<in> Well_Type TY \<Longrightarrow> \<exists>T U. TY = \<m>\<a>\<p>[T,U]\<close>
    and \<m>\<a>\<p>_zero           : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<Longrightarrow> Zero \<m>\<a>\<p>[T,U] = Some (\<m>\<a>\<p>_rep fmempty)\<close>
    and \<m>\<a>\<p>_idx_step_type  : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<Longrightarrow> idx_step_type (AgIdx_V v) \<m>\<a>\<p>[T,U] = U \<close>
    and \<m>\<a>\<p>_valid_idx_step : \<open>valid_idx_step \<m>\<a>\<p>[T,U] j \<longleftrightarrow> j \<in> {AgIdx_V v |v. v \<in> Well_Type T \<and> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> }\<close>
    and \<m>\<a>\<p>_idx_step_value : \<open>v |\<in>| fmdom f \<Longrightarrow> idx_step_value (AgIdx_V v) (\<m>\<a>\<p>_rep f) = the (fmlookup f v)\<close>
    and \<m>\<a>\<p>_idx_step_mod_value :
                             \<open>idx_step_mod_value (AgIdx_V v) g (\<m>\<a>\<p>_rep f) = \<m>\<a>\<p>_rep (fmupd v (g (the (fmlookup f v))) f)\<close>

subsubsection \<open>Basic Properties\<close>

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal T
\<Longrightarrow> Is_Type_Literal U
\<Longrightarrow> Is_Type_Literal \<m>\<a>\<p>[T,U] \<close>
  unfolding Is_Type_Literal_def ..


lemma \<m>\<a>\<p>_rep_inj[simp]:
  \<open> \<m>\<a>\<p>_rep f1 = \<m>\<a>\<p>_rep f2 \<longleftrightarrow> f1 = f2 \<close>
  by (metis \<m>\<a>\<p>_dest_rep)

subsubsection \<open>Reduction to poison\<close>

lemma \<m>\<a>\<p>_eq_\<p>\<o>\<i>\<s>\<o>\<n>_red[simp]:
  \<open> \<m>\<a>\<p>[\<p>\<o>\<i>\<s>\<o>\<n>, U] = \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  \<open> \<m>\<a>\<p>[T, \<p>\<o>\<i>\<s>\<o>\<n>] = \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by simp+

section \<open>\<phi>Type\<close>


\<phi>type_def MapVal :: "'k set \<Rightarrow> (VAL, 'k) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (VAL, 'k \<Rightarrow> 'v) \<phi>"
  where \<open>f \<Ztypecolon> MapVal D K V \<equiv> \<m>\<a>\<p>_rep f' \<Ztypecolon> Itself
        \<s>\<u>\<b>\<j> f'. fmdom' f' = concretize K ` D \<and>
                (\<forall>k\<in>D. the (fmlookup f' (concretize K k)) \<Turnstile> (f k \<Ztypecolon> V)) \<close>
  deriving \<open>Abstract_Domain\<^sub>L K P\<^sub>K \<Longrightarrow>
            Abstract_Domain  V P\<^sub>V \<Longrightarrow>
            Abstract_Domain (MapVal D K V) (\<lambda>f. \<forall>k\<in>D. P\<^sub>K k \<longrightarrow> P\<^sub>V (f k)) \<close>
       and \<open>Object_Equiv V eq \<Longrightarrow>
            Object_Equiv (MapVal D K V) (rel_fun (\<lambda>x y. x = y \<and> x \<in> D \<and> y \<in> D) eq) \<close>



lemma Transformation_Functor [\<phi>reason add]:
      \<open> Transformation_Functor (MapVal D K) (MapVal D K) V V' (\<lambda>f. f ` D) (\<lambda>_. UNIV)
                               (rel_fun (\<lambda>x y. x = y \<and> x \<in> D \<and> y \<in> D)) \<close>
  unfolding Transformation_Functor_def Transformation_def Functionality_def rel_fun_def          
            Abstract_Domain\<^sub>L_def \<r>ESC_def rel_fun_def
  apply (clarsimp simp: Satisfiable_def)
 subgoal premises prems for f g v proof -
  
    obtain h where t1: \<open>a\<in>D \<Longrightarrow> v \<Turnstile> (f a \<Ztypecolon> V) \<Longrightarrow> v \<Turnstile> (h a v \<Ztypecolon> V') \<and> g (f a) (h a v)\<close> for a v
      using prems(1) by metis
    show ?thesis
      
      apply (rule exI[where x=\<open>\<lambda>k. h k (the (fmlookup v (concretize K k)))\<close>], auto)
      using prems(3) t1 apply blast
      by (simp add: prems(3) t1)

  qed .





(*
let_\<phi>type MapVal
  deriving \<open>Abstract_Domain K P\<^sub>K \<Longrightarrow>
      Abstract_Domain\<^sub>L  V P\<^sub>V \<Longrightarrow>
      Abstract_Domain\<^sub>L (MapVal K V) (\<lambda>f. \<forall>k. P\<^sub>K k \<longrightarrow> pred_option P\<^sub>V (f k)) \<close>
*)

term \<open>Object_Equiv K eq\<^sub>K \<Longrightarrow>
            Object_Equiv V eq\<^sub>V \<Longrightarrow>
            Object_Equiv (MapVal K V) (rel_fun eq\<^sub>K (rel_option eq\<^sub>V)) \<close>

term \<open> Functionality K P\<^sub>K
    \<Longrightarrow> Functionality V P\<^sub>V
    \<Longrightarrow> Functionality (MapVal K V) P\<^sub>K \<close>

term rel_option
term \<open>(rel_fun (=) (rel_option eq\<^sub>V))\<close>

term \<open>Abstract_Domain K P\<^sub>K \<Longrightarrow>
      Abstract_Domain\<^sub>L  V P\<^sub>V \<Longrightarrow>
      Abstract_Domain\<^sub>L (MapVal K V) (\<lambda>f. \<forall>k. P\<^sub>K k \<longrightarrow> pred_option P\<^sub>V (f k)) \<close>



end