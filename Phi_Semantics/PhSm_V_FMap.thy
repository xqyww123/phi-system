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

term fset
term \<open> k' \<Turnstile> (k \<Ztypecolon> K) \<longrightarrow> P \<close>
term rel_option
term Map.empty

term rel_fun
thm rel_funE

\<phi>type_def MapVal :: "(VAL, 'k) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (VAL, 'k \<rightharpoonup> 'v) \<phi>"
  where \<open>f \<Ztypecolon> MapVal K V \<equiv> \<m>\<a>\<p>_rep f' \<Ztypecolon> Itself
        \<s>\<u>\<b>\<j> f'. (\<forall>k' k. k' \<Turnstile> (k \<Ztypecolon> K) \<longrightarrow> rel_option (\<lambda>v' v. v' \<Turnstile> (v \<Ztypecolon> V)) (fmlookup f' k') (f k)) \<close>
  deriving Basic
       and \<open>Abstract_Domain\<^sub>L K P\<^sub>K \<Longrightarrow>
            Abstract_Domain  V P\<^sub>V \<Longrightarrow>
            Abstract_Domain (MapVal K V) (\<lambda>f. \<forall>k. P\<^sub>K k \<longrightarrow> pred_option P\<^sub>V (f k)) \<close>
     (*and \<open>Abstract_Domain K P\<^sub>K \<Longrightarrow>
      Abstract_Domain\<^sub>L  V P\<^sub>V \<Longrightarrow>
      Abstract_Domain\<^sub>L (MapVal K V) (\<lambda>f. \<forall>k. P\<^sub>K k \<longrightarrow> pred_option P\<^sub>V (f k)) \<close>*)
       and \<open>Object_Equiv V eq\<^sub>V \<Longrightarrow>
            Object_Equiv (MapVal K V) (rel_map eq\<^sub>V) \<close>
     notes rel_fun_def[simp]

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