chapter \<open>Value model of Finite Map\<close>

theory PhSm_V_FMap
  imports PhSm_Ag_Base
  abbrevs "<map>" = "\<m>\<a>\<p>"
begin

section \<open>Semantics\<close>

debt_axiomatization \<m>\<a>\<p> :: \<open>TY \<Rightarrow> TY \<Rightarrow> TY\<close> ("\<m>\<a>\<p> [_,_]")
                and \<m>\<a>\<p>_rep  :: \<open>(sVAL \<Rightarrow> VAL) \<Rightarrow> VAL\<close>
  where \<m>\<a>\<p>_rep_inj [simp] : \<open>\<m>\<a>\<p>_rep vsT = \<m>\<a>\<p>_rep vsT' \<longleftrightarrow> vsT = vsT'\<close>
    and \<m>\<a>\<p>_eq_\<p>\<o>\<i>\<s>\<o>\<n>[simp] : \<open>\<m>\<a>\<p>[T,U] = \<p>\<o>\<i>\<s>\<o>\<n> \<longleftrightarrow> T = \<p>\<o>\<i>\<s>\<o>\<n> \<or> U = \<p>\<o>\<i>\<s>\<o>\<n> \<or> \<not> is_sTY T\<close>
    and \<m>\<a>\<p>_WT             : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> is_sTY T \<Longrightarrow> 
                              Well_Type \<m>\<a>\<p>[T,U] = { \<m>\<a>\<p>_rep f |f. (\<forall>k. f k \<in> Well_Type U) }\<close>
    and \<m>\<a>\<p>_WT_uniq        : \<open>\<m>\<a>\<p>_rep fU \<in> Well_Type TY \<Longrightarrow> \<exists>T U. TY = \<m>\<a>\<p>[T,U]\<close>
    and \<m>\<a>\<p>_zero           : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> is_sTY T \<Longrightarrow>
                              Zero \<m>\<a>\<p>[T,U] = map_option (\<lambda>v. \<m>\<a>\<p>_rep (\<lambda>_. v)) (Zero U)\<close>
    and \<m>\<a>\<p>_idx_step_type  : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> is_sTY T \<Longrightarrow>
                              idx_step_type (AgIdx_V v) \<m>\<a>\<p>[T,U] = U \<close>
    and \<m>\<a>\<p>_valid_idx_step : \<open>T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> is_sTY T \<Longrightarrow>
                              valid_idx_step \<m>\<a>\<p>[T,U] j \<longleftrightarrow> j \<in> {AgIdx_V v |v. sVAL_emb v \<in> Well_Type T }\<close>
    and \<m>\<a>\<p>_idx_step_value : \<open>idx_step_value (AgIdx_V v) (\<m>\<a>\<p>_rep f) = f v\<close>
    and \<m>\<a>\<p>_idx_step_mod_value :
                             \<open>idx_step_mod_value (AgIdx_V v) g (\<m>\<a>\<p>_rep f) = \<m>\<a>\<p>_rep (f(v := g (f v)))\<close>


subsubsection \<open>Basic Properties\<close>

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal U
\<Longrightarrow> Is_Type_Literal \<m>\<a>\<p>[T,U] \<close>
  unfolding Is_Type_Literal_def ..


subsubsection \<open>Reduction to poison\<close>

lemma \<m>\<a>\<p>_eq_\<p>\<o>\<i>\<s>\<o>\<n>_red[simp]:
  \<open> \<m>\<a>\<p>[T, \<p>\<o>\<i>\<s>\<o>\<n>] = \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  \<open> \<m>\<a>\<p>[\<p>\<o>\<i>\<s>\<o>\<n>, U] = \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  by simp+

lemma is_sTY_typeof:
  \<open> is_sTY (\<t>\<y>\<p>\<e>\<o>\<f> K)
\<Longrightarrow> \<t>\<y>\<p>\<e>\<o>\<f> K \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>
\<Longrightarrow> v \<Turnstile> (x \<Ztypecolon> K)
\<Longrightarrow> v \<in> range sVAL_emb \<close>
  by (meson SType_Of_not_poison is_sTY)



section \<open>\<phi>Type\<close>

\<phi>type_def VMap :: "(VAL, 'k) \<phi> \<Rightarrow> 'k set \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (VAL, 'k \<Rightarrow> 'v) \<phi>"
                    ("_ \<equiv>'(_')\<Rrightarrow> _" [76,20,75] 75)
  where \<open>f \<Ztypecolon> VMap K D V \<equiv> \<m>\<a>\<p>_rep f' \<Ztypecolon> Itself
        \<s>\<u>\<b>\<j> f'. is_sTY (\<t>\<y>\<p>\<e>\<o>\<f> K) \<and> \<t>\<y>\<p>\<e>\<o>\<f> K \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> \<t>\<y>\<p>\<e>\<o>\<f> V \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>
               \<and> (\<forall>kk k. sVAL_emb kk \<Turnstile> (k \<Ztypecolon> K) \<and> k \<in> D     \<longrightarrow> f' kk \<Turnstile> (f k \<Ztypecolon> V))
               \<and> (\<forall>kk. (\<nexists>k. sVAL_emb kk \<Turnstile> (k \<Ztypecolon> K) \<and> k \<in> D) \<longrightarrow> f' kk = the (Zero (\<t>\<y>\<p>\<e>\<o>\<f> V))) \<close>
  deriving \<open>Abstract_Domain\<^sub>L K P\<^sub>K \<Longrightarrow>
            Abstract_Domain  V P\<^sub>V \<Longrightarrow>
            Abstract_Domain (VMap K D V) (\<lambda>f. \<forall>k\<in>D. P\<^sub>K k \<longrightarrow> P\<^sub>V (f k)) \<close>
       and \<open>Abstract_Domain K D \<Longrightarrow>
            Object_Equiv V eq \<Longrightarrow>
            Object_Equiv (VMap K DD V) (rel_fun (\<lambda>x y. x = y \<and> D x \<and> D y) eq) \<close>

abbreviation Total_VMap :: "(VAL, 'k) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (VAL, 'k \<Rightarrow> 'v) \<phi>"
                            ("_ \<equiv>\<Rrightarrow> _" [76,75] 75)
  where \<open>K \<equiv>\<Rrightarrow> V \<equiv> K \<equiv>(UNIV)\<Rrightarrow> V\<close>

lemma has_Zero_\<m>\<a>\<p> [simp]:
  \<open> has_Zero (\<m>\<a>\<p>[K, V]) \<longleftrightarrow> K \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> is_sTY K \<and> has_Zero V \<close>
  unfolding has_Zero_def
  by (cases \<open>K = \<p>\<o>\<i>\<s>\<o>\<n>\<close>; cases \<open>V = \<p>\<o>\<i>\<s>\<o>\<n>\<close>; cases \<open>is_sTY K\<close>; auto simp: \<m>\<a>\<p>_zero;
      metis Zero_\<p>\<o>\<i>\<s>\<o>\<n> \<m>\<a>\<p>_eq_\<p>\<o>\<i>\<s>\<o>\<n>)


lemma \<t>\<y>\<p>\<e>\<o>\<f>_VMap [simp]:
  \<open> has_Zero (\<t>\<y>\<p>\<e>\<o>\<f> V)
\<Longrightarrow> \<t>\<y>\<p>\<e>\<o>\<f> (VMap K D V) = \<m>\<a>\<p>[\<t>\<y>\<p>\<e>\<o>\<f> K, \<t>\<y>\<p>\<e>\<o>\<f> V]\<close>
proof -

  have t1: \<open>(\<p>\<o>\<i>\<s>\<o>\<n> = \<m>\<a>\<p> [T,U]) = (T = \<p>\<o>\<i>\<s>\<o>\<n> \<or> U = \<p>\<o>\<i>\<s>\<o>\<n> \<or> \<not> is_sTY T)\<close> for T U
    by (metis \<m>\<a>\<p>_eq_\<p>\<o>\<i>\<s>\<o>\<n>)

  have t2: \<open>(\<t>\<y>\<p>\<e>\<o>\<f> K = \<p>\<o>\<i>\<s>\<o>\<n>) = (\<not> Inhabited K \<or> (\<exists>x v. v \<Turnstile> (x \<Ztypecolon> K) \<and> v \<notin> Well_Type (\<t>\<y>\<p>\<e>\<o>\<f> K)))\<close> for K
    by (metis SType_Of_not_poison)

  show \<open> has_Zero (\<t>\<y>\<p>\<e>\<o>\<f> V)
    \<Longrightarrow> \<t>\<y>\<p>\<e>\<o>\<f> (VMap K D V) = \<m>\<a>\<p>[\<t>\<y>\<p>\<e>\<o>\<f> K, \<t>\<y>\<p>\<e>\<o>\<f> V]\<close>
    unfolding SType_Of_def[where T=\<open>VMap K D V\<close>] Inhabited_def
    apply (auto simp: Satisfiable_def,
           rule some1_equality, rule, assumption,
           (unfold Semantic_Type_def; clarsimp; cases \<open>\<t>\<y>\<p>\<e>\<o>\<f> K = \<p>\<o>\<i>\<s>\<o>\<n>\<close>; cases \<open>\<t>\<y>\<p>\<e>\<o>\<f> V = \<p>\<o>\<i>\<s>\<o>\<n>\<close>; simp; metis Well_Type_unique),
           (unfold Semantic_Type_def;  cases \<open>\<t>\<y>\<p>\<e>\<o>\<f> K = \<p>\<o>\<i>\<s>\<o>\<n>\<close>; cases \<open>\<t>\<y>\<p>\<e>\<o>\<f> V = \<p>\<o>\<i>\<s>\<o>\<n>\<close>;
            clarsimp simp: \<m>\<a>\<p>_WT),
           metis SType_Of_not_poison has_Zero_def option.exhaust_sel option.pred_inject(2) zero_well_typ,
           metis \<m>\<a>\<p>_eq_\<p>\<o>\<i>\<s>\<o>\<n>,
           clarsimp simp: t1 t2 has_Zero_def Inhabited_def Satisfiable_def)
    subgoal premises prems for y x p xa pa
      by (insert prems(1)[THEN spec[where x=\<open>\<lambda>_. xa\<close>], THEN spec[where x=\<open>\<lambda>kk. if (\<exists>k. sVAL_emb kk \<Turnstile> (k \<Ztypecolon> K) \<and> k \<in> D) then pa else y\<close>], simplified],
          auto simp: prems(6) split: if_split_asm)
    apply (clarsimp simp: t1 t2 has_Zero_def Inhabited_def Satisfiable_def Semantic_Type_def)
    subgoal premises prems for y x p xa pa
    apply (insert prems(1)[THEN spec[where x=\<open>\<m>\<a>\<p>[\<t>\<y>\<p>\<e>\<o>\<f> K, \<t>\<y>\<p>\<e>\<o>\<f> V]\<close>]] prems(2-);
           cases \<open>\<t>\<y>\<p>\<e>\<o>\<f> K = \<p>\<o>\<i>\<s>\<o>\<n>\<close>; cases \<open>\<t>\<y>\<p>\<e>\<o>\<f> V = \<p>\<o>\<i>\<s>\<o>\<n>\<close>; clarsimp simp: \<m>\<a>\<p>_WT)
        by (metis option.pred_inject(2) zero_well_typ) .
qed


lemma VMap_zero [\<phi>reason add]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> T\<^sub>K = \<t>\<y>\<p>\<e>\<o>\<f> K \<and> T\<^sub>V = \<t>\<y>\<p>\<e>\<o>\<f> V
\<Longrightarrow> Semantic_Zero_Val T\<^sub>V V z
\<Longrightarrow> Semantic_Zero_Val (\<m>\<a>\<p> [T\<^sub>K, T\<^sub>V]) (VMap K D V) (\<lambda>_. z) \<close>
  unfolding Semantic_Zero_Val_def Premise_def
  by (auto simp: \<m>\<a>\<p>_zero)



lemma Transformation_Functor [\<phi>reason add]:
      \<open> Functionality K (\<lambda>x. x \<in> DD)
    \<Longrightarrow> Abstract_Domain\<^sub>L K D
    \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<t>\<y>\<p>\<e>\<o>\<f> V = \<t>\<y>\<p>\<e>\<o>\<f> V'
    \<Longrightarrow> Transformation_Functor (VMap K DD) (VMap K DD) V V' range (\<lambda>_. UNIV)
                               (rel_fun (\<lambda>x y. x = y \<and> D x \<and> D y \<and> x \<in> DD \<and> y \<in> DD)) \<close>
  unfolding Transformation_Functor_def Transformation_def rel_fun_def Premise_def
  apply (clarsimp simp: Satisfiable_def)
  subgoal premises prems for f g v proof -

    obtain h where t1: \<open>v \<Turnstile> (f a \<Ztypecolon> V) \<Longrightarrow> v \<Turnstile> (h a v \<Ztypecolon> V') \<and> g (f a) (h a v)\<close> for a v
      using prems(4) by metis

    have t2: \<open>k \<in> DD \<Longrightarrow> sVAL_emb kk \<Turnstile> (k \<Ztypecolon> K) \<Longrightarrow> concretize K k = sVAL_emb kk\<close> for k kk
      by (metis Functionality_def Satisfiable_I concretize_SAT prems(1))

    show ?thesis
      by (rule exI[where x=\<open>\<lambda>k. h k (v (inv sVAL_emb (concretize K k)))\<close>],
          auto simp add: inj_sVAL_emb prems(8) t1 t2,
          insert prems(2,5,6,8), clarsimp simp: Abstract_Domain\<^sub>L_def \<r>ESC_def,
          metis concretize_SAT f_inv_into_f is_sTY_typeof t1)
  qed .

(*
lemma Functional_Transformation_Functor [\<phi>reason add]:
  \<open> Abstract_Domain\<^sub>L K' (\<lambda>k. k \<in> D')
\<Longrightarrow> Functionality K (\<lambda>k. k \<in> D)
\<Longrightarrow> Fun_CV_TrFunctor (VMap D) (VMap D') K V K' V' (\<lambda>_. D) (\<lambda>f. f ` D)
                     (\<lambda>f _.  bij_betw f D' D)
                     (\<lambda>_. UNIV) (\<lambda>_ _ _ _ _. True) (\<lambda>f\<^sub>1 f\<^sub>2 _ _ g. f\<^sub>2 o g o f\<^sub>1 )\<close>
  unfolding Fun_CV_TrFunctor_def Transformation_def
  apply (auto simp: Ball_def)
  apply (smt (verit, best) Abstract_Domain\<^sub>L_def Functionality_def \<r>ESC_def bij_betw_imp_surj_on concretize_SAT image_iff typing_inhabited)
  apply (smt (verit, best) Abstract_Domain\<^sub>L_def Functionality_def \<r>ESC_def bij_betw_imp_surj_on concretize_SAT image_eqI typing_inhabited)
  by (smt (verit, del_insts) Abstract_Domain\<^sub>L_def Functionality_def \<r>ESC_def bij_betw_apply concretize_SAT image_eqI typing_inhabited)
*)




end