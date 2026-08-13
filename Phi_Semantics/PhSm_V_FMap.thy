chapter \<open>Value model of Finite Map\<close>

theory PhSm_V_FMap
  imports PhSm_Ag_Base
  abbrevs "<map>" = "\<map>"
begin

section \<open>Semantics\<close>

debt_axiomatization sem_map_T :: \<open>TY \<Rightarrow> TY \<Rightarrow> TY\<close> ("\<map> [_,_]")
                and map_rep   :: \<open>(sVAL \<Rightarrow> VAL) \<Rightarrow> VAL\<close>
  where map_rep_inj [simp] : \<open>map_rep vsT = map_rep vsT' \<longleftrightarrow> vsT = vsT'\<close>
    and map_eq_poison[simp] : \<open>\<map>[T,U] = \<poison> \<longleftrightarrow> T = \<poison> \<or> U = \<poison> \<or> \<not> is_sTY T\<close>
    and map_WT             : \<open>T \<noteq> \<poison> \<and> U \<noteq> \<poison> \<and> is_sTY T \<Longrightarrow> 
                              Well_Type \<map>[T,U] = { map_rep f |f. (\<forall>k. f k \<in> Well_Type U) }\<close>
    and map_WT_uniq        : \<open>map_rep fU \<in> Well_Type TY \<Longrightarrow> \<exists>T U. TY = \<map>[T,U]\<close>
    and map_zero           : \<open>T \<noteq> \<poison> \<and> U \<noteq> \<poison> \<and> is_sTY T \<Longrightarrow>
                              Zero \<map>[T,U] = map_option (\<lambda>v. map_rep (\<lambda>_. v)) (Zero U)\<close>
    and map_idx_step_type  : \<open>T \<noteq> \<poison> \<and> U \<noteq> \<poison> \<and> is_sTY T \<Longrightarrow>
                              idx_step_type (AgIdx_V v) \<map>[T,U] = U \<close>
    and map_valid_idx_step : \<open>T \<noteq> \<poison> \<and> U \<noteq> \<poison> \<and> is_sTY T \<Longrightarrow>
                              valid_idx_step \<map>[T,U] j \<longleftrightarrow> j \<in> {AgIdx_V v |v. sVAL_emb v \<in> Well_Type T }\<close>
    and map_idx_step_value : \<open>idx_step_value (AgIdx_V v) (map_rep f) = f v\<close>
    and map_idx_step_mod_value :
                             \<open>idx_step_mod_value (AgIdx_V v) g (map_rep f) = map_rep (f(v := g (f v)))\<close>


subsubsection \<open>Basic Properties\<close>

lemma [\<phi>reason add]:
  \<open> Is_Type_Literal U
\<Longrightarrow> Is_Type_Literal \<map>[T,U] \<close>
  unfolding Is_Type_Literal_def ..


subsubsection \<open>Reduction to poison\<close>

lemma map_eq_poison_red[simp]:
  \<open> \<map>[T, \<poison>] = \<poison> \<close>
  \<open> \<map>[\<poison>, U] = \<poison> \<close>
  by simp+

lemma is_sTY_typeof:
  \<open> is_sTY (\<typeof> K)
\<Longrightarrow> \<typeof> K \<noteq> \<poison>
\<Longrightarrow> v \<Turnstile> (x \<Ztypecolon> K)
\<Longrightarrow> v \<in> range sVAL_emb \<close>
  by (meson SType_Of_not_poison is_sTY)



section \<open>\<phi>Type\<close>

\<phi>type_def VMap :: "(VAL, 'k) \<phi> \<Rightarrow> 'k set \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (VAL, 'k \<Rightarrow> 'v) \<phi>"
                    ("_ \<equiv>'(_')\<Rrightarrow> _" [76,20,75] 75)
  where \<open>f \<Ztypecolon> VMap K D V \<equiv> map_rep f' \<Ztypecolon> Itself
        \<subj> f'. is_sTY (\<typeof> K) \<and> \<typeof> K \<noteq> \<poison> \<and> \<typeof> V \<noteq> \<poison>
               \<and> (\<forall>kk k. sVAL_emb kk \<Turnstile> (k \<Ztypecolon> K) \<and> k \<in> D     \<longrightarrow> f' kk \<Turnstile> (f k \<Ztypecolon> V))
               \<and> (\<forall>kk. (\<nexists>k. sVAL_emb kk \<Turnstile> (k \<Ztypecolon> K) \<and> k \<in> D) \<longrightarrow> f' kk = the (Zero (\<typeof> V))) \<close>
  deriving \<open>Abstract_Domain\<^sub>L K P\<^sub>K \<Longrightarrow>
            Abstract_Domain  V P\<^sub>V \<Longrightarrow>
            Abstract_Domain (VMap K D V) (\<lambda>f. \<forall>k\<in>D. P\<^sub>K k \<longrightarrow> P\<^sub>V (f k)) \<close>
       and \<open>Abstract_Domain K D \<Longrightarrow>
            Object_Equiv V eq \<Longrightarrow>
            Object_Equiv (VMap K DD V) (rel_fun (\<lambda>x y. x = y \<and> D x \<and> D y) eq) \<close>

abbreviation Total_VMap :: "(VAL, 'k) \<phi> \<Rightarrow> (VAL, 'v) \<phi> \<Rightarrow> (VAL, 'k \<Rightarrow> 'v) \<phi>"
                            ("_ \<equiv>\<Rrightarrow> _" [76,75] 75)
  where \<open>K \<equiv>\<Rrightarrow> V \<equiv> K \<equiv>(UNIV)\<Rrightarrow> V\<close>

lemma has_Zero_map [simp]:
  \<open> has_Zero (\<map>[K, V]) \<longleftrightarrow> K \<noteq> \<poison> \<and> is_sTY K \<and> has_Zero V \<close>
  unfolding has_Zero_def
  by (cases \<open>K = \<poison>\<close>; cases \<open>V = \<poison>\<close>; cases \<open>is_sTY K\<close>; auto simp: map_zero;
      metis Zero_poison map_eq_poison)


lemma typeof_VMap [simp]:
  \<open> has_Zero (\<typeof> V)
\<Longrightarrow> \<typeof> (VMap K D V) = \<map>[\<typeof> K, \<typeof> V]\<close>
proof -

  have t1: \<open>(\<poison> = \<map> [T,U]) = (T = \<poison> \<or> U = \<poison> \<or> \<not> is_sTY T)\<close> for T U
    by (metis map_eq_poison)

  have t2: \<open>(\<typeof> K = \<poison>) = (\<not> Inhabited K \<or> (\<exists>x v. v \<Turnstile> (x \<Ztypecolon> K) \<and> v \<notin> Well_Type (\<typeof> K)))\<close> for K
    by (metis SType_Of_not_poison)

  show \<open> has_Zero (\<typeof> V)
    \<Longrightarrow> \<typeof> (VMap K D V) = \<map>[\<typeof> K, \<typeof> V]\<close>
    unfolding SType_Of_def[where T=\<open>VMap K D V\<close>] Inhabited_def
    apply (auto simp: Satisfiable_def,
           rule some1_equality, rule, assumption,
           (unfold Semantic_Type_def; clarsimp; cases \<open>\<typeof> K = \<poison>\<close>; cases \<open>\<typeof> V = \<poison>\<close>; simp; metis Well_Type_unique),
           (unfold Semantic_Type_def;  cases \<open>\<typeof> K = \<poison>\<close>; cases \<open>\<typeof> V = \<poison>\<close>;
            clarsimp simp: map_WT),
           metis SType_Of_not_poison has_Zero_def option.exhaust_sel option.pred_inject(2) zero_well_typ,
           metis map_eq_poison,
           clarsimp simp: t1 t2 has_Zero_def Inhabited_def Satisfiable_def)
    subgoal premises prems for y x p xa pa
      by (insert prems(1)[THEN spec[where x=\<open>\<lambda>_. xa\<close>], THEN spec[where x=\<open>\<lambda>kk. if (\<exists>k. sVAL_emb kk \<Turnstile> (k \<Ztypecolon> K) \<and> k \<in> D) then pa else y\<close>], simplified],
          auto simp: prems(6) split: if_split_asm)
    apply (clarsimp simp: t1 t2 has_Zero_def Inhabited_def Satisfiable_def Semantic_Type_def)
    subgoal premises prems for y x p xa pa
    apply (insert prems(1)[THEN spec[where x=\<open>\<map>[\<typeof> K, \<typeof> V]\<close>]] prems(2-);
           cases \<open>\<typeof> K = \<poison>\<close>; cases \<open>\<typeof> V = \<poison>\<close>; clarsimp simp: map_WT)
        by (metis option.pred_inject(2) zero_well_typ) .
qed


lemma VMap_zero [\<phi>reason add]:
  \<open> \<condition> T\<^sub>K = \<typeof> K \<and> T\<^sub>V = \<typeof> V
\<Longrightarrow> Semantic_Zero_Val T\<^sub>V V z
\<Longrightarrow> Semantic_Zero_Val (\<map> [T\<^sub>K, T\<^sub>V]) (VMap K D V) (\<lambda>_. z) \<close>
  unfolding Semantic_Zero_Val_def Premise_def
  by (auto simp: map_zero)



lemma Transformation_Functor [\<phi>reason add]:
      \<open> Functionality K (\<lambda>x. x \<in> DD)
    \<Longrightarrow> Abstract_Domain\<^sub>L K D
    \<Longrightarrow> \<condition> \<typeof> V = \<typeof> V'
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