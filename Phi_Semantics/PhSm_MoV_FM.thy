theory PhSm_MoV_FM
  imports PhiSem_Mem_C PhSm_V_FMap
begin

section \<open>Semantics\<close>

debt_axiomatization
      Map_of_Val_fm: \<open>Map_of_Val (\<m>\<a>\<p>_rep vs) =
            (\<lambda>path. case path
                      of AgIdx_V k # path' \<Rightarrow>
                          (case fmlookup vs k of Some v \<Rightarrow> Map_of_Val v path'
                                               | None \<Rightarrow> 1)
                       | _ \<Rightarrow> 1)\<close>

\<phi>type_def ValIdx :: \<open>(VAL,'x) \<phi> \<Rightarrow> (aggregate_index, 'x) \<phi>\<close>
  where \<open>ValIdx T \<equiv> AgIdx_V \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and Transformation_Functor
       and Functional_Transformation_Functor

(*

abbreviation BC_Map :: \<open>(VAL,'a) \<phi> \<Rightarrow> 'a set \<Rightarrow> (aggregate_path \<Rightarrow> 'c, 'b) \<phi> \<Rightarrow> (aggregate_path \<Rightarrow> 'c::one, 'a \<Rightarrow> 'b) \<phi> \<close>
                       ("_ \<equiv>[_]\<Rrightarrow> _" [76,20,75] 75)
  where \<open>BC_Map K D V \<equiv> \<phi>MapTree D (ValIdx K) V\<close>

term \<open> (f \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal D K V) \<close>
term \<open> (f \<Ztypecolon> K \<equiv>[D]\<Rrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V) \<close>
*)


setup \<open>Context.theory_map ( Phi_Mem_Printer.add 110 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>Phi_Types.\<phi>MapTree\<close>, _)
          $ D
          $ (Const(\<^const_syntax>\<open>ValIdx\<close>, _) $ K)
          $ V) =>
        SOME (Const(\<^const_syntax>\<open>MapVal\<close>, dummyT) $ D $ K $ f ctxt V)
     | _ => NONE
  )
)\<close>

setup \<open>Context.theory_map ( Phi_Mem_Parser.add 110 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>MapVal\<close>, _) $ D $ K $ V) =>
        SOME (Const(\<^const_syntax>\<open>\<phi>MapTree\<close>, dummyT)
                $ D $ (Const(\<^const_syntax>\<open>ValIdx\<close>, dummyT) $ K) $ f ctxt V)
     | X => NONE
  )
)\<close>

term \<open>\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal D K V\<close>
term \<open>\<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V)\<close>

term \<open>\<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal D K V)\<close>
term \<open>\<m>\<e>\<m>[addr] (\<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V))\<close>
term \<open>\<m>\<e>\<m>[addr] (K \<equiv>[D]\<Rrightarrow> (V::(VAL,'x)\<phi>))\<close>

term \<open>\<m>\<e>\<m>[addr] MapVal D K V\<close>
ML \<open>@{term \<open>\<m>\<e>\<m>[addr] MapVal D K V\<close>}\<close>




lemma pull_map_map_option:
  \<open>pull_map idx (map_option g \<circ> f) = (map_option g \<circ> pull_map idx f)\<close>
  unfolding fun_eq_iff
  by (simp add: pull_map_def)

lemma map_option_o_eq_inj:
  \<open> inj f
\<Longrightarrow> map_option f o g = map_option f o g' \<longleftrightarrow> g = g'\<close>
  by (meson fun.inj_map injD option.inj_map)
  
lemma pull_map__Map_of_Val_\<m>\<a>\<p>__in_dom:
  \<open> k \<in> fmdom' f
\<Longrightarrow> pull_map [AgIdx_V k] (Map_of_Val (\<m>\<a>\<p>_rep f)) = Map_of_Val (the (fmlookup f k))\<close>
  unfolding Map_of_Val_fm fun_eq_iff pull_map_def
  by (auto, meson fmdom'_notI option.case_eq_if)


lemma Map_of_Val_\<m>\<a>\<p>_Nil:
  \<open> Map_of_Val (\<m>\<a>\<p>_rep xa) [] = 1 \<close>
  unfolding Map_of_Val_fm fun_eq_iff
  by auto

lemma to_share_inj [simp]:
  \<open>to_share x = to_share y \<longleftrightarrow> x = y\<close>
  by (metis strip_share_Share)

lemma map_option_inj:
  \<open> inj f
\<Longrightarrow> map_option f x = map_option f y \<longleftrightarrow> x = y \<close>
  by (meson injD option.inj_map)

lemma mem_coerce_MapVal:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D
\<Longrightarrow> finite D
\<Longrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal D K V = \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V) \<close>

  apply (rule \<phi>Type_eqI, clarify)
  subgoal premises prems for f u proof -
    have t1: \<open> k \<in> D \<Longrightarrow> concretize (ValIdx K) k = AgIdx_V (concretize K k) \<close> for k
      by (smt (verit, best) Abstract_Domain\<^sub>L_def Functionality_def ValIdx.Abstract_Domain\<^sub>L ValIdx.expansion \<r>ESC_def concretize_SAT prems)
    show ?thesis
    apply (auto simp: pull_map_to_share comp_assoc pull_map_map_option map_option_o_eq_inj
                      pull_map__Map_of_Val_\<m>\<a>\<p>__in_dom t1 Map_of_Val_\<m>\<a>\<p>_Nil)
    apply (clarsimp simp add: Map_of_Val_fm split: aggregate_index'.split option.split)
     apply (metis fmdom'I imageE)
    subgoal premises prems2 proof -
      obtain v where t2: \<open>k \<in> D \<Longrightarrow> pull_map [AgIdx_V (concretize K k)] u = to_share \<circ> (map_option discrete \<circ> Map_of_Val (v k)) \<and> v k \<Turnstile> (f k \<Ztypecolon> V)\<close> for k
        using prems2(1) by metis
      let ?g = \<open>\<lambda>k. if (\<exists>k'\<in>D. k = concretize K k') then Some (v (inv_into D (concretize K) k)) else None\<close>
  
      have t3: \<open>{a. \<exists>k'\<in>D. a = concretize K k'} \<subseteq> concretize K ` D\<close>
        unfolding set_eq_iff
        by (auto simp: image_iff Bex_def)
  
      have t4[simp]: \<open>fmlookup (Abs_fmap ?g) = ?g\<close>
        by (rule fmap.Abs_fmap_inverse, auto simp: dom_def prems(4))
  
      have t5: \<open>k \<in> D \<Longrightarrow> inv_into D (concretize K) (concretize K k) = k\<close> for k
        by (simp add: concretize_inj prems(1) prems(3))
  
      show ?thesis
        apply (rule exI[where x=\<open>\<m>\<a>\<p>_rep (Abs_fmap ?g)\<close>])
        apply (auto simp: fun_eq_iff Map_of_Val_fm split: list.split aggregate_index'.split)
        apply (simp add: prems2(2))
        using prems2(3) apply blast
        using prems2(3) apply blast
        subgoal premises prem3 for x22 k'
          by (insert t2[OF prem3], auto simp: pull_map_def fun_eq_iff map_option_inj t5 prem3)
        apply (simp add: prems2(3))
        apply (metis (no_types, lifting) fmdom'_notI image_iff t4)
        apply (metis (no_types, lifting) domIff fmdom'.rep_eq option.distinct(1) t4)
        by (metis t2 t5)
    qed .
  qed .


subsection \<open>ToA Mapper\<close>


lemma [\<phi>reason %mapToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %mapToA_mem_coerce]:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D
\<Longrightarrow> finite D

\<Longrightarrow> \<m>\<a>\<p> g : \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYU] V) \<OTast> R
         \<mapsto> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> DD

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (MapVal D K V) \<OTast> R
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (MapVal D K V') \<OTast> R'
    \<o>\<v>\<e>\<r> f : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> DD \<close>
  unfolding Guided_Mem_Coercion_def mem_coerce_MapVal .


lemma [\<phi>reason %mapToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %mapToA_mem_coerce]:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D
\<Longrightarrow> finite D

\<Longrightarrow> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYU] V) \<OTast> W
          \<mapsto> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> DD

\<Longrightarrow> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (MapVal D K V) \<OTast> W
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (MapVal D K V') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> DD \<close>

  unfolding Guided_Mem_Coercion_def mem_coerce_MapVal .











end
