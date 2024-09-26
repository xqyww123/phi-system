theory PhSm_MoV_FM
  imports PhiSem_Mem_C PhSm_V_FMap
begin

section \<open>Semantics\<close>

debt_axiomatization
      Map_of_Val_fm: \<open>Map_of_Val (\<m>\<a>\<p>_rep vs) =
            case_list 1 (\<lambda>k'. case k'
                  of AgIdx_V k \<Rightarrow> Map_of_Val (vs k)
                   | _ \<Rightarrow> 1)\<close>


\<phi>type_def ValIdx :: \<open>(VAL,'x) \<phi> \<Rightarrow> (aggregate_index, 'x) \<phi>\<close>
  where \<open>ValIdx T \<equiv> AgIdx_V o inv sVAL_emb \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Abstract_Domain\<^sub>L
       and Functionality
       and Transformation_Functor
       and Functional_Transformation_Functor





abbreviation BC_Map :: \<open>(VAL,'a) \<phi> \<Rightarrow> 'a set \<Rightarrow> (aggregate_path \<Rightarrow> 'c, 'b) \<phi> \<Rightarrow> (aggregate_path \<Rightarrow> 'c::one, 'a \<Rightarrow> 'b) \<phi> \<close>
                       ("_ \<equiv>[_]\<Rrightarrow> _" [76,20,75] 75)
  where \<open>BC_Map K D V \<equiv> \<phi>MapTree D (ValIdx K) V\<close>

term \<open> (f \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal K V) \<close>
term \<open> (f \<Ztypecolon> K \<equiv>[D]\<Rrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V) \<close>



setup \<open>Context.theory_map ( Phi_Mem_Printer.add 110 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>BC_Map\<close>, _) $ D $ K $ V) =>
        SOME (Const(\<^const_syntax>\<open>BC_Map\<close>, dummyT) $ D $ K $ f ctxt V)
     | _ => NONE
  )
)\<close>

setup \<open>Context.theory_map ( Phi_Mem_Parser.add 110 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>BC_Map\<close>, _) $ D $ K $ V) =>
        SOME (Const(\<^const_syntax>\<open>BC_Map\<close>, dummyT) $ D $ K $ f ctxt V)
     | X => NONE
  )
)\<close>



term \<open>A \<equiv>\<Rrightarrow> B\<close>

term \<open>\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal K V\<close>
term \<open>\<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V)\<close>

term \<open>\<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal K V)\<close>
term \<open>\<m>\<e>\<m>[addr] (\<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V))\<close>
term \<open>\<m>\<e>\<m>[addr] (K \<equiv>[D]\<Rrightarrow> (V::(VAL,'x)\<phi>))\<close>

term \<open>\<m>\<e>\<m>[addr] MapVal K V\<close>
ML \<open>@{term \<open>\<m>\<e>\<m>[addr] MapVal K V\<close>}\<close>

text \<open>Intuitively, \<open>\<phi>VM_Domain D K V\<close> specifies the domain\<close>

definition \<phi>VM_Domain :: \<open>(VAL,'x) \<phi> \<Rightarrow> TY \<Rightarrow> mem_fic BI\<close>
     where \<open>\<phi>VM_Domain K V \<equiv> case_list 1 (\<lambda>k'.
                case k' of AgIdx_V k \<Rightarrow>
                      (if (\<exists>k. k' = concretize (ValIdx K) k) then 1
                       else (to_share o map_option discrete o Map_of_Val (the (Zero V))))
                   | _ \<Rightarrow> 1) \<Ztypecolon> Itself \<close>

setup \<open>Sign.mandatory_path "\<phi>VM_Domain"\<close>

setup \<open>Sign.parent_path\<close>


lemma pull_map_map_option:
  \<open>pull_map idx (map_option g \<circ> f) = (map_option g \<circ> pull_map idx f)\<close>
  unfolding fun_eq_iff
  by (simp add: pull_map_def)

lemma map_option_o_eq_inj:
  \<open> inj f
\<Longrightarrow> map_option f o g = map_option f o g' \<longleftrightarrow> g = g'\<close>
  by (meson fun.inj_map injD option.inj_map)

(*
lemma pull_map__Map_of_Val_\<m>\<a>\<p>__in_dom:
  \<open> k \<in> fmdom' f
\<Longrightarrow> pull_map [AgIdx_V k] (Map_of_Val (\<m>\<a>\<p>_rep (f,U))) = Map_of_Val (the (fmlookup f k))\<close>
  unfolding Map_of_Val_fm fun_eq_iff pull_map_def
  by (auto, meson fmdom'_notI option.case_eq_if)
*)




lemma Map_of_Val_\<m>\<a>\<p>_Nil:
  \<open> Map_of_Val (\<m>\<a>\<p>_rep xa) [] = 1 \<close>
  unfolding fun_eq_iff
  by (auto simp: Map_of_Val_fm)

lemma to_share_inj [simp]:
  \<open>to_share x = to_share y \<longleftrightarrow> x = y\<close>
  by (metis strip_share_Share)

lemma map_option_inj:
  \<open> inj f
\<Longrightarrow> map_option f x = map_option f y \<longleftrightarrow> x = y \<close>
  by (meson injD option.inj_map)

term \<open>{c. \<exists>x. c \<Turnstile> (x \<Ztypecolon> T) \<and> x \<in> D } = Well_Type TY\<^sub>K \<close>


lemma pull_map__case_list[simp]:
  \<open> pull_map [k] (case_list x F) = F k \<close>
  unfolding pull_map_def
  by simp



lemma mem_coerce_MapVal:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. True)
\<Longrightarrow> Functionality K (\<lambda>x. True)
\<Longrightarrow> Injective_on K UNIV
\<Longrightarrow> Semantic_Type K TY\<^sub>K
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<t>\<y>\<p>\<e>\<o>\<f> V = TY\<^sub>V \<and> TY\<^sub>V \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and> is_sTY TY\<^sub>K
\<Longrightarrow> f \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> MapVal K V \<equiv> (f \<Ztypecolon> \<phi>MapTree UNIV (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V)) * \<phi>VM_Domain K TY\<^sub>V \<close>
  unfolding atomize_eq BI_eq_iff Semantic_Zero_Val_def Premise_def
  apply (clarify)
  subgoal premises prems for u proof -

    have t01: \<open>inj (concretize K)\<close>
      by (simp add: concretize_inj prems(1) prems(3))

    have t02[simp]: \<open>concretize K a = concretize K b \<longleftrightarrow> a = b\<close> for a b
      by (meson injD t01)

    have t03: \<open>v = concretize K x \<longleftrightarrow> v \<Turnstile> (x \<Ztypecolon> K)\<close> for x v
      by (metis Abstract_Domain\<^sub>L_def Functionality_def \<r>ESC_def concretize_SAT prems(1) prems(2))

    have [simp]: \<open>\<t>\<y>\<p>\<e>\<o>\<f> V = TY\<^sub>V\<close> using prems(5) by fastforce

    have t1: \<open> concretize (ValIdx K) k = AgIdx_V (inv sVAL_emb (concretize K k)) \<close> for k
      by (metis Abstract_Domain\<^sub>L_def ValIdx.Abstract_Domain\<^sub>L ValIdx.expansion \<r>ESC_def comp_apply concretize_SAT prems(1) t03)

    let ?M1 = \<open>\<lambda>g k. if (\<exists>kk. sVAL_emb k = concretize K kk) then Map_of_Val (g k) else 1\<close>
    let ?M2 = \<open>\<lambda>g k. if (\<exists>kk. sVAL_emb k = concretize K kk) then 1 else Map_of_Val (g k)\<close>

    have Map_of_Val__\<m>\<a>\<p>_rep__split:
      \<open> Map_of_Val (\<m>\<a>\<p>_rep g) =
          case_list 1 (\<lambda>k'. case k' of AgIdx_V k \<Rightarrow> ?M1 g k | _ \<Rightarrow> 1) *
          case_list 1 (\<lambda>k'. case k' of AgIdx_V k \<Rightarrow> ?M2 g k | _ \<Rightarrow> 1) \<close>
      for g
      unfolding Map_of_Val_fm fun_eq_iff
      by (clarify, case_tac x, auto split: option.split aggregate_index'.split
                                    simp: fun_eq_iff fmdom'_notI times_fun)

    have t2: \<open>
      to_share \<circ> (map_option discrete \<circ> Map_of_Val (\<m>\<a>\<p>_rep g)) =
        (to_share \<circ> (map_option discrete \<circ> case_list 1 (\<lambda>k'. case k' of AgIdx_V k \<Rightarrow> ?M1 g k | _ \<Rightarrow> 1))) *
        (to_share \<circ> (map_option discrete \<circ> case_list 1 (\<lambda>k'. case k' of AgIdx_V k \<Rightarrow> ?M2 g k | _ \<Rightarrow> 1)))\<close>
      for g
    unfolding Map_of_Val__\<m>\<a>\<p>_rep__split fun_eq_iff
    by (clarify; case_tac x; auto split: aggregate_index'.split option.split simp: times_fun prems(4))

    have t3[simp]: \<open>sVAL_emb (inv sVAL_emb (concretize K k)) = concretize K k\<close> for k
      by (meson Semantic_Type_def f_inv_into_f is_sTY prems(4) prems(7) t03)


    show ?thesis
    apply (auto simp: pull_map_to_share comp_assoc pull_map_map_option map_option_o_eq_inj
                      t1 Map_of_Val_\<m>\<a>\<p>_Nil)
subgoal for g
apply (rule exI[where x=\<open>to_share \<circ> (map_option discrete \<circ> (case_list 1 (\<lambda>k'.
                      case k' of AgIdx_V k \<Rightarrow> ?M1 g k | _ \<Rightarrow> 1 )))\<close>])
apply (rule exI[where x=\<open>to_share \<circ> (map_option discrete \<circ> (case_list 1 (\<lambda>k'.
                      case k' of AgIdx_V k \<Rightarrow> ?M2 g k | _ \<Rightarrow> 1 )))\<close>])
 apply (auto simp: pull_map_to_share comp_assoc pull_map_map_option map_option_o_eq_inj
                   t2 t1 Map_of_Val_\<m>\<a>\<p>_Nil sep_disj_fun_def
             split: option.split aggregate_index'.split list.split)
  using t03 t3 apply blast
  apply (metis inj_sVAL_emb inv_f_f)

apply (insert t03, auto simp: \<phi>VM_Domain_def fun_eq_iff t1 inj_sVAL_emb inv_f_f split: option.split list.split aggregate_index'.split)
  apply (metis inj_sVAL_emb inv_f_f)
  apply blast .
  


apply (auto simp add: \<phi>VM_Domain_def)
subgoal premises prems2 for u'

 proof -
thm prems2
      obtain v where t2: \<open>pull_map [AgIdx_V (inv sVAL_emb (concretize K k))] u' = to_share \<circ> (map_option discrete \<circ> Map_of_Val (v k)) \<and> v k \<Turnstile> (f k \<Ztypecolon> V)\<close> for k
        using prems2(2) by metis
      let ?g = \<open>\<lambda>k. if (\<exists>k'. k = concretize K k') then v (inv (concretize K) k) else the (Zero TY\<^sub>V)\<close>
  
      have t3: \<open>{a. \<exists>k'. a = concretize K k'} \<subseteq> concretize K ` UNIV\<close>
        unfolding set_eq_iff
        by (auto simp: image_iff Bex_def)
    
      have t5: \<open>inv (concretize K) (concretize K k) = k\<close> for k
        by (simp add: concretize_inj prems(1) prems(3))
  
      show ?thesis
        apply (rule exI[where x=\<open>\<m>\<a>\<p>_rep (?g o sVAL_emb)\<close>])
        apply (auto simp: fun_eq_iff Map_of_Val_fm prems2(3,4) t1 t5 times_fun
                    split: list.split aggregate_index'.split)
        apply (metis append.simps(1) append.simps(2) comp_apply pull_map_def t2)
        apply (metis inj_sVAL_emb inv_f_f)

        apply (rule exI[where x=\<open>\<lambda>xa. if (\<exists>k'. sVAL_emb xa = concretize K k') then v (inv (concretize K) (sVAL_emb xa)) else the (Zero TY\<^sub>V)\<close>],
               auto)
        apply (metis Inhabited_def SType_Of_def Semantic_Type_def Well_Type_unique concretize_SAT is_sTY_poison prems(4) prems(7) someI_ex)
        apply (metis Abstract_Domain\<^sub>L_def Inhabited_def SType_Of_not_poison Semantic_Type_def \<r>ESC_def prems(1) prems(4))
        using prems(6) apply fastforce
        apply (metis t03 t2 t5)
        using t03 apply blast
        using t03 by blast
    qed .
  qed .


subsection \<open>ToA Mapper\<close>


lemma [\<phi>reason %mapToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %mapToA_mem_coerce]:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

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

\<Longrightarrow> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) \<OTast> W
          \<mapsto> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> DD

\<Longrightarrow> \<m>\<a>\<p> g : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYV]] (MapVal D K V) \<OTast> W
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (MapVal D K V') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> DD \<close>

  unfolding Guided_Mem_Coercion_def mem_coerce_MapVal .


subsubsection \<open>Transformation\<close>

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> x \<Ztypecolon> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (MapVal D K V') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>

  unfolding Guided_Mem_Coercion_def mem_coerce_MapVal .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> x \<Ztypecolon> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (MapVal D K V) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def mem_coerce_MapVal .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (MapVal D K V) \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def mem_coerce_MapVal .

lemma [\<phi>reason %ToA_mem_coerce,
       unfolded Guided_Mem_Coercion_def,
       \<phi>reason %ToA_mem_coerce]:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) \<OTast> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (MapVal D K V) \<OTast> R \<w>\<i>\<t>\<h> P \<close>
  unfolding Guided_Mem_Coercion_def mem_coerce_MapVal .






end
