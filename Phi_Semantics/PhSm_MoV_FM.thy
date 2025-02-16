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





abbreviation VMapSlice :: \<open>(VAL,'a) \<phi> \<Rightarrow> 'a set \<Rightarrow> (aggregate_path \<Rightarrow> 'c, 'b) \<phi> \<Rightarrow> (aggregate_path \<Rightarrow> 'c::one, 'a \<Rightarrow> 'b) \<phi> \<close>
                       ("_ \<equiv>[_]\<Rrightarrow> _" [76,20,75] 75)
  where \<open>VMapSlice K D V \<equiv> \<phi>MapTree D (ValIdx K) V\<close>


term \<open> f \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> VMap K D V \<close>
term \<open> f \<Ztypecolon> K \<equiv>[D]\<Rrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V \<close>
term \<open> f \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (K \<equiv>\<Rrightarrow> V) \<close>
term \<open> f \<Ztypecolon> K \<equiv>\<Rrightarrow> V \<close>

setup \<open>Context.theory_map ( Phi_Mem_Printer.add 110 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>VMapSlice\<close>, _) $ D $ K $ V) =>
        SOME (Const(\<^const_syntax>\<open>VMapSlice\<close>, dummyT) $ D $ K $ f ctxt V)
     | _ => NONE
  )
)\<close>

setup \<open>Context.theory_map ( Phi_Mem_Parser.add 110 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>VMapSlice\<close>, _) $ D $ K $ V) =>
        SOME (Const(\<^const_syntax>\<open>VMapSlice\<close>, dummyT) $ D $ K $ f ctxt V)
     | X => NONE
  )
)\<close>




text \<open>Intuitively, \<open>\<phi>VM_Type D K V\<close> specifies the domain\<close>

\<phi>type_def \<phi>VM_Type :: \<open>(VAL,'x) \<phi> \<Rightarrow> 'x set \<Rightarrow> TY \<Rightarrow> (mem_fic, unit) \<phi>\<close>
                       ("\<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a>''")
     where \<open>unit \<Ztypecolon> \<phi>VM_Type K D V \<equiv> case_list 1 (\<lambda>k'.
                case k' of AgIdx_V k \<Rightarrow>
                      (if (\<exists>k. k' = concretize (ValIdx K) k \<and> k \<in> D) then 1
                       else (to_share o map_option discrete o Map_of_Val (the (Zero V))))
                   | _ \<Rightarrow> 1) \<Ztypecolon> Itself
                \<s>\<u>\<b>\<j> V \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and>
                    \<t>\<y>\<p>\<e>\<o>\<f> K \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<and>
                    is_sTY (\<t>\<y>\<p>\<e>\<o>\<f> K) \<close>

declare \<phi>VM_Type.expansion[simp del]

abbreviation \<phi>VM_Type' :: \<open>(VAL,'x) \<phi> \<Rightarrow> 'x set \<Rightarrow> TY \<Rightarrow> mem_fic BI\<close> ("\<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a>")
  where \<open>\<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a> K D V \<equiv> () \<Ztypecolon> \<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a>' K D V\<close>
(*
setup \<open>Sign.mandatory_path "\<phi>VM_Type"\<close>

lemma unfold[no_atp]:
  \<open> (() \<Ztypecolon> \<phi>VM_Type K D V) = \<phi>VM_Type K D V () \<close>
  unfolding \<phi>Type_def ..

setup \<open>Sign.parent_path\<close>
*)





lemma pull_map_map_option:
  \<open>pull_map idx (map_option g \<circ> f) = (map_option g \<circ> pull_map idx f)\<close>
  unfolding fun_eq_iff
  by (simp add: pull_map_def)

lemma map_option_o_eq_inj:
  \<open> inj f
\<Longrightarrow> map_option f o g = map_option f o g' \<longleftrightarrow> g = g'\<close>
  by (meson fun.inj_map injD option.inj_map)


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

lemma pull_map__case_list[simp]:
  \<open> pull_map [k] (case_list x F) = F k \<close>
  unfolding pull_map_def
  by simp



lemma mem_coerce_VMap:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<t>\<y>\<p>\<e>\<o>\<f> V = TY\<^sub>V
\<Longrightarrow> f \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> VMap K D V \<equiv> (f \<Ztypecolon> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V)) * \<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a> K D TY\<^sub>V \<close>
  unfolding atomize_eq BI_eq_iff Semantic_Zero_Val_def Premise_def
  apply (clarify)
  subgoal premises prems for u proof -

    thm prems
    have t01: \<open>inj_on (concretize K) D\<close>
      by (simp add: concretize_inj prems(1) prems(3))

    have t02[simp]: \<open>a \<in> D \<Longrightarrow> b \<in> D \<Longrightarrow> concretize K a = concretize K b \<longleftrightarrow> a = b\<close> for a b
      by (meson inj_onD t01)

    have t03: \<open>x \<in> D \<Longrightarrow> v = concretize K x \<longleftrightarrow> v \<Turnstile> (x \<Ztypecolon> K)\<close> for x v
      by (metis Abstract_Domain\<^sub>L_def Functionality_def \<r>ESC_def concretize_SAT prems(1) prems(2))

    have [simp]: \<open>\<t>\<y>\<p>\<e>\<o>\<f> V = TY\<^sub>V\<close> using prems(4) by fastforce

    have t1: \<open>k \<in> D \<Longrightarrow> concretize (ValIdx K) k = AgIdx_V (inv sVAL_emb (concretize K k)) \<close> for k
      by (metis Abstract_Domain\<^sub>L_def ValIdx.Abstract_Domain\<^sub>L ValIdx.expansion \<r>ESC_def comp_apply concretize_SAT prems(1) t03)


    let ?M1 = \<open>\<lambda>g k. if (\<exists>kk. sVAL_emb k = concretize K kk \<and> kk \<in> D) then Map_of_Val (g k) else 1\<close>
    let ?M2 = \<open>\<lambda>g k. if (\<exists>kk. sVAL_emb k = concretize K kk \<and> kk \<in> D) then 1 else Map_of_Val (g k)\<close>

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

  note rev_conj_cong[cong]
(*
    have t3[simp]: \<open>sVAL_emb (inv sVAL_emb (concretize K k)) = concretize K k\<close> for k
      by (meson Semantic_Type_def f_inv_into_f is_sTY prems(4) prems(5) t03)
    thm prems*)

    show ?thesis
    apply (auto simp: pull_map_to_share comp_assoc pull_map_map_option map_option_o_eq_inj
                      t1 Map_of_Val_\<m>\<a>\<p>_Nil)
      subgoal for g
        apply (rule exI[where x=\<open>to_share \<circ> (map_option discrete \<circ> (case_list 1 (\<lambda>k'.
                          case k' of AgIdx_V k \<Rightarrow> ?M1 g k | _ \<Rightarrow> 1 )))\<close>],
          rule exI[where x=\<open>to_share \<circ> (map_option discrete \<circ> (case_list 1 (\<lambda>k'.
                          case k' of AgIdx_V k \<Rightarrow> ?M2 g k | _ \<Rightarrow> 1 )))\<close>],
          auto simp: pull_map_to_share comp_assoc pull_map_map_option map_option_o_eq_inj
                     t2 t1 Map_of_Val_\<m>\<a>\<p>_Nil sep_disj_fun_def
               split: option.split aggregate_index'.split list.split)
        apply (metis (no_types, lifting) f_inv_into_f is_sTY_typeof t03)
        apply (meson f_inv_into_f is_sTY_typeof t03)
        apply (metis inj_sVAL_emb inv_f_f)
        apply ((insert t03, auto simp: \<phi>VM_Type.unfold \<phi>VM_Type_def fun_eq_iff t1 inj_sVAL_emb inv_f_f
                                split: option.split list.split aggregate_index'.split)[1])
        apply (metis inj_sVAL_emb inv_f_f)
        by (metis (mono_tags, opaque_lifting) f_inv_into_f is_sTY_typeof)

  apply (auto simp add: \<phi>VM_Type.unfold \<phi>VM_Type_def)
  subgoal premises prems2 for u'
  proof -
    obtain v where x2: \<open>k \<in> D \<Longrightarrow>
              pull_map [AgIdx_V (inv sVAL_emb (concretize K k))] u'
            = to_share \<circ> (map_option discrete \<circ> Map_of_Val (v k)) \<and> v k \<Turnstile> (f k \<Ztypecolon> V)\<close> for k
        using prems2(2) by metis
      let ?g = \<open>\<lambda>k. if (\<exists>k'. k = concretize K k' \<and> k' \<in> D)
                    then v (inv_into D (concretize K) k)
                    else the (Zero TY\<^sub>V)\<close>
  
      have x3: \<open>{a. \<exists>k'. a = concretize K k'} \<subseteq> concretize K ` UNIV\<close>
        unfolding set_eq_iff
        by (auto simp: image_iff Bex_def)

      have x5: \<open>k \<in> D \<Longrightarrow> inv_into D (concretize K) (concretize K k) = k\<close> for k
        by (simp add: concretize_inj[OF prems(3) prems(1)])
  
      show ?thesis
        apply (rule exI[where x=\<open>\<m>\<a>\<p>_rep (?g o sVAL_emb)\<close>],
            auto simp: fun_eq_iff Map_of_Val_fm prems2(3,4) t1 x5 times_fun
                 split: list.split aggregate_index'.split)
        apply (metis append.simps(1) append.simps(2) comp_apply inj_sVAL_emb inv_f_f pull_map_def x2)
        apply (metis inj_sVAL_emb inv_f_f)
        apply (meson f_inv_into_f is_sTY_typeof prems2(7) prems2(8) t03)
        apply (metis aggregate_index'.inject(3) prems2(4) times_option(3))
        apply (rule exI[where x=\<open>\<lambda>xa. if (\<exists>k'. sVAL_emb xa = concretize K k' \<and> k' \<in> D)
                                      then v (inv_into D (concretize K) (sVAL_emb xa))
                                      else the (Zero TY\<^sub>V)\<close>],   auto)
        apply (metis t03 x2 x5)
        using t03 apply blast
        using t03 by blast
    qed .
  qed .


subsection \<open>ToA Mapper\<close>


lemma MVT_mapper_tgt:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> \<m>\<a>\<p> g : \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYU] V) \<OTast> R
         \<mapsto> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V') \<OTast> R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T \<OTast> W \<mapsto> T' \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> (\<lambda>(x,_,w). (x,w)) ` DD

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (VMap K D V) \<OTast> R
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (VMap K D V') \<OTast> R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f id \<otimes>\<^sub>f w : T \<OTast> \<phi>VM_Type K D (\<t>\<y>\<p>\<e>\<o>\<f> V) \<^emph> W \<mapsto> T' \<OTast> \<phi>VM_Type K D (\<t>\<y>\<p>\<e>\<o>\<f> V') \<^emph> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter o (\<lambda>(x,_,w). (x,w))
         \<s>\<e>\<t>\<t>\<e>\<r> (\<lambda>(x,w). (x,(),w)) o setter \<i>\<n> DD \<close>

  unfolding \<phi>Prod'_def Guided_Mem_Coercion_def
  \<medium_left_bracket> premises AD[] and FC[] and IJ[] and TR[]
    apply_rule ToA_Mapper_onward[OF TR, where x=\<open>case x of (x,_,w) \<Rightarrow> (x,w)\<close>]
    certified by (cases x; auto_sledgehammer)
  \<semicolon> apply_rule mem_coerce_VMap[OF AD FC IJ, symmetric]
  \<medium_right_bracket> apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises AD[] and FC[] and IJ[] and TR[]
    apply_rule mem_coerce_VMap[OF AD FC IJ]
    apply_rule ToA_Mapper_backward[OF TR, where x=x]
    certified by auto_sledgehammer
  \<medium_right_bracket> certified by auto_sledgehammer
  by (rule conjunctionI, rule, drule ToA_Mapper_f_expn_rev, auto)


lemma MVT_mapper_src:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<OTast> R \<mapsto> U' \<OTast> R'
    \<o>\<v>\<e>\<r> f : \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) \<OTast> W
          \<mapsto> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> V') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> DD

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f id \<otimes>\<^sub>f r : U \<OTast> \<phi>VM_Type K D (\<t>\<y>\<p>\<e>\<o>\<f> V) \<^emph> R \<mapsto> U' \<OTast> \<phi>VM_Type K D (\<t>\<y>\<p>\<e>\<o>\<f> V') \<^emph> R'
    \<o>\<v>\<e>\<r> f : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYV]] (VMap K D V) \<OTast> W
          \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> (VMap K D V') \<OTast> W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> (\<lambda>(x,w). (x,(),w)) o getter
        \<s>\<e>\<t>\<t>\<e>\<r> setter o (\<lambda>(x,_,w). (x,w))
      \<i>\<n> DD \<close>

  unfolding \<phi>Prod'_def Guided_Mem_Coercion_def
  \<medium_left_bracket> premises AD[] and FC[] and IJ[] and TR[]
    apply_rule mem_coerce_VMap[OF AD FC IJ]
    apply_rule ToA_Mapper_onward[OF TR, where x=x]
  \<medium_right_bracket> certified by auto_sledgehammer
  apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises AD[] and FC[] and IJ[] and TR[]
    apply_rule ToA_Mapper_backward[OF TR, where x=\<open>case x of (x,_,w) \<Rightarrow> (x,w)\<close>]
    certified by (cases x; auto_sledgehammer)
  \<semicolon> apply_rule mem_coerce_VMap[OF AD FC IJ, symmetric]
  \<medium_right_bracket>
  by (rule conjunctionI, rule, drule ToA_Mapper_f_expn_rev, auto_sledgehammer)


subsubsection \<open>Transformation\<close>

lemma MVT_Tr_src:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> (x \<Ztypecolon> K \<equiv>[D]\<Rrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) * \<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a> K D (\<t>\<y>\<p>\<e>\<o>\<f> V) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (K \<equiv>(D)\<Rrightarrow> V) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>

  unfolding Guided_Mem_Coercion_def
  by (simp add: mem_coerce_VMap[where V=V and TY\<^sub>V = \<open>\<t>\<y>\<p>\<e>\<o>\<f> V\<close>, simplified])

lemma MVT_biTr_src:

  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> ((fst x, ()), snd x) \<Ztypecolon> K \<equiv>[D]\<Rrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V \<^emph> \<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a>' K D (\<t>\<y>\<p>\<e>\<o>\<f> V) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (K \<equiv>(D)\<Rrightarrow> V) \<OTast> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>

  unfolding Guided_Mem_Coercion_def \<phi>Prod'_def
  by (simp add: mem_coerce_VMap[where V=V and TY\<^sub>V = \<open>\<t>\<y>\<p>\<e>\<o>\<f> V\<close>, simplified] \<phi>Prod_expn'' \<phi>Prod_expn')

lemma MVT_Tr_tgt:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> K \<equiv>[D]\<Rrightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) * \<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a> K D (\<t>\<y>\<p>\<e>\<o>\<f> V) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (K \<equiv>(D)\<Rrightarrow> V) \<w>\<i>\<t>\<h> P \<close>

  unfolding Guided_Mem_Coercion_def
  by (simp add: mem_coerce_VMap[where V=V and TY\<^sub>V = \<open>\<t>\<y>\<p>\<e>\<o>\<f> V\<close>, simplified])

lemma MVT_biTr_tgt:
  \<open> Abstract_Domain\<^sub>L K (\<lambda>x. x \<in> D)
\<Longrightarrow> Functionality K (\<lambda>x. x \<in> D)
\<Longrightarrow> Injective_on K D

\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi>MapTree D (ValIdx K) (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TYV] V) \<^emph> \<k>\<v>-\<s>\<c>\<h>\<e>\<m>\<a>' K D (\<t>\<y>\<p>\<e>\<o>\<f> V) \<OTast> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst (fst x), snd x) \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[\<m>\<a>\<p>[TYK,TYU]] (VMap K D V) \<OTast> R \<w>\<i>\<t>\<h> P \<close>

  unfolding Guided_Mem_Coercion_def \<phi>Prod'_def
  by (simp add: mem_coerce_VMap[where V=V and TY\<^sub>V = \<open>\<t>\<y>\<p>\<e>\<o>\<f> V\<close>, simplified] \<phi>Prod_expn'' \<phi>Prod_expn')

term 1

locale AA
begin

attribute_setup AAA = \<open>\<close>
term

end


end
