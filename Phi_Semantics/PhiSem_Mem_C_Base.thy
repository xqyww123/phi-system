chapter \<open>Basis of C Memory Semantics and Fictions\<close>

theory PhiSem_Mem_C_Base
  imports PhSem_MoV PhiSem_Void "HOL-Library.Word"
begin

section \<open>Semantics\<close>

debt_axiomatization
        MemObj_Size     :: \<open>TY \<Rightarrow> nat\<close>
    and idx_step_offset :: \<open>TY \<Rightarrow> aggregate_index \<Rightarrow> nat\<close>
  where memobj_size_step : \<open>valid_idx_step T i \<Longrightarrow> MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
    and idx_step_offset_size:
          \<open>valid_idx_step T i \<Longrightarrow> idx_step_offset T i + MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
    and idx_step_offset_no_overlap:
          \<open>valid_idx_step T i \<Longrightarrow> valid_idx_step T j \<Longrightarrow>
                idx_step_offset T i \<le> idx_step_offset T j \<Longrightarrow>
                idx_step_offset T j < idx_step_offset T i + MemObj_Size (idx_step_type i T) \<Longrightarrow>
                i = j\<close>
    and memobj_size_void[simp]: \<open>MemObj_Size \<v>\<o>\<i>\<d> = 0\<close>
    and phantom_mem_value_uniq: \<open>MemObj_Size TY = 0 \<Longrightarrow> u \<in> Well_Type TY \<Longrightarrow> v \<in> Well_Type TY \<Longrightarrow> u = v\<close>

primrec index_offset :: \<open>TY \<Rightarrow> aggregate_path \<Rightarrow> nat\<close>
  where \<open>index_offset T [] = 0\<close>
      | \<open>index_offset T (i#idx) = idx_step_offset T i + index_offset (idx_step_type i T) idx\<close>

lemma index_offset_tail[simp]:
  \<open>index_offset T (idx@[i]) = index_offset T idx + idx_step_offset (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma fold_tail:
  \<open>fold f (l @ [x]) = f x o fold f l\<close>
  by (induct l; simp)

lemma index_offset_upper_bound:
  \<open>valid_index T (base@idx) \<Longrightarrow>
   index_offset T (base@idx) + MemObj_Size (index_type (base@idx) T) \<le> index_offset T base + MemObj_Size (index_type base T)\<close>
  by (induct idx arbitrary: base rule: rev_induct;
      simp del: append_assoc add: append_assoc[symmetric] fold_tail;
      insert idx_step_offset_size, fastforce)

lemmas index_offset_upper_bound_0 = index_offset_upper_bound[where base = "[]", simplified]

lemma index_offset_bound:
  \<open>valid_index T (base@idx) \<Longrightarrow>
  index_offset T base \<le> index_offset T (base@idx) \<and> index_offset T (base@idx) \<le> index_offset T base + MemObj_Size (index_type base T)\<close>
  apply (induct idx arbitrary: base rule: rev_induct;
         simp del: append_assoc add: append_assoc[symmetric] fold_tail)
  using idx_step_offset_size index_offset_upper_bound by fastforce

definition phantom_mem_semantic_type :: \<open>TY \<Rightarrow> bool\<close>
  where \<open>phantom_mem_semantic_type TY \<longleftrightarrow> MemObj_Size TY = 0\<close>

lemma phantom_mem_semantic_type_single_value:
  \<open> phantom_mem_semantic_type TY
\<Longrightarrow> u \<in> Well_Type TY
\<Longrightarrow> v \<in> Well_Type TY
\<Longrightarrow> u = v \<close>
  unfolding phantom_mem_semantic_type_def
  using phantom_mem_value_uniq[unfolded is_singleton_def]
  by metis

lemma index_offset_bound_strict:
  \<open>valid_index T (base@idx) \<Longrightarrow> \<not> phantom_mem_semantic_type (index_type (base@idx) T) \<Longrightarrow>
  index_offset T base \<le> index_offset T (base@idx) \<and> index_offset T (base@idx) < index_offset T base + MemObj_Size (index_type base T)\<close>
  unfolding phantom_mem_semantic_type_def
  by (induct idx arbitrary: base rule: rev_induct;
      simp del: append_assoc add: append_assoc[symmetric] fold_tail;
      insert idx_step_offset_size index_offset_upper_bound, fastforce)

lemma phantom_mem_semantic_type_element:
  \<open> valid_idx_step TY i
\<Longrightarrow> phantom_mem_semantic_type TY
\<Longrightarrow> phantom_mem_semantic_type (idx_step_type i TY)\<close>
  unfolding phantom_mem_semantic_type_def
  using memobj_size_step by fastforce



section \<open>Fiction\<close>

text \<open>They are not semantics, but parameters of the inference system.

\<open>Map_of_Val\<close> can be defined from \<open>valid_idx_step, idx_step_type\<close> and \<open>idx_step_value\<close>, e.g.,

\<open>primrec Map_of_Val :: \<open>TY \<Rightarrow> VAL \<Rightarrow> aggregate_path \<rightharpoonup> VAL\<close>
  where \<open>Map_of_Val _  v [] = Some v\<close>
      | \<open>Map_of_Val TY v (i#idx) = (if valid_idx_step TY i
                                    then Map_of_Val (idx_step_type i TY) (idx_step_value i v) idx
                                    else None)\<close>
\<close>

but we do not fix the definition because, \<open>idx_step_value\<close> and \<open>idx_step_type\<close> only determines the
children of a node but not the value of the node. Whether the node is valued, affects whether and
how could the tree be separated. The naive definition above actually disables any separation because
the value bound to the node contains the entire data, so actually meaningless for the purpose of
being a tree enabling separation of aggregate structures.
\<close>

debt_axiomatization Byte_Rep_of_Val :: \<open>VAL \<Rightarrow> 8 word list\<close>
  where Byte_Rep_of_Val_inj: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> Byte_Rep_of_Val Va = Byte_Rep_of_Val Vb \<Longrightarrow> Va = Vb\<close>

definition Val_of_Rep_Byte :: \<open>TY \<Rightarrow> 8 word list \<Rightarrow> VAL\<close>
  where \<open>Val_of_Rep_Byte TY rep = (@v. Byte_Rep_of_Val v = rep \<and> v \<in> Well_Type TY)\<close>

definition map_Rep_Byte :: \<open>TY \<Rightarrow> (VAL \<Rightarrow> VAL) \<Rightarrow> 8 word list \<Rightarrow> 8 word list\<close>
  where \<open>map_Rep_Byte TY f x = Byte_Rep_of_Val (f (Val_of_Rep_Byte TY x))\<close>

lemma Val_of_Rep_Byte_inj[simp]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> Val_of_Rep_Byte TY (Byte_Rep_of_Val v) = v\<close>
  unfolding Val_of_Rep_Byte_def
  using Byte_Rep_of_Val_inj by blast

abbreviation Byte_Rep_of_TY
  where \<open>Byte_Rep_of_TY TY \<equiv> Byte_Rep_of_Val ` Well_Type TY\<close>

lemma split_Byte_Rep_ExSet:
  \<open> (\<And>x. P x \<Longrightarrow> x \<in> Byte_Rep_of_TY TY)
\<Longrightarrow> (A x \<s>\<u>\<b>\<j> x. P x) =
    (A (Byte_Rep_of_Val v) \<s>\<u>\<b>\<j> v. P (Byte_Rep_of_Val v)) \<close>
  unfolding BI_eq_iff split_discrete_ex
  by (auto simp: image_iff Bex_def)


definition Byte_Rep_of_Val_ins
  where \<open>Byte_Rep_of_Val_ins TY = map_option (map_discrete (Val_of_Rep_Byte TY))\<close>

definition Byte_Rep_of_Val_ins_dom
  where \<open>Byte_Rep_of_Val_ins_dom TY = {x. pred_option (\<lambda>x'. discrete.dest x' \<in> Byte_Rep_of_TY TY) x}\<close>

lemma Byte_Rep_of_Val_ins_eval[simp]:
  \<open>Byte_Rep_of_Val_ins TY (Some (discrete u)) = (Some (discrete (Val_of_Rep_Byte TY u)))\<close>
  \<open>Byte_Rep_of_Val_ins TY None = None\<close>
  unfolding Byte_Rep_of_Val_ins_def by simp+

lemma Byte_Rep_of_Val_ins_dom_eval[simp]:
  \<open> None \<in> Byte_Rep_of_Val_ins_dom TY \<close>
  \<open>Some (discrete x) \<in> Byte_Rep_of_Val_ins_dom TY \<longleftrightarrow> x \<in> Byte_Rep_of_TY TY\<close>
  unfolding Byte_Rep_of_Val_ins_dom_def by simp+

lemma \<F>_functional_condition_Byte_Rep_of_Val_ins_dom:
  \<open>\<F>_functional_condition (Byte_Rep_of_Val_ins_dom TY)\<close>
  unfolding \<F>_functional_condition_def Byte_Rep_of_Val_ins_dom_def
  by(clarsimp; case_tac r; case_tac x; case_tac y; simp)

(*
interpretation Map_of_Val_ins_UNIV: cancl_sep_orthogonal_monoid \<open>Map_of_Val_ins\<close> UNIV
  apply (standard; clarsimp simp add: Map_of_Val_ins_def split_discrete_meta_all
                                      Map_of_Val_ins_dom_def
                            split: option.split)
  apply (auto simp add: fun_eq_iff split_option_ex times_fun 
                                  sep_disj_fun_def split_discrete_meta_all
                        split: option.split)[1]
  using Mapof_not_1 apply fastforce *)


interpretation Byte_Rep_of_Val_ins: cancl_sep_orthogonal_monoid \<open>Byte_Rep_of_Val_ins TY\<close> \<open>Byte_Rep_of_Val_ins_dom TY\<close>
  unfolding Byte_Rep_of_Val_ins_def Byte_Rep_of_Val_ins_dom_def
  by (rule cancl_sep_orthogonal_monoid__map_option_discrete,
      simp add: inj_on_def split_discrete_all split_option_all, force,
      simp)





context notes mul_carrier_option_def[simp] option.pred_True[simp] begin

lemma fiction_Map_of_Val_perm_partial_refinement_BYTE:
  \<open> valid_index TY idx
\<Longrightarrow> v \<in> Well_Type (index_type idx TY)
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> \<forall>x\<in>Well_Type TY. index_mod_value cidx (\<lambda>_. v) x = index_mod_value idx (\<lambda>_. v) x
\<Longrightarrow> (\<exists>\<^sup>su. {(Some u, (Some o map_discrete (map_Rep_Byte TY (index_mod_value cidx (\<lambda>_. v)))) u)}
          \<s>\<u>\<b>\<j>\<s> u \<in> discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}
            \<and> u \<in> discrete ` Byte_Rep_of_Val ` Well_Type TY) * Id_on UNIV
    \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx),
            to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v))}
    \<w>.\<r>.\<t> (\<F>_functional (Byte_Rep_of_Val_ins TY) (Byte_Rep_of_Val_ins_dom TY) \<Zcomp>
          \<F>_functional((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom TY))
    \<i>\<n> {to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}\<close>
  subgoal premises prems proof -

    have simp1: \<open>(\<exists>\<^sup>su. A u \<s>\<u>\<b>\<j>\<s>
        u \<in> discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} \<and> u \<in> discrete ` Byte_Rep_of_TY TY)
      = (\<exists>\<^sup>sa. A (discrete (Byte_Rep_of_Val a)) \<s>\<u>\<b>\<j>\<s> index_value idx a = u_idx \<and> a \<in> Well_Type TY)\<close>
      for A
      unfolding Byte_Rep_of_Val_ins_def
      by (auto simp: image_iff)

    have simp2: \<open>(\<exists>\<^sup>su. A u \<s>\<u>\<b>\<j>\<s>
        u \<in> discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} \<and> u \<in> discrete ` Well_Type TY)
      = (\<exists>\<^sup>sa. A (discrete a) \<s>\<u>\<b>\<j>\<s> index_value idx a = u_idx \<and> a \<in> Well_Type TY)\<close>
      for A
      unfolding Byte_Rep_of_Val_ins_def BI_eq_iff
      by (auto simp: image_iff)

    have t1[simp]:
      \<open>Domain (\<exists>\<^sup>sa. {(x a, y a)} \<s>\<u>\<b>\<j>\<s> P a) = (\<exists>\<^sup>sa. {(x a)} \<s>\<u>\<b>\<j>\<s> P a)\<close> for x y P
      unfolding set_eq_iff
      by auto

    have simp3[simp]:
         \<open>a \<in> Well_Type TY
       \<Longrightarrow> Val_of_Rep_Byte TY (map_Rep_Byte TY (index_mod_value cidx (\<lambda>_. v)) (Byte_Rep_of_Val a))
         = index_mod_value idx (\<lambda>_. v) a \<close> for a
      by (simp add: index_mod_value_welltyp map_Rep_Byte_def prems(1) prems(2) prems(4))
      

    note [cong] = SubjectionSet_cong

    note [simp] = ExSet_image SubjectionSet_image

    note t11 = refinement_frame[where R = UNIV, OF Byte_Rep_of_Val_ins.\<F>_functional_refinement_complex,
        where R4=\<open>\<exists>\<^sup>sa. {(Some (discrete (Byte_Rep_of_Val a)), Some (discrete (map_Rep_Byte TY (index_mod_value cidx (\<lambda>_. v)) (Byte_Rep_of_Val a))))}
                  \<s>\<u>\<b>\<j>\<s> index_value idx a = u_idx \<and> a \<in> Well_Type TY\<close>
          and TY4 = TY,
       simplified]

    show ?thesis
    apply (insert prems,
          rule sep_refinement_stepwise)
    prefer 2
    apply (rule fiction_Map_of_Val_perm_partial_refinement)
    apply (assumption)
    apply (assumption)
    apply (assumption)
    apply (assumption)
    apply (simp add: simp1 simp2)
    apply (rule t11)
    apply (clarsimp simp: )
          using index_mod_value_welltyp map_Rep_Byte_def apply force
    apply (clarsimp simp: frame_preserving_relation_def)
    apply (simp add: Sep_Closed_def \<F>_functional_comp)
    apply (rule subset_trans[OF fiction_Map_of_Val_ins_perm_projection])
    apply blast
    apply blast
    by (clarsimp simp: set_mult_expn)
qed .

lemma fiction_Map_of_Val_ins_perm_projection_BYTE:
  \<open> valid_index TY idx
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> refinement_projection
      (\<F>_functional (Byte_Rep_of_Val_ins TY) (Byte_Rep_of_Val_ins_dom TY) \<Zcomp>
       \<F>_functional ((\<circ>) to_share o Map_of_Val_ins) (Map_of_Val_ins_dom TY))
      { to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx) }
    \<subseteq> Some ` discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY } * UNIV \<close>
subgoal premises prems proof -
  have t1:
       \<open>Byte_Rep_of_Val_ins TY ` Some ` discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}
      = Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}\<close>
    for TY
    by (auto simp add: image_iff)
  show ?thesis
  apply (rule refinement_projections_stepwise_UNIV_paired)
  prefer 2
  apply (rule fiction_Map_of_Val_ins_perm_projection, insert prems)
  apply (assumption)
  apply (assumption)
  apply (rule Byte_Rep_of_Val_ins.\<F>_functional_projection[
          where S=\<open>Some ` discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}\<close>
            and TY=TY,
          simplified t1])
  apply (clarsimp) .
qed .

lemma fiction_Map_of_Val_ins_perm_projection_half_BYTE:
  \<open> valid_index TY idx
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> 0 < n
\<Longrightarrow> refinement_projection
     (\<F>_functional (Byte_Rep_of_Val_ins TY) (Byte_Rep_of_Val_ins_dom TY) \<Zcomp>
      \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom TY))
      { n \<odivr> (to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)) }
   \<subseteq> Some ` discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} * UNIV\<close>
  subgoal premises prems proof -
  
  have t1:
      \<open>(Byte_Rep_of_Val_ins TY ` Some ` discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY})
     = (Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY})\<close>
      unfolding Byte_Rep_of_Val_ins_def set_eq_iff
      by (auto simp: image_iff)

 show ?thesis
  by (insert prems,
      rule refinement_projections_stepwise_UNIV_paired,
      rule Byte_Rep_of_Val_ins.\<F>_functional_projection
        [where S=\<open>Some ` discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}\<close>,
          where TY=TY,
          simplified t1],
      ((auto simp: Byte_Rep_of_Val_ins_dom_def)[1]),
      rule fiction_Map_of_Val_ins_perm_projection_half,
      assumption,
      assumption,
      assumption)
qed .

end

lemma split_discrete_ExBI: \<open>(\<exists>*x. P x) = (\<exists>*x. P (discrete x))\<close>
  unfolding BI_eq_iff by (simp add: split_discrete_ex)

locale aggregate_mem_resource =
  partial_map_resource Res \<open>\<lambda>blk. discrete ` Byte_Rep_of_Val ` Well_Type (typ_of_blk blk)\<close>
  for Res :: "('blk \<Rightarrow> 8 word list discrete option) resource_entry"
  and typ_of_blk :: \<open>'blk \<Rightarrow> TY\<close>

locale perm_aggregate_mem_fiction =
  pointwise_base_fiction_for_partial_mapping_resource
      Res \<open>\<lambda>blk. \<F>_functional (Byte_Rep_of_Val_ins (typ_of_blk blk)) (Byte_Rep_of_Val_ins_dom (typ_of_blk blk)) \<Zcomp>
                 \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (typ_of_blk blk))\<close>
      Fic \<open>\<lambda>blk. discrete ` Byte_Rep_of_Val ` Well_Type (typ_of_blk blk)\<close>
  for Res :: "('blk \<Rightarrow> 8 word list discrete option) resource_entry"
  and typ_of_blk :: \<open>'blk \<Rightarrow> TY\<close>
  and null_blk :: 'blk
  and Fic :: "('blk \<Rightarrow> aggregate_path \<Rightarrow> VAL discrete share option) fiction_entry"
begin

sublocale aggregate_mem_resource Res typ_of_blk ..

lemma getter_rule:
  \<open> valid_index (typ_of_blk blk) idx
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> u_idx \<in> Well_Type (index_type idx (typ_of_blk blk)) \<and> cblk = blk
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' cblk \<lbrace> 1(blk := n \<odivr> (to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx))) \<Ztypecolon> \<phi> Itself \<longmapsto>
      \<lambda>ret. 1(blk := n \<odivr> (to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx))) \<Ztypecolon> \<phi> Itself
          \<s>\<u>\<b>\<j> x. ret = \<phi>arg (discrete (Byte_Rep_of_Val x)) \<and> x \<in> Well_Type (typ_of_blk blk) \<and> index_value idx x = u_idx \<rbrace>\<close>
  unfolding Premise_def
  subgoal premises prems proof -

  have [simp]: \<open>cblk = blk\<close>
    by (simp add: prems(2))

  have simp1: \<open>
      (A x \<s>\<u>\<b>\<j> x. B x \<and> x \<in> Byte_Rep_of_TY (typ_of_blk blk) \<and> x \<in> Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type (typ_of_blk cblk)})
    = (A (Byte_Rep_of_Val v) \<s>\<u>\<b>\<j> v. B (Byte_Rep_of_Val v) \<and> v \<in> Well_Type (typ_of_blk blk) \<and> index_value idx v = u_idx) \<close>
  for A B C ret TY S
  unfolding BI_eq_iff split_discrete_ex
  by (auto simp: image_iff Bex_def)

  show ?thesis
    by (rule "_getter_rule_2_"[OF _ fiction_Map_of_Val_ins_perm_projection_half_BYTE,
              where k=cblk and k'=blk and idx1=idx and u_idx1=u_idx,
              simplified split_discrete_ExBI inj_image_mem_iff inj_discrete simp1],
        insert prems, simp+)
qed .

lemma defined_set_in_image[simp]:
  \<open> { f u' |u'. u' \<in> h ` S} = { f (h u) |u. u \<in> S } \<close>
  unfolding set_eq_iff
  by auto

context notes mul_carrier_option_def[simp] option.pred_True[simp] begin

lemma allocate_rule:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>r. finite (dom r) \<longrightarrow> (\<exists>blk. blk \<notin> dom r \<and> typ_of_blk blk = TY \<and> blk \<noteq> null_blk))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type TY
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_allocate_res_entry (\<lambda>blk. typ_of_blk blk = TY \<and> blk \<noteq> null_blk) (\<lambda>k. {Some (discrete (Byte_Rep_of_Val v)) |v. v\<in>U k})
      \<lbrace> Void \<longmapsto> \<lambda>ret. 1(blk := to_share \<circ> (map_option discrete \<circ> Map_of_Val v)) \<Ztypecolon> \<phi> Itself
                  \<s>\<u>\<b>\<j> blk v. ret = \<phi>arg blk \<and> v \<in> U blk \<and> typ_of_blk blk = TY \<and> blk \<noteq> null_blk  \<rbrace> \<close>
  unfolding Premise_def
  subgoal premises prems proof-

  note pointwise_set_UNIV[simp] \<F>_functional_condition_Map_of_Val_ins_dom[simp]

  have t1[simp]: \<open>Val_of_Rep_Byte TY (Byte_Rep_of_Val v) = v\<close>
    using prems(2) by auto

thm sep_refinement_stepwise[
        OF refinement_frame[OF Byte_Rep_of_Val_ins.\<F>_functional_refinement'[simplified]]
           sep_refinement_stepwise[
                    OF refinement_frame[OF Map_of_Val_ins.\<F>_functional_refinement'[simplified]]
                       pointwise_to_share.\<F>_functional_refinement'[where B=\<open>Map_of_Val_ins ` B\<close> for B, unfolded defined_set_in_image]
                       pointwise_to_share.\<F>_functional_projection,
                    where B5=\<open>Byte_Rep_of_Val_ins TY ` B\<close> for B, unfolded defined_set_in_image],
        where a34=\<open>None\<close> and B21=\<open>{Some (discrete (Byte_Rep_of_Val v)) |v. v \<in> U k}\<close>,
        simplified]

thm pointwise_to_share.\<F>_functional_projection
thm pointwise_to_share.\<F>_functional_refinement'[where B=\<open>Map_of_Val_ins ` B\<close> for B, unfolded defined_set_in_image]

thm sep_refinement_stepwise[
         OF refinement_frame[OF Byte_Rep_of_Val_ins.\<F>_functional_refinement[simplified]]
            sep_refinement_stepwise[
                    OF refinement_frame[OF Map_of_Val_ins.\<F>_functional_refinement[simplified]]
                       pointwise_to_share.\<F>_functional_refinement
                       pointwise_to_share.\<F>_functional_projection],
        where a16=\<open>None\<close> and b16=\<open>Some (discrete (Byte_Rep_of_Val v))\<close> and TY16=TY,
        simplified]

  note rule = sep_refinement_stepwise[
        OF refinement_frame[OF Byte_Rep_of_Val_ins.\<F>_functional_refinement[simplified]]
           sep_refinement_stepwise[
                    OF refinement_frame[OF Map_of_Val_ins.\<F>_functional_refinement[simplified]]
                       pointwise_to_share.\<F>_functional_refinement
                       pointwise_to_share.\<F>_functional_projection],
        where a16=\<open>None\<close> and b16=\<open>Some (discrete (Byte_Rep_of_Val v))\<close> and TY16=TY,
        simplified,
        OF _ _ _ refinement_projections_stepwise_UNIV_paired[
            OF Map_of_Val_ins.\<F>_functional_projection
               pointwise_to_share.\<F>_functional_projection,
            where Dc=\<open>{1}\<close>,
            simplified]]

  show ?thesis
thm "__allocate_rule_3__"[
      where U =\<open>\<lambda>k. {Some (discrete (Byte_Rep_of_Val v)) |v. v\<in>U k }\<close>
        and U'=\<open>\<lambda>k. {to_share \<circ> (map_option discrete \<circ> Map_of_Val v) |v. v \<in> U k}\<close> , simplified]

apply (rule "__allocate_rule_3__"[
      where U =\<open>\<lambda>k. {Some (discrete (Byte_Rep_of_Val v)) |v. v\<in>U k }\<close>
        and U'=\<open>\<lambda>k. {to_share \<circ> (map_option discrete \<circ> Map_of_Val v) |v. v \<in> U k}\<close> , simplified])
apply (unfold \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified, simp]
             one_option_def)
apply (simp)
thm rule

apply (rule "__allocate_rule_3__"[where U=\<open>\<lambda>k. {Some (discrete (Byte_Rep_of_Val v)) |v. v\<in>U k }\<close> for U, simplified])

thm \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified, simp]
apply (rule "__allocate_rule_3__")
    by (unfold \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified, simp]
             one_option_def,
        simp, rule rule,
        simp add: prems(2),
        simp add: \<F>_functional_condition_Byte_Rep_of_Val_ins_dom,
        simp add: prems(2),
        simp add: R.in_invariant inj_image_mem_iff prems(2),
        clarsimp simp add: R.in_invariant Ball_def dom1_dom, metis dom_map_option_comp prems(1))
qed .

lemma setter_rule:
  assumes EQ: \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> cblk = blk\<close>
  shows \<open> valid_index (typ_of_blk blk) idx
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type (index_type idx (typ_of_blk blk))
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> u_idx \<in> Well_Type (index_type idx (typ_of_blk blk))
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>Well_Type (typ_of_blk blk). index_mod_value cidx (\<lambda>_. v) x = index_mod_value idx (\<lambda>_. v) x)
      \<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at cblk (Some \<circ> map_discrete (map_Rep_Byte (typ_of_blk cblk) (index_mod_value cidx (\<lambda>_. v))) \<circ> the))
            \<lbrace> 1(blk := to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)) \<Ztypecolon> \<phi> Itself \<longmapsto>
              \<lambda>\<r>\<e>\<t>. 1(blk := to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v)) \<Ztypecolon> \<phi> Itself \<rbrace> \<close>
  unfolding Premise_def

  by (simp only: EQ[unfolded Premise_def],
      rule "_setter_rule_2_"[where f=\<open>Some \<circ> map_discrete (map_Rep_Byte (typ_of_blk blk) (index_mod_value cidx (\<lambda>_. v)))\<close>
                        and V=\<open>discrete ` Byte_Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type (typ_of_blk blk)}\<close>
                        and F=\<open>\<lambda>_. to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v)\<close>
                        for idx cidx v u_idx,
                      OF _ fiction_Map_of_Val_perm_partial_refinement_BYTE
                           fiction_Map_of_Val_ins_perm_projection_BYTE],
      simp,
      assumption,
      assumption,
      assumption,
      assumption,
      assumption,
      assumption,
      clarsimp simp add: split_discrete_meta_all inj_image_mem_iff index_mod_value_welltyp image_iff Bex_def,
      metis Val_of_Rep_Byte_inj index_mod_value_welltyp map_Rep_Byte_def)


lemma deallocate_rule:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type (typ_of_blk blk)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at blk Map.empty)
      \<lbrace> 1(blk := to_share \<circ> (map_option discrete \<circ> Map_of_Val v)) \<Ztypecolon> \<phi> Itself \<longmapsto>
        \<lambda>\<r>\<e>\<t>. 1 \<Ztypecolon> \<phi> Itself \<rbrace> \<close>
  unfolding Premise_def
subgoal premises prems
proof -
  have [simp]:
    \<open>Map.empty \<circ> the = Map.empty\<close>
    unfolding fun_eq_iff by simp

  note inj_image_mem_iff[simp] pointwise_set_UNIV[simp] \<F>_functional_condition_Map_of_Val_ins_dom[simp]
       \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified, symmetric, simp]

  have [simp]: \<open>Val_of_Rep_Byte (typ_of_blk blk) (Byte_Rep_of_Val v) = v\<close>
    by (simp add: prems)

  note rule1 = refinement_projections_stepwise_UNIV_paired[
          OF Map_of_Val_ins.\<F>_functional_projection
             pointwise_to_share.\<F>_functional_projection,
          where Dc=\<open>{Some (discrete v)}\<close>,
          simplified]

  show ?thesis
    apply (rule "_setter_rule_2_"[where f=\<open>\<lambda>_. None\<close> and V=\<open>{discrete v}\<close> and F=\<open>\<lambda>_. 1\<close> for v, simplified],
        simp,
        unfold refinement_source_subjection, rule impI,
        rule sep_refinement_stepwise [
            OF refinement_frame[OF Byte_Rep_of_Val_ins.\<F>_functional_refinement[simplified]]
               sep_refinement_stepwise[
                        OF refinement_frame[OF Map_of_Val_ins.\<F>_functional_refinement[simplified]]
                           pointwise_to_share.\<F>_functional_refinement
                           pointwise_to_share.\<F>_functional_projection],
            where a16=\<open>Some (discrete (Byte_Rep_of_Val v))\<close> and b16=None and TY16=\<open>typ_of_blk blk\<close>,
            simplified])
    apply blast
    using \<F>_functional_condition_Byte_Rep_of_Val_ins_dom apply presburger
    using prems apply blast
    apply (rule rule1)
    using prems apply blast
    apply (rule refinement_projections_stepwise_UNIV_paired)
    prefer 2
    apply (rule rule1)
    apply (simp add: prems)
    apply (rule Byte_Rep_of_Val_ins.\<F>_functional_projection
      [where S=\<open>{Some (discrete (Byte_Rep_of_Val v))}\<close> and TY=\<open>typ_of_blk blk\<close>, simplified])
    using prems by blast
qed .

end

end

end