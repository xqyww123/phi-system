chapter \<open>Formalization Tools for Map-of-Val\<close>

theory PhSem_MoV
  imports PhiSem_Aggregate_Base Phi_System.Resource_Template
begin

debt_axiomatization Map_of_Val :: \<open>VAL \<Rightarrow> aggregate_path \<rightharpoonup> VAL\<close>
                and Dom_of_TY :: \<open>TY \<Rightarrow> aggregate_path set\<close>
  where Map_of_Val_inj: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> Map_of_Val Va = Map_of_Val Vb \<Longrightarrow> Va = Vb\<close>
  and   Map_of_Val_dom: \<open>Va \<in> Well_Type T \<Longrightarrow> dom (Map_of_Val Va) = Dom_of_TY T\<close>
  and   Dom_of_TY_step: \<open>valid_idx_step T i \<Longrightarrow> Dom_of_TY (idx_step_type i T) \<subseteq> Dom_of_TY T\<close>
  and   Mapof_not_1[simp]: \<open>V \<in> Well_Type TY \<Longrightarrow> Map_of_Val V \<noteq> 1\<close>
  and   Map_of_Val_pull_step: \<open>valid_idx_step T i \<Longrightarrow> V \<in> Well_Type T
                          \<Longrightarrow> pull_map [i] (Map_of_Val V) = Map_of_Val (idx_step_value i V)\<close>
  and   Map_of_Val_mod_step: \<open>valid_idx_step T i \<Longrightarrow> v \<in> Well_Type T
                         \<Longrightarrow> Map_of_Val (idx_step_mod_value i f v) = Map_of_Val v ++ push_map [i] (Map_of_Val (f (idx_step_value i v)))\<close>

lemma Map_of_Val_pull:
  \<open>valid_index T idx \<Longrightarrow> V \<in> Well_Type T \<Longrightarrow> pull_map idx (Map_of_Val V) = Map_of_Val (index_value idx V)\<close>
  by (induct idx arbitrary: V T; simp; metis Map_of_Val_pull_step idx_step_value_welltyp pull_map_cons)

lemma Dom_of_TY:
  \<open>valid_index T idx \<Longrightarrow> Dom_of_TY (index_type idx T) \<subseteq> Dom_of_TY T\<close>
  by (induct idx arbitrary: T; simp; meson Dom_of_TY_step dual_order.trans)

lemma map_add_subsumed_dom:
  \<open>dom f \<subseteq> dom g \<Longrightarrow> f ++ g = g\<close>
  unfolding map_add_def dom_def subset_eq fun_eq_iff apply simp
  by (metis option.case_eq_if option.collapse option.simps(3))

lemma Map_of_Val_mod:
  \<open> valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> u \<in> Well_Type (index_type idx T)
\<Longrightarrow> Map_of_Val (index_mod_value idx (\<lambda>_. u) v) = Map_of_Val v ++ push_map idx (Map_of_Val u)\<close>
  apply (induct idx arbitrary: u v T; simp)
  using Map_of_Val_dom map_add_subsumed_dom apply (metis order_refl)
  by clarify (simp add: idx_step_value_welltyp Map_of_Val_mod_step  push_map_distrib_map_add
                        Map_of_Val_pull_step[symmetric] push_pull_map map_add_subsumed2
                        push_map_push_map)

definition Map_of_Val_ins
  where \<open>Map_of_Val_ins = ((o) (map_option discrete))
                            o (\<lambda>V. (case V of Some V' \<Rightarrow> Map_of_Val V' | None \<Rightarrow> 1))
                            o map_option discrete.dest\<close>
definition Map_of_Val_ins_dom
  where \<open>Map_of_Val_ins_dom TY = {x. pred_option (\<lambda>x'. discrete.dest x' \<in> Well_Type TY) x}\<close>

lemma Map_of_Val_ins_eval[simp]:
  \<open>Map_of_Val_ins (Some (discrete u)) = (map_option discrete) o Map_of_Val u\<close>
  \<open>Map_of_Val_ins None = 1\<close>
  unfolding Map_of_Val_ins_def by simp+

lemma Map_of_Val_ins_None[simp]:
  \<open> x \<in> Map_of_Val_ins_dom TY
\<Longrightarrow> (Map_of_Val_ins x = 1) = (x = None)\<close>
  unfolding Map_of_Val_ins_def Map_of_Val_ins_dom_def
  by (cases x; clarsimp;
      smt (verit) Mapof_not_1 dom_1 dom_eq_empty_conv dom_map_option_comp)

lemma Map_of_Val_ins_dom_NONE[simp]:
  \<open> None \<in> Map_of_Val_ins_dom TY \<close>
  unfolding Map_of_Val_ins_dom_def by simp

lemma Map_of_Val_ins_dom_eval[simp]:
  \<open>Some (discrete u) \<in> Map_of_Val_ins_dom TY \<longleftrightarrow> u \<in> Well_Type TY\<close>
  unfolding Map_of_Val_ins_dom_def by simp

lemma \<F>_functional_condition_Map_of_Val_ins_dom:
  \<open>\<F>_functional_condition (Map_of_Val_ins_dom TY)\<close>
  unfolding \<F>_functional_condition_def Map_of_Val_ins_dom_def
  by (clarsimp; case_tac r; case_tac x; simp)


interpretation Map_of_Val_ins: cancl_sep_orthogonal_monoid \<open>Map_of_Val_ins\<close> \<open>Map_of_Val_ins_dom TY\<close>
  apply (standard; clarsimp simp add: Map_of_Val_ins_def split_discrete_meta_all
                                      Map_of_Val_ins_dom_def
                            split: option.split)

  apply (auto simp add: fun_eq_iff split_option_ex times_fun 
                                  sep_disj_fun_def split_discrete_meta_all
                        split: option.split)[1]
  using Mapof_not_1 apply fastforce
  apply (metis Map_of_Val_dom domIff option.map_disc_iff times_option_none)
  subgoal premises prems for a x x' proof -
    have t1: \<open>a x = 1\<close> for x
      by (metis Map_of_Val_dom domIff map_option_is_None mult_1 one_option_def prems(1) prems(2) prems(3) prems(4))
    have t2: \<open>map_option discrete o Map_of_Val x = map_option discrete o Map_of_Val x'\<close>
      using prems(4) t1 by auto
    show ?thesis
      by (metis (mono_tags, lifting) Map_of_Val_inj fun.inj_map_strong discrete.inject option.inj_map_strong prems(2) prems(3) t2) 
  qed .

lemma map_tree_refinement_modify:
  \<open> dom a = dom b \<and> dom b \<subseteq> D
\<Longrightarrow> (\<And>r. r ## push_map idx a \<and> r ## push_map idx b \<and> r * push_map idx a \<in> S \<Longrightarrow> r * push_map idx b \<in> S)
\<Longrightarrow> (\<exists>\<^sup>sa. {(a, a ++ push_map idx b)} \<s>\<u>\<b>\<j>\<s> dom a = D) * Id_on UNIV
    \<r>\<e>\<f>\<i>\<n>\<e>\<s> { (push_map idx a, push_map idx b)}
    \<w>.\<r>.\<t> \<F>_functional id S
    \<i>\<n> { push_map idx a }\<close>
  for a :: \<open>'a list \<Rightarrow> VAL discrete option\<close>
  unfolding Fictional_Forward_Simulation_def the_subtree_def
  apply (clarsimp simp add: set_mult_expn)
  subgoal premises prems for r R a' u x
  proof -
    have t1: \<open>dom x \<inter> dom (idx \<tribullet>\<^sub>m b) = {}\<close>
      using disjoint_iff prems(12) sep_disj_partial_map_disjoint by fastforce
    have t2: \<open>dom r \<inter> dom (idx \<tribullet>\<^sub>m b) = {}\<close>
      by (metis Int_commute prems(2) prems(5) push_map_dom_eq sep_disj_partial_map_disjoint)
    have t3: \<open>dom u \<inter> dom (idx \<tribullet>\<^sub>m b) = {}\<close>
      by (metis inf_commute prems(2) prems(9) push_map_dom_eq sep_disj_partial_map_disjoint)
    have t4: \<open>idx \<tribullet>\<^sub>m b ## u\<close>
      using sep_disj_partial_map_disjoint t3 by blast
    have t5: \<open>idx \<tribullet>\<^sub>m b ## r\<close>
      using sep_disj_partial_map_disjoint t2 by blast
    have t6: \<open>dom a' \<inter> dom x = {}\<close>
      by (meson prems(11) sep_disj_partial_map_disjoint)
    show ?thesis
      apply (simp add: t5, rule exI[where x=u], simp add: t4 prems)
      by (metis dual_order.refl map_add_subsumed_dom mult.commute prems(1) prems(2) prems(5) prems(6) prems(7) push_map_distrib_map_add sep_disj_commute t1 t2 t3 t5 times_fun_map_add_right)
  qed .

lemma fiction_Map_of_Val_ins_comp_id_simp:
  \<open>(\<F>_functional Map_of_Val_ins (Map_of_Val_ins_dom TY) \<Zcomp>
    \<F>_functional id (Map_of_Val_ins ` Map_of_Val_ins_dom TY))
  = \<F>_functional Map_of_Val_ins (Map_of_Val_ins_dom TY)\<close>
  by (rule \<F>_functional_comp[where f=id, simplified, symmetric]; clarsimp)

lemma val_map_eq_index_value_eq:
  \<open>valid_index TY idx \<Longrightarrow>
    u_idx \<in> Well_Type (index_type idx TY) \<Longrightarrow>
    v \<in> Well_Type TY \<Longrightarrow>
    map_option discrete \<circ> Map_of_Val v = idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx) * u \<Longrightarrow>
    u ## idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx) \<Longrightarrow>
    index_value idx v = u_idx \<close>
  subgoal premises prems proof -
    have t1: \<open>dom (pull_map idx (Map_of_Val v)) = Dom_of_TY (index_type idx TY)\<close>
      using Map_of_Val_dom Map_of_Val_pull index_value_welltyp prems(1) prems(3) by auto
    have t2: \<open>dom (pull_map idx (Map_of_Val v)) =
              dom (pull_map idx u) \<union> dom (Map_of_Val u_idx)\<close>
      by (metis dom1_dom dom1_mult dom_map_option_comp homo_one_map_option prems(4) prems(5) pull_map_funcomp pull_map_homo_mult pull_map_sep_disj pull_push_map sep_mult_commute)
    have t3: \<open>dom (pull_map idx u) \<inter> dom (Map_of_Val u_idx) = {}\<close>
      by (metis dom1_dom dom_map_option_comp prems(5) pull_map_sep_disj pull_push_map sep_disj_dom1_disj_disjoint)
    have t4: \<open>dom (Map_of_Val u_idx) = Dom_of_TY (index_type idx TY)\<close>
      using Map_of_Val_dom prems(2) by force
    have t5: \<open>pull_map idx u = 1\<close>
      using t1 t2 t3 t4 by fastforce
    then have \<open>pull_map idx (map_option discrete \<circ> Map_of_Val v) = (map_option discrete \<circ> Map_of_Val u_idx)\<close>
      by (simp add: prems(4) pull_map_homo_mult)
    then have \<open>pull_map idx (Map_of_Val v) = Map_of_Val u_idx\<close>
      by (smt (verit) fun.inj_map_strong homo_one_map_option discrete.inject option.inj_map_strong pull_map_funcomp)
    then show ?thesis
      by (metis Map_of_Val_inj Map_of_Val_pull index_value_welltyp prems(1) prems(2) prems(3))
  qed .

lemma val_map_mod_index_value:
  \<open> valid_index TY idx \<Longrightarrow>
    x \<in> Well_Type TY \<Longrightarrow>
    u \<in> Well_Type (index_type idx TY) \<Longrightarrow>
    v \<in> Well_Type (index_type idx TY) \<Longrightarrow>
    idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u) ## r \<Longrightarrow>
    idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v) ## r \<Longrightarrow>
    idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u) * r = map_option discrete \<circ> Map_of_Val x \<Longrightarrow>
    idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v) * r = map_option discrete \<circ> Map_of_Val (index_mod_value idx (\<lambda>_. v) x)\<close>
  by (simp add: Map_of_Val_mod map_option_funcomp_map_add,
      smt (verit, del_insts) Dom_of_TY Map_of_Val_dom homo_one_map_option index_type_idem
          map_add_subsumed_dom map_option_funcomp_map_add mult.commute push_map_distrib_map_add
          push_map_homo sep_disj_commute sep_disj_partial_map_disjoint times_fun_map_add_right valid_index.simps(1))

lemma val_map_mod_index_value_projection:
  \<open> valid_index TY idx \<Longrightarrow>
    u_idx \<in> Well_Type (index_type idx TY) \<Longrightarrow>
    refinement_projection (\<F>_functional id (Map_of_Val_ins ` Map_of_Val_ins_dom TY)) {idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}
    \<subseteq> Map_of_Val_ins ` Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} * UNIV\<close>
  apply (clarsimp simp add: image_iff set_mult_expn refinement_projection_def
                            Map_of_Val_ins_dom_def Map_of_Val_ins_def;
         case_tac xb; simp add: split_discrete_meta_all)
  apply (smt (verit, best) Mapof_not_1 dom_1 dom_eq_empty_conv dom_map_option_comp)
  by (metis mult_1_class.mult_1_right sep_disj_commuteI sep_magma_1_left val_map_eq_index_value_eq)

lemma fiction_Map_of_Val_ins_projection:
  \<open> valid_index TY idx
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> refinement_projection (\<F>_functional Map_of_Val_ins (Map_of_Val_ins_dom TY))
                          {idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}
      \<subseteq> Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY } * UNIV\<close>
  apply (subst fiction_Map_of_Val_ins_comp_id_simp[symmetric])
  apply (rule refinement_projections_stepwise_UNIV_paired)
  apply (rule Map_of_Val_ins.\<F>_functional_projection)
  apply (clarsimp)
  by (insert val_map_mod_index_value_projection)

lemma fiction_Map_of_Val_ins_projection':
  \<open> valid_index TY idx
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> refinement_projection (\<F>_functional Map_of_Val_ins (Map_of_Val_ins_dom TY))
                          {idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}
      \<subseteq> Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY } * UNIV\<close>
  using fiction_Map_of_Val_ins_projection by blast


lemma fiction_Map_of_Val_ins_refinement:
  \<open> valid_index TY idx
\<Longrightarrow> v \<in> Well_Type (index_type idx TY)
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> (\<forall>x \<in> Well_Type TY. index_mod_value cidx (\<lambda>_. v) x = index_mod_value idx (\<lambda>_. v) x )
\<Longrightarrow> (\<exists>\<^sup>su. {(Some u, (Some o map_discrete (index_mod_value cidx (\<lambda>_. v))) u)}
          \<s>\<u>\<b>\<j>\<s> u \<in> discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}
            \<and> u \<in> discrete ` Well_Type TY) * Id_on UNIV
    \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx),
            idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v))}
    \<w>.\<r>.\<t> \<F>_functional Map_of_Val_ins (Map_of_Val_ins_dom TY)
    \<i>\<n> {idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}\<close>
  apply (subst fiction_Map_of_Val_ins_comp_id_simp[symmetric])
  apply (rule sep_refinement_stepwise[
            OF refinement_frame[where R = UNIV, OF Map_of_Val_ins.\<F>_functional_refinement_complex[simplified]]])
  apply (simp add: split_discrete_ex inj_image_mem_iff split_option_all
                   split_discrete_all index_mod_value_welltyp)
  apply (simp add: frame_preserving_relation_def split_option_all split_discrete_all)
  apply (simp add: Sep_Closed_def)
  subgoal premises prems proof -
    have t1: \<open>A \<subseteq> A' \<Longrightarrow> A * B \<subseteq> A' * B\<close> for A A' B
      by (clarsimp simp add: subset_iff set_mult_expn; blast)
    have \<open>pairself Map_of_Val_ins `
            (\<exists>\<^sup>su. {(Some u, (Some \<circ> map_discrete (index_mod_value cidx (\<lambda>_. v))) u)} \<s>\<u>\<b>\<j>\<s>
             u \<in> discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} \<and> u \<in> discrete ` Well_Type TY)
        \<subseteq> (\<exists>\<^sup>sa. {(a, a ++ (idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v)))} \<s>\<u>\<b>\<j>\<s> dom a = Dom_of_TY TY)\<close>
      apply (clarsimp simp add: set_eq_iff ExSet_image Subjection_image;
             auto simp add: \<open>\<forall>x\<in>_. _\<close> split_discrete_ex inj_image_mem_iff)
      apply (metis Map_of_Val_mod map_option_funcomp_map_add homo_one_map_option prems(1) prems(2) push_map_homo)
      using Map_of_Val_dom apply blast
      using Map_of_Val_dom by blast
    note t2 = this[THEN t1, THEN refinement_sub_fun]
    have t3: \<open>dom (Map_of_Val v) = Dom_of_TY (index_type idx TY)\<close>
      using Map_of_Val_dom prems(2) by force
    have t4: \<open>idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx) \<noteq> 1\<close>
      by (metis Map_of_Val_ins_None Map_of_Val_ins_dom_eval Map_of_Val_ins_eval(1) option.distinct(1) prems(3) push_map_eq_1)
    then have t5: \<open> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx) * r \<noteq> 1\<close> for r
      by (metis (no_types, opaque_lifting) dom1_disjoint_sep_disj dom1_dom dom_eq_empty_conv empty_subsetI inf.orderE one_partial_map sep_no_inverse times_fun_def times_option_none)

    show ?thesis
      apply (rule t2)
      apply (rule map_tree_refinement_modify)
      apply (simp add: Dom_of_TY Map_of_Val_dom prems(1) prems(3) t3)
      apply (simp add: Map_of_Val_ins_def Map_of_Val_ins_dom_def image_iff split_option_ex
                       split_discrete_ex split_discrete_meta_all split_discrete_all t5)
      by (smt (verit, ccfv_threshold) index_mod_value_welltyp prems(1) prems(2) prems(3) sep_disj_commuteI sep_mult_commute sep_no_inverse t4 val_map_mod_index_value)
  qed
  subgoal premises prems proof -

    have t1: \<open> Domain (\<exists>\<^sup>su. {(a u, b u)} \<s>\<u>\<b>\<j>\<s> P u) = { a u |u. P u }\<close> for a b P
      unfolding set_eq_iff Domain_unfold by (clarsimp)
    have t2: \<open>{Some u |u. u \<in> discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} \<and> u \<in> discrete ` Well_Type TY}
                = Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}\<close>
      by (clarsimp simp add: set_eq_iff image_iff Bex_def; blast)

    show ?thesis
      by (subst t1, subst t2, rule val_map_mod_index_value_projection, insert prems(1) prems(3))
  qed .

context notes mul_carrier_option_def[simp] option.pred_True[simp] begin

lemma fiction_Map_of_Val_perm_partial_refinement:
  \<open> valid_index TY idx
\<Longrightarrow> v \<in> Well_Type (index_type idx TY)
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> \<forall>x\<in>Well_Type TY. index_mod_value cidx (\<lambda>_. v) x = index_mod_value idx (\<lambda>_. v) x
\<Longrightarrow> (\<exists>\<^sup>su. {(Some u, (Some o map_discrete (index_mod_value cidx (\<lambda>_. v))) u)}
          \<s>\<u>\<b>\<j>\<s> u \<in> discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}
            \<and> u \<in> discrete ` Well_Type TY) * Id_on UNIV
    \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx),
            to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v))}
    \<w>.\<r>.\<t> \<F>_functional((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom TY)
    \<i>\<n> {to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}\<close>
  unfolding \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified]
  by (rule sep_refinement_stepwise,
      rule refinement_frame[OF fiction_Map_of_Val_ins_refinement],
      assumption,
      assumption,
      assumption,
      assumption,
      rule pointwise_to_share.\<F>_functional_refinement[where a=\<open>idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)\<close>,
              simplified, simplified pointwise_set_UNIV],
      simp,
      simp,
      rule pointwise_to_share.\<F>_functional_projection[
        where S=\<open>{idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}\<close>, simplified, simplified pointwise_set_UNIV],
      simp)

lemma fiction_Map_of_Val_ins_perm_projection:
  \<open> valid_index TY idx
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> refinement_projection (\<F>_functional ((\<circ>) to_share o Map_of_Val_ins) (Map_of_Val_ins_dom TY))
                          { to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx) }
      \<subseteq> Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY } * UNIV \<close>
  unfolding \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified]
  by (rule refinement_projections_stepwise_UNIV_paired,
      rule fiction_Map_of_Val_ins_projection',
      assumption,
      assumption,
      rule pointwise_to_share.\<F>_functional_projection[
        where S=\<open>{idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}\<close>, simplified, simplified pointwise_set_UNIV],
      simp)

lemma fiction_Map_of_Val_ins_perm_projection_half:
  \<open> valid_index TY idx
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> 0 < n
\<Longrightarrow> refinement_projection (\<F>_functional ((\<circ>) to_share o Map_of_Val_ins) (Map_of_Val_ins_dom TY))
                          { n \<odivr> (to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)) }
      \<subseteq> Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} * UNIV\<close>
  unfolding \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified]
  by (rule refinement_projections_stepwise_UNIV_paired,
      rule fiction_Map_of_Val_ins_projection',
      assumption,
      assumption,
      rule pointwise_to_share.refinement_projection_half_perm[
        where S=\<open>{idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}\<close>, simplified, simplified pointwise_set_UNIV],
      simp, simp)


end


end