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

lemma split_discrete_ExBI: \<open>(\<exists>*x. P x) = (\<exists>*x. P (discrete x))\<close>
  unfolding BI_eq_iff by (simp add: split_discrete_ex)

lemma defined_set_in_image[simp]:
  \<open> { f u' |u'. u' \<in> h ` S} = { f (h u) |u. u \<in> S } \<close>
  unfolding set_eq_iff
  by auto


locale MoV =
  fixes   Rep_of_Val :: \<open>VAL \<Rightarrow> 'Rep\<close>
  assumes Rep_of_Val_inj: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> Rep_of_Val Va = Rep_of_Val Vb \<Longrightarrow> Va = Vb\<close>
begin

definition Val_of_Rep :: \<open>TY \<Rightarrow> 'Rep \<Rightarrow> VAL\<close>
  where \<open>Val_of_Rep TY rep = (@v. Rep_of_Val v = rep \<and> v \<in> Well_Type TY)\<close>

definition map_Rep :: \<open>TY \<Rightarrow> (VAL \<Rightarrow> VAL) \<Rightarrow> 'Rep \<Rightarrow> 'Rep\<close>
  where \<open>map_Rep TY f x = Rep_of_Val (f (Val_of_Rep TY x))\<close>

lemma Val_of_Rep_inj[simp]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> Val_of_Rep TY (Rep_of_Val v) = v\<close>
  unfolding Val_of_Rep_def
  using Rep_of_Val_inj by blast

abbreviation Rep_of_TY
  where \<open>Rep_of_TY TY \<equiv> Rep_of_Val ` Well_Type TY\<close>

lemma split_Byte_Rep_ExSet:
  \<open> (\<And>x. P x \<Longrightarrow> x \<in> Rep_of_TY TY)
\<Longrightarrow> (A x \<s>\<u>\<b>\<j> x. P x) =
    (A (Rep_of_Val v) \<s>\<u>\<b>\<j> v. P (Rep_of_Val v)) \<close>
  unfolding BI_eq_iff split_discrete_ex
  by (auto simp: image_iff Bex_def)

definition Rep_of_Val_ins
  where \<open>Rep_of_Val_ins TY = map_option (map_discrete (Val_of_Rep TY))\<close>

definition Rep_of_Val_ins_dom
  where \<open>Rep_of_Val_ins_dom TY = {x. pred_option (\<lambda>x'. discrete.dest x' \<in> Rep_of_TY TY) x}\<close>

lemma Rep_of_Val_ins_eval[simp]:
  \<open>Rep_of_Val_ins TY (Some (discrete u)) = (Some (discrete (Val_of_Rep TY u)))\<close>
  \<open>Rep_of_Val_ins TY None = None\<close>
  unfolding Rep_of_Val_ins_def by simp+

lemma Rep_of_Val_ins_dom_eval[simp]:
  \<open> None \<in> Rep_of_Val_ins_dom TY \<close>
  \<open>Some (discrete x) \<in> Rep_of_Val_ins_dom TY \<longleftrightarrow> x \<in> Rep_of_TY TY\<close>
  unfolding Rep_of_Val_ins_dom_def by simp+

lemma \<F>_functional_condition_Rep_of_Val_ins_dom:
  \<open>\<F>_functional_condition (Rep_of_Val_ins_dom TY)\<close>
  unfolding \<F>_functional_condition_def Rep_of_Val_ins_dom_def
  by(clarsimp; case_tac r; case_tac x; case_tac y; simp)

sublocale Rep_of_Val_ins: cancl_sep_orthogonal_monoid \<open>Rep_of_Val_ins TY\<close> \<open>Rep_of_Val_ins_dom TY\<close>
  unfolding Rep_of_Val_ins_def Rep_of_Val_ins_dom_def
  by (rule cancl_sep_orthogonal_monoid__map_option_discrete,
      simp add: inj_on_def split_discrete_all split_option_all, force,
      simp)


context notes mul_carrier_option_def[simp] option.pred_True[simp] begin

lemma fiction_Map_of_Val_perm_partial_refinement_BYTE:
  \<open> valid_index TY idx
\<Longrightarrow> v \<in> Well_Type (index_type idx TY)
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> \<forall>x\<in>Well_Type TY. index_mod_value cidx (\<lambda>_. v) x = index_mod_value idx (\<lambda>_. v) x
\<Longrightarrow> (\<exists>\<^sup>su. {(Some u, (Some o map_discrete (map_Rep TY (index_mod_value cidx (\<lambda>_. v)))) u)}
          \<s>\<u>\<b>\<j>\<s> u \<in> discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}
            \<and> u \<in> discrete ` Rep_of_Val ` Well_Type TY) * Id_on UNIV
    \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx),
            to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v))}
    \<w>.\<r>.\<t> (\<F>_functional (Rep_of_Val_ins TY) (Rep_of_Val_ins_dom TY) \<Zcomp>
          \<F>_functional((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom TY))
    \<i>\<n> {to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)}\<close>
  subgoal premises prems proof -

    have simp1: \<open>(\<exists>\<^sup>su. A u \<s>\<u>\<b>\<j>\<s>
        u \<in> discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} \<and> u \<in> discrete ` Rep_of_TY TY)
      = (\<exists>\<^sup>sa. A (discrete (Rep_of_Val a)) \<s>\<u>\<b>\<j>\<s> index_value idx a = u_idx \<and> a \<in> Well_Type TY)\<close>
      for A
      unfolding Rep_of_Val_ins_def
      by (auto simp: image_iff)

    have simp2: \<open>(\<exists>\<^sup>su. A u \<s>\<u>\<b>\<j>\<s>
        u \<in> discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} \<and> u \<in> discrete ` Well_Type TY)
      = (\<exists>\<^sup>sa. A (discrete a) \<s>\<u>\<b>\<j>\<s> index_value idx a = u_idx \<and> a \<in> Well_Type TY)\<close>
      for A
      unfolding Rep_of_Val_ins_def BI_eq_iff
      by (auto simp: image_iff)

    have t1[simp]:
      \<open>Domain (\<exists>\<^sup>sa. {(x a, y a)} \<s>\<u>\<b>\<j>\<s> P a) = (\<exists>\<^sup>sa. {(x a)} \<s>\<u>\<b>\<j>\<s> P a)\<close> for x y P
      unfolding set_eq_iff
      by auto

    have simp3[simp]:
         \<open>a \<in> Well_Type TY
       \<Longrightarrow> Val_of_Rep TY (map_Rep TY (index_mod_value cidx (\<lambda>_. v)) (Rep_of_Val a))
         = index_mod_value idx (\<lambda>_. v) a \<close> for a
      by (simp add: index_mod_value_welltyp map_Rep_def prems(1) prems(2) prems(4))
      

    note [cong] = SubjectionSet_cong

    note [simp] = ExSet_image SubjectionSet_image

    note t11 = refinement_frame[where R = UNIV, OF Rep_of_Val_ins.\<F>_functional_refinement_complex,
        where R4=\<open>\<exists>\<^sup>sa. {(Some (discrete (Rep_of_Val a)), Some (discrete (map_Rep TY (index_mod_value cidx (\<lambda>_. v)) (Rep_of_Val a))))}
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
          using index_mod_value_welltyp map_Rep_def apply force
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
      (\<F>_functional (Rep_of_Val_ins TY) (Rep_of_Val_ins_dom TY) \<Zcomp>
       \<F>_functional ((\<circ>) to_share o Map_of_Val_ins) (Map_of_Val_ins_dom TY))
      { to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx) }
    \<subseteq> Some ` discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY } * UNIV \<close>
subgoal premises prems proof -
  have t1:
       \<open>Rep_of_Val_ins TY ` Some ` discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}
      = Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}\<close>
    for TY
    by (auto simp add: image_iff)
  show ?thesis
  apply (rule refinement_projections_stepwise_UNIV_paired)
  prefer 2
  apply (rule fiction_Map_of_Val_ins_perm_projection, insert prems)
  apply (assumption)
  apply (assumption)
  apply (rule Rep_of_Val_ins.\<F>_functional_projection[
          where S=\<open>Some ` discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}\<close>
            and TY=TY,
          simplified t1])
  apply (clarsimp) .
qed .

lemma fiction_Map_of_Val_ins_perm_projection_half_BYTE:
  \<open> valid_index TY idx
\<Longrightarrow> u_idx \<in> Well_Type (index_type idx TY)
\<Longrightarrow> 0 < n
\<Longrightarrow> refinement_projection
     (\<F>_functional (Rep_of_Val_ins TY) (Rep_of_Val_ins_dom TY) \<Zcomp>
      \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom TY))
      { n \<odivr> (to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)) }
   \<subseteq> Some ` discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY} * UNIV\<close>
  subgoal premises prems proof -
  
  have t1:
      \<open>(Rep_of_Val_ins TY ` Some ` discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY})
     = (Some ` discrete ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY})\<close>
      unfolding Rep_of_Val_ins_def set_eq_iff
      by (auto simp: image_iff)

 show ?thesis
  by (insert prems,
      rule refinement_projections_stepwise_UNIV_paired,
      rule Rep_of_Val_ins.\<F>_functional_projection
        [where S=\<open>Some ` discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type TY}\<close>,
          where TY=TY,
          simplified t1],
      ((auto simp: Rep_of_Val_ins_dom_def)[1]),
      rule fiction_Map_of_Val_ins_perm_projection_half,
      assumption,
      assumption,
      assumption)
qed .

end

end



locale MoV_res =
  MoV Rep_of_Val +
  partial_map_resource Res \<open>\<lambda>blk. discrete ` Rep_of_Val ` Well_Type (typ_of_blk blk)\<close>
  for Res :: "('blk \<Rightarrow> 'Rep discrete option) resource_entry"
  and Rep_of_Val :: \<open>VAL \<Rightarrow> 'Rep\<close>
  and typ_of_blk :: \<open>'blk \<Rightarrow> TY\<close>

locale perm_MoV_fiction =
  MoV Rep_of_Val +
  pointwise_base_fiction_for_partial_mapping_resource
      Res \<open>\<lambda>blk. \<F>_functional (Rep_of_Val_ins (typ_of_blk blk)) (Rep_of_Val_ins_dom (typ_of_blk blk)) \<Zcomp>
                 \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (typ_of_blk blk))\<close>
      Fic \<open>\<lambda>blk. discrete ` Rep_of_Val ` Well_Type (typ_of_blk blk)\<close>
  for Res :: "('blk \<Rightarrow> 'Rep discrete option) resource_entry"
  and Rep_of_Val :: \<open>VAL \<Rightarrow> 'Rep\<close>
  and typ_of_blk :: \<open>'blk \<Rightarrow> TY\<close>
  and null_blk :: 'blk
  and Fic :: "('blk \<Rightarrow> aggregate_path \<Rightarrow> VAL discrete share option) fiction_entry"
begin

sublocale MoV_res Res Rep_of_Val typ_of_blk ..

lemma getter_rule:
  \<open> valid_index (typ_of_blk blk) idx
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> u_idx \<in> Well_Type (index_type idx (typ_of_blk blk)) \<and> cblk = blk
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 < n
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' cblk \<lbrace> 1(blk := n \<odivr> (to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx))) \<Ztypecolon> \<phi> Itself \<longmapsto>
      \<lambda>ret. 1(blk := n \<odivr> (to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx))) \<Ztypecolon> \<phi> Itself
          \<s>\<u>\<b>\<j> x. ret = \<phi>arg (discrete (Rep_of_Val x)) \<and> x \<in> Well_Type (typ_of_blk blk) \<and> index_value idx x = u_idx \<rbrace>\<close>
  unfolding Premise_def
  subgoal premises prems proof -

  have [simp]: \<open>cblk = blk\<close>
    by (simp add: prems(2))

  have simp1: \<open>
      (A x \<s>\<u>\<b>\<j> x. B x \<and> x \<in> Rep_of_TY (typ_of_blk blk) \<and> x \<in> Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type (typ_of_blk cblk)})
    = (A (Rep_of_Val v) \<s>\<u>\<b>\<j> v. B (Rep_of_Val v) \<and> v \<in> Well_Type (typ_of_blk blk) \<and> index_value idx v = u_idx) \<close>
  for A B C ret TY S
  unfolding BI_eq_iff split_discrete_ex
  by (auto simp: image_iff Bex_def)

  show ?thesis
    by (rule "_getter_rule_2_"[OF _ fiction_Map_of_Val_ins_perm_projection_half_BYTE,
              where k=cblk and k'=blk and idx1=idx and u_idx1=u_idx,
              simplified split_discrete_ExBI inj_image_mem_iff inj_discrete simp1],
        insert prems, simp+)
qed .


context notes mul_carrier_option_def[simp] option.pred_True[simp] begin

lemma allocate_rule:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>r. finite (dom r) \<longrightarrow> (\<exists>blk. blk \<notin> dom r \<and> typ_of_blk blk = TY \<and> blk \<noteq> null_blk))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>v\<in>U. v \<in> Well_Type TY)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_allocate_res_entry (\<lambda>blk. typ_of_blk blk = TY \<and> blk \<noteq> null_blk) (\<lambda>k. {Some (discrete (Rep_of_Val v)) |v. v\<in>U })
      \<lbrace> Void \<longmapsto> \<lambda>ret. 1(blk := to_share \<circ> (map_option discrete \<circ> Map_of_Val v)) \<Ztypecolon> \<phi> Itself
                  \<s>\<u>\<b>\<j> blk v. ret = \<phi>arg blk \<and> v \<in> U \<and> typ_of_blk blk = TY \<and> blk \<noteq> null_blk  \<rbrace> \<close>
  unfolding Premise_def
  subgoal premises prems proof-

  note pointwise_set_UNIV[simp] \<F>_functional_condition_Map_of_Val_ins_dom[simp]

  have t1[simp]: \<open>v \<in> U \<Longrightarrow> Val_of_Rep TY (Rep_of_Val v) = v\<close> for v
    using prems(2) by auto
  have [simp]:
       \<open>{(1, to_share \<circ> (map_option discrete \<circ> Map_of_Val (Val_of_Rep TY (Rep_of_Val v)))) |v. v \<in> U}
      = {(1, to_share \<circ> (map_option discrete \<circ> Map_of_Val v)) |v. v \<in> U}\<close>
    by force

  note rule = sep_refinement_stepwise[
        OF refinement_frame[OF Rep_of_Val_ins.\<F>_functional_refinement'[simplified]]
           sep_refinement_stepwise[
                    OF refinement_frame[OF Map_of_Val_ins.\<F>_functional_refinement'[simplified]]
                       pointwise_to_share.\<F>_functional_refinement'[where B=\<open>Map_of_Val_ins ` B\<close> for B, unfolded defined_set_in_image]
                       pointwise_to_share.\<F>_functional_projection,
                    where B6=\<open>Rep_of_Val_ins TY ` B\<close> for B, unfolded defined_set_in_image],
        where a35=\<open>None\<close> and B22=\<open>{Some (discrete (Rep_of_Val v)) |v. v \<in> U}\<close>,
        simplified,
        OF _ _ _ refinement_projections_stepwise_UNIV_paired[
            OF Map_of_Val_ins.\<F>_functional_projection
               pointwise_to_share.\<F>_functional_projection,
            where Dc=\<open>{1}\<close>,
            simplified]]

  show ?thesis
    by (rule "__allocate_rule_3__"[
          where U =\<open>\<lambda>k. {Some (discrete (Rep_of_Val v)) |v. v\<in>U }\<close>
            and U'=\<open>\<lambda>k. {to_share \<circ> (map_option discrete \<circ> Map_of_Val v) |v. v \<in> U}\<close> , simplified],
        unfold \<F>_functional_comp[where f=\<open>(\<circ>) to_share\<close> and Df=\<open>UNIV\<close>, simplified, simp]
               one_option_def,
        simp, rule rule,
        simp add: subset_iff, insert Rep_of_Val_ins_dom_eval(2) prems(2), blast,
        simp add: \<F>_functional_condition_Rep_of_Val_ins_dom,
        simp add: subset_iff, force,
        simp add: R.in_invariant inj_image_mem_iff, force,
        clarsimp simp add: R.in_invariant Ball_def dom1_dom, metis dom_map_option_comp prems(1))
qed .

lemma setter_rule:
  assumes EQ: \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> cblk = blk\<close>
  shows \<open> valid_index (typ_of_blk blk) idx
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type (index_type idx (typ_of_blk blk))
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> u_idx \<in> Well_Type (index_type idx (typ_of_blk blk))
      \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>Well_Type (typ_of_blk blk). index_mod_value cidx (\<lambda>_. v) x = index_mod_value idx (\<lambda>_. v) x)
      \<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (map_fun_atS cblk (\<lambda>h. {Some (map_discrete (map_Rep (typ_of_blk cblk) (index_mod_value cidx (\<lambda>_. v))) (the h))}))
            \<lbrace> 1(blk := to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val u_idx)) \<Ztypecolon> \<phi> Itself \<longmapsto>
              \<lambda>\<r>\<e>\<t>. 1(blk := to_share \<circ> idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v)) \<Ztypecolon> \<phi> Itself \<rbrace> \<close>
  unfolding Premise_def
  by (simp add: EQ[unfolded Premise_def],
      rule "_setter_rule_2_"[where f=\<open>\<lambda>h. {Some (map_discrete (map_Rep (typ_of_blk blk) (index_mod_value cidx (\<lambda>_. v))) h)}\<close>
                        and V=\<open>discrete ` Rep_of_Val ` {a. index_value idx a = u_idx \<and> a \<in> Well_Type (typ_of_blk blk)}\<close>
                        and F=\<open>\<lambda>_. {to_share o idx \<tribullet>\<^sub>m (map_option discrete \<circ> Map_of_Val v)}\<close>
                        for idx cidx v u_idx,
                      simplified,
                      OF _ fiction_Map_of_Val_perm_partial_refinement_BYTE[simplified]
                           fiction_Map_of_Val_ins_perm_projection_BYTE[simplified]],
      simp,
      assumption,
      assumption,
      assumption,
      assumption,
      assumption,
      assumption,
      clarsimp simp add: split_discrete_meta_all inj_image_mem_iff index_mod_value_welltyp image_iff Bex_def,
      metis Val_of_Rep_inj index_mod_value_welltyp map_Rep_def)

lemma deallocate_rule:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type (typ_of_blk blk)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (map_fun_atS blk (\<lambda>_. {None}))
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

  have [simp]: \<open>Val_of_Rep (typ_of_blk blk) (Rep_of_Val v) = v\<close>
    by (simp add: prems)

  note rule1 = refinement_projections_stepwise_UNIV_paired[
          OF Map_of_Val_ins.\<F>_functional_projection
             pointwise_to_share.\<F>_functional_projection,
          where Dc=\<open>{Some (discrete v)}\<close>,
          simplified]

  show ?thesis
apply simp
apply (rule "_setter_rule_2_"[where f=\<open>\<lambda>_. {None}\<close> and V=\<open>{discrete v}\<close> and F=\<open>\<lambda>_. 1\<close> for v, simplified])
apply (simp,
        unfold refinement_source_subjection, rule impI,
        rule sep_refinement_stepwise [
            OF refinement_frame[OF Rep_of_Val_ins.\<F>_functional_refinement[simplified]]
               sep_refinement_stepwise[
                        OF refinement_frame[OF Map_of_Val_ins.\<F>_functional_refinement[simplified]]
                           pointwise_to_share.\<F>_functional_refinement
                           pointwise_to_share.\<F>_functional_projection],
            where a16=\<open>Some (discrete (Rep_of_Val v))\<close> and b16=None and TY16=\<open>typ_of_blk blk\<close>,
            simplified])
    apply blast
    using \<F>_functional_condition_Rep_of_Val_ins_dom apply presburger
    using prems apply blast
    apply (rule rule1)
    using prems apply blast
    apply (rule refinement_projections_stepwise_UNIV_paired)
    prefer 2
    apply (rule rule1)
    apply (simp add: prems)
    apply (rule Rep_of_Val_ins.\<F>_functional_projection
      [where S=\<open>{Some (discrete (Rep_of_Val v))}\<close> and TY=\<open>typ_of_blk blk\<close>, simplified])
    using prems by blast
qed .

end

end



interpretation MovI: MoV id by (standard, simp)

end