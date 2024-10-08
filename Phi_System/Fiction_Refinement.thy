theory Fiction_Refinemen
  imports PhiSem_Formalization_Tools Phi_Semantics_Framework.Phi_SemFrame_ex
  abbrevs "<refines>" = "\<r>\<e>\<f>\<i>\<n>\<e>\<s>"
      and "<w.r.t>" = "\<w>.\<r>.\<t>"
begin



 





(*

definition Is_Frame_Proc :: \<open>'ret proc \<Rightarrow> bool\<close>
  where \<open>Is_Frame_Proc f \<longleftrightarrow>
    (\<forall>v s s' r. Success v s' \<in> f s \<and> r ## s \<longrightarrow> Success v (r * s') \<in> f (r * s) \<and> r ## s') \<and>
    (\<forall>e s s' r. Abnormal e s' \<in> f s \<and> r ## s \<longrightarrow> Abnormal e (r * s') \<in> f (r * s) \<and> r ## s')\<close>

(* definition Is_Frame_Proc :: \<open>'ret::VALs proc \<Rightarrow> bool\<close>
  where \<open>Is_Frame_Proc f \<longleftrightarrow>
    (\<forall>v s s' r. Success v s' \<in> f s \<and> r ## s \<longrightarrow> Success v (r * s') \<in> f (r * s) \<and> r ## s') \<and>
    (\<forall>e s s' r. Abnormal e s' \<in> f s \<and> r ## s \<longrightarrow> Abnormal e (r * s') \<in> f (r * s) \<and> r ## s')\<close> *)

lemma
  \<open> Is_Frame_Proc F
\<Longrightarrow> (\<And>v. Is_Frame_Proc (G v))
\<Longrightarrow> Is_Frame_Proc (F \<bind> G)\<close>
  unfolding Is_Frame_Proc_def bind_def
  subgoal premises prems
    apply (clarsimp; rule; clarsimp)
    apply (case_tac x; simp add: Bex_def split_comp_Ex)
    using prems(1) prems(2) apply blast
    apply (case_tac x; simp add: Bex_def split_comp_Ex)
    using prems(1) prems(2) apply blast
    using prems(1) by blast .
*)

(*
definition Transition_of :: \<open>'ret proc \<Rightarrow> 'ret \<phi>arg + ABNM \<Rightarrow> resource rel\<close>
  where \<open>Transition_of f = (\<lambda>x. case x of Inl v \<Rightarrow> { (s,s'). Success v s' \<in> f s \<and> s \<in> RES.SPACE }
                                        | Inr e \<Rightarrow> { (s,s'). Abnormal e s' \<in> f s \<and> s \<in> RES.SPACE } )\<close> *)

(*
definition Raw_Procedure :: "'ret proc
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> resource rel)
                        \<Rightarrow> bool"
    ("\<r>\<a>\<w> \<p>\<r>\<o>\<c> (2_) \<r>\<e>\<f>\<i>\<n>\<e>\<s> _ " [11,11] 10)
  where "Raw_Procedure f S \<longleftrightarrow> (\<forall>x r. f (r * x) \<subseteq> LooseState (\<lambda>v. { r * y | y. (x,y) \<in> S v }) 0)"

definition Fictional_Refine :: "'ret proc
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> fiction rel)
                        \<Rightarrow> bool"
  where \<open>Fictional_Refine f S \<longleftrightarrow> (\<forall>x r. f (r * x) \<subseteq> LooseState (\<lambda>v. { r * y | y. (x,y) \<in> S v }) 0)\<close> *)




(*
lemma refinement_frame'':
  \<open> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> Id_on R * A \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on R * B \<w>.\<r>.\<t> I \<i>\<n> R * D\<close>
  for B :: \<open>'b::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff)
  subgoal for r R u v u' v' rr a b

lemma refinement_frame':
  \<open> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> Id_on UNIV * A = A\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff set_eq_iff; rule)
   apply clarsimp
  subgoal for r a b


  subgoal for x r R u v rr a' b'

lemma
  \<open>Any \<r>\<e>\<f>\<i>\<n>\<e>\<s> Any \<w>.\<r>.\<t> Itself \<i>\<n> D\<close>
  for Any :: \<open>'a::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff)
  subgoal for x r R t u
    apply (rule exI[where x=x])


lemma
  \<open>Any \<r>\<e>\<f>\<i>\<n>\<e>\<s> UNIV \<w>.\<r>.\<t> I\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff)
  subgoal for x r R t u v *)


(*
lemma
  \<open>refinement_projection I1 (refinement_projection I2 (UNIV * D)) \<subseteq> refinement_projection (I1 ;\<^sub>\<I> I2) D\<close>
unfolding refinement_projection_def
  apply (clarsimp simp add: Bex_def set_eq_iff set_mult_expn)
  subgoal for x u v u' v'

lemma
  \<open>refinement_projection (I1 ;\<^sub>\<I> I2) D \<subseteq> refinement_projection I1 (refinement_projection I2 D)\<close>
  for I1 :: \<open>('c::sep_monoid, 'a::sep_magma_1) interp\<close>
  unfolding refinement_projection_def
  apply (clarsimp simp add: Bex_def set_eq_iff set_mult_expn)
  subgoal for x x' u v
    by (metis mult_1_class.mult_1_left sep_magma_1_right) *)




(*
lemma
  \<open> A1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 \<w>.\<r>.\<t> I \<i>\<n> D1
\<Longrightarrow> A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B2 \<w>.\<r>.\<t> I \<i>\<n> D2
\<Longrightarrow> A1 * A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 * B2 \<w>.\<r>.\<t> I \<i>\<n> D1 * D2\<close>
  for A1 :: \<open>'a::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: \<phi>expns subset_iff Image_def Bex_def)
  subgoal premises prems for r R u v ux a vx b a' b'
  proof -
    thm prems(1)[THEN spec[where x=]]
    thm prems *)



(*
lemma
  \<open>refinement_projection (\<F>_pointwise I) (fun_upd 1 k ` D') = UNIV * fun_upd 1 k ` refinement_projection I D'\<close>
  unfolding refinement_projection_def
  apply (clarsimp simp add: set_eq_iff Bex_def set_mult_expn image_iff; rule; clarsimp simp add: times_fun)
  prefer 2
  subgoal for x x' u xc *)






context resource begin

lemma \<phi>R_get_res_transition:
  \<open> Transition_of' \<phi>R_get_res' ret = Id_on {s. s \<in> SPACE \<and> ret = Normal (\<phi>arg (get s))}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff; blast)

lemma setter_transition:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> F m \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> Transition_of' (\<phi>R_set_res' F) ret
 \<subseteq> {(x,y). x \<in> SPACE \<and> (P (get x) \<longrightarrow> y = updt F x \<and> ret = Normal \<phi>V_none)}\<close>
  unfolding Transition_of'_def \<phi>R_set_res'_def
  apply (cases ret; auto simp add: set_eq_iff \<phi>V_none_def if_split_mem2)
  by (metis \<r>_valid_split fun_upd_same fun_upd_upd proj_inj)

lemma setter_valid:
  \<open>Valid_Proc (\<phi>R_set_res' F)\<close>
  unfolding Valid_Proc_def \<phi>R_set_res'_def bind_def Return_def det_lift_def
  by (clarsimp split: option.split)


end

context basic_fiction begin

context begin

private lemma from_fictional_refinement':
  \<open> Valid_Proc f
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> Rel v \<w>.\<r>.\<t> R.basic_fiction ;\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition Rel
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>v. y \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Normal v) \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. y \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Abnm e))\<close>
  unfolding \<phi>Procedure_alt Fictional_Forward_Simulation_def atomize_all Valid_Transition_def
  apply (auto simp add: Image_iff subset_iff Bex_def R.basic_fiction_\<I> \<phi>expns Transition_of'_def
          LooseState_def split_sum_all INTERP_RES_def interp_split' R.\<r>_valid_split' interp_comp_\<I>
          R.inject_wand_homo inject_wand_homo prj.homo_mult eval_stat_forall split: eval_stat.split)
  subgoal premises prems for r u y v y' rr
    thm prems
    thm prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
  proof -
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> \<I> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
      get r ## x \<and> x \<in> D \<and> Success v y' \<in> f xa \<and> R.clean xa \<in> R.SPACE \<and> (\<exists>m. xa R.name = R.inject m \<and> m \<in>\<^sub>S\<^sub>H R.domain))\<close>
      apply (rule exI[where x=\<open>(u * R.mk y)\<close>], simp add: prems R.inj.homo_mult[symmetric] )
      using prems(11) prems(12) by blast
    note prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>],
            THEN mp, OF this]
    then show ?thesis
    apply clarsimp
    subgoal for yy ya
      apply (rule exI[where x=yy], clarsimp simp add: inj.homo_mult[symmetric] prems prj.homo_mult, rule)
      apply (metis R.resource_kind_axioms Valid_Proc_def prems(1) prems(14) resource_kind.\<r>_valid_split t2 times_fupdt_1_apply_sep)
      using prems(10) by blast .
qed
  subgoal premises prems for r u y v y' rr
  proof -
    thm prems(5)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> \<I> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
      get r ## x \<and> x \<in> D \<and> Abnormal v y' \<in> f xa \<and> R.clean xa \<in> R.SPACE \<and> (\<exists>m. xa R.name = R.inject m \<and> m \<in>\<^sub>S\<^sub>H R.domain))\<close>
      by (metis (no_types, lifting) R.inj.homo_mult fiction_kind.sep_disj_get_name_eq fiction_kind_axioms insert_iff mult_in_sep_homo_set prems(11) prems(12) prems(13) prems(14) prems(15) prems(16) prems(17) prems(3) prems(7) prems(8) prems(9) times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)
    note prems(5)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>],
            THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal for yy ya
        apply (rule exI[where x=yy], clarsimp simp add: inj.homo_mult[symmetric] prems prj.homo_mult, rule)
        apply (metis R.\<r>_valid_split Valid_Proc_def prems(1) prems(14) t2 times_fupdt_1_apply_sep)
        using prems(10) by blast .
  qed
  by (metis (no_types, lifting) R.inj.homo_mult mult_in_sep_homo_set sep_disj_get_name times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)


lemma from_fictional_refinement:
  \<open> Valid_Proc f
\<Longrightarrow> YY = (\<lambda>v. y \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Normal v))
\<Longrightarrow> EE = (\<lambda>e. y \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Abnm e))
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> Rel v \<w>.\<r>.\<t> R.basic_fiction ;\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition Rel
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE\<close>
  using from_fictional_refinement' by blast

end

lemma "__getter_rule__":
  \<open> Valid_Proc getter
\<Longrightarrow> (\<And>ret. Transition_of' getter ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({x} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg v)) \<w>.\<r>.\<t> R.basic_fiction ;\<^sub>\<I> I \<i>\<n> {x})
\<Longrightarrow> \<p>\<r>\<o>\<c> getter \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>ret. x \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
  by (rule from_fictional_refinement[where Rel = \<open>\<lambda>ret. Id_on ({x} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg v))\<close>
                                       and D = \<open>{x}\<close>],
     assumption,
     clarsimp simp add: set_eq_iff Subjection_expn Id_on_iff ExBI_expn,
     simp add: Id_on_iff zero_set_def zero_fun_def,
     assumption,
     simp add: Valid_Transition_def zero_set_def,
     simp)

lemma "__setter_rule__":
  \<open> Valid_Proc setter
\<Longrightarrow> (\<And>ret. Transition_of' setter ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(x,y)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none
            \<w>.\<r>.\<t> R.basic_fiction ;\<^sub>\<I> I \<i>\<n> {x})
\<Longrightarrow> \<p>\<r>\<o>\<c> setter \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>_. y \<Ztypecolon> \<phi> Itself \<rbrace>\<close>
  by (rule from_fictional_refinement
                  [where Rel=\<open>\<lambda>ret. {(x,y)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none\<close> and D = \<open>{x}\<close>],
      assumption,
      clarsimp simp add: set_eq_iff Subjection_expn Id_on_iff ExBI_expn \<phi>arg_All fun_eq_iff \<phi>V_none_def,
      simp add: Id_on_iff zero_set_def zero_fun_def,
      assumption,
      simp add: Valid_Transition_def zero_set_def,
      simp)

lemma "__allocator_rule__":
  \<open> Valid_Proc allocator
\<Longrightarrow> (\<And>ret. Transition_of' allocator ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1,y k)} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k
            \<w>.\<r>.\<t> R.basic_fiction ;\<^sub>\<I> I \<i>\<n> {1})
\<Longrightarrow> \<p>\<r>\<o>\<c> allocator \<lbrace> Void \<longmapsto> \<lambda>ret. y k \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> k. ret = \<phi>arg k \<and> P k \<rbrace>\<close>
  by (rule from_fictional_refinement
        [where Rel=\<open>\<lambda>ret. {(1,y k)} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k\<close>
           and x=\<open>1\<close> and D=\<open>{1}\<close>, unfolded \<phi>_unit],
      assumption,
      clarsimp simp add: set_eq_iff Subjection_expn Id_on_iff ExBI_expn \<phi>arg_All fun_eq_iff \<phi>V_none_def,
      simp add: Id_on_iff zero_set_def zero_fun_def,
      assumption,
      simp add: Valid_Transition_def zero_set_def,
      simp)
end


subsubsection \<open>2-level Partial Map Resource\<close>

context partial_map_resource2 begin

lemma getter_transition:
  \<open> Transition_of' (\<phi>R_get_res_entry' k k2) ret
        = Id_on {s. s \<in> SPACE \<and> ret = (case get s k k2 of Some v \<Rightarrow> Normal (\<phi>arg v) | _ \<Rightarrow> Crash)}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def \<phi>R_get_res_entry'_def bind_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff split: option.split; blast)

lemma getter_refinement:
  \<open>Transition_of' (\<phi>R_get_res_entry' k k2) ret
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({1(k := 1(k2 \<mapsto> any))} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg any))
   \<w>.\<r>.\<t> basic_fiction \<i>\<n> {1(k := 1(k2 \<mapsto> any))}\<close>
  unfolding Fictional_Forward_Simulation_def getter_transition
  apply (cases ret; clarsimp split: option.split simp add: basic_fiction_\<I> set_mult_expn Id_on_iff
          Subjection_expn zero_set_def set_eq_iff prj.homo_mult times_fun)
  by (smt (verit, del_insts) fun_sep_disj_imply_v fun_upd_triv mult_1_class.mult_1_right option.exhaust option.inject sep_disj_commuteI sep_disj_get_name sep_disj_multD2 sep_disj_option_discrete(2) sep_mult_commute)
  
lemma getter_valid:
  \<open>Valid_Proc (\<phi>R_get_res_entry' k k2)\<close>
  unfolding Valid_Proc_def \<phi>R_get_res_entry'_def \<phi>R_get_res'_def bind_def Return_def det_lift_def
  by (clarsimp split: option.split)


lemma setter_refinement:
  \<open> \<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m k k2 = Some any \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H domain
\<Longrightarrow> Transition_of' (\<phi>R_set_res' (map_fun_at (map_fun_at (\<lambda>_. u) k2) k)) ret
\<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` pairself (fun_upd 1 k2) ` {(Some any, u)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none
\<w>.\<r>.\<t> basic_fiction \<i>\<n> (fun_upd 1 k) ` (fun_upd 1 k2) ` {Some any}\<close>
  apply (rule refinement_sub_fun[OF setter_transition[where F=\<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k\<close>]], assumption)
  unfolding Fictional_Forward_Simulation_def setter_transition
  apply (clarsimp simp add: basic_fiction_\<I> \<phi>expns prj.homo_mult times_fun_upd sep_disj_partial_map_upd
        discrete_semigroup_sepdisj_fun SPACE_mult_homo \<r>_valid_split'
        times_fun inj.homo_mult[symmetric] inject_wand_homo)
  subgoal premises prems for r R x' u' a
  proof -
    have t1[simp]: \<open>a k k2 ## Some any\<close>
      by (metis fun_sep_disj_imply_v fun_upd_triv prems(5) prems(9) sep_disj_commuteI sep_disj_multD2)
    have t2[simp]: \<open>r k k2 ## a k k2 * Some any\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv discrete_semigroup_sepdisj_fun prems(5))
    have t3[simp]: \<open>r k k2 * (a k k2 * Some any) = Some any\<close>
      using t1 t2 by force
    have t4[simp]: \<open>x' = clean u' * mk (map_fun_at (map_fun_at (\<lambda>_. u) k2) k (r * (a * 1(k := 1(k2 \<mapsto> any))))) \<and> ret = Normal \<phi>V_none\<close>
      using prems(3) by fastforce
    have t5[simp]: \<open>r ## 1(k := 1(k2 := u))\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv discrete_semigroup_sepdisj_fun prems(5))
    have t6[simp]: \<open>(r * a) k k2 = None\<close>
      by (metis sep_disj_multI1 sep_disj_option_discrete(1) t1 t2 times_fun)
    then have [simp]:
        \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (r * (a * 1(k := 1(k2 \<mapsto> any))))
            = (r * a) * 1(k := 1(k2 := u))\<close>
        unfolding map_fun_at_def fun_eq_iff times_fun_def
        by simp
    have t1[simp]: \<open>clean u' * mk a = u'\<close>
      by (metis fun_split_1 prems(8))
    show ?thesis
      apply (simp, rule exI[where x=u']; simp add: prems; rule)
      apply (smt (verit, del_insts) fun_sep_disj_1_fupdt(1) fun_upd_triv inj.homo_mult inj.sep_disj_homo_semi inject_assoc_homo discrete_semigroup_sepdisj_fun prems(5) prems(8) prems(9) sep_disj_multD1 sep_disj_multI1 sep_mult_commute sep_space_entry.times_fun_upd sep_space_entry_axioms times_fupdt_1_apply_sep)
      by (metis (mono_tags, lifting) fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo_semi discrete_semigroup_sepdisj_fun prems(5) prems(8) prems(9) sep_disj_multD1 sep_disj_multI1 sep_disj_multI2)
  qed .

end



(* lemma \<phi>R_get_res_transition:
  \<open> (\<And>res. Transition_of' (F res) ret \<subseteq> Id_on (UNIV \<s>\<u>\<b>\<j> res \<in> UNIV * P ret))
\<Longrightarrow> Transition_of' (\<phi>R_get_res F) ret \<subseteq> Id_on SPACE * Id_on (mk ` P ret)\<close>
  unfolding Transition_of'_def \<phi>R_get_res_def
  apply (cases ret; clarsimp simp add: set_eq_iff Id_on_iff subset_iff Subjection_expn image_iff
            Bex_def set_mult_expn)
  apply (smt (verit, ccfv_threshold) SPACE_mult_homo fun_sep_disj_1_fupdt(1) fun_split_1 inj_prj_in_SPACE mk_homo_mult sep_disj_clean sep_disj_mk sep_mult_assoc' times_fun_upd
  apply (smt (verit) SPACE_mult_homo fun_split_1 inj_prj_in_SPACE mk_homo_mult sep_disj_clean sep_disj_mk sep_disj_multI1 sep_mult_assoc'
  by (smt (z3) SPACE_mult_homo fun_split_1 inj_prj_in_SPACE mk_homo_mult sep_disj_clean sep_disj_mk sep_disj_multI1 sep_mult_assoc'
*)
(*
  term apply (metis \<r>_valid_split fun_split_1 proj_inj sep_disj_clean)
  apply (metis \<r>_valid_split fun_split_1 proj_inj sep_disj_clean)
  by (metis sep_disj_clean) *)

lemma
  \<open>pairself (\<lambda>x. 1(k := x)) ` {(Some any, u)} = {(1(k \<mapsto> any), 1(k := u))}\<close>
  by (clarsimp simp add: set_eq_iff image_iff; blast)

subsubsection \<open>Mapping Resource\<close>

context mapping_resource begin

lemma allocator_transition:
  \<open> (\<forall>r. r \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k))
\<Longrightarrow> Transition_of' (\<phi>R_allocate_res_entry' P init) ret
        \<subseteq> (Id_on SPACE * {(1, mk (1(k := init))) | k. ret = Normal (\<phi>arg k) \<and> P k})\<close>
  unfolding Transition_of'_def \<phi>R_allocate_res_entry'_def \<phi>R_get_res_def bind_def Return_def
      det_lift_def \<phi>R_set_res_def Let_def
  apply (cases ret; clarsimp simp add: zero_set_def set_eq_iff set_mult_expn Subjection_expn Id_on_iff)
  subgoal premises prems for r
  proof -
    thm prems
    have t1: \<open>get r \<in>\<^sub>S\<^sub>H domain\<close>
      using get_res_valid_raw prems(3) by blast
    define kk where \<open>kk = (SOME k. get r k = 1 \<and> P k)\<close>
    have t2: \<open>\<exists>k. get r k = 1 \<and> P k\<close>
      using dom1_def prems(1) t1 by fastforce
    have t3[simp]: \<open>get r kk = 1 \<and> P kk\<close>
      unfolding kk_def
      by (insert t2; clarify; rule someI[where P=\<open>\<lambda>k. get r k = 1 \<and> P k\<close>]; blast)
    note [simp] = kk_def[symmetric]
    have t4 [simp]: \<open>(get r)(kk := init) = get r * 1(kk := init)\<close>
      by (simp add: fun_eq_iff)
    have t5[simp]: \<open>get r ## 1(kk := init)\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv sep_magma_1_right t3)
    show ?thesis
      apply (simp add: fun_eq_iff inj.homo_mult prems)
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo_semi inj_prj_in_SPACE prems(3) t5)
  qed .

lemma allocator_refinement:
  \<open> \<forall>r. r \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k)
\<Longrightarrow> Transition_of' (\<phi>R_allocate_res_entry' P init) ret
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1, 1(k := init))} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k
   \<w>.\<r>.\<t> basic_fiction \<i>\<n> {1}\<close>
  apply (rule refinement_sub_fun[OF allocator_transition], assumption)
  unfolding Fictional_Forward_Simulation_def
  apply (cases ret; clarsimp simp add: set_mult_expn Subjection_expn basic_fiction_\<I>
      mk_homo_mult)
  subgoal premises prems for r R u k
  proof -
    have [simp]: \<open>r ## 1(k := init)\<close>
      using prems(4) prems(6) sep_disj_multD2 by blast
    show ?thesis
      apply (simp add: mk_homo_mult)
      using prems(3) prems(4) prems(6) sep_disj_multI2 sep_mult_assoc by blast
  qed .

lemma allocator_valid:
  \<open> \<forall>r. r \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k)
\<Longrightarrow> \<forall>k. P k \<longrightarrow> 1(k := init) \<in>\<^sub>S\<^sub>H domain
\<Longrightarrow> Valid_Proc (\<phi>R_allocate_res_entry' P init)\<close>
  unfolding Valid_Proc_def \<phi>R_allocate_res_entry'_def \<phi>R_get_res_def \<phi>R_set_res_def
            bind_def Return_def det_lift_def Let_def
  apply (clarsimp split: option.split)
  subgoal premises prems for r
  proof -
    define kk where \<open>kk = (SOME k. get r k = 1 \<and> P k)\<close>
    have [simp]: \<open>get r kk = 1 \<and> P kk\<close>
      by (smt (verit, best) dom1_def kk_def mem_Collect_eq prems(1) prems(3) resource.get_res_valid_raw resource_axioms someI)
    have t1[simp]: \<open>(get r)(kk := init) = get r * 1(kk := init)\<close>
      by (simp add: fun_eq_iff)
    have t2[simp]: \<open>get r ## 1(kk := init)\<close>
      by (simp add: sep_disj_fun_def)
    have t3[simp]: \<open>r(name := inject ((get r)(kk := init))) = r * mk(1(kk := init))\<close>
      apply simp using inj.homo_mult prems(3) by force
    have [simp]: \<open>r ## mk (1(kk := init))\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo_semi inj_prj_in_SPACE prems(3) t2)
    show ?thesis
      by (fold kk_def; simp only: t3; simp add: SPACE_mult_homo prems;
          simp add: SPACE_def prems(2))
  qed .

end

subsubsection \<open>1-level Partial Map Resource\<close>

context partial_map_resource begin

lemma getter_transition:
  \<open> Transition_of' (\<phi>R_get_res_entry' k) ret
        = Id_on {s. s \<in> SPACE \<and> ret = (case get s k of Some v \<Rightarrow> Normal (\<phi>arg v) | _ \<Rightarrow> Crash)}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def \<phi>R_get_res_entry'_def bind_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff split: option.split; blast)

lemma getter_refinement:
  \<open>Transition_of' (\<phi>R_get_res_entry' k) ret
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({1(k \<mapsto> any)} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg any))
   \<w>.\<r>.\<t> basic_fiction \<i>\<n> {1(k \<mapsto> any)}\<close>
  unfolding Fictional_Forward_Simulation_def getter_transition
  apply (cases ret; clarsimp split: option.split simp add: basic_fiction_\<I> set_mult_expn Id_on_iff
          Subjection_expn zero_set_def set_eq_iff prj.homo_mult times_fun)
  by (smt (verit, best) domIff fun_1upd_homo fun_split_1_not_dom fun_upd_same map_upd_eqD1 sep_disj_partial_map_some_none sep_space_entry.sep_disj_get_name sep_space_entry_axioms)

lemma getter_valid:
  \<open>Valid_Proc (\<phi>R_get_res_entry' k)\<close>
  unfolding Valid_Proc_def \<phi>R_get_res_entry'_def \<phi>R_get_res'_def bind_def Return_def det_lift_def
  by (clarsimp split: option.split)

lemma setter_refinement:
  \<open>(\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m k = Some any \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> Transition_of' (\<phi>R_set_res' (\<lambda>f. f(k := u))) ret
  \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` {(Some any, u)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none \<w>.\<r>.\<t> basic_fiction \<i>\<n> fun_upd 1 k ` {Some any}\<close>
  apply (rule refinement_sub_fun[OF setter_transition[where F=\<open>\<lambda>f. f(k := u)\<close>]], assumption)
  unfolding Fictional_Forward_Simulation_def setter_transition
  apply (clarsimp simp add: basic_fiction_\<I> \<phi>expns prj.homo_mult times_fun_upd sep_disj_partial_map_upd
        discrete_semigroup_sepdisj_fun SPACE_mult_homo \<r>_valid_split'
        times_fun inj.homo_mult[symmetric] inject_wand_homo dom_mult)
  subgoal premises prems for r R x' u' a
  proof -
    have t1[simp]: \<open>a ## 1(k \<mapsto> any)\<close>
      using prems(5) prems(9) sep_disj_commuteI sep_disj_multD2 by blast
    have t2[simp]: \<open>r ## (a * 1(k \<mapsto> any))\<close>
      by (simp add: prems(5) prems(9) sep_disj_commuteI sep_disj_multI1 sep_mult_commute)
    have t3[simp]: \<open>x' = clean u' * mk ((r * (a * 1(k \<mapsto> any)))(k := u)) \<and> ret = Normal \<phi>V_none\<close>
      by (smt (z3) map_upd_Some_unfold prems(3) prems(5) sep_disj_partial_map_some_none t1 times_option(3))
    have t4[simp]: \<open>mk ((r * (a * 1(k \<mapsto> any)))(k := u)) = mk (r * (a * 1(k := u)))\<close>
      by (metis domIff fun_upd_same fun_upd_upd option.distinct(1) sep_disj_partial_map_upd t1 t2)
    have t5[simp]: \<open>clean u' * mk a = u'\<close>
      by (metis fun_split_1 prems(8))
    show ?thesis
      apply (simp add: prems, rule exI[where x=u']; simp add: prems; rule)
      apply (smt (verit, ccfv_threshold) mk_homo_mult discrete_semigroup_sepdisj_fun prems(5) prems(9) sep_disj_clean sep_disj_mk sep_disj_multD1 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc' sep_mult_left_commute t4 t5)
      by (smt (verit, best) fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1) inj.sep_disj_homo mult_1_class.mult_1_left discrete_semigroup_sepdisj_fun sep_disj_commute sep_disj_multD1 sep_disj_multI1 sep_mult_commute t1 t2 t5)
  qed .

end


subsubsection \<open>pointwise_fiction_for_partial_mapping_resource\<close>

locale pointwise_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_pointwise I\<close>
for Res :: "('key \<Rightarrow> 'val::discrete_semigroup option) resource_entry"
and I :: \<open>('fic::sep_algebra, 'val option) interp\<close>
and Fic :: "('key \<Rightarrow> 'fic) fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_pointwise I\<close> ..

lemma getter_rule:
  \<open> refinement_projection I {x} \<subseteq> UNIV * {Some v}
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k \<lbrace> 1(k := x) \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>ret. 1(k := x) \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
  by (rule "__getter_rule__",
      rule R.getter_valid,
      rule sep_refinement_stepwise,
      rule R.getter_refinement[THEN refinement_frame[where R=UNIV]],
      unfold Subjection_Id_on Subjection_times,
      rule refinement_subjection[OF constant_refinement],
      rule \<F>_pointwise_projection[where D'=\<open>{x}\<close> and D=\<open>{Some v}\<close>, simplified],
      assumption)

lemma setter_rule:
  \<open> refinement_projection I {v'} \<subseteq> UNIV * {Some v}
\<Longrightarrow> Id_on UNIV * {(Some v, u)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(v', u')} \<w>.\<r>.\<t> I \<i>\<n> {v'}
\<Longrightarrow> \<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> m k = Some v \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (\<lambda>f. f(k := u))
      \<lbrace> 1(k := v') \<Ztypecolon> \<phi> Itself \<longmapsto> 1(k := u') \<Ztypecolon> \<phi> Itself \<rbrace> \<close>
  by (rule "__setter_rule__",
      rule R.setter_valid,
      rule sep_refinement_stepwise[
        OF R.setter_refinement[THEN refinement_frame[where R=UNIV], unfolded Subjection_times]
           refinement_subjection[OF \<F>_pointwise_refinement]
           \<F>_pointwise_projection,
         where D'1=\<open>{v'}\<close> and B4=\<open>{(v',u')}\<close>, simplified],
      assumption,
      assumption,
      assumption)

lemma
  \<open> \<forall>k. P k \<longrightarrow> 1(k := u) \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<forall>r. r \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_allocate_res_entry' P u \<lbrace> Void \<longmapsto> \<lambda>ret. 1(k := u') \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> k. ret = \<phi>arg k \<and> P k \<rbrace> \<close>
  apply (rule "__allocator_rule__",
      rule R.allocator_valid,
      assumption,
      assumption)
thm R.allocator_refinement
thm "__allocator_rule__"

end

subsubsection \<open>pointwise_fiction_for_two_level_partial_mapping_resource\<close>

locale pointwise_fiction_for_two_level_partial_mapping_resource =
   R: partial_map_resource2 Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_pointwise (\<F>_pointwise I)\<close>
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::discrete_semigroup option) resource_entry"
and I :: \<open>('fic::sep_algebra, 'val option) interp\<close>
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'fic) fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_pointwise (\<F>_pointwise I)\<close> ..

lemma getter_rule:
  \<open> refinement_projection I {x} \<subseteq> UNIV * {Some v}
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k k2 \<lbrace> 1(k := 1(k2 := x)) \<Ztypecolon> \<phi> Itself \<longmapsto>
                                    \<lambda>ret. 1(k := 1(k2 := x)) \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
  by (rule "__getter_rule__",
      rule R.getter_valid,
      rule sep_refinement_stepwise,
      rule R.getter_refinement[THEN refinement_frame[where R=UNIV]],
      unfold Subjection_Id_on Subjection_times,
      rule refinement_subjection[OF constant_refinement],
      rule \<F>_pointwise_projection[where D'=\<open>{1(k2 := x)}\<close> and D=\<open>{1(k2 \<mapsto> v)}\<close>, simplified],
      rule \<F>_pointwise_projection[where D'=\<open>{x}\<close> and D=\<open>{Some v}\<close>, simplified],
      assumption)

lemma setter_rule:
  \<open> refinement_projection I {v'} \<subseteq> UNIV * {Some v}
\<Longrightarrow> Id_on UNIV * {(Some v, u)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(v', u')} \<w>.\<r>.\<t> I \<i>\<n> {v'}
\<Longrightarrow> \<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> m k k2 = Some v \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at (map_fun_at (\<lambda>_. u) k2) k)
      \<lbrace> 1(k := 1(k2 := v')) \<Ztypecolon> \<phi> Itself \<longmapsto> 1(k := 1(k2 := u')) \<Ztypecolon> \<phi> Itself \<rbrace> \<close>
  by (rule "__setter_rule__",
      rule R.setter_valid,
      rule sep_refinement_stepwise[
        OF R.setter_refinement[THEN refinement_frame[where R=UNIV], unfolded Subjection_times]
           refinement_subjection[OF \<F>_pointwise_refinement[OF \<F>_pointwise_refinement]]
           \<F>_pointwise_projection[OF \<F>_pointwise_projection],
        where D'2=\<open>{v'}\<close> and B6=\<open>{(v',u')}\<close>, simplified],
      assumption,
      assumption,
      assumption)

end






print_locale share_fiction_for_partial_mapping_resource


locale share_fiction_for_partial_mapping_resource' =
   pointwise_fiction_for_partial_mapping_resource Res \<open>\<F>_functional to_share\<close> Fic
for Res :: "('key \<Rightarrow> 'val::discrete_semigroup option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val share option) fiction_entry"
begin


end






term \<open>(o) f\<close>

term \<open>(;\<^sub>\<I>) I\<close>

lemma
  \<open>Id_on UNIV * Id_on {u} \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on {f u} \<w>.\<r>.\<t> I \<i>\<n> {f u}\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Id_on_iff set_mult_expn Subjection_expn; blast)




end