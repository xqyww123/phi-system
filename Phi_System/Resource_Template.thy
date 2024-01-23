theory Resource_Template
  imports PhiSem_Formalization_Tools2 Phi_Semantics_Framework.Phi_SemFrame_ex
begin


chapter \<open>Resource Bases and Templates\<close>

section \<open>Preliminary\<close>

interpretation to_share: cancl_share_orthogonal_homo \<open>to_share::'a::{discrete_semigroup, sep_carrier} option \<Rightarrow> 'a share option\<close>
                                                     \<open>Collect mul_carrier\<close> ..

interpretation pointwise_to_share:
  cancl_share_orthogonal_homo \<open>(o) (to_share::'a::{discrete_semigroup, sep_carrier} option \<Rightarrow> 'a share option)\<close>
                              \<open>pointwise_set (Collect mul_carrier)\<close>
  by (standard; standard)

section \<open>Bases\<close>

subsection \<open>Resource Base\<close>

locale resource =
  resource_kind RES.DOMAIN Res
  for Res :: "'T::sep_algebra resource_entry"
begin

lemma get_res_valid_raw: (*TODO: depreciated?*)
  \<open> res \<in> RES.SPACE
\<Longrightarrow> get res \<in>\<^sub>S\<^sub>H domain\<close>
  unfolding RES.SPACE_def
  by (simp, metis in_DOMAIN proj_inj)

definition [simp]: \<open>basic_fiction x = { 1(Res #= x) }\<close>

lemma basic_fiction_homo_one[simp]:
  \<open>homo_one basic_fiction\<close>
  unfolding homo_one_def basic_fiction_def by (simp add: set_eq_iff)

subsubsection \<open>Getter\<close>

definition \<phi>R_get_res' :: \<open>'T proc\<close> \<comment> \<open>use this\<close>
  where \<open>\<phi>R_get_res' = (\<lambda>res. Return (\<phi>arg (get res)) res)\<close>

lemma \<phi>R_get_res'_valid:
  \<open>Valid_Proc \<phi>R_get_res'\<close>
  unfolding Valid_Proc_def \<phi>R_get_res'_def Return_def det_lift_def
  by simp

lemma \<phi>R_get_res_transition:
  \<open> Transition_of' \<phi>R_get_res' ret = Id_on {s. s \<in> SPACE \<and> ret = Normal (\<phi>arg (get s))}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff; blast)

subsubsection \<open>Setter\<close>

definition \<phi>R_set_res' :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> unit proc\<close>
  where \<open>\<phi>R_set_res' F = (\<lambda>res. if updt F res \<in> SPACE
                                then {Success (\<phi>arg ()) (updt F res)}
                                else {Invalid})\<close>


lemma setter_transition:
  \<open> Transition_of' (\<phi>R_set_res' F) ret
 \<subseteq> {(x,y). x \<in> SPACE \<and> get x \<in>\<^sub>S\<^sub>H domain
            \<and> (if F (get x) \<in>\<^sub>S\<^sub>H domain
               then y = updt F x \<and> ret = Normal \<phi>V_none
               else y = x \<and> ret = Crash)}\<close>
  unfolding Transition_of'_def \<phi>R_set_res'_def
  apply (cases ret; auto simp add: set_eq_iff \<phi>V_none_def if_split_mem2)
  using get_res_valid_raw apply fastforce
  using get_res_valid_raw apply fastforce
  apply (metis \<r>_valid_split fun_upd_same fun_upd_upd)
  using get_res_valid_raw by presburger
  

lemma setter_valid:
  \<open>Valid_Proc (\<phi>R_set_res' F)\<close>
  unfolding Valid_Proc_def \<phi>R_set_res'_def bind_def Return_def det_lift_def
  by (clarsimp split: option.split)



end


subsection \<open>Fiction Base\<close>

\<phi>reasoner_group Resource_Space = (100, [0,9999]) \<open>derived reasoning rules for Resource_Space\<close>

locale basic_fiction =
   R: resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> I\<close>
+  homo_one \<open>I\<close>
for Res :: "'T::sep_algebra resource_entry"
and I :: "('U::sep_algebra, 'T) interp"
and Fic :: "'U fiction_entry"
begin

subsubsection \<open>\<phi>-Type\<close>

declare [[collect_reasoner_statistics Resource_Space start,
          \<phi>LPR_collect_statistics derivation start]]

\<phi>type_def \<phi> :: \<open>('U, 'x) \<phi> \<Rightarrow> (fiction, 'x) \<phi>\<close>
  where \<open>\<phi> T \<equiv> mk \<Zcomp>\<^sub>f T\<close>
  deriving Sep_Functor_1
       and \<open>Gen_Br_Join \<phi> \<phi> \<phi> P True\<close>

declare \<phi>.\<S>\<^sub>E[where g=\<open>\<lambda>x. x\<close> and f=\<open>\<lambda>s _ _. s\<close>, unfolded Ball_def, simplified, \<phi>reason add]
        \<phi>.\<S>\<^sub>I[\<phi>reason add]
        \<phi>.\<Sigma>\<^sub>I[where c=fst, simplified, \<phi>reason add]
        \<phi>.\<Sigma>\<^sub>E[\<phi>reason add]
        \<phi>.\<phi>Sum\<^sub>E[\<phi>reason add]
        \<phi>.\<phi>Sum\<^sub>I[\<phi>reason add]

declare \<phi>.\<phi>Sum.rewr[assertion_simps]

declare [[collect_reasoner_statistics Resource_Space stop,
          \<phi>LPR_collect_statistics derivation stop]]

ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %Resource_Space})) "derivation"\<close>

lemma \<phi>_unit:
  \<open>(1 \<Ztypecolon> \<phi> Itself) = Void\<close>
  by (clarsimp simp add: BI_eq_iff)

paragraph \<open>Short-cut of ToA\<close>

\<phi>reasoner_group \<phi>_ToA = (1100, [1100, 1120]) in ToA_cut
  \<open>Short-cut transformations for fiction injector\<close>
                        (*v TODO*)
lemma NToA_skip [\<phi>reason 1100 except \<open> _ \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x \<Ztypecolon> \<phi> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> ]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R'\<heavy_comma> X \<w>\<i>\<t>\<h> P"
  unfolding Action_Tag_def split_paired_All Action_Tag_def
  by (simp, metis ab_semigroup_mult_class.mult_ac(1) transformation_left_frame mult.commute)

paragraph \<open>Synthesis\<close>

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (\<phi> ?T) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (\<phi> T) (\<lambda>_. x \<Ztypecolon> \<phi> T :: assn)\<close>
  unfolding Synthesis_Parse_def ..


subsubsection \<open>Fictional Refinement\<close>

context begin

private lemma sat_sing_eq[simp]: \<open>u \<Turnstile> {v} \<longleftrightarrow> u = v\<close>
          unfolding Satisfaction_def by simp

private lemma from_fictional_refinement':
  \<open> Valid_Proc f
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> Rel v \<w>.\<r>.\<t> R.basic_fiction \<Zcomp>\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition Rel
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>v. y \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Normal v) \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. y \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Abnm e))\<close>
  unfolding \<phi>Procedure_alt Fictional_Forward_Simulation_def atomize_all Valid_Transition_def
  
  apply (auto simp add: Image_iff subset_iff Bex_def
          INTERP_SPEC_subj INTERP_SPEC_ex set_mult_expn INTERP_SPEC
          Subjection_expn_set ExSet_expn_set Transition_of'_def
          LooseState_def split_sum_all INTERP_RES_def interp_split R.\<r>_valid_split'
          R.inj.sep_orthogonal inj.sep_orthogonal prj.homo_mult eval_stat_forall
          split: eval_stat.split)
  subgoal premises prems for r u y v y' rr
    thm prems
    thm prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
  proof -
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
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
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
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
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> Rel v \<w>.\<r>.\<t> R.basic_fiction \<Zcomp>\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition Rel
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE\<close>
  using from_fictional_refinement' by blast

declare sat_sing_eq[simp del]

end

lemma "__getter_rule__":
  \<open> Valid_Proc getter
\<Longrightarrow> (\<And>ret. Transition_of' getter ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({x} \<s>\<u>\<b>\<j> v. ret = Normal (\<phi>arg v) \<and> P v) \<w>.\<r>.\<t> R.basic_fiction \<Zcomp>\<^sub>\<I> I \<i>\<n> {x})
\<Longrightarrow> \<p>\<r>\<o>\<c> getter \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>ret. x \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> v. ret = \<phi>arg v \<and> P v \<rbrace>\<close>
  by (rule from_fictional_refinement[where Rel = \<open>\<lambda>ret. Id_on ({x} \<s>\<u>\<b>\<j> v. ret = Normal (\<phi>arg v) \<and> P v)\<close>
                                       and D = \<open>{x}\<close>],
     assumption,
     clarsimp simp add: set_eq_iff Subjection_expn_set Id_on_iff ExSet_expn_set fun_eq_iff,
     simp add: Id_on_iff zero_set_def zero_fun_def,
     assumption,
     simp add: Valid_Transition_def zero_set_def,
     simp)

lemma "__setter_rule__":
  \<open> Valid_Proc setter
\<Longrightarrow> (\<And>ret. Transition_of' setter ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(x,y)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none
            \<w>.\<r>.\<t> R.basic_fiction \<Zcomp>\<^sub>\<I> I \<i>\<n> {x})
\<Longrightarrow> \<p>\<r>\<o>\<c> setter \<lbrace> x \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>_. y \<Ztypecolon> \<phi> Itself\<rbrace>\<close>
  by (rule from_fictional_refinement
                  [where Rel=\<open>\<lambda>ret. {(x,y)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none\<close> and D = \<open>{x}\<close>],
      assumption,
      clarsimp simp add: set_eq_iff Id_on_iff \<phi>arg_All fun_eq_iff \<phi>V_none_def,
      simp add: Id_on_iff zero_set_def zero_fun_def,
      assumption,
      simp add: Valid_Transition_def zero_set_def,
      simp)

lemma "__allocator_rule__":
  \<open> Valid_Proc allocator
\<Longrightarrow> (\<And>ret. Transition_of' allocator ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1,y k)} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k
            \<w>.\<r>.\<t> R.basic_fiction \<Zcomp>\<^sub>\<I> I \<i>\<n> {1})
\<Longrightarrow> \<p>\<r>\<o>\<c> allocator \<lbrace> Void \<longmapsto> \<lambda>ret. y k \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> k. ret = \<phi>arg k \<and> P k \<rbrace>\<close>
  by (rule from_fictional_refinement
        [where Rel=\<open>\<lambda>ret. {(1,y k)} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k\<close>
           and x=\<open>1\<close> and D=\<open>{1}\<close>, unfolded \<phi>_unit],
      assumption,
      clarsimp simp add: set_eq_iff Subjection_expn_set Id_on_iff \<phi>arg_All fun_eq_iff \<phi>V_none_def,
      simp add: Id_on_iff zero_set_def zero_fun_def,
      assumption,
      simp add: Valid_Transition_def zero_set_def,
      simp)

end

(*
subsubsection \<open>Permission Fiction\<close>

locale permission_fiction =
   R: resource Res
+  share: share_orthogonal_homo \<psi>
+  fiction_kind FIC.DOMAIN INTERPRET Fic
      \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> (\<F>_functional \<psi>)\<close>
for Res :: "'T::sep_algebra resource_entry"
and \<psi> :: \<open>'T \<Rightarrow> 'U::{share_sep_disj,share_semimodule,sep_algebra}\<close>
and Fic :: "'U fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_functional \<psi>\<close> ..


paragraph \<open>Reasoning Rules\<close>

declare NToA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare NToA_by_structural_extraction__reverse_transformation
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end
*)



(*
subsubsection \<open>Itself Fiction\<close>

locale identity_fiction =
   R: resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_it\<close>
for Res :: "'T::sep_algebra resource_entry"
and Fic :: "'T fiction_entry"
begin

sublocale basic_fiction where I = \<open>\<F>_it\<close> ..

declare NToA_by_structural_extraction
   [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare NToA_by_structural_extraction__reverse_transformation
   [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end
*)




section \<open>Non-separable Monolithic Resource\<close>
  \<comment> \<open>The resource non-sepable and having type shape \<^typ>\<open>'a::discrete_semigroup option\<close>\<close>

locale discrete_mono_resource =
  resource Res
for Res :: "'T discrete option resource_entry"
begin

(* abbreviation fiction_agree
  where \<open>fiction_agree \<equiv> basic_fiction \<Zcomp>\<^sub>\<I> \<F>_optionwise \<F>_agree\<close> *)

end


subsubsection \<open>Interp Agreement\<close>

(*TODO: ('k \<Rightarrow> 'v) discrete option ----> ('k \<Rightarrow> 'v share option)
  total to that
  none to none
 *)

(*TODO!*)
(*
locale agreement_fiction_for_discrete_mono_resource =
   R: discrete_mono_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.fiction_agree\<close>
for Res :: "'T discrete option resource_entry"
and Fic :: "'T discrete agree option fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_optionwise \<F>_agree\<close> Fic
  by (standard; simp add: raw_domain)

lemma double:
  \<open>{mk x |x. P x} \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {mk x |x. P x} * {mk x |x. P x}\<close>
  unfolding Transformation_def
  apply (clarsimp simp add: \<phi>expns mk_homo_mult[symmetric])
  subgoal for x'
    apply (rule exI[where x=\<open>mk x'\<close>], rule exI[where x=\<open>mk x'\<close>])
    by (cases x'; simp add: mk_homo_mult[symmetric]) .

lemma contract:
  \<open>{mk x |x. P x} * {mk x |x. P x} \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> {mk x |x. P x} \<close>
  unfolding Transformation_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for x y by (cases x; cases y; simp add: mk_homo_mult[symmetric]) .

paragraph \<open>\<phi>-Type\<close>

abbreviation \<open>\<phi>_ag T \<equiv> \<phi> (Agreement (Discrete T))\<close>

(*
declare NToA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare NToA_by_structural_extraction__reverse_transformation
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
*)

lemma \<phi>_double_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (discrete v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: double)
qed

lemma \<phi>_contract_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (discrete v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: contract)
qed

end
*)


section \<open>Mapping Resources\<close>

text \<open>Resources based on mapping\<close>

locale mapping_resource =
  resource Res
for Res :: "('key \<Rightarrow> 'val::sep_algebra) resource_entry"
begin

definition
    \<phi>R_allocate_res_entry' :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> 'key proc\<close>
  where \<open>\<phi>R_allocate_res_entry' P init =
    \<phi>R_get_res' \<bind> (\<lambda>res.
    let k = (@k. \<phi>arg.dest res k = 1 \<and> P k)
     in \<phi>R_set_res' (\<lambda>f. f(k := init))
        \<ggreater> Return (\<phi>arg k)
)\<close>

lemma allocator_transition:
  \<open> (\<forall>r. r \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k))
\<Longrightarrow> \<forall>k. P k \<longrightarrow> 1(k := init) \<in>\<^sub>S\<^sub>H domain
\<Longrightarrow> Transition_of' (\<phi>R_allocate_res_entry' P init) ret
        \<subseteq> (Id_on SPACE * {(1, mk (1(k := init))) | k. ret = Normal (\<phi>arg k) \<and> P k})\<close>
  unfolding Transition_of'_def \<phi>R_allocate_res_entry'_def \<phi>R_get_res'_def bind_def Return_def
      det_lift_def \<phi>R_set_res'_def Let_def
  apply (cases ret; clarsimp simp add: zero_set_def set_eq_iff set_mult_expn Subjection_expn Id_on_iff)
  apply (case_tac x; clarsimp simp add: zero_set_def set_eq_iff set_mult_expn Subjection_expn Id_on_iff)
  subgoal premises prems for r b x 
  proof -
    have t1: \<open>get r \<in>\<^sub>S\<^sub>H domain\<close>
      by (simp add: get_res_valid_raw prems(4))
    let ?kk = \<open>SOME k. get r k = 1 \<and> P k\<close>
    have t2: \<open>\<exists>k. get r k = 1 \<and> P k\<close>
      using dom1_def prems(1) t1 by fastforce
    have t3[simp]: \<open>get r ?kk = 1 \<and> P ?kk\<close>
      by (insert t2; clarify; rule someI[where P=\<open>\<lambda>k. get r k = 1 \<and> P k\<close>]; blast)
    have t4 [simp]: \<open>(get r)(?kk := init) = get r * 1(?kk := init)\<close>
      by (simp add: fun_eq_iff)
    have t5[simp]: \<open>get r ## 1(?kk := init)\<close>
      by (metis (mono_tags, lifting) fun_sep_disj_1_fupdt(2) fun_upd_triv sep_disj_commuteI sep_magma_1_left t3)
    have t6[simp]: \<open>r(name := inject ((get r)(?kk := init))) \<in> SPACE\<close>
      by (metis comp.simps(6) empty_iff insert_iff prems(5))
    have t61[simp]: \<open>r(name := inject (get r * 1(?kk := init))) \<in> SPACE\<close>
      using t6 by auto
    have t7[simp]: \<open>b = r(name := inject ((get r)(?kk := init)))\<close>
      using prems[simplified] t4 by presburger 
    show ?thesis
      by (simp add: fun_eq_iff inj.homo_mult prems,
          metis (no_types, lifting) fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo_semi inj_prj_in_SPACE prems(4) t5)
  qed
  subgoal premises prems for r proof -
    let ?kk = \<open>SOME k. get r k = 1 \<and> P k\<close>
    have t1: \<open>get r \<in>\<^sub>S\<^sub>H domain\<close>
      by (simp add: get_res_valid_raw prems(5))
    have t2: \<open>\<exists>k. get r k = 1 \<and> P k\<close>
      using dom1_def prems(1) t1 by fastforce
    have t3[simp]: \<open>get r ?kk = 1 \<and> P ?kk\<close>
      by (insert t2; clarify; rule someI[where P=\<open>\<lambda>k. get r k = 1 \<and> P k\<close>]; blast)
    have t4 [simp]: \<open>(get r)(?kk := init) = get r * 1(?kk := init)\<close>
      by (simp add: fun_eq_iff)
    have t5[simp]: \<open>get r ## 1(?kk := init)\<close>
      by (metis (mono_tags, lifting) fun_sep_disj_1_fupdt(2) fun_upd_triv sep_disj_commuteI sep_magma_1_left t3)
    have t7: \<open>r(name := inject ((get r)(?kk := init))) \<in> SPACE\<close>
      by (metis (no_types, lifting) \<r>_valid_split fun_upd_same fun_upd_upd mult_in_sep_homo_set prems(2) prems(5) t1 t3 t4 t5)
    show ?thesis
      using prems(4) t7 by blast
   qed .

lemma allocator_refinement:
  \<open> \<forall>r. r \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k)
\<Longrightarrow> \<forall>k. P k \<longrightarrow> 1(k := init) \<in>\<^sub>S\<^sub>H domain
\<Longrightarrow> Transition_of' (\<phi>R_allocate_res_entry' P init) ret
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1, 1(k := init))} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k
   \<w>.\<r>.\<t> basic_fiction \<i>\<n> {1}\<close>
  apply (rule refinement_sub_fun[OF allocator_transition], assumption, assumption)
  unfolding Fictional_Forward_Simulation_def
  apply (cases ret; clarsimp simp add: set_mult_expn Subjection_expn_set mk_homo_mult)
  subgoal premises prems for r R u k
  proof -
    have [simp]: \<open>r ## 1(k := init)\<close>
      using prems(5) prems(7) sep_disj_multD2 by blast
    show ?thesis
      apply (simp add: mk_homo_mult)
      using mk_homo_mult prems(4) prems(5) prems(7) prems(8) sep_disj_multI2 sep_mult_assoc by fastforce
  qed .

lemma allocator_valid:
  \<open> \<forall>r. r \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k)
\<Longrightarrow> \<forall>k. P k \<longrightarrow> 1(k := init) \<in>\<^sub>S\<^sub>H domain
\<Longrightarrow> Valid_Proc (\<phi>R_allocate_res_entry' P init)\<close>
  unfolding Valid_Proc_def \<phi>R_allocate_res_entry'_def \<phi>R_get_res'_def \<phi>R_set_res'_def
            bind_def Return_def det_lift_def Let_def
  by (clarsimp split: option.split)

end

locale fiction_base_for_mapping_resource =
  R: mapping_resource Res
+ fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> I\<close>
+ homo_one \<open>I\<close>
for Res :: "('key \<Rightarrow> 'val::sep_algebra) resource_entry"
and I   :: "('T::sep_algebra, 'key \<Rightarrow> 'val) interp"
and Fic :: "'T fiction_entry"
begin

sublocale basic_fiction Res I Fic ..

lemma "__allocate_rule_2__":
  \<open> (\<And>k. P k \<Longrightarrow> Id_on UNIV * {(1, 1(k := u))} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1, u' k)} \<w>.\<r>.\<t> I \<i>\<n> {1})
\<Longrightarrow> \<forall>k. P k \<longrightarrow> 1(k := u) \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<forall>r. r \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_allocate_res_entry' P u \<lbrace> Void \<longmapsto> \<lambda>ret. u' k \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> k. ret = \<phi>arg k \<and> P k \<rbrace> \<close>
  by (rule "__allocator_rule__",
      rule R.allocator_valid,
      assumption,
      assumption,
      rule sep_refinement_stepwise[
        OF R.allocator_refinement[THEN refinement_frame[where R=UNIV]]],
      assumption,
      assumption,
      unfold ExSet_times_right Subjection_times,
      rule refinement_ExSet,
      rule refinement_subjection,
      blast,
      auto simp add: set_mult_expn)

end


section \<open>One Level Parital Mapping\<close>

subsection \<open>Preliminary\<close>

definition \<open>map_fun_at k g f = (\<lambda>x. if x = k then g (f x) else f x)\<close>

lemma map_fun_at_1[simp]: \<open>map_fun_at k g 1 = 1(k := g 1)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp

lemma map_fun_at_const[simp]:
  \<open>map_fun_at k (\<lambda>_. u) f = f(k := u)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp


subsection \<open>Resource\<close>

locale partial_map_resource =
  mapping_resource Res
  for Res :: "('key \<Rightarrow> 'val::discrete_semigroup option) resource_entry"
  and P :: \<open>'key \<Rightarrow> 'val::discrete_semigroup set\<close>
+ assumes domain0: \<open>domain = sep_homo_set {h. finite (dom h) \<and> (\<forall>k \<in> dom h. h k \<in> Some ` P k)}\<close>
begin

subsubsection \<open>Getter\<close>

lemma in_invariant:
  \<open>x \<in>\<^sub>S\<^sub>H domain \<longleftrightarrow> x \<in> {h. finite (dom h) \<and> (\<forall>k \<in> dom h. h k \<in> Some ` P k)}\<close>
proof -
  have \<open>Sep_Homo {h. finite (dom h) \<and> (\<forall>k\<in>dom h. h k \<in> Some ` P k)}\<close>
    proof -
      have t2: \<open> {h. finite (dom h) \<and> (\<forall>k\<in>dom h. h k \<in> Some ` P k)} = {h. finite (dom h)} \<inter> {h. (\<forall>k\<in>dom h. h k \<in> Some ` P k)} \<close>
        by (auto simp add: set_eq_iff)
      have t3: \<open>(\<forall>k\<in>dom h. P k) = (\<forall>k. h k \<noteq> None \<longrightarrow> P k)\<close> for h P
        by auto
      show ?thesis
        by (subst t2, rule Sep_Homo_inter, simp, subst t3, rule Sep_Homo_pointwise, auto)
    qed
  then show ?thesis
    by (simp add: domain0)
qed

definition \<phi>R_get_res_entry' :: \<open>'key \<Rightarrow> 'val proc\<close>
  where \<open>\<phi>R_get_res_entry' k =
    \<phi>R_get_res' \<bind> (\<lambda>res. case \<phi>arg.dest res k of Some v \<Rightarrow> Return (\<phi>arg v) | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma getter_transition:
  \<open> Transition_of' (\<phi>R_get_res_entry' k) ret
        = Id_on {s. s \<in> SPACE \<and> ret = (case get s k of Some v \<Rightarrow> Normal (\<phi>arg v) | _ \<Rightarrow> Crash)}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def \<phi>R_get_res_entry'_def bind_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff split: option.split; blast)

lemma getter_refinement:
  \<open>Transition_of' (\<phi>R_get_res_entry' k) ret
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({1(k \<mapsto> u)} \<s>\<u>\<b>\<j> u. ret = Normal (\<phi>arg u) \<and> u \<in> P k \<and> u \<in> S)
   \<w>.\<r>.\<t> basic_fiction \<i>\<n> fun_upd 1 k ` Some ` S\<close>
  unfolding Fictional_Forward_Simulation_def getter_transition
  apply (cases ret; clarsimp split: option.split simp add: set_mult_expn Id_on_iff
                              Subjection_expn_set prj.homo_mult times_fun set_eq_iff \<r>_valid_split'
                              inj.sep_orthogonal[simplified] in_invariant)
  by (smt (verit, ccfv_threshold) domI fun_upd_same image_iff mult_1_class.mult_1_left one_option_def option.sel sep_disj_fun_discrete(2) times_fun)
 

lemma getter_valid:
  \<open>Valid_Proc (\<phi>R_get_res_entry' k)\<close>
  unfolding Valid_Proc_def \<phi>R_get_res_entry'_def \<phi>R_get_res'_def bind_def Return_def det_lift_def
  by (clarsimp split: option.split)



subsubsection \<open>Setter\<close>

lemma setter_refinement:
  \<open>(\<And>v. v \<in> S \<and> v \<in> P k \<Longrightarrow> pred_option (\<lambda>x. x \<in> P k) (F v))
\<Longrightarrow> Transition_of' (\<phi>R_set_res' (map_fun_at k (F o the))) ret
  \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` {(Some v, F v)} \<s>\<u>\<b>\<j> v. ret = Normal \<phi>V_none \<and> v \<in> S \<and> v \<in> P k
  \<w>.\<r>.\<t> basic_fiction
  \<i>\<n> fun_upd 1 k ` Some ` S\<close>

  apply (rule refinement_sub_fun[OF setter_transition[where F=\<open>map_fun_at k (F o the)\<close>]])
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: set_mult_expn Subjection_expn_set ExSet_expn_set
            prj.homo_mult \<r>_valid_split' inj.sep_orthogonal[simplified])
  subgoal premises prems for r R x' u v
  proof -
    have x1: \<open>r ## 1(k \<mapsto> v)\<close> using prems(4) by blast
    have x2: \<open>get u ## (r * 1(k \<mapsto> v))\<close>
      using prems(7) sep_disj_get_name by blast
    have a1: \<open>k \<in> dom (get u * (r * 1(k \<mapsto> v)))\<close>
      by (simp add: domIff times_fun_def)
    have a3: \<open>get u * (r * 1(k \<mapsto> v)) \<in>\<^sub>S\<^sub>H domain\<close>
      using prems(2) prems(3) by fastforce
    then have \<open>1(k \<mapsto> v) \<in>\<^sub>S\<^sub>H domain\<close>
      using mult_in_sep_homo_set x1 x2 by blast
    then have a2: \<open>v \<in> P k\<close>
      by (clarsimp simp add: in_invariant Ball_def times_fun)
    have q3: \<open>map_fun_at k (F \<circ> the) (get u * (r * 1(k \<mapsto> v))) = get u * (r * 1(k := F v))\<close>
      apply (clarsimp simp add: fun_eq_iff map_fun_at_def times_fun)
      by (metis (mono_tags, lifting) dom_1 dom_eq_empty_conv fun_upd_same mult_1_class.mult_1_left option.sel sep_disj_fun sep_disj_option_discrete(1) times_fupdt_1_apply_sep x1 x2)
    have q4: \<open>1(k := F v) \<in>\<^sub>S\<^sub>H domain\<close>
      apply (clarsimp simp add: in_invariant)
      using a2 prems(1) prems(5) by fastforce
    have x3: \<open>map_fun_at k (F \<circ> the) (get u * (r * 1(k \<mapsto> v))) \<in>\<^sub>S\<^sub>H domain\<close>
      unfolding q3
      by (metis a3 mult_in_sep_homo_set discrete_semigroup_sepdisj_fun q4 sep_disj_multD1 sep_disj_multI1 sep_disj_multI2 x1 x2) 
    have x5: \<open>w ## r * 1(k \<mapsto> v) \<Longrightarrow>
                  map_fun_at k (F \<circ> the) (w * (r * 1(k \<mapsto> v))) = w * (r * (1(k := F v)))\<close> for w
          unfolding map_fun_at_def apply (clarsimp simp add: fun_eq_iff times_fun)
          by (metis (mono_tags, opaque_lifting) map_upd_Some_unfold option.sel sep_disj_fun_def sep_disj_option_discrete(1) times_fupdt_1_apply_sep times_option(3) x1)
    show ?thesis
      apply (insert prems, clarsimp simp add: x3 times_fun_upd x5, simp add: mk_homo_mult)
      subgoal premises prems for w
      proof -
        have x4: \<open>r ## 1(k := F v)\<close>
          by (meson discrete_semigroup_sepdisj_fun x1)
        have x4': \<open>w ## 1(k := F v)\<close>
          by (meson discrete_semigroup_sepdisj_fun prems(10) sep_disj_commuteI sep_disj_multD2 x1)
        have x6: \<open>w ## (r * 1(k := F v))\<close>
          by (meson discrete_semigroup_sepdisj_fun prems(10) sep_disj_multD1 sep_disj_multI1 sep_disj_multI2 x1)
        have x6': \<open>r ## (w * 1(k := F v))\<close>
          by (metis sep_disj_commute sep_disj_multI2 sep_mult_commute x4 x4' x6)
        have x7: \<open>clean u * mk w = u\<close>
          by (metis fun_split_1 prems(9))
        show ?thesis
          apply (insert prems, clarsimp simp add: x4 x4' x6 x6' mk_homo_mult)
          by (metis (no_types, lifting) a2 fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1) inj.homo_mult inj.sep_disj_homo_semi mult_1_class.mult_1_left prems(7) x4 x6 x7)
      qed .
  qed .

end


subsection \<open>Pointwise Base Fiction\<close>

locale pointwise_base_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res RP
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise I\<close>
+  homo_one \<open>\<F>_pointwise I\<close>
for Res :: "('key \<Rightarrow> 'val::discrete_semigroup option) resource_entry"
and I :: \<open>'key \<Rightarrow> ('fic::sep_algebra, 'val option) interp\<close>
and Fic :: "('key \<Rightarrow> 'fic) fiction_entry"
and RP :: \<open>'key \<Rightarrow> 'val set\<close>
begin

sublocale fiction_base_for_mapping_resource Res \<open>\<F>_pointwise I\<close> Fic ..

lemmas "__allocate_rule_3__" =
  "__allocate_rule_2__"[OF \<F>_pointwise_refinement[where A=\<open>{(1,u)}\<close> and B=\<open>{(1,u')}\<close> and D=\<open>{1}\<close> for u u', simplified]]

lemma "_getter_rule_2_":
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> refinement_projection (I k) {x} \<subseteq> UNIV * Some ` S
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k \<lbrace> 1(k' := x) \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>ret. 1(k' := x) \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> v. ret = \<phi>arg v \<and> v \<in> RP k' \<and> v \<in> S \<rbrace>\<close>
  unfolding Premise_def
subgoal premises prems
proof -
  have t1: \<open>{Some u |u. u \<in> S} = Some ` S\<close>
    unfolding set_eq_iff by (clarsimp simp add: image_iff; blast)

  show ?thesis
    by (unfold prems(1),
      insert prems(2-),
      rule "__getter_rule__",
      rule R.getter_valid,
      rule sep_refinement_stepwise,
      rule R.getter_refinement[where S=S, THEN refinement_frame[where R=UNIV]],
      unfold Subjection_Id_on Subjection_times ExSet_Id_on ExSet_times_right,
      rule refinement_existential[OF refinement_subjection[OF constant_refinement]],
      simp,
      rule \<F>_pointwise_projection[where D'=\<open>{x}\<close> and D=\<open>Some ` S\<close>, simplified],
      assumption)
qed .

lemma "_setter_rule_2_":
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> (Id_on UNIV * ({(Some v, f v)} \<s>\<u>\<b>\<j> v. v \<in> V \<and> v \<in> RP k) \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(v', F v')} \<w>.\<r>.\<t> I k \<i>\<n> {v'})
\<Longrightarrow> refinement_projection (I k) {v'} \<subseteq> UNIV * Some ` V
\<Longrightarrow> (\<And>v. v \<in> V \<and> v \<in> RP k \<Longrightarrow> pred_option (\<lambda>x. x \<in> RP k) (f v))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at k (f o the))
      \<lbrace> 1(k' := v') \<Ztypecolon> \<phi> Itself \<longmapsto> 1(k' := F v') \<Ztypecolon> \<phi> Itself \<rbrace> \<close>
  unfolding Premise_def
subgoal premises prems proof -
  have t1: \<open>Id_on UNIV * (pairself (fun_upd 1 k) ` {(Some v, f v)} \<s>\<u>\<b>\<j> v. ret = Normal \<phi>V_none \<and> v \<in> V \<and> v \<in> RP k)
         = (Id_on UNIV * (pairself (fun_upd 1 k) ` ({(Some v, f v)} \<s>\<u>\<b>\<j> v. v \<in> V \<and> v \<in> RP k )) \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none)\<close>
    for ret
    by (unfold Subjection_Id_on Subjection_times ExSet_Id_on ExSet_times_right ExSet_image
                  Subjection_image; simp add: set_eq_iff Subjection_expn_set ExSet_expn_set; blast)
  show ?thesis
    by (unfold prems(1),
      insert prems(2-),
      rule "__setter_rule__",
      rule R.setter_valid,
      rule sep_refinement_stepwise,
      rule R.setter_refinement[THEN refinement_frame[where R=UNIV], unfolded Subjection_times],
      assumption,
      unfold t1,
      rule refinement_subjection[OF \<F>_pointwise_refinement[where B=\<open>{(v', F v')}\<close> and D=\<open>{v'}\<close>, simplified]],
      assumption,
      simp,
      rule \<F>_pointwise_projection[where D'=\<open>{v'}\<close>, simplified],
      assumption)
qed .

end


subsection \<open>Pointwise Fiction\<close>

locale pointwise_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res P
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>_. \<F>_it)\<close>
+  homo_one \<open>\<F>_pointwise (\<lambda>_::'key. \<F>_it::'val discrete option \<Rightarrow> 'val discrete option set)\<close>
for Res :: "('key \<Rightarrow> 'val discrete option) resource_entry"
and P   :: \<open>'key \<Rightarrow> 'val discrete set\<close>
and Fic :: "('key \<Rightarrow> 'val discrete option) fiction_entry"
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource Res \<open>\<lambda>_. \<F>_it\<close> Fic P ..

lemma setter_rule:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> v \<in> P k \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> pred_option (\<lambda>x. x \<in> P k) u)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at k (\<lambda>_. u)) \<lbrace> 1(k' \<mapsto> v) \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>\<r>\<e>\<t>. 1(k' := u) \<Ztypecolon> \<phi> Itself \<rbrace>  \<close>
  unfolding Premise_def
subgoal premises prems
proof -
  have [simp]: \<open>(\<lambda>_. u) \<circ> the = (\<lambda>_. u)\<close> for u by auto
  show ?thesis
    by (unfold prems(1),
        rule "_setter_rule_2_"[where k=k and k'=k and f=\<open>\<lambda>_. u\<close> and F=\<open>\<lambda>_. u'\<close> and V=\<open>{v}\<close> for u u' v,
                simplified, unfolded refinement_source_subjection,
                OF impI,
                OF \<F>_it_refinement
                   \<F>_it_refinement_projection[where S=S and S'=S for S, simplified],
                simplified],
        rule prems)
qed .



lemma getter_rule:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k \<lbrace>
              1(k' \<mapsto> u) \<Ztypecolon> \<phi> Itself \<longmapsto>
        \<lambda>ret. 1(k' \<mapsto> u) \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> ret = \<phi>arg u \<and> u \<in> P k'
      \<rbrace> \<close>
  thm "_getter_rule_2_"[where S=\<open>{u}\<close>, simplified singleton_iff, simplified]
  by (rule "_getter_rule_2_"[where S=\<open>{u}\<close> for u, simplified singleton_iff, simplified],
      assumption,
      rule \<F>_it_refinement_projection,
      simp)

lemmas allocate_rule = "__allocate_rule_2__"
                            [OF \<F>_pointwise_refinement[where I=\<open>\<lambda>_. \<F>_it\<close>, OF \<F>_it_refinement, where u2=1, simplified]
                                Premise_D[where mode=default]
                                Premise_D[where mode=default]]

end

subsection \<open>Pointwise Share Fiction\<close>

locale pointwise_share_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res P
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>_. \<F>_functional to_share UNIV)\<close>
+  homo_one \<open>\<F>_pointwise (\<lambda>_. \<F>_functional to_share UNIV)
                :: ('key \<Rightarrow> 'val discrete share option) \<Rightarrow> ('key \<Rightarrow> 'val discrete option) set\<close>
for Res :: "('key \<Rightarrow> 'val discrete option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val discrete share option) fiction_entry"
and P   :: \<open>'key \<Rightarrow> 'val discrete set\<close>
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource Res \<open>\<lambda>_. \<F>_functional to_share UNIV\<close> Fic P ..

context notes mul_carrier_option_def[simp] option.pred_True[simp]
begin

lemma setter_rule:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> v \<in> P k \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> pred_option (\<lambda>x. x \<in> P k) u)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at k (\<lambda>x. u))
      \<lbrace> 1(k' \<mapsto> Share 1 v) \<Ztypecolon> \<phi> Itself \<longmapsto> \<lambda>\<r>\<e>\<t>. 1(k' := to_share u) \<Ztypecolon> \<phi> Itself \<rbrace>  \<close>
  by (rule "_setter_rule_2_"[where k=k and k'=k' and f=\<open>\<lambda>_. u\<close> and F=\<open>\<lambda>_. u'\<close> and V=\<open>{v}\<close> for u' v,
                  simplified, unfolded refinement_source_subjection,
                  OF _ impI,
                  OF _ to_share.\<F>_functional_refinement[where 'a=\<open>'val discrete\<close>, simplified], simplified,
                  OF _ to_share.\<F>_functional_projection[where S=\<open>{Some v}\<close>, simplified]],
      simp,
      simp add: Premise_def)

lemma getter_rule:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> k' = k
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k
      \<lbrace>       1(k' := to_share (Some u)) \<Ztypecolon> \<phi> Itself \<longmapsto>
        \<lambda>ret. 1(k' := to_share (Some u)) \<Ztypecolon> \<phi> Itself \<s>\<u>\<b>\<j> ret = \<phi>arg u \<and> u \<in> P k' \<rbrace> \<close>
  by (rule "_getter_rule_2_"[where S=\<open>{u}\<close> for u, simplified,
                            OF _ to_share.\<F>_functional_projection[where S=\<open>{x}\<close> for x :: \<open>'val discrete option\<close>, simplified]],
      assumption)

lemmas allocate_rule =
  "__allocate_rule_2__"[OF \<F>_pointwise_refinement[where I=\<open>\<lambda>_. \<F>_functional to_share UNIV\<close>,
                                                  OF to_share.\<F>_functional_refinement[where a=\<open>1::'val discrete option\<close>, simplified],
                                                  simplified],
                        where u = \<open>Some u'\<close> for u', simplified]

end

end


(*
section \<open>Two Level Parital Mapping\<close>

subsection \<open>Resource\<close>

locale partial_map_resource2 =
  mapping_resource Res
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::discrete_semigroup option) resource_entry"
begin

subsubsection \<open>Getter\<close>

definition \<phi>R_get_res_entry' :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> 'val proc\<close>
  where \<open>\<phi>R_get_res_entry' k k2 =
    \<phi>R_get_res' \<bind> (\<lambda>res. case \<phi>arg.dest res k k2 of Some v \<Rightarrow> Return (\<phi>arg v) | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

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

subsubsection \<open>Setter\<close>

lemma setter_refinement:
  \<open> \<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m k k2 = Some any \<longrightarrow> map_fun_at k (map_fun_at k2 (\<lambda>_. u)) m \<in>\<^sub>S\<^sub>H domain
\<Longrightarrow> Transition_of' (\<phi>R_set_res' (map_fun_at k (map_fun_at k2 (\<lambda>_. u)))) ret
\<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` pairself (fun_upd 1 k2) ` {(Some any, u)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none
\<w>.\<r>.\<t> basic_fiction \<i>\<n> (fun_upd 1 k) ` (fun_upd 1 k2) ` {Some any}\<close>
  apply (rule refinement_sub_fun[OF setter_transition[where F=\<open>map_fun_at k (map_fun_at k2 (\<lambda>_. u))\<close>]], assumption)
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
    have t4[simp]: \<open>x' = clean u' * mk (map_fun_at k (map_fun_at k2 (\<lambda>_. u)) (r * (a * 1(k := 1(k2 \<mapsto> any))))) \<and> ret = Normal \<phi>V_none\<close>
      using prems(3) by fastforce
    have t5[simp]: \<open>r ## 1(k := 1(k2 := u))\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv discrete_semigroup_sepdisj_fun prems(5))
    have t6[simp]: \<open>(r * a) k k2 = None\<close>
      by (metis sep_disj_multI1 sep_disj_option_discrete(1) t1 t2 times_fun)
    then have [simp]:
        \<open>map_fun_at k (map_fun_at k2 (\<lambda>_. u)) (r * (a * 1(k := 1(k2 \<mapsto> any))))
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


subsection \<open>Pointwise Base Fiction\<close>

locale pointwise_base_fiction_for_partial_mapping_resource2 =
   R: partial_map_resource2 Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_pointwise (\<lambda>k1. \<F>_pointwise (I k1))\<close>
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::discrete_semigroup option) resource_entry"
and I :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> ('fic::sep_algebra, 'val option) interp\<close>
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'fic) fiction_entry"
begin

sublocale fiction_base_for_mapping_resource Res \<open>\<F>_pointwise (\<lambda>k1. \<F>_pointwise (I k1))\<close> Fic ..

lemma "_getter_rule_2_":
  \<open> refinement_projection (I k k2) {x} \<subseteq> UNIV * {Some v}
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

lemma "_setter_rule_2_":
  \<open> Id_on UNIV * {(Some v, u)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(v', u')} \<w>.\<r>.\<t> I k k2 \<i>\<n> {v'}
\<Longrightarrow> refinement_projection (I k k2) {v'} \<subseteq> UNIV * {Some v}
\<Longrightarrow> \<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> m k k2 = Some v \<longrightarrow> map_fun_at k (map_fun_at k2 (\<lambda>_. u)) m \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at k (map_fun_at k2 (\<lambda>_. u)))
      \<lbrace> 1(k := 1(k2 := v')) \<Ztypecolon> \<phi> Itself \<longmapsto> 1(k := 1(k2 := u')) \<Ztypecolon> \<phi> Itself \<rbrace> \<close>
  by (rule "__setter_rule__",
      rule R.setter_valid,
      rule sep_refinement_stepwise[
        OF R.setter_refinement[THEN refinement_frame[where R=UNIV], unfolded Subjection_times]
           refinement_subjection[OF \<F>_pointwise_refinement[where I=\<open>(\<lambda>k1. \<F>_pointwise (\<lambda>k2. I k1 k2))\<close>,
                                          OF \<F>_pointwise_refinement[where I=\<open>I k\<close> and k=k2]]]
           \<F>_pointwise_projection[where I=\<open>(\<lambda>k1. \<F>_pointwise (\<lambda>k2. I k1 k2))\<close>,
                           OF \<F>_pointwise_projection[where I=\<open>I k\<close> and k=k2]],
           where D'2=\<open>{v'}\<close> and B5=\<open>{(v',u')}\<close>, simplified],
      assumption,
      assumption,
      assumption)

end

subsection \<open>Pointwise Fiction\<close>

locale pointwise_fiction_for_partial_mapping_resource2 =
   R: partial_map_resource2 Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_pointwise (\<lambda>_. \<F>_pointwise (\<lambda>_. \<F>_it))\<close>
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val discrete option) resource_entry"
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val discrete option) fiction_entry"
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource2 Res \<open>\<lambda>_ _. \<F>_it\<close> Fic ..

lemmas setter_rule = "_setter_rule_2_"[OF \<F>_it_refinement \<F>_it_refinement_projection]
lemmas getter_rule = "_getter_rule_2_"[OF \<F>_it_refinement_projection]
lemmas allocate_rule = "__allocate_rule_2__"[unfolded \<F>_pointwise_\<F>_it,
                          OF \<F>_pointwise_refinement[where I=\<open>\<lambda>_. \<F>_it\<close>, OF \<F>_it_refinement, where u2=1, simplified, unfolded \<F>_pointwise_\<F>_it]]


end


subsection \<open>Pointwise Share Fiction\<close>

locale pointwise_share_fiction_for_partial_mapping_resource2 =
   R: partial_map_resource2 Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction ;\<^sub>\<I> \<F>_pointwise (\<lambda>_. \<F>_pointwise (\<lambda>_. \<F>_functional to_share UNIV))\<close>
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val discrete option) resource_entry"
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val discrete share option) fiction_entry"
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource2 Res \<open>\<lambda>_ _. \<F>_functional to_share UNIV\<close> Fic ..

lemmas setter_rule =
  "_setter_rule_2_""_setter_rule_2_"[OF to_share.\<F>_functional_refinement[simplified], simplified,
                                     OF to_share.refinement_projection_half_perm[where S=\<open>{Some v}\<close> and n = 1 for v, simplified]]
lemmas getter_rule =
  "_getter_rule_2_"[OF to_share.\<F>_functional_projection[where S=\<open>{x}\<close> for x, simplified], simplified]

lemmas allocate_rule =
  "__allocate_rule_2__"[OF \<F>_pointwise_refinement[OF pointwise_to_share.\<F>_functional_refinement[where a=\<open>1\<close>, simplified],
        simplified, unfolded \<F>_functional_pointwise[OF to_share.kernel_is_1, unfolded pointwise_set_UNIV]]]
thm \<F>_pointwise_refinement[OF pointwise_to_share.\<F>_functional_refinement[where a=\<open>1\<close>, simplified], simplified, unfolded]
end
*)


end