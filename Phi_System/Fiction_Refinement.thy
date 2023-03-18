theory Fiction_Refinement
  imports PhiSem_Formalization_Tools
  abbrevs "<refines>" = "\<r>\<e>\<f>\<i>\<n>\<e>\<s>"
      and "<w.r.t>" = "\<w>.\<r>.\<t>"
begin











definition Is_Frame_Proc :: \<open>'ret::VALs proc \<Rightarrow> bool\<close>
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
    

definition Transition_of :: \<open>'ret::VALs proc \<Rightarrow> 'ret \<phi>arg + ABNM \<Rightarrow> resource rel\<close>
  where \<open>Transition_of f = (\<lambda>x. case x of Inl v \<Rightarrow> { (s,s'). Success v s' \<in> f s \<and> s \<in> RES.SPACE }
                                        | Inr e \<Rightarrow> { (s,s'). Abnormal e s' \<in> f s \<and> s \<in> RES.SPACE } )\<close>

declare [[typedef_overloaded]]
datatype 'ret eval_stat = Normal \<open>'ret \<phi>arg\<close> | Abnm ABNM | Crash
declare [[typedef_overloaded = false]]

lemma eval_stat_forall:
  \<open>All P \<longleftrightarrow> (\<forall>ret. P (Normal ret)) \<and> (\<forall>e. P (Abnm e)) \<and> P Crash\<close>
  by (metis eval_stat.exhaust)

lemma eval_stat_ex:
  \<open>Ex P \<longleftrightarrow> (\<exists>ret. P (Normal ret)) \<or> (\<exists>e. P (Abnm e)) \<or> P Crash\<close>
  by (metis eval_stat.exhaust)


definition Transition_of' :: \<open>'ret::VALs proc \<Rightarrow> 'ret eval_stat \<Rightarrow> resource rel\<close>
  where \<open>Transition_of' f = (\<lambda>x. (case x of Normal v \<Rightarrow> { (s,s'). Success v s' \<in> f s \<and> s \<in> RES.SPACE }
                                          | Abnm e \<Rightarrow> { (s,s'). Abnormal e s' \<in> f s \<and> s \<in> RES.SPACE }
                                          | Crash \<Rightarrow> { (s,s'). Invalid \<in> f s \<and> s \<in> RES.SPACE }))\<close>

definition Valid_Transition :: \<open>('ret eval_stat \<Rightarrow> 'a rel) \<Rightarrow> bool\<close>
  where \<open>Valid_Transition tr \<longleftrightarrow> tr Crash = {}\<close>


definition Transition_of_Success :: \<open>'ret::VALs proc \<Rightarrow> 'ret \<phi>arg \<Rightarrow> resource rel\<close>
  where \<open>Transition_of_Success f = (\<lambda>v. { (s,s'). Success v s' \<in> f s })\<close>




definition Raw_Procedure :: "'ret::VALs proc
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> resource rel)
                        \<Rightarrow> bool"
    ("\<r>\<a>\<w> \<p>\<r>\<o>\<c> (2_) \<r>\<e>\<f>\<i>\<n>\<e>\<s> _ " [11,11] 10)
  where "Raw_Procedure f S \<longleftrightarrow> (\<forall>x r. f (r * x) \<subseteq> \<S> (\<lambda>v. { r * y | y. (x,y) \<in> S v }) 0)"

definition Fictional_Refine :: "'ret::VALs proc
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> fiction rel)
                        \<Rightarrow> bool"
  where \<open>Fictional_Refine f S \<longleftrightarrow> (\<forall>x r. f (r * x) \<subseteq> \<S> (\<lambda>v. { r * y | y. (x,y) \<in> S v }) 0)\<close>

term Domain

definition Fictional_Forward_Simulation :: \<open>'c rel \<Rightarrow> 'a rel \<Rightarrow> ('a::sep_magma_1,'c::sep_magma_1) interp \<Rightarrow> 'a set \<Rightarrow> bool\<close>
      ("_ \<r>\<e>\<f>\<i>\<n>\<e>\<s> _ \<w>.\<r>.\<t> _ \<i>\<n> _" [11,11,11] 10)
  where \<open>(F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T \<i>\<n> D) \<longleftrightarrow> (\<forall>x r R. F `` (R * \<I> T (r * x) \<s>\<u>\<b>\<j> r ## x \<and> x \<in> D) \<subseteq> { y'. \<exists>y. y' \<in> R * \<I> T (r * y) \<and> r ## y \<and> (x,y) \<in> G})\<close>

lemma empty_refines_any[simp]:
  \<open>{} \<r>\<e>\<f>\<i>\<n>\<e>\<s> Any \<w>.\<r>.\<t> I \<i>\<n> AnyD\<close>
  unfolding Fictional_Forward_Simulation_def
  by simp

lemma
  \<open>Any \<r>\<e>\<f>\<i>\<n>\<e>\<s> Any \<w>.\<r>.\<t> \<F>_it \<i>\<n> D\<close>
  for Any :: \<open>'a::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff)
  subgoal for x r R t u
    apply (rule exI[where x=x])


lemma
  \<open>Any \<r>\<e>\<f>\<i>\<n>\<e>\<s> UNIV \<w>.\<r>.\<t> I\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff)
  subgoal for x r R t u v


lemma refinement_frame:
  \<open> 1 \<in> R
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on R * B \<w>.\<r>.\<t> I\<close>
  for B :: \<open>'b::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff)
  by (smt (z3) mult_1_class.mult_1_left mult_1_class.mult_1_right sep_disj_multD2 sep_magma_1_left)

lemma sep_refinement_stepwise:
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> I1 \<i>\<n> UNIV
\<Longrightarrow> S2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> I2 \<i>\<n> D'
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (I1 o\<^sub>\<I> I2) \<i>\<n> D'\<close>
  for S1 :: \<open>'a::sep_monoid rel\<close>
  and S2 :: \<open>'b::sep_monoid rel\<close>
  and S3 :: \<open>'c::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def interp_comp_\<I>
  apply (auto simp add: subset_iff Image_def Bex_def \<phi>expns split_option_all)
  subgoal premises prems for x r R t u v xb
  proof -
    have \<open>(\<exists>x. (\<exists>u v. x = u * v \<and> u \<in> R \<and> v \<in> \<I> I1 xb \<and> u ## v) \<and> (x, t) \<in> S1)\<close>
      apply (rule exI[where x=\<open>u * v\<close>], simp add: prems)
      using prems(6) prems(7) prems(9) by auto
    note prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>], simplified,
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y u' v'
      proof -
        have \<open>(\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<in> {1} \<and> v \<in> \<I> I2 (r * x) \<and> u ## v) \<and> r ## x \<and> x \<in> D' \<and> (xa, y) \<in> S2)\<close>
          using prems(3) prems(4) prems(8) prems2(1) by auto
        note prems(2)[THEN spec[where x=x],THEN spec[where x=r],THEN spec[where x=\<open>{1}\<close>], THEN spec[where x=y],
                THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(3) prems2(4) prems2(5) by auto
      qed
      .
  qed .

lemma sep_refinement_horizontal_stepwise:
  \<open> A1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 \<w>.\<r>.\<t> I
\<Longrightarrow> A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B2 \<w>.\<r>.\<t> I
\<Longrightarrow> A1 O A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 O B2 \<w>.\<r>.\<t> I\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: \<phi>expns subset_iff Image_def Bex_def)
  by (smt (z3) relcomp.relcompI


context basic_fiction begin

lemma
  \<open> Valid_Proc f
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 v \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition S2
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> \<lambda>v. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> S2 (Normal v) \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> S2 (Abnm e))\<close>
  unfolding \<phi>Procedure_alt Fictional_Forward_Simulation_def atomize_all Valid_Transition_def
  apply (auto simp add: Image_iff subset_iff Bex_def R.basic_fiction_\<I> \<phi>expns Transition_of'_def
          LooseStateSpec_def split_sum_all INTERP_RES_def interp_split' R.\<r>_valid_split' interp_comp_\<I>
          R.inject_wand_homo inject_wand_homo prj.homo_mult eval_stat_forall split: eval_stat.split)
  subgoal premises prems for r u y v y' rr
    thm prems
    thm prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
  proof -
    have [simp]: \<open>R.clean y' \<in> R.SPACE\<close>
      by (metis (no_types, lifting) R.\<r>_valid_split R.inj.homo_sep_mult_axioms Valid_Proc_def homo_sep_mult.homo_mult prems(1) prems(10) prems(14) prems(15) prems(16) prems(9) times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> \<I> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
      get r ## x \<and> x \<in> D \<and> Success v y' \<in> f xa \<and> R.clean xa \<in> R.SPACE \<and> (\<exists>m. xa R.name = R.inject m \<and> m \<in>\<^sub>S R.domain))\<close>
      apply (rule exI[where x=\<open>(u * R.mk y)\<close>], simp add: prems R.inj.homo_mult[symmetric] )
      using prems(12) prems(13) by blast
    note prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>],
            THEN mp, OF this]
    then show ?thesis
    apply clarsimp
    subgoal for yy ya
      apply (rule exI[where x=yy], clarsimp simp add: inj.homo_mult[symmetric] prems prj.homo_mult, rule)
      apply (metis R.resource_kind_axioms Valid_Proc_def prems(1) prems(15) resource_kind.\<r>_valid_split t2 times_fupdt_1_apply_sep)
      using prems(11) by blast .
qed
  subgoal premises prems for r u y v y' rr
  proof -
    thm prems(5)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
    have [simp]: \<open>R.clean y' \<in> R.SPACE\<close>
      by (metis R.\<r>_valid_split R.inj.homo_mult Valid_Proc_def prems(1) prems(10) prems(14) prems(15) prems(16) prems(9) times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> \<I> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
      get r ## x \<and> x \<in> D \<and> Abnormal v y' \<in> f xa \<and> R.clean xa \<in> R.SPACE \<and> (\<exists>m. xa R.name = R.inject m \<and> m \<in>\<^sub>S R.domain))\<close>
      by (metis (no_types, lifting) R.inj.homo_mult fiction_kind.sep_disj_get_name_eq fiction_kind_axioms insert_iff prems(10) prems(12) prems(13) prems(14) prems(15) prems(16) prems(3) prems(7) prems(8) prems(9) times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)
    note prems(5)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>],
            THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal for yy ya
        apply (rule exI[where x=yy], clarsimp simp add: inj.homo_mult[symmetric] prems prj.homo_mult, rule)
        apply (metis R.resource_kind_axioms Valid_Proc_def prems(1) prems(15) resource_kind.\<r>_valid_split t2 times_fupdt_1_apply_sep)
        using prems(11) by blast .
  qed
  by (metis (mono_tags, lifting) R.inj.homo_mult sep_disj_get_name times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)

end



definition GTS \<comment> \<open>Greatest Transition of a Specification\<close>
    :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set\<close> (infix "\<longrightarrow>\<^sub>R" 25)
    where \<open>GTS P Q = { (x,y) |x y. x \<in> P \<longrightarrow> y \<in> Q }\<close>

lemma GTS_iff[iff]:
  \<open>(x,y) \<in> (X \<longrightarrow>\<^sub>R Y) \<longleftrightarrow> (x \<in> X \<longrightarrow> y \<in> Y)\<close>
  unfolding GTS_def by simp





context partial_map_resource begin

term \<open>{(x,y). y = updt (\<lambda>f. f(k := u)) x}\<close>

lemma
  \<open>{(x,y). x \<in> SPACE \<and> y = updt (\<lambda>f. f(k := u)) x}
\<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1(k \<mapsto> any)) | any. True} \<longrightarrow>\<^sub>R {(1(k := u))} \<w>.\<r>.\<t> basic_fiction \<i>\<n> {(1(k \<mapsto> any)) | any. True}\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: basic_fiction_\<I> \<phi>expns prj.homo_mult times_fun_upd sep_disj_partial_map_upd
        nonsepable_semigroup_sepdisj_fun)
apply (clarsimp simp add: sep_disj_partial_map_upd
          nonsepable_semigroup_sepdisj_fun mk_homo_mult)
  subgoal premises prems for r R u' any
  proof -
    have [simp]: \<open>(get u' * (r * 1(k \<mapsto> any)))(k := u) = get u' * (r * 1(k := u))\<close>
      by (metis domIff fun_upd_same fun_upd_upd mk_homo_mult option.distinct(1) prems(2) prems(4) sep_disj_get_name sep_disj_partial_map_upd)
    have [simp]: \<open>get u' ## (r * 1(k := u))\<close>
      by (metis mk_homo_mult nonsepable_semigroup_sepdisj_fun prems(2) prems(4) sep_disj_get_name sep_disj_multD1 sep_disj_multI1 sep_disj_multI2)
    have [simp]: \<open>r ## 1(k := u)\<close>
      by (meson nonsepable_semigroup_sepdisj_fun prems(2))
    have [simp]: \<open>r ## (get u' * 1(k := u))\<close>
      by (metis \<open>get u' ## r * 1(k := u)\<close> \<open>r ## 1(k := u)\<close> sep_disj_commuteI sep_disj_multI1 sep_mult_commute)
    have [simp]: \<open>get u' ## 1(k := u)\<close>
      using \<open>get u' ## r * 1(k := u)\<close> \<open>r ## 1(k := u)\<close> sep_disj_commute sep_disj_multD2 by blast
    have \<open>clean u' * mk(get u') = u'\<close>
      by (smt (verit, ccfv_threshold) fun_split_1 inj.homo_sep_wand mk_homo_mult prems(1) prems(2) prems(4) resource_kind.inj_prj_in_SPACE resource_kind_axioms sep_insertion.proj_inj sep_insertion_axioms sep_space_entry.sep_disj_mk_name sep_space_entry_axioms times_fupdt_1_apply_sep)
    show ?thesis
      apply (simp add: mk_homo_mult)
      apply (rule exI[where x=u']; rule)
      apply (smt (verit, best) \<open>clean u' * mk (get u') = u'\<close> \<open>get u' ## r * 1(k := u)\<close> \<open>r ## 1(k := u)\<close> mk_homo_mult sep_disj_clean sep_disj_mk sep_mult_assoc' sep_mult_left_commute)
      by (metis \<open>clean u' * mk (get u') = u'\<close> \<open>get u' ## r * 1(k := u)\<close> \<open>r ## 1(k := u)\<close> mk_homo_mult prems(3) sep_disj_clean sep_disj_mk sep_disj_multI1)
  qed
  .
      thm mk_homo_mult
    apply (rule exI[where x=u']; simp add: prems)
    apply rule
     prefer 2
  proof -
    have t1[simp]: \<open>r ## 1(k := u)\<close>
      by (meson nonsepable_semigroup_sepdisj_fun prems(1))
    have t2: \<open>u' ## mk r * mk (1(k \<mapsto> any))\<close>
      by (metis fun_1upd_homo inj.homo_mult prems(1) prems(3))
    show \<open>u' ## mk (r * 1(k := u))\<close> 
     apply (clarsimp simp add: mk_homo_mult)
      thm mk_homo_mult
      thm prems[simplified mk_homo_mult]

  subgoal for r R u' any
proof -
    have t1: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(8))
    have t2: \<open>clean x ## (mk aa * mk (1(k := u)))\<close>
      by (simp add: fun_1upd_homo)
    show ?thesis
      by (metis nonsepable_semigroup_sepdisj_fun prems(6) prems(9) sep_disj_mk sep_disj_multI1 sep_mult_assoc' t1 t2)
  qed .
(*\<exists>ub. clean ua * mk ((get ua * (r * 1(k \<mapsto> any)))(k := u)) = ub * mk (r * 1(k := u)) \<and> ub \<in> R \<and> ub ## mk (r * 1(k := u))*)
(*\<exists>xa. clean x * (mk a * mk (1(k := u))) = xa * mk (1(k := u)) \<and> xa \<in> R \<and> xa ## mk (1(k := u))*)
  
    apply rule

  prefer 2
  apply (meson nonsepable_semigroup_sepdisj_fun)
  subgoal for x r R u'
    apply (rule exI[where x=\<open>x(k:=u)\<close>])
    
thm sep_disj_partial_map_upd

  unfolding \<phi>R_set_res_def Transition_of'_def
  apply (cases evs; clarsimp simp add: \<phi>expns Fictional_Forward_Simulation_def basic_fiction_\<I>
          prj.homo_mult)

lemma
  \<open>updt (\<lambda>f. f(k := u))\<close>

term updt
term Id

end


end