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
    

definition Valid_Operation :: \<open>'ret::VALs proc \<Rightarrow> bool\<close>
  where \<open>Valid_Operation f \<longleftrightarrow> (\<forall>v s s'. Success v s' \<in> f s \<and> s \<in> RES.SPACE \<longrightarrow> s' \<in> RES.SPACE)
                             \<and> (\<forall>e s s'. Abnormal e s' \<in> f s \<and> s \<in> RES.SPACE \<longrightarrow> s' \<in> RES.SPACE)\<close>

lemma
  \<open> Valid_Operation f
\<Longrightarrow> (\<And>v. Valid_Operation (g v))
\<Longrightarrow> Valid_Operation (f \<bind> g)\<close>
  unfolding Valid_Operation_def bind_def
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

definition Fictional_Forward_Simulation :: \<open>'c rel \<Rightarrow> 'a rel \<Rightarrow> ('a::sep_magma_1,'c::sep_magma_1) interp \<Rightarrow> bool\<close>
      ("_ \<r>\<e>\<f>\<i>\<n>\<e>\<s> _ \<w>.\<r>.\<t> _ " [11,11,11] 10)
  where \<open>(F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T) \<longleftrightarrow> (\<forall>x r R. F `` (R * \<I> T (r * x) \<s>\<u>\<b>\<j> r ## x) \<subseteq> { y'. \<exists>y. y' \<in> R * \<I> T (r * y) \<and> r ## y \<and> (x,y) \<in> G})\<close>

lemma sep_refinement_stepwise:
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> I1
\<Longrightarrow> S2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> I2
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (I1 o\<^sub>\<I> I2)\<close>
  for S1 :: \<open>'a::sep_monoid rel\<close>
  and S2 :: \<open>'b::sep_monoid rel\<close>
  and S3 :: \<open>'c::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def interp_comp_\<I>
  apply (auto simp add: subset_iff Image_def Bex_def \<phi>expns split_option_all)
  by (smt mult_1_class.mult_1_left sep_magma_1_right set_in_1)

lemma sep_refinement_horizontal_stepwise:
  \<open> A1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 \<w>.\<r>.\<t> I
\<Longrightarrow> A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B2 \<w>.\<r>.\<t> I
\<Longrightarrow> A1 O A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 O B2 \<w>.\<r>.\<t> I\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: \<phi>expns subset_iff Image_def Bex_def)
  by (smt (z3) relcomp.relcompI)



context resource begin



end


context basic_fiction begin

lemma
  \<open> Valid_Operation f
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 v \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I)
\<Longrightarrow> Valid_Transition S2
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> \<lambda>v. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> S2 (Normal v) \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> S2 (Abnm e))\<close>
  unfolding \<phi>Procedure_alt Fictional_Forward_Simulation_def atomize_all Valid_Transition_def
  apply (auto simp add: Image_iff subset_iff Bex_def R.basic_fiction_\<I> \<phi>expns Transition_of'_def
          LooseStateSpec_def split_sum_all INTERP_RES_def interp_split' R.\<r>_valid_split' interp_comp_\<I>
          R.inject_wand_homo inject_wand_homo prj.homo_mult eval_stat_forall split: eval_stat.split)
  subgoal premises prems for r u y v y' rr
    thm prems
    thm prems(3)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
  proof -
    have [simp]: \<open>R.clean y' \<in> R.SPACE\<close>
      by (metis R.\<r>_valid_split R.inj.homo_mult Valid_Operation_def prems(1) prems(13) prems(14) prems(15) prems(8) prems(9) times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> \<I> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
      get r ## x \<and> Success v y' \<in> f xa \<and> R.clean xa \<in> R.SPACE \<and> (\<exists>m. xa R.name = R.inject m \<and> m \<in>\<^sub>S R.domain))\<close>
      apply (rule exI[where x=\<open>(u * R.mk y)\<close>], simp add: prems R.inj.homo_mult[symmetric] )
      using prems(11) prems(12) by blast
    note prems(3)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>],
            THEN mp, OF this]
    then show ?thesis
    apply clarsimp
    subgoal for yy ya
      apply (rule exI[where x=yy], clarsimp simp add: inj.homo_mult[symmetric] prems prj.homo_mult, rule)
      apply (metis R.\<r>_valid_split Valid_Operation_def prems(1) prems(14) t2 times_fupdt_1_apply_sep)
      using prems(10) by blast .
qed
  subgoal premises prems for r u y v y' rr
  proof -
    thm prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
    have [simp]: \<open>R.clean y' \<in> R.SPACE\<close>
      by (metis R.\<r>_valid_split R.inj.homo_mult Valid_Operation_def prems(1) prems(13) prems(14) prems(15) prems(8) prems(9) times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)
    have t2: \<open>(\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u} \<and> (\<exists>xa. xa \<in> \<I> I (get r * x) \<and> v = R.mk xa) \<and> ua ## v) \<and>
      get r ## x \<and> Abnormal v y' \<in> f xa \<and> R.clean xa \<in> R.SPACE \<and> (\<exists>m. xa R.name = R.inject m \<and> m \<in>\<^sub>S R.domain))\<close>
      using R.inj.homo_mult prems(11) prems(12) prems(13) prems(14) prems(15) prems(6) prems(7) prems(8) prems(9) by force
    note prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>],
            THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal for yy ya
        apply (rule exI[where x=yy], clarsimp simp add: inj.homo_mult[symmetric] prems prj.homo_mult, rule)
        apply (metis R.\<r>_valid_split Valid_Operation_def prems(1) prems(14) t2 times_fupdt_1_apply_sep)
        using prems(10) by blast .
  qed
  by (metis (mono_tags, lifting) R.inj.homo_mult sep_disj_get_name times_fupdt_1_apply_sep times_fupdt_1_fupdt_1_sep)



lemma
  \<open> \<r>\<a>\<w> \<p>\<r>\<o>\<c> f \<r>\<e>\<f>\<i>\<n>\<e>\<s> S1
\<Longrightarrow> (\<And>v. S1 v \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> (R.basic_fiction I))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Domain S2
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> S2 \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL Raw_Procedure_def Premise_def Sep_Forward_Simulation_def
  apply (clarsimp simp add: Image_def Bex_def subset_iff
          zero_set_def zero_fun_def R.basic_fiction_\<I> INTERP_RES_def
          interp_split' \<r>_valid_split' R.inject_wand_homo inject_wand_homo
          sep_disj_get_name_eq[symmetric])
  thm sep_disj_get_name_eq[symmetric]
  thm inject_wand_homo[OF _ sep_disj_mk_name]
  thm
  thm interp_spl

end


lemma
  \<open> 1 \<in> S
\<Longrightarrow> F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T
\<Longrightarrow> F \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on S * G \<w>.\<r>.\<t> T\<close>
  for G :: \<open>'b::sep_monoid rel\<close>
  unfolding Sep_Forward_Simulation_def subset_iff Image_iff Bex_def
  apply (clarsimp simp add: Id_on_iff set_mult_expn)
  by (metis mult_1_class.mult_1_left sep_magma_1_right)

lemma
  \<open> F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T
\<Longrightarrow> Id_on S * F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T\<close>
  unfolding Sep_Forward_Simulation_def subset_iff Image_iff Bex_def
  apply (clarsimp simp add: Id_on_iff set_mult_expn)
  subgoal premises prems for x r b aa ba
  proof -
    thm prems
    have \<open>\<exists>xa. xa \<in> \<I> T (r * x) \<and> (xa, t) \<in> F\<close>
    obtain y where t1: \<open>t \<in> \<I> T (r * y) \<and> (x, y) \<in> G\<close> 
    



end