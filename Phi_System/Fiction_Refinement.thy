theory Fiction_Refinement
  imports PhiSem_Formalization_Tools
  abbrevs "<refines>" = "\<r>\<e>\<f>\<i>\<n>\<e>\<s>"
      and "<w.r.t>" = "\<w>.\<r>.\<t>"
begin











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
    

definition Transition_of :: \<open>'ret proc \<Rightarrow> 'ret \<phi>arg + ABNM \<Rightarrow> resource rel\<close>
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


definition Transition_of' :: \<open>'ret proc \<Rightarrow> 'ret eval_stat \<Rightarrow> resource rel\<close>
  where \<open>Transition_of' f = (\<lambda>x. (case x of Normal v \<Rightarrow> { (s,s'). Success v s' \<in> f s \<and> s \<in> RES.SPACE }
                                          | Abnm e \<Rightarrow> { (s,s'). Abnormal e s' \<in> f s \<and> s \<in> RES.SPACE }
                                          | Crash \<Rightarrow> { (s,s'). Invalid \<in> f s \<and> s = s' \<and> s \<in> RES.SPACE }))\<close>

definition Valid_Transition :: \<open>('ret eval_stat \<Rightarrow> 'a rel) \<Rightarrow> bool\<close>
  where \<open>Valid_Transition tr \<longleftrightarrow> tr Crash = {}\<close>


definition Transition_of_Success :: \<open>'ret proc \<Rightarrow> 'ret \<phi>arg \<Rightarrow> resource rel\<close>
  where \<open>Transition_of_Success f = (\<lambda>v. { (s,s'). Success v s' \<in> f s })\<close>




definition Raw_Procedure :: "'ret proc
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> resource rel)
                        \<Rightarrow> bool"
    ("\<r>\<a>\<w> \<p>\<r>\<o>\<c> (2_) \<r>\<e>\<f>\<i>\<n>\<e>\<s> _ " [11,11] 10)
  where "Raw_Procedure f S \<longleftrightarrow> (\<forall>x r. f (r * x) \<subseteq> \<S> (\<lambda>v. { r * y | y. (x,y) \<in> S v }) 0)"

definition Fictional_Refine :: "'ret proc
                        \<Rightarrow> ('ret \<phi>arg \<Rightarrow> fiction rel)
                        \<Rightarrow> bool"
  where \<open>Fictional_Refine f S \<longleftrightarrow> (\<forall>x r. f (r * x) \<subseteq> \<S> (\<lambda>v. { r * y | y. (x,y) \<in> S v }) 0)\<close>

term Domain

definition Fictional_Forward_Simulation :: \<open>'c rel \<Rightarrow> 'a rel \<Rightarrow> ('a::sep_magma_1,'c::sep_magma_1) interp \<Rightarrow> 'a set \<Rightarrow> bool\<close>
      ("_/ \<r>\<e>\<f>\<i>\<n>\<e>\<s> _/ \<w>.\<r>.\<t> _/ \<i>\<n> _" [11,11,11] 10)
  where \<open>(F \<r>\<e>\<f>\<i>\<n>\<e>\<s> G \<w>.\<r>.\<t> T \<i>\<n> D) \<longleftrightarrow> (\<forall>x r R. F `` (R * \<I> T (r * x) \<s>\<u>\<b>\<j> r ## x \<and> x \<in> D) \<subseteq> { y'. \<exists>y. y' \<in> R * \<I> T (r * y) \<and> r ## y \<and> (x,y) \<in> G})\<close>

lemma empty_refines_any[simp]:
  \<open>{} \<r>\<e>\<f>\<i>\<n>\<e>\<s> Any \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by simp

lemma refinement_sub_domain:
  \<open> D' \<subseteq> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D'\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: \<phi>expns subset_iff Image_def Bex_def Id_on_iff, blast)

lemma refinement_sub_fun:
  \<open> A  \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A' \<subseteq> A
\<Longrightarrow> A' \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: \<phi>expns subset_iff Image_def Bex_def Id_on_iff; blast)

lemma refinement_sub_fun_right:
  \<open> A  \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> B \<subseteq> B'
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B' \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: \<phi>expns subset_iff Image_def Bex_def Id_on_iff; blast)


lemma refinement_frame:
  \<open> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on R * B \<w>.\<r>.\<t> I \<i>\<n> R * D\<close>
  for B :: \<open>'b::sep_monoid rel\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: subset_iff \<phi>expns Image_def Bex_def Id_on_iff)
  by (smt (z3) sep_disj_multD1 sep_disj_multD2 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc')

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
  subgoal for x r R t u v *)


lemma sep_refinement_stepwise:
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> I1 \<i>\<n> D
\<Longrightarrow> S2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> I2 \<i>\<n> D'
\<Longrightarrow> \<forall>r. \<Union> (\<I> I2 ` ({r} * D')) \<subseteq> D
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (I1 o\<^sub>\<I> I2) \<i>\<n> D'\<close>
  unfolding Fictional_Forward_Simulation_def interp_comp_\<I>
  apply (auto simp add: subset_iff Image_def Bex_def \<phi>expns split_option_all)
  subgoal premises prems for x r R t u v xb
  proof -
    thm prems
    thm prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>]]
    have \<open>(\<exists>x. (\<exists>u v. x = u * v \<and> u \<in> R \<and> v \<in> \<I> I1 (1 * xb) \<and> u ## v) \<and> 1 ## xb \<and> xb \<in> D \<and> (x, t) \<in> S1)\<close>
      apply (simp add: prems)
      using prems(10) prems(3) prems(4) prems(5) prems(6) prems(7) prems(8) prems(9) by blast
    note prems(1)[THEN spec[where x=xb],THEN spec[where x=1],THEN spec[where x=\<open>R\<close>],THEN spec[where x=\<open>t\<close>],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y u'' v''
      proof -
        have \<open>(\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<in> {1} \<and> v \<in> \<I> I2 (r * x) \<and> u ## v) \<and> r ## x \<and> x \<in> D' \<and> (xa, y) \<in> S2)\<close>
          by (simp, rule exI[where x=xb], simp add: prems2 prems)
        note prems(2)[THEN spec[where x=x],THEN spec[where x=r],THEN spec[where x=\<open>{1}\<close>], THEN spec[where x=y],
                THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(3) prems2(4) prems2(5) by auto
      qed .
  qed .

lemma sep_refinement_stepwise':
  \<open> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S2 \<w>.\<r>.\<t> I1 \<i>\<n> D
\<Longrightarrow> S2' \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> I2 \<i>\<n> D'
\<Longrightarrow> \<forall>R. \<Union> (\<I> I2 ` (R * D')) \<subseteq> D
\<Longrightarrow> S2 \<subseteq> S2'
\<Longrightarrow> S1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> S3 \<w>.\<r>.\<t> (I1 o\<^sub>\<I> I2) \<i>\<n> D'\<close>
  using refinement_sub_fun sep_refinement_stepwise
  by metis


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


definition \<open>pairself f = (\<lambda>(x,y). (f x, f y))\<close>

lemma pairself[simp]:
  \<open>pairself f (x,y) = (f x, f y)\<close>
  unfolding pairself_def by simp

lemma
  \<open> \<forall>R. \<Union> (\<I> I2 ` (R * D')) \<subseteq> UNIV * D
\<Longrightarrow> \<forall>R. \<Union> (\<I> (\<F>_pointwise I2) ` (R * fun_upd 1 k ` D')) \<subseteq> UNIV * fun_upd 1 k ` D\<close>
  for D :: \<open>'b::sep_monoid set\<close>
  apply (clarsimp simp add: subset_iff Bex_def image_iff set_mult_expn times_fun)
  subgoal premises prems for R t u xb
  proof -
    thm prems
    have t1: \<open>u k ## xb\<close>
      by (metis fun_upd_same prems(4) sep_disj_fun)
    thm prems
    thm prems(1)[THEN spec[where x=\<open>{u k}\<close>], THEN spec[where x=\<open>t k\<close>]]
    have \<open>(\<exists>x. (\<exists>xa. (\<exists>ua v. xa = ua * v \<and> ua \<in> {u k} \<and> v \<in> D' \<and> ua ## v) \<and> x = \<I> I2 xa) \<and> t k \<in> x)\<close>
      apply simp
      by (metis prems(2) prems(5) t1)
    note prems(1)[THEN spec[where x=\<open>{u k}\<close>], THEN spec[where x=\<open>t k\<close>], THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for u' v'
        apply (rule exI[where x=\<open>t(k := u')\<close>], rule exI[where x=\<open>1(k := v')\<close>])
        by (simp add: fun_eq_iff prems2 sep_disj_fun_def times_fun) .
  qed .

lemma pointwise_refinement:
  \<open> Id_on UNIV * A \<r>\<e>\<f>\<i>\<n>\<e>\<s> B \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> Id_on UNIV * pairself (fun_upd 1 k) ` A \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` B
    \<w>.\<r>.\<t> \<F>_pointwise I \<i>\<n> fun_upd 1 k ` D\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: \<phi>expns image_iff Image_def subset_iff Bex_def times_fun Id_on_iff)
  subgoal premises prems for r R u v xb xc a b
  proof -
    have t1[simp]: \<open>xc k ## a\<close>
      by (metis fun_upd_same prems(8) sep_disj_fun)
    have t2[simp]: \<open>xc k ## b\<close>
      by (metis fun_upd_same prems(9) sep_disj_fun)
    have \<open>(\<exists>x. (\<exists>ua v. x = ua * v \<and> ua \<in> {u k} \<and> v \<in> \<I> I (r k * xb) \<and> ua ## v) \<and>
     r k ## xb \<and>
     xb \<in> D \<and> (\<exists>a ba aa. x = a * aa \<and> (\<exists>bb. xc k * b = ba * bb \<and> a = ba \<and> (aa, bb) \<in> A \<and> a ## aa \<and> ba ## bb)))\<close>
      apply (simp add: prems)
      by (smt (verit, del_insts) fun_upd_same prems(10) prems(2) prems(5) prems(6) prems(7) sep_disj_fun_def t1 t2 times_fun)
    note prems(1)[THEN spec[where x=xb], THEN spec[where x=\<open>r k\<close>], THEN spec[where x=\<open>{u k}\<close>, THEN spec[where x=\<open>xc k * b\<close>]],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y v'
      proof -
        thm prems
        thm prems2
        have t4: \<open>u ## v(k := v')\<close>
          by (clarsimp simp add: sep_disj_fun_def prems2 prems(7)) (simp add: prems(7))
        have t3: \<open>xc * 1(k := b) = u * v(k := v')\<close>
          apply (clarsimp simp add: fun_eq_iff times_fun prems2)
          by (metis (no_types, opaque_lifting) fun_upd_other mult_1_class.mult_1_right prems(5) times_fun_def)
        show ?thesis
        apply (rule exI[where x=\<open>1(k := y)\<close>]; simp add: prems prems2; rule)
          apply (smt (verit, ccfv_threshold) fun_split_1 fun_upd_other fun_upd_same prems(3) prems(6) prems2(4) t3 t4 times_fun)
          by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv prems2(1) prems2(2))
      qed .
  qed .


lemma sep_refinement_horizontal_stepwise:
  \<open> A1 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 \<w>.\<r>.\<t> I \<i>\<n> D
\<Longrightarrow> A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B2 \<w>.\<r>.\<t> I \<i>\<n> D'
\<Longrightarrow> (B1 `` D \<subseteq> D')
\<Longrightarrow> A1 O A2 \<r>\<e>\<f>\<i>\<n>\<e>\<s> B1 O B2 \<w>.\<r>.\<t> I \<i>\<n> D\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: \<phi>expns subset_iff Image_def Bex_def)
  subgoal premises prems for x r R u v y z
  proof -
    have \<open>(\<exists>xa. (\<exists>u v. xa = u * v \<and> u \<in> R \<and> v \<in> \<I> I (r * x) \<and> u ## v) \<and> r ## x \<and> x \<in> D \<and> (xa, y) \<in> A1)\<close>
      using prems(10) prems(4) prems(5) prems(6) prems(8) prems(9) by blast
    note prems(1)[THEN spec[where x=x], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=y],
          THEN mp, OF this]
    then show ?thesis
      apply clarsimp
      subgoal premises prems2 for y' u' v'
      proof -
        have \<open>(\<exists>x. (\<exists>u v. x = u * v \<and> u \<in> R \<and> v \<in> \<I> I (r * y') \<and> u ## v) \<and> r ## y' \<and> y' \<in> D' \<and> (x, z) \<in> A2)\<close>
          using prems(3) prems(5) prems(7) prems2(1) prems2(2) prems2(3) prems2(4) prems2(5) prems2(6) by blast
        note prems(2)[THEN spec[where x=y'], THEN spec[where x=r], THEN spec[where x=R], THEN spec[where x=z],
          THEN mp, OF this]
        then show ?thesis
          apply clarsimp
          using prems2(2) by blast
      qed .
  qed .


lemma wierd:
  \<open>Id_on UNIV * Id_on (A \<s>\<u>\<b>\<j> P)
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on (B \<s>\<u>\<b>\<j> P) \<w>.\<r>.\<t> I \<i>\<n> B\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: subset_iff Id_on_iff set_mult_expn Subjection_expn times_fun; blast)



context basic_fiction begin

context begin
private lemma from_fictional_refinement':
  \<open> Valid_Proc f
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> Rel v \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition Rel
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> \<lambda>v. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Normal v) \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Abnm e))\<close>
  unfolding \<phi>Procedure_alt Fictional_Forward_Simulation_def atomize_all Valid_Transition_def
  apply (auto simp add: Image_iff subset_iff Bex_def R.basic_fiction_\<I> \<phi>expns Transition_of'_def
          LooseStateSpec_def split_sum_all INTERP_RES_def interp_split' R.\<r>_valid_split' interp_comp_\<I>
          R.inject_wand_homo inject_wand_homo prj.homo_mult eval_stat_forall split: eval_stat.split)
  subgoal premises prems for r u y v y' rr
    thm prems
    thm prems(4)[THEN spec[where x=v], THEN spec[where x=x], THEN spec[where x=\<open>get r\<close>], THEN spec[where x=\<open>{u}\<close>], THEN spec[where x=\<open>y'\<close>]]
  proof -
    have [simp]: \<open>R.clean y' \<in> R.SPACE\<close>
      by (metis R.\<r>_valid_split Valid_Proc_def fun_upd_same fun_upd_upd prems(1) prems(11) prems(13) prems(14) prems(16) prems(17) prems(9) resource_space.SPACE_1 resource_space.SPACE_mult_homo)
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
    have [simp]: \<open>R.clean y' \<in> R.SPACE\<close>
      by (metis R.\<r>_valid_split Valid_Proc_def fun_upd_same fun_upd_upd prems(1) prems(11) prems(13) prems(14) prems(16) prems(17) prems(9) resource_space.SPACE_1 resource_space.SPACE_mult_homo)
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
\<Longrightarrow> YY = (\<lambda>v. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Normal v))
\<Longrightarrow> EE = (\<lambda>e. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Abnm e))
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> Rel v \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition Rel
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE\<close>
  using from_fictional_refinement' by blast

end

end



definition GTS \<comment> \<open>Greatest Transition of a Specification\<close>
    :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set\<close> (infix "\<longrightarrow>\<^sub>R" 25)
    where \<open>GTS P Q = { (x,y) |x y. x \<in> P \<longrightarrow> y \<in> Q }\<close>

lemma GTS_iff[iff]:
  \<open>(x,y) \<in> (X \<longrightarrow>\<^sub>R Y) \<longleftrightarrow> (x \<in> X \<longrightarrow> y \<in> Y)\<close>
  unfolding GTS_def by simp



context partial_map_resource2 begin

lemma
  \<open>{(x,y). x \<in> SPACE \<and> y = updt (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) x}
\<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1(k := 1(k2 \<mapsto> any)), 1(k := 1(k2 := u))) | any. True}
\<w>.\<r>.\<t> basic_fiction \<i>\<n> {(1(k := 1(k2 \<mapsto> any))) | any. True}\<close>
unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: basic_fiction_\<I> \<phi>expns prj.homo_mult times_fun_upd sep_disj_partial_map_upd
        nonsepable_semigroup_sepdisj_fun SPACE_mult_homo \<r>_valid_split'
        times_fun inj.homo_mult[symmetric] inject_wand_homo)
  apply rule
  subgoal premises prems for r R u' any a
    apply (rule exI[where x=u']; simp add: prems; rule)
  proof -
    have [simp]: \<open>(r * a) k k2 = None\<close>
      by (smt (verit, best) fun_upd_same prems(3) prems(7) sep_disj_fun_def sep_disj_multD1 sep_disj_multI1 sep_disj_partial_map_some_none sep_mult_commute)
    then have [simp]:
        \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (r * (a * 1(k := 1(k2 \<mapsto> any))))
            = (r * a) * 1(k := 1(k2 := u))\<close>
        unfolding map_fun_at_def fun_eq_iff times_fun_def
        by simp
    have t1[simp]: \<open>clean u' * mk a = u'\<close>
      by (metis fun_split_1 prems(6))
    show \<open>clean u' * mk (map_fun_at (map_fun_at (\<lambda>_. u) k2) k (r * (a * 1(k := 1(k2 \<mapsto> any))))) = u' * mk (r * 1(k := 1(k2 := u)))\<close>
        apply simp
      by (smt (verit, del_insts) fun_sep_disj_1_fupdt(1) fun_upd_triv inj.homo_mult inj.sep_disj_homo inject_assoc_homo nonsepable_semigroup_sepdisj_fun prems(3) prems(6) prems(7) sep_disj_multD1 sep_disj_multI1 sep_mult_commute sep_space_entry.times_fun_upd sep_space_entry_axioms times_fupdt_1_apply_sep)
    show \<open>u' ## mk (r * 1(k := 1(k2 := u)))\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo nonsepable_semigroup_sepdisj_fun prems(3) prems(6) prems(7) sep_disj_multD1 sep_disj_multI1 sep_disj_multI2)
  qed
  by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv nonsepable_semigroup_sepdisj_fun)

lemma
  \<open>Transition_of' (\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. u) k2) k)) ret
= {(x,y). x \<in> SPACE \<and> y = updt (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) x \<and> ret = Normal \<phi>V_none}\<close>
  unfolding Transition_of'_def \<phi>R_set_res_def
  by (cases ret; clarsimp simp add: set_eq_iff \<phi>V_none_def; rule; clarsimp)

lemma
  \<open>Transition_of' (\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. u) k2) k)) ret
    \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(x,y). x \<in> SPACE \<and> y = updt (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) x \<and> ret = Normal \<phi>V_none}
    \<w>.\<r>.\<t> \<F>_it \<i>\<n> { 1(Res #= 1(k := 1(k2 \<mapsto> any))) | any. True }\<close>
  unfolding Transition_of'_def \<phi>R_set_res_def
  apply (cases ret; clarsimp simp add: Fictional_Forward_Simulation_def subset_iff Image_iff
        \<phi>expns Bex_def SPACE_mult_homo)
  subgoal premises prems for r R u' any
  proof -
    thm prems
    have t1[simp]: \<open>r ## (u' * mk (1(k := 1(k2 \<mapsto> any))))\<close>
      by (simp add: prems(2) prems(4) sep_disj_commuteI sep_disj_multI1 sep_mult_commute)
    have t11[simp]: \<open>u' ## mk (1(k := 1(k2 \<mapsto> any)))\<close>
      using prems(2) prems(4) sep_disj_commuteI sep_disj_multD2 by blast 
    have t12[simp]: \<open>r * u' ## mk (1(k := 1(k2 \<mapsto> any)))\<close>
      by (simp add: sep_disj_multI1)
    have t12'[simp]: \<open>get (r * u') ## (1(k := 1(k2 \<mapsto> any)))\<close>
      using sep_disj_get_name t12 by blast
    have txx[simp]: \<open>get (r * u') k k2 = None\<close>
      by (metis (mono_tags, opaque_lifting) fun_sep_disj_imply_v fun_upd_triv sep_disj_option_nonsepable(1) t12')
    have t01[simp]: \<open>r * (u' * mk (1(k := 1(k2 := xx)))) = (r * u') * mk (1(k := 1(k2 := xx)))\<close> for xx
      by (metis (mono_tags, lifting) SPACE_mult_homo fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo inj_prj_in_SPACE nonsepable_semigroup_sepdisj_fun prems(5) sep_disj_multD1 sep_mult_assoc t1 t11 t12')
    have t02[simp]: \<open>u' * (r * mk (1(k := 1(k2 := xx)))) = (r * u') * mk (1(k := 1(k2 := xx)))\<close> for xx
      by (smt (z3) SPACE_mult_homo fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo inj_prj_in_SPACE nonsepable_semigroup_sepdisj_fun prems(2) prems(4) prems(5) sep_disj_multD1 sep_disj_multI1 sep_mult_assoc sep_mult_commute t1 t11 times_fun)
    have t5[simp]: \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (1(k := 1(k2 \<mapsto> any))) = (1(k := 1(k2 := u)))\<close>
      by (simp add: map_fun_at_def fun_eq_iff)
    have t4[simp]: \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (get (r * u') * 1(k := 1(k2 \<mapsto> any))) = get (r * u') * 1(k := 1(k2 := u))\<close>
      unfolding map_fun_at_def fun_eq_iff
      by simp
    have t6[simp]: \<open>project ((r * u') name * inject (1(k := 1(k2 \<mapsto> any)))) = get (r * u') * 1(k := 1(k2 \<mapsto> any))\<close>
      by (simp add: prj.homo_mult)

    show ?thesis
      apply (rule, rule exI[where x=u'], simp add: prems, rule)
      apply (smt (verit, ccfv_threshold) SPACE_mult_homo fun_sep_disj_1_fupdt(1) fun_upd_triv inj.homo_mult inj_prj_in_SPACE nonsepable_semigroup_sepdisj_fun prems(5) sep_space_entry.times_fun_upd sep_space_entry_axioms t01 t12 t12' times_fupdt_1_apply_sep)
       apply (smt (verit, del_insts) SPACE_mult_homo fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo_semi inj_prj_in_SPACE nonsepable_semigroup_sepdisj_fun prems(2) prems(4) prems(5) sep_disj_multD1 sep_disj_multI2 sep_mult_commute t1 t11 t12')
      apply (simp add: \<phi>V_none_def; rule)
      apply (metis (mono_tags, lifting) SPACE_mult_homo fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo inj_prj_in_SPACE nonsepable_semigroup_sepdisj_fun prems(2) prems(5) t1)
      using SPACE_mult_homo prems(5) by force      
  qed .

lemma \<phi>R_get_res_transition:
  \<open> Transition_of' (\<phi>R_get_res_entry' k k2) ret
        = Id_on {s. ret = (case get s k k2 of Some v \<Rightarrow> Normal (\<phi>arg v) | _ \<Rightarrow> Crash) \<and> s \<in> SPACE}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def \<phi>R_get_res_entry'_def bind_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff split: option.split; blast)

lemma
  \<open>Transition_of' (\<phi>R_get_res_entry' k k2) ret
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({1(k := 1(k2 \<mapsto> any))} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg any))
   \<w>.\<r>.\<t> basic_fiction \<i>\<n> {1(k := 1(k2 \<mapsto> any))}\<close>
  unfolding Fictional_Forward_Simulation_def \<phi>R_get_res_transition
  apply (cases ret; clarsimp split: option.split simp add: basic_fiction_\<I> set_mult_expn Id_on_iff
          Subjection_expn zero_set_def set_eq_iff prj.homo_mult times_fun)
  by (metis (mono_tags, opaque_lifting) fun_upd_same option.inject sep_disj_commute sep_disj_fun sep_disj_get_name sep_disj_multD2 sep_disj_option_nonsepable(2) sep_mult_commute times_option(2))


end

context resource begin

lemma
  \<open> Transition_of' (\<phi>R_get_res F) ret = {(s,s'). (s,s') \<in> Transition_of' (F (get s)) ret}\<close>
  unfolding Transition_of'_def \<phi>R_get_res_def
  by (cases ret; clarsimp simp add: set_eq_iff)

lemma \<phi>R_get_res_transition:
  \<open> Transition_of' \<phi>R_get_res' ret = Id_on {s. ret = Normal (\<phi>arg (get s)) \<and> s \<in> SPACE}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff; blast)




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

end

context partial_map_resource begin

lemma \<phi>R_get_res_transition:
  \<open> Transition_of' (\<phi>R_get_res_entry' k) ret
        = Id_on {s. ret = (case get s k of Some v \<Rightarrow> Normal (\<phi>arg v) | _ \<Rightarrow> Crash) \<and> s \<in> SPACE}\<close>
  unfolding Transition_of'_def \<phi>R_get_res'_def \<phi>R_get_res_entry'_def bind_def Return_def det_lift_def
  by (cases ret; clarsimp simp add: set_eq_iff Id_on_iff split: option.split; blast)

lemma \<phi>R_get_res_transition_refinement:
  \<open>Transition_of' (\<phi>R_get_res_entry' k) ret
   \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({1(k \<mapsto> any)} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg any))
   \<w>.\<r>.\<t> basic_fiction \<i>\<n> {1(k \<mapsto> any)}\<close>
  unfolding Fictional_Forward_Simulation_def \<phi>R_get_res_transition
  apply (cases ret; clarsimp split: option.split simp add: basic_fiction_\<I> set_mult_expn Id_on_iff
          Subjection_expn zero_set_def set_eq_iff prj.homo_mult times_fun)
  by (smt (verit, best) domIff fun_1upd_homo fun_split_1_not_dom fun_upd_same map_upd_eqD1 sep_disj_partial_map_some_none sep_space_entry.sep_disj_get_name sep_space_entry_axioms)

lemma \<phi>R_get_res_entry'_valid:
  \<open>Valid_Proc (\<phi>R_get_res_entry' k)\<close>
  unfolding Valid_Proc_def \<phi>R_get_res_entry'_def \<phi>R_get_res'_def bind_def Return_def det_lift_def
  by (clarsimp split: option.split)


(* lemma
  \<open>(\<And>v. Transition_of' (F v) ret \<subseteq> Id_on (UNIV \<s>\<u>\<b>\<j> v \<in> P ret))
\<Longrightarrow> Transition_of' (case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid})) ret
      \<subseteq> Id_on (UNIV \<s>\<u>\<b>\<j> res \<in> UNIV * (\<lambda>v. 1(k \<mapsto> v)) ` P ret)\<close>
  unfolding Transition_of'_def
  apply (cases ret; clarsimp simp add: Id_on_iff subset_iff Subjection_expn set_mult_expn
                      image_iff Bex_def split: option.split)
  apply (metis fun_sep_disj_1_fupdt(1) fun_split_1 sep_magma_1_right)
   apply (metis fun_sep_disj_1_fupdt(1) fun_split_1 sep_magma_1_right)
  apply auto 

lemma \<open>fun_upd 1 k o Some = (\<lambda>v. 1(k \<mapsto> v))\<close> *)
  

lemma
  \<open>Transition_of' (\<phi>R_get_res_entry k F) ret \<subseteq> Id_on (P ret \<inter> SPACE)\<close>

lemma
  \<open> Transition_of' (\<phi>R_get_res_entry k F) ret = {(s,s').
      (case get s k of Some v \<Rightarrow> (s,s') \<in> Transition_of' (F v) ret | _ \<Rightarrow> ret = Crash \<and> s \<in> SPACE)}\<close>
  unfolding Transition_of'_def \<phi>R_get_res_def \<phi>R_get_res_entry_def
  by (cases ret; clarsimp simp add: set_eq_iff split: option.split)

lemma
  \<open> Transition_of' (\<phi>R_get_res_entry k F) ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> R ret \<w>.\<r>.\<t> basic_fiction \<close>



lemma
  \<open>pairself (\<lambda>x. 1(k := x)) ` {(Some any, u)} = {(1(k \<mapsto> any), 1(k := u))}\<close>
  by (clarsimp simp add: set_eq_iff image_iff; blast)

lemma "__updt_refinement__":
  \<open>{(x,y). x \<in> SPACE \<and> y = updt (\<lambda>f. f(k := u)) x}
\<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1(k \<mapsto> any), 1(k := u))} \<w>.\<r>.\<t> basic_fiction \<i>\<n> {(1(k \<mapsto> any))}\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: basic_fiction_\<I> \<phi>expns prj.homo_mult times_fun_upd sep_disj_partial_map_upd
        nonsepable_semigroup_sepdisj_fun SPACE_mult_homo \<r>_valid_split'
        times_fun inj.homo_mult[symmetric] inject_wand_homo)
  subgoal premises prems for r R u' a
  proof (rule exI[where x=u']; simp add: prems; rule)
    have [simp]: \<open>mk ((r * (a * 1(k \<mapsto> any)))(k := u)) = mk (r * (a * 1(k := u)))\<close>
      by (smt (z3) domIff fun_split_1_not_dom fun_upd_same fun_upd_upd option.distinct(1) prems(3) prems(7) sep_disj_commuteI sep_disj_fun_nonsepable(1) sep_disj_multI1 sep_disj_partial_map_upd sep_mult_commute)
    have t1[simp]: \<open>clean u' * mk a = u'\<close>
      by (metis fun_split_1 prems(6))
    show \<open>clean u' * mk ((r * (a * 1(k \<mapsto> any)))(k := u)) = u' * mk (r * 1(k := u))\<close>
      apply simp
      by (smt (verit, del_insts) fun_1upd_homo_right1 fun_upd_triv mk_homo_mult mult_1_class.mult_1_left nonsepable_semigroup_sepdisj_fun prems(3) prems(6) prems(7) sep_disj_multD1 sep_disj_multI1 sep_disj_multI2 sep_mult_left_commute)
    show \<open>u' ## mk (r * 1(k := u))\<close>
      by (smt (verit, del_insts) fun_upd_def inj.sep_disj_homo_semi nonsepable_semigroup_sepdisj_fun prems(3) prems(6) prems(7) sep_disj_fun_def sep_disj_multD1 sep_disj_multI1 sep_disj_multI2 sep_magma_1_left)
  qed .



lemma transition_of_\<phi>R_set_res:
  \<open>Transition_of' (\<phi>R_set_res (\<lambda>f. f(k := u))) ret = {(x,y). x \<in> SPACE \<and> y = updt (\<lambda>f. f(k := u)) x \<and> ret = Normal \<phi>V_none}\<close>
  unfolding Transition_of'_def \<phi>R_set_res_def
  by (cases ret; clarsimp simp add: set_eq_iff \<phi>V_none_def; rule; clarsimp)

lemma transition_of_\<phi>R_set_res:
  \<open>Transition_of' (\<phi>R_get_res (\<lambda>f. f(k := u))) ret = {(x,y). x \<in> SPACE \<and> y = updt (\<lambda>f. f(k := u)) x \<and> ret = Normal \<phi>V_none}\<close>
  unfolding Transition_of'_def \<phi>R_set_res_def
  by (cases ret; clarsimp simp add: set_eq_iff \<phi>V_none_def; rule; clarsimp)


lemma
  \<open>Transition_of' (\<phi>R_set_res (\<lambda>f. f(k := u))) ret
  \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1(k \<mapsto> any), 1(k := u)) |any. True}
  \<w>.\<r>.\<t> local.basic_fiction
  \<i>\<n> {1(k \<mapsto> any) |any. True}\<close>
  apply (subst transition_of_\<phi>R_set_res)
  apply (rule refinement_sub_fun[OF "__updt_refinement__"])
  by clarsimp


end

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_get_res_entry'_frm[intro!]:
  \<open>\<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k \<lbrace> 1(k \<mapsto> Share n v) \<Ztypecolon> \<phi> Identity \<longmapsto>
                               \<lambda>ret. 1(k \<mapsto> Share n v) \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
  apply (rule from_fictional_refinement[where Rel = \<open>\<lambda>ret.  Id_on ({1(k \<mapsto> Share n v)} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg v))\<close>
                                          and D = \<open>{1(k \<mapsto> Share n v)}\<close>],
         rule R.\<phi>R_get_res_entry'_valid)
  apply (simp add: set_eq_iff Subjection_expn Id_on_iff ExSet_expn)
  apply (simp add: Id_on_iff zero_set_def zero_fun_def)
subgoal for ret
  apply (rule sep_refinement_stepwise)
  apply (rule refinement_frame[where R=UNIV, OF R.\<phi>R_get_res_transition_refinement[where any=v]])
   apply (rule wierd)
  apply (clarsimp simp add: subset_iff set_mult_expn)

end

context identity_fiction_for_partial_mapping_resource begin


lemma \<phi>R_get_res_entry'_frm[intro!]:
  \<open>\<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k \<lbrace> 1(k \<mapsto> v) \<Ztypecolon> \<phi> Identity \<longmapsto> \<lambda>ret. 1(k \<mapsto> v) \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
  thm from_fictional_refinement[where Rel = \<open>\<lambda>ret.  Id_on ({1(k \<mapsto> v)} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg v))\<close>,
            simplified, simplified Id_on_iff zero_set_def \<phi>expns, simplified]
  apply (rule from_fictional_refinement[where Rel = \<open>\<lambda>ret.  Id_on ({1(k \<mapsto> v)} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg v))\<close>
                                          and D = \<open>{1(k \<mapsto> v)}\<close>],
         rule R.\<phi>R_get_res_entry'_valid)
      apply (simp add: set_eq_iff Subjection_expn Id_on_iff ExSet_expn)
     apply (simp add: Id_on_iff zero_set_def zero_fun_def)
subgoal for ret
  apply (rule sep_refinement_stepwise)
  thm R.\<phi>R_get_res_transition_refinement[where any=v]
  thm refinement_frame[where R=UNIV, OF R.\<phi>R_get_res_transition_refinement]
      apply (rule refinement_frame[where R=UNIV, OF R.\<phi>R_get_res_transition_refinement[where any=v]])
  thm refinement_frame[where R=UNIV, OF R.\<phi>R_get_res_transition_refinement]
  
    thm wierd
     apply (rule wierd)
apply (clarsimp simp add: subset_iff set_mult_expn)
    by blast
   apply (simp add: Valid_Transition_def Id_on_def)
  by simp

    thm wierd
  thm R.\<phi>R_get_res_transition_refinement
  thm R.\<phi>R_get_res_entry'_valid

  term \<open>(F x \<s>\<u>\<b>\<j> x. x = y \<and> P x)\<close>

end






term \<open>(o) f\<close>

term \<open>(o\<^sub>\<I>) I\<close>

lemma
  \<open>Id_on UNIV * Id_on {u} \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on {f u} \<w>.\<r>.\<t> I \<i>\<n> {f u}\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Id_on_iff set_mult_expn Subjection_expn; blast)


context cancl_perm_ins_homo begin

lemma
  \<open>Id_on UNIV * Id_on {u} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(share n (\<psi> u), share n (\<psi> u))} \<w>.\<r>.\<t> \<F>_functional \<psi> \<i>\<n> {share n (\<psi> u)}\<close>
  for u :: \<open>'a::{sep_algebra, sep_cancel}\<close>
  unfolding Fictional_Forward_Simulation_def
  by (clarsimp simp add: Id_on_iff set_mult_expn Subjection_expn; blast)

lemma
  \<open>Id_on UNIV * {(u,v)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(\<psi> u, \<psi> v)} \<w>.\<r>.\<t> \<F>_functional \<psi> \<i>\<n> {\<psi> u}\<close>
  for u :: \<open>'a::{sep_algebra, sep_cancel}\<close>
  unfolding Fictional_Forward_Simulation_def
  apply (clarsimp simp add: Id_on_iff set_mult_expn Subjection_expn homo_sep_wand)
  subgoal premises prems for R ru r1 r2
  proof -
    have t1: \<open>ru * u = (r1 * r2) * u\<close>
      by (simp add: prems(1) prems(5) prems(6) sep_mult_assoc')
    have t2: \<open>r1 * r2 ## u\<close>
      using prems(5) prems(6) sep_disj_multI1 by blast
    have t3: \<open>ru = r1 * r2\<close>
      using prems(3) sep_cancel t1 t2 by blast
    have t4: \<open>r2 ## v\<close>
      using prems(4) prems(5) prems(6) sep_disj_multD1 sep_disj_multD2 t3 by blast
    then have t5: \<open>\<psi> r2 ## \<psi> v\<close> by simp
    show ?thesis
      apply (simp add: t5)
      apply (rule exI[where x=r1], rule exI[where x=\<open>r2 * v\<close>], simp add: t3)
      by (metis local.homo_mult prems(2) prems(4) prems(5) prems(6) sep_disj_multD1 sep_disj_multI2 sep_mult_assoc t3 t4)
  qed .

end


end