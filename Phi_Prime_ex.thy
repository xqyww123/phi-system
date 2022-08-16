theory Phi_Prime_ex
  imports NuPrime HOL.Transitive_Closure BI_for_Phi
begin

chapter \<open>Extension of Semantics & Specification Framework\<close>

section \<open>Resource Transition\<close>

subsection \<open>Mathematical Preliminary\<close>

lemma rel_refl_I_subset:
  \<open>Id \<subseteq> P \<Longrightarrow> refl P\<close>
  by (metis refl_reflcl sup.order_iff)

lemma rel_trans_I_subset:
  "P O P \<subseteq> P \<Longrightarrow> trans P"
  by (meson relcomp.relcompI subsetD trans_def)

lemma rel_spec_ind_base:
  \<open>refl P \<Longrightarrow> Id\<^sup>* \<subseteq> P\<close>
  by (metis pair_in_Id_conv refl_Id refl_onD2 refl_on_def rtrancl_empty rtrancl_idemp subrelI)

lemma rel_spec_ind_step:
  \<open> trans P
\<Longrightarrow> A\<^sup>* \<subseteq> P
\<Longrightarrow> B \<subseteq> P
\<Longrightarrow> (A \<union> B)\<^sup>* \<subseteq> P\<close>
  unfolding subset_iff
  apply clarsimp
  subgoal for a b
    apply (rotate_tac 3)
  apply (induct rule: rtrancl.induct)
     apply blast
    by (metis Un_iff r_into_rtrancl relcomp.relcompI transD) .


subsection \<open>Semantic Level\<close>

type_synonym ('RES_N,'RES) transition_fun = \<open>('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('RES_N \<Rightarrow> 'RES)\<close>
type_synonym ('RES_N,'RES) transition = \<open>(('RES_N \<Rightarrow> 'RES) \<times> ('RES_N \<Rightarrow> 'RES)) set\<close>

definition Transition_Of :: \<open>('ret,'RES_N,'RES) proc \<Rightarrow> ('RES_N,'RES) transition\<close>
  where \<open>Transition_Of proc =
    { (res,res') | res res'. (\<exists>ret. proc res = Success ret res')
                           \<or> proc res = Exception res'}\<close>

definition rel_of_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) set\<close>
  where \<open>rel_of_fun f = { (x,y) |x y. f x = y }\<close>


subsection \<open>Specification\<close>

(*
definition (in \<phi>resource_sem) Raw_Spec_Trans
      :: \<open>('RES_N,'RES) transition \<Rightarrow> ('RES_N \<Rightarrow> 'RES) set \<Rightarrow> ('RES_N \<Rightarrow> 'RES) set \<Rightarrow> bool\<close>
  where \<open>Raw_Spec_Trans Tr P Q \<longleftrightarrow> (\<forall>x y. x \<in> P \<and> (x,y) \<in> Tr \<longrightarrow> y \<in> Q)\<close>

lemma (in \<phi>resource_sem) Raw_Spec_Trans_alt_def:
  \<open>Raw_Spec_Trans Tr P Q \<longleftrightarrow> Tr \<subseteq> { (x,y) |x y. x \<in> P \<longrightarrow> y \<in> Q }\<close>
  unfolding Raw_Spec_Trans_def by (rule; clarsimp simp add: subset_iff)

definition (in \<phi>fiction) Spec_Trans
    :: \<open>('RES_N,'RES) transition \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> bool\<close>
  where \<open>Spec_Trans Tr P Q \<longleftrightarrow> (\<forall>R. Raw_Spec_Trans Tr (INTERP_COM (R * P)) (INTERP_COM (R * Q)))\<close>
*)

definition GTS \<comment> \<open>Greatest Transition of a Specification\<close>
    :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set\<close> (infix "\<longrightarrow>\<^sub>R" 25)
  where \<open>GTS P Q = { (x,y) |x y. x \<in> P \<longrightarrow> y \<in> Q }\<close>

definition (in \<phi>fiction) \<phi>GTS
    :: \<open>('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('RES_N,'RES) transition\<close> (infix "\<longrightarrow>\<^sub>R\<^sub>\<phi>" 25)
    where \<open>\<phi>GTS P Q = (\<forall>\<^sup>S R. INTERP_COM (R * P) \<longrightarrow>\<^sub>R INTERP_COM (R * Q))\<close>

definition (in \<phi>fiction) \<phi>GTS_R
    :: \<open>('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('RES_N,'RES) transition\<close>
        ("_ \<longrightarrow>\<^sub>\<phi>[_] _" [26,26,26] 25)
    where \<open>\<phi>GTS_R P R Q = (INTERP_COM (R * P) \<longrightarrow>\<^sub>R INTERP_COM (R * Q))\<close>


lemma (in \<phi>fiction)
  \<open>\<phi>GTS P Q = { (x,y) |x y. \<forall>R. x \<in> (INTERP_COM (R * P)) \<longrightarrow> y \<in> (INTERP_COM (R * Q)) }\<close>
  unfolding \<phi>GTS_def set_eq_iff by (simp add: \<phi>expns GTS_def)
  

(*
lemma (in \<phi>fiction) Spec_Trans_alt_def:
  \<open>Spec_Trans Tr P Q \<longleftrightarrow> Tr \<subseteq> GTS P Q\<close>
  unfolding Spec_Trans_def Raw_Spec_Trans_alt_def GTS_def
  by (rule; clarsimp simp add: subset_iff)
*)
  

definition Valid_Spec_Trans :: \<open>('a \<times> 'a) set \<Rightarrow> bool\<close>
  where \<open>Valid_Spec_Trans R \<longleftrightarrow> refl R \<and> trans R\<close>

lemma \<comment> \<open>Reflexive transitive property is enough.\<close>
  \<open> trans R \<and> refl R
\<Longrightarrow> Range R \<subseteq> Domain R\<close>
  by (metis Domain.DomainI UNIV_I UNIV_eq_I refl_on_def top_greatest)

lemma (in \<phi>fiction) Resource_Transition_Spec_I:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> Transition_Of f \<subseteq> (P \<longrightarrow>\<^sub>\<phi>[R] (ExSet Q + E))\<close>
  unfolding \<phi>Procedure_def \<phi>GTS_R_def GTS_def Transition_Of_def
  apply (clarsimp simp add: AllSet_expn)
  subgoal premises prems for x y
    apply (insert prems(1)[THEN spec, THEN spec, THEN mp, OF \<open>x \<in> _\<close>],
           insert \<open>_ \<or> _\<close>)
    apply (cases \<open>f x\<close>; simp add: semiring_class.distrib_left \<phi>expns)
    by blast .


subsection \<open>Decision Procedure for Validating Specification of Transition Closure\<close>

definition \<open>DPVSTC P \<equiv> Trueprop P\<close>

subsubsection \<open>Initialization - strip out fictions\<close>

lemma [\<phi>reason 2000]:
  \<open>(\<And>x. Valid_Spec_Trans (R x))
\<Longrightarrow> Valid_Spec_Trans (\<forall>\<^sup>Sx. R x)\<close>
  unfolding Valid_Spec_Trans_def
  by (simp add: AllSet_refl AllSet_trans) 

lemma [\<phi>reason 2000]:
  \<open> PROP DPVSTC (trans P)
\<Longrightarrow> PROP DPVSTC (refl P)
\<Longrightarrow> Valid_Spec_Trans P\<close>
  unfolding Valid_Spec_Trans_def DPVSTC_def ..


subsubsection \<open>Decision Procedure for Reflexivity\<close>

text \<open>The procedure essentially matches each additive part in domain with that in range
    by unification.\<close>

(*
lemma (in \<phi>fiction) [\<phi>reason 2000]: \<open>
    PROP DPVSTC (refl (X \<longrightarrow>  Y))
\<Longrightarrow> PROP DPVSTC (refl (X \<longrightarrow>\<^sub>\<phi>[R] Y))\<close>
  unfolding DPVSTC_def \<phi>GTS_def
  apply (rule AllSet_refl; rule refl_onI; clarsimp simp add: GTS_def \<phi>expns)
  subgoal for R x u v
  apply (elim refl_onD[elim_format, where a=v]; simp)
    by blast . *)

lemma (in \<phi>fiction) [\<phi>reason 2000]:
  \<open> PROP DPVSTC (refl (A1 \<longrightarrow>\<^sub>\<phi>[R] B))
\<Longrightarrow> PROP DPVSTC (refl (A2 \<longrightarrow>\<^sub>\<phi>[R] B))
\<Longrightarrow> PROP DPVSTC (refl (A1 + A2 \<longrightarrow>\<^sub>\<phi>[R] B))\<close>
  unfolding GTS_def \<phi>GTS_R_def refl_on_def DPVSTC_def
  by (simp add: semiring_class.distrib_left)

lemma (in \<phi>fiction) [\<phi>reason]:
  \<open> PROP DPVSTC (refl (A \<longrightarrow>\<^sub>\<phi>[R] B1))
\<Longrightarrow> PROP DPVSTC (refl (A \<longrightarrow>\<^sub>\<phi>[R] B1 + B2))\<close>
  unfolding GTS_def \<phi>GTS_R_def refl_on_def DPVSTC_def
  by (simp add: semiring_class.distrib_left)

lemma (in \<phi>fiction) [\<phi>reason]:
  \<open> PROP DPVSTC (refl (A \<longrightarrow>\<^sub>\<phi>[R] B2))
\<Longrightarrow> PROP DPVSTC (refl (A \<longrightarrow>\<^sub>\<phi>[R] B1 + B2))\<close>
  unfolding GTS_def \<phi>GTS_R_def refl_on_def DPVSTC_def
  by (simp add: semiring_class.distrib_left)

lemma (in \<phi>fiction) [\<phi>reason 80]:
  \<open> A \<subseteq> B
\<Longrightarrow> PROP DPVSTC (refl (A \<longrightarrow>\<^sub>\<phi>[R] B))\<close>
  unfolding GTS_def \<phi>GTS_R_def refl_on_def DPVSTC_def subset_iff by (simp add: \<phi>expns, blast)


subsubsection \<open>Decision Procedure for Transitivity\<close>

lemma
  \<open> PROP DPVSTC (R O R \<subseteq> R)
\<Longrightarrow> PROP DPVSTC (trans R)\<close>
  unfolding DPVSTC_def
  using rel_trans_I_subset by blast

lemma (in \<phi>fiction) [\<phi>reason 2000]: \<open>
    PROP DPVSTC (trans (X \<longrightarrow>\<^sub>R Y))
\<Longrightarrow> PROP DPVSTC (Y \<subseteq> X)
\<Longrightarrow> PROP DPVSTC (trans (X \<longrightarrow>\<^sub>R\<^sub>\<phi> Y))\<close>
  unfolding DPVSTC_def \<phi>GTS_def
  apply (rule AllSet_trans, rule transI)
  apply (clarsimp simp add: GTS_def \<phi>expns refl_on_def trans_def subset_iff)
  subgoal premises prems for R x y z u v proof -
    have \<open>(\<exists>fic. (\<exists>u v. fic = u * v \<and> u \<in> R \<and> v \<in> X) \<and> x \<in> INTERP_RES fic)\<close>
      using \<open>u \<in> R\<close> \<open>v \<in> X\<close> \<open>x \<in> INTERP_RES (u * v)\<close> by blast
    note t1 = \<open>_ \<longrightarrow> _\<close>[THEN mp, OF this]
    then obtain fic' u' v' where t2[simp]: \<open>fic' = u' * v' \<and> u' \<in> R \<and> v' \<in> Y \<and> y \<in> INTERP_RES fic'\<close> by blast
    show ?thesis
      using prems(1) prems(6) t2 by blast
  qed .




lemma
  \<open>A \<subseteq> (B \<inter> C) \<longleftrightarrow> A \<subseteq> B \<and> A \<subseteq> C\<close>
  by simp

lemma
  \<open> A \<subseteq> C \<or> B \<subseteq> C
\<Longrightarrow> (A \<inter> B) \<subseteq> C\<close>
  by blast
  


lemma GTS_CONSEQ:
  \<open> C \<subseteq> A
\<Longrightarrow> B \<subseteq> D
\<Longrightarrow> GTS A B \<subseteq> GTS C D\<close>
  unfolding GTS_def subset_iff by simp

subsection \<open>Decision Procedure for Reasoning Transitivity, R O R \<subseteq> R\<close>

text \<open>Overall, the procedure shows by enumeration, every transition path in the spec
  \<close>

subsubsection \<open>Phase I: Unfolding Universal Quantification\<close>

lemma [\<phi>reason 2000]:
  \<open>(\<And>x. A O B \<subseteq> P x)
\<Longrightarrow> A O B \<subseteq> (\<forall>\<^sup>Sx. P x) \<close>
  by (simp add: AllSet_subset)

lemma [\<phi>reason 1950]:
  \<open> A x O B \<subseteq> P
\<Longrightarrow> (\<forall>\<^sup>Sx. A x) O B \<subseteq> P \<close>
  by (metis AllSet_subset order_trans relcomp_mono subset_refl)
(*
lemma
  \<open>(\<forall>\<^sup>Sx. A x) O B \<subseteq> P \<longleftrightarrow> A x O B \<subseteq> P\<close>

lemma [\<phi>reason 19800]:
  \<open> A O B x \<subseteq> P
\<Longrightarrow> A O (\<forall>\<^sup>Sx. B x) \<subseteq> P \<close>
  by (metis AllSet_subset order_trans relcomp_mono subset_refl)
*)
subsubsection \<open>Phase II: Unfolding Domains of Specification\<close>


lemma (in \<phi>fiction) TSpec_P_left_plus[\<phi>reason 1850]:
  \<open> A O B \<subseteq> (P1 \<longrightarrow>\<^sub>\<phi>[R] Q)
\<Longrightarrow> A O B \<subseteq> (P2 \<longrightarrow>\<^sub>\<phi>[R] Q)
\<Longrightarrow> A O B \<subseteq> (P1 + P2 \<longrightarrow>\<^sub>\<phi>[R] Q)\<close>
  unfolding subset_iff GTS_def \<phi>GTS_R_def
  by (simp add: semiring_class.distrib_left)

lemma (in \<phi>fiction) [\<phi>reason 1850]:
  \<open> A O B \<subseteq> (P1 \<longrightarrow>\<^sub>\<phi>[R] Q)
\<Longrightarrow> A O B \<subseteq> (P2 \<longrightarrow>\<^sub>\<phi>[R] Q)
\<Longrightarrow> A O B \<subseteq> (P1 + P2 \<longrightarrow>\<^sub>\<phi>[R] Q)\<close>
  unfolding \<phi>GTS_def \<phi>GTS_R_def
  apply (simp add: AllSet_subset semiring_class.distrib_left)
  by (metis INTERP_COM_plus TSpec_P_left_plus \<phi>GTS_R_def distrib_left)

subsubsection \<open>Phase III: Find the right beginning \<close>

lemma [\<phi>reason]:
  \<open> A1 O B \<subseteq> P
\<Longrightarrow> (A1 \<inter> A2) O B \<subseteq> P\<close>
  by blast

lemma [\<phi>reason]:
  \<open> A2 O B \<subseteq> P
\<Longrightarrow> (A1 \<inter> A2) O B \<subseteq> P\<close>
  by blast

lemma (in \<phi>fiction) [\<phi>reason]:
  \<open> (A1 \<longrightarrow>\<^sub>\<phi>[R] B) O Y \<subseteq> P
\<Longrightarrow> (A1 + A2 \<longrightarrow>\<^sub>\<phi>[R] B) O Y \<subseteq> P\<close>
  unfolding \<phi>GTS_def subset_iff \<phi>GTS_R_def
  apply (clarsimp simp add: AllSet_subset semiring_class.distrib_left \<phi>expns GTS_def
      Relation.relcomp.simps)
  by metis

lemma (in \<phi>fiction) [\<phi>reason]:
  \<open> (A2 \<longrightarrow>\<^sub>\<phi>[R] B) O Y \<subseteq> P
\<Longrightarrow> (A1 + A2 \<longrightarrow>\<^sub>\<phi>[R] B) O Y \<subseteq> P\<close>
  unfolding \<phi>GTS_def subset_iff \<phi>GTS_R_def
  apply (clarsimp simp add: AllSet_subset semiring_class.distrib_left \<phi>expns GTS_def
      Relation.relcomp.simps)
  by metis

lemma (in \<phi>fiction) [\<phi>reason]:
  \<open> A O B \<subseteq> (P \<longrightarrow>\<^sub>\<phi>[R] Q1)
\<Longrightarrow> A O B \<subseteq> (P \<longrightarrow>\<^sub>\<phi>[R] Q1 + Q2)\<close>
  unfolding subset_iff GTS_def \<phi>GTS_R_def
  by (clarsimp simp add: AllSet_subset semiring_class.distrib_left \<phi>expns GTS_def
      Relation.relcomp.simps)

lemma (in \<phi>fiction) [\<phi>reason]:
  \<open> A O B \<subseteq> (P \<longrightarrow>\<^sub>\<phi>[R] Q2)
\<Longrightarrow> A O B \<subseteq> (P \<longrightarrow>\<^sub>\<phi>[R] Q1 + Q2)\<close>
  unfolding subset_iff GTS_def \<phi>GTS_R_def
  by (clarsimp simp add: AllSet_subset semiring_class.distrib_left \<phi>expns GTS_def
      Relation.relcomp.simps)

lemma (in \<phi>fiction)
  \<open> (A \<longrightarrow>\<^sub>\<phi>[R] B1) O Y \<subseteq> P
\<Longrightarrow> (A \<longrightarrow>\<^sub>\<phi>[R] B2) O Y \<subseteq> P
\<Longrightarrow> (A \<longrightarrow>\<^sub>\<phi>[R] B1 + B2) O Y \<subseteq> P\<close>
  unfolding GTS_def subset_iff \<phi>GTS_R_def
  apply (clarsimp simp add: AllSet_subset semiring_class.distrib_left GTS_def
      Relation.relcomp.simps AllSet_expn)
  by blast


lemma (in \<phi>fiction)
  \<open>(A \<longrightarrow>\<^sub>\<phi>[R] B) O (B \<longrightarrow>\<^sub>\<phi>[R] C) \<subseteq> (A \<longrightarrow>\<^sub>\<phi>[R] C)\<close>
  unfolding GTS_def \<phi>GTS_R_def set_eq_iff relcomp_unfold by clarsimp



lemma
  \<open> A O B1 \<subseteq> P
\<Longrightarrow> A O (B1 \<inter> B2) \<subseteq> P\<close>
  by blast

lemma
  \<open> A O B2 \<subseteq> P
\<Longrightarrow> A O (B1 \<inter> B2) \<subseteq> P\<close>
  by blast

lemma
  \<open> A O (B1 \<longrightarrow>\<^sub>R C) \<subseteq> P
\<Longrightarrow> A O (B1 + B2 \<longrightarrow>\<^sub>R C) \<subseteq> P\<close>
  unfolding GTS_def subset_iff by (simp, blast)

lemma
  \<open> A O (B2 \<longrightarrow>\<^sub>R C) \<subseteq> P
\<Longrightarrow> A O (B1 + B2 \<longrightarrow>\<^sub>R C) \<subseteq> P\<close>
  unfolding GTS_def subset_iff by (simp, blast)
  



definition \<open>MeetSpec \<equiv> Trueprop\<close>

lemma
  \<open> PROP MeetSpec (A \<subseteq> P1)
\<Longrightarrow> PROP MeetSpec (A \<subseteq> P2)
\<Longrightarrow> PROP MeetSpec (A \<subseteq> P1 \<inter> P2)\<close>
  unfolding MeetSpec_def by blast

lemma (in \<phi>fiction)
  \<open> INTERP_COM (R * A) \<inter> INTERP_COM (R * X) = {}
\<Longrightarrow> (A \<longrightarrow>\<^sub>\<phi>[R] B) \<subseteq> (X \<longrightarrow>\<^sub>\<phi>[R] Y)\<close>
  unfolding \<phi>GTS_R_def GTS_def subset_iff set_eq_iff
  apply (clarsimp simp add: \<phi>expns)
  subgoal premises prems for res res' u v proof -
    
    thm prems(1)[THEN spec[where x=res]]
    have \<open>\<not> (\<forall>fic. (\<forall>u. u \<in> R \<longrightarrow> (\<forall>v. fic = u * v \<longrightarrow> v \<notin> X)) \<or> res \<notin> INTERP_RES fic)\<close>
      apply (clarsimp, rule exI[where x=\<open>(u * v)\<close>], simp add: prems)
      using prems(4) prems(5) by blast
    then have \<open>(\<forall>fic. (\<forall>u. u \<in> R \<longrightarrow> (\<forall>v. fic = u * v \<longrightarrow> v \<notin> A)) \<or> res \<notin> INTERP_RES fic)\<close>
      using prems(1) by blast
    thm prems
    thm prems(2)[THEN mp]
    show ?thesis
      apply (rule prems(2)[THEN mp])




(*
lemma (in \<phi>fiction)
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> P \<longmapsto> Q \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> Spec_Trans (Transition_Of f) P (ExSet Q + E)\<close>
  unfolding \<phi>Procedure_def Spec_Trans_def Raw_Spec_Trans_def Transition_Of_def
  apply clarsimp
  subgoal premises prems for R x y
    apply (insert prems(1)[THEN spec, THEN spec, THEN mp, OF \<open>x \<in> _\<close>],
           insert \<open>_ \<or> _\<close>)
    apply (cases \<open>f x\<close>; simp add: semiring_class.distrib_left \<phi>expns)
    by blast .
*)



end