theory Resource_Template
  imports PhiSem_Formalization_Tools2 Phi_Semantics_Framework.Phi_SemFrame_ex
begin


chapter \<open>Resource Bases and Templates\<close>

section \<open>Preliminary\<close>

interpretation to_share: cancl_perm_ins_homo \<open>to_share::'a::nonsepable_semigroup option \<Rightarrow> 'a share option\<close> ..
interpretation pointwise_to_share:
  cancl_perm_ins_homo \<open>(o) (to_share::'a::nonsepable_semigroup option \<Rightarrow> 'a share option)\<close> ..

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

definition \<open>basic_fiction = Interp (\<lambda>x. { 1(Res #= x) })\<close>

lemma basic_fiction_\<I>:
  "\<I> basic_fiction = (\<lambda>x. { 1(Res #= x)})"
  unfolding basic_fiction_def
  by (rule Interp_inverse) (clarsimp simp add: Interpretation_def one_set_def)

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


subsection \<open>Fiction Base\<close>

locale basic_fiction =
   R: resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction \<circ>\<^sub>\<I> I\<close>
for Res :: "'T::sep_algebra resource_entry"
and I :: "('U::sep_algebra, 'T) interp"
and Fic :: "'U fiction_entry"
begin

subsubsection \<open>\<phi>-Type\<close>

definition \<phi> :: \<open>('U, 'x) \<phi> \<Rightarrow> (fiction, 'x) \<phi>\<close>
    \<comment> \<open>\<phi>Type for level-1 mapping\<close>
  where \<open>\<phi> T = (\<lambda>x. { mk v |v. v \<in> (x \<Ztypecolon> T) })\<close>

lemma \<phi>_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi> T) \<longleftrightarrow> (\<exists>v. p = mk v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Type_def \<phi>_def by simp

lemma \<phi>_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>_Prod:
  \<open> \<phi> T \<^emph> \<phi> U = \<phi> (T \<^emph> U)\<close>
  apply (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; rule; clarsimp)
  apply (metis mk_homo_mult)
  by (metis fun_1upd_homo inj.homo_mult sep_disj_mk)

lemma \<phi>_\<phi>None:
  \<open>\<phi> \<circle> = \<circle>\<close>
  by (rule \<phi>Type_eqI; simp add: \<phi>expns)

lemma \<phi>_unit:
  \<open>(1 \<Ztypecolon> \<phi> Identity) = Void\<close>
  by (clarsimp simp add: set_eq_iff \<phi>_expn Identity_expn)

lemma [\<phi>reason 1200 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = (() \<Ztypecolon> \<circle>) @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp

lemma [\<phi>reason 1300 for \<open>(?x \<Ztypecolon> \<phi> \<circle>) = ?Z @action clean_automation_waste\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) = 1 @action clean_automation_waste\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None by simp


(*
lemma [\<phi>reason 1500 for \<open>(x \<Ztypecolon> \<phi> \<circle>) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?P @action (?Act::?'act::simplification action)\<close>]:
  \<open>(x \<Ztypecolon> \<phi> \<circle>) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (() \<Ztypecolon> \<circle>) @action Act\<close>
  for Act :: \<open>'act::simplification action\<close>
  unfolding Action_Tag_def \<phi>_\<phi>None
  by (simp add: implies_refl) *)

paragraph \<open>Reasoning Rules\<close>

lemma \<phi>_cast:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi> U \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (clarsimp simp add: \<phi>expns)

lemma \<phi>_Structural_Extract:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W) P
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W) P\<close>
  unfolding Structural_Extract_def
  by (simp add: \<phi>Prod_expn'[symmetric] \<phi>_Prod \<phi>_cast)

declare \<phi>_Structural_Extract[THEN SE_clean_waste, \<phi>reason 1200]

lemma [THEN SE_clean_waste', \<phi>reason 1211]:
  \<open> Structural_Extract (x \<Ztypecolon> T) (r \<Ztypecolon> R) (y \<Ztypecolon> U) (w \<Ztypecolon> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> U') (w' \<Ztypecolon> W') (x' \<Ztypecolon> T') (r' \<Ztypecolon> R') P') \<and> P)
\<Longrightarrow> Structural_Extract (x \<Ztypecolon> \<phi> T) (r \<Ztypecolon> \<phi> R) (y \<Ztypecolon> \<phi> U) (w \<Ztypecolon> \<phi> W)
      (Automatic_Morphism RP (Structural_Extract (y' \<Ztypecolon> \<phi> U') (w' \<Ztypecolon> \<phi> W') (x' \<Ztypecolon> \<phi> T') (r' \<Ztypecolon> \<phi> R') P') \<and> P)\<close>
  unfolding Automatic_Transformation_def Action_Tag_def
  by (blast intro: \<phi>_Structural_Extract[unfolded Action_Tag_def]
                   Structural_Extract_imply_P)

lemma ToSA_by_structural_extraction:
  " Structure_Info U Q
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> Q' : Q
\<Longrightarrow> (Q' \<Longrightarrow> \<r>CALL Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W P2))
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 \<heavy_comma> \<blangle> W \<brangle> \<a>\<n>\<d> P1
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> \<phi> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<a>\<n>\<d> P1 \<and> P2"
  unfolding Premise_def FOCUS_TAG_def Structural_Extract_def Simplify_def Try_def \<r>Call_def
  \<medium_left_bracket> premises SI and Q and SE and A
  have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
  ;;  A[THEN implies_right_prod]
     SE[OF \<open>Q'\<close>]
  \<medium_right_bracket> certified using \<phi> by simp .

lemma ToSA_by_structural_extraction__reverse_morphism:
  " Structure_Info U Q
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> Q' : Q
\<Longrightarrow> (Q' \<Longrightarrow> \<r>CALL Try Any (Structural_Extract (y \<Ztypecolon> \<phi> U) R1 (x \<Ztypecolon> \<phi> T) W
             (Automatic_Morphism RP2 (Structural_Extract (x' \<Ztypecolon> \<phi> T') W' (y' \<Ztypecolon> \<phi> U') R1' P2') \<and> P2)))
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 \<heavy_comma> \<blangle> W \<brangle> \<a>\<n>\<d> (Automatic_Morphism RP1 (R2'\<heavy_comma> \<blangle> W' \<brangle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> A' \<a>\<n>\<d> P1') \<and> P1)
\<Longrightarrow> A \<heavy_comma> y \<Ztypecolon> \<phi> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2\<heavy_comma> R1\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<a>\<n>\<d>
      (Automatic_Morphism (RP2 \<and>\<^sub>\<r> RP1) (R2'\<heavy_comma> R1'\<heavy_comma> \<blangle> x' \<Ztypecolon> \<phi> T' \<brangle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> A'\<heavy_comma> y' \<Ztypecolon> \<phi> U' \<a>\<n>\<d> P1' \<and> P2')
          \<and> P1 \<and> P2)"
  unfolding Premise_def FOCUS_TAG_def Structural_Extract_def Simplify_def
            Automatic_Transformation_def Compact_Antecedent_def Try_def \<r>Call_def
  \<medium_left_bracket> premises SI and Q and SE and A
  have \<open>Q'\<close> using \<phi> SI[unfolded Structure_Info_def] Q by blast
  ;; A[THEN implies_right_prod]
     SE[OF \<open>Q'\<close>]
  \<medium_right_bracket> certified apply  (simp add: \<phi>)
  \<medium_left_bracket>
    have A : \<open>R2' \<heavy_comma> W' \<i>\<m>\<p>\<l>\<i>\<e>\<s> A' \<a>\<n>\<d> P1'\<close> using \<phi>_previous \<open>RP2 \<and> RP1\<close> by simp
    have SE: \<open>(R1' \<heavy_comma> x' \<Ztypecolon> \<phi> T' \<i>\<m>\<p>\<l>\<i>\<e>\<s> W' \<heavy_comma> y' \<Ztypecolon> \<phi> U' \<a>\<n>\<d> P2')\<close> using \<phi>_previous \<open>RP2 \<and> RP1\<close> by simp
    ;; SE A[THEN implies_right_prod]
  \<medium_right_bracket>. .


lemma ToSA_skip [\<phi>reason 1200 except \<open> _ \<heavy_comma> ?y \<Ztypecolon> \<phi> ?U \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<a>\<n>\<d> _\<close> ]:
  " R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R'\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> R \<heavy_comma> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<a>\<n>\<d> P"
  unfolding Action_Tag_def FOCUS_TAG_def split_paired_All Action_Tag_def
  by (metis ab_semigroup_mult_class.mult_ac(1) implies_left_prod mult.commute)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action \<A>_structural Act
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi> U \<a>\<n>\<d> P @action \<A>_structural Act \<close>
  unfolding Action_Tag_def using \<phi>_cast .

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Target
\<Longrightarrow> x \<Ztypecolon> \<phi> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> \<phi> U \<a>\<n>\<d> P @action to Target \<close>
  unfolding Action_Tag_def using \<phi>_cast .


lemma [\<phi>reason 1200]:
  \<open> \<r>Clean (x \<Ztypecolon> T)
\<Longrightarrow> \<r>Clean (x \<Ztypecolon> \<phi> T) \<close>
  unfolding \<r>Clean_def Imply_def apply (simp add: \<phi>expns)
  using mk_homo_one by blast

lemma [\<phi>reason 1200 for \<open>If _ (_ \<Ztypecolon> \<phi> _) (_ \<Ztypecolon> \<phi> _) \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ @action branch_convergence\<close>]:
  \<open> If P (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (z \<Ztypecolon> Z) @action branch_convergence
\<Longrightarrow> If P (x \<Ztypecolon> \<phi> T) (y \<Ztypecolon> \<phi> U) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (z \<Ztypecolon> \<phi> Z) @action branch_convergence\<close>
  unfolding Action_Tag_def by (cases P; simp add: \<phi>_cast)

paragraph \<open>Conversion\<close>

lemma [simp]:
  \<open>(\<phi> (ExTyp T)) = (\<exists>\<phi> c. \<phi> (T c))\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma [simp]:
  \<open>(\<phi> (T \<phi>\<s>\<u>\<b>\<j> P)) = (\<phi> T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI; clarsimp simp add: \<phi>expns; blast)

lemma \<phi>_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<phi> T) = (x' \<Ztypecolon> \<phi> T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup \<phi>\<phi>_simp_cong ("x \<Ztypecolon> \<phi> T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>_simp_cong} ctxt)
\<close>

paragraph \<open>Synthesis for moving\<close>

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse (\<phi> ?T) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (\<phi> T) (\<lambda>_. x \<Ztypecolon> \<phi> T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

(* lemma [\<phi>reason for \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?S1 \<longmapsto> \<lambda>ret. ?S2\<heavy_comma>  \<blangle> ?x \<Ztypecolon> \<phi> ?T \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E\<close>]:
  \<open> SUBGOAL G G'
\<Longrightarrow> S1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> S2\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle>
\<Longrightarrow> SOLVE_SUBGOAL G'
\<Longrightarrow> \<p>\<r>\<o>\<c> Return \<phi>V_none \<lbrace> S1 \<longmapsto> \<lambda>_. S2\<heavy_comma> \<blangle> x \<Ztypecolon> \<phi> T \<brangle> \<rbrace>\<close>
  unfolding FOCUS_TAG_def Synthesis_def Action_Tag_def
  using \<phi>__Return_rule__ view_shift_by_implication by blast *)


subsubsection \<open>Fictional Refinement\<close>

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
\<Longrightarrow> YY = (\<lambda>v. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Normal v))
\<Longrightarrow> EE = (\<lambda>e. y \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> y. (x,y) \<in> Rel (Abnm e))
\<Longrightarrow> (\<And>v. Transition_of' f v \<r>\<e>\<f>\<i>\<n>\<e>\<s> Rel v \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I \<i>\<n> D)
\<Longrightarrow> Valid_Transition Rel
\<Longrightarrow> x \<in> D
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE\<close>
  using from_fictional_refinement' by blast

end

lemma "__getter_rule__":
  \<open> Valid_Proc getter
\<Longrightarrow> (\<And>ret. Transition_of' getter ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> Id_on ({x} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg v)) \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I \<i>\<n> {x})
\<Longrightarrow> \<p>\<r>\<o>\<c> getter \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> \<lambda>ret. x \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
  by (rule from_fictional_refinement[where Rel = \<open>\<lambda>ret. Id_on ({x} \<s>\<u>\<b>\<j> ret = Normal (\<phi>arg v))\<close>
                                       and D = \<open>{x}\<close>],
     assumption,
     clarsimp simp add: set_eq_iff Subjection_expn Id_on_iff ExSet_expn,
     simp add: Id_on_iff zero_set_def zero_fun_def,
     assumption,
     simp add: Valid_Transition_def zero_set_def,
     simp)

lemma "__setter_rule__":
  \<open> Valid_Proc setter
\<Longrightarrow> (\<And>ret. Transition_of' setter ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(x,y)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none
            \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I \<i>\<n> {x})
\<Longrightarrow> \<p>\<r>\<o>\<c> setter \<lbrace> x \<Ztypecolon> \<phi> Identity \<longmapsto> \<lambda>_. y \<Ztypecolon> \<phi> Identity \<rbrace>\<close>
  by (rule from_fictional_refinement
                  [where Rel=\<open>\<lambda>ret. {(x,y)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none\<close> and D = \<open>{x}\<close>],
      assumption,
      clarsimp simp add: set_eq_iff Subjection_expn Id_on_iff ExSet_expn \<phi>arg_All fun_eq_iff \<phi>V_none_def,
      simp add: Id_on_iff zero_set_def zero_fun_def,
      assumption,
      simp add: Valid_Transition_def zero_set_def,
      simp)

lemma "__allocator_rule__":
  \<open> Valid_Proc allocator
\<Longrightarrow> (\<And>ret. Transition_of' allocator ret \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1,y k)} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k
            \<w>.\<r>.\<t> R.basic_fiction o\<^sub>\<I> I \<i>\<n> {1})
\<Longrightarrow> \<p>\<r>\<o>\<c> allocator \<lbrace> Void \<longmapsto> \<lambda>ret. y k \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> k. ret = \<phi>arg k \<and> P k \<rbrace>\<close>
  by (rule from_fictional_refinement
        [where Rel=\<open>\<lambda>ret. {(1,y k)} \<s>\<u>\<b>\<j> k. ret = Normal (\<phi>arg k) \<and> P k\<close>
           and x=\<open>1\<close> and D=\<open>{1}\<close>, unfolded \<phi>_unit],
      assumption,
      clarsimp simp add: set_eq_iff Subjection_expn Id_on_iff ExSet_expn \<phi>arg_All fun_eq_iff \<phi>V_none_def,
      simp add: Id_on_iff zero_set_def zero_fun_def,
      assumption,
      simp add: Valid_Transition_def zero_set_def,
      simp)

end

(*
subsubsection \<open>Permission Fiction\<close>

locale permission_fiction =
   R: resource Res
+  share: perm_ins_homo \<psi>
+  fiction_kind FIC.DOMAIN INTERPRET Fic
      \<open>R.basic_fiction \<circ>\<^sub>\<I> (\<F>_functional \<psi>)\<close>
for Res :: "'T::sep_algebra resource_entry"
and \<psi> :: \<open>'T \<Rightarrow> 'U::{share_sep_disj,share_module_sep,sep_algebra}\<close>
and Fic :: "'U fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_functional \<psi>\<close> ..


paragraph \<open>Reasoning Rules\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end
*)



(*
subsubsection \<open>Identity Fiction\<close>

locale identity_fiction =
   R: resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_it\<close>
for Res :: "'T::sep_algebra resource_entry"
and Fic :: "'T fiction_entry"
begin

sublocale basic_fiction where I = \<open>\<F>_it\<close> ..

declare ToSA_by_structural_extraction
   [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
   [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

end
*)




section \<open>Non-separable Monolithic Resource\<close>
  \<comment> \<open>The resource non-sepable and having type shape \<^typ>\<open>'a::nonsepable_semigroup option\<close>\<close>

locale nonsepable_mono_resource =
  resource Res
for Res :: "'T nosep option resource_entry"
begin

abbreviation fiction_agree
  where \<open>fiction_agree \<equiv> basic_fiction o\<^sub>\<I> \<F>_optionwise \<F>_agree\<close>

end


subsubsection \<open>Interp Agreement\<close>

(*TODO: ('k \<Rightarrow> 'v) nosep option ----> ('k \<Rightarrow> 'v share option)
  total to that
  none to none
 *)

(*TODO!*)
locale agreement_fiction_for_nosepable_mono_resource =
   R: nonsepable_mono_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.fiction_agree\<close>
for Res :: "'T nosep option resource_entry"
and Fic :: "'T nosep agree option fiction_entry"
begin

sublocale basic_fiction Res \<open>\<F>_optionwise \<F>_agree\<close> Fic
  by (standard; simp add: raw_domain)

lemma double:
  \<open>{mk x |x. P x} \<i>\<m>\<p>\<l>\<i>\<e>\<s> {mk x |x. P x} * {mk x |x. P x}\<close>
  unfolding Imply_def
  apply (clarsimp simp add: \<phi>expns mk_homo_mult[symmetric])
  subgoal for x'
    apply (rule exI[where x=\<open>mk x'\<close>], rule exI[where x=\<open>mk x'\<close>])
    by (cases x'; simp add: mk_homo_mult[symmetric]) .

lemma contract:
  \<open>{mk x |x. P x} * {mk x |x. P x} \<i>\<m>\<p>\<l>\<i>\<e>\<s> {mk x |x. P x} \<close>
  unfolding Imply_def
  apply (clarsimp simp add: \<phi>expns)
  subgoal for x y by (cases x; cases y; simp add: mk_homo_mult[symmetric]) .

paragraph \<open>\<phi>-Type\<close>

abbreviation \<open>\<phi>_ag T \<equiv> \<phi> (Agreement (Nosep T))\<close>

declare ToSA_by_structural_extraction
    [\<phi>reason 1210 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]
declare ToSA_by_structural_extraction__reverse_morphism
    [\<phi>reason 1213 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]

lemma \<phi>_double_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nosep v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: double)
qed

lemma \<phi>_contract_\<phi>app:
  \<open>x \<Ztypecolon> \<phi>_ag T \<heavy_comma> x \<Ztypecolon> \<phi>_ag T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<phi>_ag T\<close>
proof -
  have \<open>\<exists>P. (x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close>
    unfolding set_eq_iff apply (simp add: \<phi>expns)
    apply (rule exI[where x=\<open>\<lambda>y. \<exists>v. y = Some (agree (nosep v)) \<and> v \<in> (x \<Ztypecolon> T)\<close>])
    by blast
  then obtain P where [simp]: \<open>(x \<Ztypecolon> \<phi>_ag T) = {mk x |x. P x}\<close> by blast
  show ?thesis by (simp add: contract)
qed

end



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
  apply (cases ret; clarsimp simp add: set_mult_expn Subjection_expn basic_fiction_\<I>
      mk_homo_mult)
  subgoal premises prems for r R u k
  proof -
    have [simp]: \<open>r ## 1(k := init)\<close>
      using prems(5) prems(7) sep_disj_multD2 by blast
    show ?thesis
      apply (simp add: mk_homo_mult)
      using prems(4) prems(5) prems(7) sep_disj_multI2 sep_mult_assoc by blast
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
+ fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> I\<close>
for Res :: "('key \<Rightarrow> 'val::sep_algebra) resource_entry"
and I   :: "('T::sep_algebra, 'key \<Rightarrow> 'val) interp"
and Fic :: "'T fiction_entry"
begin

sublocale basic_fiction Res I Fic ..

lemma "__allocate_rule_2__":
  \<open> (\<And>k. Id_on UNIV * {(1, 1(k := u))} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(1, u' k)} \<w>.\<r>.\<t> I \<i>\<n> {1})
\<Longrightarrow> \<forall>k. P k \<longrightarrow> 1(k := u) \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<forall>r. r \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> (\<exists>k. k \<notin> dom1 r \<and> P k)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_allocate_res_entry' P u \<lbrace> Void \<longmapsto> \<lambda>ret. u' k \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> k. ret = \<phi>arg k \<and> P k \<rbrace> \<close>
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
      assumption,
      auto simp add: set_mult_expn)

end


section \<open>One Level Parital Mapping\<close>

subsection \<open>Resource\<close>

locale partial_map_resource =
  mapping_resource Res
for Res :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
begin


subsubsection \<open>Getter\<close>

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


subsubsection \<open>Setter\<close>

lemma setter_refinement:
  \<open>(\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m k = Some any \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> Transition_of' (\<phi>R_set_res' (\<lambda>f. f(k := u))) ret
  \<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` {(Some any, u)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none \<w>.\<r>.\<t> basic_fiction \<i>\<n> fun_upd 1 k ` {Some any}\<close>
  apply (rule refinement_sub_fun[OF setter_transition[where F=\<open>\<lambda>f. f(k := u)\<close>]], assumption)
  unfolding Fictional_Forward_Simulation_def setter_transition
  apply (clarsimp simp add: basic_fiction_\<I> \<phi>expns prj.homo_mult times_fun_upd sep_disj_partial_map_upd
        nonsepable_semigroup_sepdisj_fun SPACE_mult_homo \<r>_valid_split'
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
      apply (smt (verit, ccfv_threshold) mk_homo_mult nonsepable_semigroup_sepdisj_fun prems(5) prems(9) sep_disj_clean sep_disj_mk sep_disj_multD1 sep_disj_multI1 sep_disj_multI2 sep_mult_assoc' sep_mult_left_commute t4 t5)
      by (smt (verit, best) fun_1upd_homo_right1 fun_sep_disj_1_fupdt(1) inj.sep_disj_homo mult_1_class.mult_1_left nonsepable_semigroup_sepdisj_fun sep_disj_commute sep_disj_multD1 sep_disj_multI1 sep_mult_commute t1 t2 t5)
  qed .


end


subsection \<open>Pointwise Base Fiction\<close>

locale pointwise_base_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_pointwise I\<close>
for Res :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
and I :: \<open>('fic::sep_algebra, 'val option) interp\<close>
and Fic :: "('key \<Rightarrow> 'fic) fiction_entry"
begin

sublocale fiction_base_for_mapping_resource Res \<open>\<F>_pointwise I\<close> Fic ..

lemma "_getter_rule_2_":
  \<open> refinement_projection I {x} \<subseteq> UNIV * {Some v}
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k \<lbrace> 1(k := x) \<Ztypecolon> \<phi> Identity \<longmapsto> \<lambda>ret. 1(k := x) \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
  by (rule "__getter_rule__",
      rule R.getter_valid,
      rule sep_refinement_stepwise,
      rule R.getter_refinement[THEN refinement_frame[where R=UNIV]],
      unfold Subjection_Id_on Subjection_times,
      rule refinement_subjection[OF constant_refinement],
      rule \<F>_pointwise_projection[where D'=\<open>{x}\<close> and D=\<open>{Some v}\<close>, simplified],
      assumption)

lemma "_setter_rule_2_":
  \<open> Id_on UNIV * {(Some v, u)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(v', u')} \<w>.\<r>.\<t> I \<i>\<n> {v'}
\<Longrightarrow> refinement_projection I {v'} \<subseteq> UNIV * {Some v}
\<Longrightarrow> \<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> m k = Some v \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (\<lambda>f. f(k := u))
      \<lbrace> 1(k := v') \<Ztypecolon> \<phi> Identity \<longmapsto> 1(k := u') \<Ztypecolon> \<phi> Identity \<rbrace> \<close>
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


end


subsection \<open>Pointwise Fiction\<close>

locale pointwise_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_pointwise \<F>_it\<close>
for Res :: "('key \<Rightarrow> 'val nosep option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val nosep option) fiction_entry"
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource Res \<F>_it Fic ..

lemmas setter_rule = "_setter_rule_2_"[OF \<F>_it_refinement \<F>_it_refinement_projection]
lemmas getter_rule = "_getter_rule_2_"[OF \<F>_it_refinement_projection]
lemmas allocate_rule = "__allocate_rule_2__"
                            [OF \<F>_pointwise_refinement[OF \<F>_it_refinement, where u1=1, simplified]]

end

subsection \<open>Pointwise Share Fiction\<close>

locale pointwise_share_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_pointwise (\<F>_functional to_share)\<close>
for Res :: "('key \<Rightarrow> 'val nosep option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val nosep share option) fiction_entry"
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource Res \<open>\<F>_functional to_share\<close> Fic ..

lemmas setter_rule =
  "_setter_rule_2_"[OF to_share.refinement[simplified], simplified,
                    OF to_share.refinement_projection[where S=\<open>{Some v}\<close> and n = 1 for v, simplified]]

lemmas getter_rule =
  "_getter_rule_2_"[OF to_share.refinement_projection[where S=\<open>{x}\<close> for x, simplified], simplified]

lemmas allocate_rule =
  "__allocate_rule_2__"[OF \<F>_pointwise_refinement[OF to_share.refinement[where u=\<open>1\<close>, simplified], simplified],
                        where u = \<open>Some u'\<close> for u', simplified]

end



section \<open>Two Level Parital Mapping\<close>

subsection \<open>Preliminary\<close>

definition \<open>map_fun_at g k f = (\<lambda>x. if x = k then g (f x) else f x)\<close>

lemma map_fun_at_1[simp]: \<open>map_fun_at g k 1 = 1(k := g 1)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp

lemma map_fun_at_const[simp]:
  \<open>map_fun_at (\<lambda>_. u) k f = f(k := u)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp


subsection \<open>Resource\<close>

locale partial_map_resource2 =
  mapping_resource Res
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
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
  by (smt (verit, del_insts) fun_sep_disj_imply_v fun_upd_triv mult_1_class.mult_1_right option.exhaust option.inject sep_disj_commuteI sep_disj_get_name sep_disj_multD2 sep_disj_option_nonsepable(2) sep_mult_commute)

lemma getter_valid:
  \<open>Valid_Proc (\<phi>R_get_res_entry' k k2)\<close>
  unfolding Valid_Proc_def \<phi>R_get_res_entry'_def \<phi>R_get_res'_def bind_def Return_def det_lift_def
  by (clarsimp split: option.split)

subsubsection \<open>Setter\<close>

lemma setter_refinement:
  \<open> \<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m k k2 = Some any \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H domain
\<Longrightarrow> Transition_of' (\<phi>R_set_res' (map_fun_at (map_fun_at (\<lambda>_. u) k2) k)) ret
\<r>\<e>\<f>\<i>\<n>\<e>\<s> pairself (fun_upd 1 k) ` pairself (fun_upd 1 k2) ` {(Some any, u)} \<s>\<u>\<b>\<j> ret = Normal \<phi>V_none
\<w>.\<r>.\<t> basic_fiction \<i>\<n> (fun_upd 1 k) ` (fun_upd 1 k2) ` {Some any}\<close>
  apply (rule refinement_sub_fun[OF setter_transition[where F=\<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k\<close>]], assumption)
  unfolding Fictional_Forward_Simulation_def setter_transition
  apply (clarsimp simp add: basic_fiction_\<I> \<phi>expns prj.homo_mult times_fun_upd sep_disj_partial_map_upd
        nonsepable_semigroup_sepdisj_fun SPACE_mult_homo \<r>_valid_split'
        times_fun inj.homo_mult[symmetric] inject_wand_homo)
  subgoal premises prems for r R x' u' a
  proof -
    have t1[simp]: \<open>a k k2 ## Some any\<close>
      by (metis fun_sep_disj_imply_v fun_upd_triv prems(5) prems(9) sep_disj_commuteI sep_disj_multD2)
    have t2[simp]: \<open>r k k2 ## a k k2 * Some any\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv nonsepable_semigroup_sepdisj_fun prems(5))
    have t3[simp]: \<open>r k k2 * (a k k2 * Some any) = Some any\<close>
      using t1 t2 by force
    have t4[simp]: \<open>x' = clean u' * mk (map_fun_at (map_fun_at (\<lambda>_. u) k2) k (r * (a * 1(k := 1(k2 \<mapsto> any))))) \<and> ret = Normal \<phi>V_none\<close>
      using prems(3) by fastforce
    have t5[simp]: \<open>r ## 1(k := 1(k2 := u))\<close>
      by (metis fun_sep_disj_1_fupdt(1) fun_upd_triv nonsepable_semigroup_sepdisj_fun prems(5))
    have t6[simp]: \<open>(r * a) k k2 = None\<close>
      by (metis sep_disj_multI1 sep_disj_option_nonsepable(1) t1 t2 times_fun)
    then have [simp]:
        \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (r * (a * 1(k := 1(k2 \<mapsto> any))))
            = (r * a) * 1(k := 1(k2 := u))\<close>
        unfolding map_fun_at_def fun_eq_iff times_fun_def
        by simp
    have t1[simp]: \<open>clean u' * mk a = u'\<close>
      by (metis fun_split_1 prems(8))
    show ?thesis
      apply (simp, rule exI[where x=u']; simp add: prems; rule)
      apply (smt (verit, del_insts) fun_sep_disj_1_fupdt(1) fun_upd_triv inj.homo_mult inj.sep_disj_homo_semi inject_assoc_homo nonsepable_semigroup_sepdisj_fun prems(5) prems(8) prems(9) sep_disj_multD1 sep_disj_multI1 sep_mult_commute sep_space_entry.times_fun_upd sep_space_entry_axioms times_fupdt_1_apply_sep)
      by (metis (mono_tags, lifting) fun_sep_disj_1_fupdt(1) fun_upd_triv inj.sep_disj_homo_semi nonsepable_semigroup_sepdisj_fun prems(5) prems(8) prems(9) sep_disj_multD1 sep_disj_multI1 sep_disj_multI2)
  qed .

end


subsection \<open>Pointwise Base Fiction\<close>

locale pointwise_base_fiction_for_partial_mapping_resource2 =
   R: partial_map_resource2 Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_pointwise (\<F>_pointwise I)\<close>
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
and I :: \<open>('fic::sep_algebra, 'val option) interp\<close>
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'fic) fiction_entry"
begin

sublocale fiction_base_for_mapping_resource Res \<open>\<F>_pointwise (\<F>_pointwise I)\<close> Fic ..

lemma "_getter_rule_2_":
  \<open> refinement_projection I {x} \<subseteq> UNIV * {Some v}
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry' k k2 \<lbrace> 1(k := 1(k2 := x)) \<Ztypecolon> \<phi> Identity \<longmapsto>
                                    \<lambda>ret. 1(k := 1(k2 := x)) \<Ztypecolon> \<phi> Identity \<s>\<u>\<b>\<j> ret = \<phi>arg v \<rbrace>\<close>
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
  \<open> Id_on UNIV * {(Some v, u)} \<r>\<e>\<f>\<i>\<n>\<e>\<s> {(v', u')} \<w>.\<r>.\<t> I \<i>\<n> {v'}
\<Longrightarrow> refinement_projection I {v'} \<subseteq> UNIV * {Some v}
\<Longrightarrow> \<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> m k k2 = Some v \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H R.domain
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res' (map_fun_at (map_fun_at (\<lambda>_. u) k2) k)
      \<lbrace> 1(k := 1(k2 := v')) \<Ztypecolon> \<phi> Identity \<longmapsto> 1(k := 1(k2 := u')) \<Ztypecolon> \<phi> Identity \<rbrace> \<close>
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

subsection \<open>Pointwise Fiction\<close>

locale pointwise_fiction_for_partial_mapping_resource2 =
   R: partial_map_resource2 Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_pointwise (\<F>_pointwise \<F>_it)\<close>
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val nosep option) resource_entry"
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val nosep option) fiction_entry"
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource2 Res \<F>_it Fic ..

lemmas setter_rule = "_setter_rule_2_"[OF \<F>_it_refinement \<F>_it_refinement_projection]
lemmas getter_rule = "_getter_rule_2_"[OF \<F>_it_refinement_projection]
lemmas allocate_rule = "__allocate_rule_2__"[unfolded \<F>_pointwise_\<F>_it,
                          OF \<F>_pointwise_refinement[OF \<F>_it_refinement, where u1=1, simplified, unfolded \<F>_pointwise_\<F>_it]]

end


subsection \<open>Pointwise Share Fiction\<close>

locale pointwise_share_fiction_for_partial_mapping_resource2 =
   R: partial_map_resource2 Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_pointwise (\<F>_pointwise (\<F>_functional to_share))\<close>
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val nosep option) resource_entry"
and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val nosep share option) fiction_entry"
begin

sublocale pointwise_base_fiction_for_partial_mapping_resource2 Res \<open>\<F>_functional to_share\<close> Fic ..

lemmas setter_rule =
  "_setter_rule_2_""_setter_rule_2_"[OF to_share.refinement[simplified], simplified,
                                     OF to_share.refinement_projection[where S=\<open>{Some v}\<close> and n = 1 for v, simplified]]
lemmas getter_rule =
  "_getter_rule_2_"[OF to_share.refinement_projection[where S=\<open>{x}\<close> for x, simplified], simplified]

lemmas allocate_rule =
  "__allocate_rule_2__"[OF \<F>_pointwise_refinement[OF pointwise_to_share.refinement[where u=\<open>1\<close>, simplified], simplified, unfolded to_share.\<F>_functional_pointwise]]

end




















subsection \<open>Identity Fiction\<close>

locale identity_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.basic_fiction o\<^sub>\<I> \<F>_it\<close>
for Res :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val option) fiction_entry"
begin

sublocale identity_fiction Res Fic ..

end


subsubsection \<open>Permission Fiction\<close>

locale share_fiction_for_partial_mapping_resource =
   R: partial_map_resource Res
+  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.share_fiction\<close>
for Res :: "('key \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val share option) fiction_entry"
begin

sublocale permission_fiction Res \<open>R.perm_ins_homo\<close> ..

lemma expand:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> r ## mk (R.perm_ins_homo x)
\<Longrightarrow> \<phi>Res_Spec (\<I> INTERP (r * mk (R.perm_ins_homo x))) =
    \<phi>Res_Spec (\<I> INTERP r * {R.mk x} )\<close>
  subgoal premises prems
    using expand_subj[where r=r and x=x, simplified prems(2) Subjection_True, OF prems(1)] . .

lemma partial_implies:
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k \<mapsto> Share n v))
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k \<mapsto> Share n v)))
\<Longrightarrow> R.get res k = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k \<mapsto> v)\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, ccfv_threshold) fun_split_1 fun_upd_same join_sub_def one_option_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep)

lemma partial_implies'[simp]:
  assumes FS: \<open>r \<in> FIC.SPACE\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k \<mapsto> Share n v))\<close>
    and A: \<open>\<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k \<mapsto> Share n v)))\<close>
  shows \<open>R.get res k = Some v\<close>
proof -
  from partial_implies[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

(* lemma VS_merge_ownership_identity:
  \<open> na + nb \<le> 1
\<Longrightarrow> x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<phi> (share.\<phi> (na + nb) Identity)\<close>
  by (rule VS_merge_ownership; simp add: \<phi>expns)

lemma VS_split_ownership_identity:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (0 < n \<longrightarrow> na + nb = n \<and> 0 < na \<and> 0 < nb)
\<Longrightarrow> x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<phi> (share.\<phi> na Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> nb Identity)\<close>
  by (rule VS_split_ownership; simp add: \<phi>expns sep_disj_fun_def share_fun_def; clarify)
  (* subgoal premises prems for a
    by (insert \<open>\<forall>_. _\<close>[THEN spec[where x=a]], cases \<open>x a\<close>; simp add: share_All prems) . *)


lemma VS_divide_ownership:
  \<open>FIX x \<Ztypecolon> \<phi> (share.\<phi> n Identity) \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity) \<heavy_comma> x \<Ztypecolon> \<phi> (share.\<phi> (1/2*n) Identity)\<close>
  unfolding Fix_def
  by (rule VS_split_ownership_identity; simp add: Premise_def)
*)
end

locale share_fiction_for_partial_mapping_resource_nonsepable =
  share_fiction_for_partial_mapping_resource Res Fic
for Res :: "('key \<Rightarrow> 'val nosep option) resource_entry"
and Fic :: "('key \<Rightarrow> 'val nosep share option) fiction_entry"
begin

lemma \<phi>nonsepable_normalize:
  \<open>(x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some (Nosep Identity)))))
 = (nosep x \<Ztypecolon> \<phi> (share.\<phi> (\<phi>MapAt addr (\<phi>Some Identity))))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

end



subsection \<open>Two Level Parital Mapping\<close>

definition \<open>map_fun_at g k f = (\<lambda>x. if x = k then g (f x) else f x)\<close>

lemma map_fun_at_1[simp]: \<open>map_fun_at g k 1 = 1(k := g 1)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp

lemma map_fun_at_const[simp]:
  \<open>map_fun_at (\<lambda>_. u) k f = f(k := u)\<close>
  unfolding map_fun_at_def fun_eq_iff by simp


subsubsection \<open>Locale of Resource\<close>

locale partial_map_resource2 =
  mapping_resource Res
for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
begin

lemma "__updt_rule__":
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> updt (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
      \<i>\<s> R * {mk (1(k := 1(k2 := u)))} \<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def inject_wand_homo
          prj.homo_mult times_fun_upd)
  subgoal premises prems for x aa proof -
    have [simp]: \<open>aa k k2 = None\<close>
      by (metis fun_upd_same prems(8) sep_disj_fun_def sep_disj_option_nonsepable(1))
    then have [simp]:
        \<open>map_fun_at (map_fun_at (\<lambda>_. u) k2) k (aa * 1(k := 1(k2 \<mapsto> any)))
            = aa * 1(k := 1(k2 := u))\<close>
      unfolding map_fun_at_def fun_eq_iff times_fun_def
      by simp
    have t1[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(7))
    have t2[simp]: \<open>aa ## 1(k := 1(k2 := u))\<close>
      by (simp add: sep_disj_fun_def)
    have t3[simp]:
      \<open>clean x ## (mk aa * mk (1(k := 1(k2 := u))))\<close>
      by (simp add: fun_1upd_homo)
    have t4:
      \<open>x ## mk (1(k := 1(k2 := u)))\<close>
      by (metis sep_disj_mk sep_disj_multI1 t1 t2 t3)

    show ?thesis
      apply (simp add: prems mk_homo_mult sep_mult_assoc')
      using prems(6) t4
      by (metis prems(5))
  qed .


lemma "__dispose_rule__":
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := any))}
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> updt (\<lambda>f. f(k := 1)) res \<i>\<s> R\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: \<r>_valid_split' times_set_def inject_wand_homo
          prj.homo_mult times_fun_upd )
  subgoal premises prems for x aa proof -
    have \<open>dom (aa k) = {}\<close>
    proof -
      obtain kk :: "('key2 \<Rightarrow> 'val option) \<Rightarrow> 'key2" where
        f1: "\<forall>f. 1 \<noteq> f (kk f) \<or> dom f = {}"
        by (metis dom_eq_empty_conv one_option_def)
      have "aa k ## any"
        by (metis fun_upd_same prems(9) sep_disj_fun)
      then have "\<forall>ka. 1 = aa k ka \<or> 1 = any ka"
        by (metis one_option_def option.exhaust sep_disj_fun_nonsepable(2))
      then show ?thesis
        by (metis domIff f1 mult_1_class.mult_1_right one_option_def prems(2) times_fun)
    qed
    then have t1[simp]: \<open>(aa * 1(k := any))(k := 1) = aa\<close>
      by (smt (verit, del_insts) Diff_iff dom1_upd dom_1 dom_eq_empty_conv fun_split_1_not_dom1 fun_upd_triv fun_upd_upd insertCI)
    have t2[simp]: \<open>clean x * mk aa = x\<close>
      by (metis fun_split_1 prems(8))
    show ?thesis
      using prems(10) prems(6) t1 by force
  qed .

abbreviation perm_ins_homo :: \<open>('key \<Rightarrow> 'key2 \<Rightarrow> 'val option) \<Rightarrow> ('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option)\<close>
  where \<open>perm_ins_homo \<equiv> (o) ((o) to_share)\<close>
abbreviation \<open>share_fiction \<equiv> basic_fiction o\<^sub>\<I> \<F>_functional perm_ins_homo\<close>

(*depreciated!*)
(*lemma share_fiction_expn_full':
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := to_share o f))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := f)))})\<close>
  unfolding set_eq_iff
  apply (clarify, rule;
         clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' inject_wand_homo times_fun)
  subgoal premises prems for res_r y a r
    apply (insert \<open>\<forall>x. a x * _ = _\<close>[THEN spec[where x=k], simplified,
          unfolded to_share_wand_homo[where b=f, simplified,
                      OF sep_disj_fun[where x=k, OF \<open>a ## _\<close>, simplified]]])
      apply (clarify)
      subgoal premises prems2 for a' proof -
        have t1: \<open>y = y(k := a') * 1(k := f)\<close>
          unfolding fun_eq_iff times_fun
          apply simp
          by (metis fun_upd_apply mult_1_class.mult_1_right prems2(2) times_fun_def)
        have t2: \<open>y(k := a') ## 1(k := f)\<close>
          using prems2(3) sep_disj_fun_def by fastforce
        show ?thesis
          apply (subst t1)
          apply (clarsimp simp add: times_fine'[OF t2, symmetric] mk_homo_mult mult.assoc[symmetric])
          apply (rule exI[where x="res_r * mk (Fine (y(k := a')))"], simp)
          apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (y(k := a')))"], simp add: prems)
          by (smt (verit, del_insts) mult_1_class.mult_1_right one_fun prems(4) prems2(1))
      qed .
    subgoal premises prems for res_r a fic_r r proof -
      have t1: \<open>a ## 1(k := f)\<close>
        by (metis prems(7) prems(8) sep_disj_commuteI sep_disj_multD1 sep_mult_commute)
      have t2: \<open>fic_r ## 1(k := to_share o f)\<close>
        unfolding sep_disj_fun_def
        apply (clarsimp)
        by (metis comp_apply fun_upd_same prems(4) sep_disj_fun_def t1 to_share_funcomp_sep_disj_I)

      show ?thesis
        apply (clarsimp simp add: mult.assoc mk_homo_mult[symmetric] times_fine'[OF t1])
        apply (rule exI[where x=res_r], rule exI[where x="mk (Fine (a * 1(k := f))) "],
                simp add: prems t2)
        by (smt (verit, best) fun_split_1 fun_upd_def fun_upd_same map_option_o_map_upd prems(4) sep_disj_fun t1 t2 times_fun to_share_funcomp_1 to_share_wand_homo)
    qed .

lemma share_fiction_expn_full:
  \<open>\<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> 1 \<Znrres> v)))))
 = \<phi>Res_Spec (R * \<I> share_fiction R2 * { mk (Fine (1(k := 1(k2 \<mapsto> v))))})\<close>
  using share_fiction_expn_full'[where f=\<open>1(k2 \<mapsto> v)\<close>, simplified] .

(*depreciated!*)
lemma share_fiction_partially_implies:
  \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))
\<Longrightarrow> \<exists>objs. get res = Fine objs \<and> objs k k2 = Some v\<close>
  apply (clarsimp simp add: share_fiction_def basic_fine_fiction_\<I> \<phi>expns fiction_to_share_\<I>
            mult_strip_fine_011 \<phi>Res_Spec_def \<r>_valid_split' inject_wand_homo
            proj_homo_mult)
  subgoal premises prems for res_r y a r proof -
    note t1 = \<open>a ## _\<close>[THEN sep_disj_fun[where x=k], simplified,
                 THEN sep_disj_fun[where x=k2], simplified]
    from \<open>\<forall>_. (a * _) _ = _\<close>[THEN spec[where x=k], simplified times_fun, simplified,
          THEN fun_cong[where x=k2],
          simplified times_fun, simplified]
    have t2: \<open>y k k2 = Some v\<close>
      using t1 apply (cases \<open>a k k2\<close>; cases \<open>y k k2\<close>; simp)
      by (metis sep_disj_share share.collapse share.inject times_share)

    then show ?thesis apply (simp add: t2 times_fun)
      by (metis mult_1_class.mult_1_left one_option_def prems(9) sep_disj_fun sep_disj_option_nonsepable(1) t2)
  qed .

lemma
  assumes A: \<open> res \<in> \<phi>Res_Spec (R * \<I> share_fiction (R2 * Fine (1(k := 1(k2 \<mapsto> n \<Znrres> v)))))\<close>
  shows share_fiction_partially_implies'[simp]: \<open>!!( get res) k k2 = Some v\<close>
proof -
  from A[THEN share_fiction_partially_implies]
  show ?thesis by fastforce
qed
*)

lemma raw_unit_assertion_implies[simp]:
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * { mk (1(k := 1(k2 \<mapsto> v)))}
\<Longrightarrow> get res k k2 = Some v\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' inject_wand_homo
      prj.homo_mult sep_disj_fun_def times_fun)
  by (metis (full_types) fun_upd_same sep_disj_option_nonsepable(1) times_option(3))

lemma raw_unit_assertion_implies':
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * { mk (1(k := f))}
\<Longrightarrow> f \<subseteq>\<^sub>m get res k\<close>
  unfolding \<phi>Res_Sat_def \<phi>Res_Spec_def
  apply (clarsimp simp add: times_set_def \<r>_valid_split' inject_wand_homo)
  subgoal premises prems for x a proof -
    have t1[simp]: \<open>inject a ## inject (1(k := f))\<close>
      using prems(6) by fastforce
    show ?thesis apply (clarsimp simp add: prj.homo_mult[OF t1] sep_disj_fun_def times_fun map_le_def)
      by (metis (mono_tags, lifting) fun_sep_disj_1_fupdt(1) fun_upd_triv mult_1_class.mult_1_left one_option_def prems(6) sep_disj_fun_nonsepable(2))
  qed .

lemma raw_unit_assertion_implies''[simp]:
  \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * { mk (1(k := f))}
\<Longrightarrow> k2 \<in> dom f
\<Longrightarrow> get res k k2 = f k2\<close>
  using raw_unit_assertion_implies'[unfolded map_le_def]
  by simp

end

subsubsection \<open>Permission Fiction\<close>

locale share_fiction_for_partial_mapping_resource2 =
  R: partial_map_resource2 Res
  +  fiction_kind FIC.DOMAIN INTERPRET Fic \<open>R.share_fiction\<close>
  for Res :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val::nonsepable_semigroup option) resource_entry"
    and Fic :: "('key \<Rightarrow> 'key2 \<Rightarrow> 'val share option) fiction_entry"
begin

sublocale permission_fiction Res \<open>R.perm_ins_homo\<close> ..

lemma [simp]:
  \<open>R.perm_ins_homo (1(k := f)) = 1(k := to_share o f)\<close>
  unfolding fun_eq_iff by simp

lemmas partial_implies = partial_implies_raw

lemma partial_implies':
  \<open> r \<in> FIC.SPACE
\<Longrightarrow> 0 < n
\<Longrightarrow> r ## mk (1(k := 1(k2 \<mapsto> Share n v)))
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v))))
\<Longrightarrow> R.get res k k2 = Some v\<close>
  using partial_implies_raw[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close> and n=n, simplified]
    nonsepable_partial_map_subsumption
  by (smt (verit, del_insts) fun_upd_same join_sub_def sep_disj_fun_def sep_disj_option_nonsepable(1) times_fupdt_1_apply_sep times_option(3))

lemma partial_implies'':
  assumes FS: \<open>r \<in> FIC.SPACE\<close>
    and N: \<open>0 < n\<close>
    and S: \<open>r ## mk (1(k := 1(k2 \<mapsto> Share n v)))\<close>
    and A: \<open> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP (r * mk (1(k := 1(k2 \<mapsto> Share n v)))) \<close>
  shows [simp]: \<open>R.get res k k2 = Some v\<close>
proof -
  from partial_implies'[OF FS, OF N, OF S, OF A]
  show ?thesis by fastforce
qed

end


section \<open>Common Instructions\<close>

subsection \<open>Drop & Duplicate Value\<close>

lemma [\<phi>reason 1200 for \<open>?x \<Ztypecolon> Val ?raw ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?P @action action_dup\<close>]:
  \<open>x \<Ztypecolon> Val raw T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> Val raw T \<heavy_comma> x \<Ztypecolon> Val raw T @action action_dup\<close>
  unfolding Imply_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>?R \<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?P @action action_drop\<close>]:
  \<open>Void \<heavy_comma> x \<Ztypecolon> Val raw T \<i>\<m>\<p>\<l>\<i>\<e>\<s> Void @action action_drop\<close>
  unfolding Imply_def Action_Tag_def
  by (clarsimp simp add: \<phi>expns)


subsection \<open>Abnormal\<close>

definition throw :: \<open>ABNM \<Rightarrow> 'ret proc\<close>
  where \<open>throw raw = det_lift (Abnormal raw)\<close>

lemma throw_reduce_tail[procedure_simps,simp]:
  \<open>(throw any \<ggreater> f) = throw any\<close>
  unfolding throw_def bind_def det_lift_def by simp

lemma "__throw_rule__"[intro!]:
  \<open> (\<And>a. X a \<i>\<m>\<p>\<l>\<i>\<e>\<s> X' a)
\<Longrightarrow> \<p>\<r>\<o>\<c> (throw excep :: 'ret proc) \<lbrace> X excep \<longmapsto> Any \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> X'\<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Imply_def
  apply clarsimp
  by (meson Imply_def View_Shift_def view_shift_by_implication)

lemma throw_\<phi>app:
  \<open> (\<And>v. Remove_Values (X v) (X' v))
\<Longrightarrow> \<p>\<r>\<o>\<c> throw excep \<lbrace> X excep \<longmapsto> 0 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> X' \<close>
  unfolding \<phi>Procedure_def subset_iff det_lift_def throw_def Remove_Values_def Imply_def
  apply clarsimp
  by (meson Imply_def View_Shift_def view_shift_by_implication)

definition op_try :: "'ret proc \<Rightarrow> (ABNM \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc"
  where \<open>op_try f g s = \<Union>((\<lambda>y. case y of Success x s' \<Rightarrow> {Success x s'}
                                       | Abnormal v s' \<Rightarrow> g v s'
                                       | AssumptionBroken \<Rightarrow> {AssumptionBroken}
                                       | NonTerm \<Rightarrow> {NonTerm}
                                       | Invalid \<Rightarrow> {Invalid}) ` f s)\<close>

lemma "__op_try__"[intro!]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. E v)
\<Longrightarrow> (\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 )
\<Longrightarrow> \<p>\<r>\<o>\<c> op_try f g \<lbrace> X \<longmapsto> \<lambda>v. Y1 v + Y2 v \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2  \<close>
  unfolding op_try_def \<phi>Procedure_def subset_iff
  apply clarsimp subgoal for comp R x s
    apply (cases s; simp; cases x; clarsimp simp add: \<phi>expns ring_distribs)
    subgoal premises prems for a b u v
      using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
      by (metis (no_types, lifting) INTERP_SPEC LooseStateSpec_expn(1) prems(3) prems(6) prems(7) prems(8) prems(9) set_mult_expn)
    subgoal premises prems for a b c d u v2 proof -
      have \<open>Abnormal a b \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Success c d \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E2 v))\<close>
        using prems(2)[of a, THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_SPEC prems(4) set_mult_expn)
      note this[simplified]
      then show ?thesis
        by (metis INTERP_SPEC prems(11) set_mult_expn)
    qed
    subgoal premises prems for a b c d u v proof -
      have \<open>Abnormal a b \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y1 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E v))\<close>
        using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
        using prems(10) prems(3) prems(7) prems(8) prems(9) by blast
      note this[simplified]
      then have \<open>Abnormal c d \<in> \<S> (\<lambda>v. INTERP_SPEC (R \<heavy_comma> Y2 v)) (\<lambda>v. INTERP_SPEC (R \<heavy_comma> E2 v))\<close>
        using prems(2)[THEN spec[where x=b], THEN spec[where x=R]]
        by (meson INTERP_SPEC prems(4) set_mult_expn)
      note this[simplified]
      then show ?thesis
        by (simp add: INTERP_SPEC set_mult_expn)
    qed
     apply (smt (z3) INTERP_SPEC LooseStateSpec_expn(2) LooseStateSpec_expn(3) set_mult_expn)
    by blast .

definition "Union_the_Same_Or_Arbitrary_when_Var Z X Y \<longleftrightarrow> (\<forall>v. (Z::'v \<Rightarrow> 'a set) v = X v + Y v)"

lemma Union_the_Same_Or_Arbitrary_when_Var__the_Same:
  \<open>Union_the_Same_Or_Arbitrary_when_Var Z Z Z\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by simp

lemma Union_the_Same_Or_Arbitrary_when_Var__Arbitrary:
  \<open>Union_the_Same_Or_Arbitrary_when_Var (\<lambda>v. X v + Y v) X Y\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by blast

\<phi>reasoner_ML Union_the_Same_Or_Arbitrary_when_Var 1200
  (\<open>Union_the_Same_Or_Arbitrary_when_Var ?Z ?X ?Y\<close>) = \<open>
fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Union_the_Same_Or_Arbitrary_when_Var\<close>, _)
          $ Z $ _ $ _) = Thm.major_prem_of sequent
  in (ctxt,
        (if is_Var (Envir.beta_eta_contract Z)
         then @{thm Union_the_Same_Or_Arbitrary_when_Var__Arbitrary}
         else @{thm Union_the_Same_Or_Arbitrary_when_Var__the_Same})
        RS sequent) |> Seq.single
  end
\<close>

proc (nodef) try'':
  assumes F: \<open>\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  assumes G: \<open>(\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE2 )\<close>
  input  X
    output YY
  throws EE2
  \<medium_left_bracket> "__op_try__"
    F
    G
  \<medium_right_bracket> .

proc (nodef) try':
  assumes A: \<open>Union_the_Same_Or_Arbitrary_when_Var Z Y1 Y2\<close>
  assumes F: \<open>\<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> Y1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  assumes G: \<open>\<And>v. \<p>\<r>\<o>\<c> g v \<lbrace> E v \<longmapsto> Y2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E2 \<close>
  input  X
    output Z
  throws E2
  \<medium_left_bracket> "__op_try__" F G
    unfold A[unfolded Union_the_Same_Or_Arbitrary_when_Var_def, THEN spec, symmetric]
  \<medium_right_bracket>.


subsection \<open>Access the Resource\<close>

subsubsection \<open>Legacy\<close>

definition \<phi>M_get_res :: \<open>(resource \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>M_get_res R F = (\<lambda>res. F (R res) res)\<close>

definition \<phi>M_get_res_entry :: \<open>(resource \<Rightarrow> ('k \<rightharpoonup> 'a)) \<Rightarrow> 'k \<Rightarrow> ('a \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>M_get_res_entry R k F =
    \<phi>M_get_res R (\<lambda>res. case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition \<phi>M_set_res :: \<open> (('x \<Rightarrow> 'x) \<Rightarrow> resource \<Rightarrow> resource) \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> unit proc \<close>
  where \<open>\<phi>M_set_res Updt F = (\<lambda>res. {Success (\<phi>arg ()) (Updt F res)})\<close>

subsubsection \<open>Getters\<close>

paragraph \<open>basic resource\<close>

context resource begin


lemma \<phi>R_get_res[intro!]:
  \<open> get res = v
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_def subset_iff by simp

end

paragraph \<open>nonsepable_mono_resource\<close>

definition (in nonsepable_mono_resource) \<phi>R_get_res_entry :: \<open>('T \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_get_res_entry F = \<phi>R_get_res (\<lambda>v. case v of Some v' \<Rightarrow> F (nosep.dest v')
                                                      | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in nonsepable_mono_resource) \<phi>R_get_res_entry:
  \<open> get res = Some (nosep v)
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res_entry F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

paragraph \<open>partial_map_resource\<close>

definition (in partial_map_resource)
  \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> ('val \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_get_res_entry k F =
    \<phi>R_get_res (\<lambda>res. case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition (in partial_map_resource)
  \<phi>R_get_res_entry' :: \<open>'key \<Rightarrow> 'val proc\<close>
  where \<open>\<phi>R_get_res_entry' k =
    \<phi>R_get_res' \<bind> (\<lambda>res. case \<phi>arg.dest res k of Some v \<Rightarrow> Return (\<phi>arg v) | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

lemma (in partial_map_resource) \<phi>R_get_res_entry[intro!]:
  \<open> get res k = Some v
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res_entry k F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

subparagraph \<open>identity_fiction_for_partial_mapping_resource\<close>

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_get_res_entry_frm[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry key F
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_Hybrid_DL \<phi>Res_Spec_expn_R imp_conjL
            \<phi>Res_Sat_expn_impEx \<phi>Res_Sat_expn_impSubj
  by (clarsimp simp add: \<phi>expns expand; rule R.\<phi>R_get_res_entry[where v=v]; simp)

lemmas \<phi>R_get_res_entry[intro!] = \<phi>R_get_res_entry_frm[where R=1, simplified]

end

subparagraph \<open>share_fiction_for_partial_mapping_resource\<close>

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_get_res_entry_frm[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry key F
      \<lbrace> R\<heavy_comma> v \<Ztypecolon> \<phi> (key \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_Hybrid_DL
    \<phi>Res_Spec_expn_R \<phi>Res_Sat_expn_impEx \<phi>Res_Sat_expn_impSubj imp_conjL
  apply (clarsimp simp add: \<phi>expns zero_set_def)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

lemmas \<phi>R_get_res_entry[intro!] = \<phi>R_get_res_entry_frm[where R=1, simplified]

end

paragraph \<open>partial_map_resource2\<close>

definition (in partial_map_resource2) \<comment> \<open>depreciated\<close>
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> ('val \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_get_res_entry k k2 F = \<phi>R_get_res (\<lambda>res.
    case res k k2 of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>

definition (in partial_map_resource2)
  \<phi>R_get_res_entry' :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> 'val proc\<close>
  where \<open>\<phi>R_get_res_entry' k k2 =
    \<phi>R_get_res' \<bind> (\<lambda>res. case \<phi>arg.dest res k k2 of Some v \<Rightarrow> Return (\<phi>arg v) | _ \<Rightarrow> (\<lambda>_. {Invalid}))\<close>


lemma (in partial_map_resource2) \<phi>R_get_res_entry[intro!]:
  \<open> get res k k2 = Some v
\<Longrightarrow> F v res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<phi>R_get_res_entry k k2 F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def)
  apply (rule R.\<phi>R_get_res_entry[where v=v])
  apply simp
  by blast

lemma (in share_fiction_for_partial_mapping_resource2) \<phi>R_get_res_entry1[intro!]:
  \<open>\<p>\<r>\<o>\<c> F v
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_get_res_entry k1 k2 F
      \<lbrace> v \<Ztypecolon> \<phi> (k1 \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  using \<phi>R_get_res_entry[where n=1, simplified] .


subsubsection \<open>Setters\<close>

definition (in resource) \<phi>R_set_res :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> unit proc\<close>
  where \<open>\<phi>R_set_res F = (\<lambda>res. {Success (\<phi>arg ()) (updt F res)})\<close>

definition (in resource) \<phi>R_set_res' :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> unit proc\<close>
  where \<open>\<phi>R_set_res' F = (\<lambda>res. if updt F res \<in> SPACE
                                then {Success (\<phi>arg ()) (updt F res)}
                                else {Invalid})\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_set_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R * {mk (1(k := u))}) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def
  by (simp add: \<phi>expns "__updt_rule__")

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_set_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k \<mapsto> u) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. (\<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))}) \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def
          expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
          expand_subj[where x=\<open>1(k \<mapsto> u)\<close>, simplified])
  subgoal for r res
    thm R.\<phi>R_set_res[where k=k and res=res]
    by (rule R.\<phi>R_set_res[where k=k and res=res], assumption, simp, assumption) .

declare \<phi>R_set_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_set_res_frm[intro!] = \<phi>R_set_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]
end

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_set_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k \<mapsto> u) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def
          expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified]
          expand_subj[where x=\<open>1(k \<mapsto> u)\<close>, simplified])
  subgoal for r res
    by (rule R.\<phi>R_set_res[where k=k and res=res], assumption, simp, assumption) .

declare \<phi>R_set_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_set_res_frm[intro!] = \<phi>R_set_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]

end


paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_set_res[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := 1(k2 \<mapsto> any)))}
\<Longrightarrow> \<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
      \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R * {mk (1(k := 1(k2 := u)))}) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__")

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_set_res"[THEN \<phi>CONSEQ'E0, intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k) m \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k := 1(k2 \<mapsto> v)))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some u) k2) k)
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> k2 \<^bold>\<rightarrow> \<fish_eye> Identity) \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def
                            expand[where x=\<open>1(k := 1(k2 \<mapsto> v))\<close>, simplified]
                            expand_subj[where x=\<open>1(k := 1(k2 \<mapsto> u))\<close>, simplified])
  subgoal for r res
    by (rule R.\<phi>R_set_res, assumption, simp, assumption) .


subsubsection \<open>Dispose\<close>

paragraph \<open>partial_map_resource\<close>

lemma (in partial_map_resource) \<phi>R_dispose_res[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k := None) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k \<mapsto> any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := None)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__")

context identity_fiction_for_partial_mapping_resource begin

lemma \<phi>R_dispose_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k := None) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k := None))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified])
  subgoal for r res
    by (rule R.\<phi>R_dispose_res, assumption, simp, simp) .

declare \<phi>R_dispose_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_dispose_res_frm[intro!] = \<phi>R_dispose_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]

end

context share_fiction_for_partial_mapping_resource begin

lemma \<phi>R_dispose_res:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k := None) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k \<mapsto> v))} \<Longrightarrow> P (R.get res))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k := None))
         \<lbrace> v \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> \<fish_eye> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k \<mapsto> v)\<close>, simplified])
  subgoal for r res by (rule R.\<phi>R_dispose_res, assumption, simp, simp) .

declare \<phi>R_dispose_res[THEN \<phi>CONSEQ'E0, intro!]
lemmas \<phi>R_dispose_res_frm[intro!] = \<phi>R_dispose_res[THEN \<phi>frame, simplified, THEN \<phi>CONSEQ'E0[simplified zero_fun_def]]

end

paragraph \<open>partial_map_resource2\<close>

lemma (in partial_map_resource2) \<phi>R_dispose_res[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> dom (get res k) = dom any
\<Longrightarrow> P (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := any))}
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := 1)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__")

lemma (in share_fiction_for_partial_mapping_resource2) "\<phi>R_dispose_res"[THEN \<phi>CONSEQ'E0, intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> P m \<longrightarrow> m(k := 1) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>res r. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> \<I> INTERP r * {R.mk (1(k := f))}
      \<Longrightarrow> P (R.get res) \<and> dom f = dom (R.get res k))
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_set_res (\<lambda>f. f(k := 1))
         \<lbrace> to_share o f \<Ztypecolon> \<phi> (k \<^bold>\<rightarrow> Identity) \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL
  apply (clarsimp simp add: \<phi>expns zero_set_def expand[where x=\<open>1(k := f)\<close>, simplified])
  subgoal for r res
    apply (rule R.\<phi>R_dispose_res, assumption, standard, simp)
    subgoal premises prems proof -
      have t1: \<open>dom f = dom (R.get res k)\<close>
        using prems(2) prems(3) by blast
      have t2: \<open>f \<subseteq>\<^sub>m R.get res k\<close>
        using R.raw_unit_assertion_implies' prems(3) by blast
      have t3: \<open>R.get res k = f\<close>
        by (metis (no_types, lifting) map_le_antisym map_le_def t1 t2)
      show ?thesis
        using prems(3) t3 by blast
    qed . .

subsubsection \<open>Allocate\<close>

context mapping_resource begin

definition
    \<phi>R_allocate_res_entry :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> ('key \<Rightarrow> 'ret proc)
                           \<Rightarrow> 'ret proc\<close>
  where \<open>\<phi>R_allocate_res_entry P init F =
    \<phi>R_get_res (\<lambda>res.
    let k = (@k. res k = 1 \<and> P k)
     in \<phi>R_set_res (\<lambda>f. f(k := init))
        \<ggreater> F k
)\<close>

definition
    \<phi>R_allocate_res_entry' :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> 'key proc\<close>
  where \<open>\<phi>R_allocate_res_entry' P init =
    \<phi>R_get_res (\<lambda>res.
    let k = (@k. res k = 1 \<and> P k)
     in \<phi>R_set_res (\<lambda>f. f(k := init))
        \<ggreater> Return (\<phi>arg k)
)\<close>

lemma \<phi>R_set_res_new[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m(k := u) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> k \<notin> dom1 (get res)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> (\<lambda>_. R * {mk (1(k := u))}) \<t>\<h>\<r>\<o>\<w>\<s> Any\<close>
  unfolding \<phi>R_set_res_def
  by (simp add: \<phi>expns "__allocation_rule__")

lemma \<phi>R_allocate_res_entry[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in>\<^sub>S\<^sub>H domain \<longrightarrow> m(k := init) \<in>\<^sub>S\<^sub>H domain)
\<Longrightarrow> (\<And>k res. \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R * {mk (1(k := init))} \<s>\<u>\<b>\<j> P k
      \<Longrightarrow> F k res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<s>\<t>\<a>\<t>\<e> res \<i>\<s> R
\<Longrightarrow> \<phi>R_allocate_res_entry P init F res \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> Y \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding \<phi>R_allocate_res_entry_def \<phi>R_get_res_def
  subgoal premises prems proof -
    let ?m = \<open>get res\<close>
    define k' where \<open>k' = (SOME k. ?m k = 1 \<and> P k)\<close>
    have \<open>\<exists>k'. ?m k' = 1 \<and> P k'\<close>
      using get_res_Valid prems(1) prems(4) by blast
    note this[THEN someI_ex]
    then have t1[simp]: \<open>?m k' = 1 \<and> P k'\<close> unfolding k'_def by blast
    show ?thesis
      unfolding k'_def[symmetric]
      apply (simp, rule \<phi>M_RS_WP_SEQ, rule \<phi>R_set_res_new)
      using prems(2) t1 apply blast
      apply (simp add: dom1_def)
      using \<open>\<s>\<t>\<a>\<t>\<e> res \<i>\<s> _\<close> apply this
      by (simp add: prems(3))
  qed .

end

lemma (in identity_fiction_for_partial_mapping_resource) "\<phi>R_allocate_res_entry"[intro!]:
  \<open> (\<forall>m. m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in>\<^sub>S\<^sub>H R.domain \<longrightarrow> m(k \<mapsto> init) \<in>\<^sub>S\<^sub>H R.domain)
\<Longrightarrow> (\<And>new. P new \<Longrightarrow> \<p>\<r>\<o>\<c> F new \<lbrace> X \<heavy_comma> init \<Ztypecolon> \<phi> (new \<^bold>\<rightarrow> \<black_circle> Identity) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> R.\<phi>R_allocate_res_entry P (Some init) F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
 apply (clarsimp simp add: \<phi>expns \<phi>Procedure_Hybrid_DL)
  subgoal for r res c
  apply (rule R.\<phi>R_allocate_res_entry[where R="(\<I> INTERP (r * c))"])
  apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp)
  subgoal premises prems for k res'
  apply (rule prems(3)[OF \<open>P _\<close>, THEN spec[where x=r], THEN spec[where x=res'],
              simplified prems, simplified, THEN mp])
    apply (rule exI[where x=\<open>c * mk (1(k \<mapsto> init))\<close>])
    apply rule
    apply (smt (verit, ccfv_threshold) SPACE_mult_homo expand prems(6) prems(7) prems(8) prems(9) sep_disj_commute sep_disj_fiction sep_disj_multD2 sep_mult_commute sep_mult_left_commute)
    apply rule
    using FIC.SPACE_mult_homo prems(5) prems(6) prems(7) prems(8) prems(9) sep_disj_fiction sep_disj_multD2 apply blast
    by (metis Fic_Space_m SPACE_mult_homo identity_fiction.sep_disj_fiction identity_fiction_axioms prems(6) prems(7) prems(8) prems(9) sep_disj_multD2 sep_disj_multI2)
  . .



(*


(*
subsection \<open>Tuple Operations\<close>



subsubsection \<open>Construct Tuple\<close>

definition cons_tup :: "TY list \<Rightarrow> VAL list \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "cons_tup tys vs = (
    let N = length tys in
    \<phi>M_assert (N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (rev (take N vs)) tys)
    \<ggreater> Success (V_tup.mk (rev (take N vs))))"

lemma cons_tup_nil:
  \<open>cons_tup [] = \<phi>M_put_Val (V_tup.mk [])\<close>
  unfolding cons_tup_def \<phi>M_put_Val_def
  by simp

lemma cons_tup_cons:
  \<open>cons_tup (TY#TYs) =
    cons_tup TYs \<ggreater>
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (V_tup.mk [v] * tup)
    ))\<close>
  apply (auto split: list.split
    simp add: cons_tup_def fun_eq_iff pair_forall instr_comp_def bind_def
    \<phi>M_get_Val_def \<phi>M_assert_def \<phi>M_put_Val_def Let_def V_tup_mult)
  apply (metis Suc_le_eq list.sel(1) take_hd_drop)
  apply (metis Cons_nth_drop_Suc Suc_le_eq list.sel(3))
  apply (metis Suc_le_eq drop_all leI list.simps(3))
  apply (metis (no_types, lifting) drop_all leI list.ctr_transfer(1) list.sel(1) list.simps(3) list_all2_Cons2 list_all2_appendI list_all2_rev1 rev.simps(2) take_hd_drop)
  apply (smt (verit, del_insts) Suc_le_eq append1_eq_conv list.sel(1) list_all2_Cons2 rev_eq_Cons_iff take_hd_drop)
  by (simp add: take_Suc_conv_app_nth)

lemma (in \<phi>empty) op_cons_tup_nil:
  \<open> \<p>\<r>\<o>\<c> cons_tup [] \<lbrace> Void \<longmapsto> () \<Ztypecolon> EmptyTuple \<rbrace>\<close>
  unfolding cons_tup_nil by \<phi>reason

lemma (in \<phi>empty) op_cons_tup_cons:
  \<open> \<p>\<r>\<o>\<c> cons_tup TYs \<lbrace> X \<longmapsto> VAL y \<Ztypecolon> Y \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> cons_tup (TY#TYs) \<lbrace> VAL a \<Ztypecolon> A\<heavy_comma> X \<longmapsto> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> Y) \<rbrace>\<close>
  unfolding cons_tup_cons
  apply \<phi>reason apply (rule \<phi>frame0, assumption)
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  apply \<phi>reason apply (simp add: \<phi>expns) by blast


subsubsection \<open>Destruct Tuple\<close>


definition op_dest_tup :: "TY list \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "op_dest_tup tys =
    \<phi>M_getV (\<tau>Tuple tys) V_tup.dest (\<lambda>tup.
    \<lambda>(vs, res). Success (rev tup@vs, res))"

lemma op_dest_tup_nil_expn:
  \<open>op_dest_tup [] = \<phi>M_getV (\<tau>Tuple []) V_tup.dest (\<lambda>_. SKIP)\<close>
  by (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)

lemma op_dest_tup_cons_expn:
  \<open>op_dest_tup (TY#TYs) =
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_assert (\<exists>h tup'. tup = V_tup.mk (h#tup') \<and> h \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (hd (V_tup.dest tup)) \<ggreater>
    \<phi>M_put_Val (V_tup.mk (tl (V_tup.dest tup))) \<ggreater>
    op_dest_tup TYs)\<close>
  apply (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)
  by (metis list.discI list.exhaust_sel list.rel_sel list.sel(1))

lemma (in \<phi>empty) op_dest_tup_nil:
  \<open>\<p>\<r>\<o>\<c> op_dest_tup [] \<lbrace> () \<Ztypecolon> EmptyTuple \<longmapsto> Void \<rbrace> \<close>
  unfolding op_dest_tup_nil_expn by \<phi>reason

lemma (in \<phi>empty) op_dest_tup_cons:
  \<open> \<p>\<r>\<o>\<c> op_dest_tup TYs \<lbrace> VAL y \<Ztypecolon> Y \<longmapsto> X \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_dest_tup (TY#TYs) \<lbrace> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> \<phi>Is_Tuple Y) \<longmapsto> VAL a \<Ztypecolon> A\<heavy_comma> X \<rbrace>\<close>
  unfolding op_dest_tup_cons_expn
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  by (rule \<phi>frame0, assumption)



subsubsection \<open>Accessing Elements\<close>


definition op_get_element :: "nat list \<Rightarrow> TY \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "op_get_element idx TY =
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx) \<ggreater>
    \<phi>M_put_Val (index_value idx v))"

definition op_set_element :: "nat list \<Rightarrow> TY \<Rightarrow> (VAL,'RES_N,'RES) proc"
  where "op_set_element idx TY =
    \<phi>M_get_Val (\<lambda>u.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx \<and> u \<in> Well_Type (index_type idx TY)) \<ggreater>
    \<phi>M_put_Val (index_mod_value idx (\<lambda>_. u) v)
  ))"

lemma (in \<phi>empty) op_get_element:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> valid_index TY idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_element idx TY \<lbrace> VAL x \<Ztypecolon> X \<longmapsto> VAL f x \<Ztypecolon> Y \<rbrace> \<close>
  unfolding op_get_element_def \<phi>Index_getter_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason

lemma (in \<phi>empty) op_set_element:
  \<open> \<s>\<i>\<m>\<p>\<r>\<e>\<m> valid_index TY idx
\<Longrightarrow> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> Y) (index_type idx TY)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_element idx TY \<lbrace> VAL x \<Ztypecolon> X\<heavy_comma> VAL y \<Ztypecolon> Y \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> X \<rbrace>\<close>
  unfolding op_set_element_def \<phi>Index_mapper_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
   apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason


*)

*)


end