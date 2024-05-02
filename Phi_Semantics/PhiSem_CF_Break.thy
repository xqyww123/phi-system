theory PhiSem_CF_Break
  imports Phi_System.Resource_Template
begin

section \<open>Semantic Model\<close>

subsection \<open>Abnormal\<close>

virtual_datatype \<phi>CF_break_abnormal = \<phi>empty_abnormal +
  ABN_break    :: unit

debt_axiomatization ABN_break :: \<open>unit abnormal_entry\<close>
  where \<phi>CF_break_abnormal_ax: \<open>\<phi>CF_break_abnormal ABN_CONS_OF ABN_break\<close>

interpretation \<phi>CF_break_abnormal ABN_CONS_OF _ _ ABN_break
  using \<phi>CF_break_abnormal_ax .

hide_fact \<phi>CF_break_abnormal_ax


subsection \<open>Resource of Scope Frames\<close>


setup \<open>Sign.mandatory_path "RES"\<close>

type_synonym brk_label = nat
type_synonym brk_frame = \<open>RES.brk_label \<rightharpoonup> VAL list option discrete\<close>

setup \<open>Sign.parent_path\<close>

resource_space \<phi>CF_break =
  brk_frame :: \<open>{frames::RES.brk_frame. finite (dom frames)}\<close>
    (partial_map_resource \<open>\<lambda>_::nat. UNIV :: VAL list option discrete set\<close>)
  by (standard; simp; metis domIff notin_range_Some)

hide_fact RES.\<phi>CF_break_res_ax


subsection \<open>Fiction of Scope Frames\<close>

fiction_space \<phi>CF_break =
  brk_frame :: \<open>RES.brk_frame.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>_. \<F>_it)\<close>
               (pointwise_fiction_for_partial_mapping_resource RES.brk_frame \<open>\<lambda>_::nat. UNIV :: VAL list option discrete set\<close>)
  by (standard; simp add: set_eq_iff)

hide_fact FIC.\<phi>CF_break_fic_ax


section \<open>\<phi>-Types\<close>

(*
abbreviation Brk_Frame' :: \<open>brk_label \<Rightarrow> (VAL list option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Brk_Frame' label T \<equiv> (FIC.brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Discrete T)))\<close>
*)

definition Brk_Frame :: \<open>RES.brk_label \<Rightarrow> assn\<close>
  where \<open>Brk_Frame label \<equiv> () \<Ztypecolon> FIC.brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Discrete \<circle>))\<close>

definition Brking_Frame :: \<open>RES.brk_label \<Rightarrow> ('v::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> assn\<close> ("\<^bold>b\<^bold>r\<^bold>o\<^bold>k\<^bold>e\<^bold>n _ \<w>\<i>\<t>\<h> _" [1000,10] 3)
  where \<open>Brking_Frame label S =
     (\<exists>*v. to_vals (\<phi>arg.dest v) \<Ztypecolon> FIC.brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Discrete (\<black_circle> Itself)))\<heavy_comma> S v)\<close>

ML \<open>Phi_Syntax.register_connective (\<^const_name>\<open>Brking_Frame\<close>, 1)\<close>

lemma [\<phi>reason %abstract_domain]:
  \<open> Brk_Frame X \<i>\<m>\<p>\<l>\<i>\<e>\<s> True \<close>
  unfolding \<r>EIF_def
  by simp

lemma [\<phi>reason %abstract_domain]:
  \<open> (\<And>v. S v \<i>\<m>\<p>\<l>\<i>\<e>\<s> P v)
\<Longrightarrow> Brking_Frame label S \<i>\<m>\<p>\<l>\<i>\<e>\<s> Ex P \<close>
  unfolding Action_Tag_def Inhabited_def Brking_Frame_def \<r>EIF_def
  by clarsimp blast

lemma Brk_Frame_eq_identity:
  \<open>Brk_Frame l = (discrete None \<Ztypecolon> FIC.brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Itself))\<close>
  unfolding BI_eq_iff Brk_Frame_def
  by simp

lemma Brk_Frame_eq_identity':
  \<open> Brk_Frame l = (1(l \<mapsto> discrete None) \<Ztypecolon> FIC.brk_frame.\<phi> Itself) \<close>
  unfolding BI_eq_iff Brk_Frame_def
  by simp

lemma Brk_Frame_eq_identity'2:
  \<open>(1(l := None) \<Ztypecolon> FIC.brk_frame.\<phi> Itself) = 1\<close>
  unfolding BI_eq_iff Brk_Frame_def
  by simp

lemma Brking_Frame_eq_identity:
  \<open>Brking_Frame l S = (\<exists>*v. discrete (Some (to_vals (\<phi>arg.dest v))) \<Ztypecolon> FIC.brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Itself)\<heavy_comma> S v)\<close>
  unfolding BI_eq_iff Brking_Frame_def
  by simp



section \<open>Instruction\<close>

definition \<open>sift_brking_frame' l Y E = (Brking_Frame l Y) + (TECHNICAL Brk_Frame l\<heavy_comma> E)\<close>
definition sift_brking_frame ("\<b>\<r>\<e>\<a>\<k> _/ \<w>\<i>\<t>\<h> _/ \<o>\<r> _" [1000,10,3] 3)
  where \<open>sift_brking_frame = sift_brking_frame'\<close>

declare sift_brking_frame'_def[folded sift_brking_frame_def, assertion_simps_source]


declare [[\<phi>hide_techinicals=false]]

proc op_brk_scope:
  requires BLK: \<open>(\<And>l. \<p>\<r>\<o>\<c> f l \<lbrace> TECHNICAL Brk_Frame l\<heavy_comma> X \<longmapsto> \<lambda>ret. TECHNICAL Brk_Frame l \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y ret \<rbrace>
                      \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>a. sift_brking_frame l Y' (E a)))\<close>
  input  \<open>X\<close>
  output \<open>\<lambda>ret. Y ret + Y' ret\<close>
  throws E
\<medium_left_bracket>
  apply_rule FIC.brk_frame.allocate_rule[where P=\<open>\<lambda>_. True\<close> and u=\<open>Some (discrete None)\<close>] \<exists>l
  try'' \<medium_left_bracket>
    fold Brk_Frame_eq_identity'

    have BLK': \<open>\<p>\<r>\<o>\<c> f (\<phi>arg.dest \<v>0) \<lbrace> Brk_Frame l\<heavy_comma> X \<longmapsto> \<lambda>ret. Brk_Frame l \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y ret \<rbrace>
                \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>a. \<b>\<r>\<e>\<a>\<k> l \<w>\<i>\<t>\<h> Y' \<o>\<r> E a) \<close>
      by (simp add: useful BLK[of \<open>l\<close>, unfolded Technical_def, simplified]) ;;

    apply_rule BLK'
    apply_rule FIC.brk_frame.setter_rule[where k=\<open>\<phi>arg.dest \<v>0\<close> and k=l and v=\<open>discrete None\<close> and u=\<open>None\<close>,
                                         folded Brk_Frame_eq_identity' Brk_Frame_eq_identity'2[symmetric]]

  \<medium_right_bracket> for \<open>Y \<v>1 + Y' \<v>1\<close>
  \<medium_left_bracket> for \<e> 
    unfold sift_brking_frame_def
    unfold sift_brking_frame'_def
    unfold Technical_def
    case_analysis \<medium_left_bracket>
      unfold Brk_Frame_eq_identity'
      apply_rule FIC.brk_frame.getter_rule[where k=\<open>\<phi>arg.dest \<v>0\<close> and k=l]
      apply_rule FIC.brk_frame.setter_rule[where k=\<open>\<phi>arg.dest \<v>0\<close> and k=l and u=None]
      Brk_Frame_eq_identity'2

      have thrw: \<open>\<p>\<r>\<o>\<c> (case discrete.dest (\<phi>arg.dest \<v>1) of Some vs \<Rightarrow> Return (\<phi>arg (from_vals vs))
                                                        | None \<Rightarrow> throw \<e>)
                       \<lbrace> E \<e> \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
        by (simp add: useful "__throw_rule__") ;;

      thrw
    \<medium_right_bracket> \<medium_left_bracket>
      Brking_Frame_eq_identity
      to \<open>FIC.brk_frame.\<phi> Itself\<close>
      apply_rule FIC.brk_frame.getter_rule[where k=\<open>\<phi>arg.dest \<v>0\<close> and k=l]
      apply_rule FIC.brk_frame.setter_rule[where k=\<open>\<phi>arg.dest \<v>0\<close> and k=l and u=None]
      Brk_Frame_eq_identity'2

      have thrw: \<open>\<p>\<r>\<o>\<c> (case discrete.dest (\<phi>arg.dest \<v>1) of Some vs \<Rightarrow> Return (\<phi>arg (from_vals vs))
                                                        | None \<Rightarrow> throw \<e>)
                       \<lbrace> Y' v \<longmapsto> Y' \<rbrace> \<close>
        by (simp add: useful "__Return_rule__") ;;

      thrw
    \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc op_break:
  input \<open>TECHNICAL Brk_Frame l\<heavy_comma> S vs\<close>
  output \<open>0 :: 'ret \<phi>arg \<Rightarrow> assn\<close>
  throws \<open>\<lambda>_. Brking_Frame l S\<close>
\<medium_left_bracket>
  unfold Technical_def
  unfold Brk_Frame_eq_identity'
  apply_rule FIC.brk_frame.setter_rule [where u=\<open>Some (discrete (Some (to_vals (\<phi>arg.dest vs))))\<close>]
  apply_rule Brking_Frame_eq_identity[symmetric, where S=S]
  apply_rule throw[where 'a='ret] \<open>ABN_break.mk ()\<close>
\<medium_right_bracket> .

lemma op_break_reduce_tail[procedure_simps,simp]:
  \<open>(op_break TYPE('ret) TYPE('val::VALs) L v \<ggreater> f) = op_break TYPE('ret2) TYPE('val::VALs) L v\<close>
  unfolding op_break_def by simp


section \<open>Reasoning Processes\<close>

subsection \<open>ToA of Brk_Frame\<close>

\<phi>reasoner_group ToA_brk_frame = (%ToA_cut, [%ToA_cut, %ToA_cut+10]) in ToA_cut
  \<open>ToA rules about \<open>Brk_Frame\<close>\<close>

text \<open>Covered by ToA-refl:

\<^item> \<open> TECHNICAL Brk_Frame l \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brk_Frame l \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top> \<close>
\<^item> \<open> R * TECHNICAL Brk_Frame l \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brk_Frame l \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<close>
\<close>

lemma [\<phi>reason %ToA_brk_frame+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> l = l'
\<Longrightarrow> TECHNICAL Brk_Frame l \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brk_Frame l' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top> \<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma [\<phi>reason %ToA_brk_frame+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> l = l'
\<Longrightarrow> TECHNICAL Brk_Frame l\<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brk_Frame l' \<r>\<e>\<m>\<a>\<i>\<n>\<s> X \<close>
  unfolding Premise_def \<r>Guard_def
  by simp

lemma [\<phi>reason %ToA_brk_frame]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> TECHNICAL Brk_Frame l\<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> TECHNICAL Brk_Frame l\<heavy_comma> R \<w>\<i>\<t>\<h> P \<close>
  by (simp, metis (no_types, opaque_lifting) mult.assoc mult.commute transformation_right_frame)

lemma [\<phi>reason %ToA_brk_frame]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brk_Frame l \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> X\<heavy_comma> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brk_Frame l \<r>\<e>\<m>\<a>\<i>\<n>\<s> X\<heavy_comma> R' \<w>\<i>\<t>\<h> P \<close>
  by (simp, metis mult.assoc mult.commute transformation_left_frame)


subsection \<open>sift brking frame\<close>

\<phi>reasoner_group entry_of_sift_brking_frame = (%ToA_normalizing, [%ToA_normalizing, %ToA_normalizing+10])
                                              in ToA_normalizing
      \<open>entry point of sift_brking_frame\<close>
  and sift_brking_frame = (1730, [1700,1730]) in ToA_assertion_cut
      \<open>\<close>

declare [[\<phi>reason_default_pattern
     \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' ?l ?Y ?E \<w>\<i>\<t>\<h> ?Any\<close>
  \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' ?l _ _ \<w>\<i>\<t>\<h> _\<close> (1000)
 and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame ?l ?Y ?E \<w>\<i>\<t>\<h> ?Any\<close>
  \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame ?l _ _ \<w>\<i>\<t>\<h> _\<close>  (1000)]]


lemma [\<phi>reason %entry_of_sift_brking_frame+10 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame ?l ?var_Y' ?var_E' \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E \<w>\<i>\<t>\<h> P
\<Longrightarrow> (\<And>v. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps SOURCE] (Y' v) : Y v)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps ABNORMAL] E' : E
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame  l Y' E' \<w>\<i>\<t>\<h> P\<close>
  unfolding sift_brking_frame_def Simplify_def
  by simp presburger

lemma [\<phi>reason %entry_of_sift_brking_frame]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E \<w>\<i>\<t>\<h> P\<^sub>X
\<Longrightarrow> (\<And>v. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps SOURCE] (Y'' v) : Y v)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps ABNORMAL] E'' : E
\<Longrightarrow> (\<And>v. Y'' v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y' v \<w>\<i>\<t>\<h> P\<^sub>Y v)
\<Longrightarrow> E'' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> E' \<w>\<i>\<t>\<h> P\<^sub>E
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame  l Y' E' \<w>\<i>\<t>\<h> P\<^sub>X \<and> (Ex P\<^sub>Y \<or> P\<^sub>E)\<close>
  unfolding sift_brking_frame_def sift_brking_frame'_def
            Transformation_def Brking_Frame_eq_identity
            Action_Tag_def Simplify_def
  by clarsimp blast

(*Y, E in \<open>sift_brking_frame' l Y E\<close> are always schematic variables*)

lemma [\<phi>reason 3000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame ?l ?Y ?E \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame l Y E \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame l Y E \<r>\<e>\<m>\<a>\<i>\<n>\<s> 1 \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by simp


lemma Brking_Frame_plus:
  \<open>Brking_Frame l (Y1 + Y2) = Brking_Frame l Y1 + Brking_Frame l Y2\<close>
  unfolding BI_eq_iff Brking_Frame_def plus_fun_def distrib_right ExSet_additive_disj
  by clarsimp blast


lemma [\<phi>reason %sift_brking_frame]:
  \<open> X1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y1 E1
\<Longrightarrow> X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y2 E2
\<Longrightarrow> (X1 + X2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l (Y1 + Y2) (E1 + E2)\<close>
  unfolding sift_brking_frame'_def Brking_Frame_plus distrib_right
  \<medium_left_bracket> premises X1 and X2
    case_analysis
      \<medium_left_bracket> X2 \<medium_right_bracket> for \<open>Brking_Frame l Y1 + Brking_Frame l Y2 + ((TECHNICAL Brk_Frame l\<heavy_comma> E1) + (TECHNICAL Brk_Frame l\<heavy_comma> E2))\<close>
      \<medium_left_bracket> X1 \<medium_right_bracket>
  \<medium_right_bracket>.

(* lemma [\<phi>reason 1200]:
  \<open> X1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E
\<Longrightarrow> X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E
\<Longrightarrow> X1 + X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E\<close>
  using \<phi>CASE_IMP by fastforce *)

lemma Brking_Frame_absorb_item[assertion_simps]:
  \<open>((Brking_Frame l Y)\<heavy_comma> X) = Brking_Frame l (\<lambda>v. X\<heavy_comma> Y v)\<close>
  unfolding Brking_Frame_def
  apply (intro assertion_eq_intro)
  \<medium_left_bracket> \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>.

lemma Brking_Frame_absorb_subj[assertion_simps]:
  \<open>((Brking_Frame l Y) \<s>\<u>\<b>\<j> P) = Brking_Frame l (\<lambda>v. Y v \<s>\<u>\<b>\<j> P)\<close>
  unfolding Brking_Frame_def
  apply (intro assertion_eq_intro)
  \<medium_left_bracket> \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>.

lemma Brking_Frame_absorb_ex[assertion_simps]:
  \<open>(\<exists>*x. (Brking_Frame l (Y x))) = Brking_Frame l (\<lambda>v. \<exists>*x. Y x v)\<close>
  unfolding Brking_Frame_def
  apply (intro assertion_eq_intro)
  \<medium_left_bracket> \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason %sift_brking_frame]:
  \<open>Brking_Frame l Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y 0\<close>
  unfolding sift_brking_frame'_def \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason %sift_brking_frame-10]:
  \<open> NO_MATCH TYPE('a) TYPE('b)
\<Longrightarrow> ERROR TEXT(\<open>The exits of scope\<close> l \<open>mismach in return type. One is\<close>
                    TYPE('a) \<open>while another is\<close> TYPE('b))
\<Longrightarrow> Brking_Frame l Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y' 0\<close>
  for Y :: \<open>'a::VALs \<phi>arg \<Rightarrow> _\<close> and Y' :: \<open>'b::VALs \<phi>arg \<Rightarrow> _\<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason %sift_brking_frame]:
  \<open> TECHNICAL Brk_Frame l\<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l 0 X\<close>
  unfolding sift_brking_frame'_def Technical_def
  \<medium_left_bracket> \<medium_right_bracket>.

lemma [\<phi>reason %sift_brking_frame-10]:
  \<open> NO_MATCH TYPE('a) TYPE('b)
\<Longrightarrow> ERROR TEXT(\<open>The exits of scope\<close> l \<open>mismach in return type. One is\<close>
                    TYPE('a) \<open>while another is\<close> TYPE('b))
\<Longrightarrow> Brking_Frame l Y\<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y' 0\<close>
  for Y :: \<open>'a::VALs \<phi>arg \<Rightarrow> _\<close> and Y' :: \<open>'b::VALs \<phi>arg \<Rightarrow> _\<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason %sift_brking_frame-20]:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E
\<Longrightarrow> A\<heavy_comma> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l (\<lambda>v. A\<heavy_comma> Y v) (A\<heavy_comma> E)\<close>
  unfolding sift_brking_frame'_def Technical_def
  \<medium_left_bracket> premises X
    X
  \<medium_right_bracket>.

lemma [\<phi>reason %sift_brking_frame-30]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brk_Frame l \<r>\<e>\<m>\<a>\<i>\<n>\<s> E \<w>\<i>\<t>\<h> Any
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l 0 E\<close>
  unfolding sift_brking_frame'_def Technical_def
  \<medium_left_bracket> premises X
    X
  \<medium_right_bracket>.

hide_fact Brking_Frame_plus

subsection \<open>NToA through Brking_Frame\<close>


lemma [\<phi>reason 2200]:
  (*The priority must override Void Padding*)
  \<open> (\<And>v. S v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> R v \<w>\<i>\<t>\<h> P)
\<Longrightarrow> Brking_Frame l S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> Brking_Frame l R \<w>\<i>\<t>\<h> P\<close>
  unfolding Brking_Frame_def REMAINS_simp
  \<medium_left_bracket> premises X
    apply_rule X[THEN transformation_right_frame]
  \<medium_right_bracket> .

lemma [\<phi>reason 2201]:
  (*The priority must override Void Padding*)
  \<open> (\<And>v. S v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> R v \<w>\<i>\<t>\<h> P)
\<Longrightarrow> TECHNICAL Brking_Frame l S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> TECHNICAL Brking_Frame l R \<w>\<i>\<t>\<h> P\<close>
  unfolding Brking_Frame_def Technical_def REMAINS_simp
  \<medium_left_bracket> premises X
    apply_rule X[THEN transformation_right_frame]
  \<medium_right_bracket>.


subsection \<open>Other Reasoning - Br Join\<close>

\<phi>reasoner_group \<phi>br_join_brk = (1000, [1000, 1030]) in \<phi>br_join_cut \<open>\<close>

declare Br_join_atom_assertion [where A=\<open>TECHNICAL Brk_Frame l\<close> for l,
                                \<phi>reason %\<phi>br_join_brk]
        Br_join_atom_assertion'[where A=\<open>TECHNICAL Brk_Frame l\<close> for l,
                                \<phi>reason %\<phi>br_join_brk]




subsection \<open>Syntax hiding technical separation items\<close>

(*
ML \<open>
val phi_display_brk_frame = Attrib.setup_config_bool \<^binding>\<open>\<phi>display_brk_frame\<close> (K false)

val _ = Theory.setup (
  Procedure_Syntax.add_item_printer (\<^const_syntax>\<open>Brk_Frame\<close>, (fn m => fn ctxt => fn X =>
    if Config.get ctxt phi_display_brk_frame
    then raise Match
    else (case m of Phi_Kind.Procedure => NONE
                  | Phi_Kind.Construction => NONE)
)))
\<close> *)


section \<open>Example\<close>

proc
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U\<close>
  output \<open>y \<Ztypecolon> \<v>\<a>\<l> U\<close>
  \<medium_left_bracket>
    op_brk_scope \<medium_left_bracket> for l1
      op_brk_scope \<medium_left_bracket> for l2
        ;; apply_rule "op_break"[of l1 \<a>\<r>\<g>2 \<open>\<lambda>ret. TECHNICAL Brk_Frame l2\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[ret] U\<close>] ($y)
      \<medium_right_bracket>
      assert \<open>\<bottom>\<^sub>B\<^sub>I\<close> (*this place is unreachable!*)
    \<medium_right_bracket>
  \<medium_right_bracket> .


end
