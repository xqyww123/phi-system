theory PhiSem_CF_Break
  imports Phi_System.PhiSem_Formalization_Tools
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
type_synonym brk_frame = \<open>RES.brk_label \<rightharpoonup> VAL list option nosep\<close>

setup \<open>Sign.parent_path\<close>

resource_space \<phi>CF_break =
  brk_frame :: \<open>{frames::RES.brk_frame. finite (dom frames)}\<close> (partial_map_resource) ..

hide_fact RES.\<phi>CF_break_res_ax


subsection \<open>Fiction of Scope Frames\<close>

fiction_space \<phi>CF_break =
  brk_frame :: \<open>RES.brk_frame.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_it\<close>
               (identity_fiction_for_partial_mapping_resource RES.brk_frame) ..

hide_fact FIC.\<phi>CF_break_fic_ax

section \<open>\<phi>-Types\<close>

(*
abbreviation Brk_Frame' :: \<open>brk_label \<Rightarrow> (VAL list option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Brk_Frame' label T \<equiv> (FIC.brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nosep T)))\<close>
*)

definition Brk_Frame :: \<open>RES.brk_label \<Rightarrow> assn\<close>
  where \<open>Brk_Frame label \<equiv> () \<Ztypecolon> FIC.brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nosep \<circle>))\<close>

definition Brking_Frame :: \<open>RES.brk_label \<Rightarrow> ('v::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> assn\<close> ("\<^bold>b\<^bold>r\<^bold>o\<^bold>k\<^bold>e\<^bold>n _ \<w>\<i>\<t>\<h> _" [1000,10] 3)
  where \<open>Brking_Frame label S =
     (\<exists>*v. S v\<heavy_comma> to_vals (\<phi>arg.dest v) \<Ztypecolon> FIC.brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nosep (\<black_circle> Itself))))\<close>

lemma [elim!]:
  \<open>Inhabited (Brk_Frame X) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma [\<phi>inhabitance_rule 1000]:
  \<open>Inhabited (Brk_Frame X) \<longrightarrow> True\<close> by blast

lemma Brk_Frame_eq_identity:
  \<open>Brk_Frame l = (nosep None \<Ztypecolon> FIC.brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Itself))\<close>
  unfolding set_eq_iff Brk_Frame_def
  by (simp add: \<phi>expns)

lemma Brking_Frame_eq_identity:
  \<open>Brking_Frame l S = (\<exists>*v. S v\<heavy_comma> nosep (Some (to_vals (\<phi>arg.dest v))) \<Ztypecolon> FIC.brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Itself))\<close>
  unfolding set_eq_iff Brking_Frame_def
  by (simp add: \<phi>expns)



section \<open>Instruction\<close>

definition op_brk_scope :: \<open>(RES.brk_label \<Rightarrow> ('a::VALs) proc) \<Rightarrow> 'a proc\<close>
  where \<open>op_brk_scope F =
    RES.brk_frame.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nosep None)) (\<lambda>l.
    op_try
    (F l \<bind> (\<lambda>ret. RES.brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<ggreater> Return ret))
    (\<lambda>a. RES.brk_frame.\<phi>R_get_res_entry l (\<lambda>brk.
      RES.brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<ggreater>
     (case nosep.dest brk of Some vs \<Rightarrow> Return (\<phi>arg (from_vals vs))
                                | None \<Rightarrow> throw a)
)))
\<close>

definition op_break :: \<open>RES.brk_label \<Rightarrow> ('a::VALs, 'ret) proc'\<close>
  where \<open>op_break l = (\<lambda>vs.
     RES.brk_frame.\<phi>R_set_res (\<lambda>f. f(l \<mapsto> nosep (Some (to_vals (\<phi>arg.dest vs)))))
  \<ggreater> throw (ABN_break.mk ())
)\<close>

lemma op_break_reduce_tail[procedure_simps,simp]:
  \<open>(op_break L v \<ggreater> f) = op_break L v\<close>
  unfolding op_break_def by simp

definition \<open>sift_brking_frame' l Y E = (Brking_Frame l Y) + (E\<heavy_comma> TECHNICAL Brk_Frame l)\<close>
definition sift_brking_frame ("\<b>\<r>\<e>\<a>\<k> _/ \<w>\<i>\<t>\<h> _/ \<o>\<r> _" [1000,10,3] 3)
  where \<open>sift_brking_frame = sift_brking_frame'\<close>

declare sift_brking_frame'_def[folded sift_brking_frame_def, assertion_simps_source]

context begin

private lemma alloc_brk_scope[intro!]:
  \<open>(\<And>l. \<p>\<r>\<o>\<c> F l \<lbrace> X\<heavy_comma> Brk_Frame l \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  )
\<Longrightarrow> \<p>\<r>\<o>\<c> RES.brk_frame.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nosep None)) F
         \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding Brk_Frame_eq_identity
  by (rule; simp add: finite_map_freshness)

private lemma dispose_brk_scope:
  \<open>\<p>\<r>\<o>\<c> RES.brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<lbrace> Brk_Frame l \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding Brk_Frame_eq_identity
  by (rule FIC.brk_frame.\<phi>R_dispose_res[where P=\<open>\<lambda>_. True\<close>]; simp)

lemma brk_scope:
  \<open> (\<And>l. \<p>\<r>\<o>\<c> f l \<lbrace> X\<heavy_comma> TECHNICAL Brk_Frame l \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> \<blangle> TECHNICAL Brk_Frame l \<brangle> \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>a. sift_brking_frame l Y' (E a)))
\<Longrightarrow> \<p>\<r>\<o>\<c> op_brk_scope f \<lbrace> X \<longmapsto> \<lambda>ret. Y ret + Y' ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding op_brk_scope_def sift_brking_frame_def sift_brking_frame'_def
            Technical_def FOCUS_TAG_def
  apply (rule, rule, rule, assumption, rule)
  apply (rule \<phi>CONSEQ'E0[unfolded zero_fun_def], rule dispose_brk_scope[THEN \<phi>frame, simplified], rule)
  apply (rule \<phi>CASE)
  apply (simp only: Brking_Frame_eq_identity norm_precond_ex, rule, rule, simp, rule)
  apply (rule FIC.brk_frame.\<phi>R_dispose_res_frm[where P=\<open>\<lambda>_. True\<close>]; simp)
  apply (rule)
  apply (simp only: Brk_Frame_eq_identity, rule, simp, rule)
  apply (rule \<phi>CONSEQ'E0, rule FIC.brk_frame.\<phi>R_dispose_res_frm[where P=\<open>\<lambda>_. True\<close>]; simp)
  by (rule, rule implies_refl)

lemma "_op_break_rule_":
  \<open>\<p>\<r>\<o>\<c> op_break l vs \<lbrace> S vs\<heavy_comma> TECHNICAL Brk_Frame l \<longmapsto> 0 \<rbrace>
   \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame l S)\<close>
  unfolding op_break_def Brking_Frame_eq_identity Brk_Frame_eq_identity Technical_def
  by (rule, rule, simp, simp, simp, rule, \<phi>reason)

end


section \<open>Reasoning Processes\<close>

subsection \<open>sift brking frame\<close>

declare [[\<phi>reason_default_pattern
     \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' ?l ?Y ?E \<w>\<i>\<t>\<h> ?Any\<close>
  \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' ?l _ _ \<w>\<i>\<t>\<h> _\<close> (100)
 and \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame ?l ?Y ?E \<w>\<i>\<t>\<h> ?Any\<close>
  \<Rightarrow> \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame ?l _ _ \<w>\<i>\<t>\<h> _\<close>  (100)]]


lemma [\<phi>reason 1010 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame ?l ?var_Y' ?var_E'\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined] Y' : Y
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined] E' : E
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame  l Y' E'\<close>
  unfolding sift_brking_frame_def Simplify_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E
\<Longrightarrow> (\<And>v. Y v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y' v @action ToSA)
\<Longrightarrow> E \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> E' @action ToSA
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame  l Y' E'\<close>
  unfolding sift_brking_frame_def Simplify_def Action_Tag_def sift_brking_frame'_def
           Brking_Frame_def
  \<medium_left_bracket> premises X and Y and E
    X cases \<medium_left_bracket> apply_rule E[THEN implies_right_prod] \<medium_right_bracket> for \<open>(\<exists>*v. Y' v\<heavy_comma> to_vals (\<phi>arg.dest v) \<Ztypecolon> _) + (E'\<heavy_comma> TECHNICAL Brk_Frame l)\<close>
            \<medium_left_bracket> apply_rule Y[THEN implies_right_prod] \<medium_right_bracket>
  \<medium_right_bracket>.


lemma [\<phi>reason 3000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> sift_brking_frame ?l ?Y ?E \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame l Y E
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 * \<blangle> sift_brking_frame l Y E \<brangle> \<w>\<i>\<t>\<h> True\<close>
  unfolding FOCUS_TAG_def Action_Tag_def
  by simp


lemma Brking_Frame_plus:
  \<open>Brking_Frame l (Y1 + Y2) = Brking_Frame l Y1 + Brking_Frame l Y2\<close>
  unfolding set_eq_iff Brking_Frame_def plus_fun_def distrib_right ExSet_plus by clarify

declare [[\<phi>trace_reasoning = 2]]

lemma [\<phi>reason 1200]:
  \<open> X1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y1 E1
\<Longrightarrow> X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y2 E2
\<Longrightarrow> (X1 + X2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l (Y1 + Y2) (E1 + E2)\<close>
  unfolding sift_brking_frame'_def Brking_Frame_plus distrib_right
  \<medium_left_bracket> premises X1 and X2
    cases \<medium_left_bracket> X2 \<medium_right_bracket> for \<open>Brking_Frame l Y1 + Brking_Frame l Y2 + ((E1 \<heavy_comma> TECHNICAL Brk_Frame l) + (E2 \<heavy_comma> TECHNICAL Brk_Frame l))\<close>
          \<medium_left_bracket> X1 \<medium_right_bracket>
  \<medium_right_bracket>.

(* lemma [\<phi>reason 1200]:
  \<open> X1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E
\<Longrightarrow> X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E
\<Longrightarrow> X1 + X2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y E\<close>
  using \<phi>CASE_IMP by fastforce *)

lemma [\<phi>reason 1200]:
  \<open>Brking_Frame l Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y 0\<close>
  unfolding sift_brking_frame'_def \<medium_left_bracket> \<medium_right_bracket>.

lemma Brking_Frame_absorb_item[assertion_simps]:
  \<open>((Brking_Frame l Y)\<heavy_comma> X) = Brking_Frame l (\<lambda>v. Y v \<heavy_comma> X)\<close>
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

lemma [\<phi>reason 1180]:
  \<open> NO_MATCH TYPE('a) TYPE('b)
\<Longrightarrow> ERROR TEXT(\<open>The exits of scope\<close> l \<open>mismach in return type. One is\<close>
                    TYPE('a) \<open>while another is\<close> TYPE('b))
\<Longrightarrow> Brking_Frame l Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l Y' 0\<close>
  for Y :: \<open>'a::VALs \<phi>arg \<Rightarrow> _\<close> and Y' :: \<open>'b::VALs \<phi>arg \<Rightarrow> _\<close>
  by blast

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> E\<heavy_comma> \<blangle> TECHNICAL Brk_Frame l \<brangle> \<w>\<i>\<t>\<h> Any
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> sift_brking_frame' l 0 E\<close>
  unfolding sift_brking_frame'_def FOCUS_TAG_def Technical_def
  \<medium_left_bracket> premises X
    X
  \<medium_right_bracket>.

hide_fact Brking_Frame_plus

subsection \<open>ToSA through Brking_Frame\<close>


lemma [\<phi>reason 2200]:
  (*The priority must override Void Padding*)
  \<open> (\<And>v. S v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R v \<heavy_comma> \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> Brking_Frame l S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Brking_Frame l R \<heavy_comma> \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P\<close>
  unfolding Brking_Frame_def FOCUS_TAG_def
  \<medium_left_bracket> premises X
    apply_rule X[THEN implies_right_prod]
  \<medium_right_bracket>.

lemma [\<phi>reason 2201]:
  (*The priority must override Void Padding*)
  \<open> (\<And>v. S v \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R v \<heavy_comma> \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> TECHNICAL Brking_Frame l S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> TECHNICAL Brking_Frame l R \<heavy_comma> \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P\<close>
  unfolding Brking_Frame_def FOCUS_TAG_def Technical_def
  \<medium_left_bracket> premises X
    apply_rule X[THEN implies_right_prod]
  \<medium_right_bracket>.


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
    brk_scope \<medium_left_bracket> for l1
      brk_scope \<medium_left_bracket> for l2
        apply_rule "_op_break_rule_"[of l1 \<a>\<r>\<g>2 \<open>\<lambda>ret. TECHNICAL Brk_Frame l2\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[ret] U\<close>] ($y)
      \<medium_right_bracket>
      assert \<bottom> (*this place is unreachable!*)
    \<medium_right_bracket>
  \<medium_right_bracket> .


end
