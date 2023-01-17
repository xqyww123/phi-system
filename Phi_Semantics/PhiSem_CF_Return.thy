theory PhiSem_CF_Return
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

type_synonym brk_label = nat

type_synonym R_brk_frame = \<open>brk_label \<rightharpoonup> VAL list option nonsepable\<close>

resource_space \<phi>CF_break_res = \<phi>empty_res +
  R_brk_frame :: R_brk_frame

debt_axiomatization R_brk_frame :: \<open>R_brk_frame resource_entry\<close>
  where \<phi>CF_break_res_ax: \<open>\<phi>CF_break_res R_brk_frame\<close>

interpretation \<phi>CF_break_res R_brk_frame using \<phi>CF_break_res_ax .

hide_fact \<phi>CF_break_res_ax

debt_axiomatization
  R_brk_frame_valid[simp]: \<open>Resource_Validator R_brk_frame.name =
                              { R_brk_frame.inject frames |frames. finite (dom frames)}\<close>

interpretation R_brk_frame: partial_map_resource \<open>{frames. finite (dom frames)}\<close> R_brk_frame
  by (standard; simp add: set_eq_iff image_iff; blast)


subsection \<open>Fiction of Scope Frames\<close>

fiction_space \<phi>CF_break_fic :: \<open>RES_N \<Rightarrow> RES\<close> =
  FIC_brk_frame :: \<open>R_brk_frame.raw_basic_fiction \<F>_it\<close>

debt_axiomatization FIC_brk_frame :: \<open>R_brk_frame fiction_entry\<close>
  where \<phi>CF_break_fic_ax: \<open>\<phi>CF_break_fic INTERPRET FIC_var\<close>

interpretation \<phi>CF_break_fic INTERPRET FIC_brk_frame using \<phi>CF_break_fic_ax .

hide_fact \<phi>CF_break_fic_ax

interpretation FIC_brk_frame:
    identity_fiction_for_partial_mapping_resource \<open>{frames. finite (dom frames)}\<close> R_brk_frame FIC_brk_frame ..


section \<open>\<phi>-Types\<close>

(*
abbreviation Brk_Frame' :: \<open>brk_label \<Rightarrow> (VAL list option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Brk_Frame' label T \<equiv> (FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable T)))\<close>
*)

definition Brk_Frame :: \<open>brk_label \<Rightarrow> assn\<close>
  where \<open>Brk_Frame label \<equiv> () \<Ztypecolon> FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable \<circle>))\<close>

definition Brking_Frame' :: \<open>brk_label \<Rightarrow> ('v::VALs sem \<Rightarrow> assn) \<Rightarrow> assn\<close>
  where \<open>Brking_Frame' label S =
     (\<exists>*v. S v\<heavy_comma> to_vals (sem.dest v) \<Ztypecolon> FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable (\<black_circle> Identity))))\<close>

abbreviation \<open>Brking_Frame l S \<equiv> TAIL (Brking_Frame' l S)\<close>

lemma Brk_Frame_eq_identity:
  \<open>Brk_Frame l = (nonsepable None \<Ztypecolon> FIC_brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff Brk_Frame_def
  by (simp add: \<phi>expns)

lemma Brking_Frame_eq_identity:
  \<open>Brking_Frame l S = (\<exists>*v. S v\<heavy_comma> nonsepable (Some (to_vals (sem.dest v))) \<Ztypecolon> FIC_brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff Brking_Frame'_def TAIL_def
  by (simp add: \<phi>expns)



section \<open>Instruction\<close>

definition op_brk_scope :: \<open>(brk_label \<Rightarrow> ('a::VALs) proc) \<Rightarrow> 'a proc\<close>
  where \<open>op_brk_scope F =
    R_brk_frame.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nonsepable None)) (\<lambda>l.
    op_try
    (F l \<bind> (\<lambda>ret. R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<ggreater> Return ret))
    (\<lambda>a. R_brk_frame.\<phi>R_get_res_entry l (\<lambda>brk.
      R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<ggreater>
     (case nonsepable.dest brk of Some vs \<Rightarrow> Return (sem (from_vals vs))
                                | None \<Rightarrow> throw a)
)))
\<close>

definition op_break :: \<open>brk_label \<Rightarrow> ('a::VALs, 'ret::VALs) proc'\<close>
  where \<open>op_break l = (\<lambda>vs.
     R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l \<mapsto> nonsepable (Some (to_vals (sem.dest vs)))))
  \<ggreater> throw (ABN_break.mk ())
)\<close>

definition \<open>sift_brking_frame' l Y E = (Brking_Frame l Y) + (E\<heavy_comma> Brk_Frame l)\<close>
definition \<open>sift_brking_frame = sift_brking_frame'\<close>

context begin

private lemma alloc_brk_scope[intro!]:
  \<open>(\<And>l. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F l \<lbrace> X\<heavy_comma> Brk_Frame l \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_brk_frame.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nonsepable None)) F
         \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding Brk_Frame_eq_identity
  by (rule; simp add: finite_map_freshness)

private lemma dispose_brk_scope:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<lbrace> Brk_Frame l \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding Brk_Frame_eq_identity
  by (rule FIC_brk_frame.\<phi>R_dispose_res[where P=\<open>\<lambda>_. True\<close>]; simp)

lemma brk_scope:
  \<open> (\<And>l. \<^bold>p\<^bold>r\<^bold>o\<^bold>c f l \<lbrace> X\<heavy_comma> Brk_Frame l \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> Brk_Frame l \<rbrace>
    \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>a. sift_brking_frame l Y' (E a)))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_brk_scope f \<lbrace> X \<longmapsto> \<lambda>ret. Y ret + Y' ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  unfolding op_brk_scope_def sift_brking_frame_def sift_brking_frame'_def
  apply (rule, rule, rule, assumption, rule)
  apply (rule \<phi>CONSEQ'E0, rule dispose_brk_scope[THEN \<phi>frame, simplified], rule)
  apply (rule \<phi>CASE)
  apply (simp only: Brking_Frame_eq_identity norm_precond_ex, rule, rule, simp, rule)
  apply (rule FIC_brk_frame.\<phi>R_dispose_res_frm[where P=\<open>\<lambda>_. True\<close>]; simp)
  apply (rule)
  apply (simp only: Brk_Frame_eq_identity, rule, simp, rule)
  apply (rule \<phi>CONSEQ'E0, rule FIC_brk_frame.\<phi>R_dispose_res_frm[where P=\<open>\<lambda>_. True\<close>]; simp)
  by (rule, rule implies_refl)

lemma op_break_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_break l vs \<lbrace> collect_return_values S vs\<heavy_comma> Brk_Frame l \<longmapsto> 0 \<rbrace>
   \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>_. Brking_Frame l S)\<close>
  unfolding op_break_def Brking_Frame_eq_identity Brk_Frame_eq_identity
            collect_return_values'_def
  unfolding TAIL_def
  by (rule, rule, simp, simp, simp, rule, \<phi>reason)

end


section \<open>Reasoning Processes\<close>

subsection \<open>sift brking frame\<close>

\<phi>setup_reason_rule_default_pattern
     \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' ?l ?Y ?E \<^bold>a\<^bold>n\<^bold>d ?Any\<close>
  \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' ?l _ _ \<^bold>a\<^bold>n\<^bold>d _\<close>
 and \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame ?l ?Y ?E \<^bold>a\<^bold>n\<^bold>d ?Any\<close>
  \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame ?l _ _ \<^bold>a\<^bold>n\<^bold>d _\<close>

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[assertion_simplification] Y' : Y
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[assertion_simplification] E' : E
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame  l Y' E'\<close>
  unfolding sift_brking_frame_def Simplify_def by simp

lemma [\<phi>reason 3000 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?X \<longmapsto> \<blangle> sift_brking_frame ?l ?Y ?E \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?Any @action reason_ToSA ?G ?mode\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame l Y E
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> \<blangle> sift_brking_frame l Y E \<brangle> @action reason_ToSA G mode\<close>
  unfolding FOCUS_TAG_def Action_Tag_def
  using view_shift_by_implication .

lemma Brking_Frame_plus:
  \<open>Brking_Frame l (Y1 + Y2) = Brking_Frame l Y1 + Brking_Frame l Y2\<close>
  unfolding set_eq_iff Brking_Frame'_def plus_fun_def distrib_right ExSet_plus TAIL_def by clarify

lemma [\<phi>reason 1200]:
  \<open> X1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y1 E1
\<Longrightarrow> X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y2 E2
\<Longrightarrow> (X1 + X2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l (Y1 + Y2) (E1 + E2)\<close>
  unfolding sift_brking_frame'_def Brking_Frame_plus distrib_right
  \<medium_left_bracket> premises X1 and X2
    cases' \<medium_left_bracket> X1 \<medium_right_bracket> for \<open>Brking_Frame l Y1 + Brking_Frame l Y2 + ((E1 \<heavy_comma> Brk_Frame l) + (E2 \<heavy_comma> Brk_Frame l))\<close> by fast
           \<medium_left_bracket> X2 \<medium_right_bracket>.
  \<medium_right_bracket>. .

(* lemma [\<phi>reason 1200]:
  \<open> X1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E
\<Longrightarrow> X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E
\<Longrightarrow> X1 + X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E\<close>
  using \<phi>CASE_IMP by fastforce *)

lemma [\<phi>reason 1200]:
  \<open>Brking_Frame l Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y 0\<close>
  unfolding sift_brking_frame'_def \<medium_left_bracket> \<medium_right_bracket>. .

lemma [\<phi>reason 1180]:
  \<open> NO_MATCH TYPE('a) TYPE('b)
\<Longrightarrow> ERROR TEXT(\<open>The exits of scope\<close> l \<open>mismach in return type. One is\<close>
                    TYPE('a) \<open>while another is\<close> TYPE('b))
\<Longrightarrow> Brking_Frame l Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y' 0\<close>
  for Y :: \<open>'a::VALs sem \<Rightarrow> _\<close> and Y' :: \<open>'b::VALs sem \<Rightarrow> _\<close>
  by blast

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s E\<heavy_comma> Brk_Frame l @action ToSA' False
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l 0 E\<close>
  unfolding sift_brking_frame'_def
  \<medium_left_bracket> premises X
    X
  \<medium_right_bracket>. .

hide_fact Brking_Frame_plus

subsection \<open>ToSA through Brking_Frame\<close>

lemma [\<phi>reason 2000]:
  \<open> Brking_Frame l (\<lambda>v. S v\<heavy_comma> A v\<heavy_comma> B v) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> Brking_Frame l (\<lambda>v. S v\<heavy_comma> (A v\<heavy_comma> B v)) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding mult.assoc .

lemma [\<phi>reason 2000]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Brking_Frame l (\<lambda>v. S v\<heavy_comma> A v\<heavy_comma> B v) \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Brking_Frame l (\<lambda>v. S v\<heavy_comma> (A v\<heavy_comma> B v)) \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding mult.assoc .

lemma [\<phi>reason 1200 for \<open>Brking_Frame ?l ?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R \<heavy_comma> \<blangle> ?Y \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> (\<And>v. S v \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R v \<heavy_comma> \<blangle> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G)
\<Longrightarrow> Brking_Frame l S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Brking_Frame l R \<heavy_comma> \<blangle> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding Brking_Frame'_def TAIL_def Action_Tag_def FOCUS_TAG_def
  \<medium_left_bracket> premises X
    X[THEN implies_right_prod]
  \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w Brking_Frame ?l ?S \<longmapsto> ?R \<heavy_comma> \<blangle> ?Y \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open>(\<And>v. \<^bold>v\<^bold>i\<^bold>e\<^bold>w S v \<longmapsto> R v \<heavy_comma> \<blangle> Y \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w Brking_Frame l S \<longmapsto> Brking_Frame l R \<heavy_comma> \<blangle> Y \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P @action reason_ToSA mode G\<close>
  unfolding Brking_Frame'_def TAIL_def Action_Tag_def FOCUS_TAG_def
  \<medium_left_bracket> premises X
    X
  \<medium_right_bracket>. .


declare [[\<phi>trace_reasoning]]
 
proc
  input \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l U\<close>
  output \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close>
  \<medium_left_bracket> brk_scope \<medium_left_bracket> for l1
      brk_scope \<medium_left_bracket> for l2
      $x op_break[of l1]
    \<medium_right_bracket>. ;;  $y op_break[of l1 \<open>\<a>\<r>\<g>2\<close>]
    \<medium_right_bracket> ..
  \<medium_right_bracket>. .



end
