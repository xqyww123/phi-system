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

definition Brking_Frame :: \<open>brk_label \<Rightarrow> ('v::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> assn\<close> ("\<^bold>b\<^bold>r\<^bold>o\<^bold>k\<^bold>e\<^bold>n _ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _" [1000,10] 3)
  where \<open>Brking_Frame label S =
     (\<exists>*v. S v\<heavy_comma> to_vals (\<phi>arg.dest v) \<Ztypecolon> FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable (\<black_circle> Identity))))\<close>

lemma Brk_Frame_eq_identity:
  \<open>Brk_Frame l = (nonsepable None \<Ztypecolon> FIC_brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff Brk_Frame_def
  by (simp add: \<phi>expns)

lemma Brking_Frame_eq_identity:
  \<open>Brking_Frame l S = (\<exists>*v. S v\<heavy_comma> nonsepable (Some (to_vals (\<phi>arg.dest v))) \<Ztypecolon> FIC_brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff Brking_Frame_def TAIL_def
  by (simp add: \<phi>expns)



section \<open>Instruction\<close>

definition op_brk_scope :: \<open>(brk_label \<Rightarrow> ('a::VALs) proc) \<Rightarrow> 'a proc\<close>
  where \<open>op_brk_scope F =
    R_brk_frame.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nonsepable None)) (\<lambda>l.
    op_try
    (F l \<bind> (\<lambda>ret. R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<ggreater> Return ret))
    (\<lambda>a. R_brk_frame.\<phi>R_get_res_entry l (\<lambda>brk.
      R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<ggreater>
     (case nonsepable.dest brk of Some vs \<Rightarrow> Return (\<phi>arg (from_vals vs))
                                | None \<Rightarrow> throw a)
)))
\<close>

definition op_break :: \<open>brk_label \<Rightarrow> ('a::VALs, 'ret::VALs) proc'\<close>
  where \<open>op_break l = (\<lambda>vs.
     R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l \<mapsto> nonsepable (Some (to_vals (\<phi>arg.dest vs)))))
  \<ggreater> throw (ABN_break.mk ())
)\<close>

lemma op_break_reduce_tail[procedure_simps,simp]:
  \<open>(op_break L v \<ggreater> f) = op_break L v\<close>
  unfolding op_break_def by simp

definition \<open>sift_brking_frame' l Y E = (Brking_Frame l Y) + (E\<heavy_comma> Brk_Frame l)\<close>
definition sift_brking_frame ("\<^bold>b\<^bold>r\<^bold>e\<^bold>a\<^bold>k _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>o\<^bold>r _" [1000,10,3] 3)
  where \<open>sift_brking_frame = sift_brking_frame'\<close>

declare sift_brking_frame'_def[folded sift_brking_frame_def, assertion_simps_source]

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

lemma "_op_break_rule_":
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_break l vs \<lbrace> S vs\<heavy_comma> Brk_Frame l \<longmapsto> 0 \<rbrace>
   \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>_. Brking_Frame l S)\<close>
  unfolding op_break_def Brking_Frame_eq_identity Brk_Frame_eq_identity
  by (rule, rule, simp, simp, simp, rule, \<phi>reason)

end


section \<open>Reasoning Processes\<close>

subsection \<open>sift brking frame\<close>

declare [[\<phi>reason_default_pattern
     \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' ?l ?Y ?E \<^bold>a\<^bold>n\<^bold>d ?Any\<close>
  \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' ?l _ _ \<^bold>a\<^bold>n\<^bold>d _\<close> (100)
 and \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame ?l ?Y ?E \<^bold>a\<^bold>n\<^bold>d ?Any\<close>
  \<Rightarrow> \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame ?l _ _ \<^bold>a\<^bold>n\<^bold>d _\<close>  (100)]]
     

lemma [\<phi>reason 1010 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame ?l ?var_Y' ?var_E'\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[assertion_simps undefined] Y' : Y
\<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[assertion_simps undefined] E' : E
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame  l Y' E'\<close>
  unfolding sift_brking_frame_def Simplify_def by simp

lemma [\<phi>reason 1000]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E
\<Longrightarrow> (\<And>v. Y v \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y' v @action ToSA)
\<Longrightarrow> E \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s E' @action ToSA
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame  l Y' E'\<close>
  unfolding sift_brking_frame_def Simplify_def Action_Tag_def sift_brking_frame'_def
            TAIL_def Brking_Frame_def 
  \<medium_left_bracket> premises X and Y and E
    X cases \<medium_left_bracket> E[THEN implies_right_prod] \<medium_right_bracket> for \<open>(\<exists>*v. Y' v\<heavy_comma> to_vals (\<phi>arg.dest v) \<Ztypecolon> _) + (E'\<heavy_comma> Brk_Frame l)\<close> ..
            \<medium_left_bracket> Y[THEN implies_right_prod] \<medium_right_bracket> ..
  \<medium_right_bracket>. .
  

lemma [\<phi>reason 3000 for \<open>?X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s \<blangle> sift_brking_frame ?l ?Y ?E \<brangle> \<^bold>a\<^bold>n\<^bold>d ?Any @action reason_ToSA ?G ?mode\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame l Y E
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s \<blangle> sift_brking_frame l Y E \<brangle> @action reason_ToSA G mode\<close>
  unfolding FOCUS_TAG_def Action_Tag_def
  using view_shift_by_implication .

lemma [\<phi>reason 3000 for \<open>?X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> sift_brking_frame ?l ?Y ?E \<brangle> \<^bold>a\<^bold>n\<^bold>d ?Any @action reason_ToSA ?G ?mode\<close>]:
  \<open> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame l Y E
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s \<blangle> sift_brking_frame l Y E \<brangle> @action reason_ToSA G mode\<close>
  unfolding FOCUS_TAG_def Action_Tag_def .

lemma Brking_Frame_plus:
  \<open>Brking_Frame l (Y1 + Y2) = Brking_Frame l Y1 + Brking_Frame l Y2\<close>
  unfolding set_eq_iff Brking_Frame_def plus_fun_def distrib_right ExSet_plus TAIL_def by clarify

lemma [\<phi>reason 1200]:
  \<open> X1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y1 E1
\<Longrightarrow> X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y2 E2
\<Longrightarrow> (X1 + X2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l (Y1 + Y2) (E1 + E2)\<close>
  unfolding sift_brking_frame'_def Brking_Frame_plus distrib_right
  \<medium_left_bracket> premises X1 and X2
    cases \<medium_left_bracket> X2 \<medium_right_bracket> for \<open>Brking_Frame l Y1 + Brking_Frame l Y2 + ((E1 \<heavy_comma> Brk_Frame l) + (E2 \<heavy_comma> Brk_Frame l))\<close> by fast
          \<medium_left_bracket> X1 \<medium_right_bracket>.
  \<medium_right_bracket>. .

(* lemma [\<phi>reason 1200]:
  \<open> X1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E
\<Longrightarrow> X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E
\<Longrightarrow> X1 + X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y E\<close>
  using \<phi>CASE_IMP by fastforce *)

lemma [\<phi>reason 1200]:
  \<open>Brking_Frame l Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y 0\<close>
  unfolding sift_brking_frame'_def \<medium_left_bracket> \<medium_right_bracket>. .

lemma Brking_Frame_absorb_item[assertion_simps]:
  \<open>((Brking_Frame l Y)\<heavy_comma> X) = Brking_Frame l (\<lambda>v. Y v \<heavy_comma> X)\<close>
  unfolding Brking_Frame_def TAIL_def
  apply (intro assertion_eq_intro)
  \<medium_left_bracket> ;; \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. .

lemma Brking_Frame_absorb_subj[assertion_simps]:
  \<open>((Brking_Frame l Y) \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = Brking_Frame l (\<lambda>v. Y v \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding Brking_Frame_def TAIL_def
  apply (intro assertion_eq_intro)
  \<medium_left_bracket> \<medium_right_bracket>. \<medium_left_bracket> ;; \<medium_right_bracket>. .

lemma Brking_Frame_absorb_ex[assertion_simps]:
  \<open>(\<exists>*x. (Brking_Frame l (Y x))) = Brking_Frame l (\<lambda>v. \<exists>*x. Y x v)\<close>
  unfolding Brking_Frame_def TAIL_def
  apply (intro assertion_eq_intro)
  \<medium_left_bracket> \<medium_right_bracket>. \<medium_left_bracket> ;; \<medium_right_bracket>. .

lemma [\<phi>reason 1180]:
  \<open> NO_MATCH TYPE('a) TYPE('b)
\<Longrightarrow> ERROR TEXT(\<open>The exits of scope\<close> l \<open>mismach in return type. One is\<close>
                    TYPE('a) \<open>while another is\<close> TYPE('b))
\<Longrightarrow> Brking_Frame l Y \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y' 0\<close>
  for Y :: \<open>'a::VALs \<phi>arg \<Rightarrow> _\<close> and Y' :: \<open>'b::VALs \<phi>arg \<Rightarrow> _\<close>
  by blast

lemma [\<phi>reason 1000]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s E\<heavy_comma> \<blangle> Brk_Frame l \<brangle> \<^bold>a\<^bold>n\<^bold>d Any @action reason_ToSA False G
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l 0 E\<close>
  unfolding sift_brking_frame'_def FOCUS_TAG_def
  \<medium_left_bracket> premises _ and X and _
    X
  \<medium_right_bracket>. .

(*It doesn't matter if the structure of sift_brking_frame is broken in the source part.*)
(*
lemma [\<phi>reason 3000]:
  \<open> Brking_Frame l Y + (E\<heavy_comma> Brk_Frame l) \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> sift_brking_frame l Y E \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding sift_brking_frame_def sift_brking_frame'_def .

lemma [\<phi>reason 3000]:
  \<open> Brking_Frame l Y + (E\<heavy_comma> Brk_Frame l) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> sift_brking_frame l Y E \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Z \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding sift_brking_frame_def sift_brking_frame'_def .
*)

hide_fact Brking_Frame_plus

subsection \<open>ToSA through Brking_Frame\<close>

(*
lemma [\<phi>reason 2000]:
  \<open> Brking_Frame l (\<lambda>v. S v\<heavy_comma> A v\<heavy_comma> B v) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> Brking_Frame l (\<lambda>v. S v\<heavy_comma> (A v\<heavy_comma> B v)) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding mult.assoc .

lemma [\<phi>reason 2000]:
  \<open> Brking_Frame l (\<lambda>v. S v\<heavy_comma> A v\<heavy_comma> B v) \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G
\<Longrightarrow> Brking_Frame l (\<lambda>v. S v\<heavy_comma> (A v\<heavy_comma> B v)) \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding mult.assoc . *)

lemma [\<phi>reason 2200 for \<open>Brking_Frame ?l ?S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?R \<heavy_comma> \<blangle> ?Y \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  (*The priority must override Void Padding*)
  \<open> (\<And>v. S v \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R v \<heavy_comma> Y \<^bold>a\<^bold>n\<^bold>d P @action ToSA' mode)
\<Longrightarrow> Brking_Frame l S \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Brking_Frame l R \<heavy_comma> \<blangle> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding Brking_Frame_def TAIL_def Action_Tag_def FOCUS_TAG_def
  \<medium_left_bracket> premises X
    X[THEN implies_right_prod]
  \<medium_right_bracket>. .

lemma [\<phi>reason 2200 for \<open>Brking_Frame ?l ?S \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?R \<heavy_comma> \<blangle> ?Y \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open>(\<And>v. S v \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R v \<heavy_comma> \<blangle> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G)
\<Longrightarrow> Brking_Frame l S \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Brking_Frame l R \<heavy_comma> \<blangle> Y \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  unfolding Brking_Frame_def TAIL_def Action_Tag_def FOCUS_TAG_def
  \<medium_left_bracket> premises X
    X
  \<medium_right_bracket>. .


subsection \<open>Syntax hiding technical separation items\<close>

optional_translations (\<phi>hide_brk_frame)
  "L" <= "CONST Brk_Frame l\<heavy_comma> L"
  "R" <= "R \<heavy_comma> CONST Brk_Frame l"
  "R\<heavy_comma> L" <= "R \<heavy_comma> CONST Brk_Frame l\<heavy_comma> L"
  "XCONST Void" <= "CONST Brk_Frame l"
  \<open>Hides technical SL assertions for control flowing breaking\<close>

declare [[\<phi>hide_brk_frame]]

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
  input  \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l U\<close>
  output \<open>y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l U\<close>
  \<medium_left_bracket> brk_scope \<medium_left_bracket> for l1
      brk_scope \<medium_left_bracket> for l2
        $y "_op_break_rule_"[of l1 \<a>\<r>\<g>2 \<open>\<lambda>ret. Brk_Frame l2\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[ret] U\<close>]
      \<medium_right_bracket> .. ;;
      assert \<bottom> (*this place is unreachable!*)
    \<medium_right_bracket>.
  \<medium_right_bracket>. .


end
