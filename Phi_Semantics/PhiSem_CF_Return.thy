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

definition Brking_Frame :: \<open>brk_label \<Rightarrow> ('v::VALs sem \<Rightarrow> assn) \<Rightarrow> assn\<close>
  where \<open>Brking_Frame label S \<equiv>
    (\<exists>*v. S v\<heavy_comma> to_vals (sem.dest v) \<Ztypecolon> FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable (\<black_circle> Identity))))\<close>

lemma Brk_Frame_eq_identity:
  \<open>Brk_Frame l = (nonsepable None \<Ztypecolon> FIC_brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff Brk_Frame_def
  by (simp add: \<phi>expns)

lemma Brking_Frame_eq_identity:
  \<open>Brking_Frame l S = (\<exists>*v. S v\<heavy_comma> nonsepable (Some (to_vals (sem.dest v))) \<Ztypecolon> FIC_brk_frame.\<phi> (l \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff Brking_Frame_def
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
  \<ggreater> throw (sem (ABN_break.mk ()))
)\<close>


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
    \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>a. (Brking_Frame l Y') + (E a\<heavy_comma> Brk_Frame l)))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_brk_scope f \<lbrace> X \<longmapsto> \<lambda>ret. Y ret + Y' ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E\<close>
  unfolding op_brk_scope_def
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
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_break l vs \<lbrace> S vs\<heavy_comma> Brk_Frame l \<longmapsto> (0 :: unreachable sem \<Rightarrow> _) \<rbrace>
   \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>_. Brking_Frame l S)\<close>
  unfolding op_break_def Brking_Frame_eq_identity Brk_Frame_eq_identity
  by (rule, rule, simp, simp, simp, rule, \<phi>reason)

end



definition \<open>sift_brking_frame' l Y E = (Brking_Frame l Y) + (E\<heavy_comma> Brk_Frame l)\<close>
definition \<open>sift_brking_frame = sift_brking_frame'\<close>

lemma Brking_Frame_plus:
  \<open>Brking_Frame l (Y1 + Y2) = Brking_Frame l Y1 + Brking_Frame l Y2\<close>
  unfolding set_eq_iff Brking_Frame_def plus_fun_def distrib_right ExSet_plus by clarify

lemma
  \<open> X1 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y1 E1
\<Longrightarrow> X2 \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l Y2 E2
\<Longrightarrow> (X1 + X2) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s sift_brking_frame' l (Y1 + Y2) (E1 + E2)\<close>
  unfolding sift_brking_frame'_def Brking_Frame_plus distrib_right
  \<medium_left_bracket> ;; ;; cases'
  apply (clarsimp simp add: \<phi>expns Brking_Frame_plus)


hide_fact Brking_Frame_plus


  notepad
begin
  define xx where \<open>xx \<equiv> 10\<close>
  term xx
end