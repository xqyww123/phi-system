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
    identity_fiction \<open>{frames. finite (dom frames)}\<close> R_brk_frame FIC_brk_frame ..

section \<open>\<phi>-Types\<close>

abbreviation Brk_Frame' :: \<open>brk_label \<Rightarrow> (VAL list option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Brk_Frame' label T \<equiv> (FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable T)))\<close>

abbreviation Brk_Frame :: \<open>brk_label \<Rightarrow> assn\<close>
  where \<open>Brk_Frame label \<equiv> () \<Ztypecolon> FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable \<circle>))\<close>

abbreviation Brking_Frame :: \<open>brk_label \<Rightarrow> (VAL list,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Brking_Frame label T \<equiv> (FIC_brk_frame.\<phi> (label \<^bold>\<rightarrow> \<black_circle> (Nonsepable (\<black_circle> T))))\<close>


section \<open>Instruction\<close>

definition op_brk_scope :: \<open>(brk_label \<Rightarrow> ('a::VALs) proc) \<Rightarrow> 'a proc\<close>
  where \<open>op_brk_scope F =
    R_brk_frame.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nonsepable None)) (\<lambda>l.
    op_try
    (F l \<bind> (\<lambda>ret. R_brk_frame.\<phi>R_set_res (\<lambda>f. f(l := None)) \<ggreater> Return ret))
    (\<lambda>a. R_brk_frame.\<phi>R_get_res_entry l (\<lambda>brk.
      case nonsepable.dest brk of Some vs \<Rightarrow> Return (sem (from_vals vs))
                                | None \<Rightarrow> throw a
)))
\<close>

context begin

private lemma alloc:
  \<open>(\<And>l. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F l \<lbrace> X\<heavy_comma> Brk_Frame l \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_brk_frame.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nonsepable None)) F
         \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  apply (clarsimp simp add: \<phi>expns \<phi>Procedure_\<phi>Res_Spec simp del: set_mult_expn del: subsetI)
  subgoal for r res c
  apply (rule R_brk_frame.\<phi>R_allocate_res_entry[where R="(\<I> INTERP (r * c))"])
  apply clarsimp using finite_map_freshness apply blast
  
  apply clarsimp
  
  apply (clarsimp simp del: \<phi>Res_Spec_mult_homo set_mult_expn del: subsetI)
  subgoal premises prems for k res'
  apply (rule prems(1)[THEN spec[where x=r], THEN spec[where x=res'],
              simplified prems, simplified, THEN mp])
    apply (rule exI[where x=\<open>c * FIC_brk_frame.mk (1(k \<mapsto> nonsepable None))\<close>])
  apply (simp add: \<phi>expns prems)
  by (smt (verit, best) FIC_brk_frame.expand FIC_brk_frame.sep_disj_fiction Fic_Space_Un Fic_Space_m \<phi>Res_Spec_mult_homo prems(3) prems(4) prems(5) prems(6) prems(7) sep_disj_multD2 sep_disj_multI2 sep_mult_assoc)
  by meson .

lemma
  \<open> (\<And>l. \<^bold>p\<^bold>r\<^bold>o\<^bold>c f l \<lbrace> X\<heavy_comma> Brk_Frame l \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> Brk_Frame l \<rbrace>
    \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>a. (E1 a\<heavy_comma> y \<Ztypecolon> Brking_Frame l U) + (E2 a\<heavy_comma> Brk_Frame l)))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_brk_scope f \<lbrace> X \<longmapsto> \<lambda>ret. Y ret + S ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2\<close>
  unfolding op_brk_scope_def
  apply (rule alloc, rule "__op_try__", rule, assumption, rule)
  thm "__op_try__"
  thm R_brk_frame.\<phi>R_allocate_res_entry


term \<open>
 op_try (F magic) (\<lambda>a.
    if sem.dest a \<in> ABN_break.domain \<and> fst (ABN_break.dest (sem.dest a)) = magic
    then Return (sem (from_vals (snd (ABN_break.dest (sem.dest a)))))
    else det_lift (Exception a))\<close>

definition \<phi>Break :: \<open>cf_label \<Rightarrow> ('vs::VALs sem \<Rightarrow> assn) \<Rightarrow> ABNM sem \<Rightarrow> assn\<close>
  where \<open>\<phi>Break l S = (\<lambda>a. (S vs \<^bold>s\<^bold>u\<^bold>b\<^bold>j vs. ABN_break.mk (l, to_vals (sem.dest vs)) = sem.dest a))\<close>

term \<open>X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s  \<close>

lemma
  \<open> (\<And>l. \<^bold>p\<^bold>r\<^bold>o\<^bold>c f l \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>a. \<phi>Break l S a + E2 a))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c scope f \<lbrace> X \<longmapsto> \<lambda>ret. Y ret + S ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2\<close>
  unfolding scope_def
  apply (rule "__op_try__")
   apply assumption
  subgoal for ret
    apply (cases ret)
    apply (cases \<open>sem.dest ret \<in> ABN_break.domain \<and> fst (ABN_break.dest (sem.dest ret)) = magic\<close>; simp)
prefer 2
  unfolding \<phi>Break_def ABN_break.domain_def apply clarsimp
  

  unfolding \<phi>Procedure_def \<phi>Procedure_def
  apply clarsimp apply rule
  apply clarsimp
subgoal for ret comp R x s
    apply (cases s; simp; cases x; clarsimp simp add: \<phi>expns ring_distribs)


  unfolding scope_def op_try_def
  apply clarsimp
  unfolding \<phi>Procedure_def
  apply clarsimp
subgoal for comp R x s
    apply (cases s; simp; cases x; clarsimp simp add: \<phi>expns ring_distribs)
subgoal premises prems for a b u v
      using prems(1)[THEN spec[where x=comp], THEN spec[where x=R]]
      by (smt (verit) INTERP_SPEC LooseStateTy_expn(1) LooseStateTy_plus in_mono prems(2) prems(5) prems(6) prems(7) prems(8) set_mult_expn)

end