theory PhiSem_Variable
  imports Phi_System.PhiSem_Formalization_Tools
begin

chapter \<open>Minimal Semantics\<close>

text \<open>This minimal semantics contains integer and variable.\<close>

section \<open>Semantic\<close>

subsection \<open>Models\<close>

subsubsection \<open>Resource\<close>

typedef varname = \<open>UNIV::nat set\<close> ..
type_synonym R_var = \<open>varname \<rightharpoonup> VAL nonsepable\<close>

lemma infinite_varname:
  \<open>infinite (UNIV::varname set)\<close>
  by (metis (mono_tags, opaque_lifting) Rep_varname_cases UNIV_I finite_imageI infinite_UNIV_char_0 surj_def)

resource_space \<phi>min_res = \<phi>empty_res +
  R_var :: R_var

debt_axiomatization R_var :: \<open>R_var resource_entry\<close>
  where \<phi>min_res_ax: \<open>\<phi>min_res R_var\<close>

interpretation \<phi>min_res R_var using \<phi>min_res_ax .

hide_fact \<phi>min_res_ax \<phi>min_res_axioms \<phi>min_res_fields_axioms

debt_axiomatization
  res_valid_var[simp]: \<open>Resource_Validator R_var.name =
                           {R_var.inject vars |vars. finite (dom vars)}\<close>

interpretation R_var: partial_map_resource \<open>{vars. finite (dom vars)}\<close> R_var
  by (standard; simp add: set_eq_iff image_iff; blast)

subsubsection \<open>Fiction\<close>

fiction_space \<phi>min_fic :: \<open>RES_N \<Rightarrow> RES\<close> =
  FIC_var :: \<open>R_var.raw_basic_fiction \<F>_it\<close>

debt_axiomatization FIC_var :: \<open>R_var fiction_entry\<close>
  where \<phi>min_fic_ax: \<open>\<phi>min_fic INTERPRET FIC_var\<close>

interpretation \<phi>min_fic INTERPRET FIC_var using \<phi>min_fic_ax .

hide_fact \<phi>min_fic_ax \<phi>min_fic_axioms

interpretation FIC_var: identity_fiction \<open>{vars. finite (dom vars)}\<close> R_var FIC_var ..


section \<open>\<phi>-Types\<close>

subsection \<open>Variable\<close>

abbreviation Var :: \<open>varname \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> assn\<close>
  where \<open>Var vname T \<equiv> (FIC_var.\<phi> (vname \<^bold>\<rightarrow> \<black_circle> (Nonsepable T)))\<close>

lemma Var_inhabited[\<phi>inhabitance_rule,elim!]:
  \<open>Inhabited (x \<Ztypecolon> Var vname T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Var_subty:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> Var vname T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> Var vname T' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma Var_view_shift:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> Var vname T \<longmapsto> x' \<Ztypecolon> Var vname T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Imply_def View_Shift_def by (clarsimp simp add: \<phi>expns, blast)

lemma Var_cast_\<phi>app[\<phi>overload cast]: 
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> Var vname T \<longmapsto> x' \<Ztypecolon> Var vname T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Argument_def using Var_view_shift .

(* lemma Var_ExTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (ExTyp T)) = (\<exists>*a. x a \<Ztypecolon> Var vname (T a))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma Var_SubjTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (x \<Ztypecolon> Var vname T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns) *)

(*lemma [\<phi>reason 1200 for \<open>EqualAddress (?xa \<Ztypecolon> Var ?va ?Ta) (?xb \<Ztypecolon> Var ?vb ?Tb)\<close>]:
  \<open>EqualAddress (xa \<Ztypecolon> Var var Ta) (xb \<Ztypecolon> Var var Tb)\<close>
  unfolding EqualAddress_def .. *)

lemma [\<phi>reason 1305 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> x \<Ztypecolon> Var var T \<longmapsto> R\<heavy_comma> \<blangle> x' \<Ztypecolon> Var var T' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding GOAL_CTXT_def FOCUS_TAG_def
  by (simp add: Var_view_shift \<phi>frame_view) 

lemma [\<phi>reason 1300 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?X \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R\<heavy_comma> x \<Ztypecolon> Var var T \<longmapsto> R\<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding GOAL_CTXT_def FOCUS_TAG_def
  by (simp add: Var_view_shift \<phi>frame_view view_shift_id) 

lemma Var_simp_cong:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Var v T) = (x' \<Ztypecolon> Var v T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup Var_simp_cong ("x \<Ztypecolon> Var v T") = \<open>
  K (NuSimpCong.simproc @{thm Var_simp_cong[folded atomize_eq]})
\<close>


subsubsection \<open>Rules\<close>

lemma [\<phi>reason 1200 for \<open>PROP Branch_Convergence_Type_Pattern (Var ?v ?T) ?X\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern (Var v T) (Var v T')\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1500 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?x \<Ztypecolon> Var ?var ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
    \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> x \<Ztypecolon> Var var T \<longmapsto> R \<heavy_comma> \<blangle> x' \<Ztypecolon> Var var T' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding GOAL_CTXT_def FOCUS_TAG_def
  by (simp add: Var_view_shift \<phi>frame_view)

lemma [\<phi>reason 1450 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> ?H \<longmapsto> ?R''' * \<blangle> ?x \<Ztypecolon> Var ?var ?T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' ?mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R' \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P  \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> H \<longmapsto> R' \<heavy_comma> H \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA' mode  \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G\<close>
  using ToSA_skip[OF CHK_SUBGOAL_I] .


subsubsection \<open>Application Methods for Subtyping\<close>

lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Var ?var ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def] implies_left_prod
  by (metis Var_subty)


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (?x' \<Ztypecolon> ?T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Var ?var ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x' \<Ztypecolon> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using "\<phi>cast_P" Var_cast_\<phi>app[unfolded Argument_def] implies_left_prod
  by (metis Var_subty)


section \<open>Instructions\<close>

subsection \<open>Variable Operations\<close>

definition \<phi>M_get_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc"
  where "\<phi>M_get_var vname TY F = R_var.\<phi>R_get_res_entry vname ((\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type TY) \<ggreater> F val) o nonsepable.dest)"

definition op_get_var :: "varname \<Rightarrow> TY \<Rightarrow> VAL proc"
  where "op_get_var vname TY = \<phi>M_get_var vname TY (\<lambda>x. Return (sem_value x))"

definition op_set_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL,unit) proc'"
  where "op_set_var vname TY v =
          \<phi>M_getV TY id v (\<lambda>v.
          \<phi>M_get_var vname TY (\<lambda>_.
          R_var.\<phi>R_set_res (\<lambda>f. f(vname := Some (nonsepable v)))))"

definition op_free_var :: "varname \<Rightarrow> unit proc"
  where "op_free_var vname = R_var.\<phi>R_set_res (\<lambda>f. f(vname := None))"

definition op_var_scope' :: "TY \<Rightarrow> (varname \<Rightarrow> 'ret proc) \<Rightarrow> (VAL,'ret) proc'"
  where "op_var_scope' TY F v =
    \<phi>M_getV TY id v (\<lambda>v.
    R_var.\<phi>R_allocate_res_entry (\<lambda>_. True) (Some (nonsepable v)) F
  )"

lemma \<phi>M_get_var[intro!]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_var vname TY F \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec \<phi>M_get_var_def
  by (clarsimp simp add: \<phi>expns FIC_var.expand simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_get_res_entry[where v=\<open>nonsepable v\<close>]; simp)

lemma \<phi>M_set_var[intro!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c R_var.\<phi>R_set_res (\<lambda>f. f(vname \<mapsto> nonsepable u))
      \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  thm  FIC_var.expand_subj[where x=\<open>1(vname \<mapsto> nonsepable u)\<close>]
  by (clarsimp simp add: \<phi>expns FIC_var.expand[where x=\<open>1(vname \<mapsto> nonsepable v)\<close>]
                                FIC_var.expand_subj[where x=\<open>1(vname \<mapsto> nonsepable u)\<close>]
               simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_set_res[where P=\<open>\<lambda>_. True\<close>]; simp)

lemma op_get_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var vname TY \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> v \<Ztypecolon> Var vname Identity \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding op_get_var_def Premise_def
  by (rule,assumption,rule,simp add: \<phi>expns)


lemma op_set_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_var vname TY rawv \<lbrace> v \<Ztypecolon> Var vname Identity\<heavy_comma> u \<Ztypecolon> Val rawv Identity \<longmapsto> u \<Ztypecolon> Var vname Identity \<rbrace>\<close>
  unfolding op_set_var_def Premise_def
  by (cases rawv; simp, rule, simp add: \<phi>expns, rule, assumption, simp add: \<phi>expns, rule)

lemma op_var_scope':
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> (\<And>vname. \<^bold>p\<^bold>r\<^bold>o\<^bold>c F vname \<lbrace> X\<heavy_comma> v \<Ztypecolon> Var vname Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope' TY F rawv \<lbrace> X\<heavy_comma> v \<Ztypecolon> Val rawv Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding op_var_scope'_def Premise_def
  apply (cases rawv; simp, rule, simp add: \<phi>expns)
  apply (clarsimp simp add: \<phi>expns \<phi>Procedure_\<phi>Res_Spec simp del: set_mult_expn del: subsetI)
  subgoal for r res c
  apply (rule R_var.\<phi>R_allocate_res_entry[where R="(\<I> INTERP (r * c))"])
     apply (clarsimp) using finite_map_freshness infinite_varname apply blast
      apply (clarsimp)

 apply (clarsimp simp del: \<phi>Res_Spec_mult_homo set_mult_expn del: subsetI)
  subgoal premises prems for k res'
    apply (rule prems(2)[THEN spec[where x=r], THEN spec[where x=res'],
                simplified prems, simplified, THEN mp])
    apply (rule exI[where x=\<open>c * FIC_var.mk (1(k \<mapsto> nonsepable v))\<close>])
    apply (simp add: \<phi>expns prems)
    by (smt (verit, ccfv_threshold) FIC_var.expand FIC_var.sep_disj_fiction Fic_Space_Un Fic_Space_m \<phi>Res_Spec_mult_homo prems(5) prems(6) prems(7) prems(8) prems(9) sep_disj_multD2 sep_disj_multI2 sep_mult_assoc')
  . .


lemma op_free_var:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_var vname \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> 1 \<rbrace>\<close>
  unfolding op_free_var_def \<phi>Procedure_\<phi>Res_Spec
  by (clarsimp simp add: \<phi>expns FIC_var.expand simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_dispose_res[where any=\<open>nonsepable v\<close> and P=\<open>\<lambda>_. True\<close>];
      clarsimp simp add: \<phi>Res_Spec_mult_homo)



end


