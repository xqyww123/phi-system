chapter \<open>Typed Variable\<close>

text \<open>This is a generic formalization variables supporting either typed variables or non-typed.
If the formalization is untyped, variables in the formalization can be assigned by values of
any type.
You can set the flag \<phi>variable_is_typed to indicate whether the formalization of variables is typed.\<close>

theory PhiSem_Variable
  imports Phi_System.PhiSem_Formalization_Tools
  abbrevs "<var>" = "\<^bold>v\<^bold>a\<^bold>r"
begin

section \<open>Semantic\<close>

subsection \<open>Models\<close>

subsubsection \<open>Resource\<close>

declare [ [typedef_overloaded] ]
datatype varname = varname nat \<comment> \<open>nonce\<close> (type: \<open>TY option\<close>) \<comment> \<open>None denotes no type restriction.\<close>
hide_const (open) type
declare [ [typedef_overloaded = false] ]

type_synonym R_var = \<open>varname \<rightharpoonup> VAL option nonsepable\<close>
  \<comment> \<open>NONE: declared but not initialized.\<close>

lemma infinite_varname:
  \<open>infinite {k. varname.type k = TY}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{k. varname.type k = TY}\<close>
        and f = \<open>\<lambda>n. varname n TY\<close>]
  using inj_def by fastforce
  

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

abbreviation Var :: \<open>varname \<Rightarrow> (VAL option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Var vname T \<equiv> (FIC_var.\<phi> (vname \<^bold>\<rightarrow> \<black_circle> (Nonsepable T)))\<close>

abbreviation Inited_Var :: \<open>varname \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close> ("\<^bold>v\<^bold>a\<^bold>r[_] _" [22,22] 21)
  where \<open>Inited_Var vname T \<equiv> Var vname (\<black_circle> T)\<close>

abbreviation Uninited_Var :: \<open>varname \<Rightarrow> assn\<close> ("\<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[_]" [22] 21)
  where \<open>Uninited_Var vname \<equiv> () \<Ztypecolon> Var vname \<circle>\<close>

lemma Var_inhabited[\<phi>inhabitance_rule,elim!]:
  \<open>Inhabited (x \<Ztypecolon> Var vname T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Var_subty:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> Var v T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> Var v T' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma Var_view_shift:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> Var v T \<longmapsto> x' \<Ztypecolon> Var v T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Imply_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

lemma Var_cast_\<phi>app[\<phi>overload cast]: 
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[v] T \<longmapsto> x' \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[v] T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding Argument_def
  unfolding Imply_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

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
\<Longrightarrow> (x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[v] T) = (x' \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[v] T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup Var_simp_cong ("x \<Ztypecolon> Var v T") = \<open>
  K (Phi_SimpCong.simproc @{thm Var_simp_cong[folded atomize_eq]})
\<close>


subsubsection \<open>Rules\<close>

lemma [\<phi>reason 1200 for \<open>PROP Branch_Convergence_Type_Pattern (Var ?v ?T) ?X\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern (Var v T) (Var v T')\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..

lemma [\<phi>reason 1520 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?R \<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[?var] \<longmapsto> ?R' \<heavy_comma> \<blangle> ?x' \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[?var] ?T' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>]:
    \<comment> \<open>attempts the immediate cell\<close>
  " FAIL TEXT(\<open>Variable\<close> var \<open>has not been initialized.\<close>)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[var] \<longmapsto> R \<heavy_comma> \<blangle> x' \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T' \<brangle> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold><\<^bold>a\<^bold>c\<^bold>t\<^bold>i\<^bold>o\<^bold>n\<^bold>> ToSA \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding GOAL_CTXT_def Action_Tag_def by blast

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
  by (meson Var_view_shift \<phi>apply_view_shift \<phi>frame_view)


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
  by (meson Var_view_shift \<phi>apply_view_shift \<phi>view_shift_intro_frame)


section \<open>Instructions\<close>

subsection \<open>Variable Operations\<close>

definition \<phi>M_get_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc"
  where "\<phi>M_get_var vname TY F = R_var.\<phi>R_get_res_entry vname ((\<lambda>val.
            \<phi>M_assert (val \<in> Some ` Well_Type TY) \<ggreater> F (the val)) o nonsepable.dest)"

definition op_get_var :: "varname \<Rightarrow> TY \<Rightarrow> VAL proc"
  where "op_get_var vname TY = \<phi>M_get_var vname TY (\<lambda>x. Return (sem_value x))"

definition op_set_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL,unit) proc'"
  where "op_set_var vname TY v =
          \<phi>M_assert (pred_option (\<lambda>TY'. TY = TY') (varname.type vname)) \<ggreater>
          \<phi>M_getV TY id v (\<lambda>v.
          R_var.\<phi>R_set_res (\<lambda>f. f(vname := Some (nonsepable (Some v)))))"

definition op_free_var :: "varname \<Rightarrow> unit proc"
  where "op_free_var vname = R_var.\<phi>R_set_res (\<lambda>f. f(vname := None))"

definition op_var_scope' :: "TY option \<Rightarrow> (varname \<Rightarrow> 'ret proc) \<Rightarrow> 'ret proc"
  where "op_var_scope' TY F =
    R_var.\<phi>R_allocate_res_entry (\<lambda>v. varname.type v = TY) (Some (nonsepable None)) F"

lemma \<phi>M_get_var[intro!]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> v \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] Identity \<longmapsto> Y \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_var var TY F \<lbrace> v \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec \<phi>M_get_var_def
  by (clarsimp simp add: \<phi>expns FIC_var.expand simp del: set_mult_expn del: subsetI,
      rule R_var.\<phi>R_get_res_entry[where v=\<open>nonsepable (Some v)\<close>]; simp)

lemma \<phi>M_set_var[intro!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c R_var.\<phi>R_set_res (\<lambda>f. f(vname \<mapsto> nonsepable (Some u)))
      \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. u \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[vname] Identity \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  by (clarsimp simp add: \<phi>expns FIC_var.expand[where x=\<open>1(vname \<mapsto> nonsepable v)\<close>]
                                FIC_var.expand_subj[where x=\<open>1(vname \<mapsto> nonsepable (Some u))\<close>]
               simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_set_res[where P=\<open>\<lambda>_. True\<close>]; simp)

lemma op_get_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var var TY \<lbrace> v \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] Identity \<longmapsto> v \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] Identity \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding op_get_var_def Premise_def
  by (rule; rule; simp add: \<phi>expns)


lemma op_set_var''_\<phi>app:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e pred_option (\<lambda>TY'. TY = TY') (varname.type var)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_var var TY raw \<lbrace> v \<Ztypecolon> Var var Identity\<heavy_comma> u \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] Identity \<longmapsto> u \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] Identity \<rbrace>\<close>
  unfolding op_set_var_def Premise_def
  by (cases raw; simp; rule; simp add: \<phi>expns; rule)

lemma finite_map_freshness':
  \<open>finite (dom f) \<Longrightarrow> infinite P \<Longrightarrow> \<exists>x. f x = None \<and> x \<in> P\<close>
  by (meson domIff finite_subset subsetI)

lemma op_var_scope':
   \<open>(\<And>var. varname.type var \<equiv> TY \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> X\<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[var] \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope' TY F \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding op_var_scope'_def Premise_def
  apply (clarsimp simp add: \<phi>expns \<phi>Procedure_\<phi>Res_Spec simp del: set_mult_expn del: subsetI)
  subgoal for r res c
  apply (rule R_var.\<phi>R_allocate_res_entry[where R="(\<I> INTERP (r * c))"])
    apply (clarsimp) using finite_map_freshness' infinite_varname apply blast
      apply (clarsimp)

  apply (clarsimp simp add: Subjection_expn
                  simp del: \<phi>Res_Spec_mult_homo set_mult_expn del: subsetI)
  subgoal premises prems for k res'
  apply (rule prems(1)[THEN spec[where x=r], THEN spec[where x=res'],
              simplified prems, simplified, THEN mp], simp)
  apply (rule exI[where x=\<open>c * FIC_var.mk (1(k \<mapsto> nonsepable None))\<close>])
  apply (simp add: \<phi>expns prems)
    by (smt (verit, best) FIC_var.expand FIC_var.sep_disj_fiction Fic_Space_Un Fic_Space_mm \<phi>Res_Spec_mult_homo prems(3) prems(4) prems(5) prems(6) prems(7) sep_disj_multD2 sep_disj_multI2 sep_mult_assoc)
  . .

lemma op_free_var:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_var vname \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> 1 \<rbrace>\<close>
  unfolding op_free_var_def \<phi>Procedure_\<phi>Res_Spec
  by (clarsimp simp add: \<phi>expns FIC_var.expand simp del: set_mult_expn del: subsetI;
      rule R_var.\<phi>R_dispose_res[where any=\<open>nonsepable v\<close> and P=\<open>\<lambda>_. True\<close>];
      clarsimp simp add: \<phi>Res_Spec_mult_homo)



end


