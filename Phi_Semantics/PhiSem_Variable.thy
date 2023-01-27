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

interpretation FIC_var: identity_fiction_for_partial_mapping_resource \<open>{vars. finite (dom vars)}\<close> R_var FIC_var ..


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

lemma Var_ToA:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> Var v T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> Var v T' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma Var_view_shift:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> Var v T \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s x' \<Ztypecolon> Var v T' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

lemma Var_cast_\<phi>app[\<phi>overload cast]: 
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[v] T \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s x' \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[v] T' \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Argument_def
  unfolding Imply_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

lemma Raw_Var_identity_eq:
  \<open>(raw \<Ztypecolon> Var v Identity) = (nonsepable raw \<Ztypecolon> FIC_var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma UnInited_Var_identity_eq:
  \<open>(\<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[v]) = (nonsepable None \<Ztypecolon> FIC_var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma Inited_Var_identity_eq:
  \<open>(raw \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[v] Identity) = (nonsepable (Some raw) \<Ztypecolon> FIC_var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

(* lemma Var_ExTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (ExTyp T)) = (\<exists>*a. x a \<Ztypecolon> Var vname (T a))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma Var_SubjTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)) = (x \<Ztypecolon> Var vname T \<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns) *)

(*lemma [\<phi>reason 1200 for \<open>EqualAddress (?xa \<Ztypecolon> Var ?va ?Ta) (?xb \<Ztypecolon> Var ?vb ?Tb)\<close>]:
  \<open>EqualAddress (xa \<Ztypecolon> Var var Ta) (xb \<Ztypecolon> Var var Tb)\<close>
  unfolding EqualAddress_def .. *)

lemma [\<phi>reason 1305 for \<open>?R \<heavy_comma> ?H \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?R''' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P  @action reason_ToSA True ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> R\<heavy_comma> x \<Ztypecolon> Var var T \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R\<heavy_comma> \<blangle> x' \<Ztypecolon> Var var T' \<brangle> \<^bold>a\<^bold>n\<^bold>d P  @action reason_ToSA True G"
  unfolding Action_Tag_def FOCUS_TAG_def
  by (simp add: Var_view_shift \<phi>frame_view)

lemma [\<phi>reason 1300 for \<open>?R \<heavy_comma> ?H \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?R''' * \<blangle> ?X \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P  @action reason_ToSA ?mode ?G\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> R\<heavy_comma> x \<Ztypecolon> Var var T \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R\<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> @action reason_ToSA mode G"
  unfolding Action_Tag_def FOCUS_TAG_def
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

lemma [\<phi>reason 1520 for \<open>?R \<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[?var] \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?R' \<heavy_comma> \<blangle> ?x' \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[?var] ?T' \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA True ?G\<close>]:
    \<comment> \<open>attempts the immediate cell\<close>
  " FAIL TEXT(\<open>Variable\<close> var \<open>has not been initialized.\<close>)
\<Longrightarrow> R \<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[var] \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R \<heavy_comma> \<blangle> x' \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T' \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA True G"
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 1500 for \<open>?R \<heavy_comma> ?H \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?R''' * \<blangle> ?x \<Ztypecolon> Var ?var ?T \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA True ?G\<close>]:
    \<comment> \<open>attempts the immediate cell\<close>
  " CHK_SUBGOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> R \<heavy_comma> x \<Ztypecolon> Var var T \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R \<heavy_comma> \<blangle> x' \<Ztypecolon> Var var T' \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA True G"
  unfolding Action_Tag_def FOCUS_TAG_def
  by (simp add: Var_view_shift \<phi>frame_view)

lemma [\<phi>reason 1450 for \<open>?R \<heavy_comma> ?H \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s ?R''' * \<blangle> ?x \<Ztypecolon> Var ?var ?T \<brangle> \<^bold>a\<^bold>n\<^bold>d ?P @action reason_ToSA ?mode ?G\<close>]:
  \<open> R \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R' \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<^bold>a\<^bold>n\<^bold>d P  @action reason_ToSA mode G
\<Longrightarrow> R \<heavy_comma> H \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s R' \<heavy_comma> H \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<^bold>a\<^bold>n\<^bold>d P @action reason_ToSA mode G\<close>
  using ToSA_skip[OF CHK_SUBGOAL_I] .


lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P @action to Target
\<Longrightarrow> x \<Ztypecolon> Var v T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> Var v U \<^bold>a\<^bold>n\<^bold>d P @action to Target \<close>
  unfolding Action_Tag_def
  using Var_ToA .


subsubsection \<open>Application Methods for Subtyping\<close>

lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Var ?var ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def
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
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x' \<Ztypecolon> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def
  by (meson Var_view_shift \<phi>apply_view_shift \<phi>view_shift_intro_frame)


section \<open>Instructions\<close>

subsection \<open>Variable Operations\<close>

definition \<phi>M_get_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc"
  where "\<phi>M_get_var vname TY F = R_var.\<phi>R_get_res_entry vname ((\<lambda>val.
            \<phi>M_assert (val \<in> Some ` Well_Type TY) \<ggreater> F (the val)) o nonsepable.dest)"

definition op_get_var :: "varname \<Rightarrow> TY \<Rightarrow> VAL proc"
  where "op_get_var vname TY = \<phi>M_get_var vname TY (\<lambda>x. Return (\<phi>arg x))"

definition op_set_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL,unit) proc'"
  where "op_set_var vname TY v =
          \<phi>M_assert (pred_option (\<lambda>TY'. TY = TY') (varname.type vname)) \<ggreater>
          \<phi>M_getV TY id v (\<lambda>v.
          R_var.\<phi>R_set_res (\<lambda>f. f(vname := Some (nonsepable (Some v)))))"

definition op_free_var :: "varname \<Rightarrow> unit proc"
  where "op_free_var vname = R_var.\<phi>R_set_res (\<lambda>f. f(vname := None))"

definition op_var_scope' :: "TY option \<Rightarrow> (varname \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc"
  where "op_var_scope' TY F =
    R_var.\<phi>R_allocate_res_entry (\<lambda>v. varname.type v = TY) (Some (nonsepable None)) F"

lemma \<phi>M_get_var[intro!]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> v \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] Identity \<longmapsto> Y \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_var var TY F \<lbrace> v \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>M_get_var_def Inited_Var_identity_eq
  by (rule FIC_var.\<phi>R_get_res_entry; simp)

lemma \<phi>M_set_var[intro!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c R_var.\<phi>R_set_res (\<lambda>f. f(vname \<mapsto> nonsepable (Some u)))
      \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. u \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[vname] Identity \<rbrace>\<close>
  unfolding Inited_Var_identity_eq
  unfolding Raw_Var_identity_eq
  thm FIC_var.\<phi>R_set_res
  by (rule FIC_var.\<phi>R_set_res[where P=\<open>\<lambda>_. True\<close>]; simp)

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
   \<open>(\<And>var. varname.type var \<equiv> TY \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> X\<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[var] \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope' TY F \<lbrace> X \<longmapsto> Y \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding op_var_scope'_def UnInited_Var_identity_eq
  thm FIC_var.\<phi>R_allocate_res_entry
  apply (rule FIC_var.\<phi>R_allocate_res_entry; simp)
  using finite_map_freshness' infinite_varname by blast

lemma op_free_var:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_var vname \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding op_free_var_def Raw_Var_identity_eq
  by (rule FIC_var.\<phi>R_dispose_res[where P=\<open>\<lambda>_. True\<close>]; simp)



section \<open>IDE-CP Operations\<close>

subsection \<open>Syntax\<close>

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (?var::varname) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

subsection \<open>Reasoning Process\<close>

subsubsection \<open>Infer Semantic Type of Variable\<close>

consts infer_var_type :: \<open>unit action\<close>

lemma [\<phi>reason 1000]:
  \<open> varname.type var \<equiv> TY'
\<Longrightarrow> pred_option ((=) TY) TY' @action infer_var_type
\<Longrightarrow> pred_option ((=) TY) (varname.type var) @action infer_var_type\<close>
  \<comment> \<open>TY is the output. The rule invokes evaluation of the \<open>varname.type var\<close>.\<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open>pred_option ((=) TY) None @action infer_var_type\<close>
  \<comment> \<open>the output TY can be anything freely\<close>
  by simp

lemma [\<phi>reason 1000 for \<open>pred_option ((=) ?TY') (Some ?TY) @action infer_var_type\<close>]:
  \<open>pred_option ((=) TY) (Some TY) @action infer_var_type\<close>
  \<comment> \<open>the output TY equals to that TY in \<open>Some TY\<close> exactly.\<close>
  by simp


lemma
  \<open>pred_option (\<lambda>TY'. TY = TY') None\<close>
  \<open>pred_option (\<lambda>TY'. TY = TY') (Some TY)\<close>
  by simp+


subsection \<open>Rules of Variable Operations\<close>

subsubsection \<open>Get\<close>

proc (nodef) op_get_var:
  assumes [unfolded \<phi>SemType_def subset_iff, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  input  \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T\<close>
  output \<open>x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l T\<close>
  \<medium_left_bracket> to Identity  op_get_var'' \<medium_right_bracket>. .

lemma [\<phi>reason 1200 for
    \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> SYNTHESIS ?x <val-of> ?var \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
  \<open> SUBGOAL G G2
\<Longrightarrow> X \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y\<heavy_comma> \<blangle> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T \<brangle> @action reason_ToSA True G2
\<Longrightarrow> SOLVE_SUBGOAL G2
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_var var TY \<lbrace> X \<longmapsto> Y\<heavy_comma> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] T \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l x <val-of> var \<Ztypecolon> T \<rbrace> @action synthesis G\<close>
  unfolding Action_Tag_def
  \<medium_left_bracket> premises _ and GetVar and _ and [\<phi>reason]
    GetVar op_get_var \<medium_right_bracket>. .



subsubsection \<open>Set\<close>

lemma op_set_var_\<phi>app:
  assumes [unfolded Action_Tag_def, useful]:
      \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type\<close>
  assumes [unfolded \<phi>SemType_def subset_iff, useful]:
      \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  shows \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_var var TY \<a>\<r>\<g> \<lbrace> x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[\<a>\<r>\<g>] U \<longmapsto> \<lambda>\<r>\<e>\<t>. y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U \<rbrace> \<close>
  \<medium_left_bracket> to Identity 
    $y to Identity
    op_set_var'' 
  \<medium_right_bracket>. .

(* proc (nodef) op_set_var:
  assumes [unfolded Action_Tag_def, useful]:
      \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type\<close>
  assumes [unfolded \<phi>SemType_def subset_iff, useful]:
      \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  input  \<open>x \<Ztypecolon> Var var T\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> U\<close>
  output \<open>y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<close>
  \<medium_left_bracket> to_Identity 
    $y to_Identity
    op_set_var'' 
  \<medium_right_bracket>. .
*)
schematic_goal op_set_var__synthesis [\<phi>reason 1200 for 
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> SYNTHESIS (?y <set-to> ?var) \<Ztypecolon> ?U ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E  @action synthesis ?G\<close>
]:
assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> X \<longmapsto> X1\<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> U \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E @action synthesis G \<close>
  and P: \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type\<close>
  and S[unfolded Action_Tag_def]:
         \<open>X1 \<^bold>s\<^bold>h\<^bold>i\<^bold>f\<^bold>t\<^bold>s Y\<heavy_comma> x \<Ztypecolon> Var var T \<^bold>a\<^bold>n\<^bold>d Any @action ToSA\<close>
  and [\<phi>reason]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
shows \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?FF \<lbrace> X \<longmapsto> Y\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U \<heavy_comma> SYNTHESIS \<^bold>v\<^bold>a\<^bold>l (y <set-to> var) \<Ztypecolon> U \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  @action synthesis G\<close>
  \<medium_left_bracket> G S op_set_var P op_get_var \<medium_right_bracket>. .


subsubsection \<open>Declare New Variables\<close>

declare [[eta_contract=false]]

proc op_var_scope:
  assumes BLK: \<open>\<And>var. varname.type var \<equiv> TY
                  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F var \<lbrace> X\<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[var] \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                      \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any) \<close>
  input  \<open>X\<close>
  output \<open>Y\<close>
  throws  E
  \<medium_left_bracket> op_var_scope'[where TY=TY]
    try''
    \<medium_left_bracket> premises [\<phi>reason]
      BLK to Identity op_free_var \<medium_right_bracket>.
    \<medium_left_bracket> to Identity
      op_free_var
      throw \<medium_right_bracket>. 
  \<medium_right_bracket>. .

subsection \<open>Implementing IDE-CP Generic Variable Access\<close>

lemma "__set_var_rule__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<heavy_comma> X \<longmapsto> Z \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E 
\<Longrightarrow> pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (op_set_var var TY raw \<ggreater> g) \<lbrace> R\<heavy_comma> (x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] U\<heavy_comma> X) \<longmapsto> Z \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  \<medium_left_bracket> premises G and P and [\<phi>reason]
    op_set_var P G
  \<medium_right_bracket> .. .

lemma "__new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> TY
              \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g var \<lbrace> R\<heavy_comma> \<^bold>u\<^bold>n\<^bold>i\<^bold>n\<^bold>i\<^bold>t\<^bold>e\<^bold>d \<^bold>v\<^bold>a\<^bold>r[var]\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TYPE('a::VALs) TY g \<lbrace> R\<heavy_comma> X \<longmapsto> Z \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  \<medium_left_bracket> premises G
    op_var_scope[where TY=\<open>TY\<close>] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>] G \<medium_right_bracket>.
  \<medium_right_bracket> .. .


lemma "__set_new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> Some TY
              \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g var \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any ))
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TYPE('a::VALs) (Some TY) (\<lambda>var. op_set_var var TY raw \<ggreater> g var)
     \<lbrace> R\<heavy_comma> (y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] U\<heavy_comma> X) \<longmapsto> Z \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  \<medium_left_bracket> premises G and [\<phi>reason]
    op_var_scope[where TY=\<open>Some TY\<close>] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      op_set_var G
    \<medium_right_bracket>.
  \<medium_right_bracket>. .

lemma "__set_new_var_noty_rule__":
  \<open> (\<And>var. varname.type var \<equiv> None
              \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g var \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>r[var] U\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any))
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_var_scope TYPE('a::VALs) None (\<lambda>var. op_set_var var TY raw \<ggreater> g var)
     \<lbrace> R\<heavy_comma> (y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] U\<heavy_comma> X) \<longmapsto> Z \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  \<medium_left_bracket> premises G and [\<phi>reason]
    op_var_scope[where TY=None] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      op_set_var G
    \<medium_right_bracket>.
  \<medium_right_bracket>. .


ML_file "library/variable.ML"

end


