chapter \<open>Typed Variable\<close>

text \<open>This is a generic formalization variables supporting either typed variables or non-typed.
If the formalization is untyped, variables in the formalization can be assigned by values of
any type.
You can set the flag \<phi>variable_is_typed to indicate whether the formalization of variables is typed.\<close>

theory PhiSem_Variable
  imports Phi_System.PhiSem_Formalization_Tools
  abbrevs "<var>" = "\<v>\<a>\<r>"
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Resource\<close>

declare [[typedef_overloaded]]
datatype varname = varname nat \<comment> \<open>nonce\<close> (type: \<open>TY option\<close>) \<comment> \<open>None denotes no type restriction.\<close>
hide_const (open) type
declare [[typedef_overloaded = false]]

setup \<open>Sign.mandatory_path "RES"\<close>

type_synonym Var = \<open>varname \<rightharpoonup> VAL option nosep\<close>
  \<comment> \<open>NONE: declared but not initialized.\<close>

setup \<open>Sign.parent_path\<close>

lemma infinite_varname:
  \<open>infinite {k. varname.type k = TY}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{k. varname.type k = TY}\<close>
        and f = \<open>\<lambda>n. varname n TY\<close>]
  using inj_def by fastforce

resource_space \<phi>var =
  Var  :: \<open>{vars::RES.Var. finite (dom vars)}\<close> (partial_map_resource) ..

hide_fact RES.\<phi>var_res_ax RES.\<phi>var_res_axioms RES.\<phi>var_res_fields_axioms


subsubsection \<open>Fiction\<close>

fiction_space \<phi>var =
  Var :: \<open>RES.Var.raw_basic_fiction \<F>_it\<close> (identity_fiction_for_partial_mapping_resource RES.Var) ..

hide_fact FIC.\<phi>var_fic_ax FIC.\<phi>var_fic_axioms



section \<open>\<phi>-Types\<close>

subsection \<open>Variable\<close>

abbreviation Var :: \<open>varname \<Rightarrow> (VAL option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Var vname T \<equiv> (FIC.Var.\<phi> (vname \<^bold>\<rightarrow> \<black_circle> (Nosep T)))\<close>

abbreviation Inited_Var :: \<open>varname \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close> ("\<v>\<a>\<r>[_] _" [22,22] 21)
  where \<open>Inited_Var vname T \<equiv> Var vname (\<black_circle> T)\<close>

abbreviation Uninited_Var :: \<open>varname \<Rightarrow> assn\<close> ("\<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[_]" [22] 21)
  where \<open>Uninited_Var vname \<equiv> () \<Ztypecolon> Var vname \<circle>\<close>

lemma Var_inhabited[\<phi>inhabitance_rule,elim!]:
  \<open>Inhabited (x \<Ztypecolon> Var vname T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Var_transformation:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> Var v T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> Var v T' \<a>\<n>\<d> P\<close>
  unfolding Imply_def by (simp add: \<phi>expns, blast)

lemma Var_cast_\<phi>app[\<phi>overload cast]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P
\<Longrightarrow> x \<Ztypecolon> \<v>\<a>\<r>[v] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> \<v>\<a>\<r>[v] T' \<a>\<n>\<d> P\<close>
  unfolding Argument_def
  unfolding Imply_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)

lemma Raw_Var_identity_eq:
  \<open>(raw \<Ztypecolon> Var v Identity) = (nosep raw \<Ztypecolon> FIC.Var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma UnInited_Var_identity_eq:
  \<open>(\<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[v]) = (nosep None \<Ztypecolon> FIC.Var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma Inited_Var_identity_eq:
  \<open>(raw \<Ztypecolon> \<v>\<a>\<r>[v] Identity) = (nosep (Some raw) \<Ztypecolon> FIC.Var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

(* lemma Var_ExTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (ExTyp T)) = (\<exists>*a. x a \<Ztypecolon> Var vname (T a))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma Var_SubjTyp[simp]:
  \<open>(x \<Ztypecolon> Var vname (T \<phi>\<s>\<u>\<b>\<j> P)) = (x \<Ztypecolon> Var vname T \<s>\<u>\<b>\<j> P)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns) *)

(*lemma [\<phi>reason 1200 for \<open>EqualAddress (?xa \<Ztypecolon> Var ?va ?Ta) (?xb \<Ztypecolon> Var ?vb ?Tb)\<close>]:
  \<open>EqualAddress (xa \<Ztypecolon> Var var Ta) (xb \<Ztypecolon> Var var Tb)\<close>
  unfolding EqualAddress_def .. *)


subsubsection \<open>Rules\<close>

lemma [\<phi>reason 1305 for \<open>_\<heavy_comma> _ \<Ztypecolon> Var _ _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<heavy_comma> \<blangle> _ \<Ztypecolon> Var _ _ \<brangle> \<a>\<n>\<d> _\<close>]:
  " R\<heavy_comma> x \<Ztypecolon> Var var T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R\<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> "
  unfolding Action_Tag_def FOCUS_TAG_def
  using implies_refl by blast

lemma [\<phi>reason 1300 for \<open>_\<heavy_comma> _ \<Ztypecolon> Var _ _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _\<heavy_comma> \<blangle> _ \<Ztypecolon> Var _ _ \<brangle> \<a>\<n>\<d> _\<close>
                     if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]:
  " x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> P
\<Longrightarrow> R\<heavy_comma> x \<Ztypecolon> Var var T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R\<heavy_comma> \<blangle> x' \<Ztypecolon> Var var T' \<brangle> \<a>\<n>\<d> P "
  unfolding Action_Tag_def FOCUS_TAG_def
  by (simp add: Var_transformation implies_left_prod)

lemma [\<phi>reason 1310]:
    \<comment> \<open>attempts the immediate cell\<close>
  " FAIL TEXT(\<open>Variable\<close> var \<open>has not been initialized.\<close>)
\<Longrightarrow> R \<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var] \<i>\<m>\<p>\<l>\<i>\<e>\<s> R \<heavy_comma> \<blangle> x' \<Ztypecolon> \<v>\<a>\<r>[var] T' \<brangle> \<a>\<n>\<d> P"
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 1280]:
  \<open> R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> R \<heavy_comma> H \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' \<heavy_comma> H \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<a>\<n>\<d> P\<close>
  using ToSA_skip .

lemma Var_simp_cong:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> \<v>\<a>\<r>[v] T) = (x' \<Ztypecolon> \<v>\<a>\<r>[v] T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup Var_simp_cong ("x \<Ztypecolon> Var v T") = \<open>
  K (Phi_SimpCong.simproc @{thm Var_simp_cong[folded atomize_eq]})
\<close>


lemma [\<phi>reason 1200 for \<open>PROP Branch_Convergence_Type_Pattern (Var ?v ?T) ?X\<close>]:
  \<open> PROP Branch_Convergence_Type_Pattern (Var v T) (Var v T')\<close>
  unfolding Branch_Convergence_Type_Pattern_def ..


lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Var v T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Var v U \<a>\<n>\<d> P @action to Z \<close>
  unfolding Action_Tag_def
  using Var_transformation .

lemma [\<phi>reason 2100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Var v T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Var v U \<a>\<n>\<d> P @action to (Var v Z) \<close>
  unfolding Action_Tag_def
  using Var_transformation .

lemma [\<phi>reason 2000]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as Z
\<Longrightarrow> x \<Ztypecolon> Var v T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Var v U \<a>\<n>\<d> P @action as Z \<close>
  unfolding Action_Tag_def
  using Var_transformation .

lemma [\<phi>reason 2100]:
  \<open> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Var v T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> Var v U \<a>\<n>\<d> P @action as (z \<Ztypecolon> Var v Z) \<close>
  unfolding Action_Tag_def
  using Var_transformation .


subsubsection \<open>Application Methods for Subtyping\<close>

lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?U \<a>\<n>\<d> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Var ?var ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?U \<a>\<n>\<d> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_def
  by (meson Var_transformation \<phi>apply_implication implies_left_prod)


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?x' \<Ztypecolon> ?T' \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?U \<a>\<n>\<d> ?P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Var ?var ?T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?y \<Ztypecolon> ?U \<a>\<n>\<d> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> x' \<Ztypecolon> T' \<a>\<n>\<d> Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (x' \<Ztypecolon> T' \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_def
  by (meson Var_transformation \<phi>apply_implication implies_left_prod)


section \<open>Instructions\<close>

subsection \<open>Variable Operations\<close>

definition \<phi>M_get_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc"
  where "\<phi>M_get_var vname TY F = RES.Var.\<phi>R_get_res_entry vname ((\<lambda>val.
            \<phi>M_assert (val \<in> Some ` Well_Type TY) \<ggreater> F (the val)) o nosep.dest)"

definition op_get_var :: "varname \<Rightarrow> TY \<Rightarrow> VAL proc"
  where "op_get_var vname TY = \<phi>M_get_var vname TY (\<lambda>x. Return (\<phi>arg x))"

definition op_set_var :: "varname \<Rightarrow> TY \<Rightarrow> (VAL,unit) proc'"
  where "op_set_var vname TY v =
          \<phi>M_assert (pred_option (\<lambda>TY'. TY = TY') (varname.type vname)) \<ggreater>
          \<phi>M_getV TY id v (\<lambda>v.
          RES.Var.\<phi>R_set_res (\<lambda>f. f(vname := Some (nosep (Some v)))))"

definition op_free_var :: "varname \<Rightarrow> unit proc"
  where "op_free_var vname = RES.Var.\<phi>R_set_res (\<lambda>f. f(vname := None))"

definition op_var_scope' :: "TY option \<Rightarrow> (varname \<Rightarrow> 'ret proc) \<Rightarrow> 'ret::VALs proc"
  where "op_var_scope' TY F =
    RES.Var.\<phi>R_allocate_res_entry (\<lambda>v. varname.type v = TY) (Some (nosep None)) F"

lemma \<phi>M_get_var[intro!]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> \<p>\<r>\<o>\<c> F v \<lbrace> v \<Ztypecolon> \<v>\<a>\<r>[var] Identity \<longmapsto> Y \<rbrace>
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_get_var var TY F \<lbrace> v \<Ztypecolon> \<v>\<a>\<r>[var] Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>M_get_var_def Inited_Var_identity_eq
  by (rule FIC.Var.\<phi>R_get_res_entry; simp)

lemma \<phi>M_set_var[intro!]:
  \<open>\<p>\<r>\<o>\<c> RES.Var.\<phi>R_set_res (\<lambda>f. f(vname \<mapsto> nosep (Some u)))
      \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. u \<Ztypecolon> \<v>\<a>\<r>[vname] Identity \<rbrace>\<close>
  unfolding Inited_Var_identity_eq
  unfolding Raw_Var_identity_eq
  thm FIC.Var.\<phi>R_set_res
  by (rule FIC.Var.\<phi>R_set_res[where P=\<open>\<lambda>_. True\<close>]; simp)

lemma op_get_var''_\<phi>app:
   \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_var var TY \<lbrace> v \<Ztypecolon> \<v>\<a>\<r>[var] Identity \<longmapsto> v \<Ztypecolon> \<v>\<a>\<r>[var] Identity \<heavy_comma> \<v>\<a>\<l> v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding op_get_var_def Premise_def
  by (rule; rule; simp add: \<phi>expns)


lemma op_set_var''_\<phi>app:
   \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> pred_option (\<lambda>TY'. TY = TY') (varname.type var)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> u \<in> Well_Type TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_var var TY raw \<lbrace> v \<Ztypecolon> Var var Identity\<heavy_comma> u \<Ztypecolon> \<v>\<a>\<l>[raw] Identity \<longmapsto> u \<Ztypecolon> \<v>\<a>\<r>[var] Identity \<rbrace>\<close>
  unfolding op_set_var_def Premise_def
  by (cases raw; simp; rule; simp add: \<phi>expns; rule)

lemma finite_map_freshness':
  \<open>finite (dom f) \<Longrightarrow> infinite P \<Longrightarrow> \<exists>x. f x = None \<and> x \<in> P\<close>
  by (meson domIff finite_subset subsetI)

lemma op_var_scope':
   \<open>(\<And>var. varname.type var \<equiv> TY \<Longrightarrow> \<p>\<r>\<o>\<c> F var \<lbrace> X\<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var] \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E  )
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope' TY F \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding op_var_scope'_def UnInited_Var_identity_eq
  thm FIC.Var.\<phi>R_allocate_res_entry
  apply (rule FIC.Var.\<phi>R_allocate_res_entry; simp)
  using finite_map_freshness' infinite_varname by blast

lemma op_free_var:
   \<open>\<p>\<r>\<o>\<c> op_free_var vname \<lbrace> v \<Ztypecolon> Var vname Identity \<longmapsto> \<lambda>_. Void \<rbrace>\<close>
  unfolding op_free_var_def Raw_Var_identity_eq
  by (rule FIC.Var.\<phi>R_dispose_res[where P=\<open>\<lambda>_. True\<close>]; simp)



section \<open>IDE-CP Operations\<close>

subsection \<open>Syntax\<close>

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (?var::varname) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

subsection \<open>Reasoning Process\<close>

subsubsection \<open>Infer Semantic Type of Variable\<close>

consts infer_var_type :: \<open>action\<close>

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
  input  \<open>x \<Ztypecolon> \<v>\<a>\<r>[var] T\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<r>[var] T\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> T\<close>
  \<medium_left_bracket> to Identity  op_get_var'' \<medium_right_bracket>. .

lemma [\<phi>reason 1200]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y\<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<r>[var] T \<brangle> \<a>\<n>\<d> Any
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_var var TY \<lbrace> X \<longmapsto> Y\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<r>[var] T \<heavy_comma> \<blangle> \<v>\<a>\<l> x <val-of> var \<Ztypecolon> T \<brangle> \<rbrace> @action synthesis\<close>
  unfolding Action_Tag_def
  \<medium_left_bracket> premises GetVar and _
    GetVar op_get_var \<medium_right_bracket>. .



subsubsection \<open>Set\<close>

lemma op_set_var_\<phi>app:
  assumes [unfolded Action_Tag_def, useful]:
      \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type\<close>
  assumes [unfolded \<phi>SemType_def subset_iff, useful]:
      \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  shows \<open>\<p>\<r>\<o>\<c> op_set_var var TY \<a>\<r>\<g> \<lbrace> x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[\<a>\<r>\<g>] U \<longmapsto> \<lambda>\<r>\<e>\<t>. y \<Ztypecolon> \<v>\<a>\<r>[var] U \<rbrace> \<close>
  \<medium_left_bracket> to Identity
    \<open>var\<close> to Identity
    op_set_var''
  \<medium_right_bracket>. .

lemma op_set_var__synthesis [\<phi>reason 1200 for
  \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> \<blangle> (?y <set-to> ?var) \<Ztypecolon> ?U ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action synthesis\<close>
]:
assumes G: \<open>\<p>\<r>\<o>\<c> g \<lbrace> X \<longmapsto> X1\<heavy_comma> \<blangle> \<v>\<a>\<l> y \<Ztypecolon> U \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis \<close>
  and P: \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type\<close>
  and S[unfolded Action_Tag_def]:
         \<open>X1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y\<heavy_comma> x \<Ztypecolon> Var var T \<a>\<n>\<d> Any @action ToSA\<close>
  and [\<phi>reason]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
shows \<open>\<p>\<r>\<o>\<c> (g \<bind> (\<lambda>\<v>0. op_set_var var TY \<v>0 \<ggreater> (op_get_var var TY)))
            \<lbrace> X \<longmapsto> Y\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U \<heavy_comma> \<blangle> \<v>\<a>\<l> (y <set-to> var) \<Ztypecolon> U \<brangle> \<rbrace>
       \<t>\<h>\<r>\<o>\<w>\<s> E  @action synthesis\<close>
  \<medium_left_bracket> G S op_set_var P op_get_var \<medium_right_bracket>. .


subsubsection \<open>Declare New Variables\<close>

proc op_var_scope:
  assumes BLK: \<open>\<And>var. varname.type var \<equiv> TY
                  \<Longrightarrow> \<p>\<r>\<o>\<c> F var \<lbrace> X\<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var] \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                      \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any) \<close>
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
  \<open> \<p>\<r>\<o>\<c> g \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U\<heavy_comma> X \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_set_var var TY raw \<ggreater> g) \<lbrace> R\<heavy_comma> (x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X) \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G and P and [\<phi>reason]
    op_set_var P G
  \<medium_right_bracket> .. .

lemma "__new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> TY
              \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> R\<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var]\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any))
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope TYPE('a::VALs) TY g \<lbrace> R\<heavy_comma> X \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G
    op_var_scope[where TY=\<open>TY\<close>] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>] G \<medium_right_bracket>.
  \<medium_right_bracket> .. .


lemma "__set_new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> Some TY
              \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any ))
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope TYPE('a::VALs) (Some TY) (\<lambda>var. op_set_var var TY raw \<ggreater> g var)
     \<lbrace> R\<heavy_comma> (y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X) \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G and [\<phi>reason]
    op_var_scope[where TY=\<open>Some TY\<close>] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      op_set_var G
    \<medium_right_bracket>.
  \<medium_right_bracket>. .

lemma "__set_new_var_noty_rule__":
  \<open> (\<And>var. varname.type var \<equiv> None
              \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U\<heavy_comma> X \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any))
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope TYPE('a::VALs) None (\<lambda>var. op_set_var var TY raw \<ggreater> g var)
     \<lbrace> R\<heavy_comma> (y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X) \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G and [\<phi>reason]
    op_var_scope[where TY=None] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      op_set_var G
    \<medium_right_bracket>.
  \<medium_right_bracket>. .


ML_file "library/variable.ML"

end


