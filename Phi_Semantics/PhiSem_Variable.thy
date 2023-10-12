chapter \<open>Typed Variable\<close>

text \<open>This is a generic formalization variables supporting either typed variables or non-typed.
If the formalization is untyped, variables in the formalization can be assigned by values of
any type.
You can set the flag \<phi>variable_is_typed to indicate whether the formalization of variables is typed.\<close>

theory PhiSem_Variable
  imports Phi_System.Resource_Template PhiSem_Aggregate_Base
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

(*TODO: polish this*)

resource_space \<phi>var =
  Var  :: \<open>{vars::RES.Var. finite (dom vars)}\<close> (partial_map_resource \<open>(\<lambda>_::varname. UNIV :: VAL option nosep set)\<close>)
  by (standard, simp, metis domIff notin_range_Some)

hide_fact RES.\<phi>var_res_ax RES.\<phi>var_res_axioms RES.\<phi>var_res_fields_axioms


subsubsection \<open>Fiction\<close>

fiction_space \<phi>var =
  Var :: \<open>RES.Var.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>_. \<F>_it)\<close>
            (pointwise_fiction_for_partial_mapping_resource RES.Var \<open>(\<lambda>_::varname. UNIV :: VAL option nosep set)\<close>)
  by (standard; simp add: set_eq_iff)

hide_fact FIC.\<phi>var_fic_ax FIC.\<phi>var_fic_axioms



section \<open>\<phi>-Types\<close>

subsection \<open>Variable\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Var :: \<open>varname \<Rightarrow> (VAL option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Var vname T \<equiv> (FIC.Var.\<phi> (vname \<^bold>\<rightarrow> \<black_circle> (Nosep T)))\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and \<open>Gen_Br_Join (Var v) (Var v) (Var v) P True \<close>

(* abbreviation Var :: \<open>varname \<Rightarrow> (VAL option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Var vname T \<equiv> (FIC.Var.\<phi> (vname \<^bold>\<rightarrow> \<black_circle> (Nosep T)))\<close> *)

abbreviation Inited_Var :: \<open>varname \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Inited_Var vname T \<equiv> Var vname (\<black_circle> T)\<close>

abbreviation Uninited_Var :: \<open>varname \<Rightarrow> assn\<close> ("\<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[_]" [22] 21)
  where \<open>Uninited_Var vname \<equiv> () \<Ztypecolon> Var vname \<circle>\<close>

subsubsection \<open>Syntax\<close>

syntax Inited_Var_ :: \<open>logic \<Rightarrow> logic\<close> ("\<v>\<a>\<r>[_]")

ML_file "library/variable_pre.ML"

parse_translation \<open>let

fun get_bound ctxt (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ X $ _) = get_bound ctxt X
  | get_bound ctxt (Free (N, _)) = Option.map (K N) (Generic_Variable_Access.lookup_bindings ctxt N)
  | get_bound _ _ = NONE

in [
  (\<^syntax_const>\<open>Inited_Var_\<close>, (fn ctxt => fn [v] =>
    Const (\<^const_abbrev>\<open>Inited_Var\<close>, dummyT)
        $ (if Generic_Variable_Access.is_under_value_context ctxt
           then (case get_bound ctxt v
                   of SOME N => Const (\<^const_name>\<open>\<phi>identifier\<close>, dummyT) $ Abs (N, dummyT, Term.dummy)
                    | NONE => v)
           else v)))
] end\<close>

print_translation \<open>let

fun recovery ctxt (Const (\<^syntax_const>\<open>_free\<close>, _) $ X) = recovery ctxt X
  | recovery ctxt (Free (N, TY)) =
     (case Phi_Variable.external_name_of ctxt N
        of SOME N' => SOME (Free (N', TY))
         | _       => NONE)
  | recovery ctxt (Var ((N,idx), TY)) =
     (case Phi_Variable.external_name_of ctxt N
        of SOME N' => SOME (Var ((N',idx), TY))
         | _       => NONE)
  | recovery _ _ = NONE

fun recovery' ctxt X = case recovery ctxt X of SOME Y => Y | _ => X

in [(\<^const_syntax>\<open>Inited_Var\<close>, (fn ctxt => fn [a,b] =>
      Const(\<^syntax_const>\<open>Inited_Var_\<close>, dummyT) $ recovery' ctxt a $ b))]
end
\<close>

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (?v::varname) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (Var ?var) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (Var var) (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (Inited_Var ?var) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (Inited_Var var) (\<lambda>_. x \<Ztypecolon> Inited_Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (Uninited_Var ?var) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (Uninited_Var var) (\<lambda>_. Uninited_Var var :: assn)\<close>
  unfolding Synthesis_Parse_def ..



subsubsection \<open>Properties\<close>

(*
lemma Var_inhabited[elim!]:
  \<open>Inhabited (x \<Ztypecolon> Var vname T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: )

lemma Var_transformation:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> Var v T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> Var v T' \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (simp add: \<phi>expns, blast)

lemma Var_cast_\<phi>app[\<phi>overload cast]:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<v>\<a>\<r>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> \<v>\<a>\<r>[v] T' \<w>\<i>\<t>\<h> P\<close>
  unfolding Argument_def
  unfolding Transformation_def View_Shift_def
  by (clarsimp simp add: \<phi>expns, metis)
*)

lemma Raw_Var_identity_eq:
  \<open>(raw \<Ztypecolon> Var v Itself) = (1(v \<mapsto> nosep raw) \<Ztypecolon> FIC.Var.\<phi> Itself)\<close>
  unfolding BI_eq_iff
  by simp

lemma UnInited_Var_identity_eq:
  \<open>(\<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[v]) = (nosep None \<Ztypecolon> FIC.Var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Itself))\<close>
  unfolding BI_eq_iff
  by simp

lemma Inited_Var_identity_eq:
  \<open>(raw \<Ztypecolon> \<v>\<a>\<r>[v] Itself) = (1(v \<mapsto> nosep (Some raw)) \<Ztypecolon> FIC.Var.\<phi> Itself)\<close>
  unfolding BI_eq_iff
  by simp

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

(* TODO
lemma [\<phi>reason 1305 for \<open>_\<heavy_comma> _ \<Ztypecolon> Var _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _\<heavy_comma> \<blangle> _ \<Ztypecolon> Var _ _ \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  " R\<heavy_comma> x \<Ztypecolon> Var var T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R\<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> "
  unfolding Action_Tag_def FOCUS_TAG_def
  using transformation_refl by blast

lemma [\<phi>reason 1300 for \<open>_\<heavy_comma> _ \<Ztypecolon> Var _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _\<heavy_comma> \<blangle> _ \<Ztypecolon> Var _ _ \<brangle> \<w>\<i>\<t>\<h> _\<close>
                     if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]:
  " x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> P
\<Longrightarrow> R\<heavy_comma> x \<Ztypecolon> Var var T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R\<heavy_comma> \<blangle> x' \<Ztypecolon> Var var T' \<brangle> \<w>\<i>\<t>\<h> P "
  unfolding Action_Tag_def FOCUS_TAG_def
  by (simp add: Var_transformation transformation_left_frame)

lemma [\<phi>reason 1310]:
    \<comment> \<open>attempts the immediate cell\<close>
  " FAIL TEXT(\<open>Variable\<close> var \<open>has not been initialized.\<close>)
\<Longrightarrow> R \<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var] \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<heavy_comma> \<blangle> x' \<Ztypecolon> \<v>\<a>\<r>[var] T' \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Action_Tag_def by blast

lemma [\<phi>reason 1280]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> H \<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<brangle> \<w>\<i>\<t>\<h> P\<close>
  using NToA_skip .
*)



lemma [\<phi>reason 2100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to Z
\<Longrightarrow> x \<Ztypecolon> Var v T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Var v U \<s>\<u>\<b>\<j> y. r y \<w>\<i>\<t>\<h> P @action to (Var v Z) \<close>
  unfolding Action_Tag_def Transformation_def
  by (auto simp add: \<phi>expns, metis)


lemma [\<phi>reason 2100]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Z)
\<Longrightarrow> x \<Ztypecolon> Var v T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Var v U \<w>\<i>\<t>\<h> P @action as (z \<Ztypecolon> Var v Z) \<close>
  unfolding Action_Tag_def
  using Var_transformation .


subsubsection \<open>Application Methods for Subtyping\<close>

lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Var ?var ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_def
  by (meson Var_transformation \<phi>apply_implication transformation_left_frame)


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?x' \<Ztypecolon> ?T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R\<heavy_comma> ?x \<Ztypecolon> Var ?var ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Var ?var ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (x' \<Ztypecolon> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> x \<Ztypecolon> Var var T))
      (Trueprop ((\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> y \<Ztypecolon> Var var U) \<and> P))\<close>
  unfolding \<phi>Application_def
  by (meson Var_transformation \<phi>apply_implication transformation_left_frame)


section \<open>Instructions\<close>

subsection \<open>Preliminary - Reasoning Process\<close>

subsubsection \<open>Infer Semantic Type of Variable\<close>

consts infer_var_type :: \<open>action\<close>

lemma [\<phi>reason 1000]:
  \<open> varname.type var \<equiv> TY'
\<Longrightarrow> pred_option ((=) TY) TY' @action infer_var_type
\<Longrightarrow> pred_option ((=) TY) (varname.type var) @action infer_var_type\<close>
  \<comment> \<open>TY is the output. The rule invokes evaluation of the \<open>varname.type var\<close>.\<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open>pred_option P None @action infer_var_type\<close>
  \<comment> \<open>the output TY can be anything freely\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1020 for \<open>pred_option ((=) ?TY') (Some ?TY) @action infer_var_type\<close>]:
  \<open>pred_option ((=) TY) (Some TY) @action infer_var_type\<close>
  \<comment> \<open>the output TY equals to that TY in \<open>Some TY\<close> exactly.\<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> P TY
\<Longrightarrow> pred_option P (Some TY) @action infer_var_type\<close>
  \<comment> \<open>the output TY equals to that TY in \<open>Some TY\<close> exactly.\<close>
  unfolding Action_Tag_def
  by simp

subsubsection \<open>Aggregate_Mapper that can handle option\<close>

definition \<open>index_mode_value_opt idx g = (\<lambda>u. case u of Some u' \<Rightarrow> index_mod_value idx (g o Some) u' | _ \<Rightarrow> g None)\<close>

definition \<phi>Aggregate_Mapper_Opt :: \<open>aggregate_path \<Rightarrow> (VAL option,'a) \<phi> \<Rightarrow> (VAL,'a2) \<phi> \<Rightarrow> (VAL option,'b) \<phi> \<Rightarrow> (VAL,'b2) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b2) \<Rightarrow> 'a \<Rightarrow> 'a2) \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Mapper_Opt idx T T' U U' f
    \<longleftrightarrow> (\<forall>g g'. \<phi>Type_Mapping U U' g' g \<longrightarrow> \<phi>Type_Mapping T T' (f g') (index_mode_value_opt idx g)) \<close>

declare [[\<phi>reason_default_pattern \<open>\<phi>Aggregate_Mapper_Opt ?idx ?T _ _ _ _ \<close> \<Rightarrow> \<open>\<phi>Aggregate_Mapper_Opt ?idx ?T _ _ _ _\<close> (100) ]]

lemma \<phi>Aggregate_Mapper_Opt_Nil[\<phi>reason 1200]:
  \<open>\<phi>Aggregate_Mapper_Opt [] U U' U U' id\<close>
  unfolding \<phi>Aggregate_Mapper_Opt_def index_mode_value_opt_def
  by (clarsimp simp add: \<phi>Type_Mapping_def split: option.split)

lemma [\<phi>reason 1180]:
  \<open> \<phi>Aggregate_Mapper idx T T' U U' f
\<Longrightarrow> \<phi>Aggregate_Mapper_Opt idx (\<black_circle> T) T' (\<black_circle> U) U' f\<close>
  unfolding \<phi>Aggregate_Mapper_Opt_def \<phi>Aggregate_Mapper_def index_mode_value_opt_def
  by (clarsimp simp add: \<phi>Type_Mapping_def \<phi>Some_expn split: option.split)

definition \<open>\<phi>SemType_opt S TY \<longleftrightarrow> (case TY of Some TY' \<Rightarrow> (\<forall>p. p \<Turnstile> S \<longrightarrow> (\<exists>p'. p = Some p' \<and> p' \<in> Well_Type TY'))
                                            | _ \<Rightarrow> S = {None}) \<close>

declare [[\<phi>reason_default_pattern \<open>\<phi>SemType_opt ?S _\<close> \<Rightarrow> \<open>\<phi>SemType_opt ?S _\<close> (100) ]]

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType_opt (x \<Ztypecolon> \<black_circle> T) (Some TY)\<close>
  unfolding \<phi>SemType_opt_def \<phi>SemType_def
  by (clarsimp simp add: image_iff subset_iff)

lemma [\<phi>reason 1200]:
  \<open>\<phi>SemType_opt (x \<Ztypecolon> \<circle>) None\<close>
  unfolding \<phi>SemType_opt_def
  by (clarsimp simp add: set_eq_iff)

definition \<open>
  parse_element_index_input_by_semantic_type_at_least_1_opt TY input_index sidx idx pidx reject
    \<longleftrightarrow> (case TY of Some TY' \<Rightarrow> parse_element_index_input_by_semantic_type_at_least_1 TY' input_index sidx idx pidx reject
                  | None \<Rightarrow> reject = input_index \<and> sidx = [] \<and> idx = [] \<and> pidx = [])
\<close>

lemma [\<phi>reason 1000]:
  \<open> parse_element_index_input_by_semantic_type_at_least_1 TY input_index sidx idx pidx reject
\<Longrightarrow> parse_element_index_input_by_semantic_type_at_least_1_opt (Some TY) input_index sidx idx pidx reject\<close>
  unfolding parse_element_index_input_by_semantic_type_at_least_1_opt_def
            parse_element_index_input_by_semantic_type_at_least_1_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> parse_element_index_input_by_semantic_type_at_least_1_opt None input [] [] [] input\<close>
  unfolding parse_element_index_input_by_semantic_type_at_least_1_opt_def
  by simp

lemma parse_element_index_input_by_semantic_type_at_least_1_opt_NIL:
  \<open> parse_element_index_input_by_semantic_type_at_least_1_opt TY [] [] [] [] [] \<close>
  unfolding parse_element_index_input_by_semantic_type_at_least_1_opt_def
            parse_element_index_input_by_semantic_type_at_least_1_def
            parse_element_index_input_by_semantic_type_def
  by (cases TY; simp)

subsection \<open>Variable Operations\<close>

declare [[\<phi>trace_reasoning = 2]]

proc op_get_var:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<r>[var] T\<close>
  requires [\<phi>reason, unfolded \<phi>SemType_def, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and [\<phi>reason 10000]: \<open>parse_element_index_input_by_semantic_type_at_least_1 TY input_index sidx idx pidx reject\<close>
    and [\<phi>reason 10000]: \<open>\<phi>Aggregate_Getter idx T U f\<close>
    and [\<phi>reason 10000]: \<open>report_unprocessed_element_index reject\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<r>[var] T\<heavy_comma> f x \<Ztypecolon> \<v>\<a>\<l> U\<close>
\<medium_left_bracket>
  to Itself
  unfold Inited_Var_identity_eq
  FIC.Var.getter_rule
  semantic_assert \<open>nosep.dest (\<phi>arg.dest \<v>0) \<Turnstile> Some ` Well_Type TY\<close>
  semantic_return \<open>the (nosep.dest (\<phi>arg.dest \<v>0)) \<Turnstile> (x \<Ztypecolon> T)\<close>
  fold Inited_Var_identity_eq
  apply_rule op_get_aggregate[where input_index=input_index and sidx=sidx and unwinded=idx
                                and pidx=pidx and reject=reject]
\<medium_right_bracket> .

lemma op_get_var0:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_var var TY [] \<lbrace> x \<Ztypecolon> \<v>\<a>\<r>[var] T \<longmapsto> \<lambda>ret. x \<Ztypecolon> \<v>\<a>\<r>[var] T\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[ret] T \<rbrace> \<close>
  by (rule op_get_var_\<phi>app[where input_index=\<open>[]\<close> and idx=\<open>[]\<close> and pidx=\<open>[]\<close> and reject=\<open>[]\<close> and f=id, simplified];
      simp add: parse_element_index_input_by_semantic_type_at_least_1_def
                parse_element_index_input_by_semantic_type_def
                \<phi>Aggregate_Getter_Nil report_unprocessed_element_index_I)


proc op_set_var:
  input  \<open>x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U'\<close>
  requires [useful]: \<open>varname.type var \<equiv> TY_var\<close>
    and           \<open>\<phi>SemType_opt (x \<Ztypecolon> T) TY\<close>
    and [useful]: \<open>pred_option (\<lambda>TY_var. pred_option ((=) TY_var) TY) TY_var\<close>
    and [useful]: \<open>parse_element_index_input_by_semantic_type_at_least_1_opt TY input_index sidx idx pidx reject\<close>
    and AMO:      \<open>\<phi>Aggregate_Mapper_Opt idx T T' U U' f\<close>
    and           \<open>\<phi>SemType (y \<Ztypecolon> U') UY\<close>
    and [useful]: \<open>pred_option (\<lambda>TY. is_valid_index_of sidx TY UY) TY_var\<close>
    and           \<open>report_unprocessed_element_index reject\<close>
  output \<open>f (\<lambda>_. y) x \<Ztypecolon> \<v>\<a>\<r>[var] T'\<close>
\<medium_left_bracket>
  $y semantic_local_value UY
  \<open>var\<close> to Itself
  unfold Raw_Var_identity_eq
  FIC.Var.getter_rule

  semantic_assert \<open>
        pred_option (\<lambda>TY_var. pred_option ((=) TY_var) TY \<and> index_type sidx TY_var = UY) (varname.type var) \<and>
        pred_option (\<lambda>TY'. valid_index TY' sidx) TY\<close>
    certified by (insert \<phi>; cases TY; cases TY_var;
        simp add: parse_element_index_input_by_semantic_type_at_least_1_opt_def
                  parse_element_index_input_by_semantic_type_at_least_1_def
                  parse_element_index_input_by_semantic_type_def
                  is_valid_index_of_def) ;;

  apply_rule FIC.Var.setter_rule[
    where u=\<open>Some (nosep (Some (index_mode_value_opt sidx (\<lambda>_. \<phi>arg.dest \<a>\<r>\<g>1)
                                (nosep.dest (\<phi>arg.dest \<v>1)))))\<close>]
  fold Inited_Var_identity_eq

  \<medium_right_bracket> certified
    by (insert \<phi> AMO; cases TY;
        clarsimp simp add: \<phi>Aggregate_Mapper_Opt_def \<phi>Type_Mapping_def
        parse_element_index_input_by_semantic_type_at_least_1_opt_def
        parse_element_index_input_by_semantic_type_at_least_1_def
        parse_element_index_input_by_semantic_type_def) .


lemma op_set_var_0:
  \<open> varname.type var \<equiv> TY_var
\<Longrightarrow> \<phi>SemType_opt (x \<Ztypecolon> U) TY
\<Longrightarrow> pred_option (\<lambda>TY_var. pred_option ((=) TY_var) TY) TY_var
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U') UY
\<Longrightarrow> pred_option ((=) UY) TY_var
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_var UY var TY [] v \<lbrace> x \<Ztypecolon> Var var U\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v] U' \<longmapsto> \<lambda>\<r>\<e>\<t>. y \<Ztypecolon> \<v>\<a>\<r>[var] U' \<rbrace> \<close>
  by (rule op_set_var_\<phi>app[where f=id and input_index=\<open>[]\<close> and sidx=\<open>[]\<close> and idx=\<open>[]\<close>
                             and pidx=\<open>[]\<close> and reject=\<open>[]\<close> and T=U and T'=U' and U=U and U'=U',
                            simplified];
      simp add: parse_element_index_input_by_semantic_type_at_least_1_opt_NIL
                \<phi>Aggregate_Mapper_Opt_Nil report_unprocessed_element_index_I
                is_valid_index_of_Nil;
      cases TY_var; simp)


proc op_free_var:
  requires \<open>\<p>\<a>\<r>\<a>\<m> var\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> var' = var\<close>
  input  \<open>x \<Ztypecolon> Var var' T\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  to Itself
  unfold Raw_Var_identity_eq
  apply_rule FIC.Var.setter_rule[where u=\<open>None\<close> and k=\<open>var\<close>]
\<medium_right_bracket> .


proc op_var_scope:
  requires \<open>\<p>\<a>\<r>\<a>\<m> TY\<close>
       and BLK: \<open>\<And>var. varname.type var \<equiv> TY
                  \<Longrightarrow> \<p>\<r>\<o>\<c> F var \<lbrace> X\<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var] \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>
                      \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any) \<close>
  input  \<open>X\<close>
  output \<open>Y\<close>
  throws  E
  \<medium_left_bracket>
    apply_rule FIC.Var.allocate_rule[where P=\<open>(\<lambda>v. varname.type v = TY)\<close> and u=\<open>Some (nosep None)\<close>]
    \<exists>v \<open>() \<Ztypecolon> MAKE (Var v \<circle>)\<close>
    try'' \<medium_left_bracket>
        apply_rule BLK[of \<open>\<phi>arg.dest \<v>0\<close>, unfolded atomize_eq, OF Premise_D[where mode=default], simplified]
        op_free_var \<open>\<phi>arg.dest \<v>0\<close>
    \<medium_right_bracket> \<medium_left_bracket>
        op_free_var \<open>\<phi>arg.dest \<v>0\<close>
        throw \<open>v\<close>
    \<medium_right_bracket>
\<medium_right_bracket> .


subsection \<open>Rules of Variable Operations\<close>

subsubsection \<open>Get\<close> 

proc [\<phi>reason 1200]:
  input \<open>X\<close>
  requires Find: \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<r>[var] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y \<w>\<i>\<t>\<h> Any\<close>
      and  \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
      and [\<phi>reason 10000]: \<open>parse_element_index_input_by_semantic_type_at_least_1 TY input_index sidx idx pidx reject\<close>
      and [\<phi>reason 10000]: \<open>\<phi>Aggregate_Getter idx T U f\<close>
      and [\<phi>reason 10000]: \<open>report_unprocessed_element_index reject\<close>
  output \<open>\<v>\<a>\<l> f x <val-of> var <path> input_index \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<r>[var] T\<close>
  @action synthesis
\<medium_left_bracket>
  Find
  apply_rule op_get_var[where input_index=input_index and sidx=sidx and idx=idx
                          and pidx=pidx and reject=reject]
\<medium_right_bracket>.

proc [\<phi>reason 1210]:
  input \<open>X\<close>
  requires Find: \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<r>[var] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y \<w>\<i>\<t>\<h> Any\<close>
      and  \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  output \<open>\<v>\<a>\<l> x <val-of> var <path> [] \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<r>[var] T\<close>
  @action synthesis
\<medium_left_bracket>
  Find
  op_get_var0
\<medium_right_bracket> .


subsubsection \<open>Set\<close>

proc (nodef) [\<phi>reason 1200]:
  input X
  requires G : \<open>\<p>\<r>\<o>\<c> g \<lbrace> X \<longmapsto> \<v>\<a>\<l> y \<Ztypecolon> U' \<r>\<e>\<m>\<a>\<i>\<n>\<s> X1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
       and S : \<open>X1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<heavy_comma> x \<Ztypecolon> Var var T \<w>\<i>\<t>\<h> Any @action NToA\<close>
       and T1: \<open>varname.type var \<equiv> TY_var\<close>
       and T2: \<open>\<phi>SemType_opt (x \<Ztypecolon> T) TY\<close>
       and T3: \<open>pred_option (\<lambda>TY_var. pred_option ((=) TY_var) TY) TY_var\<close>
       and T4: \<open>parse_element_index_input_by_semantic_type_at_least_1_opt TY input_index sidx idx pidx reject\<close>
       and     \<open>chk_element_index_all_solved reject\<close>
       and T5: \<open>\<phi>Aggregate_Mapper_Opt idx T T' U U' f\<close>
       and T6: \<open>\<phi>SemType (y \<Ztypecolon> U') UY\<close>
       and T7: \<open>pred_option (\<lambda>TY. is_valid_index_of sidx TY UY) TY_var\<close>
  output \<open>\<v>\<a>\<l> (y <set-to> var <path> input_index) \<Ztypecolon> U' \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y\<heavy_comma> f (\<lambda>_. y) x \<Ztypecolon> \<v>\<a>\<r>[var] T'\<close>
  throws E
  @action synthesis
\<medium_left_bracket>
  G  
  S \<rightarrow> val v
  $v apply_rule op_set_var[OF T1 T2 T3 T4 T5 T6 T7 report_unprocessed_element_index_I]
  $v
\<medium_right_bracket> .

proc (nodef) [\<phi>reason 1210]:
  input X
  requires G : \<open>\<p>\<r>\<o>\<c> g \<lbrace> X \<longmapsto> \<v>\<a>\<l> y \<Ztypecolon> T' \<r>\<e>\<m>\<a>\<i>\<n>\<s> X1 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
       and S : \<open>X1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y\<heavy_comma> x \<Ztypecolon> Var var T \<w>\<i>\<t>\<h> Any @action NToA\<close>
       and T1: \<open>varname.type var \<equiv> TY_var\<close>
       and T2: \<open>\<phi>SemType_opt (x \<Ztypecolon> T) TY\<close>
       and T3: \<open>pred_option (\<lambda>TY_var. pred_option ((=) TY_var) TY) TY_var\<close>
       and T6: \<open>\<phi>SemType (y \<Ztypecolon> T') UY\<close>
       and T7: \<open>pred_option ((=) UY) TY_var\<close>
  output \<open>\<v>\<a>\<l> (y <set-to> var <path> []) \<Ztypecolon> T' \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] T'\<close>
  throws E
  @action synthesis
\<medium_left_bracket>
  G
  S \<rightarrow> val v
  $v apply_rule op_set_var_0[OF T1 T2 T3 T6 T7]
  $v
\<medium_right_bracket> .



subsection \<open>Implementing IDE-CP Generic Variable Access\<close>

\<phi>reasoner_group local_var = (1000, [1000,1000]) for (\<open>varname.type var \<equiv> TY\<close>)
  \<open>storing semantic types of local variables\<close>

proc (nodef) "__set_var_rule_":
  input  \<open>x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw] U'\<heavy_comma> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>
  requires G : \<open>\<p>\<r>\<o>\<c> g \<lbrace> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<heavy_comma> f (\<lambda>_. y) x \<Ztypecolon> \<v>\<a>\<r>[var] T' \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
       and T1: \<open>varname.type var \<equiv> TY_var\<close>
       and T2: \<open>\<phi>SemType_opt (x \<Ztypecolon> T) TY\<close>
       and T3: \<open>pred_option (\<lambda>TY_var. pred_option ((=) TY_var) TY) TY_var\<close>
       and T4: \<open>parse_element_index_input_by_semantic_type_at_least_1_opt TY input_index sidx idx pidx reject\<close>
       and T5: \<open>\<phi>Aggregate_Mapper_Opt idx T T' U U' f\<close>
       and T6: \<open>\<phi>SemType (y \<Ztypecolon> U') UY\<close>
       and T7: \<open>pred_option (\<lambda>TY. is_valid_index_of sidx TY UY) TY_var\<close>
       and T8: \<open>report_unprocessed_element_index reject\<close>
  output \<open>Z\<close>
  throws E
\<medium_left_bracket>
  apply_rule op_set_var_\<phi>app[OF T1 T2 T3 T4 T5 T6 T7 T8]
  G
\<medium_right_bracket> .

proc (nodef) "__set_var_rule_0_":
  input  \<open>x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw] U'\<heavy_comma> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>
  requires G : \<open>\<p>\<r>\<o>\<c> g \<lbrace> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U' \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
       and T1: \<open>varname.type var \<equiv> TY_var\<close>
       and T2: \<open>\<phi>SemType_opt (x \<Ztypecolon> T) TY\<close>
       and T3: \<open>pred_option (\<lambda>TY_var. pred_option ((=) TY_var) TY) TY_var\<close>
       and T4: \<open>\<phi>SemType (y \<Ztypecolon> U') UY\<close>
       and T5: \<open>pred_option ((=) UY) TY_var\<close>
  output \<open>Z\<close>
  throws E
\<medium_left_bracket>
  apply_rule op_set_var_0[OF T1 T2 T3 T4 T5]
  G
\<medium_right_bracket> .


lemma "__new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> TY
              \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var] \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>
                  \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any))
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope TYPE('a) TY g \<lbrace> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G
    op_var_scope \<open>TY\<close> \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>] G \<medium_right_bracket>
  \<medium_right_bracket> .

proc (nodef) "__set_new_var_rule_":
  input  \<open>y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>
  requires G: \<open>\<And>var. varname.type var \<equiv> Some TY
            \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>
                \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any)\<close>
      and \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  output \<open>Z\<close>
  throws E
\<medium_left_bracket>
  op_var_scope \<open>Some TY\<close> \<medium_left_bracket>
    premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
    op_set_var_0
    G
  \<medium_right_bracket>
\<medium_right_bracket> .

proc (nodef) "__set_new_var_noty_rule_":
  input  \<open>y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>
  requires G: \<open>\<And>var. varname.type var \<equiv> None
        \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>
            \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any)\<close>
       and \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  output \<open>Z\<close>
  throws E
\<medium_left_bracket>
  op_var_scope None \<medium_left_bracket>
    premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
    op_set_var_0
    G
  \<medium_right_bracket>
\<medium_right_bracket> .


ML_file "library/variable.ML"


setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put NONE)\<close>

end


