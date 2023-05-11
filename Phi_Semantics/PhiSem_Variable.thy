chapter \<open>Typed Variable\<close>

text \<open>This is a generic formalization variables supporting either typed variables or non-typed.
If the formalization is untyped, variables in the formalization can be assigned by values of
any type.
You can set the flag \<phi>variable_is_typed to indicate whether the formalization of variables is typed.\<close>

theory PhiSem_Variable
  imports Phi_System.Resource_Template
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
  Var :: \<open>RES.Var.basic_fiction o\<^sub>\<I> \<F>_pointwise \<F>_it\<close> (pointwise_fiction_for_partial_mapping_resource RES.Var) ..

hide_fact FIC.\<phi>var_fic_ax FIC.\<phi>var_fic_axioms



section \<open>\<phi>-Types\<close>

subsection \<open>Variable\<close>

abbreviation Var :: \<open>varname \<Rightarrow> (VAL option,'a) \<phi> \<Rightarrow> (fiction,'a) \<phi>\<close>
  where \<open>Var vname T \<equiv> (FIC.Var.\<phi> (vname \<^bold>\<rightarrow> \<black_circle> (Nosep T)))\<close>

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

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (?var::varname) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse var (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (Var ?var) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (Var var) (\<lambda>_. x \<Ztypecolon> Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (Inited_Var ?var) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (Inited_Var var) (\<lambda>_. x \<Ztypecolon> Inited_Var var T :: assn)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 2000 for
  \<open>Synthesis_Parse (Uninited_Var ?var) (?Y::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (Uninited_Var var) (\<lambda>_. Uninited_Var var :: assn)\<close>
  unfolding Synthesis_Parse_def ..



subsubsection \<open>Properties\<close>

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
  \<open>(raw \<Ztypecolon> Var v Identity) = (1(v \<mapsto> nosep raw) \<Ztypecolon> FIC.Var.\<phi> Identity)\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma UnInited_Var_identity_eq:
  \<open>(\<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[v]) = (nosep None \<Ztypecolon> FIC.Var.\<phi> (v \<^bold>\<rightarrow> \<black_circle> Identity))\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

lemma Inited_Var_identity_eq:
  \<open>(raw \<Ztypecolon> \<v>\<a>\<r>[v] Identity) = (1(v \<mapsto> nosep (Some raw)) \<Ztypecolon> FIC.Var.\<phi> Identity)\<close>
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
  \<open>pred_option ((=) TY) None @action infer_var_type\<close>
  \<comment> \<open>the output TY can be anything freely\<close>
  by simp

lemma [\<phi>reason 1000 for \<open>pred_option ((=) ?TY') (Some ?TY) @action infer_var_type\<close>]:
  \<open>pred_option ((=) TY) (Some TY) @action infer_var_type\<close>
  \<comment> \<open>the output TY equals to that TY in \<open>Some TY\<close> exactly.\<close>
  by simp


subsection \<open>Variable Operations\<close>

proc op_get_var:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<r>[var] T\<close>
  requires [unfolded \<phi>SemType_def, useful]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<r>[var] T\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  to Identity
  unfold Inited_Var_identity_eq
  FIC.Var.getter_rule
  semantic_assert \<open>nosep.dest (\<phi>arg.dest \<v>0) \<in> Some ` Well_Type TY\<close>
  semantic_return \<open>the (nosep.dest (\<phi>arg.dest \<v>0)) \<in> (x \<Ztypecolon> T)\<close>
  fold Inited_Var_identity_eq
\<medium_right_bracket> .

proc op_set_var:
  input  \<open>x \<Ztypecolon> Var var T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U\<close>
  requires [unfolded Action_Tag_def, useful]:
      \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type\<close>
  requires \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  output \<open>y \<Ztypecolon> \<v>\<a>\<r>[var] U\<close>
\<medium_left_bracket>
  $y semantic_local_value TY
  \<open>var\<close> to Identity
  unfold Raw_Var_identity_eq
  FIC.Var.setter_rule[where u=\<open>Some (nosep (Some (\<phi>arg.dest \<a>\<r>\<g>1)))\<close>]
  fold Inited_Var_identity_eq
\<medium_right_bracket> .

proc op_free_var:
  input  \<open>x \<Ztypecolon> Var var T\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  to Identity
  unfold Raw_Var_identity_eq
  FIC.Var.setter_rule[where u=\<open>None\<close>]
\<medium_right_bracket> .


proc op_var_scope:
  requires BLK: \<open>\<And>var. varname.type var \<equiv> TY
                  \<Longrightarrow> \<p>\<r>\<o>\<c> F var \<lbrace> X\<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var] \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any \<rbrace>
                      \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>v. E v \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any) \<close>
  input  \<open>X\<close>
  output \<open>Y\<close>
  throws  E
  \<medium_left_bracket>
    FIC.Var.allocate_rule[where P=\<open>(\<lambda>v. varname.type v = TY)\<close> and u=\<open>Some (nosep None)\<close>]
    \<exists>v as \<open>\<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[v]\<close>
    note \<phi>Procedure_protect_body[cong] \<open>\<v>0 = \<phi>arg v\<close>[simp] ;;
    try'' \<medium_left_bracket>
        BLK[of \<open>\<phi>arg.dest \<v>0\<close>, unfolded atomize_eq, OF Premise_D[where mode=default], simplified]
        op_free_var[of \<open>\<phi>arg.dest \<v>0\<close>, simplified]
    \<medium_right_bracket> \<medium_left_bracket>
        op_free_var[of \<open>\<phi>arg.dest \<v>0\<close>, simplified]
        throw
    \<medium_right_bracket>
\<medium_right_bracket> .


subsection \<open>Rules of Variable Operations\<close>
  
subsubsection \<open>Get\<close> 

proc [\<phi>reason 1200]:
  input \<open>X\<close>
  requires Find: \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<v>\<a>\<r>[var] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y \<a>\<n>\<d> Any\<close>
      and  \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  output \<open>\<v>\<a>\<l> x <val-of> var \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> Y\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<r>[var] T\<close>
  @action synthesis
\<medium_left_bracket>
  Find
  op_get_var
\<medium_right_bracket>.


subsubsection \<open>Set\<close>

proc (nodef) op_set_var__synthesis
  [\<phi>reason 1200 for
      \<open>\<p>\<r>\<o>\<c> ?f \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R'\<heavy_comma> \<blangle> (?y <set-to> ?var) \<Ztypecolon> ?U ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E  @action synthesis\<close>]:
  input X
  requires G: \<open>\<p>\<r>\<o>\<c> g \<lbrace> X \<longmapsto> X1\<heavy_comma> \<blangle> \<v>\<a>\<l> y \<Ztypecolon> U \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
       and P: \<open>pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type\<close>
       and S: \<open>X1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y\<heavy_comma> x \<Ztypecolon> Var var T \<a>\<n>\<d> Any @action ToSA\<close>
       and    \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  output \<open>Y\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U \<heavy_comma> \<blangle> \<v>\<a>\<l> (y <set-to> var) \<Ztypecolon> U \<brangle>\<close>
  throws E
  @action synthesis
\<medium_left_bracket>
  G S op_set_var P op_get_var
\<medium_right_bracket> .


subsection \<open>Implementing IDE-CP Generic Variable Access\<close>

lemma "__set_var_rule__":
  \<open> \<p>\<r>\<o>\<c> g \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U\<heavy_comma> \<blangle> X \<brangle> \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E
\<Longrightarrow> pred_option (\<lambda>TY'. TY = TY') (varname.type var) @action infer_var_type
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_set_var TY var raw \<ggreater> g) \<lbrace> R\<heavy_comma> \<blangle> x \<Ztypecolon> Var var T \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X \<brangle> \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G and P and [\<phi>reason]
    op_set_var P G
  \<medium_right_bracket>.

lemma "__new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> TY
              \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> R\<heavy_comma> \<u>\<n>\<i>\<n>\<i>\<t>\<e>\<d> \<v>\<a>\<r>[var]\<heavy_comma> \<blangle> X \<brangle> \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any))
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope TYPE('a) TY g \<lbrace> R\<heavy_comma> \<blangle> X \<brangle> \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G
    op_var_scope[where TY=\<open>TY\<close>] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>] G \<medium_right_bracket>
  \<medium_right_bracket> .

lemma "__set_new_var_rule__":
  \<open> (\<And>var. varname.type var \<equiv> Some TY
              \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U\<heavy_comma> \<blangle> X \<brangle> \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any ))
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope TYPE('a) (Some TY) (\<lambda>var. op_set_var TY var raw \<ggreater> g var)
     \<lbrace> R\<heavy_comma> \<blangle> y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X \<brangle> \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G and [\<phi>reason]
    op_var_scope[where TY=\<open>Some TY\<close>] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      op_set_var G
    \<medium_right_bracket>
  \<medium_right_bracket>.

lemma "__set_new_var_noty_rule__":
  \<open> (\<And>var. varname.type var \<equiv> None
              \<Longrightarrow> \<p>\<r>\<o>\<c> g var \<lbrace> R\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<r>[var] U\<heavy_comma> \<blangle> X \<brangle> \<longmapsto> \<lambda>ret. Z ret \<heavy_comma> () \<Ztypecolon> Var var \<phi>Any
                             \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. E e\<heavy_comma> () \<Ztypecolon> Var var \<phi>Any))
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_var_scope TYPE('a) None (\<lambda>var. op_set_var TY var raw \<ggreater> g var)
     \<lbrace> R\<heavy_comma> \<blangle> y \<Ztypecolon> \<v>\<a>\<l>[raw] U\<heavy_comma> X \<brangle> \<longmapsto> Z \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  \<medium_left_bracket> premises G and [\<phi>reason]
    op_var_scope[where TY=None] \<medium_left_bracket> premises [\<phi>reason for \<open>varname.type var \<equiv> _\<close>]
      op_set_var G
    \<medium_right_bracket>
  \<medium_right_bracket>.

ML_file "library/variable.ML"


setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put NONE)\<close>

end


