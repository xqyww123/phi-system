theory IDE_CP_App2
  imports Phi_Types
begin

section \<open>Value \& Reasoning of it\<close>

subsection \<open>Reasoning Rules\<close>

paragraph \<open>Implication\<close>

lemma Val_transformation [
    \<phi>reason add for \<open>_ \<Ztypecolon> Val _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                    \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Val _ _ \<w>\<i>\<t>\<h> _\<close>
]:
  \<open> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> y \<Ztypecolon> Val v U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Val v T \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def by (simp add: \<phi>expns)

paragraph \<open>Action\<close>

lemma [\<phi>reason 1200]:
  \<open> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> y \<Ztypecolon> Val v U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Val v T \<w>\<i>\<t>\<h> P @action \<A>_structural A\<close>
  unfolding Action_Tag_def using Val_transformation .

lemma [\<phi>reason 1200]:
  \<open> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. r x \<w>\<i>\<t>\<h> P @action to A
\<Longrightarrow> y \<Ztypecolon> Val v U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Val v T \<s>\<u>\<b>\<j> x. r x \<w>\<i>\<t>\<h> P @action to A\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<s>\<u>\<b>\<j> x. r x \<w>\<i>\<t>\<h> P @action as A
\<Longrightarrow> y \<Ztypecolon> Val v U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Val v T \<s>\<u>\<b>\<j> x. r x \<w>\<i>\<t>\<h> P @action as A\<close>
  unfolding Action_Tag_def Transformation_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> D \<w>\<i>\<t>\<h> P @action \<A>_destruct\<phi> T'
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[mode_embed_into_\<phi>type] (y \<Ztypecolon> U) : D
\<Longrightarrow> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<v>\<a>\<l>[v] U \<w>\<i>\<t>\<h> P @action \<A>_destruct\<phi> T'\<close>
  unfolding Action_Tag_def Rewrite_into_\<phi>Type_def
  by (rule Val_transformation, simp)

paragraph \<open>Simplification\<close>

lemma [\<phi>programming_simps]:
    \<open>Val raw (ExTyp T) = (\<exists>\<phi> c. Val raw (T c))\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)

lemma [\<phi>programming_simps]:
    \<open>Val raw (T \<phi>\<s>\<u>\<b>\<j> P) = (Val raw T \<phi>\<s>\<u>\<b>\<j> P)\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)

lemma \<phi>Val_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Val v T) = (x' \<Ztypecolon> Val v T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup Val_simp_cong ("x \<Ztypecolon> Val v T") = \<open>
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>Val_simp_cong} ctxt)
\<close>

subsection \<open>Algebraic Properties\<close>

interpretation Val: Functional_Transformation_Functor \<open>Val v\<close> \<open>Val v'\<close>
      \<open>\<lambda>x. {x}\<close> \<open>\<lambda>x. x\<close> \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> v = v'\<close> \<open>\<lambda>x. x\<close> \<open>\<lambda>x. x\<close>
  by (standard; clarsimp simp add: Transformation_Functor_def Transformation_def ExSet_expn Premise_def
      Subjection_expn Val_expn)

lemma Val_inhabitance_functor[\<phi>reason add]:
  \<open>Inhabitance_Functor (Val v) id\<close>
  unfolding Inhabitance_Functor_def Inhabited_def
  by (cases v; clarsimp simp add: Val_expn Subjection_expn; blast)


subsection \<open>Application Methods for Transformations\<close>

(*TODO: I really don't like this. It is not generic.
It should be some generic structural morphism.*)

lemma [\<phi>reason 2100 for \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P)\<close>
  unfolding \<phi>Application_def
  using \<phi>apply_implication Val_transformation implies_left_frame by metis


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?x' \<Ztypecolon> ?T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (x' \<Ztypecolon> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P)\<close>
  unfolding \<phi>Application_def
  by (meson Val_transformation \<phi>apply_implication implies_left_frame)


subsection \<open>Synthesis\<close>

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse (?x \<Ztypecolon> (?T::?'a \<Rightarrow> VAL set)) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (x \<Ztypecolon> T) (\<lambda>v. x \<Ztypecolon> Val v T)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason 1200 for
  \<open>Synthesis_Parse (?raw::?'a \<phi>arg) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse raw (\<lambda>_. x \<Ztypecolon> Val raw T)\<close>
  unfolding Synthesis_Parse_def ..

(*
lemma [\<phi>reason 1200 for \<open>?S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S2\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> Val ?raw ?T\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<v>\<a>\<l>[raw] T\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn transformation_refl) *)

lemma [\<phi>reason 1200 for \<open>?S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S2\<heavy_comma> \<blangle> ?x <val-of> (?raw::VAL \<phi>arg) <path> ?path \<Ztypecolon> ?T \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R\<heavy_comma> \<blangle> x <val-of> raw <path> path \<Ztypecolon> \<v>\<a>\<l>[raw] T \<brangle>\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn)

lemma [\<phi>reason 1200 for
    \<open>\<p>\<r>\<o>\<c> ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?x <val-of> (?raw::VAL \<phi>arg) <path> ?path \<Ztypecolon> ?T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E @action synthesis\<close>
]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> \<p>\<r>\<o>\<c> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x <val-of> raw <path> path \<Ztypecolon> \<v>\<a>\<l>[ret] T \<brangle> \<rbrace> @action synthesis\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: \<phi>M_Success)

lemma \<phi>arg_val_varify_type:
  \<open> \<phi>arg.dest raw \<in> (x  \<Ztypecolon> T)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> Any
||| FAIL TEXT(\<open>Expect the value\<close> raw \<open>has spec\<close> (x' \<Ztypecolon> T') \<open>but is specified by\<close>
      (x \<Ztypecolon> T) \<open>actually, and the conversion fails.\<close>)
\<Longrightarrow> \<phi>arg.dest raw \<in> (x' \<Ztypecolon> T')\<close>
  unfolding Transformation_def atomize_Branch by blast

lemma [\<phi>reason 1200 for
    \<open>?S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S2\<heavy_comma> \<blangle> ?x <set-to> (?raw::VAL \<phi>arg) <path> _ \<Ztypecolon> ?T \<brangle> \<w>\<i>\<t>\<h> _ \<close>
]:
  \<open> ERROR TEXT(\<open>Local value is immutable. Cannot assign to\<close> raw)
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R\<heavy_comma> \<blangle> x <set-to> (raw::VAL \<phi>arg) <path> any \<Ztypecolon> T \<brangle>\<close>
  by simp

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason 1500 for \<open>PROP Synthesis_by (?raw::VAL \<phi>arg) (Trueprop (\<p>\<r>\<o>\<c> ?f \<lbrace> ?R1 \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> ?x \<Ztypecolon> Val ret ?T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E ))\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> PROP Synthesis_by raw (Trueprop (\<p>\<r>\<o>\<c> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> x \<Ztypecolon> Val ret T \<rbrace>))\<close>
  unfolding Synthesis_by_def Action_Tag_def \<phi>Procedure_def Return_def det_lift_def
  by (cases raw; simp add: Val_expn)


subsection \<open>Assignment\<close>

typedecl valname \<comment> \<open>The name of local value in user programming interface\<close>

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason 1200 for \<open>?S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S2\<heavy_comma> \<blangle> ?x <val-of> (?name::valname) <path> ?path \<Ztypecolon> ?T \<brangle> \<w>\<i>\<t>\<h> _ \<close>]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname) <path> []) \<in> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R\<heavy_comma> \<blangle> x <val-of> name <path> path \<Ztypecolon> \<v>\<a>\<l>[raw] T \<brangle>\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn)

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason 1200 for
    \<open>\<p>\<r>\<o>\<c> ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> \<blangle> ?x <val-of> (?name::valname) <path> ?path \<Ztypecolon> ?T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E @action synthesis\<close>
]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname) <path> []) \<in> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> \<p>\<r>\<o>\<c> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x <val-of> name <path> path \<Ztypecolon> \<v>\<a>\<l>[ret] T \<brangle> \<rbrace> @action synthesis\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: \<phi>M_Success)




lemma "__set_value_rule__":
  \<open> (\<phi>arg.dest (v <val-of> (name::valname) <path> []) \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> R\<heavy_comma> \<blangle> X \<brangle> \<longmapsto> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E )
\<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> R\<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T\<heavy_comma> X \<brangle> \<longmapsto> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_def Value_of_def
  by (clarsimp simp add: \<phi>expns)

lemma "__fast_assign_val__":
  \<open> R\<heavy_comma> \<blangle> X \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> R\<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T\<heavy_comma> X \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> \<phi>arg.dest (v <val-of> (name::valname) <path> []) \<in> (x \<Ztypecolon> T) \<and> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: Val_expn Subjection_expn)

lemma "__fast_assign_val_0__":
  \<open> R\<heavy_comma> \<blangle> Void \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<close>
  by simp

ML_file \<open>library/additions/local_value.ML\<close>


(*subsection \<open>Deep Representation of Values\<close>

abbreviation Vals :: \<open>(VAL, 'a) \<phi> \<Rightarrow> (VAL list, 'a) \<phi>\<close> ("\<v>\<a>\<l>\<^bold>s _" [51] 50)
  where \<open>Vals \<equiv> List_Item\<close>

translations "(CONST Vals T) \<^emph> (CONST Vals U)" == "XCONST Vals (T \<^emph> U)"*)


subsection \<open>Prove Properties of Value Abstractions by Programming\<close>

subsubsection \<open>Semantic Type\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (Trueprop (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Well_Type TY)) M D R F
\<Longrightarrow> Friendly_Help TEXT(\<open>Hi! You are trying to show the value abstraction\<close> S \<open>has semantic type\<close> TY
      \<open>Now you entered the programming mode and you need to transform the specification to\<close>
      \<open>some representation of \<phi>-types whose semantic type is know so that we can verify your claim.\<close>)
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (\<phi>SemType S TY)) M D R F\<close>
  unfolding \<phi>Programming_Method_def  ToA_Construction_def \<phi>SemType_def Transformation_def
  by (simp add: subset_iff)

lemma [\<phi>reason 1000]:
  \<open> \<phi>SemType S TY
\<Longrightarrow> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Well_Type TY\<close>
  unfolding Transformation_def \<phi>SemType_def subset_iff by blast

subsubsection \<open>Zero Value\<close>

consts working_mode_\<phi>Zero :: working_mode

lemma \<phi>deduce_zero_value:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<p>\<a>\<r>\<a>\<m> (y \<Ztypecolon> U)
\<Longrightarrow> \<phi>Zero TY U y
\<Longrightarrow> y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> Any
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> \<phi>Zero TY T x\<close>
  unfolding ToA_Construction_def \<phi>Zero_def image_iff Inhabited_def Transformation_def
  by (clarsimp; blast)

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (Trueprop (\<phi>Zero TY T x)) working_mode_\<phi>Zero
                             (Trueprop (\<phi>Zero TY T x))
                             (Trueprop True)
                             (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def .


subsubsection \<open>Equality\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method
          (\<And>x y vx vy. \<p>\<r>\<e>\<m>\<i>\<s>\<e> ceq x y
              \<Longrightarrow> x \<Ztypecolon> \<v>\<a>\<l>[vx] T \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[vy] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> \<v>\<a>\<l>[vx] U \<heavy_comma> y' \<Ztypecolon> \<v>\<a>\<l>[vy] U
                  \<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g> \<phi>Equal U ceq' eq'
                  \<s>\<u>\<b>\<j> U x' y'. ceq' x' y' \<and> eq x y = eq' x' y')
          M D R F
\<Longrightarrow> Friendly_Help
    TEXT(\<open>Hi! Transform the specification to some representation of \<phi>-types whose\<close> \<phi>Equal
         \<open>property is known so that we can generate proof obligations for your claim.\<close>)
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (\<phi>Equal T ceq eq)) M D R F\<close>
  (is \<open>PROP \<phi>Programming_Method (PROP ?IMP) _ _ _ _ \<Longrightarrow> PROP _\<close>
   is \<open>PROP ?PPP \<Longrightarrow> PROP _\<close>)
  unfolding \<phi>Programming_Method_def conjunction_imp
proof -
  have rule: \<open>PROP ?IMP \<Longrightarrow> \<phi>Equal T ceq eq\<close>
  unfolding \<phi>Equal_def Premise_def Transformation_def Embedded_Reasoning_def
  by (clarsimp simp add: \<phi>expns \<phi>arg_All, blast)

  assume D: \<open>PROP D\<close>
    and  R: \<open>PROP R\<close>
    and  F: \<open>PROP F\<close>
    and PP: \<open>PROP D \<Longrightarrow> PROP R \<Longrightarrow> PROP F \<Longrightarrow> PROP ?IMP\<close>
  show \<open>\<phi>Equal T ceq eq\<close>
    using PP[OF D R F, THEN rule] .
qed

subsubsection \<open>Finale\<close>

ML_file \<open>library/additions/value_properties.ML\<close>

hide_fact \<phi>deduce_zero_value


(*
TODO: fix this feature
subsubsection \<open>Auto unfolding for value list\<close>

lemma [\<phi>programming_simps]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv Empty_List) = (1 \<s>\<u>\<b>\<j> USELESS (rawv = \<phi>V_nil))\<close>
  unfolding set_eq_iff USELESS_def
  by (cases rawv; simp add: \<phi>expns)

lemma [\<phi>programming_simps]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv (List_Item T))
 = (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T \<s>\<u>\<b>\<j> USELESS (\<exists>v. rawv = \<phi>V_cons v \<phi>V_nil))\<close>
  unfolding set_eq_iff \<phi>V_cons_def USELESS_def
  apply (cases rawv; clarsimp simp add: \<phi>expns \<phi>V_tl_def \<phi>V_hd_def times_list_def; rule;
          clarsimp simp add: \<phi>arg_All \<phi>arg_exists)
  by blast+

lemma [simp]:
  \<open> [] \<notin> (\<exists>*x. x \<Ztypecolon> L)
\<Longrightarrow> ((\<exists>*x. x \<Ztypecolon> Val rawv (List_Item T \<^emph> L)) :: 'a::sep_algebra set)
  = ((\<exists>*x. x \<Ztypecolon> Val (\<phi>V_tl rawv) L) * (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T))\<close>
  unfolding set_eq_iff
  apply (cases rawv; clarsimp simp add: \<phi>expns \<phi>V_tl_def \<phi>V_hd_def times_list_def)
  by (metis (no_types, opaque_lifting) append_Cons append_Nil list.exhaust_sel
            list.sel(1) list.sel(2) list.sel(3))

lemma [simp]:
  \<open>[] \<notin> (\<exists>*x. x \<Ztypecolon> (List_Item T \<^emph> L))\<close>
  by (rule; clarsimp simp add: \<phi>expns times_list_def)

lemma [simp]:
  \<open>[] \<notin> (\<exists>*x. x \<Ztypecolon> List_Item T)\<close>
  by (rule; clarsimp simp add: \<phi>expns times_list_def)
*)




end
