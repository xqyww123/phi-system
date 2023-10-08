theory IDE_CP_App2
  imports Phi_Types
begin

section \<open>Value \& Reasoning over it\<close>

subsection \<open>\<phi>-Type Abstraction\<close>

setup \<open>Context.theory_map (
  Phi_Type_Algebra.add_type {no_auto=true}
        (Phi_Type_Algebra.DIRECT_DEF (\<^pattern>\<open>Val\<close>, Thm.transfer \<^theory> @{thm' Val_def}),
         \<^here>, Phi_Type_Algebra.Derivings.empty, [])
   #> snd )\<close>

declare [[\<phi>trace_reasoning = 0]]

let_\<phi>type Val
  deriving \<open>Abstract_Domain T P
        \<Longrightarrow> Abstract_Domain (\<v>\<a>\<l>[v] T) P\<close>
       and \<open>Abstract_Domain\<^sub>L (\<v>\<a>\<l>[v] T) (\<lambda>x. \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T))\<close>
       and \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (\<v>\<a>\<l>[v] T) eq\<close>
       and Basic
       and \<open>Identity_Elements\<^sub>I (\<v>\<a>\<l> T) (\<lambda>x. True) (\<lambda>x. True)\<close>
       and Identity_Elements
       and Functional_Transformation_Functor


subsubsection \<open>Application Methods for Transformations\<close>

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
  unfolding \<phi>Application_def Premise_def
  by (simp, smt (z3) Premise_norm(1) Val.functional_transformation \<phi>apply_implication \<r>Guard_I transformation_left_frame)


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?x' \<Ztypecolon> ?T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?U \<w>\<i>\<t>\<h> ?P))
          (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> Any @action NToA
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (x' \<Ztypecolon> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P))
      (Trueprop (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (\<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True \<Longrightarrow> (\<c>\<u>\<r>\<r>\<e>\<n>\<t> blk [RR] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P)\<close>
  unfolding \<phi>Application_def Action_Tag_def Premise_def
  by (simp, smt (z3) Premise_I Val.functional_transformation \<phi>apply_implication \<r>Guard_def mk_elim_transformation transformation_left_frame)


subsubsection \<open>Synthesis\<close>

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (?x \<Ztypecolon> (?T::?'a \<Rightarrow> VAL set)) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (x \<Ztypecolon> T) (\<lambda>v. x \<Ztypecolon> Val v T)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (?raw::?'a \<phi>arg) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse raw (\<lambda>_. x \<Ztypecolon> Val raw T)\<close>
  unfolding Synthesis_Parse_def ..


subsection \<open>Access of Local Values\<close>

typedecl valname \<comment> \<open>Binding of local values used in user programming interface, only used syntactically\<close>

subsubsection \<open>Conventions\<close>

\<phi>reasoner_group ToA_access_to_local_value = (1000, [1000,1100]) in ToA_cut
    \<open>Access local values via ToA\<close>
  and synthesis_access_to_local_value = (1000, [1000, 1100]) in \<phi>synthesis_cut
    \<open>Access local values via Synthesis\<close>

  and local_value = (1000, [1000, 1000])
                    for \<open>\<phi>arg.dest (v <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T)\<close>
    \<open>specification facts of local values\<close>


subsubsection \<open>Read\<close>

(*
lemma [\<phi>reason 1200 for \<open>?S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S2\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> Val ?raw ?T\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<v>\<a>\<l>[raw] T\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn transformation_refl) *)

lemma [\<phi>reason %ToA_access_to_local_value for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x <val-of> (?raw::VAL \<phi>arg) <path> ?path \<Ztypecolon> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> \<phi>arg.dest raw \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x <val-of> raw <path> path \<Ztypecolon> \<v>\<a>\<l>[raw] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val.unfold)

lemma [\<phi>reason %ToA_access_to_local_value for
    \<open>\<p>\<r>\<o>\<c> ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?x <val-of> (?raw::VAL \<phi>arg) <path> ?path \<Ztypecolon> ?T ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E @action synthesis\<close>
]:
  \<open> \<phi>arg.dest raw \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> \<p>\<r>\<o>\<c> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. x <val-of> raw <path> path \<Ztypecolon> \<v>\<a>\<l>[ret] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<rbrace> @action synthesis\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: \<phi>M_Success)

lemma \<phi>arg_val_varify_type:
  \<open> \<phi>arg.dest raw \<Turnstile> (x  \<Ztypecolon> T)
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T' \<w>\<i>\<t>\<h> Any
||| FAIL TEXT(\<open>Expect the value\<close> raw \<open>has spec\<close> (x' \<Ztypecolon> T') \<open>but is specified by\<close>
      (x \<Ztypecolon> T) \<open>actually, and the conversion fails.\<close>)
\<Longrightarrow> \<phi>arg.dest raw \<Turnstile> (x' \<Ztypecolon> T')\<close>
  unfolding Transformation_def atomize_Branch FAIL_def
  by blast

lemma [\<phi>reason %ToA_access_to_local_value for
    \<open>?S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x <set-to> (?raw::VAL \<phi>arg) <path> _ \<Ztypecolon> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?S2 \<w>\<i>\<t>\<h> _ \<close>
]:
  \<open> ERROR TEXT(\<open>Local value is immutable. Cannot assign to\<close> raw)
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x <set-to> (raw::VAL \<phi>arg) <path> any \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>
  unfolding ERROR_def
  by blast

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason %\<phi>ant_by_synthesis for \<open>PROP Synthesis_by (?raw::VAL \<phi>arg) (Trueprop (\<p>\<r>\<o>\<c> ?f \<lbrace> ?R1 \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> ?x \<Ztypecolon> Val ret ?T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E ))\<close>]:
  \<open> \<phi>arg.dest raw \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> PROP Synthesis_by raw (Trueprop (\<p>\<r>\<o>\<c> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> x \<Ztypecolon> Val ret T \<rbrace>))\<close>
  unfolding Synthesis_by_def Action_Tag_def \<phi>Procedure_def Return_def det_lift_def
  by (cases raw; simp add: Val.unfold)


subsubsection \<open>Assignment\<close>

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason %ToA_access_to_local_value for \<open>?S1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x <val-of> (?name::valname) <path> ?path \<Ztypecolon> ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?S2 \<w>\<i>\<t>\<h> _ \<close>]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x <val-of> name <path> path \<Ztypecolon> \<v>\<a>\<l>[raw] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val.unfold)

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason %synthesis_access_to_local_value for
    \<open>\<p>\<r>\<o>\<c> ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?x <val-of> (?name::valname) <path> ?path \<Ztypecolon> ?T ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E @action synthesis\<close>
]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path
\<Longrightarrow> \<p>\<r>\<o>\<c> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. x <val-of> name <path> path \<Ztypecolon> \<v>\<a>\<l>[ret] T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<rbrace> @action synthesis\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: \<phi>M_Success)




lemma "__set_value_rule__":
  \<open> (\<phi>arg.dest (v <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<longmapsto> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E )
\<Longrightarrow> \<p>\<r>\<o>\<c> F \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[v] T\<heavy_comma> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<longmapsto> R' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E \<close>
  unfolding \<phi>Procedure_def Value_of_def
  by (clarsimp simp add: Val.unfold INTERP_SPEC_subj Subjection_expn_set)

lemma "__fast_assign_val__":
  \<open> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<v>\<a>\<l>[v] T\<heavy_comma> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<w>\<i>\<t>\<h> \<phi>arg.dest (v <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T) \<and> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: Val.unfold; blast)

lemma "__fast_assign_val_0__":
  \<open> Void \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<close>
  by simp

ML_file \<open>library/additions/local_value.ML\<close>


(*subsection \<open>Deep Representation of Values\<close>

abbreviation Vals :: \<open>(VAL, 'a) \<phi> \<Rightarrow> (VAL list, 'a) \<phi>\<close> ("\<v>\<a>\<l>\<^bold>s _" [51] 50)
  where \<open>Vals \<equiv> List_Item\<close>

translations "(CONST Vals T) \<^emph> (CONST Vals U)" == "XCONST Vals (T \<^emph> U)"*)


subsection \<open>Prove Properties of Value Abstractions by Programming\<close>

subsubsection \<open>Semantic Type\<close>

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (Trueprop (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S')) M D R F
\<Longrightarrow> Friendly_Help TEXT(\<open>Hi! You are trying to show the value abstraction\<close> S \<open>has semantic type\<close> TY
      \<open>Now you entered the programming mode and you need to transform the specification to\<close>
      \<open>some representation of \<phi>-types whose semantic type is know so that we can verify your claim.\<close>)
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (\<phi>SemType S TY)) M D (\<phi>SemType S' TY &&& PROP R) F\<close>
  unfolding \<phi>Programming_Method_def  ToA_Construction_def \<phi>SemType_def Transformation_def
  by (simp add: subset_iff conjunction_imp)


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
  by clarsimp

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (Trueprop (\<phi>Zero TY T x)) working_mode_\<phi>Zero
                             (Trueprop (\<phi>Zero TY T x))
                             (Trueprop True)
                             (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def .


subsubsection \<open>Equality\<close>

lemma [\<phi>reason %\<phi>programming_method]:
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
  unfolding \<phi>Equal_def Premise_def Transformation_def Subj_Reasoning_def
  by (clarsimp simp add: \<phi>arg_All, blast)

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
