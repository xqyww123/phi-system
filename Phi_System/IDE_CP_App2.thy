(*IDE_CP_P: Programming Module*)
theory IDE_CP_App2
  imports Phi_Types
begin

section \<open>Derivers for IDE-CP\<close>

subsection \<open>Properties of Semantic Value\<close>


subsubsection \<open>Semantic Type\<close>

context begin

private lemma \<phi>TA_SemTy_rule:
  \<open> \<r>EIF Ant Ant'
\<Longrightarrow> (\<condition> Ant' \<Longrightarrow> Abstract_Domain T D)
\<Longrightarrow> (\<condition> Ant' \<Longrightarrow> Abstract_Domain\<^sub>L T D\<^sub>L)
\<Longrightarrow> \<premise> (Ant' \<longrightarrow> TY = (if Ex D then TY' else \<p>\<o>\<i>\<s>\<o>\<n>) \<and> D\<^sub>L = D)
\<Longrightarrow> (\<And>x. Ant \<longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY' @tag \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> Ant @tag \<phi>TA_ANT
\<Longrightarrow> \<typeof> T = TY \<close>
  unfolding Action_Tag_def Premise_def Abstract_Domain_def \<r>EIF_def Abstract_Domain\<^sub>L_def \<r>ESC_def
            SType_Of_def Inhabited_def Semantic_Type'_def Semantic_Type_def
  by (auto,
      smt (z3) Action_Tag_def Premise_True Satisfiable_def \<phi>SemType_Itself_brute exE_some,
      meson)

(*
private lemma \<phi>TA_SemTy_rule:
  \<open> (\<And>x. Ant \<longrightarrow> \<typeof> (x \<Ztypecolon> T) = TY @tag \<phi>TA_subgoal \<A>infer)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> Ant @tag \<phi>TA_ANT
\<Longrightarrow> \<typeof> T = TY \<close>
  unfolding Action_Tag_def Premise_def
  by (rule SType_Of'_implies_SType_Of, clarsimp)
*)

private lemma \<phi>TA_SemTy_IH_rewr:
  \<open> Trueprop (Ant \<longrightarrow> PPP @tag \<phi>TA_subgoal undefined) \<equiv>
    (Ant @tag \<phi>TA_ANT \<Longrightarrow> PPP ) \<close>
  unfolding Action_Tag_def atomize_imp Premise_def
  ..

private lemma \<phi>TA_SemTy_cong:
  \<open> TY \<equiv> TY'
\<Longrightarrow> \<typeof> T = TY \<equiv> \<typeof> T = TY' \<close>
  for T :: \<open>(VAL,'x) \<phi>\<close>
  by simp


ML_file \<open>library/phi_type_algebra/semantic_type.ML\<close>

end

\<phi>property_deriver Semantic_Type 120 for (\<open>SType_Of _ = _\<close>)
    = \<open> Phi_Type_Derivers.semantic_type \<close> 

ML_file \<open>library/additions/infer_semantic_type_prem.ML\<close>


(*
subsubsection \<open>Semantic Type Rewrites\<close>

context begin

private lemma styp_of_derv_rule':
  \<open> Abstract_Domain\<^sub>L T D\<^sub>L
\<Longrightarrow> Abstract_Domain T D
\<Longrightarrow> Semantic_Type T TY
\<Longrightarrow> \<premise> ((\<exists>x. D\<^sub>L x) = (\<exists>x. D x) \<and>
            ((\<exists>x. D x) \<longrightarrow> TY' = TY) \<and>
            ((\<forall>x. \<not> D x) \<longrightarrow> TY' = \<p>\<o>\<i>\<s>\<o>\<n>))
\<Longrightarrow> SType_Of T = TY' \<close>
  unfolding Abstract_Domain\<^sub>L_def Abstract_Domain_def \<r>ESC_def \<r>EIF_def
            Premise_def SType_Of_def Inhabited_def 
  by (auto, metis Satisfiable_def Semantic_Type_def Well_Type_unique some_equality,
            simp add: Satisfiable_def Semantic_Type_def)

private lemma styp_of_derv_rule:
  \<open> (Ant @tag \<phi>TA_ANT \<Longrightarrow> SType_Of T = TY')
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> Ant @tag \<phi>TA_ANT
\<Longrightarrow> SType_Of T = TY' \<close> .

ML_file \<open>library/phi_type_algebra/SType_Of.ML\<close>

end

\<phi>property_deriver SType_Of 150 for (\<open>SType_Of _ = _\<close>)
    = \<open> Phi_Type_Derivers.STyp_Of \<close> 
*)


subsubsection \<open>Semantic Zero Value\<close>

context begin

private lemma \<phi>TA_Semantic_Zero_Val_rule:
  \<open> (Ant \<Longrightarrow> \<premise> (TY \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<longrightarrow> Zero TY \<noteq> None \<and> (\<forall>v. Zero TY = Some v \<longrightarrow> v \<Turnstile> (z \<Ztypecolon> T))))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<obligation> True
\<Longrightarrow> Ant @tag \<phi>TA_ANT
\<Longrightarrow> Semantic_Zero_Val TY T z \<close>
  unfolding Semantic_Zero_Val_def Premise_def Action_Tag_def
  by clarsimp

ML_file \<open>library/phi_type_algebra/semantic_zero_val.ML\<close>

end

\<phi>property_deriver Semantic_Zero_Val 130 for (\<open>Semantic_Zero_Val _ _ _\<close>)
  requires Semantic_Type
    = \<open> Phi_Type_Derivers.semantic_zero_val \<close> 


declare [[\<phi>parameter_default_equality \<open>TY\<close> \<Rightarrow> obligation (100)]]


subsection \<open>\<open>\<phi>App_Conv\<close>\<close> \<comment> \<open>used only when the given ToA is not in the target space\<close>

lemma [\<phi>reason_template default %\<phi>app_conv_derived+10]:
  \<open> Functional_Transformation_Functor Fa Fb T U (\<lambda>x. {D x}) R pm fm
\<Longrightarrow> NO_LAMBDA_CONVERTIBLE TYPE('c\<^sub>a \<times> 'x\<^sub>a) TYPE('c \<times> 'x) @tag \<A>_template_reason None
\<Longrightarrow> \<guard> \<condition> D x = a \<and> b \<in> R x
\<Longrightarrow> NO_SIMP (ToA_App_Conv TYPE('c\<^sub>a\<^sub>a) TYPE('c\<^sub>a) T ToA (a \<Ztypecolon> T \<transforms> b \<Ztypecolon> U \<with> P))
\<Longrightarrow> ToA_App_Conv TYPE('c\<^sub>a\<^sub>a) TYPE('c) (Fa T) ToA (x \<Ztypecolon> Fa T \<transforms> fm (\<lambda>_. b) (\<lambda>_. P) x \<Ztypecolon> Fb U \<with> pm (\<lambda>_. b) (\<lambda>_. P) x) \<close>
  for Fa :: \<open>('c\<^sub>a,'x\<^sub>a) \<phi> \<Rightarrow> ('c,'x) \<phi>\<close>
  unfolding ToA_App_Conv_def \<r>Guard_def Premise_def Functional_Transformation_Functor_def NO_SIMP_def
  by clarsimp

(* TODO: planned
lemma [\<phi>reason_template default %\<phi>app_conv_derived]:
  \<open> Functional_Transformation_Functor Fa Fb T U D R pm fm
\<Longrightarrow> NO_MATCH (\<lambda>x. {D'' x}) D @tag \<A>_template_reason
\<Longrightarrow> \<simplify> D' : (\<forall>a \<in> D x. Q a) @tag \<A>_template_reason
\<Longrightarrow> NO_SIMP (\<phi>App_Conv ToA (\<forall>a. Q a \<longrightarrow> (a \<Ztypecolon> T \<transforms> f a \<Ztypecolon> U \<with> P a)))
\<Longrightarrow> \<condition> (\<forall>a \<in> D x. f a \<in> R x)
\<Longrightarrow> \<phi>App_Conv ToA (D' \<longrightarrow> (x \<Ztypecolon> Fa T \<transforms> fm f P x \<Ztypecolon> Fb U \<with> pm f P x)) \<close>
  unfolding Functional_Transformation_Functor_def \<phi>App_Conv_def \<r>Guard_def Premise_def
            Action_Tag_def Simplify_def NO_SIMP_def
  by clarsimp
*)


section \<open>Value \& Reasoning over it\<close>

subsection \<open>\<phi>-Type Abstraction\<close>

local_setup \<open>
  Phi_Type.add_type {no_auto=true}
        (\<^binding>\<open>Val\<close>, \<^pattern>\<open>Val::VAL \<phi>arg \<Rightarrow> (VAL, ?'a) \<phi> \<Rightarrow> (?'x::one, ?'a) \<phi>\<close>,
         Phi_Type.DIRECT_DEF (Thm.transfer \<^theory> @{thm' Val_def}),
         \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>

local_setup \<open>
  Phi_Type.add_type {no_auto=true}
        (\<^binding>\<open>Vals\<close>, \<^pattern>\<open>Vals::VAL list \<phi>arg \<Rightarrow> (VAL list, ?'a) \<phi> \<Rightarrow> (?'x::one, ?'a) \<phi>\<close>,
         Phi_Type.DIRECT_DEF (Thm.transfer \<^theory> @{thm' Vals_def}),
         \<^here>, Phi_Type.Derivings.empty, [], NONE)
   #> snd \<close>

let_\<phi>type Val
  deriving \<open>Abstract_Domain T P
        \<Longrightarrow> Abstract_Domain (\<val>[v] T) P\<close>
       and \<open>Abstract_Domain\<^sub>L (\<val>[v] T) (\<lambda>x. \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T))\<close>
       and \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (\<val>[v] T) eq\<close>
       and Basic
       and \<open>Identity_Elements\<^sub>I (\<val>[v] T) (\<lambda>x. True) (\<lambda>x. True)\<close>
       and \<open> ERROR TEXT(\<open>Insuffieicnt arguments or local values\<close>)
         \<Longrightarrow> Identity_Elements\<^sub>E (\<val>[v] T) (\<lambda>x. False)\<close>
       and Functional_Transformation_Functor


subsubsection \<open>Application Methods for Transformations\<close>

(*TODO: I really don't like this. It is not generic.
It should be some generic structural morphism.*)

lemma [\<phi>reason 2100 for \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> ?T \<transforms> ?y \<Ztypecolon> ?U \<with> ?P))
          (Trueprop (\<current> ?blk [?RR] \<results> \<in'> ?x \<Ztypecolon> Val ?raw ?T\<heavy_comma> ?R)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<transforms> ?y \<Ztypecolon> ?U \<with> ?P))
          (Trueprop (\<current> ?blk [?RR] \<results> \<in'> ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application (Trueprop (x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<with> P))
      (Trueprop (\<current> blk [RR] \<results> \<in'> x \<Ztypecolon> Val raw T\<heavy_comma> R))
      (\<obligation> True \<Longrightarrow> (\<current> blk [RR] \<results> \<in'> y \<Ztypecolon> Val raw U\<heavy_comma> R) \<and> P)\<close>
  unfolding \<phi>Application_def Premise_def
  by (simp, smt (verit, del_insts) CurrentConstruction_def INTERP_SPEC_subj Satisfaction_def
                                   Subjection_expn Subjection_times(1) Transformation_def Val.unfold)


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application (Trueprop (?x' \<Ztypecolon> ?T' \<transforms> ?y \<Ztypecolon> ?U \<with> ?P))
      (Trueprop (\<current> ?blk [?RR] \<results> \<in'> ?x \<Ztypecolon> Val ?raw ?T\<heavy_comma> ?R)) ?Result
\<close> except \<open>
  PROP \<phi>Application (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<transforms> ?y \<Ztypecolon> ?U \<with> ?P))
          (Trueprop (\<current> ?blk [?RR] \<results> \<in'> ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<transforms> x' \<Ztypecolon> T' \<with> Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> \<obligation> True
\<Longrightarrow> PROP \<phi>Application (Trueprop (x' \<Ztypecolon> T' \<transforms> y \<Ztypecolon> U \<with> P))
      (Trueprop (\<current> blk [RR] \<results> \<in'> x \<Ztypecolon> Val raw T\<heavy_comma> R))
      (\<obligation> True \<Longrightarrow> (\<current> blk [RR] \<results> \<in'> y \<Ztypecolon> Val raw U\<heavy_comma> R) \<and> P)\<close>
  unfolding \<phi>Application_def Action_Tag_def Premise_def
  by (simp, smt (z3) Action_Tag_E Action_Tag_I Premise_True
                     Val.functional_transformation \<phi>apply_implication \<r>Guard_I transformation_right_frame)


subsubsection \<open>Synthesis\<close>

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (?x \<Ztypecolon> (?T::?'a \<Rightarrow> VAL BI)) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (x \<Ztypecolon> T) (\<lambda>v. x \<Ztypecolon> Val v T)\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (MAKE _ (?T::?'a \<Rightarrow> VAL BI)) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse (MAKE n T) (\<lambda>v. x \<Ztypecolon> MAKE n (Val v T))\<close>
  unfolding Synthesis_Parse_def ..

lemma [\<phi>reason %\<phi>synthesis_parse for
  \<open>Synthesis_Parse (?raw::?'a \<phi>arg) (?X::?'ret \<Rightarrow> assn)\<close>
]:
  \<open>Synthesis_Parse raw (\<lambda>_. x \<Ztypecolon> Val raw T)\<close>
  unfolding Synthesis_Parse_def ..

subsubsection \<open>Special Parsing of Annotations\<close>

lemma [\<phi>reason %To_ToA_fallback]:
  \<open> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> U \<subj> y. r y @tag to U'
\<Longrightarrow> x \<Ztypecolon> \<val>[v] T \<transforms> y \<Ztypecolon> \<val>[v] U \<subj> y. r y @tag to U' \<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp


subsubsection \<open>Short-cut of ToA\<close>

text \<open>We can assume the name bindings of values are lambda-equivalent. \<close>

\<phi>reasoner_group Val_ToA = (1100, [1100, 1120]) in ToA_cut
  \<open>Short-cut transformations about values\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason %Val_ToA+20 for \<open>_ \<Ztypecolon> \<val>[_] _ \<transforms> _ \<Ztypecolon> \<val>[_] _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  "x \<Ztypecolon> \<val>[v] T \<transforms> x \<Ztypecolon> \<val>[v] T \<remains> Void @tag \<T>\<P>"
  unfolding REMAINS_def Transformation_def Action_Tag_def
  by simp

lemma [\<phi>reason %Val_ToA+10 for \<open>_ \<Ztypecolon> \<val>[_] _ \<transforms> _ \<Ztypecolon> \<val>[_] _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  " y \<Ztypecolon> U \<transforms> x \<Ztypecolon> T \<with> P @tag \<T>\<P>
\<Longrightarrow> y \<Ztypecolon> \<val>[v] U \<transforms> x \<Ztypecolon> \<val>[v] T \<remains> Void \<with> P @tag \<T>\<P>"
  unfolding Transformation_def Action_Tag_def
  by (simp add: times_list_def)



lemma [\<phi>reason %Val_ToA+20 for \<open>_ \<Ztypecolon> \<val>[_] _ \<heavy_comma> _ \<transforms> _ \<Ztypecolon> \<val>[_] _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  "x \<Ztypecolon> \<val>[v] T\<heavy_comma> R \<transforms> x \<Ztypecolon> \<val>[v] T \<remains> R @tag \<T>\<P>"
  unfolding REMAINS_def Transformation_def Action_Tag_def
  by simp

lemma [\<phi>reason %Val_ToA+10 for \<open>_ \<Ztypecolon> \<val>[_] _ \<heavy_comma> _ \<transforms> _ \<Ztypecolon> \<val>[_] _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  " y \<Ztypecolon> U \<transforms> x \<Ztypecolon> T \<with> P @tag \<T>\<P>
\<Longrightarrow> y \<Ztypecolon> \<val>[v] U\<heavy_comma> R \<transforms> x \<Ztypecolon> \<val>[v] T \<remains> R \<with> P @tag \<T>\<P>"
  unfolding Transformation_def Action_Tag_def
  by (simp add: times_list_def) metis

lemma [\<phi>reason %Val_ToA for \<open>_\<heavy_comma> _ \<transforms> _ \<Ztypecolon> \<val>[_] _ \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  " R \<transforms> x \<Ztypecolon> \<val>[v] T \<remains> R' \<with> P @tag \<T>\<P>
\<Longrightarrow> X\<heavy_comma> R \<transforms> x \<Ztypecolon> \<val>[v] T \<remains> X\<heavy_comma> R' \<with> P @tag \<T>\<P>"
  unfolding REMAINS_def split_paired_All Action_Tag_def
  by (simp add: mult.left_commute transformation_left_frame)

lemma [\<phi>reason %Val_ToA except \<open>_ \<transforms> ?x \<Ztypecolon> \<val>[?v] ?V \<remains> _ \<with> _ @tag \<T>\<P>\<close>
    if \<open>fn (_, sequent) =>
          case #2 (Phi_Syntax.dest_transformation (
                  Logic.strip_assums_concl (Phi_Help.leading_antecedent' sequent)))
            of Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ =>
                  not (Phi_Syntax.is_BI_connective X)
       \<close> ]:
  " R \<transforms> X \<remains> R' \<with> P @tag \<T>\<P>
\<Longrightarrow> x \<Ztypecolon> \<val>[v] V\<heavy_comma> R \<transforms> X \<remains> x \<Ztypecolon> \<val>[v] V\<heavy_comma> R' \<with> P @tag \<T>\<P>"
  unfolding REMAINS_def Action_Tag_def
  by (metis (no_types, opaque_lifting) transformation_right_frame mult.assoc mult.commute)




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
lemma [\<phi>reason 1200 for \<open>?S1 \<transforms> ?S2\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> Val ?raw ?T\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> R \<transforms> R\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<val>[raw] T\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn transformation_refl) *)

lemma [\<phi>reason %ToA_access_to_local_value
           for \<open>_ \<transforms> ?x <val-of> (?raw::VAL \<phi>arg) <path> ?path \<Ztypecolon> ?T \<remains> _ \<with> _ @tag \<T>\<P>\<close>]:
  \<open> \<phi>arg.dest raw \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path EIHOOK_none
\<Longrightarrow> R \<transforms> x <val-of> raw <path> path \<Ztypecolon> \<val>[raw] T \<remains> R @tag \<T>\<P>\<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def REMAINS_def
  by (cases raw; simp add: Val.unfold)

lemma [\<phi>reason %ToA_access_to_local_value for
    \<open>\<proc> ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?x <val-of> (?raw::VAL \<phi>arg) <path> ?path \<Ztypecolon> ?T ret \<remains> ?R' \<rbrace> \<throws> ?E @tag synthesis\<close>
]:
  \<open> \<phi>arg.dest raw \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path EIHOOK_none
\<Longrightarrow> \<proc> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. x <val-of> raw <path> path \<Ztypecolon> \<val>[ret] T \<remains> R \<rbrace> @tag synthesis\<close>
  unfolding Action_Tag_def REMAINS_def
  by (cases raw; simp add: \<phi>M_Success)

lemma \<phi>arg_val_varify_type:
  \<open> \<phi>arg.dest raw \<Turnstile> (x  \<Ztypecolon> T)
\<Longrightarrow> x \<Ztypecolon> T \<transforms> x' \<Ztypecolon> T' \<with> Any @tag \<T>\<P>
||| FAIL TEXT(\<open>Expect the value\<close> raw \<open>has spec\<close> (x' \<Ztypecolon> T') \<open>but is specified by\<close>
      (x \<Ztypecolon> T) \<open>actually, and the conversion fails.\<close>)
\<Longrightarrow> \<phi>arg.dest raw \<Turnstile> (x' \<Ztypecolon> T')\<close>
  unfolding Transformation_def atomize_Branch FAIL_def Action_Tag_def
  by blast

lemma [\<phi>reason %ToA_access_to_local_value for
    \<open>?S1 \<transforms> ?x <set-to> (?raw::VAL \<phi>arg) <path> _ \<Ztypecolon> ?T \<remains> ?S2 \<with> _ @tag \<T>\<P> \<close>
]:
  \<open> ERROR TEXT(\<open>Local value is immutable. Cannot assign to\<close> raw)
\<Longrightarrow> R \<transforms> x <set-to> (raw::VAL \<phi>arg) <path> any \<Ztypecolon> T \<remains> R @tag \<T>\<P>\<close>
  unfolding ERROR_def
  by blast

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason %\<phi>ant_by_synthesis for \<open>PROP Synthesis_by (?raw::VAL \<phi>arg) (Trueprop (\<proc> ?f \<lbrace> ?R1 \<longmapsto> \<lambda>ret. ?x \<Ztypecolon> Val ret ?T\<heavy_comma> ?R2 \<rbrace> \<throws> ?E ))\<close>]:
  \<open> \<phi>arg.dest raw \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> PROP Synthesis_by raw (Trueprop (\<proc> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. x \<Ztypecolon> Val ret T\<heavy_comma> R \<rbrace>))\<close>
  unfolding Synthesis_by_def Action_Tag_def \<phi>Procedure_def Return_def det_lift_def
  by (cases raw; simp add: Val.unfold less_eq_BI_iff)


subsubsection \<open>Assignment\<close>

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason %ToA_access_to_local_value for \<open>?S1 \<transforms> ?x <val-of> (?name::valname) <path> ?path \<Ztypecolon> ?T \<remains> ?S2 \<with> _ @tag \<T>\<P> \<close>]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path EIHOOK_none
\<Longrightarrow> R \<transforms> x <val-of> name <path> path \<Ztypecolon> \<val>[raw] T \<remains> R @tag \<T>\<P> \<close>
  for R :: \<open>'c::sep_magma_1 BI\<close>
  unfolding Action_Tag_def REMAINS_def
  by (cases raw; simp add: Val.unfold)

lemma [OF \<phi>arg_val_varify_type,
       \<phi>reason %synthesis_access_to_local_value for
    \<open>\<proc> ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?x <val-of> (?name::valname) <path> ?path \<Ztypecolon> ?T ret \<remains> ?R' \<rbrace> \<throws> ?E @tag synthesis\<close>
]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> report_unprocessed_element_index path EIHOOK_none
\<Longrightarrow> \<proc> Return raw \<lbrace> R \<longmapsto> \<lambda>ret. x <val-of> name <path> path \<Ztypecolon> \<val>[ret] T \<remains> R \<rbrace> @tag synthesis\<close>
  unfolding Action_Tag_def REMAINS_def
  by (cases raw; simp add: \<phi>M_Success)




lemma "__set_value_rule__":
  \<open> (\<phi>arg.dest (v <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T) \<Longrightarrow> \<proc> F \<lbrace> X \<remains> R \<longmapsto> R' \<rbrace> \<throws> E )
\<Longrightarrow> \<proc> F \<lbrace> x \<Ztypecolon> \<val>[v] T\<heavy_comma> X \<remains> R \<longmapsto> R' \<rbrace> \<throws> E \<close>
  unfolding \<phi>Procedure_def Value_of_def REMAINS_def
  by (clarsimp simp add: Val.unfold INTERP_SPEC_subj less_eq_BI_iff)

lemma "__fast_assign_val__":
  \<open> X \<remains> R \<transforms> R' \<with> P
\<Longrightarrow> x \<Ztypecolon> \<val>[v] T\<heavy_comma> X \<remains> R \<transforms> R' \<with> \<phi>arg.dest (v <val-of> (name::valname) <path> []) \<Turnstile> (x \<Ztypecolon> T) \<and> P\<close>
  unfolding Transformation_def
  by (clarsimp simp add: Val.unfold; blast)

lemma "__fast_assign_val_0__":
  \<open> Void \<remains> R \<transforms> R \<close>
  unfolding REMAINS_def
  by simp

ML_file \<open>library/additions/local_value.ML\<close>


(*subsection \<open>Deep Representation of Values\<close>

abbreviation Vals :: \<open>(VAL, 'a) \<phi> \<Rightarrow> (VAL list, 'a) \<phi>\<close> ("\<val>\<^bold>s _" [51] 50)
  where \<open>Vals \<equiv> List_Item\<close>

translations "(CONST Vals T) \<^emph> (CONST Vals U)" == "XCONST Vals (T \<^emph> U)"*)

subsection \<open>MAKE Abstraction for Values\<close>

lemma [\<phi>reason %\<phi>synthesis_cut for \<open>\<proc> _ \<lbrace> _ \<longmapsto> \<lambda>ret. ?y \<Ztypecolon> MAKE ?n (\<val>[ret] ?U) \<remains> ?R \<rbrace> \<throws> ?E @tag synthesis\<close>]:
  \<open> X \<transforms> x \<Ztypecolon> \<val>[v] T \<remains> R
\<Longrightarrow> x \<Ztypecolon> T \<transforms> y \<Ztypecolon> MAKE n U \<with> any
\<Longrightarrow> \<proc> Return v \<lbrace> X \<longmapsto> \<lambda>ret. y \<Ztypecolon> MAKE n (\<val>[ret] U) \<remains> R \<rbrace> @tag synthesis\<close>
  unfolding MAKE_def
  \<medium_left_bracket> premises X[] and T[]
    X T
  \<medium_right_bracket> .

subsection \<open>Programming Methods for Showing Properties of Values\<close>

subsubsection \<open>Semantic Type\<close>
(*
lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>x. x \<Ztypecolon> T \<transforms> A x) M D R F
\<Longrightarrow> Friendly_Help TEXT(\<open>Hi! You are trying to show the value abstraction\<close> S \<open>has semantic type\<close> TY
      \<open>Now you entered the programming mode and you need to transform the specification to\<close>
      \<open>some representation of \<phi>-types whose semantic type is know so that we can verify your claim.\<close>)
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (\<typeof> T = TY)) M D
                             ((\<And>x. \<typeof> (A x) = TY @tag \<A>infer) &&& PROP R) F\<close>
  unfolding \<phi>Programming_Method_def ToA_Construction_def Transformation_def Action_Tag_def
 
  apply (simp add: subset_iff conjunction_imp, rule SType_Of'_implies_SType_Of)
  subgoal premises prems for xx
    thm prems(1)[OF \<open>PROP D\<close> \<open>PROP R\<close> \<open>PROP F\<close>, of xx]
    apply (insert prems(3)[of xx] prems(1)[OF \<open>PROP D\<close> \<open>PROP R\<close> \<open>PROP F\<close>, of xx])
    by (insert prems(3) prems(1)[OF \<open>PROP D\<close> \<open>PROP R\<close> \<open>PROP F\<close>], blast) .
*)

subsubsection \<open>Zero Value\<close>

consts working_mode_Semantic_Zero_Val :: working_mode

lemma \<phi>deduce_zero_value:
  \<open> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> \<param> (y \<Ztypecolon> U)
\<Longrightarrow> Semantic_Zero_Val TY U y
\<Longrightarrow> y \<Ztypecolon> U \<transforms> x \<Ztypecolon> T \<with> Any
\<Longrightarrow> \<obligation> True
\<Longrightarrow> Semantic_Zero_Val TY T x\<close>
  unfolding ToA_Construction_def Semantic_Zero_Val_def image_iff Satisfiable_def Transformation_def
  by clarsimp

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (Trueprop (Semantic_Zero_Val TY T x)) working_mode_Semantic_Zero_Val
                             (Trueprop (Semantic_Zero_Val TY T x))
                             (Trueprop True)
                             (Trueprop True)\<close>
  unfolding \<phi>Programming_Method_def .


subsubsection \<open>Equality\<close>

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method
          (\<And>x y vx vy. \<premise> ceq x y
              \<Longrightarrow> x \<Ztypecolon> \<val>[vx] T \<heavy_comma> y \<Ztypecolon> \<val>[vy] T \<transforms> x' \<Ztypecolon> \<val>[vx] U \<heavy_comma> y' \<Ztypecolon> \<val>[vy] U
                  \<subj>-\<reasoning> \<phi>Equal U ceq' eq'
                  \<subj> U x' y'. ceq' x' y' \<and> eq x y = eq' x' y')
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
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv Empty_List) = (1 \<subj> USELESS (rawv = \<phi>V_nil))\<close>
  unfolding set_eq_iff USELESS_def
  by (cases rawv; simp add: \<phi>expns)

lemma [\<phi>programming_simps]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv (List_Item T))
 = (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T \<subj> USELESS (\<exists>v. rawv = \<phi>V_cons v \<phi>V_nil))\<close>
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
