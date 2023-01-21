chapter \<open>IDE-CP Functions \& Applications - Part I\<close>

text \<open>In this part, we build simple applications based on IDE-CP directly, without too much
  advanced reasoning processes.\<close>

theory IDE_CP_Applications1
  imports Phi_Types
  keywords "val" :: quasi_command
  abbrevs "<vals>" = "\<^bold>v\<^bold>a\<^bold>l\<^bold>s"
begin

section \<open>Basic Applications\<close>

lemma assert_\<phi>app:
  \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m Y \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y \<^bold>a\<^bold>n\<^bold>d Any @action ToSA \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<close>
  unfolding Action_Tag_def
  using implies_weaken by blast

lemma transform_by_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P \<Longrightarrow> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s X' \<^bold>a\<^bold>n\<^bold>d P"
  unfolding Argument_def .

lemma is_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> x' \<Ztypecolon> N" using view_shift_id by force
lemma as_\<phi>app: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m X' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> X' \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w x \<Ztypecolon> N \<longmapsto> X'"  by blast 

lemma view_shift_whole_\<phi>app:
  "\<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Argument_def .

lemma cases_\<phi>app:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> Y
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> Y
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B + A \<longmapsto> Y\<close>
  unfolding Argument_def
  using \<phi>CASE_VS by fastforce

lemma cases'_\<phi>app:
  \<open> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t B \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y
\<Longrightarrow> B + A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s Y\<close>
  unfolding Argument_def
  using \<phi>CASE_IMP by fastforce

subsection \<open>Construct \& Destruct \<open>\<phi>\<close>-Type\<close>

lemma destruct_\<phi>app:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y D : T x
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s D\<close>
  unfolding Simplify_def \<phi>Type_def by (simp add: implies_refl)

section \<open>Value \& Its Settings\<close>

subsection \<open>Reasoning Rules\<close>

paragraph \<open>Implication\<close>

lemma Val_cast [\<phi>reason]:
  \<open> y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> y \<Ztypecolon> Val v U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> Val v T \<^bold>a\<^bold>n\<^bold>d P\<close>
  unfolding Imply_def by (simp add: \<phi>expns)

paragraph \<open>Action\<close>

lemma [\<phi>reason 1200 for \<open>?y \<Ztypecolon> Val ?v ?U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?T \<^bold>a\<^bold>n\<^bold>d ?P @action (?Act::?'a::structural action)\<close>]:
  \<open> y \<Ztypecolon> U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> T \<^bold>a\<^bold>n\<^bold>d P @action Act
\<Longrightarrow> y \<Ztypecolon> Val v U \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x \<Ztypecolon> Val v T \<^bold>a\<^bold>n\<^bold>d P @action Act\<close>
  for Act :: \<open>'a::structural action\<close>
  unfolding Action_Tag_def
  using Val_cast .

paragraph \<open>Simplification\<close>

lemma [\<phi>programming_simps]:
    \<open>Val raw (ExTyp T) = (\<exists>\<phi> c. Val raw (T c))\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)

lemma [\<phi>programming_simps]:
    \<open>Val raw (T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (Val raw T \<phi>\<^bold>s\<^bold>u\<^bold>b\<^bold>j P)\<close>
  by (rule \<phi>Type_eqI) (simp add: \<phi>expns)

lemma \<phi>Val_simp_cong[folded atomize_eq]:
  \<open> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Val v T) = (x' \<Ztypecolon> Val v T')\<close>
  unfolding set_eq_iff by (simp add: \<phi>expns)

simproc_setup Val_simp_cong ("x \<Ztypecolon> Val v T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>Val_simp_cong} ctxt)
\<close>

subsection \<open>Application Methods for Transformations\<close>

(*TODO: I really don't like this. It is not generic.
It should be some generic structural morphism.*)

lemma [\<phi>reason 2100 for \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> PROP \<phi>Application_Success
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using \<phi>apply_implication Val_cast implies_left_prod by metis


lemma [\<phi>reason 2000 for \<open>
  PROP \<phi>Application_Method (Trueprop (?x' \<Ztypecolon> ?T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R\<heavy_comma> ?x \<Ztypecolon> Val ?raw ?T)) ?Result
\<close> except \<open>
  PROP \<phi>Application_Method (Trueprop (?x \<Ztypecolon> Val ?raw ?T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s ?y \<Ztypecolon> ?U \<^bold>a\<^bold>n\<^bold>d ?P))
          (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?R)) ?Result
\<close>]:
  \<open> SUBGOAL TOP_GOAL G
\<Longrightarrow> x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x' \<Ztypecolon> T' \<^bold>a\<^bold>n\<^bold>d Any
\<Longrightarrow> SOLVE_SUBGOAL G
\<Longrightarrow> PROP \<phi>Application_Success
\<Longrightarrow> \<^bold>o\<^bold>b\<^bold>l\<^bold>i\<^bold>g\<^bold>a\<^bold>t\<^bold>i\<^bold>o\<^bold>n True
\<Longrightarrow> PROP \<phi>Application_Method (Trueprop (x' \<Ztypecolon> T' \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y \<Ztypecolon> U \<^bold>a\<^bold>n\<^bold>d P))
      (Trueprop (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> x \<Ztypecolon> Val raw T))
      (Trueprop ((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [RR] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<heavy_comma> y \<Ztypecolon> Val raw U) \<and> P))\<close>
  unfolding \<phi>Application_Method_def \<phi>Application_def
  using \<phi>apply_implication Val_cast implies_left_prod by metis


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

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S1 \<longmapsto> ?S2\<heavy_comma> SYNTHESIS ?x \<Ztypecolon> Val ?raw ?T @action synthesis ?G\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R\<heavy_comma> SYNTHESIS x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] T  @action synthesis G\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn view_shift_id)

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S1 \<longmapsto> ?S2\<heavy_comma> SYNTHESIS ?x <val-of> (?raw::VAL \<phi>arg) \<Ztypecolon> ?T  @action synthesis ?G\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R\<heavy_comma> SYNTHESIS x <val-of> raw \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] T  @action synthesis G\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn view_shift_id)

lemma [\<phi>reason 1300 for
    \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> SYNTHESIS ?x <val-of> (?raw::VAL \<phi>arg) \<Ztypecolon> ?T \<rbrace>  @action synthesis ?G\<close>
]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> SYNTHESIS x <val-of> raw \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] T \<rbrace>  @action synthesis G\<close>
  apply (rule Synthesis_Proc_fallback_VS)
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn view_shift_id)

lemma [\<phi>reason 1200 for
    \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret::VAL \<phi>arg. ?R' \<heavy_comma> SYNTHESIS ?x <val-of> (?raw::VAL \<phi>arg) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E   @action synthesis ?G\<close>
]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return raw \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> SYNTHESIS x <val-of> raw \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[ret] T \<rbrace>  @action synthesis G\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: \<phi>M_Success)


lemma [\<phi>reason 1200 for
    \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S1 \<longmapsto> ?S2\<heavy_comma> SYNTHESIS ?x <set-to> (?raw::VAL \<phi>arg) \<Ztypecolon> ?T  @action synthesis ?G\<close>
]:
  \<open> ERROR TEXT(\<open>Local value is immutable. Cannot assign to\<close> raw)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R\<heavy_comma> SYNTHESIS x <set-to> (raw::VAL \<phi>arg) \<Ztypecolon> T  @action synthesis G\<close>
  by simp

lemma [\<phi>reason 1500 for \<open>PROP Synthesis_by (?raw::VAL \<phi>arg) (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<lbrace> ?R1 \<longmapsto> \<lambda>ret. ?R2\<heavy_comma> ?x \<Ztypecolon> Val ret ?T \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E )) @action synthesis ?G\<close>]:
  \<open> \<phi>arg.dest raw \<in> (x \<Ztypecolon> T)
\<Longrightarrow> PROP Synthesis_by raw (Trueprop (\<^bold>p\<^bold>r\<^bold>o\<^bold>c Return raw \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> x \<Ztypecolon> Val ret T \<rbrace>)) @action synthesis G\<close>
  unfolding Synthesis_by_def Action_Tag_def \<phi>Procedure_def Return_def det_lift_def
  by (cases raw; simp add: Val_expn)


subsection \<open>Assignment\<close>

typedecl valname

lemma "__set_value_rule__":
  \<open> (\<phi>arg.dest (v <val-of> (name::valname)) \<in> (x \<Ztypecolon> T) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R\<heavy_comma> X \<longmapsto> R' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E )
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F \<lbrace> R\<heavy_comma> (x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T\<heavy_comma> X) \<longmapsto> R' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<close>
  unfolding \<phi>Procedure_def Value_of_def
  by (clarsimp simp add: \<phi>expns)

lemma [\<phi>reason 1200 for \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w ?S1 \<longmapsto> ?S2\<heavy_comma> SYNTHESIS ?x <val-of> (?name::valname) \<Ztypecolon> ?T  @action synthesis ?G\<close>]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R \<longmapsto> R\<heavy_comma> SYNTHESIS x <val-of> name \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] T  @action synthesis G\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn view_shift_id)

lemma [\<phi>reason 1300 for
    \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret. ?R' \<heavy_comma> SYNTHESIS ?x <val-of> (?name::valname) \<Ztypecolon> ?T \<rbrace>  @action synthesis ?G\<close>
]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return \<phi>V_none \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> SYNTHESIS x <val-of> name \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[raw] T \<rbrace>  @action synthesis G\<close>
  apply (rule Synthesis_Proc_fallback_VS)
  unfolding Action_Tag_def
  by (cases raw; simp add: Val_expn view_shift_id)

lemma [\<phi>reason 1200 for
    \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?GG \<lbrace> ?R \<longmapsto> \<lambda>ret::VAL \<phi>arg. ?R' \<heavy_comma> SYNTHESIS ?x <val-of> (?name::valname) \<Ztypecolon> ?T ret \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s ?E   @action synthesis ?G\<close>
]:
  \<open> \<phi>arg.dest (raw <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Return raw \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> SYNTHESIS x <val-of> name \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[ret] T \<rbrace>  @action synthesis G\<close>
  unfolding Action_Tag_def
  by (cases raw; simp add: \<phi>M_Success)


lemma "__fast_assign_val__":
  \<open> R\<heavy_comma> X \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> R\<heavy_comma> (x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[v] T\<heavy_comma> X) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R' \<^bold>a\<^bold>n\<^bold>d \<phi>arg.dest (v <val-of> (name::valname)) \<in> (x \<Ztypecolon> T) \<and> P\<close>
  unfolding Imply_def
  by (clarsimp simp add: Val_expn Subjection_expn)

lemma "__fast_assign_val_0__":
  \<open> R\<heavy_comma> Void \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s R \<close>
  by (simp add: implies_refl)

thm "__fast_assign_val__"[OF "__fast_assign_val__", OF "__fast_assign_val__", OF "__fast_assign_val_0__"]

ML_file \<open>library/additions/local_value.ML\<close>


subsection \<open>Deep Representation of Values\<close>

abbreviation Vals :: \<open>(VAL, 'a) \<phi> \<Rightarrow> (VAL list, 'a) \<phi>\<close> ("\<^bold>v\<^bold>a\<^bold>l\<^bold>s _" [51] 50)
  where \<open>Vals \<equiv> List_Item\<close>

translations "(CONST Vals T) \<^emph> (CONST Vals U)" == "XCONST Vals (T \<^emph> U)"

(*
TODO: fix this feature
subsubsection \<open>Auto unfolding for value list\<close>

lemma [\<phi>programming_simps]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv Empty_List) = (1 \<^bold>s\<^bold>u\<^bold>b\<^bold>j USELESS (rawv = \<phi>V_nil))\<close>
  unfolding set_eq_iff USELESS_def
  by (cases rawv; simp add: \<phi>expns)

lemma [\<phi>programming_simps]:
  \<open>(\<exists>*x. x \<Ztypecolon> Val rawv (List_Item T))
 = (\<exists>*x. x \<Ztypecolon> Val (\<phi>V_hd rawv) T \<^bold>s\<^bold>u\<^bold>b\<^bold>j USELESS (\<exists>v. rawv = \<phi>V_cons v \<phi>V_nil))\<close>
  unfolding set_eq_iff \<phi>V_cons_def USELESS_def
  apply (cases rawv; clarsimp simp add: \<phi>expns \<phi>V_tl_def \<phi>V_hd_def times_list_def; rule;
          clarsimp simp add: sem_value_All sem_value_exists)
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