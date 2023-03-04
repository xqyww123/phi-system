theory PhiSem_CF_Routine
  imports PhiSem_CF_Break PhiSem_CF_Basic
begin

typ \<open>'a::VALs\<close>

section \<open>Routine\<close>

text \<open>Procedure in \<open>\<phi>\<close>-system is a program segment, which does not correspond to a function
  in the target language necessarily. To model them, we formalize a specific semantic statement
  and we call them \<^emph>\<open>routine\<close> to distinguish with \<^emph>\<open>procedure\<close>.\<close>

definition Well_Typed_Vals :: \<open>TY list \<Rightarrow> 'a::VALs \<phi>arg set\<close>
  where \<open>Well_Typed_Vals TYs = {vs. list_all2 (\<lambda>v T. v \<in> Well_Type T) (to_vals (\<phi>arg.dest vs)) TYs}\<close>

definition op_routine :: \<open>TY list \<Rightarrow> TY list \<Rightarrow> ('a::FIX_ARITY_VALs, 'b::FIX_ARITY_VALs) proc' \<Rightarrow> ('a,'b) proc'\<close>
  where \<open>op_routine argtys rettys F = (\<lambda>args.
      \<phi>M_assert (args \<in> Well_Typed_Vals argtys)
   \<ggreater> F args
  \<bind> (\<lambda>rets. \<phi>M_assert (rets \<in> Well_Typed_Vals rettys)
           \<ggreater> Return rets))\<close>

definition \<phi>_Have_Types :: \<open>('a::VALs \<phi>arg \<Rightarrow> assn) \<Rightarrow> TY list \<Rightarrow> bool\<close>
  where \<open>\<phi>_Have_Types spec TYs = (\<forall>v. Inhabited (spec v) \<longrightarrow> v \<in> Well_Typed_Vals TYs)\<close>

declare [[\<phi>reason_default_pattern \<open>\<phi>_Have_Types ?S _\<close> \<Rightarrow> \<open>\<phi>_Have_Types ?S _\<close> (100)]]

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 1200 for \<open>\<phi>_Have_Types (\<lambda>vs. ?R vs\<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst vs] ?T) _\<close>]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R vs) TYs
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R (\<phi>V_snd vs)\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst vs] T) (TY#TYs)\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def \<phi>arg_forall \<phi>SemType_def subset_iff
  by (clarsimp simp add: to_vals_prod_def to_vals_VAL_def Val_inhabited_rewr)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[vs] T) [TY]\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def \<phi>arg_forall \<phi>SemType_def subset_iff
  by (clarsimp simp add: to_vals_prod_def to_vals_VAL_def Val_inhabited_rewr)

lemma [\<phi>reason 1200]:
  \<open> \<phi>_Have_Types R TYs
\<Longrightarrow> \<phi>_Have_Types (\<lambda>vs. R vs\<heavy_comma> S) TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def by clarsimp

lemma [\<phi>reason 2000]:
  \<open> \<phi>_Have_Types (\<lambda>_::unit \<phi>arg. Void) []\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def to_vals_unit_def by clarsimp

lemma [\<phi>reason 1020 except \<open>\<phi>_Have_Types (\<lambda>vs. ?A vs\<heavy_comma> ?B vs) _\<close>]:
  \<open> \<phi>_Have_Types (\<lambda>vs. Void\<heavy_comma> R vs) TYs
\<Longrightarrow> \<phi>_Have_Types R TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def by clarsimp

lemma [\<phi>reason 1000]:
  \<open> FAIL TEXT(\<open>Fail to infer the semantic type of\<close> R)
\<Longrightarrow> \<phi>_Have_Types R TYs\<close>
  unfolding \<phi>_Have_Types_def Well_Typed_Vals_def by clarsimp

lemma "__routine__":
  \<open> \<phi>_Have_Types X TY_ARGs
\<Longrightarrow> \<phi>_Have_Types Y TY_RETs
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>(vs:: 'a::FIX_ARITY_VALs \<phi>arg <named> 'names).
          \<p>\<r>\<o>\<c> F (case_named id vs) \<lbrace> X (case_named id vs) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_routine TY_ARGs TY_RETs F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding op_routine_def \<phi>_Have_Types_def named_All named.case id_apply
  by (rule \<phi>SEQ, rule \<phi>SEQ, rule \<phi>M_assert, blast, assumption, rule \<phi>SEQ,
      rule \<phi>M_assert, blast, rule \<phi>M_Success')

ML_file \<open>library/cf_routine.ML\<close>

attribute_setup routine =
  \<open>Scan.succeed (Phi_Modifier.wrap_to_attribute PhiSem_Control_Flow.routine_mod)\<close>


end