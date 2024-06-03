theory PhiSem_CF_Routine_Basic
  imports PhiSem_CF_Basic
begin

section \<open>Routine\<close>

text \<open>Procedure in \<open>\<phi>\<close>-system is a program segment, which does not correspond to a function
  in the target language necessarily. To model them, we formalize a specific semantic statement
  and we call them \<^emph>\<open>routine\<close> to distinguish with \<^emph>\<open>procedure\<close>.\<close>

definition op_routine_basic :: \<open>TY list \<Rightarrow> TY list \<Rightarrow> ('a::FIX_ARITY_VALs, 'b::FIX_ARITY_VALs) proc' \<Rightarrow> ('a,'b) proc'\<close>
  where \<open>op_routine_basic argtys rettys F = (\<lambda>args.
      \<phi>M_assert (args \<in> Well_Typed_Vals argtys)
   \<then> F args
  \<bind> (\<lambda>rets. \<phi>M_assert (rets \<in> Well_Typed_Vals rettys)
           \<then> Return rets))\<close>

lemma "__routine_basic__":
  \<open> \<phi>_Have_Types X TY_ARGs
\<Longrightarrow> \<phi>_Have_Types Y TY_RETs
\<Longrightarrow> (\<And>(vs:: 'a::FIX_ARITY_VALs \<phi>arg <named> 'names).
          \<p>\<r>\<o>\<c> F (case_named id vs) \<lbrace> X (case_named id vs) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_routine_basic TY_ARGs TY_RETs F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding op_routine_basic_def \<phi>_Have_Types_def named_All named.case id_apply
  by (rule \<phi>SEQ, rule \<phi>SEQ, rule \<phi>M_assert, blast, assumption, rule \<phi>SEQ,
      rule \<phi>M_assert, blast, rule \<phi>M_Success')

ML_file \<open>library/cf_routine.ML\<close>

attribute_setup routine_basic =
  \<open>Scan.succeed (Phi_Modifier.wrap_to_attribute
                    (PhiSem_Control_Flow.routine_mod I (K I) @{thm "__routine_basic__"}))\<close>



end