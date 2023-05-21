theory PhiSem_CF_Routine
  imports PhiSem_CF_Break PhiSem_CF_Routine_Basic
begin

definition op_routine
        :: \<open>TY list \<Rightarrow> TY list \<Rightarrow>
            (RES.brk_label \<Rightarrow> ('a::FIX_ARITY_VALs, 'b::FIX_ARITY_VALs) proc') \<Rightarrow>
            ('a,'b) proc'\<close>
  where \<open>op_routine argtys rettys F =
    op_routine_basic argtys rettys (\<lambda>arg. op_brk_scope (\<lambda>brk. F brk arg))\<close>

abbreviation
  \<open>op_rec_routine argtys rettys F \<equiv> op_fix_point (\<lambda>\<f>. op_routine argtys rettys (F \<f>))\<close>

lemma "__routine__":
  \<open> \<phi>_Have_Types X TY_ARGs
\<Longrightarrow> \<phi>_Have_Types Y TY_RETs
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>(vs:: 'a::FIX_ARITY_VALs \<phi>arg <named> 'names) label_ret.
      return_\<phi>app\<^bold>: TECHNICAL(
          \<forall>ret :: 'b :: FIX_ARITY_VALs \<phi>arg.
            \<p>\<r>\<o>\<c> (op_break label_ret ret :: 'b proc) \<lbrace> Y ret\<heavy_comma> TECHNICAL Brk_Frame label_ret \<longmapsto> 0 \<rbrace>
            \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label_ret Y))
      \<Longrightarrow> \<p>\<r>\<o>\<c> F label_ret (case_named (\<lambda>x. x) vs) \<lbrace> X (case_named id vs)\<heavy_comma> TECHNICAL Brk_Frame label_ret
                                          \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> TECHNICAL Brk_Frame label_ret
                                            \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. \<b>\<r>\<e>\<a>\<k> label_ret \<w>\<i>\<t>\<h> Y \<o>\<r> E e))
\<Longrightarrow> \<p>\<r>\<o>\<c> op_routine TY_ARGs TY_RETs F vs \<lbrace> X vs \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  unfolding op_routine_def
  \<medium_left_bracket> premises [\<phi>reason 5000] and [\<phi>reason 5000] and _ and F
    apply_rule "__routine_basic__"[where TY_ARGs=TY_ARGs and TY_RETs=TY_RETs and X=X and Y=Y
                                                         and vs=vs and 'names='names, simplified]
    \<medium_left_bracket> for vs
      brk_scope \<medium_left_bracket> for label_ret
        apply_rule F[where vs=\<open>tag vs\<close>, unfolded Technical_def[where 'a=\<open>bool\<close>], simplified]
        apply_rule "_op_break_rule_"
      \<medium_right_bracket>
    \<medium_right_bracket>
  \<medium_right_bracket>.

attribute_setup routine =
  \<open>Scan.succeed (Phi_Modifier.wrap_to_attribute
      (PhiSem_Control_Flow.routine_mod
          (fn T => \<^typ>\<open>RES.brk_label\<close> --> T)
          (fn N => fn wrap => fn Tm => Abs("label_ret", \<^typ>\<open>RES.brk_label\<close>, wrap (Tm $ Bound N)))
          @{thm "__routine__"}))\<close>


end