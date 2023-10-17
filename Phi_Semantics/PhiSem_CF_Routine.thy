theory PhiSem_CF_Routine
  imports PhiSem_CF_Break PhiSem_CF_Routine_Basic
begin

declare [[\<phi>hide_techinicals = false]]

proc op_routine:
  requires Ty_X: \<open>\<phi>_Have_Types X TY_ARGs\<close>
      and  Ty_Y: \<open>\<phi>_Have_Types Y TY_RETs\<close>
      and  \<open>\<r>Success\<close>
      and  F: \<open>(\<And>(vs:: 'args::FIX_ARITY_VALs \<phi>arg <named> 'names) label_ret.
            return_\<phi>app\<^bold>: TECHNICAL(
                \<forall>ret :: 'rets::FIX_ARITY_VALs \<phi>arg.
                  \<p>\<r>\<o>\<c> (op_break TYPE('rets) TYPE('rets) label_ret ret) \<lbrace> Y ret\<heavy_comma> TECHNICAL Brk_Frame label_ret \<longmapsto> 0 \<rbrace>
                  \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label_ret Y))
            \<Longrightarrow> \<p>\<r>\<o>\<c> F label_ret (case_named (\<lambda>x. x) vs) \<lbrace> X (case_named id vs)\<heavy_comma> TECHNICAL Brk_Frame label_ret
                                                \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> TECHNICAL Brk_Frame label_ret
                                                  \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. \<b>\<r>\<e>\<a>\<k> label_ret \<w>\<i>\<t>\<h> Y \<o>\<r> E e))\<close>
  input  \<open>X vs\<close>
  output \<open>Y\<close>
  throws \<open>E\<close>
\<medium_left_bracket>
  apply_rule "__routine_basic__"[OF Ty_X Ty_Y \<r>Success_I, where 'names='names,
                                 unfolded named_All, simplified]
  \<medium_left_bracket> for vs 
    op_brk_scope \<medium_left_bracket> for label_ret
      apply_rule F[of label_ret \<open>tag vs\<close>, unfolded Technical_def[where 'a=\<open>bool\<close>], simplified]
      apply_rule op_break
    \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .

thm op_routine_\<phi>app

abbreviation
  \<open>op_rec_routine argtys rettys F \<equiv> op_fix_point (\<lambda>\<f>.
        op_routine TYPE('ret::FIX_ARITY_VALs) TYPE('arg::FIX_ARITY_VALs) argtys rettys (F \<f>))\<close>

attribute_setup routine =
  \<open>Scan.succeed (Phi_Modifier.wrap_to_attribute
      (PhiSem_Control_Flow.routine_mod
          (fn T => \<^typ>\<open>RES.brk_label\<close> --> T)
          (fn N => fn wrap => fn Tm => Abs("label_ret", \<^typ>\<open>RES.brk_label\<close>, wrap (Tm $ Bound N)))
          @{thm "op_routine_\<phi>app"}))\<close>


end