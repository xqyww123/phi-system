theory PhiSem_CF_Routine
  imports PhiSem_CF_Break PhiSem_CF_Routine_Basic
begin

text \<open>Based on the basic routine module, we provide the version that supports return statement.\<close>

declare [[\<phi>hide_techinicals = false]]

definition RETURN_FRAME :: \<open>'rets::FIX_ARITY_VALs itself \<Rightarrow> RES.brk_label \<Rightarrow> ('rets \<phi>arg \<Rightarrow> fiction set) \<Rightarrow> bool\<close>
  where \<open>RETURN_FRAME _ label Y \<longleftrightarrow> True\<close>

lemma RETURN_FRAME_I:
  \<open> RETURN_FRAME TY label Y \<close>
  unfolding RETURN_FRAME_def ..

lemma RETURN_FRAME_normal:
  \<open> RETURN_FRAME TYPE('rets) label Y
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_break TYPE('any) TYPE('rets) label ret) \<lbrace> Y ret\<heavy_comma> TECHNICAL Brk_Frame label \<longmapsto> 0 \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label Y) \<close>
  for ret :: \<open>'rets::FIX_ARITY_VALs \<phi>arg\<close>
  using op_break_\<phi>app .

lemma RETURN_FRAME_unit:
  \<open> RETURN_FRAME TYPE(unit) label Y
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_break TYPE('any) TYPE(unit) label (\<phi>arg ())) \<lbrace> Y (\<phi>arg ())\<heavy_comma> TECHNICAL Brk_Frame label \<longmapsto> 0 \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label Y) \<close>
  using op_break_\<phi>app[where S=Y] .

(* TODO: suppress the Frame tailing in the above rules!!!!
lemma RETURN_FRAME_normal:
  \<open> RETURN_FRAME TYPE('rets) label Y
\<Longrightarrow> State \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y ret\<heavy_comma> TECHNICAL Brk_Frame label @action NToA
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_break TYPE('any) TYPE('rets) label ret) \<lbrace> State \<longmapsto> 0 \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label Y) \<close>
  for ret :: \<open>'rets::FIX_ARITY_VALs \<phi>arg\<close>
\<medium_left_bracket> premises _ and Tr 
  Tr
  op_break_\<phi>app
\<medium_right_bracket> .

term \<open>Identity_Elements\<close>

lemma RETURN_FRAME_unit:
  \<open> RETURN_FRAME TYPE(unit) label Y
\<Longrightarrow> State \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y (\<phi>arg ())\<heavy_comma> TECHNICAL Brk_Frame label @action NToA
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_break TYPE('any) TYPE(unit) label (\<phi>arg ())) \<lbrace> State \<longmapsto> 0 \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label Y) \<close>
\<medium_left_bracket> premises _ and Tr
  Tr
  apply_rule op_break_\<phi>app[where S=Y]
\<medium_right_bracket> .
*)

attribute_setup RETURN_FRAME = \<open>Scan.succeed (Thm.rule_attribute [] (fn ctxt => fn th =>
                    th RS (Thm.transfer'' ctxt @{thm' RETURN_FRAME_unit})
    handle THM _ => th RS (Thm.transfer'' ctxt @{thm' RETURN_FRAME_normal})) )\<close>

declare [[
  \<phi>premise_attribute [RETURN_FRAME] for \<open>RETURN_FRAME _ _ _\<close>  (%\<phi>attr)
]]

(* RETURN_FRAME TYPE('rets::FIX_ARITY_VALs) label_ret *)

proc op_routine:
  requires Ty_X: \<open>\<phi>_Have_Types X TY_ARGs\<close>
      and  Ty_Y: \<open>\<phi>_Have_Types Y TY_RETs\<close>
      and  \<open>\<r>Success\<close>
      and  F: \<open>(\<And>(vs:: 'args::FIX_ARITY_VALs \<phi>arg <named> 'names) label_ret.
            return_\<phi>app\<^bold>: TECHNICAL(RETURN_FRAME TYPE('rets::FIX_ARITY_VALs) label_ret Y)
            \<Longrightarrow> \<p>\<r>\<o>\<c> F label_ret (case_named (\<lambda>x. x) vs)
                   \<lbrace> X (case_named id vs)\<heavy_comma> TECHNICAL Brk_Frame label_ret
                 \<longmapsto> \<lambda>ret. Y ret\<heavy_comma> TECHNICAL Brk_Frame label_ret
                   \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. \<b>\<r>\<e>\<a>\<k> label_ret \<w>\<i>\<t>\<h> Y \<o>\<r> E e))\<close>
  input  \<open>X vs\<close>
  output \<open>Y\<close>
  throws \<open>E\<close>
\<medium_left_bracket>
  apply_rule "__routine_basic__"[OF Ty_X Ty_Y \<r>Success_I, where 'names='names,
                                 unfolded named_All, simplified]
  \<medium_left_bracket> for vs 
    op_brk_scope \<medium_left_bracket>  for label_ret
      apply_rule F[of label_ret \<open>tag vs\<close>, unfolded Technical_def[where 'a=\<open>bool\<close>], simplified, OF RETURN_FRAME_I]
    \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .

ML \<open>Synchronized.change Phi_Syntax.semantic_oprs (Symtab.update (\<^const_name>\<open>op_routine\<close>, 0))\<close>

abbreviation
  \<open>op_rec_routine argtys rettys F \<equiv> op_fix_point (\<lambda>\<f>.
        op_routine TYPE('ret::FIX_ARITY_VALs) TYPE('arg::FIX_ARITY_VALs) argtys rettys (F \<f>))\<close>

attribute_setup routine =
  \<open>Scan.succeed (Phi_Modifier.wrap_to_attribute
      (PhiSem_Control_Flow.routine_mod
          (fn T => \<^typ>\<open>RES.brk_label\<close> --> T)
          (fn N => fn wrap => fn Tm => Abs("label_ret", \<^typ>\<open>RES.brk_label\<close>, wrap (Tm $ Bound N)))
          @{thm "op_routine_\<phi>app"}))\<close>

hide_fact RETURN_FRAME_normal RETURN_FRAME_unit

end