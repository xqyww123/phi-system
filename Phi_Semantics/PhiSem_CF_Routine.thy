theory PhiSem_CF_Routine
  imports PhiSem_CF_Break PhiSem_CF_Routine_Basic PhiSem_Void
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
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_break TYPE('any) TYPE('rets) label ret) \<lbrace> TECHNICAL Brk_Frame label\<heavy_comma> Y ret \<longmapsto> 0 \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label Y) \<close>
  for ret :: \<open>'rets::FIX_ARITY_VALs \<phi>arg\<close>
  using op_break_\<phi>app .

lemma RETURN_FRAME_unit:
  \<open> RETURN_FRAME TYPE(unit) label Y
\<Longrightarrow> \<p>\<r>\<o>\<c> (op_break TYPE('any) TYPE(unit) label \<phi>V_none) \<lbrace> TECHNICAL Brk_Frame label\<heavy_comma> Y (\<phi>arg ()) \<longmapsto> 0 \<rbrace>
    \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame label Y) \<close>
  unfolding \<phi>V_none_def
  using op_break_\<phi>app[where S=Y] .

(* TODO: suppress the Frame tailing in the above rules!!!!
lemma RETURN_FRAME_normal:
  \<open> RETURN_FRAME TYPE('rets) label Y
\<Longrightarrow> State \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y ret\<heavy_comma> TECHNICAL Brk_Frame label
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
\<Longrightarrow> State \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y (\<phi>arg ())\<heavy_comma> TECHNICAL Brk_Frame label
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
      and  F: \<open>(\<And>(vs:: 'args::FIX_ARITY_VALs \<phi>arg <named> 'names) label_ret.
            return_\<phi>app\<^bold>: TECHNICAL(RETURN_FRAME TYPE('rets::FIX_ARITY_VALs) label_ret Y)
            \<Longrightarrow> \<p>\<r>\<o>\<c> F label_ret (case_named (\<lambda>x. x) vs)
                   \<lbrace> TECHNICAL Brk_Frame label_ret\<heavy_comma> X (case_named id vs)
                 \<longmapsto> \<lambda>ret. TECHNICAL Brk_Frame label_ret\<heavy_comma> Y ret
                   \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. \<b>\<r>\<e>\<a>\<k> label_ret \<w>\<i>\<t>\<h> Y \<o>\<r> E e))\<close>
  input  \<open>X vs\<close>
  output \<open>Y\<close>
  throws \<open>E\<close>
\<medium_left_bracket>
  apply_rule "__routine_basic__"[OF Ty_X Ty_Y, where 'names='names,
                                 unfolded named_All, simplified]
  \<medium_left_bracket> for vs 
    op_brk_scope \<medium_left_bracket>  for label_ret
      apply_rule F[of label_ret \<open>tag vs\<close>, unfolded Technical_def[where 'a=\<open>bool\<close>], simplified, OF RETURN_FRAME_I]
    \<medium_right_bracket>
  \<medium_right_bracket>
\<medium_right_bracket> .

ML \<open>Synchronized.change Phi_Syntax.semantic_oprs (Symtab.update (\<^const_name>\<open>op_routine\<close>, 0))\<close>


definition
  \<open>op_rec_routine TYr TYa argtys rettys F \<equiv> op_fix_point (\<lambda>\<f>.
        op_routine TYr TYa argtys rettys (F \<f>))\<close>

declare op_rec_routine_def[symmetric, procedure_simps]

attribute_setup routine =
  \<open>Scan.succeed (Phi_Modifier.wrap_to_attribute
      (PhiSem_Control_Flow.routine_mod
          (fn T => \<^typ>\<open>RES.brk_label\<close> --> T)
          (fn N => fn wrap => fn Tm => Abs("label_ret", \<^typ>\<open>RES.brk_label\<close>, wrap (Tm $ Bound N)))
          @{thm "op_routine_\<phi>app"}))\<close>

hide_fact RETURN_FRAME_normal RETURN_FRAME_unit


subsection \<open>Syntax\<close>

syntax "_routine_" :: \<open>idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> do_binds \<Rightarrow> do_bind\<close>
          ("((2\<r>\<o>\<u>\<t>\<i>\<n>\<e> '(_ : _') : _ {//)(_)//})" [12,12,100,12] 13)
       "_recursive_routine_" :: \<open>idt \<Rightarrow> idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> do_binds \<Rightarrow> do_bind\<close>
          ("((2\<r>\<e>\<c>\<u>\<r>\<s>\<i>\<v>\<e>-\<r>\<o>\<u>\<t>\<i>\<n>\<e> _ '(_ : _') : _ {//)(_)//})")

print_ast_translation \<open>let open Ast
  fun get_label (Appl [Constant "_constrain", BV, _]) = get_label BV
    | get_label (Appl [Constant "_bound", Variable bv]) = bv
  fun is_label lb (Appl [Constant "_constrain", BV, _]) = is_label lb BV
    | is_label lb (Appl [Constant "_bound", Variable bv]) = bv = lb
  fun tr lret (tm as Appl [Constant \<^const_syntax>\<open>PhiSem_CF_Break.op_break\<close>, _, _, BV, X]) =
        if is_label lret BV
        then Appl [Constant \<^const_syntax>\<open>Return\<close>, X]
        else tm
    | tr lret (Appl aps) = Appl (map (tr lret) aps)
    | tr _ X = X
  fun tr0 cfg (Appl [Constant \<^syntax_const>\<open>_do_block\<close>, X]) = tr cfg X
    | tr0 cfg X = tr cfg X
  fun strip_list (Appl [Constant \<^syntax_const>\<open>_list\<close>, X]) = strip_list X
    | strip_list (Appl [Constant "_args", A, B]) =
        Appl [Constant "\<^const>Product_Type.Times", strip_list A, strip_list B]
    | strip_list (Constant \<^const_syntax>\<open>Nil\<close>) =
        Constant \<^const_syntax>\<open>\<v>\<o>\<i>\<d>\<close>
    | strip_list X = X
in [
  (\<^const_syntax>\<open>op_routine\<close>, fn ctxt =>
    if Syntax_Group.is_enabled (Proof_Context.theory_of ctxt) @{syntax_group do_notation}
    then
      fn [_, _, TY1, TY2, Appl [Constant "_abs", lret, Appl [Constant "_abs", arg, X]]] =>
          Appl [Constant \<^syntax_const>\<open>_routine_\<close>, arg,
                strip_list TY1, strip_list TY2, tr0 (get_label lret) X]
       | [_, _, TY1, TY2, Appl [Constant "_abs", lret, Appl [Constant "_abs", arg, X]], Y] =>
          Appl [
            Appl [Constant \<^syntax_const>\<open>_routine_\<close>, arg,
                  strip_list TY1, strip_list TY2, tr0 (get_label lret) X],
            Y]
    else fn _ => raise Match),
  (\<^const_syntax>\<open>op_rec_routine\<close>, fn ctxt =>
    if Syntax_Group.is_enabled (Proof_Context.theory_of ctxt) @{syntax_group do_notation}
    then
      fn [TY1, TY2, Appl [Constant "_abs", lf,
                              Appl [Constant "_abs", lret, Appl [Constant "_abs", arg, X]]]] =>
          Appl [Constant \<^syntax_const>\<open>_recursive_routine_\<close>, lf, arg,
                strip_list TY1, strip_list TY2, tr0 (get_label lret) X]
       | [TY1, TY2, Appl [Constant "_abs", lf, 
                              Appl [Constant "_abs", lret, Appl [Constant "_abs", arg, X]], Y]] =>
          Appl [
            Appl [Constant \<^syntax_const>\<open>_routine_\<close>, lf, arg,
                  strip_list TY1, strip_list TY2, tr0 (get_label lret) X],
            Y]
    else fn _ => raise Match)
] end\<close>


ML_file \<open>codegen/C/routine.ML\<close>

end