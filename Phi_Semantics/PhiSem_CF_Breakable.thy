theory PhiSem_CF_Breakable
  imports PhiSem_CF_Break PhiSem_CF_Basic
begin

(*declare [[\<phi>hide_techinicals=false]]*)

text \<open>Since we have \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> now, the termination condition of a loop is not
  necessarily the negative of the loop guard. Therefore here we need 3 assertions, invariance,
  guard, and termination condition.\<close>

proc while:
  requires \<open>\<p>\<a>\<r>\<a>\<m> (X x \<s>\<u>\<b>\<j> x. Inv: invariant x \<and> Guard: cond x \<and> End: termination x)\<close>
  and S: \<open>U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((X x \<r>\<e>\<m>\<a>\<i>\<n>\<s> R) \<s>\<u>\<b>\<j> x. invariant x)\<close>
  and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x. invariant x \<and> \<not> cond x \<longrightarrow> termination x)\<close>
  and C: "\<And>x. \<p>\<r>\<e>\<m>\<i>\<s>\<e> invariant x \<Longrightarrow>
                  \<p>\<r>\<o>\<c> Cond \<lbrace> X x\<heavy_comma> R \<longmapsto> \<v>\<a>\<l> cond x' \<Ztypecolon> \<bool>\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1"
  and B: "\<And>x lb lc. \<p>\<r>\<e>\<m>\<i>\<s>\<e> invariant x \<Longrightarrow>
                    \<p>\<r>\<e>\<m>\<i>\<s>\<e> cond x \<Longrightarrow>
                    break_\<phi>app\<^bold>: TECHNICAL
                        \<p>\<r>\<o>\<c> op_break TYPE(unit) TYPE(unit) lb \<phi>V_none
                           \<lbrace> TECHNICAL Brk_Frame lb\<heavy_comma> (TECHNICAL Brk_Frame lc\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x') \<longmapsto> 0 \<rbrace>
                        \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame lb (\<lambda>_::unit \<phi>arg. TECHNICAL Brk_Frame lc\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x')) \<Longrightarrow>
                    continue_\<phi>app\<^bold>: TECHNICAL
                        \<p>\<r>\<o>\<c> op_break TYPE(unit) TYPE(unit) lc \<phi>V_none
                           \<lbrace> TECHNICAL Brk_Frame lc\<heavy_comma> (TECHNICAL Brk_Frame lb\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x') \<longmapsto> 0 \<rbrace>
                        \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame lc (\<lambda>_::unit \<phi>arg. TECHNICAL Brk_Frame lb\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x')) \<Longrightarrow>
                    \<p>\<r>\<o>\<c> Body lb lc
                        \<lbrace> TECHNICAL Brk_Frame lb\<heavy_comma> TECHNICAL Brk_Frame lc\<heavy_comma> X x\<heavy_comma> R
                      \<longmapsto> TECHNICAL Brk_Frame lb\<heavy_comma> TECHNICAL Brk_Frame lc\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x'
                         \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. \<b>\<r>\<e>\<a>\<k> lb \<w>\<i>\<t>\<h> (\<lambda>_::unit \<phi>arg. TECHNICAL Brk_Frame lc\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x')
                                    \<o>\<r> \<b>\<r>\<e>\<a>\<k> lc \<w>\<i>\<t>\<h> (\<lambda>_::unit \<phi>arg. X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x')
                                    \<o>\<r> E2 e)"
  input \<open>U\<close>
  output \<open>R\<heavy_comma> X x \<s>\<u>\<b>\<j> x. invariant x \<and> termination x\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> S
    op_brk_scope \<medium_left_bracket> for lb
      PhiSem_CF_Basic.while \<open>X x\<heavy_comma> R\<heavy_comma> TECHNICAL Brk_Frame lb \<s>\<u>\<b>\<j> x. Inv: invariant x \<and> Guard: cond x\<close>
      \<medium_left_bracket> C \<medium_right_bracket>
      \<medium_left_bracket> op_brk_scope \<medium_left_bracket> for lc 
          apply_rule B[where lb1=lb]
          apply_rule op_break[THEN Technical_I, THEN Labelled_I]
          apply_rule op_break[THEN Technical_I, THEN Labelled_I] \<semicolon>
        \<medium_right_bracket> for \<open>TECHNICAL Brk_Frame lc\<heavy_comma> (TECHNICAL Brk_Frame lb\<heavy_comma> X x'\<heavy_comma> R \<s>\<u>\<b>\<j> x'. invariant x')\<close> \<semicolon>
      \<medium_right_bracket> \<semicolon>
    \<medium_right_bracket> for \<open>(R\<heavy_comma> X x' \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x')\<heavy_comma> TECHNICAL Brk_Frame lb\<close> \<semicolon>
  \<medium_right_bracket>.

hide_const (open) PhiSem_CF_Basic.while

lemmas while'_\<phi>app = PhiSem_CF_Basic.while_\<phi>app \<comment> \<open>Non-breaking while loop\<close>


subsection \<open>Syntax\<close>

optional_translations (do_notation)
  "_while_ C B" <= "CONST PhiSem_CF_Breakable.while C B"

syntax "_continue_" :: \<open>do_bind\<close> ("\<c>\<o>\<n>\<t>\<i>\<n>\<u>\<e>")
       "_break_" :: \<open>do_bind\<close> ("\<b>\<r>\<e>\<a>\<k>")

print_ast_translation \<open>let open Ast
  fun get_label (Appl [Constant "_constrain", BV, _]) = get_label BV
    | get_label (Appl [Constant "_bound", Variable bv]) = bv
  fun is_label lb (Appl [Constant "_constrain", BV, _]) = is_label lb BV
    | is_label lb (Appl [Constant "_bound", Variable bv]) = bv = lb
  fun tr (lc,lb) (tm as Appl [Constant \<^const_syntax>\<open>PhiSem_CF_Break.op_break\<close>, _, _, BV, _]) =
        if is_label lc BV
        then Constant \<^syntax_const>\<open>_continue_\<close>
        else if is_label lb BV
        then Constant \<^syntax_const>\<open>_break_\<close>
        else tm
    | tr lbc (Appl aps) = Appl (map (tr lbc) aps)
    | tr _ X = X
  fun tr0 cfg (Appl [Constant \<^syntax_const>\<open>_do_block\<close>, X]) = tr cfg X
    | tr0 cfg X = tr cfg X
in [
  (\<^syntax_const>\<open>_while_\<close>, fn ctxt =>
    fn [C, Appl [Constant "_abs", lb0, Appl [Constant "_abs", lc0, X]]] =>
      if Syntax_Group.is_enabled (Proof_Context.theory_of ctxt) @{syntax_group do_notation}
      then Appl [Constant \<^syntax_const>\<open>_while_\<close>, C, tr0 (get_label lc0, get_label lb0) X]
      else raise Match)
] end\<close>


end