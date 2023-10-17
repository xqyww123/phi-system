theory PhiSem_CF_Breakable
  imports PhiSem_CF_Break PhiSem_CF_Basic
begin

declare [[\<phi>hide_techinicals=false]]

text \<open>Since we have \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> now, the termination condition of a loop is not
  necessarily the negative of the loop guard. Therefore here we need 3 assertions, invariance,
  guard, and termination condition.\<close>

proc while:
  requires \<open>\<p>\<a>\<r>\<a>\<m> (X x \<s>\<u>\<b>\<j> x. Inv: invariant x \<and> Guard: cond x \<and> End: termination x)\<close>
  and S: \<open>U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((X x \<r>\<e>\<m>\<a>\<i>\<n>\<s> R) \<s>\<u>\<b>\<j> x. invariant x) @action NToA\<close>
  and \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x. invariant x \<and> \<not> cond x \<longrightarrow> termination x)\<close>
  and C: "\<And>x. \<p>\<r>\<e>\<m>\<i>\<s>\<e> invariant x \<Longrightarrow>
                  \<p>\<r>\<o>\<c> Cond \<lbrace> R\<heavy_comma> X x \<longmapsto> R\<heavy_comma> X x'\<heavy_comma> \<v>\<a>\<l> cond x' \<Ztypecolon> \<bool> \<s>\<u>\<b>\<j> x'. invariant x' \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E1"
  and B: "\<And>x lb lc. \<p>\<r>\<e>\<m>\<i>\<s>\<e> invariant x \<Longrightarrow>
                    \<p>\<r>\<e>\<m>\<i>\<s>\<e> cond x \<Longrightarrow>
                    break_\<phi>app\<^bold>: TECHNICAL
                        \<p>\<r>\<o>\<c> op_break TYPE(unit) TYPE(unit) lb \<phi>V_none
                           \<lbrace> (R\<heavy_comma> X x'\<heavy_comma> TECHNICAL Brk_Frame lc \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x')\<heavy_comma> TECHNICAL Brk_Frame lb \<longmapsto> 0 \<rbrace>
                        \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame lb (\<lambda>_::unit \<phi>arg. R\<heavy_comma> X x'\<heavy_comma> TECHNICAL Brk_Frame lc \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x')) \<Longrightarrow>
                    continue_\<phi>app\<^bold>: TECHNICAL
                        \<p>\<r>\<o>\<c> op_break TYPE(unit) TYPE(unit) lc \<phi>V_none
                           \<lbrace> (R\<heavy_comma> X x'\<heavy_comma> TECHNICAL Brk_Frame lb \<s>\<u>\<b>\<j> x'. invariant x')\<heavy_comma> TECHNICAL Brk_Frame lc \<longmapsto> 0 \<rbrace>
                        \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>_. Brking_Frame lc (\<lambda>_::unit \<phi>arg. R\<heavy_comma> X x'\<heavy_comma> TECHNICAL Brk_Frame lb \<s>\<u>\<b>\<j> x'. invariant x')) \<Longrightarrow>
                    \<p>\<r>\<o>\<c> Body lb lc
                        \<lbrace> R\<heavy_comma> X x\<heavy_comma> TECHNICAL Brk_Frame lc\<heavy_comma> TECHNICAL Brk_Frame lb
                      \<longmapsto> R\<heavy_comma> X x'\<heavy_comma> TECHNICAL Brk_Frame lc\<heavy_comma> TECHNICAL Brk_Frame lb \<s>\<u>\<b>\<j> x'. invariant x'
                         \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> (\<lambda>e. \<b>\<r>\<e>\<a>\<k> lb \<w>\<i>\<t>\<h> (\<lambda>_::unit \<phi>arg. R\<heavy_comma> X x'\<heavy_comma> TECHNICAL Brk_Frame lc \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x')
                                    \<o>\<r> \<b>\<r>\<e>\<a>\<k> lc \<w>\<i>\<t>\<h> (\<lambda>_::unit \<phi>arg. R\<heavy_comma> X x' \<s>\<u>\<b>\<j> x'. invariant x')
                                    \<o>\<r> E2 e)"
  input \<open>U\<close>
  output \<open>R\<heavy_comma> X x \<s>\<u>\<b>\<j> x. invariant x \<and> termination x\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> S
    brk_scope \<medium_left_bracket> for lb
      PhiSem_CF_Basic.while \<open>TECHNICAL Brk_Frame lb\<heavy_comma> R\<heavy_comma> X x \<s>\<u>\<b>\<j> x. Inv: invariant x \<and> Guard: cond x\<close>
      \<medium_left_bracket> C \<medium_right_bracket>
      \<medium_left_bracket> brk_scope \<medium_left_bracket> for lc    
          apply_rule B[where lb1=lb]
          apply_rule op_break[THEN Technical_I, THEN Labelled_I]
          apply_rule op_break[THEN Technical_I, THEN Labelled_I]
        ;;
        \<medium_right_bracket> for \<open>(R\<heavy_comma> X x'\<heavy_comma> TECHNICAL Brk_Frame lb \<s>\<u>\<b>\<j> x'. invariant x')\<heavy_comma> TECHNICAL Brk_Frame lc\<close> ;;
      \<medium_right_bracket> ;;
    \<medium_right_bracket> for \<open>(R\<heavy_comma> X x' \<s>\<u>\<b>\<j> x'. invariant x' \<and> termination x')\<heavy_comma> TECHNICAL Brk_Frame lb\<close> ;;
  \<medium_right_bracket>.

hide_const (open) PhiSem_CF_Basic.while

end