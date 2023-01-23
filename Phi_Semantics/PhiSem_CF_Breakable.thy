theory PhiSem_CF_Breakable
  imports PhiSem_CF_Break PhiSem_CF_Basic
begin


text \<open>Since we have \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> now, the termination condition of a loop is not
  necessarily the negative of the loop guard. Therefore here we need 3 assertions, invariance,
  guard, and termination condition.\<close>

proc while:
  assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x \<and> End: termination x)\<close>
  and S: \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w U \<longmapsto> (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x) @action ToSA\<close>
  and \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (\<forall>x. \<not> cond x \<longrightarrow> termination x)\<close>
  and C: "\<And>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<Longrightarrow>
                  \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<lbrace> X x \<longmapsto> X x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1"
  and B: "\<And>x lb lc. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<Longrightarrow>
                    \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<Longrightarrow>
                    break_\<phi>app\<^bold>: HIDDEN_PREM(
                        \<^bold>p\<^bold>r\<^bold>o\<^bold>c (op_break lb \<phi>V_none :: unit proc)
                           \<lbrace> (X x'\<heavy_comma> Brk_Frame lc \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> termination x')\<heavy_comma> Brk_Frame lb \<longmapsto> 0 \<rbrace>
                        \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>_. Brking_Frame lb (\<lambda>_::unit \<phi>arg. X x'\<heavy_comma> Brk_Frame lc \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> termination x'))) \<Longrightarrow>
                    continue_\<phi>app\<^bold>: HIDDEN_PREM(
                        \<^bold>p\<^bold>r\<^bold>o\<^bold>c (op_break lc \<phi>V_none :: unit proc)
                           \<lbrace> (X x'\<heavy_comma> Brk_Frame lb \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x')\<heavy_comma> Brk_Frame lc \<longmapsto> 0 \<rbrace>
                        \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>_. Brking_Frame lc (\<lambda>_::unit \<phi>arg. X x'\<heavy_comma> Brk_Frame lb \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x'))) \<Longrightarrow>
                    \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body lb lc
                        \<lbrace> X x\<heavy_comma> Brk_Frame lc\<heavy_comma> Brk_Frame lb
                      \<longmapsto> X x'\<heavy_comma> Brk_Frame lc\<heavy_comma> Brk_Frame lb \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x'
                         \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>e. \<^bold>b\<^bold>r\<^bold>e\<^bold>a\<^bold>k lb \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<lambda>_::unit \<phi>arg. X x'\<heavy_comma> Brk_Frame lc \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> termination x')
                                    \<^bold>o\<^bold>r \<^bold>b\<^bold>r\<^bold>e\<^bold>a\<^bold>k lc \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<lambda>_::unit \<phi>arg. X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x')
                                    \<^bold>o\<^bold>r E2 e)"
  input \<open>U\<close>
  output \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> termination x\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> S
    brk_scope \<medium_left_bracket> for lb
      PhiSem_CF_Basic.while \<open>Brk_Frame lb\<heavy_comma> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x\<close>
      \<medium_left_bracket> C \<medium_right_bracket>.
      \<medium_left_bracket> brk_scope \<medium_left_bracket> for lc
          B[where lb1=lb]
          "_op_break_rule_"[THEN HIDDEN_PREM_I, THEN Labelled_I]
          "_op_break_rule_"[THEN HIDDEN_PREM_I, THEN Labelled_I]
        \<medium_right_bracket> for \<open>(X x'\<heavy_comma> Brk_Frame lb \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x')\<heavy_comma> Brk_Frame lc\<close> .. ;;
      \<medium_right_bracket>. ;;
      \<medium_right_bracket> for \<open>(X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> termination x')\<heavy_comma> Brk_Frame lb\<close> .. ;;
  \<medium_right_bracket>. .

hide_const (open) PhiSem_CF_Basic.while

end