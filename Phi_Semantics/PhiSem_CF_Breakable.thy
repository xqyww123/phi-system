theory PhiSem_CF_Breakable
  imports PhiSem_CF_Break PhiSem_CF_Basic
begin

thm while_\<phi>app

definition continue_label :: \<open>brk_label \<Rightarrow> brk_label\<close>
  where \<open>continue_label x = x\<close>

thm brk_scope

declare [[\<phi>trace_reasoning]]
declare distrib_right[assertion_simps]
thm assertion_simps


proc while:
  assumes \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x)\<close>
  and CT: \<open>\<^bold>v\<^bold>i\<^bold>e\<^bold>w U \<longmapsto> (X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x) @action ToSA\<close>
  and C: "\<And>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<Longrightarrow>
                  \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<lbrace> X x \<longmapsto> X x'\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l cond x' \<Ztypecolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E1"
  and B: "\<And>x lb lc. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e invariant x \<Longrightarrow>
                    \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<Longrightarrow>
                    \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<lbrace> X x\<heavy_comma> Brk_Frame (continue_label lc)\<heavy_comma> Brk_Frame lb
                            \<longmapsto> X x'\<heavy_comma> Brk_Frame (continue_label lc)\<heavy_comma> Brk_Frame lb
                                \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x'
                              \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s (\<lambda>e. \<^bold>b\<^bold>r\<^bold>e\<^bold>a\<^bold>k lb \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<lambda>_::unit \<phi>arg. X x'\<heavy_comma> Brk_Frame (continue_label lc) \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> \<not> cond x')
                                         \<^bold>o\<^bold>r \<^bold>b\<^bold>r\<^bold>e\<^bold>a\<^bold>k (continue_label lc) \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<lambda>_::unit \<phi>arg. X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x')
                                         \<^bold>o\<^bold>r E2 e)"
  input \<open>U\<close>
  output \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. invariant x \<and> \<not> cond x\<close>
  throws \<open>E1 + E2\<close>
  \<medium_left_bracket> CT
    brk_scope \<medium_left_bracket> for lb
      PhiSem_CF_Basic.while \<open>Brk_Frame lb\<heavy_comma> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: invariant x \<and> Guard: cond x\<close>
      \<medium_left_bracket> C \<medium_right_bracket>.
      \<medium_left_bracket> brk_scope \<medium_left_bracket> for lc
          B[unfolded continue_label_def, where lb=lb]
        \<medium_right_bracket> for \<open>(X x'\<heavy_comma> Brk_Frame lb \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x')\<heavy_comma> Brk_Frame lc\<close> .. ;;
      \<medium_right_bracket>. ;;
    \<medium_right_bracket> for \<open>(X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> \<not> cond x')\<heavy_comma> Brk_Frame lb\<close> .. ;;
  \<medium_right_bracket>. .

term \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<lbrace> X x \<longmapsto> \<lambda>\<r>\<e>\<t>. X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<rbrace>
      \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>e. \<^bold>b\<^bold>r\<^bold>e\<^bold>a\<^bold>k lb
                       \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<lambda>_. X x'\<heavy_comma> Brk_Frame (continue_label lc) \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x' \<and> \<not> cond x')
                       \<^bold>o\<^bold>r \<^bold>b\<^bold>r\<^bold>e\<^bold>a\<^bold>k (continue_label lc)
                       \<^bold>w\<^bold>i\<^bold>t\<^bold>h (\<lambda>_. X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. invariant x')
                       \<^bold>o\<^bold>r E2 e\<close>
        thm \<phi>

        term \<open>A \<Longrightarrow> B\<close>

end