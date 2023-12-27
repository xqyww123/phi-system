theory PhiStd_Loop
  imports Phi_Semantics.PhiSem_CF_Basic
          Phi_Semantics.PhiSem_Machine_Integer
          Phi_Semantics.PhiSem_Variable
begin

declare [[\<phi>trace_reasoning = 0]]

proc replicate:
  requires \<open>\<p>\<a>\<r>\<a>\<m> X\<close>
       and TR: \<open>X\<^sub>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X s \<r>\<e>\<m>\<a>\<i>\<n>\<s> R @action NToA\<close>
       and ITER: \<open>\<And>i v. \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<le> i \<and> i < t \<Longrightarrow>
              \<p>\<r>\<o>\<c> ITER v \<lbrace> X i\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>('b) \<longmapsto> X (i+1) \<rbrace>\<close>
  input  \<open>X\<^sub>0\<heavy_comma> s \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<heavy_comma> t \<Ztypecolon> \<v>\<a>\<l> \<nat>('b)\<close>
  premises \<open>s \<le> t\<close>
       and \<open>t < 2 ^ LENGTH('b)\<close>
  output \<open>R\<heavy_comma> X t\<close>
\<medium_left_bracket>
  TR
  var i \<leftarrow> $s ;;
  while \<open>i \<Ztypecolon> \<v>\<a>\<r>[i] \<nat>('b)\<heavy_comma> X i
         \<s>\<u>\<b>\<j> i. Inv: (s \<le> i \<and> i \<le> t) \<and> Guard: (i < t)\<close>
  \<medium_left_bracket> $i < $t \<medium_right_bracket>
  \<medium_left_bracket>
    ITER ($i) ;;
    $i \<leftarrow> $i + \<open>1 \<Ztypecolon> \<nat>('b)\<close>
  \<medium_right_bracket> ;;
  have[simp]: \<open>i = t\<close> by auto_sledgehammer \<comment> \<open>TODO: optimize this annotation\<close> ;;
\<medium_right_bracket> .


end