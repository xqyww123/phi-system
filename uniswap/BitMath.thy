theory BitMath
  imports "../Phi_Solidity" "HOL-Library.Log_Nat"
begin

term log
term floorlog
value \<open>floorlog 2 4 - 1\<close>

abbreviation msb where \<open>msb x \<equiv> floorlog 2 x - 1\<close>

context solidity begin

proc BitMath_'_mostSignificantBit:
  argument \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[256]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l msb x \<Ztypecolon> \<nat>[8]\<close>
  \<medium_left_bracket> \<rightarrow> v
  ;; \<open>0 \<Ztypecolon> \<nat>[8]\<close> \<rightarrow> r
  ;; \<open>$v > 0\<close> op_const_str[where s=\<open>''''\<close>] require
  ;; if \<open>$v \<ge> 0x100000000000000000000000000000000\<close> \<medium_left_bracket>
  ;;   \<open>$v := $v LSHR (128 <bits> 8)\<close> drop
  ;;   \<open>$r := $r + 128\<close> drop
  \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
  ;; 
(* TODO: relax *)
  
  term \<open>$v := 1\<close>
  ;; \<open>($v := 1) \<Ztypecolon> \<nat>[256]\<close>
  
  thm \<phi>
  thm op_const_str_\<phi>app[where s=\<open>''''\<close>]

end

end