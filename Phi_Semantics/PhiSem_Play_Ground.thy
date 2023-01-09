theory PhiSem_Play_Ground
  imports PhiSem_Machine_Integer_Lib
    PhiSem_Variable_Lib
    PhiSem_Basic_Control_Flow
begin

(*Example*)


proc AA:
  argument \<open>\<^bold>v\<^bold>a\<^bold>l 1 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 2 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 3 \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l 6 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 4 \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l 2 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket> + + 4 2 1 - 1 + 30000 * 30000 /  \<medium_right_bracket>. .

thm op_const_int_\<phi>app
thm AA_\<phi>compilation

(*
int XX(int x) { if 0 < x then x - 1 else 0 }
*)
proc
  argument \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l x - 1 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket> \<rightarrow> varx
  ;; (*assign the value x to a variable named varx*)
     (* command `;;` leads a statement, or ends the previous statement. *)
    if \<medium_left_bracket> \<open>0 < $varx\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>$varx - 1\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>0::nat\<close> \<medium_right_bracket>.
    (* the cartouche like \<open>0 < $varx\<close> invokes a synthesis process
       to make that value automatically *)
  \<medium_right_bracket> using \<phi> by simp .


proc
  premises \<open>x < 10\<close>
  argument \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l 10 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket> \<open>\<a>\<r>\<g>0\<close> \<rightarrow> v ;;
    while \<open>xxx \<Ztypecolon> ?X \<^bold>s\<^bold>u\<^bold>b\<^bold>j xxx. Inv: (xxx \<le> 10) \<and> Guard: xxx < 10\<close> (*specification*)
    \<medium_left_bracket> \<open>$v < 10\<close> \<medium_right_bracket>. (*guard*)
    \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v \<medium_right_bracket>. (*loop body*)
    $v
  \<medium_right_bracket>. .

  
end