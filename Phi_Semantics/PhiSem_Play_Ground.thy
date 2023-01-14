theory PhiSem_Play_Ground
  imports PhiSem_Machine_Integer
    PhiSem_Variable
    PhiSem_Basic_Control_Flow
begin

(*
proc
  assumes [\<phi>reason]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  assumes [\<phi>reason]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY'\<close>
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> T\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> U\<close>
  output \<open>Any\<close>
  \<medium_left_bracket> $x \<rightarrow> var z
  ;; $y \<rightarrow> z
 *)
(*
int XX(int x) { if 0 < x then x - 1 else 0 }
*)

proc
  input  \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l x - 1 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket>
    if \<medium_left_bracket> \<open>0 < $x\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>$x - 1\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>0 \<Ztypecolon> \<nat>[32]\<close> \<medium_right_bracket>.
    (* the cartouche like \<open>0 < $x\<close> invokes a synthesis process
       to make a value satisfying that specification *)
  \<medium_right_bracket> using \<phi> by simp .

(*
setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put
            (SOME Generic_Variable_Access.to_value_no_clean))\<close> *)


proc
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  premises \<open>x < 10\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l 10 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket>
    $x \<rightarrow> var v (*x is an immutable value, and here we assign it to a variable v*)
    while \<open>x \<Ztypecolon> ?T \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: (x \<le> 10) \<and> Guard: x < 10\<close> (*annotation*)
    \<medium_left_bracket> \<open>$v < 10\<close> \<medium_right_bracket>. (*guard*)
    \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v \<medium_right_bracket>. (*loop body*)
    $v
  \<medium_right_bracket>. .


end