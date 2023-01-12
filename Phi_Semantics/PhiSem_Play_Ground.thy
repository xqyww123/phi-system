theory PhiSem_Play_Ground
  imports PhiSem_Machine_Integer
    PhiSem_Variable
    PhiSem_Basic_Control_Flow
begin

(*Example*)

(*
int XX(int x) { if 0 < x then x - 1 else 0 }
*)
proc
  argument \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l x - 1 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket>
    if \<medium_left_bracket> \<open>0 < $x\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>$x - 1\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>0 \<Ztypecolon> \<nat>[32]\<close> \<medium_right_bracket>.
    (* the cartouche like \<open>0 < $x\<close> invokes a synthesis process
       to make a value satisfying that specification *)
  \<medium_right_bracket> using \<phi> by simp .

proc
  premises \<open>x < 10\<close>
  argument \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  return \<open>\<^bold>v\<^bold>a\<^bold>l 10 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket> $x \<rightarrow> var v (*x is an immutable value, and here we assign it to a variable v*)
    while \<open>x \<Ztypecolon> ?T \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: (x \<le> 10) \<and> Guard: x < 10\<close> (*annotation*)
    \<medium_left_bracket> \<open>$v < 10\<close> \<medium_right_bracket>. (*guard*)
    \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v \<medium_right_bracket>. (*loop body*)
    $v
  \<medium_right_bracket>. .


end