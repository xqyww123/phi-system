theory PhiSem_Play_Ground
  imports
    PhiSem_CF_Breakable
    PhiSem_Machine_Integer
    PhiSem_Variable
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

(* declare [[\<phi>hide_techinicals=false]] *)

(* declare [[\<phi>hide_brk_frame=false, \<phi>trace_reasoning]] *)
   
proc
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  premises \<open>x < 10\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l 10 \<Ztypecolon> \<nat>[32]\<close>
  \<medium_left_bracket> $x \<rightarrow> var v (*x is an immutable value, and here we assign it to a variable v*)
    while \<open>x \<Ztypecolon> ?T \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. Inv: (x \<le> 10) \<and> Guard: True \<and> End: (x = 10)\<close> (*annotation*)
    \<medium_left_bracket> \<open>True\<close> \<medium_right_bracket>. (*guard*)
    \<medium_left_bracket>
      if \<open>$v = 10\<close> \<medium_left_bracket> break \<medium_right_bracket>. \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v;; continue \<medium_right_bracket>.
      assert \<bottom>
    \<medium_right_bracket>. (*loop body*)
    $v
  \<medium_right_bracket>. .
 
proc XXX:
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  premises A: \<open>x < 10\<close>  
  output \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<close>
  is [recursive x]
  \<medium_left_bracket> $x XXX \<medium_right_bracket>. .

thm XXX_def

proc XXX:
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>[32]\<close>
  premises A: \<open>x < y\<close>    
  output \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>[32]\<heavy_comma> 20 \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<nat>[32]\<close>
  is [recursive x y]
  \<medium_left_bracket> $x $y XXX \<medium_right_bracket>. .

thm XXX_def

ML \<open>@{term \<open>A\<^bold>: X\<close>}\<close>

notepad
begin

  fix x :: nat
  ML_val

  assume A: \<open>(\<And>x::((nat \<times> int \<times> bool) <named> ('name_a \<times> 'name_b \<times> 'name_c)).
    P (case_named (fst) x) \<and> Q (case_named (fst o snd) x) \<and> Z (case_named (snd o snd) x))\<close>

assume B: \<open>(\<And>x::(((nat \<times> int \<times> bool) <named> ('name_a \<times> 'name_b \<times> 'name_c)) \<Rightarrow> bool). x aaa)\<close>

  term case_named
  
  thm B
  ML_val \<open>QuantExpansion.named_predicate_expansion @{context} @{thm B}\<close>

  assume C: \<open>PROP Pure.prop (AAA \<Longrightarrow> (\<And>x. P x))\<close>
  ML_val \<open>@{thm C[unfolded Pure.prop_def]} COMP @{thm meta_spec}\<close>

end
thm meta_spec
end