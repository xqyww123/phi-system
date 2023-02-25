theory PhiSem_Play_Ground
  imports
    PhiSem_CF_Breakable
    PhiSem_Int_ArbiPrec
    PhiSem_Variable
begin

no_notation inter (infixl "Int" 70)
        and union (infixl "Un" 65)
        and Nats  ("\<nat>")
        and Ints  ("\<int>")

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
  input  \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l x - 1 \<Ztypecolon> \<nat>\<close>
  \<medium_left_bracket>
    if \<medium_left_bracket> \<open>0 < $x\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>$x - 1\<close> \<medium_right_bracket>. \<medium_left_bracket> \<open>0\<close> \<medium_right_bracket>.
    (* the cartouche like \<open>0 < $x\<close> invokes a synthesis process
       to make a value satisfying that specification *)
  \<medium_right_bracket> using \<phi> by simp .

(*
setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put
           (SOME Generic_Variable_Access.to_value_no_clean))\<close> *)

(* declare [[\<phi>hide_techinicals=false]] *)

declare [[\<phi>hide_techinicals=false]]

ML \<open>Phi_Helper_Conv.aggregate_imps_obj (K Conv.all_conv) \<^context> \<^cprop>\<open>A \<Longrightarrow> B \<Longrightarrow> asd\<^bold>: (\<And>x. P x) \<Longrightarrow> D\<close>\<close>

(* declare [[\<phi>hide_brk_frame=false, \<phi>easoning]] *)

fun fib :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>fib 0 = 1\<close> | \<open>fib (Suc 0) = 1\<close> | \<open>fib n = fib (n-1) + fib (n-2)\<close>
    
proc FIB:
  input \<open>\<^bold>v\<^bold>a\<^bold>l n \<Ztypecolon> \<nat>\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l fib n \<Ztypecolon> \<nat>\<close>
  is [recursive n]
  \<medium_left_bracket> if \<open>$n \<le> 1\<close> \<medium_left_bracket> 1 \<medium_right_bracket>. \<medium_left_bracket>
      \<open>$n - 1\<close> FIB \<rightarrow> val a;;
      \<open>$n - 2\<close> FIB \<rightarrow> val b;;
      \<open>$a + $b\<close>
  \<medium_right_bracket>.
  \<medium_right_bracket> by (metis One_nat_def Value_of_def fib.elims fib.simps(2) le_Suc_eq le_zero_eq) .

thm FIB_def

proc
  input \<open>\<^bold>v\<^bold>a\<^bold>l a \<Ztypecolon> \<int>\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l b \<Ztypecolon> \<int>\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l c \<Ztypecolon> \<int>\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l a + b + c \<Ztypecolon> \<int>\<close>
  \<medium_left_bracket> \<open>$a + $b + $c\<close> \<medium_right_bracket>. .

proc
  input \<open>\<^bold>v\<^bold>a\<^bold>l a \<Ztypecolon> \<int>\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l b \<Ztypecolon> \<int>\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l c \<Ztypecolon> \<int>\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l a + b + c \<Ztypecolon> \<int>\<close>
  \<medium_left_bracket> $a $b + $c + \<medium_right_bracket>. .


proc
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>\<close>
  premises \<open>x < 10\<close>
  output \<open>\<^bold>v\<^bold>a\<^bold>l 10 \<Ztypecolon> \<nat>\<close>
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
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>\<close>
  premises A: \<open>x < 10\<close>  
  output \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>\<close>
  is [recursive x]
  is [recursive x]
  is [recursive xa]
  \<medium_left_bracket> premises A and XXX and YYY and ZZZ
  thm ZZZ
  ;; $xaa ZZZ XXX YYY
 \<medium_right_bracket> .. .
    
proc YYY:
  input \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l y \<Ztypecolon> \<nat>\<close>
  premises A: \<open>x < y\<close>    
  output \<open>\<^bold>v\<^bold>a\<^bold>l x \<Ztypecolon> \<nat>\<heavy_comma> 20 \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l \<nat>\<close>
  is [recursive x y]
  is [recursive x y]
  is [recursive xa ya]
  \<medium_left_bracket> premises A and AAA and BBB and CCC
    $xaa $yaa CCC AAA BBB \<medium_right_bracket>. .

thm YYY_def

end