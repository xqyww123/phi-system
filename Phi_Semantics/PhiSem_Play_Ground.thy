theory PhiSem_Play_Ground
  imports
    PhiSem_CF_Breakable
    PhiSem_CF_Routine
    PhiSem_Variable
    PhiSem_Int_ArbiPrec
    PhiSem_Machine_Integer
    PhiSem_Aggregate_Tuple
    PhiSem_Aggregate_Named_Tuple
begin


\<phi>type_def \<phi>Rational :: \<open>(VAL, rat) \<phi>\<close> ("\<rat>")
  where [\<phi>defs]: \<open>\<phi>Rational x = ((n,d) \<Ztypecolon> \<lbrace> \<int>, \<int> \<rbrace> \<s>\<u>\<b>\<j> n d. of_int n / of_int d = x \<and> d \<noteq> 0)\<close>

lemma [\<phi>reason]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> of_int n / of_int d = x \<and> d \<noteq> 0
\<Longrightarrow> (n,d) \<Ztypecolon> \<lbrace> \<int>, \<int> \<rbrace> \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> \<rat>\<close>
  \<medium_left_bracket> construct\<phi> \<open>x \<Ztypecolon> \<rat>\<close> \<medium_right_bracket> .


proc rat_add:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 + q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>
  $q1 destruct\<phi> _ \<rightarrow> val q1 \<comment> \<open>The reasoner will not open an abstraction by default\<close>
  $q2 destruct\<phi> _ \<rightarrow> val q2
  $q1[0] * $q2[1] + $q2[0] * $q1[1] \<rightarrow> val numerator
  $q1[1] * $q2[1] \<rightarrow> val denominator
  \<lbrace> $numerator, $denominator \<rbrace>
\<medium_right_bracket> .


(*
proc
  assumes [\<phi>reason]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  assumes [\<phi>reason]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY'\<close>
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> T\<heavy_comma> \<v>\<a>\<l> y \<Ztypecolon> U\<close>
  output \<open>Any\<close>
  \<medium_left_bracket> $x \<rightarrow> var z
  ;; $y \<rightarrow> z
 *)
(*
int XX(int x) { if 0 < x then x - 1 else 0 }
*)

proc
  input  \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> x - 1 \<Ztypecolon> \<nat>\<close>
  is [routine]
  \<medium_left_bracket>
    if ( \<open>0 < $x\<close> ) \<medium_left_bracket> \<open>$x - 1\<close> \<medium_right_bracket> \<medium_left_bracket> \<open>0\<close> \<medium_right_bracket>
    (* the cartouche like \<open>0 < $x\<close> invokes a synthesis proce
ss
       to make a value satisfying that specification *)
  \<medium_right_bracket> .

(*
setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put
           (SOME Generic_Variable_Access.store_value_no_clean))\<close> *)

(* declare [[\<phi>hide_techinicals=false]] *)

declare [[\<phi>hide_techinicals=false]]

(* declare [[\<phi>hide_brk_frame=false, \<phi>easoning]] *)

fun fib :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>fib 0 = 1\<close> | \<open>fib (Suc 0) = 1\<close> | \<open>fib n = fib (n-1) + fib (n-2)\<close>

thm fib.induct
thm fib.simps
thm fib.elims

proc FIB:
  input \<open>\<v>\<a>\<l> n \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> fib n \<Ztypecolon> \<nat>\<close>
  is [recursive n]
  is [routine]
\<medium_left_bracket>
  if \<open>$n \<le> 1\<close> \<medium_left_bracket> 1 \<medium_right_bracket> \<medium_left_bracket>
    FIB (\<open>$n - 1\<close>) + FIB (\<open>$n - 2\<close>)
  \<medium_right_bracket>
\<medium_right_bracket>.

proc FIB2:
  input \<open>\<v>\<a>\<l> n \<Ztypecolon> \<nat>(8)\<close>
  output \<open>\<v>\<a>\<l> fib n \<Ztypecolon> \<nat>\<^sup>r(32)\<close>
  is [recursive n]
\<medium_left_bracket>
  if \<open>$n \<le> 1\<close>
  \<medium_left_bracket> \<open>1 \<Ztypecolon> \<nat>\<^sup>r(32)\<close> \<medium_right_bracket>
  \<medium_left_bracket> FIB2 (\<open>$n - 1\<close>) + FIB2 (\<open>$n - 2\<close>) \<medium_right_bracket>
\<medium_right_bracket>.

thm FIB2_def

proc YYY:
  input \<open>\<v>\<a>\<l> a \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> b \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> c \<Ztypecolon> \<int>\<close>
  output \<open>\<v>\<a>\<l> a + b + c \<Ztypecolon> \<int>\<close>
  is [routine]
  \<medium_left_bracket>  \<open>$a + $b + $c\<close> \<medium_right_bracket>.

thm YYY_def


proc XXXX:
  input \<open>\<v>\<a>\<l> a \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> b \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> c \<Ztypecolon> \<int>\<close>
  output \<open>\<v>\<a>\<l> a + b * c \<Ztypecolon> \<int>\<close>
  is [routine_basic]
  \<medium_left_bracket> $a + $b * $c \<medium_right_bracket> .

proc
  input \<open>\<v>\<a>\<l> a \<Ztypecolon> \<nat>\<^sup>r('b)\<heavy_comma> \<v>\<a>\<l> b \<Ztypecolon> \<nat>\<^sup>r('b)\<heavy_comma> \<v>\<a>\<l> c \<Ztypecolon> \<nat>\<^sup>r('b)\<close>
  output \<open>\<v>\<a>\<l> a + b + c \<Ztypecolon> \<nat>\<^sup>r('b)\<close>
  \<medium_left_bracket> \<open>$a + $b + $c\<close> \<medium_right_bracket>.

declare [[\<phi>hide_techinicals=true]]

proc
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  premises \<open>x < 10\<close>
  output \<open>\<v>\<a>\<l> 10 \<Ztypecolon> \<nat>\<close>
  is [routine]
\<medium_left_bracket>
  $x \<rightarrow> var v (*x is an immutable value, and here we assign it to a variable v*)
  while \<open>x \<Ztypecolon> ?T \<s>\<u>\<b>\<j> x. Inv: (x \<le> 10) \<and> Guard: True \<and> End: (x = 10)\<close> (*annotation*)
  \<medium_left_bracket> \<open>True\<close> \<medium_right_bracket> (*guard*)
  \<medium_left_bracket>
    if \<open>$v = 10\<close> \<medium_left_bracket> break \<medium_right_bracket> \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v;; continue \<medium_right_bracket>
    assert \<bottom>
  \<medium_right_bracket> (*loop body*)
  $v
\<medium_right_bracket>.
  
proc
  input \<open>\<v>\<a>\<l> b \<Ztypecolon> \<bool>\<close>
  output \<open>(if b then 32 else 24) \<Ztypecolon> \<v>\<a>\<l> (if b then \<nat>(32) else \<nat>(16))\<close>
  \<medium_left_bracket>
    if $b \<medium_left_bracket> \<open>32 \<Ztypecolon> \<nat>(32)\<close> \<medium_right_bracket> \<medium_left_bracket> \<open>24 \<Ztypecolon> \<nat>(16)\<close> \<medium_right_bracket>
  \<medium_right_bracket> .

(*
proc XXX:
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  premises A: \<open>x < 10\<close>
  output \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  is [recursive x]
  is [recursive x]
  is [recursive xa]
  \<medium_left_bracket> premises A and XXX and YYY and ZZZ
  thm ZZZ
  ;; $xaa ZZZ XXX YYY
 \<medium_right_bracket> .. .


proc YYY2:
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<heavy_comma> \<v>\<a>\<l> y \<Ztypecolon> \<nat>\<close>
  premises A: \<open>x < y\<close>
  output \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<heavy_comma> 20 \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  is [recursive x y]
  is [recursive x y]
  is [recursive xa ya]
  is [routine]
  \<medium_left_bracket> premises A and AAA and BBB and CCC
    $xaa $yaa CCC AAA BBB \<medium_right_bracket>. .

thm YYY2_def
*)

end