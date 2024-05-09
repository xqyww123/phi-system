theory PhiSem_Play_Ground
  imports
    PhiSem_CF_Breakable
    PhiSem_CF_Routine
    PhiSem_Variable
    PhiSem_Int_ArbiPrec
    PhiSem_Machine_Integer
    PhiSem_Aggregate_Tuple
    PhiSem_Aggregate_Named_Tuple
    PhiSem_Mem_Pointer
begin

\<phi>type_def \<phi>Rational :: \<open>(VAL, rat) \<phi>\<close> ("\<rat>")
  where \<open>x \<Ztypecolon> \<phi>Rational \<equiv> (n,d) \<Ztypecolon> \<lbrace> \<int>, \<int> \<rbrace> \<s>\<u>\<b>\<j> n d. of_int n / of_int d = x \<and> d \<noteq> 0\<close>
  deriving Basic
       and \<open>Object_Equiv \<rat> (=)\<close>

thm \<phi>Rational.intro_reasoning

lemma [\<phi>reason add]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> snd x \<noteq> 0
\<Longrightarrow> x \<Ztypecolon> \<lbrace> \<int>, \<int> \<rbrace> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> of_int (fst x) / of_int (snd x) \<Ztypecolon> \<rat>\<close>
  \<medium_left_bracket>
    \<open>of_int (fst x) / of_int (snd x) \<Ztypecolon> MAKE _ \<rat>\<close>
  \<medium_right_bracket> .

declare One_nat_def [simp del]

thm ":=_\<phi>app"

proc rat_add:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 + q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 to \<open>OPEN _ _\<close>
  val q2 \<leftarrow> $q2 to \<open>OPEN _ _\<close>
  val numerator \<leftarrow> $q1[0] * $q2[1] + $q2[0] * $q1[1]
  val denominator \<leftarrow> $q1[1] * $q2[1] ;
  \<lbrace> $numerator, $denominator \<rbrace>
\<medium_right_bracket> . 

thm rat_add_def


proc test_ptr:
  input \<open>(ptr, x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> Ptr (\<t>\<u>\<p> {\<t>\<u>\<p> {aint}, aint, aint}), \<int> \<rbrace>\<close>
  premises \<open>ptr \<noteq> 0\<close>
  output \<open>ptr \<tribullet> 2 \<Ztypecolon> \<v>\<a>\<l> Ptr aint\<close>
\<medium_left_bracket>
  val a, b \<leftarrow> (0, 0) \<semicolon>
  $1[$b]\<tribullet>$a[0] \<semicolon>
  $1[$b]\<tribullet>$a\<tribullet>0 \<semicolon>
  $1\<tribullet>$b\<tribullet>2
\<medium_right_bracket> .






no_notation Set.member ("(_/ : _)" [51, 51] 50)


proc test_ptr2:
  input \<open>(ptr, x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {a: \<p>\<t>\<r>, x: \<t>\<u>\<p> {\<b>\<o>\<o>\<l>, \<s>\<t>\<r>\<u>\<c>\<t> {q: \<a>\<i>\<n>\<t>, w: \<p>\<t>\<r>}}, y: \<a>\<i>\<n>\<t>}, \<int> \<rbrace>\<close>
  premises \<open>ptr \<noteq> 0\<close>
  output \<open>ptr \<tribullet> x \<tribullet> 1\<^sup>\<t>\<^sup>\<h> \<tribullet> w \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<p>\<t>\<r>\<close>
\<medium_left_bracket>
  val a, b \<leftarrow> (0, 1) \<semicolon>
  $1[$a].x[$b].w
\<medium_right_bracket> .

proc test_ptr3:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {a: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>addr \<tribullet> a \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<a>\<i>\<n>\<t>\<close>
\<medium_left_bracket>
  $addr.a
\<medium_right_bracket> .

proc test_agg2:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
    
  $v[0,1] \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  $v[0,0] \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  $v
\<medium_right_bracket> .

proc test_agg21:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
    
  $v\<tribullet>0\<tribullet>1 \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  $v\<tribullet>0\<tribullet>0 \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  $v
\<medium_right_bracket> .

proc test_agg22:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
     
  $v[0]\<tribullet>1 \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  $v[0]\<tribullet>0 \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  $v
\<medium_right_bracket> .

proc test_agg23:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
     
  v[0][1] \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  v[0][0] \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  v
\<medium_right_bracket> .

proc test_agg24:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
     
  v\<tribullet>0[1] \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  v\<tribullet>0[0] \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  v
\<medium_right_bracket> .

proc test_agg25:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,3), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
     
  v\<tribullet>0[1] \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  v\<tribullet>0[0] \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  v[0,1] := \<open>3 \<Ztypecolon> \<int>\<close>
\<medium_right_bracket> .

proc test_agg26:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,3), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
     
  $v\<tribullet>0[1] \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  $v\<tribullet>0[0] \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  $v \<tribullet> 0 \<tribullet> 1 := \<open>3 \<Ztypecolon> \<int>\<close>
\<medium_right_bracket> .

proc test_agg27:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket>  
  val v \<leftarrow> ( $1[0,1] := \<open>2 \<Ztypecolon> \<int>\<close> )\<semicolon>
  $v[0,0] := \<open>1 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

proc test_agg28:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<int>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> \<lbrace> \<nat>, \<int> \<rbrace>, \<int> \<rbrace>\<close>
\<medium_left_bracket>  
  ($1[0,1] := \<open>2 \<Ztypecolon> \<int>\<close>) [0,0] := \<open>1 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .


proc test_agg3:
  input \<open>((a,b), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> x: \<lbrace> m: \<int>, n: \<int> \<rbrace>, y: \<int> \<rbrace>\<close>
  output \<open>((1,2), x) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> x: \<lbrace> m: \<nat>, n: \<int> \<rbrace>, y: \<int> \<rbrace>\<close>
\<medium_left_bracket> 
  var v \<leftarrow> $1 \<semicolon>
  $v.x.n \<leftarrow> \<open>2 \<Ztypecolon> \<int>\<close> \<semicolon>
  $v.x.m \<leftarrow> \<open>1 \<Ztypecolon> \<nat>\<close> \<semicolon>
  $v
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

  
proc AAA:
  input  \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> x - 1 \<Ztypecolon> \<nat>\<close>
  is [routine]
  \<medium_left_bracket>
    ($x, $x) \<rightarrow> val y, var z \<semicolon> 
    if \<open>0 < $x\<close> \<open>$x - 1\<close> 0
  \<medium_right_bracket> .




proc
  input  \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  output \<open>\<v>\<a>\<l> x - 1 \<Ztypecolon> \<nat>\<close>
  is [routine]
  \<medium_left_bracket>
    if ( 0 < $x ) \<medium_left_bracket> $x - 1 \<medium_right_bracket> \<medium_left_bracket> 0 \<medium_right_bracket>
    (* the cartouche like \<open>0 < $x\<close> invokes a synthesis proce
ss \<leftarrow>
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

(*
syntax "_rec_fun_"
    ("\<r>\<e>\<c>\<u>\<r>\<s>\<i>\<v>\<e>- *)

declare [[\<phi>hide_techinicals, \<phi>display_value_internal_name=false]]

proc FIB2:
  input \<open>\<v>\<a>\<l> n \<Ztypecolon> \<nat>(8)\<close>
  output \<open>\<v>\<a>\<l> fib n \<Ztypecolon> \<nat>\<^sup>r(32)\<close>
  is [recursive n]
\<medium_left_bracket> 
  if \<open>$n \<le> 1\<close> \<medium_left_bracket>
    \<open>1 \<Ztypecolon> \<nat>\<^sup>r(32)\<close>
  \<medium_right_bracket> \<medium_left_bracket>
    FIB2 (\<open>$n - 1\<close>) + FIB2 (\<open>$n - 2\<close>)
  \<medium_right_bracket>
\<medium_right_bracket>.



thm FIB2_def


proc YYY:
  input \<open>\<v>\<a>\<l> a \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> b \<Ztypecolon> \<nat>\<heavy_comma> \<v>\<a>\<l> c \<Ztypecolon> \<int>\<close>
  output \<open>\<v>\<a>\<l> a + of_nat b + c \<Ztypecolon> \<int>\<close>
  is [routine]
  \<medium_left_bracket> \<open>$a + of_nat $b + $c\<close> \<medium_right_bracket>.

proc YYY2:
  input \<open>\<v>\<a>\<l> a \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> b \<Ztypecolon> \<nat>\<heavy_comma> \<v>\<a>\<l> c \<Ztypecolon> \<int>\<close>
  premises \<open>0 \<le> a \<and> 0 \<le> c\<close>
  output \<open>\<v>\<a>\<l> nat a + b + nat c \<Ztypecolon> \<nat>\<close>
  \<medium_left_bracket> \<open> nat $a + $b + nat $c \<close> \<medium_right_bracket>.

thm YYY2_def

proc XXXX:
  input \<open>\<v>\<a>\<l> a \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> b \<Ztypecolon> \<int>\<heavy_comma> \<v>\<a>\<l> c \<Ztypecolon> \<int>\<close>
  output \<open>\<v>\<a>\<l> a + b * c \<Ztypecolon> \<int>\<close>
  \<medium_left_bracket> $a + $b * $c \<medium_right_bracket> .

proc
  input \<open>\<v>\<a>\<l> a \<Ztypecolon> \<nat>\<^sup>r('b)\<heavy_comma> \<v>\<a>\<l> b \<Ztypecolon> \<nat>\<^sup>r('b)\<heavy_comma> \<v>\<a>\<l> c \<Ztypecolon> \<nat>\<^sup>r('b)\<close>
  output \<open>\<v>\<a>\<l> a + b + c \<Ztypecolon> \<nat>\<^sup>r('b)\<close>
  \<medium_left_bracket> \<open>$a + $b + $c\<close> \<medium_right_bracket>.

declare [[\<phi>hide_techinicals=false]]


declare [[\<phi>trace_reasoning = 2]]



proc
  input \<open>\<v>\<a>\<l> x \<Ztypecolon> \<nat>\<close>
  premises \<open>x < 10\<close>
  output \<open>\<v>\<a>\<l> 10 \<Ztypecolon> \<nat>\<close>
\<medium_left_bracket>
  $x \<rightarrow> var v (*x is an immutable value, and here we assign it to a variable v*)
  while \<open>x \<Ztypecolon> ?T \<s>\<u>\<b>\<j> x. Inv: (x \<le> 10) \<and> Guard: True \<and> End: (x = 10)\<close> (*annotation*)
  \<medium_left_bracket> \<open>True\<close> \<medium_right_bracket> (*guard*)
  \<medium_left_bracket> $v \<rightarrow> $v ;;
    \<open>$v = 10\<close> ;;
    if ( \<open>$v = 10\<close> ) \<medium_left_bracket> 
       break  
    \<medium_right_bracket> 
    \<medium_left_bracket> \<open>$v + 1\<close> \<rightarrow> v ;; continue \<medium_right_bracket>
    assert \<open>\<bottom>\<^sub>B\<^sub>I\<close>  
  \<medium_right_bracket> \<semicolon>
  $v
\<medium_right_bracket>.




(*
print_ast_translation \<open>
[(\<^syntax_const>\<open>_do_bind\<close>, fn _ => fn L => (@{print} L; hd L))]
\<close>
*)

thm op_var_scope_def
thm AAA_def

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