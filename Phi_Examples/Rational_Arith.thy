theory Rational_Arith
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

abbreviation \<open>\<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l> \<equiv> \<struct>{num: \<aint>, den: \<aint>}\<close>

  
\<phi>type_def \<phi>Rational ("\<rat>")
  where \<open>x \<Ztypecolon> \<phi>Rational \<equiv> (n,d) \<Ztypecolon> \<lbrace> num: \<int>, den: \<int> \<rbrace> \<subj> n d. of_int n / of_int d = x \<and> d \<noteq> 0\<close>
  deriving Basic
       and \<open>Object_Equiv \<rat> (=)\<close>
       and \<open>Abstract_Domain\<^sub>L \<rat> (\<lambda>_. True)\<close>
       and \<open>Abstract_Domain \<rat> (\<lambda>_. True)\<close>
       and Semantic_Type
       and Inhabited

  proc rat_add:
    input \<open>\<val> q1 \<Ztypecolon> \<rat> \<heavy_comma> \<val> q2 \<Ztypecolon> \<rat>\<close>
    output \<open>\<val> q1 + q2 \<Ztypecolon> \<rat>\<close>
  \<medium_left_bracket>  
    val q1 = (q1 transforms_to \<open'>) \<semicolon>
    val q2 = (q2 transforms_to \<open'>) \<semicolon>
    \<lbrace> num: q1.num * q2.den + q2.num * q1.den,
      den: q1.den * q2.den \<rbrace>
    \<makes> \<open>\<rat>\<close>
  \<medium_right_bracket> .


  proc rat_sub:
    input \<open>q1 \<Ztypecolon> \<val> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<val> \<rat>\<close>
    output \<open>q1 - q2 \<Ztypecolon> \<val> \<rat>\<close>
  \<medium_left_bracket>
    val q1 = (q1 transforms_to \<open'>) \<semicolon>
    val q2 = (q2 transforms_to \<open'>) \<semicolon>
    \<lbrace> num: q1.num * q2.den - q2.num * q1.den,
      den: q1.den * q2.den \<rbrace>
    \<makes> \<open>\<rat>\<close>
  \<medium_right_bracket> .
  
  
  proc rat_mul:
    input \<open>q1 \<Ztypecolon> \<val> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<val> \<rat>\<close>
    output \<open>q1 * q2 \<Ztypecolon> \<val> \<rat>\<close>
  \<medium_left_bracket>  
    val q1 = (q1 transforms_to \<open'>) \<semicolon>
    val q2 = (q2 transforms_to \<open'>) \<semicolon>
    \<lbrace> num: q1.num * q2.num,
      den: q1.den * q2.den \<rbrace>
    \<makes> \<open>\<rat>\<close>
  \<medium_right_bracket> .
  
  
  proc rat_div:
    input \<open>\<val> q1 \<Ztypecolon> \<rat> \<heavy_comma> \<val> q2 \<Ztypecolon> \<rat>\<close>
    premises \<open>q2 \<noteq> 0\<close>
    output \<open>\<val> q1 / q2 \<Ztypecolon> \<rat>\<close>
  \<medium_left_bracket>  
    val q1 \<leftarrow> (q1 transforms_to \<open'>) \<semicolon>
    val q2 \<leftarrow> (q2 transforms_to \<open'>) \<semicolon>
    \<lbrace> num: q1.num * q2.den,
      den: q1.den * q2.num \<rbrace>
    \<makes> \<open>\<rat>\<close>
  \<medium_right_bracket> .


proc rat_lt [\<phi>overload <]:
  input \<open>\<val> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<val> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 < q2 \<Ztypecolon> \<val> \<bool>\<close>
\<medium_left_bracket>
  val q1 \<leftarrow> (q1 transforms_to \<open'>) \<semicolon>
  val q2 \<leftarrow> (q2 transforms_to \<open'>) \<semicolon>
  val a \<leftarrow> q1.num * q2.den \<semicolon>
  val b \<leftarrow> q1.den * q2.num \<semicolon>
  sel (q1.den > 0 \<oplus> q2.den > 0, a > b, a < b)
\<medium_right_bracket> .

proc rat_le [\<phi>overload \<le>]:
  input \<open>\<val> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<val> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 \<le> q2 \<Ztypecolon> \<val> \<bool>\<close>
\<medium_left_bracket>
  val q1 \<leftarrow> (q1 transforms_to \<open'>) \<semicolon>
  val q2 \<leftarrow> (q2 transforms_to \<open'>) \<semicolon>
  val a \<leftarrow> q1.num * q2.den \<semicolon>
  val b \<leftarrow> q1.den * q2.num \<semicolon>
  sel (q1.den > 0 \<oplus> q2.den > 0, a \<ge> b, a \<le> b)
\<medium_right_bracket>  .

proc rat_gt [\<phi>overload >]:
  input \<open>\<val> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<val> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 > q2 \<Ztypecolon> \<val> \<bool>\<close>
\<medium_left_bracket>
  q2 < q1
\<medium_right_bracket> .

proc rat_ge [\<phi>overload >]:
  input \<open>\<val> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<val> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 \<ge> q2 \<Ztypecolon> \<val> \<bool>\<close>
\<medium_left_bracket>
  q2 \<le> q1
\<medium_right_bracket> .


text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm rat_add_\<phi>app
thm rat_sub_\<phi>app
thm rat_mul_\<phi>app
thm rat_div_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm rat_add_def
thm rat_sub_def
thm rat_mul_def
thm rat_div_def

end