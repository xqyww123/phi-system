theory Rational_Arith
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

abbreviation \<open>\<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t>{k: \<a>\<i>\<n>\<t>, v: \<a>\<i>\<n>\<t>}\<close>

\<phi>type_def \<phi>Rational :: \<open>(VAL, rat) \<phi>\<close> ("\<rat>")
  where \<open>x \<Ztypecolon> \<phi>Rational \<equiv> (n,d) \<Ztypecolon> \<lbrace> num: \<int>, den: \<int> \<rbrace> \<s>\<u>\<b>\<j> n d. of_int n / of_int d = x \<and> d \<noteq> 0\<close>
  deriving Basic
       and \<open>Object_Equiv \<rat> (=)\<close>
       and \<open>Abstract_Domain\<^sub>L \<rat> (\<lambda>_. True)\<close>
       and \<open>Abstract_Domain \<rat> (\<lambda>_. True)\<close>


proc rat_add:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 + q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 = (q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val q2 = (q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  \<lbrace> num: q1.num * q2.den + q2.num * q1.den,
    den: q1.den * q2.den \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
\<medium_right_bracket> .


proc rat_sub:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 - q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 = (q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val q2 = (q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  \<lbrace> num: q1.num * q2.den - q2.num * q1.den,
    den: q1.den * q2.den \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
\<medium_right_bracket> .


proc rat_mul:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 * q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 = (q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val q2 = (q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  \<lbrace> num: q1.num * q2.num,
    den: q1.den * q2.den \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
\<medium_right_bracket> .


proc rat_div:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  premises \<open>q2 \<noteq> 0\<close>
  output \<open>q1 / q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> (q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val q2 \<leftarrow> (q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  \<lbrace> num: q1.num * q2.den,
    den: q1.den * q2.num \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
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