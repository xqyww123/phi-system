theory PhiEx_Rational
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

abbreviation \<open>\<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t>{k: \<a>\<i>\<n>\<t>, v: \<a>\<i>\<n>\<t>}\<close>

\<phi>reasoner_group \<phi>Rational = (100,[0,9999]) \<open>derived reasoning rules of Linked_Lst\<close>

declare [[recording_timing_of_semantic_operation = true,
         \<phi>LPR_collect_statistics derivation start,
         collect_reasoner_statistics \<phi>Rational start]]


\<phi>type_def \<phi>Rational :: \<open>(VAL, rat) \<phi>\<close> ("\<rat>")
  where \<open>x \<Ztypecolon> \<phi>Rational \<equiv> (n,d) \<Ztypecolon> \<lbrace> num: \<int>, den: \<int> \<rbrace> \<s>\<u>\<b>\<j> n d. of_int n / of_int d = x \<and> d \<noteq> 0\<close>
  deriving Basic
       and \<open>Object_Equiv \<rat> (=)\<close>


ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %\<phi>Rational})) "derivation"\<close>


declare [[collect_reasoner_statistics \<phi>Rational stop,
          \<phi>LPR_collect_statistics derivation stop,
          \<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics,
          \<phi>async_proof = false]]


proc rat_add:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 + q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val q2 \<leftarrow> $q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> den + $q2 \<tribullet> num * $q1 \<tribullet> den,
    den: $q1 \<tribullet> den * $q2 \<tribullet> den \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
\<medium_right_bracket> .


proc rat_sub:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 - q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val q2 \<leftarrow> $q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> den - $q2 \<tribullet> num * $q1 \<tribullet> den,
    den: $q1 \<tribullet> den * $q2 \<tribullet> den \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
\<medium_right_bracket> .


proc rat_mul:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 * q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val q2 \<leftarrow> $q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> num,
    den: $q1 \<tribullet> den * $q2 \<tribullet> den \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
\<medium_right_bracket> .


proc rat_div:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  premises \<open>q2 \<noteq> 0\<close>
  output \<open>q1 / q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val q2 \<leftarrow> $q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> den,
    den: $q1 \<tribullet> den * $q2 \<tribullet> num \<rbrace>
  \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
\<medium_right_bracket> .

declare [[\<phi>LPR_collect_statistics program stop,
          collecting_subgoal_statistics = false,
          \<phi>async_proof,
          recording_timing_of_semantic_operation = false]]


end