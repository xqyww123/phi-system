theory Rational_Arith
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

abbreviation \<open>\<r>\<a>\<t>\<i>\<o>\<n>\<a>\<l> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t>{num: \<a>\<i>\<n>\<t>, den: \<a>\<i>\<n>\<t>}\<close>

\<phi>reasoner_group \<phi>Rational = (100,[0,9999]) \<open>derived reasoning rules of Linked_Lst\<close>

declare [[recording_timing_of_semantic_operation = true,
         \<phi>LPR_collect_statistics derivation start,
         collect_reasoner_statistics \<phi>Rational start]]
 
  \<phi>type_def \<phi>Rational :: \<open>(VAL, rat) \<phi>\<close> ("\<rat>")
    where \<open>x \<Ztypecolon> \<phi>Rational \<equiv> (n,d) \<Ztypecolon> \<lbrace> num: \<int>, den: \<int> \<rbrace>
                       \<s>\<u>\<b>\<j> n d. of_int n / of_int d = x \<and> d \<noteq> 0\<close>
    deriving Basic
         and \<open>Object_Equiv \<rat> (=)\<close>
         and \<open>Abstract_Domain\<^sub>L \<rat> (\<lambda>_. True)\<close>
         and \<open>Abstract_Domain \<rat> (\<lambda>_. True)\<close>
         and Semantic_Type
         and Inhabited

ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %\<phi>Rational})) "derivation"\<close>


declare [[collect_reasoner_statistics \<phi>Rational stop,
          \<phi>LPR_collect_statistics derivation stop]]

(* ML \<open>PLPR_Statistics.reset_utilization_statistics_all ()\<close> *)

declare [[\<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics,
          \<phi>async_proof = false]]



  proc rat_add:
    input \<open>\<v>\<a>\<l> q1 \<Ztypecolon> \<rat> \<heavy_comma> \<v>\<a>\<l> q2 \<Ztypecolon> \<rat>\<close>
    output \<open>\<v>\<a>\<l> q1 + q2 \<Ztypecolon> \<rat>\<close>
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
    input \<open>\<v>\<a>\<l> q1 \<Ztypecolon> \<rat> \<heavy_comma> \<v>\<a>\<l> q2 \<Ztypecolon> \<rat>\<close>
    premises \<open>q2 \<noteq> 0\<close>
    output \<open>\<v>\<a>\<l> q1 / q2 \<Ztypecolon> \<rat>\<close>
  \<medium_left_bracket>  
    val q1 \<leftarrow> (q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
    val q2 \<leftarrow> (q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
    \<lbrace> num: q1.num * q2.den,
      den: q1.den * q2.num \<rbrace>
    \<m>\<a>\<k>\<e>\<s> \<open>\<rat>\<close>
  \<medium_right_bracket> .


proc rat_lt [\<phi>overload <]:
  input \<open>\<v>\<a>\<l> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<v>\<a>\<l> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 < q2 \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  val q1 \<leftarrow> (q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val q2 \<leftarrow> (q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val a \<leftarrow> q1.num * q2.den \<semicolon>
  val b \<leftarrow> q1.den * q2.num \<semicolon>
  sel (q1.den > 0 \<oplus> q2.den > 0, a > b, a < b)
\<medium_right_bracket> .

proc rat_le [\<phi>overload \<le>]:
  input \<open>\<v>\<a>\<l> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<v>\<a>\<l> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 \<le> q2 \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  val q1 \<leftarrow> (q1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val q2 \<leftarrow> (q2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n>) \<semicolon>
  val a \<leftarrow> q1.num * q2.den \<semicolon>
  val b \<leftarrow> q1.den * q2.num \<semicolon>
  sel (q1.den > 0 \<oplus> q2.den > 0, a \<ge> b, a \<le> b)
\<medium_right_bracket>  .

proc rat_gt [\<phi>overload >]:
  input \<open>\<v>\<a>\<l> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<v>\<a>\<l> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 > q2 \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  q2 < q1
\<medium_right_bracket> .

proc rat_ge [\<phi>overload >]:
  input \<open>\<v>\<a>\<l> q1 \<Ztypecolon> \<rat>\<heavy_comma> \<v>\<a>\<l> q2 \<Ztypecolon> \<rat>\<close>
  output \<open>q1 \<ge> q2 \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  q2 \<le> q1
\<medium_right_bracket> .


declare [[\<phi>LPR_collect_statistics program stop,
          collecting_subgoal_statistics = false,
          \<phi>async_proof,
          recording_timing_of_semantic_operation = false]]

ML \<open>fun filter_out (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>to\<close>, _) $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>OPEN\<close>, _) $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>MAKE\<close>, _) $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = filter_out X
    | filter_out (Abs (_, _, X)) = filter_out X
    | filter_out (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = filter_out X
    | filter_out (Const(\<^const_name>\<open>Identifier_of\<close>, _) $ _ $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>Semantic_Type\<close>, _) $ _ $ _) = true
    | filter_out (Const(\<^const_name>\<open>Is_Aggregate\<close>, _) $ _) = true
    | filter_out _ = false

  fun report_utilization statistic_groups reasoner_groups =
  let open Pretty
      val statistics = Phi_Reasoner.utilization_of_groups_in_all_theories
          (Context.Theory \<^theory>) (map (the o snd) reasoner_groups) statistic_groups
        |> filter (fn (th, i) => i > 0 andalso not (filter_out (Thm.concl_of th)))
   in (length statistics, Integer.sum (map snd statistics))
  end
\<close>

ML \<open>report_utilization ["program"] [@{reasoner_group %all_derived_rules} ] \<close>

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