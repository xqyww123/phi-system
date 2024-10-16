theory Linked_List
  imports Phi_Semantics.PhiSem_C
begin

abbreviation \<open>\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>

\<phi>reasoner_group Linked_Lst = (100,[0,9999]) \<open>derived reasoning rules of Linked_Lst\<close>

declare [[collect_reasoner_statistics Linked_Lst start,
         \<phi>LPR_collect_statistics derivation start,
         recording_timing_of_semantic_operation = true,
         \<phi>async_proof = false]]

\<phi>type_def Linked_Lst :: \<open>address \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T)   = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
      | \<open>(x#ls \<Ztypecolon> Linked_Lst addr TY T) = (ls \<Ztypecolon> Linked_Lst nxt TY T\<heavy_comma>
                                          (nxt, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> nxt: \<bbbP>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY, data: T \<rbrace>
                                         \<s>\<u>\<b>\<j> nxt. address_to_base addr )\<close>

     deriving Basic
          and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst addr TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = 0)) \<close>
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr TY T) (\<lambda>l. l = []) (\<lambda>_. addr = 0)\<close>
          and \<open>Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr TY) T U set (\<lambda>_. UNIV) list_all2\<close>
          and \<open>Functional_Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr TY) T U
                                                 set (\<lambda>x. UNIV) (\<lambda>f. list_all) (\<lambda>f P. map f)\<close>


declare [[auto_sledgehammer_params = "try0 = false"]]
   \<comment> \<open>For some reason I don't know, Sledgehammer fails silently (with throwing an Interrupt exception)
      when \<open>try0\<close> --- reconstructing proofs using classical tactics --- is enabled.
      Anyway, it is an engineering problem due to some bug in our system or Sledgehammer, so we don't
      count this line into our statistics in the paper.\<close>

declare [[collect_reasoner_statistics Linked_Lst stop,
          \<phi>LPR_collect_statistics derivation stop]]

(* ML \<open>PLPR_Statistics.reset_utilization_statistics_all ()\<close> *)

declare [[\<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics]]

proc init:
  input  Void
  output \<open>[] \<Ztypecolon> Linked_Lst 0 TY T\<close>
  is [routine]
\<medium_left_bracket>
  \<m>\<a>\<k>\<e>\<s>(0) \<open>Linked_Lst _ TY T\<close> \<semicolon>
  return \<open>0 \<Ztypecolon> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<close>
\<medium_right_bracket> .

proc is_empty:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  output \<open>l = [] \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  is [routine]
\<medium_left_bracket>
  addr = \<open>0 \<Ztypecolon> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<close>
\<medium_right_bracket> .




context
  fixes T :: \<open>(VAL, 'a) \<phi>\<close>                            \<comment> \<open>we provide a generic verification\<close>
    and TY :: TY                                      \<comment> \<open>semantic type\<close>
  assumes [\<phi>reason add]: \<open>Semantic_Type T TY\<close>    \<comment> \<open>specify the semantic type of T\<close>
begin

proc prepend_llist:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  requires [\<phi>reason]: \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>addr' \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma> v#l \<Ztypecolon> Linked_Lst addr' TY T \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc1 \<open>\<lbrace> nxt: \<bbbP>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY, data: T \<rbrace>\<close> \<semicolon>
  ret.nxt := addr \<semicolon>
  ret.data := v \<semicolon>
  \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst _ TY T\<close> \<semicolon>
  ret
\<medium_right_bracket> .


proc pop_llist:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma>
          l \<Ztypecolon> Linked_Lst addr TY T \<close>
  output \<open>addr' \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma>
          (if l = [] then [] else tl l) \<Ztypecolon> Linked_Lst addr' TY T
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
  is [routine]
\<medium_left_bracket>
  if (addr = \<open>0 \<Ztypecolon> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<close>) \<medium_left_bracket>
    return(addr)
  \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> \<semicolon>
   
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
  val ret \<leftarrow> addr.nxt \<semicolon>
  mfree (addr) \<semicolon>

  ret  
\<medium_right_bracket> .


proc nth_llist:
  input    \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
  is [recursive]
  \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon> \<comment> \<open>annotation 1: open abstraction\<close>
    if (i = \<open>0 \<Ztypecolon> \<nat>(\<i>\<n>\<t>)\<close>) \<medium_left_bracket>
        addr.data
    \<medium_right_bracket> \<medium_left_bracket>
        nth_llist (addr.nxt, i - 1)
    \<medium_right_bracket>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr TY T\<close> \<comment> \<open>annotation 2: close abstraction\<close>
  \<medium_right_bracket> .

thm nth_llist_def

proc hd_llist:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  premises \<open>l \<noteq> []\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma>
          hd l \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  nth_llist (addr, 0)
\<medium_right_bracket> .


proc update_nth_llist:
  input    \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := y] \<Ztypecolon> Linked_Lst addr TY T\<close>
  is [recursive]
  \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon> \<comment> \<open>annotation 1: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        addr.data := y
    \<medium_right_bracket> \<medium_left_bracket>
        update_nth_llist (addr.nxt, i - 1, y)
    \<medium_right_bracket> \<semicolon>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr TY T\<close>  \<comment> \<open>annotation 2: close abstraction\<close>
  \<medium_right_bracket> .

  thm update_nth_llist_def

end

proc length_of:
  input    \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  premises \<open>length l < 2 ^ LENGTH(\<i>\<n>\<t>)\<close>
  output   \<open>length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> l \<Ztypecolon> Linked_Lst addr TY T\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    return(0)
  \<medium_right_bracket> \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
    val ret \<leftarrow> length_of (addr.nxt) + 1 \<semicolon>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr TY T\<close> \<semicolon> (* 1: call the second constructor *)
    return (ret)
  \<medium_right_bracket>
\<medium_right_bracket> .
 
thm length_of_def

proc reverse_aux:
  input  \<open>addr' \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma>
          addr  \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma>
          l  \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma>
          l' \<Ztypecolon> Linked_Lst addr' TY T\<close>
  output \<open>addr'' \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma>
          rev l @ l' \<Ztypecolon> Linked_Lst addr'' TY T
          \<s>\<u>\<b>\<j> addr''. \<top>\<close>
  is [recursive]
  \<medium_left_bracket>
    if \<open>$addr = 0\<close> \<medium_left_bracket>
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(0)\<close>
      addr'
    \<medium_right_bracket> \<medium_left_bracket>
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
      addr.nxt \<rightarrow> val aa \<semicolon>
      addr.nxt := addr' \<semicolon>
      \<open>Linked_Lst addr' TY T\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>hd l # l' \<Ztypecolon> Linked_Lst addr TY T\<close> \<semicolon>
      reverse_aux (addr, aa) 
    \<medium_right_bracket>
  \<medium_right_bracket> .

proc reverse:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma>
          l \<Ztypecolon> Linked_Lst addr TY T\<close>
  output \<open>addr'' \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma>
          rev l \<Ztypecolon> Linked_Lst addr'' TY T
          \<s>\<u>\<b>\<j> addr''. \<top>\<close>
  \<medium_left_bracket>
    \<m>\<a>\<k>\<e>\<s>(0) \<open>Linked_Lst 0 TY T\<close>
    reverse_aux( \<open>0 \<Ztypecolon> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>, $addr )
              \<comment> \<open>^ \<phi>-type annotation here is not considered as a manual annotation because
                    it is exactly the C language type of the pointer literal.It can be
                    automatically generated by an C parser. 0 denotes the NULL pointer. \<close>
  \<medium_right_bracket> .


declare [[\<phi>LPR_collect_statistics program stop,
          collecting_subgoal_statistics=false,
          recording_timing_of_semantic_operation = false,
          \<phi>async_proof = true]]

text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm init_\<phi>app
thm is_empty_\<phi>app
thm prepend_llist_\<phi>app
thm pop_llist_\<phi>app
thm nth_llist_\<phi>app
thm hd_llist_\<phi>app
thm update_nth_llist_\<phi>app
thm length_of_\<phi>app
thm reverse_aux_\<phi>app
thm reverse_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm init_def
thm is_empty_def
thm prepend_llist_def
thm pop_llist_def
thm nth_llist_def
thm hd_llist_def
thm update_nth_llist_def
thm length_of_def
thm reverse_aux_def
thm reverse_def

ML \<open>report_utilization ["program"] [@{reasoner_group %all_derived_rules} ] \<close>

end