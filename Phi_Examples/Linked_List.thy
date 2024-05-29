theory Linked_List
  imports Phi_Semantics.PhiSem_C
begin

declare [[auto_sledgehammer_params = "try0 = false"]]
declare [[\<phi>trace_reasoning = 1]]
declare [[\<phi>infer_requirements]]

abbreviation \<open>\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>

\<phi>type_def Linked_Lst :: \<open>address \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr T)   = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
      | \<open>(x#ls \<Ztypecolon> Linked_Lst addr T) = (ls \<Ztypecolon> Linked_Lst nxt T\<heavy_comma>
                                      (nxt, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> nxt: \<bbbP>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> (\<t>\<y>\<p>\<e>\<o>\<f> T), data: T \<rbrace>
                                      \<s>\<u>\<b>\<j> nxt. address_to_base addr \<and>
                                               \<t>\<y>\<p>\<e>\<o>\<f> addr = \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> (\<t>\<y>\<p>\<e>\<o>\<f> T) )\<close>

     deriving Basic
          and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst addr T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = 0)) \<close>
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr T) (\<lambda>l. l = []) (\<lambda>_. addr = 0)\<close>
          and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<t>\<y>\<p>\<e>\<o>\<f> T = \<t>\<y>\<p>\<e>\<o>\<f> U
            \<Longrightarrow> Transformation_Functor (Linked_Lst addr) (Linked_Lst addr) T U set (\<lambda>_. UNIV) list_all2\<close>
          and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<t>\<y>\<p>\<e>\<o>\<f> T = \<t>\<y>\<p>\<e>\<o>\<f> U
            \<Longrightarrow> Functional_Transformation_Functor (Linked_Lst addr) (Linked_Lst addr) T U
                                                   set (\<lambda>x. UNIV) (\<lambda>f. list_all) (\<lambda>f P. map f)\<close>
          and Pointer_Of

 
proc init:
  input  Void
  output \<open>[] \<Ztypecolon> \<r>\<e>\<f> Linked_Lst 0 T\<close>
\<medium_left_bracket>
  \<m>\<a>\<k>\<e>\<s>(0) \<open>Linked_Lst _ T\<close> \<semicolon>
  NULL
\<medium_right_bracket> .

proc is_empty:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<close>
  output \<open>l = [] \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> l \<Ztypecolon> Linked_Lst addr T\<close>
  is [routine]
\<medium_left_bracket>
  addr = NULL
\<medium_right_bracket> .

  
proc prepend_llist:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T z\<close>
  output \<open>v#l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr' T \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc1 \<open>\<lbrace> nxt: \<bbbP>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> (\<t>\<y>\<p>\<e>\<o>\<f> T), data: T \<rbrace>\<close> \<semicolon>
  ret.nxt := addr \<semicolon> 
  ret.data := v \<semicolon>
  \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst _ T\<close> \<semicolon>
  ret
\<medium_right_bracket> .


proc pop_llist:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T \<close>
  output \<open>(if l = [] then [] else tl l) \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr' T
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
  is [routine]
\<medium_left_bracket>
  if (addr = NULL) \<medium_left_bracket>
    return(addr)
  \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> \<semicolon>
   
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
  val ret \<leftarrow> addr.nxt \<semicolon>
  mfree (addr) \<semicolon>

  ret  
\<medium_right_bracket> .



proc nth_llist:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
  premises \<open>i < length l\<close>
  output   \<open>l \<Ztypecolon> Linked_Lst addr T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
  is [recursive]
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
  if (i = 0) \<medium_left_bracket>
      addr.data
  \<medium_right_bracket> \<medium_left_bracket>
      nth_llist (addr.nxt, i - 1)
  \<medium_right_bracket>
  \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr T\<close>
\<medium_right_bracket> .


proc hd_llist:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<close>
  premises \<open>l \<noteq> []\<close>
  output \<open>hd l \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> l \<Ztypecolon> Linked_Lst addr T\<close>
\<medium_left_bracket>
  nth_llist (addr, 0)
\<medium_right_bracket> .


proc update_nth_llist:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := y] \<Ztypecolon> Linked_Lst addr T\<close>
  is [recursive]
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
  if (i = 0) \<medium_left_bracket>
      addr.data := y
  \<medium_right_bracket> \<medium_left_bracket>
      update_nth_llist (addr.nxt, i - 1, y)
  \<medium_right_bracket> \<semicolon>
  \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr T\<close>
\<medium_right_bracket> .


proc length_of:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<close>
  premises \<open>length l < 2 ^ LENGTH(\<i>\<n>\<t>)\<close>
  output   \<open>length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> l \<Ztypecolon> Linked_Lst addr T\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if (addr = NULL) \<medium_left_bracket>
    return(0)
  \<medium_right_bracket> \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
    addr.nxt \<rightarrow> val t1 \<semicolon>
    val ret \<leftarrow> length_of (addr.nxt) + 1 \<semicolon>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr T\<close> \<semicolon>
    return (ret)
  \<medium_right_bracket>
\<medium_right_bracket> .


proc reverse_aux:
  input  \<open>l  \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<heavy_comma>
          l' \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr' T\<close>
  output \<open>rev l @ l' \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr'' T
          \<s>\<u>\<b>\<j> addr''. \<top>\<close>
  is [recursive]
\<medium_left_bracket>
  if (addr = NULL) \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(0)\<close>
    addr'
  \<medium_right_bracket> \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
    addr.nxt \<rightarrow> val aa \<semicolon>
    addr.nxt := addr' \<semicolon>
    \<open>Linked_Lst addr' T\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>hd l # l' \<Ztypecolon> Linked_Lst addr T\<close> \<semicolon>
    reverse_aux (aa, addr)
  \<medium_right_bracket>
\<medium_right_bracket> .

proc reverse:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr T\<close>
  output \<open>rev l \<Ztypecolon> \<r>\<e>\<f> Linked_Lst addr'  T
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  \<m>\<a>\<k>\<e>\<s>(0) \<open>Linked_Lst 0 T\<close>
  reverse_aux( addr, NULL )
            \<comment> \<open>^ \<phi>-type annotation here is not considered as a manual annotation because
                  it is exactly the C language type of the pointer literal.It can be
                  automatically generated by an C parser. 0 denotes the NULL pointer. \<close>
\<medium_right_bracket> .

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


end