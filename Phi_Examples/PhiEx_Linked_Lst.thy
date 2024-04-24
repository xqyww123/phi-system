theory PhiEx_Linked_Lst
  imports Phi_Semantics.PhiSem_C
begin

abbreviation \<open>\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>

\<phi>type_def Linked_Lst :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T)   = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
      | \<open>(x#ls \<Ztypecolon> Linked_Lst addr TY T) = ((nxt, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> nxt: \<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY, data: T \<rbrace>\<heavy_comma>
                                           ls \<Ztypecolon> Linked_Lst nxt TY T
                                         \<s>\<u>\<b>\<j> nxt. address_to_base addr )\<close> (**)

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


proc init:
  input  Void
  output \<open>[] \<Ztypecolon> Linked_Lst 0 TY T\<close>
  is [routine]
\<medium_left_bracket>
  \<m>\<a>\<k>\<e>\<s>(0) \<open>Linked_Lst _ TY T\<close> \<semicolon>
  return \<open>0 \<Ztypecolon> \<Pp>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<close>
\<medium_right_bracket> .

proc is_empty:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> l = [] \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  is [routine]
\<medium_left_bracket>
  \<open>$addr = 0\<close>
\<medium_right_bracket> .




context
  fixes T :: \<open>(VAL, 'a) \<phi>\<close>                            \<comment> \<open>we provide a generic verification\<close>
    and TY :: TY                                      \<comment> \<open>semantic type\<close>
  assumes [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>    \<comment> \<open>specify the semantic type of T\<close>
begin

proc prepend_llist:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  requires [\<phi>reason]: \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>v#l \<Ztypecolon> Linked_Lst addr' TY T\<heavy_comma> addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY) \<s>\<u>\<b>\<j> addr'. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc_1 \<open>\<lbrace> nxt: \<Pp>\<t>\<r> \<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY, data: T \<rbrace>\<close> \<semicolon>
  $ret \<tribullet> nxt := $addr \<semicolon>
  $ret \<tribullet> data := $v \<semicolon>
  \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst _ TY T\<close> \<semicolon>
  $ret
\<medium_right_bracket> .


proc pop_llist:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<close>
  output \<open>(if l = [] then [] else tl l) \<Ztypecolon> Linked_Lst addr' TY T\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)
          \<s>\<u>\<b>\<j> addr'. \<top>\<close>
  is [routine]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    return(\<open>0 \<Ztypecolon> \<Pp>\<t>\<r> (\<l>\<i>\<n>\<k>_\<l>\<i>\<s>\<t> TY)\<close>)
    \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> \<semicolon>
      note [[\<phi>trace_reasoning = 2]]
      \<semicolon> 
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
  val ret \<leftarrow> $addr \<tribullet> nxt ! \<semicolon>
  mfree ($addr) \<semicolon>









proc nth_llist:
  input    \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
  premises \<open>i < length l\<close>
  output   \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
  is [recursive]
  \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon> \<comment> \<open>annotation 1: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data !
    \<medium_right_bracket> \<medium_left_bracket>
        nth_llist ($addr \<tribullet> nxt !, $i - 1)
    \<medium_right_bracket>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr TY T\<close> \<comment> \<open>annotation 2: close abstraction\<close>
  \<medium_right_bracket> .


proc update_nth_llist:
  input    \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := y] \<Ztypecolon> Linked_Lst addr TY T\<close>
  is [recursive]
  \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon> \<comment> \<open>annotation 1: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data := $y
    \<medium_right_bracket> \<medium_left_bracket>
        update_nth_llist ($addr \<tribullet> nxt !, $i - 1, $y)
    \<medium_right_bracket>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr TY T\<close> \<comment> \<open>annotation 2: close abstraction\<close>
 \<medium_right_bracket> .


end

proc length_of:
  input    \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  premises \<open>length l < 2 ^ LENGTH(\<i>\<n>\<t>)\<close>
  output   \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
  is [recursive]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    0
  \<medium_right_bracket> \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
    length_of ($addr \<tribullet> nxt !) + 1
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr TY T\<close> \<comment> \<open>1: call the second constructor\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc length_of':
  \<comment> \<open>personally, I prefer this version which is more readable though costs more annotations\<close>
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  premises \<open>length l < 2 ^ LENGTH(\<i>\<n>\<t>)\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<i>\<n>\<t>)\<close>
  is [recursive]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    0 is \<open>length l\<close>
  \<medium_right_bracket> \<medium_left_bracket>
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
    (length_of ($addr \<tribullet> nxt !) + 1) is \<open>length l\<close>
    \<m>\<a>\<k>\<e>\<s>(1) \<open>Linked_Lst addr TY T\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .


proc reverse_aux:
  input  \<open>l' \<Ztypecolon> Linked_Lst addr' TY T\<heavy_comma>
          l  \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma>
          addr' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma>
          addr  \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  output \<open>rev l @ l' \<Ztypecolon> Linked_Lst addr'' TY T\<heavy_comma>
          addr'' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}
          \<s>\<u>\<b>\<j> addr''. \<top>\<close>
  is [recursive]
  \<medium_left_bracket>
    if \<open>$addr = 0\<close> \<medium_left_bracket>
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(0)\<close>
      $addr'
    \<medium_right_bracket> \<medium_left_bracket>
      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<open>\<o>\<p>\<e>\<n>(1)\<close> \<semicolon>
      $addr \<tribullet> nxt ! \<rightarrow> val aa \<semicolon>
      $addr \<tribullet> nxt := $addr' \<semicolon>
      \<open>Linked_Lst addr' TY T\<close> \<m>\<a>\<k>\<e>\<s>(1) \<open>hd l # l' \<Ztypecolon> Linked_Lst addr TY T\<close> \<semicolon>
      reverse_aux ($addr, $aa) 
    \<medium_right_bracket>
  \<medium_right_bracket> .

proc reverse:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  output \<open>rev l \<Ztypecolon> Linked_Lst addr'' TY T\<heavy_comma>
          addr'' \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}
          \<s>\<u>\<b>\<j> addr''. \<top>\<close>
  \<medium_left_bracket>
    \<m>\<a>\<k>\<e>\<s>(0) \<open>Linked_Lst 0 TY T\<close>
    reverse_aux( \<open>0 \<Ztypecolon> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>, $addr )
              \<comment> \<open>^ \<phi>-type annotation here is not considered as a manual annotation because
                    it is directly the C language type of the pointer literal and can be
                    automatically generated by an C parser.
                    0 denotes the NULL pointer. \<close>
  \<medium_right_bracket> .


end