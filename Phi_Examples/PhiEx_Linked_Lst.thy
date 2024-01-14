theory PhiEx_Linked_Lst
  imports Phi_Semantics.PhiSem_C
begin

\<phi>reasoner_group Linked_Lst = (100,[0,9999]) \<open>derived reasoning rules of Linked_Lst\<close>

declare [[collect_reasoner_statistics Linked_Lst start,
         \<phi>LPR_collect_statistics derivation start]]

\<phi>type_def Linked_Lst :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>(x#ls \<Ztypecolon> Linked_Lst addr TY T) =
        ((nxt, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> nxt: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Linked_Lst nxt TY T
         \<s>\<u>\<b>\<j> nxt. \<top>)\<close> 
     deriving Basic
          and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst addr TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = 0)) \<close>
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr TY T) (\<lambda>l. l = []) (\<lambda>_. addr = 0)\<close>
          and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
              \<Longrightarrow> Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr' TY') T U set (\<lambda>_. UNIV) list_all2 \<close> 
            (arbitrary: addr')
          and Functional_Transformation_Functor

declare [[collect_reasoner_statistics Linked_Lst stop,
          \<phi>LPR_collect_statistics derivation stop]]

ML \<open>Phi_Reasoner.clear_utilization_of_group \<^theory> (the (snd @{reasoner_group %Linked_Lst})) "derivation"\<close>

declare [[\<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics]]

context
  fixes T :: \<open>(VAL, 'a) \<phi>\<close>
    and TY :: TY \<comment> \<open>semantic type\<close>
  assumes [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>
begin

declare [[auto_sledgehammer_params = "try0 = false"]]
  \<comment> \<open>For some reason I don't know, sledgehammer fails silently (with throwing an Interrupt exception)
      when \<open>try0\<close> --- reconstructing proofs using classical tactics --- is enabled.\<close>

proc nth_llist:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  premises \<open>i < length l\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
  is [recursive]
  \<medium_left_bracket>
    to \<open>OPEN 1 _\<close> ;; \<comment> \<open>annotation 1: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data !
    \<medium_right_bracket> \<medium_left_bracket>
        nth_llist ($addr \<tribullet> nxt !, $i - 1)
    \<medium_right_bracket>
    \<open>MAKE 1 (Linked_Lst addr TY T)\<close> \<comment> \<open>annotation 2: close abstraction\<close>
  \<medium_right_bracket> .

proc update_nth_llist:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output \<open>l[i := y] \<Ztypecolon> Linked_Lst addr TY T\<close>
  is [recursive]
  \<medium_left_bracket>
    to \<open>OPEN 1 _\<close> ;; \<comment> \<open>annotation 1: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data := $y
    \<medium_right_bracket> \<medium_left_bracket>
        update_nth_llist ($addr \<tribullet> nxt !, $i - 1, $y)
    \<medium_right_bracket>
    \<open>MAKE 1 (Linked_Lst addr TY T)\<close> \<comment> \<open>annotation 2: close abstraction\<close>
 \<medium_right_bracket> .

end

proc length_of:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  premises \<open>length l < 2 ^ LENGTH(32)\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  is [recursive]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    0
  \<medium_right_bracket> \<medium_left_bracket>                           \<comment> \<open>TODO: create a syntax for this existential instantiation\<close>
    to \<open>OPEN 1 _\<close> ;;
    length_of ($addr \<tribullet> nxt !) + 1
    \<open>MAKE 1 (Linked_Lst addr TY T)\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc length_of':
  \<comment> \<open>personally, I prefer this version which is more readable though costs more annotations\<close>
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  premises \<open>length l < 2 ^ LENGTH(32)\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  is [recursive]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    0 is \<open>length l\<close>
  \<medium_right_bracket> \<medium_left_bracket>
    to \<open>OPEN 1 _\<close> ;;
    (length_of ($addr \<tribullet> nxt !) + 1) is \<open>length l\<close>
    \<open>MAKE 1 (Linked_Lst addr TY T)\<close>
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
      to \<open>OPEN 0 _\<close>
      $addr'
    \<medium_right_bracket> \<medium_left_bracket>
      to \<open>OPEN 1 _\<close> ;;
      $addr \<tribullet> nxt ! \<rightarrow> val aa ;;
      $addr \<tribullet> nxt := $addr' ;;
      (*select*) \<open>Linked_Lst addr' TY T\<close> (*to apply 1st constructor*) \<open>hd l # l' \<Ztypecolon> MAKE 1 (Linked_Lst addr TY T)\<close> ;;
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
    \<open>MAKE 0 (Linked_Lst 0 TY T)\<close>
    reverse_aux( \<open>0 \<Ztypecolon> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>, $addr )
              \<comment> \<open>^ \<phi>-type annotation here is not considered as a manual annotation because
                    it is given from the type of the pointer literal and can be
                    automatically generated by an C parser.
                    0 denotes the NULL pointer. \<close>
  \<medium_right_bracket> .

declare [[\<phi>LPR_collect_statistics program stop,
          collecting_subgoal_statistics=false]]



end