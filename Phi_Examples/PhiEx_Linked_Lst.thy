theory PhiEx_Linked_Lst
  imports Phi_Semantics.PhiSem_C
begin

declare [[\<phi>reasoning_step_limit = 120]]

    
(*
\<phi>type_def Linked_Lst' :: \<open>TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, logaddr \<times> 'a list) \<phi>\<close>
  where \<open>((addr, []) \<Ztypecolon> Linked_Lst' TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>((addr, x#ls) \<Ztypecolon> Linked_Lst' TY T) =
        ((nxt, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> nxt: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         (nxt, ls) \<Ztypecolon> Linked_Lst' TY T
         \<s>\<u>\<b>\<j> nxt. nxt \<noteq> 0)\<close>
   deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst' TY T) (\<lambda>(a,x). list_all P x \<and> (x = [] \<longleftrightarrow> a = 0)) \<close>
        and \<open>Identity_Elements\<^sub>E (Linked_Lst' TY T) (\<lambda>(a,l). a = 0 \<and> l = [])\<close>
        and \<open>Identity_Elements\<^sub>I (Linked_Lst' TY T) (\<lambda>(a,l). a = 0 \<or> l = []) (\<lambda>(a,l). a = 0 \<and> l = [])\<close>
        and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY
          \<Longrightarrow> Transformation_Functor (Linked_Lst' TY) (Linked_Lst' TY') T U (set o snd) (\<lambda>_. UNIV) (\<lambda>r (a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 r l\<^sub>1 l\<^sub>2) \<close> 
          (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ (_,x). x\<close>], rule exI[where x=\<open>\<lambda>(a,_) _. a\<close>],
                   rule, auto_sledgehammer, rule exI[where x=\<open>\<lambda>(_,x) _. x\<close>])
        and \<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (Linked_Lst' TY T) (\<lambda>(a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 eq l\<^sub>1 l\<^sub>2) \<close>
      (*\<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (Linked_Lst' TY T) (\<lambda>(a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 eq l\<^sub>1 l\<^sub>2) \<close>*)
*)


declare [[\<phi>trace_reasoning = 0]]
declare [[\<phi>reasoning_step_limit = 180]]
      
\<phi>type_def Linked_Lst :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>(x#ls \<Ztypecolon> Linked_Lst addr TY T) =
        ((nxt, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> nxt: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Linked_Lst nxt TY T
         \<s>\<u>\<b>\<j> nxt. nxt \<noteq> 0)\<close> 
     deriving Basic
          and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst addr TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = 0)) \<close>
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr TY T) (\<lambda>l. l = []) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY' = TY) \<and> (addr' = addr)
              \<Longrightarrow> Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr' TY') T U set (\<lambda>_. UNIV) list_all2 \<close> 
            (arbitrary: addr')
          and Functional_Transformation_Functor

term True

declare [[\<phi>trace_reasoning = 1]] 
 
proc nth_llist:
  requires [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  premises \<open>i < length l\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
  is [recursive l i addr]
  \<medium_left_bracket>
    obtain l\<^sub>h l\<^sub>r where [simp]: \<open>l = l\<^sub>h # l\<^sub>r\<close> by auto_sledgehammer  ;;
        \<comment> \<open>annotation 1 due to deficiency of sledgehammer for instantiating existential quantification (unknown variables).
            Readers may remove this line to see a correct proof obligation is still generated but
            sledgehammer fails on it.\<close> 
    to \<open>OPEN 1 _\<close> \<comment> \<open>annotation 2: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data !
    \<medium_right_bracket> \<medium_left_bracket>
        nth_llist ($addr \<tribullet> nxt !, $i - 1)
    \<medium_right_bracket>
    \<open>l \<Ztypecolon> MAKE 1 (Linked_Lst addr TY T)\<close> \<comment> \<open>annotation 3: close abstraction\<close>
  \<medium_right_bracket> .

proc update_nth_llist:
  requires [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output \<open>l[i := y] \<Ztypecolon> Linked_Lst addr TY T\<close>
  is [recursive l i addr]
  \<medium_left_bracket>
    obtain l\<^sub>h l\<^sub>r where [simp]: \<open>l = l\<^sub>h # l\<^sub>r\<close> by auto_sledgehammer \<comment> \<open>annotation 1\<close> ;; 
    to \<open>OPEN 1 _\<close> \<comment> \<open>annotation 2: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data := $y
    \<medium_right_bracket> \<medium_left_bracket>
        update_nth_llist ($addr \<tribullet> "nxt" !, $i - 1, $y)
    \<medium_right_bracket>
    \<open>l[i := y] \<Ztypecolon> MAKE 1 (Linked_Lst addr TY T)\<close> \<comment> \<open>annotation 3: close abstraction\<close>
 \<medium_right_bracket> .

proc length_of:
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  premises \<open>length l < 2 ^ LENGTH(32)\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  is [recursive l addr]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    0
  \<medium_right_bracket> \<medium_left_bracket>                           \<comment> \<open>TODO: create a syntax for this existential instantiation\<close>
    to \<open>OPEN 1 _\<close> certified by (of_tac \<open>hd l\<close>, of_tac \<open>tl l\<close>, auto_sledgehammer) ;;
    length_of ($addr \<tribullet> nxt !) + 1
    \<open>l \<Ztypecolon> MAKE 1 (Linked_Lst addr TY T)\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc length_of':
  \<comment> \<open>personally, I prefer this version which is more readable though requires more annotations\<close>
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {nxt: \<p>\<t>\<r>, data: TY}\<close>
  premises \<open>length l < 2 ^ LENGTH(32)\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  is [recursive l addr]
\<medium_left_bracket>
  if \<open>$addr = 0\<close> \<medium_left_bracket>
    0 is \<open>length l\<close>
  \<medium_right_bracket> \<medium_left_bracket>
    obtain l\<^sub>h l\<^sub>r where [useful]: \<open>l = l\<^sub>h # l\<^sub>r\<close> by auto_sledgehammer  ;;
    to \<open>OPEN _ _\<close>
    (length_of ($addr \<tribullet> nxt !) + 1) is \<open>length l\<close>
    \<open>l \<Ztypecolon> MAKE _ (Linked_Lst addr TY T)\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .


(*\<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY' = TY) \<and> (addr' = addr)
              \<Longrightarrow> Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr TY') T U set (\<lambda>_. UNIV) list_all2 \<close> 
            (tactic: clarsimp, rule exI[where x=\<open>\<lambda>(_,b). b\<close>]) *)
(*\<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst' TY T) (\<lambda>(a,x). list_all P x \<and> (x = [] \<longleftrightarrow> a = 0)) \<close>
        and \<open>Identity_Elements\<^sub>E (Linked_Lst' TY T) (\<lambda>(a,l). a = 0 \<and> l = [])\<close>
        and \<open>Identity_Elements\<^sub>I (Linked_Lst' TY T) (\<lambda>(a,l). a = 0 \<or> l = []) (\<lambda>(a,l). a = 0 \<and> l = [])\<close>
        and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY
          \<Longrightarrow> Transformation_Functor (Linked_Lst' TY) (Linked_Lst' TY') T U (set o snd) (\<lambda>_. UNIV) (\<lambda>r (a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 r l\<^sub>1 l\<^sub>2) \<close> 
          (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ (_,x). x\<close>], rule exI[where x=\<open>\<lambda>(a,_) _. a\<close>],
                   rule, auto_sledgehammer, rule exI[where x=\<open>\<lambda>(_,x) _. x\<close>])
        and \<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (Linked_Lst' TY T) (\<lambda>(a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 eq l\<^sub>1 l\<^sub>2) \<close>*)
      (*\<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (Linked_Lst' TY T) (\<lambda>(a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 eq l\<^sub>1 l\<^sub>2) \<close>*)




end