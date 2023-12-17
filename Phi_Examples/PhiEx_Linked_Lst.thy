theory PhiEx_Linked_Lst
  imports Phi_Semantics.PhiSem_C
begin

typ fiction

term \<open>\<Pp>\<t>\<r> T\<close>
term \<open>0 :: logaddr\<close>

declare [[\<phi>trace_reasoning = 0]]
declare [[\<phi>reasoning_step_limit = 120]]

    
(*
\<phi>type_def Linked_Lst' :: \<open>TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, logaddr \<times> 'a list) \<phi>\<close>
  where \<open>((addr, []) \<Ztypecolon> Linked_Lst' TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>((addr, x#ls) \<Ztypecolon> Linked_Lst' TY T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         (next, ls) \<Ztypecolon> Linked_Lst' TY T
         \<s>\<u>\<b>\<j> next. next \<noteq> 0)\<close>
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



declare [[\<phi>reasoning_step_limit = 180]]
     
\<phi>type_def Linked_Lst :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>(x#ls \<Ztypecolon> Linked_Lst addr TY T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Linked_Lst next TY T
         \<s>\<u>\<b>\<j> next. next \<noteq> 0)\<close> 
     deriving Basic
          and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst addr TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = 0)) \<close>
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<or> l = []) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY' = TY) \<and> (addr' = addr)
              \<Longrightarrow> Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr' TY') T U set (\<lambda>_. UNIV) list_all2 \<close> 
            (arbitrary: addr')
          and Functional_Transformation_Functor

term True

declare [[\<phi>trace_reasoning = 1]]
 
proc nth_llist:
  requires [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>('a::len)\<close>
  premises \<open>i < length l\<close>
  output \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
  is [recursive l i addr]
  \<medium_left_bracket>
    obtain l\<^sub>h l\<^sub>r where l_split[simp]: \<open>l = l\<^sub>h # l\<^sub>r\<close> by auto_sledgehammer \<comment> \<open>annotation 1\<close> ;; 
    to \<open>OPEN _\<close> \<comment> \<open>annotation 2: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data !
    \<medium_right_bracket> \<medium_left_bracket> 
        nth_llist ($addr \<tribullet> "next" !, $i - \<open>1 \<Ztypecolon> \<nat>('a)\<close>)
    \<medium_right_bracket>
    \<open>l \<Ztypecolon> MAKE (Linked_Lst addr TY T)\<close> \<comment> \<open>annotation 3: close abstraction\<close>
  \<medium_right_bracket> .

proc update_nth_llist:
  requires [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>
  input  \<open>l \<Ztypecolon> Linked_Lst addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>('a::len)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output \<open>l[i := y] \<Ztypecolon> Linked_Lst addr TY T\<close>
  is [recursive l i addr]
  \<medium_left_bracket>
    obtain l\<^sub>h l\<^sub>r where l_split[simp]: \<open>l = l\<^sub>h # l\<^sub>r\<close> by auto_sledgehammer \<comment> \<open>annotation 1\<close> ;; 
    to \<open>OPEN _\<close> \<comment> \<open>annotation 2: open abstraction\<close>
    if \<open>$i = 0\<close> \<medium_left_bracket>
        $addr \<tribullet> data := $y
    \<medium_right_bracket> \<medium_left_bracket>
        update_nth_llist ($addr \<tribullet> "next" !, $i - \<open>1 \<Ztypecolon> \<nat>('a)\<close>, $y)
        \<medium_right_bracket> ;;
    have t2[simp]: \<open>\<exists>a b. a # b = l[i := y]\<close> by auto_sledgehammer
            note [[\<phi>trace_reasoning = 2]]  ;;  
    \<open>l[i := y] \<Ztypecolon> MAKE (Linked_Lst addr TY T)\<close>

      thm useful

      have \<open>\<exists>a b. a # b = l[i := y]\<close>
        apply auto

  thm nth_llist




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