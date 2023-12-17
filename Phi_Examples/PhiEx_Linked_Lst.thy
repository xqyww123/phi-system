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


declare [[\<phi>trace_reasoning = 0]]

declare [[\<phi>reasoning_step_limit = 120]]
     
\<phi>type_def Linked_Lst :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>(x#ls \<Ztypecolon> Linked_Lst addr TY T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Linked_Lst next TY T
         \<s>\<u>\<b>\<j> next. next \<noteq> 0)\<close> 
     deriving (*Basic
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<or> l = []) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and*) \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY' = TY) \<and> (addr' = addr)
              \<Longrightarrow> Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr TY') T U set (\<lambda>_. UNIV) list_all2 \<close> 
            (arbitrary:  addr')
            (tactic: clarsimp, rule exI[where x=\<open>\<lambda>(_,b). b\<close>])





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