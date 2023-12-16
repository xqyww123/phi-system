theory PhiEx_Linked_Lst
  imports Phi_Semantics.PhiSem_C
begin

typ fiction

term \<open>\<Pp>\<t>\<r> T\<close>
term \<open>0 :: logaddr\<close>

declare [[\<phi>trace_reasoning = 0]]
declare [[\<phi>reasoning_step_limit = 200]]

  
    
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
      (*\<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (Linked_Lst' TY T) (\<lambda>(a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 eq l\<^sub>1 l\<^sub>2) \<close>*)







lemma
  \<open>\<forall>x xa xb xc xd.
              \<exists>uu a.
                 (xd = [] \<longrightarrow> (\<forall>xaa. Inhabited ((xaa, []) \<Ztypecolon> Linked_Lst' xa T) \<longrightarrow> Inhabited ((xaa, []) \<Ztypecolon> Linked_Lst' xa U))) \<longrightarrow>
                 (\<forall>xe xf.
                     (a = xc \<longrightarrow> Inhabited (xc \<Ztypecolon> T) \<longrightarrow> x xc xf \<and> Inhabited (xf \<Ztypecolon> U)) \<and>
                     (a \<in> set xd \<longrightarrow> Inhabited (a \<Ztypecolon> T) \<longrightarrow> x a xe \<and> Inhabited (xe \<Ztypecolon> U)) \<longrightarrow>
                     (\<forall>a b ba.
                         x xc ba \<and> list_all2 x xd b \<and> a \<noteq> 0 \<longrightarrow>
                         memaddr.blk xb \<noteq> Null \<and>
                         Inhabited (ba \<Ztypecolon> U) \<and>
                         valid_logaddr a \<and> logaddr_type a = \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: xa} \<and> Inhabited ((a, b) \<Ztypecolon> Linked_Lst' xa U) \<longrightarrow>
                         list_all2 x xd (uu (a, b) (a, ba))) \<and>
                     (\<forall>a b ba.
                         x xc ba \<and> list_all2 x xd b \<and> a \<noteq> 0 \<longrightarrow>
                         memaddr.blk xb \<noteq> Null \<and>
                         Inhabited (ba \<Ztypecolon> U) \<and>
                         valid_logaddr a \<and> logaddr_type a = \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: xa} \<and> Inhabited ((a, b) \<Ztypecolon> Linked_Lst' xa U) \<longrightarrow>
                         b = uu (a, b) (a, ba))) \<close>
  apply clarsimp
  apply (rule exI[where x=\<open>\<lambda>(a, b) (a, ba). b\<close>])
  apply auto
  apply rule
  prefer 2










term \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst' TY T) (\<lambda>(a,x). list_all P x \<and> (x = [] \<longleftrightarrow> a = 0)) \<close>
term \<open>Identity_Elements\<^sub>I (Linked_Lst' TY T) (\<lambda>(a,l). a = 0 \<and> l = [])\<close>

term \<open> Transformation_Functor (Linked_Lst' TY) (Linked_Lst' TY) T U (set o snd) (\<lambda>_. UNIV) (\<lambda>r (a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 r l\<^sub>1 l\<^sub>2) \<close>
term \<open> Abstract_Domain T D \<Longrightarrow> Abstract_Domain (Linked_Lst' TY T) (\<lambda>(_,l). list_all D l) \<close>
term \<open> Object_Equiv T eq \<Longrightarrow> Object_Equiv (Linked_Lst' TY T) (\<lambda>(a\<^sub>1,l\<^sub>1) (a\<^sub>2,l\<^sub>2). a\<^sub>1 = a\<^sub>2 \<and> list_all2 eq l\<^sub>1 l\<^sub>2) \<close>

    (*
\<phi>type_def Linked_Lst :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Linked_Lst addr TY T) = (Void \<s>\<u>\<b>\<j> addr = 0)\<close>
     | \<open>((x#ls) \<Ztypecolon> Linked_Lst addr TY T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Linked_Lst next TY T
         \<s>\<u>\<b>\<j> next. \<top>)\<close>
  deriving (*\<open>Abstract_Domain (Linked_Lst addr) (\<lambda>x. True)\<close>
       and*) Object_Equiv
*)

thm Linked_Lst.Abstract_Domain
term \<open>Abstract_Domain\<close>

thm Linked_Lst.Abstract_Domain

end