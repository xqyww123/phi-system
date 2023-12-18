theory PhiEx_DblLst
  imports Phi_Semantics.PhiSem_C
begin
   
\<phi>type_def Dbl_LLst :: \<open>logaddr \<Rightarrow> logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Dbl_LLst addr addr' TY T) = (Void \<s>\<u>\<b>\<j> addr = addr')\<close>
     | \<open>(x#ls \<Ztypecolon> Dbl_LLst addr addr' TY T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Dbl_LLst next addr' TY T
         \<s>\<u>\<b>\<j> next. next \<noteq> 0)\<close>
  deriving Basic 
       and \<open>Identity_Elements\<^sub>E (Dbl_LLst addr addr' TY T) (\<lambda>l. addr = addr' \<and> l = [])\<close>
       and \<open>Identity_Elements\<^sub>I (Dbl_LLst addr addr' TY T) (\<lambda>l. l = []) (\<lambda>l. addr = addr' \<and> l = [])\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY\<^sub>2 = TY\<^sub>1) \<and> (addr\<^sub>2 = addr\<^sub>1) \<and> (addr'\<^sub>2 = addr'\<^sub>1)
        \<Longrightarrow> Transformation_Functor (Dbl_LLst addr\<^sub>1 addr'\<^sub>1 TY\<^sub>1) (Dbl_LLst addr\<^sub>2 addr'\<^sub>2 TY\<^sub>2)
              T U set (\<lambda>_. UNIV) list_all2 \<close>
           (arbitrary: addr\<^sub>2)
       and Functional_Transformation_Functor





term \<open>  \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY\<^sub>2 = TY\<^sub>1) \<and> (addr\<^sub>2 = addr\<^sub>1) \<and> (addr\<^sub>2' = addr\<^sub>1')
    \<Longrightarrow> Transformation_Functor (Dbl_LLst addr\<^sub>1 addr'\<^sub>1 TY\<^sub>1) (Dbl_LLst addr\<^sub>2 addr'\<^sub>2 TY\<^sub>2)
          T U set (\<lambda>_. UNIV) list_all2 \<close>
term \<open>Identity_Elements\<^sub>I (Dbl_LLst addr addr' TY T) (\<lambda>l. addr = addr' \<or> l = []) (\<lambda>l. addr = addr' \<and> l = [])\<close>
term \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Dbl_LLst addr addr' TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = addr'))\<close>
(*Basic
          and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Linked_Lst addr TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longleftrightarrow> addr = 0)) \<close>
          and \<open>Identity_Elements\<^sub>E (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open>Identity_Elements\<^sub>I (Linked_Lst addr TY T) (\<lambda>l. addr = 0 \<or> l = []) (\<lambda>l. addr = 0 \<and> l = [])\<close>
          and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY' = TY) \<and> (addr' = addr)
              \<Longrightarrow> Transformation_Functor (Linked_Lst addr TY) (Linked_Lst addr' TY') T U set (\<lambda>_. UNIV) list_all2 \<close> 
            (arbitrary: addr')
          and Functional_Transformation_Functor*)

end