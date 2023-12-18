theory PhiEx_DblLst
  imports Phi_Semantics.PhiSem_C
begin

declare [[\<phi>trace_reasoning = 1]]

\<phi>type_def Dbl_LLst :: \<open>logaddr \<Rightarrow> logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Dbl_LLst addr addr' TY T) = (Void \<s>\<u>\<b>\<j> addr = addr')\<close>
     | \<open>(x#ls \<Ztypecolon> Dbl_LLst addr addr' TY T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Dbl_LLst next addr' TY T
         \<s>\<u>\<b>\<j> next. next \<noteq> 0)\<close>
  deriving Basic 
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Dbl_LLst addr addr' TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longrightarrow> addr = addr')) \<close>
                                                \<comment> \<open>TODO: \<open>(x = [] \<longleftrightarrow> addr = addr')\<close>\<close>
       and \<open>Identity_Elements\<^sub>E (Dbl_LLst addr addr' TY T) (\<lambda>l. addr = addr' \<and> l = [])\<close>
       and \<open>Identity_Elements\<^sub>I (Dbl_LLst addr addr' TY T) (\<lambda>l. l = []) (\<lambda>l. addr = addr' \<and> l = [])\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY\<^sub>2 = TY\<^sub>1) \<and> (addr\<^sub>2 = addr\<^sub>1) \<and> (addr'\<^sub>2 = addr'\<^sub>1)
        \<Longrightarrow> Transformation_Functor (Dbl_LLst addr\<^sub>1 addr'\<^sub>1 TY\<^sub>1) (Dbl_LLst addr\<^sub>2 addr'\<^sub>2 TY\<^sub>2)
              T U set (\<lambda>_. UNIV) list_all2 \<close>
           (arbitrary: addr\<^sub>2)
       and Functional_Transformation_Functor


lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> l = l\<^sub>L @ l\<^sub>R
\<Longrightarrow> l \<Ztypecolon> Dbl_LLst a\<^sub>s a\<^sub>t TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> l\<^sub>L \<Ztypecolon> Dbl_LLst a\<^sub>s a\<^sub>m TY T\<heavy_comma> l\<^sub>R \<Ztypecolon> Dbl_LLst a\<^sub>m a\<^sub>t TY T \<s>\<u>\<b>\<j> a\<^sub>m. \<top> \<close>
  apply (induct l arbitrary: l\<^sub>L)
  \<medium_left_bracket>
    to \<open>OPEN 0 _\<close>
    thm useful
  thm list_induct3

end