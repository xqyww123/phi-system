theory PhiEx_DblLst
  imports Phi_Semantics.PhiSem_C
begin

declare [[\<phi>trace_reasoning = 1]]

\<phi>type_def Dbl_LLst :: \<open>logaddr arrow_st \<Rightarrow> TY \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Dbl_LLst addr TY T) = (Void \<s>\<u>\<b>\<j> Arrow_st.s addr = Arrow_st.t addr)\<close>
     | \<open>(x#ls \<Ztypecolon> Dbl_LLst addr TY T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[Arrow_st.s addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Dbl_LLst (next \<BRarrow> Arrow_st.t addr) TY T
         \<s>\<u>\<b>\<j> next. next \<noteq> 0)\<close>
  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Dbl_LLst addr TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longrightarrow> Arrow_st.s addr = Arrow_st.t addr)) \<close>
                                                \<comment> \<open>TODO: \<open>(x = [] \<longleftrightarrow> addr = addr')\<close>\<close>
       and \<open>Identity_Elements\<^sub>E (Dbl_LLst addr TY T) (\<lambda>l. Arrow_st.s addr = Arrow_st.t addr \<and> l = [])\<close>
       and \<open>Identity_Elements\<^sub>I (Dbl_LLst addr TY T) (\<lambda>l. l = []) (\<lambda>l. Arrow_st.s addr = Arrow_st.t addr \<and> l = [])\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY\<^sub>2 = TY\<^sub>1) \<and> (addr = addr')
         \<Longrightarrow> Transformation_Functor (Dbl_LLst addr TY\<^sub>1) (Dbl_LLst addr' TY\<^sub>2)
                T U set (\<lambda>_. UNIV) list_all2 \<close>
           (arbitrary: addr')
       and Functional_Transformation_Functor

(*Basic 
       and \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Dbl_LLst addr addr' TY T) (\<lambda>x. list_all P x \<and> (x = [] \<longrightarrow> addr = addr')) \<close>
                                                \<comment> \<open>TODO: \<open>(x = [] \<longleftrightarrow> addr = addr')\<close>\<close>
       and \<open>Identity_Elements\<^sub>E (Dbl_LLst addr addr' TY T) (\<lambda>l. addr = addr' \<and> l = [])\<close>
       and \<open>Identity_Elements\<^sub>I (Dbl_LLst addr addr' TY T) (\<lambda>l. l = []) (\<lambda>l. addr = addr' \<and> l = [])\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY\<^sub>2 = TY\<^sub>1) \<and> (addr\<^sub>2 = addr\<^sub>1) \<and> (addr'\<^sub>2 = addr'\<^sub>1)
        \<Longrightarrow> Transformation_Functor (Dbl_LLst addr\<^sub>1 addr'\<^sub>1 TY\<^sub>1) (Dbl_LLst addr\<^sub>2 addr'\<^sub>2 TY\<^sub>2)
              T U set (\<lambda>_. UNIV) list_all2 \<close>
           (arbitrary: addr\<^sub>2)
       and Functional_Transformation_Functor
*)

(*term \<open>\<close>*)
 
lemma split_Dbl_LLst:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> l = l\<^sub>L @ l\<^sub>R
\<Longrightarrow> l \<Ztypecolon> Dbl_LLst (s \<BRarrow> t) TY T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> l\<^sub>L \<Ztypecolon> Dbl_LLst (s \<BRarrow> m) TY T\<heavy_comma> l\<^sub>R \<Ztypecolon> Dbl_LLst (m \<BRarrow> t) TY T \<s>\<u>\<b>\<j> m. \<top> \<close>
  apply (induct l arbitrary: l\<^sub>L s)
  \<medium_left_bracket>
    to \<open>OPEN 0 _\<close>
    \<open>[] \<Ztypecolon> MAKE 0 (Dbl_LLst (s \<BRarrow> t) TY T)\<heavy_comma> [] \<Ztypecolon> MAKE 0 (Dbl_LLst (t \<BRarrow> t) TY T)\<close>
  \<medium_right_bracket>
  \<medium_left_bracket> premises IH
    case_analysis \<open> l\<^sub>L = [] \<close> \<medium_left_bracket>
      \<open>l\<^sub>L \<Ztypecolon> MAKE 0 (Dbl_LLst (s \<BRarrow> s) TY T)\<heavy_comma> _ \<Ztypecolon> Dbl_LLst (s \<BRarrow> t) TY T\<close> 
    \<medium_right_bracket> for \<open>(l\<^sub>L \<Ztypecolon> Dbl_LLst (s \<BRarrow> m) TY T\<heavy_comma> l\<^sub>R \<Ztypecolon> Dbl_LLst (m \<BRarrow> t) TY T \<s>\<u>\<b>\<j> m. \<top>)\<close>
    \<medium_left_bracket>
      obtain l\<^sub>L' where t1[useful]: \<open>l\<^sub>L = a # l\<^sub>L'\<close> by auto_sledgehammer ;;
      to \<open>OPEN 1 _\<close>
      IH
      \<open>_ \<Ztypecolon> MAKE 1 (Dbl_LLst (s \<BRarrow> c) TY T)\<close>
    \<medium_right_bracket>
  \<medium_right_bracket> .


end