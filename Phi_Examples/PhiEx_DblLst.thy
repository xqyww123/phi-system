theory PhiEx_DblLst
  imports Phi_Semantics.PhiSem_C
begin

lemma ttt [simp, \<phi>constraint_expansion for list]:
  \<open>(case x of (x, y) \<Rightarrow> y @ x) = [] \<longleftrightarrow> x = ([], [])\<close>
  \<open>(case x of (x, y) \<Rightarrow> x @ y) = [] \<longleftrightarrow> x = ([], [])\<close>
  by (cases x; auto)+

setup \<open>Context.theory_map (Phi_Type_Derivers.Expansion.map (fn ctxt =>
  ctxt addsimps @{thms ttt}))\<close>

declare [[\<phi>trace_reasoning = 3]]
  
\<phi>type_def Dbl_LLst :: \<open>TY \<Rightarrow> logaddr arrow_st \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>([] \<Ztypecolon> Dbl_LLst TY addr T) = (Void \<s>\<u>\<b>\<j> Arrow_st.s addr = Arrow_st.t addr)\<close>
     | \<open>(x#ls \<Ztypecolon> Dbl_LLst TY addr T) =
        ((next, x) \<Ztypecolon> \<m>\<e>\<m>[Arrow_st.s addr] \<lbrace> next: \<Pp>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {next: \<p>\<t>\<r>, data: TY}, data: T \<rbrace>\<heavy_comma>
         ls \<Ztypecolon> Dbl_LLst TY (next \<BRarrow> Arrow_st.t addr) T
         \<s>\<u>\<b>\<j> next. next \<noteq> 0)\<close>
  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (Dbl_LLst TY addr T) (\<lambda>x. list_all P x \<and> (x = [] \<longrightarrow> Arrow_st.s addr = Arrow_st.t addr)) \<close>
                                                \<comment> \<open>TODO: \<open>(x = [] \<longleftrightarrow> addr = addr')\<close>\<close>
       and \<open>Identity_Elements\<^sub>E (Dbl_LLst TY addr T) (\<lambda>l. Arrow_st.s addr = Arrow_st.t addr \<and> l = [])\<close>
       and \<open>Identity_Elements\<^sub>I (Dbl_LLst TY addr T) (\<lambda>l. l = []) (\<lambda>l. Arrow_st.s addr = Arrow_st.t addr \<and> l = [])\<close>
(*       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (TY\<^sub>2 = TY\<^sub>1) \<and> (addr = addr')
         \<Longrightarrow> Transformation_Functor (Dbl_LLst TY\<^sub>1 addr) (Dbl_LLst TY\<^sub>2 addr')
                T U set (\<lambda>_. UNIV) list_all2 \<close>
           (arbitrary: addr')
       and Functional_Transformation_Functor
       and*) and \<open>Semimodule_SDistr_Homo\<^sub>Z (\<lambda>addr. Dbl_LLst TY addr T) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ (x,y). y @ x) \<close>
          (tactic: clarsimp, rule exI[where x=\<open>\<lambda>_ _ _ ls _ _ (a,b). take (length b - 1) ls\<close>],
                             rule exI[where x=\<open>\<lambda>_ _ _ ls _ _ (a,b) _. drop (length b - Suc 0) ls\<close>],
                             rule exI[where x=\<open>\<lambda>_ _ _ _ _ _ (a,b). hd a\<close>],
                             rule exI[where x=\<open>\<lambda>_ _ _ _ _ _ (a,b). tl a\<close>],
tactic \<open>all_tac o @{print}\<close>)

term \<open>Semimodule_SDistr_Homo\<^sub>Z (\<lambda>addr. Dbl_LLst TY addr T) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ (x,y). y @ x) \<close>

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
\<Longrightarrow> l \<Ztypecolon> Dbl_LLst TY (s \<BRarrow> t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> l\<^sub>L \<Ztypecolon> Dbl_LLst TY (s \<BRarrow> m) T\<heavy_comma> l\<^sub>R \<Ztypecolon> Dbl_LLst TY (m \<BRarrow> t) T \<s>\<u>\<b>\<j> m. \<top> \<close>
  apply (induct l arbitrary: l\<^sub>L s)
  \<medium_left_bracket>
    to \<open>OPEN 0 _\<close>
    \<open>[] \<Ztypecolon> MAKE 0 (Dbl_LLst TY (s \<BRarrow> t) T)\<heavy_comma> [] \<Ztypecolon> MAKE 0 (Dbl_LLst TY (t \<BRarrow> t) T)\<close>
  \<medium_right_bracket>
  \<medium_left_bracket> premises IH
    case_analysis \<open> l\<^sub>L = [] \<close> \<medium_left_bracket>
      \<open>l\<^sub>L \<Ztypecolon> MAKE 0 (Dbl_LLst TY (s \<BRarrow> s) T)\<heavy_comma> _ \<Ztypecolon> Dbl_LLst TY (s \<BRarrow> t) T\<close> 
    \<medium_right_bracket> for \<open>(l\<^sub>L \<Ztypecolon> Dbl_LLst TY (s \<BRarrow> m) T\<heavy_comma> l\<^sub>R \<Ztypecolon> Dbl_LLst TY (m \<BRarrow> t) T \<s>\<u>\<b>\<j> m. \<top>)\<close>
    \<medium_left_bracket>
      obtain l\<^sub>L' where t1[useful]: \<open>l\<^sub>L = a # l\<^sub>L'\<close> by auto_sledgehammer ;;
      to \<open>OPEN 1 _\<close>
      IH
      \<open>_ \<Ztypecolon> MAKE 1 (Dbl_LLst TY (s \<BRarrow> c) T)\<close>
    \<medium_right_bracket>
  \<medium_right_bracket> .


end