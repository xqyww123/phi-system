theory NuDataStructure
  imports NuInstructions
begin

section \<open>Dynamic List\<close>


definition "DynLst T = (Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T)
    <where> {(a \<R_arr_tail> (len,cap,ptr),addr \<R_arr_tail> data) | a len cap ptr addr data.
        length data = cap \<and> ptr = addr \<and> len < cap}
    <up-lift> (\<lambda>x. case x of (a \<R_arr_tail> (len,cap,ptr),addr \<R_arr_tail> data) \<Rightarrow> a \<R_arr_tail> data)"

lemma "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> data \<tycolon> DynLst T
  \<longmapsto> (\<exists>* addr. (a \<R_arr_tail> (len,length data,addr),addr \<R_arr_tail> data) \<tycolon> Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T)
    \<^bold>w\<^bold>i\<^bold>t\<^bold>h len < length data"
  unfolding DynLst_def Dest_def
  apply (\<nu>reason)

lemma "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e length data = cap \<Longrightarrow>
  \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a \<R_arr_tail> (len,cap,ptr),addr \<R_arr_tail> data) \<tycolon> Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T \<longmapsto> a \<R_arr_tail> data \<tycolon> DynLst T"
  unfolding DynLst_def Intro_def Premise_def
  ML_val \<open>#goal @{Isar.goal} |> Thm.prop_of\<close>
  apply (\<nu>reason)


end