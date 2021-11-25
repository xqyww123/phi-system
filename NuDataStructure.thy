theory NuDataStructure
  imports NuInstructions
begin

section \<open>Dynamic List\<close>


definition "DynLst T = (Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T)
    <where> {(a \<R_arr_tail> (len,cap,ptr),addr \<R_arr_tail> data) | a len cap ptr addr data.
        length data = cap \<and> ptr = addr \<and> len \<le> cap}
    <up-lift> (\<lambda>x. case x of (a \<R_arr_tail> (len,cap,ptr),addr \<R_arr_tail> data) \<Rightarrow> a \<R_arr_tail> take len data)"

lemma Cast_I: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (P \<longrightarrow> Q) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q"
  unfolding Cast_def Premise_def by simp
lemma Intro_Cast_I: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (P \<longrightarrow> Q) \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q"
  unfolding Intro_def Cast_def Premise_def by simp
lemma Dest_Cast_I: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (P \<longrightarrow> Q) \<Longrightarrow> \<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q"
  unfolding Dest_def Cast_def Premise_def by simp


lemma DynLst_I_\<nu>app:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e len \<le> length data \<and> cap = length data \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a \<R_arr_tail> (len,cap,addr),addr \<R_arr_tail> data) \<tycolon> Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T
    \<longmapsto> a \<R_arr_tail> take len data \<tycolon> DynLst T"
  unfolding DynLst_def Cast_def by (cases a, cases addr) (auto simp add: lrep_exps)
(* unfolding DynLst_def by (rule Cast_I) \<nu>reason *)

lemma [\<nu>overload D]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l \<tycolon> DynLst T
  \<longmapsto> (\<exists>* buf addr. (a \<R_arr_tail> (length l,length l + length buf,addr),addr \<R_arr_tail> (l @ buf)) \<tycolon> Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T)"
  unfolding DynLst_def Cast_def
  apply (auto simp add: lrep_exps)
  subgoal for v len base ofs list
    by (rule exI[of _ "drop len list"]) (auto simp add: min_absorb1 min_absorb2)
  done

proc DynLst_new: \<open>R\<heavy_comma> buf_size \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H\<close> \<longmapsto> \<open>\<exists>*ptr. (R\<heavy_comma> ptr \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> ptr \<R_arr_tail> [] \<tycolon> DynLst T)\<close>
  requires \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m T\<close>
        and [\<nu>intro]: \<open>\<nu>Zero T zero\<close>
  \<bullet> \<rightarrow> buf_size
  \<bullet> alloc \<open>\<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace>\<close>
  \<bullet> buf_size \<down>: 2 buf_size alloc_array \<open>T\<close> -- ppptr \<down>: 3 DynLst_I
  finish


ML \<open>Runtime.exn_trace\<close>
end