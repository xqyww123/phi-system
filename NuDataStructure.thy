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
ML \<open>find_first\<close>

lemma "(\<And>x. \<exists>y. y = x)" proof

lemma "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l \<tycolon> DynLst T
  \<longmapsto> (\<exists>* addr buf. (a \<R_arr_tail> (length l,length l + length buf,addr),addr \<R_arr_tail> (l @ buf)) \<tycolon> Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T)"
  unfolding DynLst_def Cast_def
  
  
  apply (rule Cast_I)
  ML_val \<open>
val ctx = Config.put Pattern.unify_trace_failure true @{context}
fun RSNX tha (i, thb) = let open Thm in
  (case Seq.chop 2 (biresolution (SOME ctx) false [(false, tha)] i thb) of
    ([th], _) => solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", i, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", i, [tha, thb]))
end


val x= RSNX @{thm BBB} (1, #goal @{Isar.goal})
\<close>
   apply (\<nu>reason) unfolding Premise_def
  apply auto
ML \<open>find_first\<close>
notepad
begin
  assume  A[simplified (no_asm_simp)]: "id ((a,b,c) = (a',b',c')) \<Longrightarrow> P (a,b,c)"
end

lemma "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e len < length data \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a \<R_arr_tail> (len,length data,addr),addr \<R_arr_tail> data) \<tycolon> Ref \<lbrace> \<nat>[size_t] \<cross_product> \<nat>[size_t] \<cross_product> Pointer \<rbrace> \<^emph> Array T
    \<longmapsto> a \<R_arr_tail> take len data \<tycolon> DynLst T"
  unfolding DynLst_def by (rule Cast_I) \<nu>reason


end