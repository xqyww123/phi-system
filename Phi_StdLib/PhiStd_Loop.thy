theory PhiStd_Loop
  imports Phi_Semantics.PhiSem_CF_Basic
          Phi_Semantics.PhiSem_Int_ArbiPrec
          Phi_Semantics.PhiSem_Variable
begin

declare [[\<phi>trace_reasoning = 0]]

proc map_list_loop:
  requires \<open>\<p>\<a>\<r>\<a>\<m> U\<close>
       and map: \<open>\<And>i l. \<m>\<a>\<p> g \<otimes>\<^sub>f id : U i \<^emph> R i \<mapsto> U i \<^emph> R i
                       \<o>\<v>\<e>\<r> list_upd_map i (f i) : T \<mapsto> T
                       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h i \<s>\<e>\<t>\<t>\<e>\<r> s i \<i>\<n> {l}\<close>
       and body: \<open>\<And>i v. \<p>\<r>\<o>\<c> Body v \<lbrace> X\<heavy_comma> fst (h i l) \<Ztypecolon> U i\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>
                                  \<longmapsto> X\<heavy_comma> g (fst (h i l)) \<Ztypecolon> U i \<rbrace>\<close>
  premises P1[]: \<open>\<forall>i l l'. length l = length l' \<and> l!i = l'!i \<longrightarrow> fst (h i l) = fst (h i l')\<close>
       and [simp]: \<open>len = length l\<close>

  input  \<open>X\<heavy_comma> l \<Ztypecolon> T\<heavy_comma> len \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>X\<heavy_comma> map_index f l \<Ztypecolon> T\<close>
\<medium_left_bracket>
  var i \<leftarrow> \<open>0 \<Ztypecolon> \<nat>\<close> ;;
  while \<open>X\<heavy_comma> l' \<Ztypecolon> T\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<r>[i] \<nat> \<s>\<u>\<b>\<j> l' i.
           Inv: (i \<le> length l \<and> length l' = length l \<and>
                 take i l' = map_index f (take i l) \<and> drop i l' = drop i l) \<and>
           Guard: (i < length l) \<close>
    \<medium_left_bracket> $i < $len \<medium_right_bracket>
    \<medium_left_bracket>
      apply_rule ToA_Mapper_onward[OF map[where i1=i]]
      body ($i)
      apply_rule ToA_Mapper_backward[OF map[where i1=i]]
              is \<open>list_upd_map i (f i) l'\<close> certified using ToA_Mapper_f_expn[OF map[where i1=i]] by auto_sledgehammer ;;
      $i \<leftarrow> $i + 1
    \<medium_right_bracket>
\<medium_right_bracket> .


proc map_2list_loop:
  requires map\<^sub>a: \<open>\<And>i l. \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>a i : T\<^sub>a \<mapsto> U\<^sub>a i \<^emph> R\<^sub>a i \<i>\<n> {l} \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>a i\<close>
       and map\<^sub>b[\<phi>reason]: \<open>\<And>x i l. \<m>\<a>\<p> g\<^sub>b x \<otimes>\<^sub>f id : U\<^sub>b i \<^emph> R\<^sub>b i \<mapsto> U\<^sub>b i \<^emph> R\<^sub>b i
                       \<o>\<v>\<e>\<r> list_upd_map i (f x i) : T\<^sub>b \<mapsto> T\<^sub>b
                       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>b i \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>b i \<i>\<n> {l}\<close>
       and body: \<open>\<And>i v. \<p>\<r>\<o>\<c> Body v \<lbrace> X\<heavy_comma> fst (h\<^sub>a i l\<^sub>a) \<Ztypecolon> U\<^sub>a i\<heavy_comma> fst (h\<^sub>b i l\<^sub>b) \<Ztypecolon> U\<^sub>b i\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>
                                  \<longmapsto> X\<heavy_comma> g\<^sub>b (fst (h\<^sub>a i l\<^sub>a)) (fst (h\<^sub>b i l\<^sub>b)) \<Ztypecolon> U i \<rbrace>\<close>
  premises P1[]: \<open>\<forall>i l l'. length l = length l' \<and> l!i = l'!i \<longrightarrow> fst (h i l) = fst (h i l')\<close>
       and [simp]: \<open>len = length l\<^sub>b \<and> length l\<^sub>a = length\<^sub>b\<close>

  input  \<open>X\<heavy_comma> l\<^sub>a \<Ztypecolon> T\<^sub>a\<heavy_comma> l\<^sub>b \<Ztypecolon> T\<^sub>b\<heavy_comma> len \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>X\<heavy_comma> l\<^sub>a \<Ztypecolon> T\<^sub>a\<heavy_comma> map_index (\<lambda>i. case_prod (f i)) (zip l\<^sub>a l\<^sub>b) \<Ztypecolon> T\<^sub>b\<close>
\<medium_left_bracket>
  map_list_loop


end