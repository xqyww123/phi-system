theory PhiStd_Loop
  imports Phi_Semantics.PhiSem_CF_Basic
          Phi_Semantics.PhiSem_Int_ArbiPrec
          Phi_Semantics.PhiSem_Variable
begin

declare [[\<phi>trace_reasoning = 0]]

proc map_list_loop:
  requires \<open>\<p>\<a>\<r>\<a>\<m> U\<close>
       and \<open>Abstract_Domain T D\<close>
       and map: \<open>\<And>i l. \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < length l \<and> D l
                   \<Longrightarrow> \<m>\<a>\<p> g i \<otimes>\<^sub>f id : U i \<^emph> R i \<mapsto> U i \<^emph> R i
                       \<o>\<v>\<e>\<r> ff i : T \<mapsto> T
                       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h i \<s>\<e>\<t>\<t>\<e>\<r> s i \<i>\<n> {l}\<close>
       and \<open>(\<And>i. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (list_upd_map i (f i)) : ff i)\<close> \<comment> \<open>TODO: error print\<close>
       and body: \<open>\<And>i v. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> i < length l
                     \<Longrightarrow> \<p>\<r>\<o>\<c> Body v \<lbrace> X\<heavy_comma> fst (h i l) \<Ztypecolon> U i\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>
                                  \<longmapsto> X\<heavy_comma> g i (fst (h i l)) \<Ztypecolon> U i \<rbrace>\<close>
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




lemma map_index_map2:
  \<open> length la = length lb
\<Longrightarrow> map_index (\<lambda>i. f (la ! i)) lb = map2 f la lb\<close>
  unfolding map_index
  by (smt (verit) length_map map2_map_map map_eq_conv map_fst_zip map_nth map_snd_zip map_zip_map old.prod.case)

lemma map_index_2_map_index_zip:
  \<open> length la = length lb
\<Longrightarrow> map_index (\<lambda>i. f i (la ! i)) lb = map_index (\<lambda>i. case_prod (f i)) (zip la lb) \<close>
  unfolding list_eq_iff_nth_eq
  by clarsimp


 
proc map_2list_loop:
  requires \<open>\<p>\<a>\<r>\<a>\<m> (U\<^sub>a, U\<^sub>b)\<close>
       and \<open>Abstract_Domain T\<^sub>a D\<^sub>a\<close>
       and \<open>Abstract_Domain T\<^sub>b D\<^sub>b\<close>
       and map\<^sub>b: \<open>\<And>i l. \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < length l \<and> D\<^sub>b l
                    \<Longrightarrow> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>b' i : T\<^sub>b \<mapsto> U\<^sub>b i \<^emph> R\<^sub>b i \<i>\<n> {l} \<w>\<i>\<t>\<h> \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>b i\<close>
       and [symmetric, simp]: \<open>(\<And>l i. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (h\<^sub>b i (l ! i)) : fst (h\<^sub>b' i l))\<close> \<comment> \<open>TODO: error print\<close>
       and map\<^sub>a[\<phi>reason 9999]: \<open>\<And>x i l.
                       \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < length l \<and> D\<^sub>a l
                   \<Longrightarrow> \<m>\<a>\<p> g\<^sub>a x \<otimes>\<^sub>f id : U\<^sub>a i \<^emph> R\<^sub>a i \<mapsto> U\<^sub>a i \<^emph> R\<^sub>a i
                       \<o>\<v>\<e>\<r> ff i x : T\<^sub>a \<mapsto> T\<^sub>a
                       \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h\<^sub>a i \<s>\<e>\<t>\<t>\<e>\<r> s\<^sub>a i \<i>\<n> {l} \<close>
       and P2[symmetric, simp, \<phi>safe_simp]: \<open>(\<And>i x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] (list_upd_map i (f i x)) : ff i x)\<close> \<comment> \<open>TODO: error print, defualt premise attribute!\<close>
       and body: \<open>\<And>i v. \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < length l\<^sub>b
                    \<Longrightarrow> \<p>\<r>\<o>\<c> Body v \<lbrace> X\<heavy_comma> fst (h\<^sub>a i l\<^sub>a) \<Ztypecolon> U\<^sub>a i\<heavy_comma> h\<^sub>b i (l\<^sub>b ! i) \<Ztypecolon> U\<^sub>b i\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l>[v] \<nat>
                                  \<longmapsto> X\<heavy_comma> g\<^sub>a (h\<^sub>b i (l\<^sub>b ! i)) (fst (h\<^sub>a i l\<^sub>a)) \<Ztypecolon> U\<^sub>a i\<heavy_comma> h\<^sub>b i (l\<^sub>b ! i) \<Ztypecolon> U\<^sub>b i \<rbrace>\<close>

  premises P1[]: \<open>\<forall>i l l'. length l = length l' \<and> l!i = l'!i \<longrightarrow> fst (h\<^sub>a i l) = fst (h\<^sub>a i l')\<close>
       and [simp]: \<open>len = length l\<^sub>b \<and> length l\<^sub>a = length l\<^sub>b\<close>

  input  \<open>X\<heavy_comma> l\<^sub>a \<Ztypecolon> T\<^sub>a\<heavy_comma> l\<^sub>b \<Ztypecolon> T\<^sub>b\<heavy_comma> len \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>X\<heavy_comma> map_index (\<lambda>i (a,b). f i (h\<^sub>b i b) a) (zip l\<^sub>a l\<^sub>b) \<Ztypecolon> T\<^sub>a\<heavy_comma> l\<^sub>b \<Ztypecolon> T\<^sub>b\<close>
\<medium_left_bracket>
  \<open>T\<^sub>a\<close> map_list_loop ($len) U\<^sub>a \<medium_left_bracket>
    apply_rule ToA_Mapper_onward[OF map\<^sub>b[where i1=i]]
    body
    apply_rule ToA_Mapper_backward[OF map\<^sub>b[where i1=i]] is l\<^sub>b
            certified using ToA_Mapper_f_expn[OF map\<^sub>a[where i1=i]] by auto_sledgehammer
  \<medium_right_bracket> ;;
\<medium_right_bracket> certified unfolding list_eq_iff_nth_eq by auto_sledgehammer  .









end