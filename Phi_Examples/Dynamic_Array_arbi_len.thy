theory Dynamic_Array_arbi_len
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Mem_C_AI
          PhiStd.PhiStd_Slice_a
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

















\<phi>type_def DynArr :: \<open>address \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x list) \<phi>\<close>
  where \<open>l \<Ztypecolon> DynArr addr T \<equiv> (a\<^sub>D, len, cap) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> data: Ptr[\<a>\<r>\<r>\<a>\<y>[cap] \<t>\<y>\<p>\<e>\<o>\<f> T], len: \<nat>, cap: \<nat> \<rbrace>\<heavy_comma>
                              data \<Ztypecolon> \<m>\<e>\<m>[a\<^sub>D] \<bbbA>\<r>\<r>\<a>\<y>[cap] T
                              \<s>\<u>\<b>\<j> a\<^sub>D len cap data. len = length l \<and> cap = length data \<and>
                                                   len \<le> cap \<and> (cap = 0 \<or> cap < 2 * len) \<and>
                                                   take len data = l \<and> address_to_base a\<^sub>D \<and> address_to_base addr \<and>
                                                   \<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {data: \<p>\<t>\<r>, len: \<a>\<i>\<n>\<t>, cap: \<a>\<i>\<n>\<t>} \<and>
                                                   \<t>\<y>\<p>\<e>\<o>\<f> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n> \<close>

  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0 \<and> \<t>\<y>\<p>\<e>\<o>\<f> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr T) (list_all2 eq)\<close>
            (tactic: auto, subgoal' for x xa xb xc \<open>rule exI[where x=\<open>xa @ drop (length xa) xc\<close>]\<close>)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (addr' = addr)
         \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> \<t>\<y>\<p>\<e>\<o>\<f> T = \<t>\<y>\<p>\<e>\<o>\<f> U
         \<Longrightarrow> Transformation_Functor (DynArr addr) (DynArr addr') T U (\<lambda>_. UNIV) (\<lambda>_. UNIV) list_all2\<close>
       
       (*and Functional_Transformation_Functor*)
       and Pointer_Of
       and \<open>\<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> addr = addr'
        \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> \<t>\<y>\<p>\<e>\<o>\<f> T = \<t>\<y>\<p>\<e>\<o>\<f> U
        \<Longrightarrow> Functional_Transformation_Functor (DynArr addr) (DynArr addr') T U (\<lambda>_. UNIV) (\<lambda>x. UNIV)
             (\<lambda>f. list_all) (\<lambda>f P. map f)\<close>

abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {data: \<p>\<t>\<r>, len: \<a>\<i>\<n>\<t>, cap: \<a>\<i>\<n>\<t>}\<close>


proc len_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<close>
  output   \<open>length l \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val ret \<leftarrow> addr.len \<semicolon>
  \<open>MAKE _ (DynArr addr _)\<close> \<semicolon>
  ret
\<medium_right_bracket> .


proc get_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i < length l\<close>
  output   \<open>l!i \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  addr.data[i]
  \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _\<close>
\<medium_right_bracket> .


proc set_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := v] \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  addr.data[i] := v \<semicolon> 
  \<m>\<a>\<k>\<e>\<s> \<open>l[i := v] \<Ztypecolon> (DynArr addr _)\<close>
\<medium_right_bracket> .

proc Max:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  output \<open>max x y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  if (x < y) \<medium_left_bracket> y \<medium_right_bracket> \<medium_left_bracket> x \<medium_right_bracket>
\<medium_right_bracket> .


proc push_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output   \<open>l @ [v] \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val len \<leftarrow> addr.len \<semicolon>
  val cap \<leftarrow> addr.cap \<semicolon>
  if (cap = len) \<medium_left_bracket>
      val cap' \<leftarrow> Max(cap * 2, 1) \<semicolon>
      val data' \<leftarrow> calloc_aN (cap') \<open>T\<close> \<semicolon>
      memcpy_a (data', addr.data, len) \<semicolon>
      mfree (addr.data) \<semicolon>
      addr.data := data' \<semicolon>
      addr.len := addr.len + 1 \<semicolon>
      addr.cap := cap' \<semicolon>
      data'[len] := v \<semicolon>
      \<m>\<a>\<k>\<e>\<s> \<open>l@[v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket> \<medium_left_bracket>
      addr.data[len] := v \<semicolon>
      addr.len := len + 1 \<semicolon>
      \<m>\<a>\<k>\<e>\<s> \<open>l@[v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc concat_dynarr:
  input   \<open>l1 \<Ztypecolon> \<r>\<e>\<f> DynArr addr1 T\<heavy_comma> l2 \<Ztypecolon> \<r>\<e>\<f> DynArr addr2 T\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output  \<open>l1 @ l2 \<Ztypecolon> DynArr addr1 T\<heavy_comma> l2 \<Ztypecolon> DynArr addr2 T\<close>
\<medium_left_bracket>
  val len \<leftarrow> len_dynarr (addr2) \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len)
            \<open>\<lambda>i. l1 @ take i l2 \<Ztypecolon> DynArr addr1 T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    push_dynarr (addr1, get_dynarr (addr2, i))
  \<medium_right_bracket>
\<medium_right_bracket> .


proc pop_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>l \<noteq> []\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output   \<open>last l \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> butlast l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val len \<leftarrow> addr.len - 1 \<semicolon>
  val half_cap \<leftarrow> addr.cap / 2 \<semicolon>
  val ret \<leftarrow> addr.data[len] \<semicolon>
  addr.len := len \<semicolon>
  if (len \<le> half_cap) \<medium_left_bracket>
    holds_fact [simp]: \<open>length ya div 2 = length l - Suc 0\<close>\<semicolon>
    val data' \<leftarrow> calloc_aN (half_cap) \<open>T\<close> \<semicolon>
    memcpy_a (data', addr.data, len) \<semicolon>
    mfree (addr.data) \<semicolon>
    addr.data := data' \<semicolon>
    addr.cap := half_cap \<semicolon>
    \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _\<close>
  \<medium_right_bracket>
  \<medium_left_bracket> \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _\<close> \<medium_right_bracket>
  ret
\<medium_right_bracket> .


proc new_dynarr:
  input  \<open>Void\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output \<open>[] \<Ztypecolon> \<r>\<e>\<f> DynArr addr T \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc1 \<open>\<lbrace> data: Ptr[\<a>\<r>\<r>\<a>\<y>[0] (\<t>\<y>\<p>\<e>\<o>\<f> T)], len: \<nat>, cap: \<nat> \<rbrace>\<close> \<semicolon>
  ret.data := (calloc_aN (0) \<open>T\<close>) \<semicolon>
  \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _\<close> \<semicolon>
  ret
\<medium_right_bracket> .


proc del_dynarr:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  mfree (addr.data) \<semicolon>
  mfree (addr)
\<medium_right_bracket> .

proc map_dynarr:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<close>
  requires C: \<open>\<And>x u. \<p>\<r>\<o>\<c> C u \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> T \<rbrace> \<close>
  output \<open>map f l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_eq_iff_nth_eq nth_append \<semicolon>

  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr ($addr)) \<open>\<lambda>i. (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
     set_dynarr (addr, i, C (get_dynarr (addr, i)))
  \<medium_right_bracket>
\<medium_right_bracket> .

proc exists_dynarr:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<close>
  requires C: \<open>\<And>x u. \<p>\<r>\<o>\<c> C u \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T \<longmapsto> P x \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>
  output \<open>list_ex P l \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> False ;;
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
            \<open>\<lambda>i. l \<Ztypecolon> DynArr addr T\<heavy_comma> list_ex P (take i l) \<Ztypecolon> \<v>\<a>\<r>[zz] \<bool>\<close> \<semicolon>
    \<medium_left_bracket> \<rightarrow> val i \<semicolon>
      zz \<or> C (get_dynarr (addr, i)) \<rightarrow> zz
    \<medium_right_bracket> \<semicolon>
  zz
\<medium_right_bracket> .


proc fold_map_dynarr:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> z0 \<Ztypecolon> \<v>\<a>\<l> U\<close>
  requires [\<phi>reason]: \<open>Semantic_Type U TY\<^sub>U\<close>
       and C: \<open>\<And>x z u v. \<p>\<r>\<o>\<c> C u v \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T\<heavy_comma> z \<Ztypecolon> \<v>\<a>\<l>[v] U \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> g x z \<Ztypecolon> \<v>\<a>\<l> U \<rbrace> \<close>
  output \<open>fold g l z0 \<Ztypecolon> \<v>\<a>\<l> U\<heavy_comma> map f l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> z0 \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
             \<open>\<lambda>i. fold g (take i l) z0 \<Ztypecolon> \<v>\<a>\<r>[zz] U\<heavy_comma> (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    C (get_dynarr (addr, i), zz) \<rightarrow> val x', var zz \<semicolon>
    set_dynarr (addr, i, x')
  \<medium_right_bracket> certified by (auto simp add: list_eq_iff_nth_eq nth_append, auto_sledgehammer,
                  insert \<open>i < length l\<close>, induct i, auto simp add: take_Suc_conv_app_nth) \<semicolon>
  $zz
\<medium_right_bracket> .

text \<open>The Conclusions of above Certification is the following Specification Theorems\<close>

thm len_dynarr_\<phi>app
thm get_dynarr_\<phi>app
thm set_dynarr_\<phi>app
thm push_dynarr_\<phi>app
thm concat_dynarr_\<phi>app
thm pop_dynarr_\<phi>app
thm new_dynarr_\<phi>app
thm del_dynarr_\<phi>app
thm map_dynarr_\<phi>app
thm exists_dynarr_\<phi>app
thm fold_map_dynarr_\<phi>app

text \<open>Semantic Representations of the Programs: \<close>

thm len_dynarr_def
thm get_dynarr_def
thm set_dynarr_def
thm push_dynarr_def
thm concat_dynarr_def
thm pop_dynarr_def
thm new_dynarr_def
thm del_dynarr_def
thm map_dynarr_def
thm exists_dynarr_def
thm fold_map_dynarr_def

end