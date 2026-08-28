theory Dynamic_Array_arbi_len
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Mem_C_AI
          PhiStd.PhiStd_Slice_a
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

















\<phi>type_def DynArr :: \<open>address \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x list) \<phi>\<close>
  where \<open>l \<Ztypecolon> DynArr addr T \<equiv> (a\<^sub>D, len, cap) \<Ztypecolon> \<mem>[addr] \<lbrace> data: Ptr[\<array>[cap] \<typeof> T], len: \<nat>, cap: \<nat> \<rbrace>\<heavy_comma>
                              data \<Ztypecolon> \<mem>[a\<^sub>D] \<Array>[cap] T
                              \<subj> a\<^sub>D len cap data. len = length l \<and> cap = length data \<and>
                                                   len \<le> cap \<and> (cap = 0 \<or> cap < 2 * len) \<and>
                                                   take len data = l \<and> address_to_base a\<^sub>D \<and> address_to_base addr \<and>
                                                   \<typeof> addr = \<struct> {data: \<ptr>, len: \<aint>, cap: \<aint>} \<and>
                                                   \<typeof> T \<noteq> \<poison> \<close>

  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0 \<and> \<typeof> T \<noteq> \<poison>)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr T) (list_all2 eq)\<close>
            (tactic: auto, subgoal' for x xa xb xc \<open>rule exI[where x=\<open>xa @ drop (length xa) xc\<close>]\<close>)
       and \<open> \<condition> (addr' = addr)
         \<Longrightarrow> \<premise> \<typeof> T = \<typeof> U
         \<Longrightarrow> Transformation_Functor (DynArr addr) (DynArr addr') T U (\<lambda>_. UNIV) (\<lambda>_. UNIV) list_all2\<close>
       
       (*and Functional_Transformation_Functor*)
       and Pointer_Of
       and \<open>\<guard> \<condition> addr = addr'
        \<Longrightarrow> \<premise> \<typeof> T = \<typeof> U
        \<Longrightarrow> Functional_Transformation_Functor (DynArr addr) (DynArr addr') T U (\<lambda>_. UNIV) (\<lambda>x. UNIV)
             (\<lambda>f. list_all) (\<lambda>f P. map f)\<close>

abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<struct> {data: \<ptr>, len: \<aint>, cap: \<aint>}\<close>


proc len_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<close>
  output   \<open>length l \<Ztypecolon> \<val> \<nat>\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
  val ret \<leftarrow> addr.len \<semicolon>
  \<open>MAKE _ (DynArr addr _)\<close> \<semicolon>
  ret
\<medium_right_bracket> .


proc get_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<val> \<nat>\<close>
  premises \<open>i < length l\<close>
  output   \<open>l!i \<Ztypecolon> \<val> T\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
  addr.data[i]
  \<makes> \<open>DynArr addr _\<close>
\<medium_right_bracket> .


proc set_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<val> \<nat>\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := v] \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
  addr.data[i] := v \<semicolon> 
  \<makes> \<open>l[i := v] \<Ztypecolon> (DynArr addr _)\<close>
\<medium_right_bracket> .

proc Max:
  input  \<open>x \<Ztypecolon> \<val> \<nat>\<heavy_comma> y \<Ztypecolon> \<val> \<nat>\<close>
  output \<open>max x y \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  if (x < y) \<medium_left_bracket> y \<medium_right_bracket> \<medium_left_bracket> x \<medium_right_bracket>
\<medium_right_bracket> .


proc push_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output   \<open>l @ [v] \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
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
      \<makes> \<open>l@[v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket> \<medium_left_bracket>
      addr.data[len] := v \<semicolon>
      addr.len := len + 1 \<semicolon>
      \<makes> \<open>l@[v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc concat_dynarr:
  input   \<open>l1 \<Ztypecolon> \<ref> DynArr addr1 T\<heavy_comma> l2 \<Ztypecolon> \<ref> DynArr addr2 T\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
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
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  premises \<open>l \<noteq> []\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output   \<open>last l \<Ztypecolon> \<val> T\<heavy_comma> butlast l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
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
    \<makes> \<open>DynArr addr _\<close>
  \<medium_right_bracket>
  \<medium_left_bracket> \<makes> \<open>DynArr addr _\<close> \<medium_right_bracket>
  ret
\<medium_right_bracket> .


proc new_dynarr:
  input  \<open>Void\<close>
  premises \<open>\<typeof> T \<noteq> \<poison>\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output \<open>[] \<Ztypecolon> \<ref> DynArr addr T \<subj> addr. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc1 \<open>\<lbrace> data: Ptr[\<array>[0] (\<typeof> T)], len: \<nat>, cap: \<nat> \<rbrace>\<close> \<semicolon>
  ret.data := (calloc_aN (0) \<open>T\<close>) \<semicolon>
  \<makes> \<open>DynArr addr _\<close> \<semicolon>
  ret
\<medium_right_bracket> .


proc del_dynarr:
  input  \<open>l \<Ztypecolon> \<ref> DynArr addr T\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
  mfree (addr.data) \<semicolon>
  mfree (addr)
\<medium_right_bracket> .

proc map_dynarr:
  input  \<open>l \<Ztypecolon> \<ref> DynArr addr T\<close>
  requires C: \<open>\<And>x u. \<proc> C u \<lbrace> x \<Ztypecolon> \<val>[u] T \<longmapsto> f x \<Ztypecolon> \<val> T \<rbrace> \<close>
  output \<open>map f l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_eq_iff_nth_eq nth_append \<semicolon>

  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr ($addr)) \<open>\<lambda>i. (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
     set_dynarr (addr, i, C (get_dynarr (addr, i)))
  \<medium_right_bracket>
\<medium_right_bracket> .

proc exists_dynarr:
  input  \<open>l \<Ztypecolon> \<ref> DynArr addr T\<close>
  requires C: \<open>\<And>x u. \<proc> C u \<lbrace> x \<Ztypecolon> \<val>[u] T \<longmapsto> P x \<Ztypecolon> \<val> \<bool> \<rbrace> \<close>
  output \<open>list_ex P l \<Ztypecolon> \<val> \<bool>\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> False ;;
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
            \<open>\<lambda>i. l \<Ztypecolon> DynArr addr T\<heavy_comma> list_ex P (take i l) \<Ztypecolon> \<var>[zz] \<bool>\<close> \<semicolon>
    \<medium_left_bracket> \<rightarrow> val i \<semicolon>
      zz \<or> C (get_dynarr (addr, i)) \<rightarrow> zz
    \<medium_right_bracket> \<semicolon>
  zz
\<medium_right_bracket> .


proc fold_map_dynarr:
  input  \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> z0 \<Ztypecolon> \<val> U\<close>
  requires [\<phi>reason]: \<open>Semantic_Type U TY\<^sub>U\<close>
       and C: \<open>\<And>x z u v. \<proc> C u v \<lbrace> x \<Ztypecolon> \<val>[u] T\<heavy_comma> z \<Ztypecolon> \<val>[v] U \<longmapsto> f x \<Ztypecolon> \<val> T\<heavy_comma> g x z \<Ztypecolon> \<val> U \<rbrace> \<close>
  output \<open>fold g l z0 \<Ztypecolon> \<val> U\<heavy_comma> map f l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> z0 \<semicolon>
  iterate_a (\<open>0 \<Ztypecolon> \<nat>\<close>, len_dynarr (addr))
             \<open>\<lambda>i. fold g (take i l) z0 \<Ztypecolon> \<var>[zz] U\<heavy_comma> (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    C (get_dynarr (addr, i), zz) \<rightarrow> val x', var zz \<semicolon>
    set_dynarr (addr, i, x')
  \<medium_right_bracket> 
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