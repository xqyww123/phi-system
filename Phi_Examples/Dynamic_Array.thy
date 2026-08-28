theory Dynamic_Array
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Mem_C_MI
          PhiStd.PhiStd_Slice
begin

\<phi>type_def DynArr
  where \<open>l \<Ztypecolon> DynArr addr T \<equiv> (a\<^sub>D, len, cap) \<Ztypecolon> \<obj>[addr] \<lbrace> data: Ptr[\<array>[cap] (\<typeof> T)], len: \<nat>(\<size_t>), cap: \<nat>(\<size_t>) \<rbrace>\<heavy_comma>
                             data \<Ztypecolon> \<obj>[a\<^sub>D] \<Array>[cap] T
         \<subj> a\<^sub>D len cap data. len = length l \<and> cap = length data \<and>
                              len \<le> cap \<and> (cap = 0 \<or> cap < 2 * len) \<and>
                              take len data = l \<and>
                              \<typeof> T \<noteq> \<poison> \<close>

  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0 \<and> \<typeof> T \<noteq> \<poison>)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr T) (list_all2 eq)\<close>
       and \<open> \<condition> (\<typeof> T = \<typeof> U \<and> addr' = addr)
         \<Longrightarrow> Transformation_Functor (DynArr addr) (DynArr addr') T U (\<lambda>_. UNIV) (\<lambda>_. UNIV) list_all2\<close>
       and Pointer_Of


abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<struct> {data: \<ptr>, len: \<size_t>, cap: \<size_t>}\<close>



proc len_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<close>
  output   \<open>length l \<Ztypecolon> \<val> \<nat>(\<size_t>)\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  addr.len
\<medium_right_bracket> .


proc get_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<val> \<nat>(\<size_t>)\<close>
  premises \<open>i < length l\<close>
  output   \<open>l!i \<Ztypecolon> \<val> T\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  addr.data[i]
\<medium_right_bracket> .


proc set_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<val> \<nat>(\<size_t>)\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := v] \<Ztypecolon> DynArr addr T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  addr.data[i] := v
\<medium_right_bracket> .

proc Max:
  input  \<open>x \<Ztypecolon> \<val> \<nat>(\<size_t>)\<heavy_comma> y \<Ztypecolon> \<val> \<nat>(\<size_t>)\<close>
  output \<open>max x y \<Ztypecolon> \<val> \<nat>(\<size_t>)\<close>
\<medium_left_bracket>
  if (x < y) \<medium_left_bracket> y \<medium_right_bracket> \<medium_left_bracket> x \<medium_right_bracket>
\<medium_right_bracket> .


proc push_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  premises \<open>length l \<le> 2^(addrspace_bits-2) \<and> 2 \<le> addrspace_bits\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output   \<open>l + [v] \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
  val len \<leftarrow> addr.len \<semicolon>
  val cap \<leftarrow> addr.cap \<semicolon>
  if (cap = len) \<medium_left_bracket>
      val cap' \<leftarrow> Max(cap * 2, 1) \<semicolon>
      val data' \<leftarrow> calloc (cap') \<open>T\<close> \<semicolon>
      memcpy (data', addr.data , len) \<semicolon>
      mfree (addr.data) \<semicolon>
      addr.data := data' \<semicolon>
      addr.len := addr.len + 1 \<semicolon>
      addr.cap := cap' \<semicolon>
      data'[len] := v \<semicolon>
      \<makes> \<open>l + [v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket> \<medium_left_bracket>
      addr.data[len] := v \<semicolon>
      addr.len := len + 1 \<semicolon>
      \<makes> \<open>l + [v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc concat_dynarr:
  input   \<open>l1 \<Ztypecolon> \<ref> DynArr addr1 T\<heavy_comma> l2 \<Ztypecolon> \<ref> DynArr addr2 T\<close>
  premises \<open>length l1 + length l2 < 2^(addrspace_bits-2) \<and> 2 \<le> addrspace_bits\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output  \<open>l1 + l2 \<Ztypecolon> DynArr addr1 T\<heavy_comma> l2 \<Ztypecolon> DynArr addr2 T\<close>
\<medium_left_bracket>
  val len \<leftarrow> len_dynarr (addr2) \<semicolon>

  iterate (0, len) \<open>\<lambda>i. l1 + take i l2 \<Ztypecolon> DynArr addr1 T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    push_dynarr (addr1, get_dynarr (addr2, i))
  \<medium_right_bracket>
\<medium_right_bracket> .

proc pop_dynarr:
  input    \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<val> T\<close>
  premises \<open>l \<noteq> [] \<and> 2 \<le> addrspace_bits\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output   \<open>last l \<Ztypecolon> \<val> T\<heavy_comma> butlast l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  transforms_to \<open'> \<semicolon>
  val len \<leftarrow> addr.len - 1 \<semicolon>
  val half_cap \<leftarrow> addr.cap / 2 \<semicolon>
  val ret \<leftarrow> addr.data[len] \<semicolon>
  addr.len := len \<semicolon>
  if (len \<le> half_cap) \<medium_left_bracket>
    val data' \<leftarrow> calloc (half_cap) \<open>T\<close> \<semicolon>
    memcpy (data', addr.data, len) \<semicolon>
    mfree (addr.data) \<semicolon>
    addr.data := data' \<semicolon>
    addr.cap := half_cap \<semicolon> 
    \<makes> \<open>DynArr addr _\<close>
  \<medium_right_bracket> \<medium_left_bracket> 
    \<makes> \<open>DynArr addr _\<close>
  \<medium_right_bracket>
  ret
\<medium_right_bracket> .


proc new_dynarr:
  input  \<open>Void\<close>
  premises \<open>\<typeof> T \<noteq> \<poison>\<close>
  requires \<open>Semantic_Zero_Val (\<typeof> T) T zero\<close>
  output \<open>[] \<Ztypecolon> \<ref> DynArr addr T \<subj> addr. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc1 \<open>\<lbrace> data: Ptr[\<array>[0] (\<typeof> T)], len: \<nat>(\<size_t>), cap: \<nat>(\<size_t>) \<rbrace>\<close> \<semicolon>
  ret.data := (calloc (\<open>0 \<Ztypecolon> \<nat>(\<size_t>)\<close>) \<open>T\<close>) \<semicolon>
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
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<size_t>)\<close>, len_dynarr (addr)) \<open>\<lambda>i. (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
     set_dynarr (addr, i, C (get_dynarr (addr, i)))
  \<medium_right_bracket> \<semicolon>
\<medium_right_bracket> .

proc exists_dynarr:
  input  \<open>l \<Ztypecolon> \<ref> DynArr addr T\<close>
  requires C: \<open>\<And>x u. \<proc> C u \<lbrace> x \<Ztypecolon> \<val>[u] T \<longmapsto> P x \<Ztypecolon> \<val> \<bool> \<rbrace> \<close>
  output \<open>list_ex P l \<Ztypecolon> \<val> \<bool>\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> False \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<size_t>)\<close>, len_dynarr (addr)) \<open>\<lambda>i. l \<Ztypecolon> DynArr addr T\<heavy_comma> list_ex P (take i l) \<Ztypecolon> \<var>[zz] \<bool>\<close>
    \<medium_left_bracket> \<rightarrow> val i \<semicolon>
      zz \<or> C (get_dynarr (addr, i)) \<rightarrow> zz
    \<medium_right_bracket> \<semicolon>
  zz
\<medium_right_bracket> .


proc fold_map_dynarr:
  input  \<open>l \<Ztypecolon> \<ref> DynArr addr T\<heavy_comma> z0 \<Ztypecolon> \<val> U\<close>
  premises \<open>\<typeof> U \<noteq> \<poison>\<close>
  requires C: \<open>\<And>x z u v. \<proc> C u v \<lbrace> x \<Ztypecolon> \<val>[u] T\<heavy_comma> z \<Ztypecolon> \<val>[v] U \<longmapsto> f x \<Ztypecolon> \<val> T\<heavy_comma> g x z \<Ztypecolon> \<val> U \<rbrace> \<close>
  output \<open>fold g l z0 \<Ztypecolon> \<val> U\<heavy_comma> map f l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> z0 \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<size_t>)\<close>, len_dynarr (addr))
           \<open>\<lambda>i. fold g (take i l) z0 \<Ztypecolon> \<var>[zz] U\<heavy_comma> (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    C (get_dynarr (addr, i), zz) \<rightarrow> val x', var zz ;;
    set_dynarr (addr, i, x')
  \<medium_right_bracket>
  zz
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