theory Dynamic_Array
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Mem_C_MI
          PhiStd.PhiStd_Slice
begin

declare [[\<phi>trace_reasoning = 1]]

\<phi>type_def DynArr :: \<open>address \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x list) \<phi>\<close>
  where \<open>l \<Ztypecolon> DynArr addr T \<equiv> (a\<^sub>D, len, cap) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> data: TypedPtr (\<a>\<r>\<r>\<a>\<y>[cap] (\<t>\<y>\<p>\<e>\<o>\<f> T)), len: \<nat>(\<s>\<i>\<z>\<e>_\<t>), cap: \<nat>(\<s>\<i>\<z>\<e>_\<t>) \<rbrace>\<heavy_comma>
                             data \<Ztypecolon> \<m>\<e>\<m>[a\<^sub>D] \<bbbA>\<r>\<r>\<a>\<y>[cap] T
                             \<s>\<u>\<b>\<j> a\<^sub>D len cap data. len = length l \<and> cap = length data \<and>
                                                  len \<le> cap \<and> (cap = 0 \<or> cap < 2 * len) \<and>
                                                  take len data = l \<and> address_to_base a\<^sub>D \<and> address_to_base addr \<and>
                                                  \<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {data: \<p>\<t>\<r>, len: \<s>\<i>\<z>\<e>_\<t>, cap: \<s>\<i>\<z>\<e>_\<t>} \<and>
                                                  \<t>\<y>\<p>\<e>\<o>\<f> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>

  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0 \<and> \<t>\<y>\<p>\<e>\<o>\<f> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr T) (list_all2 eq)\<close>
            (tactic: auto, subgoal' for x xa xb xc \<open>rule exI[where x=\<open>xa @ drop (length xa) xc\<close>]\<close>)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<t>\<y>\<p>\<e>\<o>\<f> T = \<t>\<y>\<p>\<e>\<o>\<f> U \<and> addr' = addr)
         \<Longrightarrow> Transformation_Functor (DynArr addr) (DynArr addr') T U (\<lambda>_. UNIV) (\<lambda>_. UNIV) list_all2\<close>
       (*and Functional_Transformation_Functor*)
       and Pointer_Of


abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {data: \<p>\<t>\<r>, len: \<s>\<i>\<z>\<e>_\<t>, cap: \<s>\<i>\<z>\<e>_\<t>}\<close>


proc len_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<close>
  output   \<open>length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  addr.len
\<medium_right_bracket> .

declare [[\<phi>infer_requirements, \<phi>trace_reasoning = 1]]

(*
context
  fixes T :: \<open>(VAL, 'x) \<phi>\<close>
    and zero :: 'x
  assumes [\<phi>reason add]: \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
begin
*)


proc get_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>
  premises \<open>i < length l\<close>
  output   \<open>l!i \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  addr.data[i]
\<medium_right_bracket> .


proc set_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := v] \<Ztypecolon> DynArr addr T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  addr.data[i] := v
\<medium_right_bracket> .

proc Max:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>
  output \<open>max x y \<Ztypecolon> \<v>\<a>\<l> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>
\<medium_left_bracket>
  if (x < y) \<medium_left_bracket> y \<medium_right_bracket> \<medium_left_bracket> x \<medium_right_bracket>
\<medium_right_bracket> .


proc push_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>length l \<le> 2^(addrspace_bits-2) \<and> 2 \<le> addrspace_bits\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output   \<open>l + [v] \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
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
      \<m>\<a>\<k>\<e>\<s> \<open>l + [v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket> \<medium_left_bracket>
      addr.data[len] := v \<semicolon>
      addr.len := len + 1 \<semicolon>
      \<m>\<a>\<k>\<e>\<s> \<open>l + [v] \<Ztypecolon> DynArr addr _\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc concat_dynarr:
  input   \<open>l1 \<Ztypecolon> \<r>\<e>\<f> DynArr addr1 T\<heavy_comma> l2 \<Ztypecolon> \<r>\<e>\<f> DynArr addr2 T\<close>
  premises \<open>length l1 + length l2 < 2^(addrspace_bits-2) \<and> 2 \<le> addrspace_bits\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output  \<open>l1 + l2 \<Ztypecolon> DynArr addr1 T\<heavy_comma> l2 \<Ztypecolon> DynArr addr2 T\<close>
\<medium_left_bracket>
  val len \<leftarrow> len_dynarr (addr2) \<semicolon>

  iterate (0, len) \<open>\<lambda>i. l1 + take i l2 \<Ztypecolon> DynArr addr1 T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    push_dynarr (addr1, get_dynarr (addr2, i))
  \<medium_right_bracket>
\<medium_right_bracket> .

proc pop_dynarr:
  input    \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>l \<noteq> [] \<and> 2 \<le> addrspace_bits\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output   \<open>last l \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> butlast l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val len \<leftarrow> addr.len - 1 \<semicolon>
  val half_cap \<leftarrow> addr.cap / 2 \<semicolon>
  val ret \<leftarrow> addr.data[len] \<semicolon>
  addr.len := len \<semicolon>
  if (len \<le> half_cap) \<medium_left_bracket>
    holds_fact [simp]: \<open>length l - Suc 0 = length ya div 2\<close> \<semicolon>
    val data' \<leftarrow> calloc (half_cap) \<open>T\<close> \<semicolon>
    memcpy (data', addr.data, len) \<semicolon>
    mfree (addr.data) \<semicolon>
    addr.data := data' \<semicolon>
    addr.cap := half_cap \<semicolon> 
    \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _\<close>
  \<medium_right_bracket> \<medium_left_bracket> 
    \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _\<close>
  \<medium_right_bracket>
  ret
\<medium_right_bracket> .


proc new_dynarr:
  input  \<open>Void\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  requires \<open>Semantic_Zero_Val (\<t>\<y>\<p>\<e>\<o>\<f> T) T zero\<close>
  output \<open>[] \<Ztypecolon> \<r>\<e>\<f> DynArr addr T \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc1 \<open>\<lbrace> data: Ptr[\<a>\<r>\<r>\<a>\<y>[0] (\<t>\<y>\<p>\<e>\<o>\<f> T)], len: \<nat>(\<s>\<i>\<z>\<e>_\<t>), cap: \<nat>(\<s>\<i>\<z>\<e>_\<t>) \<rbrace>\<close> \<semicolon>
  ret.data := (calloc (\<open>0 \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>) \<open>T\<close>) \<semicolon>
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
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>, len_dynarr (addr)) \<open>\<lambda>i. (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
     set_dynarr (addr, i, C (get_dynarr (addr, i)))
  \<medium_right_bracket> \<semicolon>
\<medium_right_bracket> .

proc exists_dynarr:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<close>
  requires C: \<open>\<And>x u. \<p>\<r>\<o>\<c> C u \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T \<longmapsto> P x \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>
  output \<open>list_ex P l \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> False \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>, len_dynarr (addr)) \<open>\<lambda>i. l \<Ztypecolon> DynArr addr T\<heavy_comma> list_ex P (take i l) \<Ztypecolon> \<v>\<a>\<r>[zz] \<bool>\<close>
    \<medium_left_bracket> \<rightarrow> val i \<semicolon>
      zz \<or> C (get_dynarr (addr, i)) \<rightarrow> zz
    \<medium_right_bracket> \<semicolon>
  zz
\<medium_right_bracket> .


proc fold_map_dynarr:
  input  \<open>l \<Ztypecolon> \<r>\<e>\<f> DynArr addr T\<heavy_comma> z0 \<Ztypecolon> \<v>\<a>\<l> U\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> U \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  requires C: \<open>\<And>x z u v. \<p>\<r>\<o>\<c> C u v \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T\<heavy_comma> z \<Ztypecolon> \<v>\<a>\<l>[v] U \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> g x z \<Ztypecolon> \<v>\<a>\<l> U \<rbrace> \<close>
  output \<open>fold g l z0 \<Ztypecolon> \<v>\<a>\<l> U\<heavy_comma> map f l \<Ztypecolon> DynArr addr T\<close>
\<medium_left_bracket>
  var zz \<leftarrow> z0 \<semicolon>
  iterate (\<open>0 \<Ztypecolon> \<nat>(\<s>\<i>\<z>\<e>_\<t>)\<close>, len_dynarr (addr))
           \<open>\<lambda>i. fold g (take i l) z0 \<Ztypecolon> \<v>\<a>\<r>[zz] U\<heavy_comma> (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    C (get_dynarr (addr, i), zz) \<rightarrow> val x', var zz ;;
    set_dynarr (addr, i, x')
  \<medium_right_bracket> certified by (auto simp add: list_eq_iff_nth_eq nth_append, auto_sledgehammer,
                  insert \<open>i < length l\<close>, induct i, auto simp add: take_Suc_conv_app_nth) ;;
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