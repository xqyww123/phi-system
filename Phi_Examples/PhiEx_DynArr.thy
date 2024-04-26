theory PhiEx_DynArr
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Mem_C_MI
          PhiStd.PhiStd_Slice
begin

\<phi>reasoner_group DynArr = (100,[0,9999]) \<open>derived reasoning rules of DynArr\<close>

declare [[collect_reasoner_statistics DynArr start,
         \<phi>LPR_collect_statistics derivation start]]


\<phi>type_def DynArr :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x list) \<phi>\<close>
  where \<open>l \<Ztypecolon> DynArr addr TY T \<equiv> data \<Ztypecolon> \<m>\<e>\<m>[a\<^sub>D] \<Aa>\<r>\<r>\<a>\<y>[cap] T\<heavy_comma>
                                (a\<^sub>D, len, cap) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> data: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[cap] TY, len: \<nat>(size_t), cap: \<nat>(size_t) \<rbrace>
                                \<s>\<u>\<b>\<j> a\<^sub>D len cap data. len = length l \<and> cap = length data \<and>
                                                     len \<le> cap \<and> (cap = 0 \<or> cap < 2 * len) \<and>
                                                     take len data = l \<and> address_to_base a\<^sub>D \<and> address_to_base addr\<close>

  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr TY T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr TY T) (list_all2 eq)\<close>
            (tactic: auto, subgoal' for x xa xb xc \<open>rule exI[where x=\<open>xa @ drop (length xa) xc\<close>]\<close>)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (DynArr addr TY) (DynArr addr' TY') T U (\<lambda>_. UNIV) (\<lambda>_. UNIV) list_all2\<close>
       and Functional_Transformation_Functor


declare [[collect_reasoner_statistics DynArr stop,
         \<phi>LPR_collect_statistics derivation stop]]

ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %DynArr})) "derivation"\<close>


abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {data: pointer, len: \<i>\<n>\<t>(size_t), cap: \<i>\<n>\<t>(size_t)}\<close>

declare [[\<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics,
          recording_timing_of_semantic_operation,
          \<phi>async_proof = false]]

(*
ML \<open>PLPR_Statistics.reset_utilization_statistics_all ()\<close>
*)

proc len_dynarr:
  input    \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close>
  output   \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  $addr \<tribullet> len !
\<medium_right_bracket> .


context
  fixes TY :: TY
    and T :: \<open>(VAL, 'x) \<phi>\<close>                              \<comment> \<open>we provide a generic verification\<close>
    and zero :: 'x
  assumes [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>      \<comment> \<open>specify the semantic type of T\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY T zero\<close>  \<comment> \<open>specify the semantic zero value of T\<close>
begin

proc get_dynarr:
  input    \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  premises \<open>i < length l\<close>
  output   \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  $addr \<tribullet> data ! \<tribullet> $i !
\<medium_right_bracket> .


proc set_dynarr:
  input    \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output   \<open>l[i := v] \<Ztypecolon> DynArr addr TY T\<close>
  unfolding DynArr.unfold
\<medium_left_bracket>
  $addr \<tribullet> data ! \<tribullet> $i := $v
\<medium_right_bracket> .

proc Max:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  output \<open>max x y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
\<medium_left_bracket>
  if ($x < $y) \<medium_left_bracket> $y \<medium_right_bracket> \<medium_left_bracket> $x \<medium_right_bracket>
\<medium_right_bracket> .


proc push_dynarr:
  input    \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>length l \<le> 2^(addrspace_bits-2) \<and> 2 \<le> addrspace_bits\<close>
  output   \<open>l @ [v] \<Ztypecolon> DynArr addr TY T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val len \<leftarrow> $addr \<tribullet> len ! \<semicolon>
  val cap \<leftarrow> $addr \<tribullet> cap ! \<semicolon>
  if ($cap = $len) \<medium_left_bracket>
      val cap' \<leftarrow> Max($cap * 2, 1) \<semicolon>
      val data' \<leftarrow> calloc_N ($cap') \<open>T\<close> \<semicolon>
      memcpy ($data', $addr \<tribullet> data !, $len) \<semicolon>
      mfree ($addr \<tribullet> data !) \<semicolon>
      $addr \<tribullet> data := $data' \<semicolon>
      $addr \<tribullet> len := $addr \<tribullet> len ! + 1 \<semicolon>
      $addr \<tribullet> cap := $cap' \<semicolon>
      $data' \<tribullet> $len := $v \<semicolon>
      \<m>\<a>\<k>\<e>\<s> \<open>l@[v] \<Ztypecolon> DynArr addr _ _\<close>
  \<medium_right_bracket> \<medium_left_bracket>
      $addr \<tribullet> data ! \<tribullet> $len := $v \<semicolon>
      $addr \<tribullet> len := $len + 1 \<semicolon>
      \<m>\<a>\<k>\<e>\<s> \<open>l@[v] \<Ztypecolon> DynArr addr _ _\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc concat_dynarr:
  input   \<open>l1 \<Ztypecolon> DynArr addr1 TY T\<heavy_comma> l2 \<Ztypecolon> DynArr addr2 TY T\<heavy_comma>
           addr1 \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> addr2 \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close>
  premises \<open>length l1 + length l2 < 2^(addrspace_bits-2) \<and> 2 \<le> addrspace_bits\<close>
  output  \<open>l1 @ l2 \<Ztypecolon> DynArr addr1 TY T\<heavy_comma> l2 \<Ztypecolon> DynArr addr2 TY T\<close>
\<medium_left_bracket>
  val len \<leftarrow> len_dynarr ($addr2) \<semicolon>

  replicate (\<open>0 \<Ztypecolon> \<nat>(size_t)\<close>, $len) \<open>\<lambda>i. l1 @ take i l2 \<Ztypecolon> DynArr addr1 TY T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    push_dynarr ($addr1, get_dynarr ($addr2, $i))
  \<medium_right_bracket>
\<medium_right_bracket> .


proc pop_dynarr:
  input    \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>l \<noteq> [] \<and> 2 \<le> addrspace_bits\<close>
  output   \<open>butlast l \<Ztypecolon> DynArr addr TY T\<heavy_comma> last l \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  val len \<leftarrow> $addr \<tribullet> len ! - 1 \<semicolon>
  val half_cap \<leftarrow> ($addr \<tribullet> cap !) / 2 \<semicolon>
  val ret \<leftarrow> $addr \<tribullet> data ! \<tribullet> $len ! \<semicolon>
  $addr \<tribullet> len := $len \<semicolon>
  if ($len \<le> $half_cap) \<medium_left_bracket>
    val data' \<leftarrow> calloc_N ($half_cap) \<open>T\<close> \<semicolon>
    memcpy ($data', $addr \<tribullet> data !, $len) \<semicolon>
    mfree ($addr \<tribullet> data !) \<semicolon>
    $addr \<tribullet> data := $data' \<semicolon>
    $addr \<tribullet> cap := $half_cap \<semicolon>
    \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _ _\<close>
  \<medium_right_bracket>
  \<medium_left_bracket> \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _ _\<close> \<medium_right_bracket>
  $ret
\<medium_right_bracket> .


proc new_dynarr:
  input  \<open>Void\<close>
  output \<open>[] \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r> \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc_1 \<open>\<lbrace> data: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[0] TY, len: \<nat>(size_t), cap: \<nat>(size_t) \<rbrace>\<close> \<semicolon>
  $ret \<tribullet> data := (calloc_N (\<open>0 \<Ztypecolon> \<nat>(size_t)\<close>) \<open>T\<close>) \<semicolon>
  \<m>\<a>\<k>\<e>\<s> \<open>DynArr addr _ _\<close> \<semicolon>
  $ret
\<medium_right_bracket> .


proc del_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s>_\<t>\<o> \<o>\<p>\<e>\<n> \<semicolon>
  mfree ($addr \<tribullet> data !) \<semicolon>
  mfree ($addr)
\<medium_right_bracket> .

proc map_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close>
  requires C: \<open>\<And>x u. \<p>\<r>\<o>\<c> C u \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> T \<rbrace> \<close>
  output \<open>map f l \<Ztypecolon> DynArr addr TY T\<close>
\<medium_left_bracket>
  note [\<phi>sledgehammer_simps] = list_eq_iff_nth_eq nth_append \<semicolon>
  replicate (\<open>0 \<Ztypecolon> \<nat>(size_t)\<close>, len_dynarr ($addr)) \<open>\<lambda>i. (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr TY T\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
     set_dynarr ($addr, $i, C (get_dynarr ($addr, $i)))
  \<medium_right_bracket> \<semicolon>
\<medium_right_bracket> .

proc exists_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close>
  requires C: \<open>\<And>x u. \<p>\<r>\<o>\<c> C u \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T \<longmapsto> P x \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>
  output \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> list_ex P l \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
\<medium_left_bracket>
  var zz \<leftarrow> False \<semicolon>
  replicate (\<open>0 \<Ztypecolon> \<nat>(size_t)\<close>, len_dynarr ($addr)) \<open>\<lambda>i. l \<Ztypecolon> DynArr addr TY T\<heavy_comma> list_ex P (take i l) \<Ztypecolon> \<v>\<a>\<r>[zz] \<bool>\<close>
    \<medium_left_bracket> \<rightarrow> val i \<semicolon>
      $zz \<or> C (get_dynarr ($addr, $i)) \<rightarrow> $zz
    \<medium_right_bracket> \<semicolon>
  $zz
\<medium_right_bracket> .


proc fold_map_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> z0 \<Ztypecolon> \<v>\<a>\<l> U\<close>
  requires [\<phi>reason]: \<open>\<And>z. \<phi>SemType (z \<Ztypecolon> U) TY\<^sub>U\<close>
       and C: \<open>\<And>x z u v. \<p>\<r>\<o>\<c> C u v \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[u] T\<heavy_comma> z \<Ztypecolon> \<v>\<a>\<l>[v] U \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> g x z \<Ztypecolon> \<v>\<a>\<l> U \<rbrace> \<close>
  output \<open>map f l \<Ztypecolon> DynArr addr TY T\<heavy_comma> fold g l z0 \<Ztypecolon> \<v>\<a>\<l> U\<close>
\<medium_left_bracket>
  var zz \<leftarrow> $z0 \<semicolon>
  replicate (\<open>0 \<Ztypecolon> \<nat>(size_t)\<close>, len_dynarr ($addr))
            \<open>\<lambda>i. (map f (take i l) @ drop i l) \<Ztypecolon> DynArr addr TY T\<heavy_comma> fold g (take i l) z0 \<Ztypecolon> \<v>\<a>\<r>[zz] U\<close>
  \<medium_left_bracket> \<rightarrow> val i \<semicolon>
    C (get_dynarr ($addr, $i), $zz) \<rightarrow> val x', var zz ;;
    set_dynarr ($addr, $i, $x')
  \<medium_right_bracket> certified by (auto simp add: list_eq_iff_nth_eq nth_append, auto_sledgehammer,
                  insert \<open>i < length l\<close>, induct i, auto simp add: take_Suc_conv_app_nth) ;;
  $zz
\<medium_right_bracket> .

end

declare [[\<phi>LPR_collect_statistics program stop,
          collecting_subgoal_statistics = false,
          recording_timing_of_semantic_operation = false,
          \<phi>async_proof = true]]

(*
ML \<open>PLPR_Statistics.timing_of_semantic_operations () \<close>

ML \<open>fun report_utilization statistic_groups reasoner_groups =
  let open Pretty
      val statistics = Phi_Reasoner.utilization_of_groups_in_all_theories
          (Context.Theory \<^theory>) (map (the o snd) reasoner_groups) statistic_groups
        |> filter (fn (_, i) => i > 0)
   in (length statistics, Integer.sum (map snd statistics))
  end
\<close>

ML \<open>report_utilization ["program"] [@{reasoner_group %all_derived_rules} ] \<close>


ML \<open>report_utilization ["program"] [@{reasoner_group %Field}, @{reasoner_group %Array},
        @{reasoner_group %\<phi>MapAt}, @{reasoner_group %\<phi>MapAt_L}, @{reasoner_group %\<phi>Some},
        @{reasoner_group %Mem_Coercion}, @{reasoner_group %\<phi>Share},
        @{reasoner_group %Resource_Space},
        @{reasoner_group %Var}, @{reasoner_group %MemBlk},
        @{reasoner_group %\<phi>Mul_Quant_Tree},
        @{reasoner_group %DynArr} ] \<close>
*)

end