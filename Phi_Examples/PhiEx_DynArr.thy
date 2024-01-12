theory PhiEx_DynArr
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Mem_C_MI
          PhiStd.PhiStd_Slice
begin

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

abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {data: pointer, len: \<i>\<n>\<t>(size_t), cap: \<i>\<n>\<t>(size_t)}\<close>

context
  fixes TY :: TY
    and T :: \<open>(VAL, 'x) \<phi>\<close>
    and zero :: 'x
  assumes [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY T zero\<close>
begin


proc get_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  premises \<open>i < length l\<close>
  output \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  $addr \<tribullet> data ! \<tribullet> $i !
  \<open>MAKE _ (DynArr addr _ _)\<close>
\<medium_right_bracket> .

proc set_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>i < length l\<close>
  output \<open>l[i := v] \<Ztypecolon> DynArr addr TY T\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  $addr \<tribullet> data ! \<tribullet> $i := $v ;;
 \<open>l[i := v] \<Ztypecolon> MAKE _ (DynArr addr _ _)\<close>
\<medium_right_bracket> .

proc Max:
  input  \<open>x \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
  output \<open>max x y \<Ztypecolon> \<v>\<a>\<l> \<nat>(size_t)\<close>
\<medium_left_bracket>
  if ($x < $y) \<medium_left_bracket> $y \<medium_right_bracket> \<medium_left_bracket> $x \<medium_right_bracket>
\<medium_right_bracket> .

proc push_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>length l \<le> 2^(addrspace_bits-2) \<and> 2 \<le> addrspace_bits\<close>
  output \<open>l @ [v] \<Ztypecolon> DynArr addr TY T\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  val len \<leftarrow> $addr \<tribullet> len ! ;;
  val cap \<leftarrow> $addr \<tribullet> cap ! ;;
  if ($cap = $len) \<medium_left_bracket>
      val cap' \<leftarrow> Max($cap * 2, 1) ;;
      val data' \<leftarrow> calloc_N ($cap') \<open>T\<close> ;;
      memcpy ($data', $addr \<tribullet> data !, $len) ;;
      mfree ($addr \<tribullet> data !) ;;
      $addr \<tribullet> data := $data' ;;
      $addr \<tribullet> len := $addr \<tribullet> len ! + 1 ;;
      $addr \<tribullet> cap := $cap' ;;
      $data' \<tribullet> $len := $v ;;
      \<open>l@[v] \<Ztypecolon> MAKE _ (DynArr addr _ _)\<close>
  \<medium_right_bracket> \<medium_left_bracket>
      $addr \<tribullet> data ! \<tribullet> $len := $v ;;
      $addr \<tribullet> len := $len + 1 ;;
      \<open>l@[v] \<Ztypecolon> MAKE _ (DynArr addr _ _)\<close>
  \<medium_right_bracket>
\<medium_right_bracket> .

proc pop_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> v \<Ztypecolon> \<v>\<a>\<l> T\<close>
  premises \<open>l \<noteq> [] \<and> 2 \<le> addrspace_bits\<close>
  output \<open>butlast l \<Ztypecolon> DynArr addr TY T\<heavy_comma> last l \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  val len \<leftarrow> $addr \<tribullet> len ! - 1 ;;
  val half_cap \<leftarrow> ($addr \<tribullet> cap !) / 2 ;;
  val ret \<leftarrow> $addr \<tribullet> data ! \<tribullet> $len ! ;;
  $addr \<tribullet> len := $len ;;
  if ($len \<le> $half_cap) \<medium_left_bracket>
  (* ^ if we use ($len * 2 \<le> $cap) instead, it can cause fatal overflow when addrspace_bits is small *)
    val data' \<leftarrow> calloc_N ($half_cap) \<open>T\<close> ;;
    memcpy ($data', $addr \<tribullet> data !, $len) ;;
    mfree ($addr \<tribullet> data !) ;;
    $addr \<tribullet> data := $data' ;;
    $addr \<tribullet> cap := $half_cap ;;
    \<open>MAKE _ (DynArr addr _ _)\<close>
  \<medium_right_bracket>
  \<medium_left_bracket> \<open>MAKE _ (DynArr addr _ _)\<close> \<medium_right_bracket>
  $ret
\<medium_right_bracket> .

proc new_dynarr:
  input  \<open>Void\<close>
  output \<open>[] \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r> \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  val ret \<leftarrow> calloc_1 \<open>\<lbrace> data: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[0] TY, len: \<nat>(size_t), cap: \<nat>(size_t) \<rbrace>\<close> ;;
  $ret \<tribullet> data := (calloc_N (\<open>0 \<Ztypecolon> \<nat>(size_t)\<close>) \<open>T\<close>) ;;
  \<open>MAKE _ (DynArr addr _ _)\<close> ;;
  $ret
\<medium_right_bracket> .

proc del_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  mfree ($addr \<tribullet> data !) ;;
  mfree ($addr)
\<medium_right_bracket> .


ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' get_dynarr_def})))\<close>
ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' set_dynarr_def})))\<close>
ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' Max_def})))\<close>
ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' push_dynarr_def})))\<close>
ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' pop_dynarr_def})))\<close>
ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' new_dynarr_def})))\<close>
ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' del_dynarr_def})))\<close>

end


end