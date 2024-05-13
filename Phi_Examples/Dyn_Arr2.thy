theor Dyn_Arr2
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Mem_C_AI
          PhiStd.PhiStd_Slice_a
          Phi_Semantics.PhiSem_Int_ArbiPrec
  
begin

term \<open>\<m>\<e>\<m>[a\<^sub>D] \<bbbA>\<r>\<r>\<a>\<y>[cap] \<nat>\<close>
term \<open>\<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[0,cap] \<nat>\<close>
ML \<open>@{term \<open>\<m>\<e>\<m>[a\<^sub>D] \<bbbA>\<r>\<r>\<a>\<y>[cap] \<nat>\<close>}\<close>
ML \<open>@{term \<open>\<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[0,cap] \<nat>\<close>}\<close>
term Mem_Coercion

declare [[ML_print_depth = 100]]

\<phi>type_def DynArr :: \<open>address \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x list) \<phi>\<close>
  where \<open>l \<Ztypecolon> DynArr addr TY T \<equiv> buf \<Ztypecolon> \<m>\<e>\<m>[a\<^sub>D] \<s>\<l>\<i>\<c>\<e>[len,cap-len] (\<top>\<^sub>\<phi> :: (VAL, 'x) \<phi>)\<heavy_comma>
                                l \<Ztypecolon> \<m>\<e>\<m>[a\<^sub>D] \<s>\<l>\<i>\<c>\<e>[0, len] T\<heavy_comma>
                                (a\<^sub>D, len, cap) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> data: \<bbbP>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[cap] TY, len: \<nat>, cap: \<nat> \<rbrace>
                                \<s>\<u>\<b>\<j> a\<^sub>D len cap buf. len = length l \<and>
                                                     len \<le> cap \<and> (cap = 0 \<or> cap < 2 * len) \<and>
                                                     address_to_base a\<^sub>D \<and> address_to_base addr\<close>
  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr TY T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr TY T) (list_all2 eq)\<close>
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (DynArr addr TY) (DynArr addr' TY') T U set (\<lambda>_. UNIV) list_all2\<close>
       and Functional_Transformation_Functor


abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {data: pointer, len: \<a>\<i>\<n>\<t>, cap: \<a>\<i>\<n>\<t>}\<close>


proc len_dynarr:
  input    \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<close>
  output   \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> length l \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> \<semicolon>
  $addr \<tribullet> len !
  \<open>MAKE _ (DynArr addr _ _)\<close>
\<medium_right_bracket> .


context
  fixes TY :: TY
    and T :: \<open>(VAL, 'x) \<phi>\<close>                              \<comment> \<open>we provide a generic verification\<close>
    and zero :: 'x
  assumes [\<phi>reason add]: \<open>Semantic_Type T TY\<close>      \<comment> \<open>specify the semantic type of T\<close>
      and [\<phi>reason add]: \<open>Semantic_Zero_Val TY T zero\<close>  \<comment> \<open>specify the semantic zero value of T\<close>
begin

proc get_dynarr:
  input    \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i < length l\<close>
  output   \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> \<semicolon>
  $addr \<tribullet> data !
thm \<phi>
 ;; \<open>MAKE _ (DynArr addr _ _)\<close>
\<medium_right_bracket> .



end