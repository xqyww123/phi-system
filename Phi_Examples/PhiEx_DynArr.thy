theory PhiEx_DynArr
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def DynArr :: \<open>logaddr \<Rightarrow> TY \<Rightarrow> (VAL, 'x) \<phi> \<Rightarrow> (fiction, 'x list) \<phi>\<close>
  where \<open>l \<Ztypecolon> DynArr addr TY T \<equiv> (a\<^sub>D, len, cap) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> data: \<Pp>\<t>\<r> \<a>\<r>\<r>\<a>\<y>[cap] TY, len: \<nat>, cap: \<nat> \<rbrace>\<heavy_comma>
                                data \<Ztypecolon> \<m>\<e>\<m>[a\<^sub>D] \<Aa>\<r>\<r>\<a>\<y>[cap] T
                                \<s>\<u>\<b>\<j> a\<^sub>D len cap data. len = length l \<and> cap = length data \<and> len \<le> cap \<and>
                                                     take len data = l \<close>
  deriving \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr TY T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0)\<close>
       and \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr TY T) (list_all2 eq)\<close>
            (tactic: auto, subgoal' for x xa xb xc \<open>rule exI[where x=\<open>xa @ drop (length xa) xc\<close>]\<close>)
       and \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> TY' = TY \<and> addr' = addr
         \<Longrightarrow> Transformation_Functor (DynArr addr TY) (DynArr addr' TY') T U (\<lambda>_. UNIV) (\<lambda>_. UNIV) list_all2\<close>
       and Functional_Transformation_Functor

term t1

abbreviation \<open>\<d>\<y>\<n>\<a>\<r>\<r> \<equiv> \<s>\<t>\<r>\<u>\<c>\<t> {data: pointer, len: \<a>\<i>\<n>\<t>, cap: \<a>\<i>\<n>\<t>}\<close>



context
  fixes TY :: TY
    and T :: \<open>(VAL, 'x) \<phi>\<close>
  assumes [\<phi>reason add]: \<open>\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY\<close>
begin


proc get_dynarr:
  input  \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<Pp>\<t>\<r> \<d>\<y>\<n>\<a>\<r>\<r>\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>i < length l\<close>
  output \<open>l \<Ztypecolon> DynArr addr TY T\<heavy_comma> l!i \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> ;;
  $addr \<tribullet> data ! \<tribullet> $i !
  \<open>MAKE _ (DynArr addr _ _)\<close>
\<medium_right_bracket> .




end






term \<open>Transformation_Functor (DynArr addr TY) (DynArr addr TY) T U set (\<lambda>_. UNIV) list_all2\<close>



term \<open>Object_Equiv T eq \<Longrightarrow> Object_Equiv (DynArr addr TY T) (list_all2 eq)\<close>

term \<open>Abstract_Domain T P \<Longrightarrow> Abstract_Domain (DynArr addr TY T) (\<lambda>l. list_all P l \<and> addr \<noteq> 0)\<close>

end