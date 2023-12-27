theory PhiEx_Slice
  imports Phi_Semantics.PhiSem_C
          "HOL-Combinatorics.List_Permutation"
          PhiStd.PhiStd_Loop
begin

declare One_nat_def[simp del]

term sorted
term permute_list

term \<open>A <~~> B\<close>

declare [[\<phi>trace_reasoning = 0]]


proc qsort:
  input  \<open>l  \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32)\<heavy_comma>
          ptr  \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:i:len] \<i>\<n>\<t>(32)\<heavy_comma>
          len \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  premises [simp]: \<open>ptr = 0\<close>
  output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32) \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
  is [recursive l addr i len]
\<medium_left_bracket>
  if ($len \<le> 1)
  \<medium_left_bracket> \<medium_right_bracket>
  \<medium_left_bracket>
    val pivot \<leftarrow> ($ptr + ($len - 1)) ! ;;
    var d \<leftarrow> 0 ;;
    replicate (0,$len) \<open>\<lambda>n. l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32)\<heavy_comma>
                            d \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(32)
                         \<s>\<u>\<b>\<j> l' d.
                            d \<le> n \<and> l <~~> l' \<and>
                            (\<forall>k<d. l' ! k \<le> ?pivot) \<and>
                            (\<forall>k<n-d. ?pivot < l' ! (d + k)) \<close> 
    \<medium_left_bracket> for n \<rightarrow> val n ;;
      ($ptr + $n)! \<rightarrow> val x ;;
      if ($x \<le> $pivot)
      \<medium_left_bracket>
        ($ptr + $n) := ($ptr + $d)! ;;
        ($ptr + $d) := $x ;;
        $d \<leftarrow> $d + 1
      \<medium_right_bracket>
      \<medium_left_bracket> \<medium_right_bracket> ;;
    \<medium_right_bracket> ;;
    (*readers may inspect \<open>thm useful\<close> to look the contextual facts*)
    (* thm useful *)
    qsort ($ptr + $d, $len - $d
          thm qsort[]
    thm useful
    thm qsort























(*

proc qsort:
  input  \<open>l  \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32)\<heavy_comma>
          j  \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:i:len] \<i>\<n>\<t>(32)\<heavy_comma>
          len \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  premises \<open>j = 0\<close>
  output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,n] \<nat>(32) \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
\<medium_left_bracket>
  if ($len \<le> 1)
  \<medium_left_bracket> \<medium_right_bracket>
  \<medium_left_bracket>
    val pivot \<leftarrow> $j !;;
    var k \<leftarrow> 1 ;;
    while' \<open>k \<Ztypecolon> \<v>\<a>\<r>[k] \<nat>(32)\<heavy_comma>
            low \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,k] \<nat>(32)\<heavy_comma>
            up \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i+k,len-k] \<nat>(32)
            \<s>\<u>\<b>\<j> k low up. Inv: (k \<le> )
                        \<and> Guard: ()\<close>

*)





end