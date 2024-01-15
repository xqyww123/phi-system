theory PhiEx_Slice
  imports Phi_Semantics.PhiSem_C
          "HOL-Combinatorics.List_Permutation"
          PhiStd.PhiStd_Loop
begin

declare [[\<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics,
          recording_timing_of_semantic_operation,
          \<phi>assync_proof = false]]

proc qsort:
  input  \<open>l \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32)\<heavy_comma>
          i \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:LEN] \<i>\<n>\<t>(32)\<heavy_comma> \<comment> \<open>\<open>LEN\<close> is the length of the entire array, which decides
                                            the range of the pointer arithmetic.\<close>
          len \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  premises \<open>i + len \<le> LEN\<close>
  output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32) \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
  is [recursive]
  is [routine]
\<medium_left_bracket>
  if ($len \<le> 1)
  \<medium_left_bracket> return \<medium_right_bracket>
  \<medium_left_bracket>
    val pivot \<leftarrow> ($i + ($len - 1)) ! ;;
    var d \<leftarrow> 0 ;;
    replicate (0,$len) \<open>\<lambda>n. l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32)\<heavy_comma>
                            d \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(32)
                         \<s>\<u>\<b>\<j> l' d.
                            d \<le> n \<and> l <~~> l' \<and>
                            (\<forall>k<d. l' ! k \<le> ?pivot) \<and>
                            (\<forall>k<n-d. ?pivot < l' ! (d + k)) \<close> 
    \<medium_left_bracket> 
      for n \<rightarrow> val n ;;
      ($i + $n)! \<rightarrow> val x ;;
      if ($x \<le> $pivot)
      \<medium_left_bracket>
        ($i + $n) := ($i + $d)! ;;
        ($i + $d) := $x ;;
        $d \<leftarrow> $d + 1
      \<medium_right_bracket>
      \<medium_left_bracket> \<medium_right_bracket> ;;
    \<medium_right_bracket> ;;

    (*readers may inspect \<open>thm useful\<close> to look the contextual facts*)
    (* thm useful *)
    qsort ($i, $d) ;;
    qsort ($i + $d, $len - $d) ;;
          
    holds_fact take_and_drop: \<open>(\<forall>x\<in>set (drop d l'). l ! (len - 1) < x) \<and>
                               (\<forall>x\<in>set (take d l'). x \<le> l ! (len - 1))\<close> ;;

    return

  \<medium_right_bracket>
\<medium_right_bracket> .

thm qsort_def   \<comment> \<open>semantic representation of \<open>qsort\<close>\<close>
thm qsort_\<phi>app \<comment> \<open>specification theorem\<close>

ML \<open> Phi_Syntax.count_semantic_operations (Thm.prop_of @{thm' qsort_def}) \<close> \<comment> \<open>semantic operations\<close>


declare [[\<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics=false,
          recording_timing_of_semantic_operation = true,
          \<phi>assync_proof = true]]

end