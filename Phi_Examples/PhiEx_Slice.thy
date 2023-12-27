theory PhiEx_Slice
  imports Phi_Semantics.PhiSem_C
          "HOL-Combinatorics.List_Permutation"
          PhiStd.PhiStd_Loop
begin

declare One_nat_def[simp del]

term sorted
term permute_list

term \<open>A <~~> B\<close>


proc qsort:
  input  \<open>l  \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32)\<heavy_comma>
          ptr  \<Ztypecolon> \<v>\<a>\<l> \<Ss>\<Pp>\<t>\<r>[addr:i:len] \<i>\<n>\<t>(32)\<heavy_comma>
          len \<Ztypecolon> \<v>\<a>\<l> \<nat>(32)\<close>
  premises [simp]: \<open>ptr = 0\<close>
  output \<open>l' \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,len] \<nat>(32) \<s>\<u>\<b>\<j> l'. l <~~> l' \<and> sorted l'\<close>
\<medium_left_bracket>
  if ($len \<le> 1)
  \<medium_left_bracket> \<medium_right_bracket>
  \<medium_left_bracket>
    val pivot \<leftarrow> $ptr ! ;;
    var d \<leftarrow> 1 ;;
    replicate (0,$len) \<open>\<lambda>n. low \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,d] \<nat>(32)\<heavy_comma>
                            up \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i+d,n-d] \<nat>(32)\<heavy_comma>
                            rem \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i+n,len-n] \<nat>(32)\<heavy_comma>
                            d \<Ztypecolon> \<v>\<a>\<r>[d] \<nat>(32)
                         \<s>\<u>\<b>\<j> low up rem d.
                            d \<le> n \<and> l <~~> (low @ up @ rem)\<close> 
    \<medium_left_bracket> \<rightarrow> val i ;;
        $ptr + $i

















        
        ;;
    var k \<leftarrow> 1 ;;
    while' \<open>k \<Ztypecolon> \<v>\<a>\<r>[k] \<nat>(32)\<heavy_comma>
            low \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,k] \<nat>(32)\<heavy_comma>
            up \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i+k,len-k] \<nat>(32)
            \<s>\<u>\<b>\<j> k low up. Inv: (k \<le> )
                        \<and> Guard: ()\<close>

















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







end