theory NuTest
  imports NuStd_Base NuInstructions "HOL-Library.Permutation" "List_Index"
begin

text \<open>The command `\<bullet>`  leads a construction statement, and the construction state by this statement is printed.
  You can insert command `\<bullet>` at any intermediate place to split it into two statements,
    to see what the construction state respectively is in those two parts.\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]
declare find_index_le_size[simp]

proc sub1:  \<open>x \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>x -1 \<tycolon> \<nat>[32]\<close>
  premises \<open>0 < x\<close>
  \<bullet> 1 -
  finish

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 1" | "fib (Suc 0) = 1" | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

(* int fib (int i) { if (i \<le> 1) return 1; else return fib (i-2) + fib (i-1); } *)
  rec_proc Fib: \<open>i \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>fib i \<tycolon> \<nat>\<^sup>r[32]\<close> var i
    \<bullet> -- i 1 \<le> if \<medium_left_bracket> \<open>1\<tycolon> \<nat>\<^sup>r[32]\<close> \<medium_right_bracket> \<medium_left_bracket> i 2 - Fib i 1 - Fib + \<medium_right_bracket>
    \<bullet> goal affirm by (cases i rule: fib.cases) auto
  finish

thm Fib_\<nu>compilation

proc Fib2: \<open>i \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>fib i \<tycolon> \<nat>\<^sup>r[32]\<close>
  \<bullet> \<rightarrow> i
  \<bullet> \<open>1\<tycolon> \<nat>\<^sup>r[32]\<close> 1
  \<bullet> i times var y y' in y, y' \<open>\<lambda>i. y' = fib (Suc i) \<and> y = fib i\<close>
  \<bullet> \<medium_left_bracket> drop \<rightarrow> y, y' y' y y' + \<medium_right_bracket> drop
  finish

\<nu>interface hhh = Fib
\<nu>interface yyy = Fib2

lemma find_index_sorted_le: "sorted xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i < x \<Longrightarrow> i < find_index ((\<le>) x) xs" 
    and find_index_sorted_leq: "sorted xs \<Longrightarrow> i < length xs \<Longrightarrow> x \<le> xs ! i \<Longrightarrow> find_index ((\<le>) x) xs \<le> i"
  unfolding sorted_iff_nth_mono
  by (metis less_le_trans linorder_neqE_nat not_le find_index_property find_index_property)+

lemmas find_index_sorted = find_index_sorted_le find_index_sorted_leq
lemmas add1_le_eq = Suc_le_eq[unfolded Suc_eq_plus1]

proc bin_search: \<open>ptr \<tycolon> Pointer\<heavy_comma> len \<tycolon> \<nat>[size_t]\<heavy_comma> x \<tycolon> \<nat>['b::len]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> xs \<tycolon> Array \<nat>['b]\<close>
  \<longmapsto> \<open>?index \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> xs \<tycolon> Array \<nat>['b]\<close>
  where ?index = "find_index (\<lambda>y. x \<le> y) xs"
  premises "length xs = len" and "sorted xs"
  \<bullet> \<rightarrow> ptr, len, x
  \<bullet> len 0 while var h l in h, l always \<open>l \<le> ?index \<and> ?index \<le> h \<and> h \<le> len\<close> 
  \<bullet> \<medium_left_bracket> -- h, l l h < \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> -- h, l - 2 / l + \<rightarrow> m ptr m \<up> x < if \<medium_left_bracket> h m 1 + \<medium_right_bracket> \<medium_left_bracket> m l \<medium_right_bracket>
  \<bullet> goal affirm using \<nu> by (auto simp add: add1_le_eq find_index_sorted)
  \<bullet> \<medium_right_bracket>
  \<bullet> drop
  finish

thm bin_search_\<nu>compilation

\<nu>interface bin_search = bin_search : \<open>32 word \<times> size_t word \<times> memptr\<close> \<longmapsto> \<open>size_t word\<close>

thm bin_search_\<nu>app
thm bin_search_\<nu>compilation
thm while_\<nu>compilation

(* proc sel_sort: \<open>R\<heavy_comma> ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> xs \<tycolon> Array \<nat>['b::len]\<close> \<longmapsto> \<open>R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> sort xs \<tycolon> Array \<nat>['b]\<close>
  premises [used]: "length xs = n"
  \<bullet> \<rightarrow> ptr, n
  \<bullet> n times var ys heap "ptr \<R_arr_tail> ys" \<open>\<lambda>i. take i ys = sort (take i xs)\<close> \<medium_left_bracket> \<rightarrow> i
  \<bullet> ptr i 1 + \<up>
  thm used *)


proc swap:  \<open>R\<heavy_comma> ptr \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> j \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> xs \<tycolon> Array \<nat>[32]\<close>
  \<longmapsto> \<open>R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> xs[i := xs ! j, j := xs ! i] \<tycolon> Array \<nat>[32]\<close>
  premises \<open>i < length xs\<close> and \<open>j < length xs\<close>
  \<bullet> \<rightarrow> ptr, i, j ptr i \<up>\<rightarrow> i' ptr j \<up> \<rightarrow> j' ptr i j' \<down> ptr j i' \<down>
  finish

proc partition: \<open>ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> xs \<tycolon> Array \<nat>[32]\<close>
  \<longmapsto> \<open>\<exists>*j ys. j \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> ys \<tycolon> Array \<nat>[32]
    \<^bold>s\<^bold>u\<^bold>b\<^bold>j j < length xs \<and> ys  <~~> xs \<and>
      (\<forall>k. k < j \<longrightarrow> ys ! k \<le> ys ! j) \<and> (\<forall>k. j < k \<and> k < n \<longrightarrow> ys ! j < ys ! k)\<close>
  premises \<open>length xs = n\<close> and \<open>0 < n\<close>
  note nth_list_update[simp] not_le[simp] perm_length[simp]
  \<bullet> -- ptr, n 1 - \<up> \<rightarrow> pivot
  \<bullet> \<open>0 \<tycolon> \<nat>[size_t]\<close> n 1 - times var j, ys in j heap "ptr \<R_arr_tail> ys"
  \<bullet> \<open>\<lambda>i. j \<le> i \<and> ys <~~> xs \<and> (ys ! (n-1) = ?pivot) \<and>
    (\<forall>k. k < j \<longrightarrow> ys ! k \<le> ?pivot) \<and> (\<forall>k. j \<le> k \<and> k < i \<longrightarrow> ?pivot < ys ! k)\<close> \<medium_left_bracket>
  \<bullet> \<rightarrow> j, i ptr j \<up>\<rightarrow> j'  ptr i \<up> -- i' pivot \<le> if \<medium_left_bracket> ptr i j' \<down> ptr j i' \<down> j 1 + \<medium_right_bracket> \<medium_left_bracket> j \<medium_right_bracket> 
  \<bullet> goal affirm using \<nu> by (auto simp add: less_Suc_eq intro!: perm_swap[THEN perm.trans])
  \<bullet> \<medium_right_bracket>
  have [useful]: "j < n" using \<nu> by linarith
  \<bullet> \<rightarrow> j ptr j n 1 - swap j
  \<bullet> goal affirm using \<nu> by (smt (z3) Suc_diff_1 Suc_leI diff_less leD length_list_update
        less_numeral_extra(1) less_or_eq_imp_le mset_eq_perm mset_swap nat_neq_iff nth_list_update_eq
         nth_list_update_neq perm_length)
    (*Albeit it is long, it is generated by sledgehammer fully-automatically!
    Actually `auto intro!: perm_swap[THEN perm.trans]` should has been enough to solve this (just try this),
    however I do not know why it is stuck at some silly condition.
    Anyway since no one in those theorems relates to the \<nu>-system nor the low level representations,
      the ugly proof here is basically another proof engineer problem irrelevant with \<nu>-system.*)
  finish


rec_proc qsort: \<open>ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> xs \<tycolon> Array \<nat>[32]\<close>
  \<longmapsto> \<open>\<exists>*ys. (Void\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> ys \<tycolon> Array \<nat>[32]) \<and>\<^sup>s (sorted ys \<and> ys  <~~> xs)\<close>
  var ptr xs n
  premises "n = length xs"
  note perm_length[simp]

  \<bullet> -- ptr, n 0 = if \<medium_left_bracket> drop \<medium_right_bracket> \<medium_left_bracket> n partition \<rightarrow> j
  let ?pivot = "ys ! j" have a1[simp]: " hd (drop j ys) = ?pivot " using \<nu> by (metis hd_drop_conv_nth perm_length)
  \<bullet> ptr j split pop n 1 - j - qsort \<exists>high ptr j qsort \<exists>low push merge

  \<bullet> !! subj \<open>low @ ?pivot # high <~~> xs\<close> affirm using \<nu>
    by (metis (no_types, hide_lams) a1 append_take_drop_id cons_perm_eq drop_all_iff leD list.collapse 
        perm.trans perm_append1 perm_append2 perm_length) \<comment> \<open>generated by Sledgehammer\<close>

  \<bullet> !! subj \<open>sorted (low @ ?pivot # high)\<close> affirm unfolding sorted_append using \<nu>
    by (auto simp add: perm_set_eq in_set_conv_nth nth_tl Suc_eq_plus1)
      (metis add.left_commute add1_le_eq le_add2 le_less_trans less_diff_conv less_or_eq_imp_le)+

  \<bullet> \<medium_right_bracket>
  finish

\<nu>interface my_qsort = qsort

\<nu>export_llvm \<open>/tmp/aa.ll\<close> \<comment> \<open>The desired LLVM IR text is outputted to /tmp/aa.ll\<close>

(*   \<bullet> \<Longrightarrow> precondition[used] \<bullet> \<rightarrow> (v,n) n 0 = if \<medium_left_bracket> \<bullet> $v \<medium_right_bracket> \<medium_left_bracket> \<bullet> $v \<open>0\<tycolon>\<nat>[32]\<close> \<up>\<rightarrow> pivot \<open>1\<tycolon>\<nat>[32]\<close> \<open>1\<tycolon>\<nat>[32]\<close>
  \<bullet> while xs' i j in \<open>((seg |+ ofs) \<R_arr_tail> xs', i, j)\<close> subj \<open>j \<noteq> n\<close>
      always \<open>0 < i \<and> i \<le> j \<and> j \<le> n \<and> length xs' = n \<and> xs' ! 0 = xs ! 0 \<and> (\<forall>k. k <i \<longrightarrow> xs' ! k \<le> xs ! 0) \<and> (\<forall>k. i \<le> k \<and> k < j \<longrightarrow> xs ! 0 < xs' ! k) \<close>
  \<medium_left_bracket> \<bullet> \<Longrightarrow> x[used] \<bullet> \<rightarrow> (a,b,c) c n < $a b c pr^3 \<medium_right_bracket> \<medium_left_bracket> \<bullet> \<Longrightarrow> x[used] \<bullet> \<rightarrow> (xs,i,j) $xs j \<up>\<rightarrow> j' i \<up>\<rightarrow> i' \<rightarrow> xs
  \<bullet> j' pivot \<le> if \<medium_left_bracket> \<bullet> $xs i' j \<Down> j' i \<Down> \<rightarrow> xs i 1 + \<rightarrow> i \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> \<bullet> $xs i j 1 + pr^2 \<medium_right_bracket>
  \<bullet> xs2, i, j \<Longrightarrow> x[used] \<bullet> drop 1 - \<rightarrow> i i \<up>0 \<Down>pivot i \<Down> *)

end
