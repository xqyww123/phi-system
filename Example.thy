theory Example
  imports NuStd_Base NuInstructions "HOL-Library.Permutation" "List_Index"
begin

text \<open>
  For the \<nu>-type variant of a Hoare triple " {\<PP>} f {\<QQ>} ", the \<PP> and \<QQ> are sets of \<nu>-types.
  In Isabelle/HOL, a set is represented by indicating explicitly the quantified variables to
    distinguish with fixed free variables, e.g. \<^term>\<open>{ (x,y) |x. x < y }\<close>,
    where the 'x' is a quantified variable but the 'y' is a fixed free variable,
    and this set represents all pairs where the second element equals to the fixed y and the first
    element is less than y.
  In this case, the set of \<nu>-types \<PP> and \<QQ> are of form \<^term>\<open>{ X x |x. P x }\<close> and \<^term>\<open>{ Y y |y. Q y }\<close>.
  Upon this, in the implementation we represent the Hoare triple "{ X x |x. P x } f { Y y |y. Q y }"
  by the proposition \<^prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x \<longmapsto> Y y \<^bold>s\<^bold>u\<^bold>b\<^bold>j y. Q y \<brangle>\<close>.
  For example, the random function that generates a 32-bits integer less than 10 can be specified by,
  \<^prop>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c rand \<blangle> Nothing \<longmapsto> x \<tycolon> \<nat>[32] \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. x < 10 \<brangle>\<close>.
\<close>

text \<open>The command `\<bullet>`  leads a construction statement, and the construction state by this statement is printed.
  You can insert command `\<bullet>` at any intermediate place to split it into two statements,
    to see what the construction state respectively is in those two parts.\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]
lemmas add1_le_eq[simp] = Suc_le_eq[unfolded Suc_eq_plus1]

section\<open>Subtraction by 1\<close>

proc sub1:  \<open>x \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>x - 1 \<tycolon> \<nat>[32]\<close>
  premises \<open>0 < x\<close>
  \<bullet> 1 -
  finish

section\<open>Fibonacci\<close>

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 1" | "fib (Suc 0) = 1" | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

(* int fib (int i) { if (i \<le> 1) return 1; else return fib (i-2) + fib (i-1); } *)
rec_proc Fib: \<open>i \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>fib i \<tycolon> \<nat>\<^sup>r[32]\<close> var i
    (* The (i \<tycolon> \<nat>\<^sup>r[32]) is the rounding abstraction which represents the integer \<open>i mod 2^32\<close>,
        so we do not need to consider the arithmetic overflow *)
    \<bullet> \<rightarrow> i
    \<bullet> i 1 \<le> if \<medium_left_bracket> \<open>1\<tycolon> \<nat>\<^sup>r[32]\<close> \<medium_right_bracket> \<medium_left_bracket>
    \<bullet> i 2 - Fib \<rightarrow> f2
    \<bullet> i 1 - Fib \<rightarrow> f1
    \<bullet> f1 f2 +
    \<bullet> \<medium_right_bracket> goal affirm by (cases i rule: fib.cases) auto
  finish

thm Fib_\<nu>app \<comment> \<open>The specification theorem\<close>
thm Fib_\<nu>compilation \<comment> \<open>The definition of the procedure\<close>

proc Fib2: \<open>i \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>fib i \<tycolon> \<nat>\<^sup>r[32]\<close>
  \<bullet> \<rightarrow> i
  \<bullet> \<open>1\<tycolon> \<nat>\<^sup>r[32]\<close> 1
  \<bullet> i times y, y' \<open>\<lambda>i. y' = fib (Suc i) \<and> y = fib i\<close> \<medium_left_bracket> \<rightarrow> y, y', i 
  \<bullet>   y' y y' + 
  \<bullet> \<medium_right_bracket> drop
  finish

\<nu>interface my_fib = Fib \<comment> \<open>To export the procedure Fib to an LLVM function with name my_fib.\<close>
\<nu>interface my_fib2 = Fib2

thm Fib_\<nu>app \<comment> \<open>The specification theorem\<close>
thm Fib_\<nu>compilation \<comment> \<open>The definition of the procedure\<close>

section\<open>Binary Search\<close>

proc bin_search:
  argument \<open>ptr \<R_arr_tail> xs \<tycolon> Array \<nat>['b] \<heavy_asterisk> ptr \<tycolon> Pointer \<heavy_asterisk> len \<tycolon> \<nat>[size_t] \<heavy_asterisk> x \<tycolon> \<nat>['b::len]\<close>
  return \<open>ptr \<R_arr_tail> xs \<tycolon> Array \<nat>['b] \<heavy_asterisk> ?index \<tycolon> \<nat>[size_t]\<close>
  where ?index = "find_index (\<lambda>y. x \<le> y) xs"
  premises "length xs = len" and "sorted xs"
  \<bullet> \<rightarrow> ptr, len, x
  \<bullet> len 0 while h, l always \<open>l \<le> ?index \<and> ?index \<le> h \<and> h \<le> len\<close> \<open>l < h\<close>
      \<comment> \<open>the always clause indicates the invariant (the first term) and the loop condition (the second term)\<close>
  \<bullet> \<medium_left_bracket> -- h, l l h < \<medium_right_bracket> \<comment> \<open>The loop condition\<close>
  \<bullet> \<medium_left_bracket> -- h, l - 2 / l + \<rightarrow> m ptr m \<up> x < if \<medium_left_bracket> h m 1 + \<medium_right_bracket> \<medium_left_bracket> m l \<medium_right_bracket> \<medium_right_bracket> \<comment> \<open>The loop body\<close>
  \<bullet> drop
  finish

\<nu>interface bin_search = bin_search : \<open>32 word \<times> size_t word \<times> memptr\<close> \<longmapsto> \<open>size_t word\<close>

thm bin_search_\<nu>app \<comment> \<open>The specification theorem\<close>
thm bin_search_\<nu>compilation \<comment> \<open>The definition of the procedure\<close>


section\<open>Quick-sort\<close>

proc swap:
  argument \<open>ptr \<R_arr_tail> xs \<tycolon> Array \<nat>[32] \<heavy_asterisk> ptr \<tycolon> Pointer \<heavy_asterisk> i \<tycolon> \<nat>[size_t] \<heavy_asterisk> j \<tycolon> \<nat>[size_t]\<close>
  return \<open>ptr \<R_arr_tail> xs[i := xs ! j, j := xs ! i] \<tycolon> Array \<nat>[32]\<close>
  premises \<open>i < length xs\<close> and \<open>j < length xs\<close>
  \<bullet> \<rightarrow> ptr, i, j ptr i \<up>\<rightarrow> i' ptr j \<up> \<rightarrow> j' ptr i j' \<down> ptr j i' \<down>
  finish

proc partition:
  argument \<open>ptr \<R_arr_tail> xs \<tycolon> Array \<nat>[32] \<heavy_asterisk> ptr \<tycolon> Pointer \<heavy_asterisk> n \<tycolon> \<nat>[size_t]\<close>
  return \<open>ptr \<R_arr_tail> ys \<tycolon> Array \<nat>[32] \<heavy_asterisk> j \<tycolon> \<nat>[size_t]
    \<^bold>s\<^bold>u\<^bold>b\<^bold>j j ys. j < length xs \<and> ys  <~~> xs \<and>
      (\<forall>k. k < j \<longrightarrow> ys ! k \<le> ys ! j) \<and> (\<forall>k. j < k \<and> k < n \<longrightarrow> ys ! j < ys ! k)\<close>
  premises \<open>length xs = n\<close> and \<open>0 < n\<close>
  note nth_list_update[simp] not_le[simp] perm_length[simp]

  \<bullet> -- ptr, n 1 - \<up> \<rightarrow> pivot
  \<bullet> \<open>0 \<tycolon> \<nat>[size_t]\<close> n 1 - times var j, ys in "ptr \<R_arr_tail> ys", j
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
    Actually `auto intro!: perm_swap[THEN perm.trans]` should has been enough to solve this,
    however I do not know why it is stuck at some simple condition.*)
  finish


rec_proc qsort:
  argument \<open>ptr \<R_arr_tail> xs \<tycolon> Array \<nat>[32] \<heavy_asterisk> ptr \<tycolon> Pointer \<heavy_asterisk> n \<tycolon> \<nat>[size_t]\<close>
  return \<open>OBJ ptr \<R_arr_tail> ys \<tycolon> Array \<nat>[32] \<^bold>s\<^bold>u\<^bold>b\<^bold>j ys. sorted ys \<and> ys  <~~> xs\<close>
  var ptr xs n
  premises "n = length xs"
  note perm_length[simp]

  \<bullet> -- ptr, n 0 = if \<medium_left_bracket> drop \<medium_right_bracket> \<medium_left_bracket> n partition \<rightarrow> j
  let ?pivot = "ys ! j" have a1[simp]: " hd (drop j ys) = ?pivot " using \<nu> by (metis hd_drop_conv_nth perm_length)

  \<bullet> ptr j split pop n 1 - j - qsort \<exists>high
      \<comment> \<open>the annotation '\<exists>high' indicates the name of  the existential quantified variable to be instantiated\<close>
  \<bullet> ptr j qsort \<exists>low
  \<bullet> push merge

  \<bullet> !! subj \<open>low @ ?pivot # high <~~> xs \<and> sorted (low @ ?pivot # high)\<close> affirm unfolding sorted_append using \<nu>
  by (auto simp add: perm_set_eq in_set_conv_nth nth_tl Suc_eq_plus1)
     (metis (no_types, hide_lams) \<nu>lemmata(1) a1 append_take_drop_id cons_perm_eq drop_all_iff dual_order.strict_trans1
      list.collapse not_less_iff_gr_or_eq perm.trans perm_append1 perm_append2 perm_length add.left_commute add1_le_eq le_add2 le_less_trans less_diff_conv less_or_eq_imp_le)+

  \<bullet> \<medium_right_bracket>
  finish

\<nu>interface my_qsort = qsort


section\<open>KMP\<close>

subsection\<open>An algebra for sub-string matching\<close>

definition "matches' a1 i1 a2 i2 n \<longleftrightarrow>
    i1 + n \<le> length a1 \<and> i2 + n \<le> length a2 \<and> (\<forall>i. i < n \<longrightarrow> a1 ! (i1 + i) = a2 ! (i2 + i)) "

definition "is_next p j n \<longleftrightarrow> n < j \<and> matches' p (j - n) p 0 n \<and> (\<forall> z. n < z \<and> z < j \<longrightarrow> \<not> (matches' p (j - z) p 0 z))"

definition "kmp_table n ktab xs \<longleftrightarrow> (\<forall>j. 0 < j \<and> j < n \<longrightarrow> is_next xs j (ktab ! j))"

lemma matches_empty[simp]:
  "i1 \<le> length a1 \<Longrightarrow> i2 \<le> length a2 \<Longrightarrow> matches' a1 i1 a2 i2 0"
 unfolding matches'_def by auto

lemma matches'_right_extension:
    "matches' a1 i1 a2 i2 n \<Longrightarrow> i1 + n + 1 \<le> length a1 \<Longrightarrow> i2 + n + 1 \<le> length a2 \<Longrightarrow>
    a1 ! (i1 + n) = a2 ! (i2 + n) \<Longrightarrow> matches' a1 i1 a2 i2 (n + 1)"
  unfolding matches'_def by (metis add.assoc add_le_imp_le_right discrete le_neq_implies_less)  

lemma matches'_contradiction_at_first:
    "0 < n \<Longrightarrow> a1 ! i1 \<noteq> a2 ! i2 \<Longrightarrow> \<not> (matches' a1 i1 a2 i2 n)"
  using matches'_def by force

lemma matches_contradiction_at_i :
    "0 < n \<Longrightarrow> i < n \<Longrightarrow> a1 ! (i1 + i) \<noteq> a2 ! (i2 + i) \<Longrightarrow> \<not> matches' a1 i1 a2 i2 n"
  using matches'_def by blast

lemma matches_right_weakening:
    "matches' a1 i1 a2 i2 n \<Longrightarrow> n' < n \<Longrightarrow> matches' a1 i1 a2 i2 n'"
    unfolding matches'_def  by auto

lemma matches_left_weakening:
    "matches' a1 i1 a2 i2 (n + d) \<Longrightarrow> matches' a1 (i1 + d) a2 (i2 + d) n " 
unfolding matches'_def by auto (metis add.commute add.left_commute nat_add_left_cancel_less)

lemma matches'_sym:
    "matches' a1 i1 a2 i2 n \<Longrightarrow> matches' a2 i2 a1 i1 n"
    unfolding matches'_def by simp

lemma matches_trans:
    "matches' a1 i1 a2 i2 n \<Longrightarrow> matches' a2 i2 a3 i3 n \<Longrightarrow> matches' a1 i1 a3 i3 n"
    unfolding matches'_def by simp

lemma next_iteration:
    "0 < j \<Longrightarrow> j < length p \<Longrightarrow>
    j \<le> i \<Longrightarrow> i \<le> length a \<Longrightarrow>
    matches' a (i - j) p 0 j \<Longrightarrow> is_next p j n \<Longrightarrow> matches' a (i - n) p 0 n"  
  unfolding matches'_def is_next_def apply auto 
  subgoal premises prems for ia proof -
    from prems have A: "j + ia - n < j" by linarith 
    from prems A show ?thesis using Nat.add_diff_assoc2 Nat.diff_diff_right by fastforce
  qed done

lemma next_is_maximal:
    "0 < j \<Longrightarrow> j < length p \<Longrightarrow>
    j \<le> i \<Longrightarrow> i \<le> length a \<Longrightarrow>
    i - j < k \<and> k < i - n \<Longrightarrow>
    matches' a (i - j) p 0 j \<Longrightarrow>
    is_next p j n \<Longrightarrow> \<not> matches' a k p 0 (length p)"
    unfolding is_next_def matches'_def apply auto
    subgoal premises prems proof -
      from prems(9)[THEN spec, of "i - k"] prems show ?thesis
        by (smt (verit, ccfv_SIG) Nat.add_diff_assoc2 Nat.diff_diff_right add.commute add_diff_cancel_left' diff_le_self le_trans less_add_eq_less less_or_eq_imp_le less_trans ordered_cancel_comm_monoid_diff_class.diff_add)
    qed done

definition "first_occur p a r \<longleftrightarrow>
    (r < length a \<longrightarrow> matches' a r p 0 (length p)) \<and> (\<forall>k < r. \<not> (matches' a k p 0 (length p)))"


subsection\<open>Procedure Constructions\<close>

proc mk_kmp_table:
  argument \<open>px \<R_arr_tail> xs \<tycolon> Array \<nat>[8] \<heavy_asterisk> px \<tycolon> Pointer \<heavy_asterisk> nx \<tycolon> \<nat>[size_t]\<close>
  return \<open>px \<R_arr_tail> xs \<tycolon> Array \<nat>[8] \<heavy_asterisk> pk \<R_arr_tail> ktab \<tycolon> Array \<nat>[size_t] \<heavy_asterisk> pk \<tycolon> Pointer
    \<^bold>s\<^bold>u\<^bold>b\<^bold>j pk ktab. kmp_table nx ktab xs \<and> length ktab = nx\<close>
  premises \<open>1 \<le> nx\<close> and \<open>length xs = nx\<close>
  note  kmp_table_def[simp]

  \<bullet> \<rightarrow> px, nx
  \<bullet> nx alloc_array \<open>\<nat>[size_t]\<close> \<rightarrow> pk
  \<bullet> \<open>1 \<tycolon> \<nat>[size_t]\<close> nx < if \<medium_left_bracket>
  \<bullet> pk \<open>1\<tycolon>\<nat>[size_t]\<close> 0 \<down>
  note is_next_def [simp] nth_list_update[simp]
  \<bullet> \<open>1\<tycolon>\<nat>[size_t]\<close> 0 while var i j ktab in \<open>(c |+ 0) \<R_arr_tail> ktab\<close>, i, j
    always \<open>j < i \<and> i < nx 
    \<and> matches' xs (i - j) xs 0 j
    \<and> (\<forall>z. j < z \<and> z < i \<longrightarrow> \<not>matches' xs (i - z) xs 0 (z + 1))
    \<and> (\<forall>k. 0 < k \<and> k \<le> i \<longrightarrow> is_next xs k (ktab ! k))
    \<and> length ktab = nx\<close> \<open>i < nx - 1\<close>
  note is_next_def [simp del] nth_list_update[simp del]
  \<bullet> \<medium_left_bracket> -- i, j i nx 1 - < \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> \<rightarrow> i, j px i \<up> px j \<up> = if
  \<bullet> \<medium_left_bracket> i 1 + j 1 + -- i, j pk i j \<down>\<medium_right_bracket>
  \<bullet> \<medium_left_bracket> j 0 = if \<medium_left_bracket> i 1 + -- i pk i 0 \<down>j \<medium_right_bracket> \<medium_left_bracket> i pk j \<up> \<medium_right_bracket> \<medium_right_bracket>

  have CC: "(\<forall>z. j + 1 < z \<and> z < i + 1 \<longrightarrow> \<not> matches' xs (i + 1 - z) xs 0 z)" using \<nu>
    by (metis leI le_add_diff_inverse2 less_diff_conv less_diff_conv2 less_nat_zero_code nat_diff_split_asm ordered_cancel_comm_monoid_diff_class.diff_diff_right) 
  have A1: "i + 1 < nx" using \<nu> by auto
  have AA2: "\<And>k. k \<le> i + 1 \<longleftrightarrow> k \<le> i \<or> k = i + 1" by auto
  \<bullet> goal affirm apply (elim TrueE, rule)
    apply (cases "xs ! i = xs ! j") using \<nu> apply auto[1]
    apply (smt (z3) Nat.le_diff_conv2 add_cancel_left_left le_add_diff_inverse2 less_imp_le less_trans matches'_right_extension \<nu>)
    apply (metis (full_types) Nat.diff_diff_right add_lessD1 le_add_diff_inverse2 less_add_one less_diff_conv less_diff_conv2 less_one matches_right_weakening not_less \<nu>)
    apply (smt (verit, ccfv_threshold) AA2 CC Nat.add_0_right Nat.diff_diff_right add.commute add_diff_cancel_right' dual_order.strict_iff_order is_next_def le_add_diff_inverse2 less_add_same_cancel2 less_diff_conv less_trans matches'_right_extension neq0_conv nth_list_update_eq nth_list_update_neq \<nu>)
  apply (cases "j = 0") using \<nu> apply auto[1]
  apply (metis CC One_nat_def Suc_leI add.commute add_diff_cancel_right' antisym_conv2 less_add_one matches'_contradiction_at_first matches_right_weakening plus_1_eq_Suc)
  subgoal for k apply (cases "k = i + 1")
    apply (smt (verit, ccfv_threshold) CC Suc_eq_plus1 Suc_leI add_diff_cancel_right' diff_diff_cancel diff_is_0_eq' is_next_def le_neq_implies_less le_trans less_imp_le matches'_contradiction_at_first matches_empty nth_list_update_eq zero_le_one)
    by (metis AA2 nth_list_update_neq)
 using \<nu> apply auto[1]
  apply (meson is_next_def less_imp_le less_le_trans \<nu>)
  apply (metis (no_types, lifting) \<nu> less_imp_le less_le_trans next_iteration) 
  subgoal for z 
    apply (cases "j < z") using \<nu>(1) apply blast apply (simp add: not_less)
    apply (cases "z = j") using \<nu> apply (metis le0 le_add_diff_inverse2 less_add_one less_imp_le matches'_def plus_nat.add_0) 
    subgoal premises prems proof -
      from prems \<nu> have A: " is_next xs j (ktab ! j)" by (metis less_le less_nat_zero_code neq0_conv)
      from \<nu> prems have X1: "z + (j - z) = j" "i - j + (j - z) = i - z" apply (meson le_add_diff_inverse) by (simp add: less_or_eq_imp_le prems(12) prems(4) le_add_diff_inverse) 
      note X2 = matches_left_weakening[where n = z and d = \<open>j - z\<close>, simplified X1]
      thm matches_left_weakening[where n = z and d = \<open>j - z\<close>, simplified X1]
      from A[unfolded is_next_def] prems \<nu> show ?thesis
        by (metis (no_types, lifting) X1(2) X2 add.left_neutral le_neq_implies_less less_add_one matches'_sym matches_right_weakening matches_trans)
    qed done
  done
  \<bullet> \<medium_right_bracket> drop drop subj \<open>kmp_table nx ktab xs \<and> length ktab = nx\<close> \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> \<medium_right_bracket> 
  \<bullet> pk
  finish


proc kmp:
  argument \<open>px \<R_arr_tail> xs \<tycolon> Array \<nat>[8] \<heavy_asterisk> py \<R_arr_tail> ys \<tycolon> Array \<nat>[8] \<heavy_asterisk>
    px \<tycolon> Pointer \<heavy_asterisk> py \<tycolon> Pointer \<heavy_asterisk> nx \<tycolon> \<nat>[size_t] \<heavy_asterisk> ny \<tycolon> \<nat>[size_t]\<close>
  return \<open> i \<tycolon> \<nat>[size_t] \<heavy_asterisk> pk \<R_arr_tail> ktab \<tycolon> Array \<nat>[size_t] \<heavy_asterisk> px \<R_arr_tail> xs \<tycolon> Array \<nat>[8] \<heavy_asterisk> py \<R_arr_tail> ys \<tycolon> Array \<nat>[8]
    \<^bold>s\<^bold>u\<^bold>b\<^bold>j i ktab pk. first_occur xs ys i \<and> kmp_table nx ktab xs\<close>
  premises \<open>length xs = nx\<close> and \<open>length ys = ny\<close> and "1 \<le> nx"

  \<bullet> \<rightarrow> px,py,nx,ny
  \<bullet> px nx mk_kmp_table \<rightarrow> pk
  \<bullet> \<open>0 \<tycolon> \<nat>[size_t]\<close>0 while var i j in i, j 
    always \<open> j \<le> nx \<and> j \<le> i \<and> i \<le> ny
      \<and> matches' ys (i - j) xs 0 j \<and>
    (\<forall>k < i - j.  \<not> (matches' ys k xs 0 nx))\<close> \<open>i < ny \<and> j < nx\<close>
  \<bullet> \<medium_left_bracket> -- i, j i ny < j nx < \<and> \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> \<rightarrow> i, j
  \<bullet> py i \<up> px j \<up> = if
  \<bullet> \<medium_left_bracket> i 1 + j 1 + \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> j 0 = if \<medium_left_bracket> i 1 + j \<medium_right_bracket> \<medium_left_bracket> i pk j \<up>\<medium_right_bracket> \<medium_right_bracket>
  \<bullet> goal affirm using \<nu> apply auto
  apply (metis One_nat_def Suc_eq_plus1 \<nu>lemmata \<open>i < ny \<and> j < nx\<close> add.right_neutral diff_zero discrete matches'_right_extension)
  apply (metis Suc_eq_plus1 \<open>i < ny \<and> j < nx\<close> less_Suc_eq matches'_contradiction_at_first)
  apply (metis add.commute add.right_neutral discrete le_add_diff_inverse2 matches'_right_extension \<nu>)
  apply (simp add: is_next_def kmp_table_def matches'_def)
  apply (meson dual_order.trans is_next_def kmp_table_def le_less \<nu>)
  apply (metis kmp_table_def next_iteration \<nu>)
  by (smt (verit, ccfv_threshold) \<nu> add.commute add.left_neutral diff_add_inverse kmp_table_def le0 le_Suc_ex linorder_neqE_nat matches'_def next_is_maximal) 
  \<bullet> \<medium_right_bracket>
  \<bullet> nx = if \<medium_left_bracket> nx - \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>
  \<bullet> goal affirm unfolding first_occur_def using \<nu> apply auto
  by (metis add_mono_thms_linordered_field(2) antisym_conv1 dual_order.strict_trans1 less_diff_conv matches'_def) 
finish

section\<open>Ending\<close>

text \<open>In the end, we output the desired LLVM IR.\<close>

\<nu>export_llvm \<open>/tmp/aa.ll\<close> \<comment> \<open>Output the desired LLVM IR text to /tmp/aa.ll\<close>

end
