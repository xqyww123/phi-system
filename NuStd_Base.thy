theory NuStd_Base
  imports NuSys NuInstructions NuLLReps
  keywords
     "\<up>:" "\<Up>:" "\<down>:" "\<Down>:" "subj" "always" "--" "\<rightarrow>" "\<lambda>" "\<lambda>'" :: quasi_command
  abbrevs "|^" = "\<up>"
    and "||^" = "\<Up>"
    and "|v" = "\<down>"
    and "||v" = "\<Down>"
    and "<up>" = "\<up>"
    and "<down>" = "\<down>"
    and "<Up>" = "\<Up>"
    and "<Down>" = "\<Down>"
    and "<some>" = "\<^bold>s\<^bold>o\<^bold>m\<^bold>e"
begin

section \<open>Preliminary\<close>

\<phi>overloads singular and plural
\<phi>overloads split and split_cast and merge and pop and pop_cast and push

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

section \<open>\<phi>-Types\<close>

(*

subsection \<open>Ref\<close>

definition Ref  :: "('a::field, 'b) \<phi> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b) \<phi>"
  where "Ref = (\<lambda>T xx. {heap. (case xx of addr \<R_arr_tail> x \<Rightarrow> (heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T))})"

lemma [simp]: "heap \<in> (addr \<R_arr_tail> x \<tycolon> Ref T) \<longleftrightarrow> (heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T)"
  by (simp add: lrep_exps Ref_def \<phi>Type_def)
lemma [elim]: " addr \<R_arr_tail> x \<ratio> Ref T \<Longrightarrow> (x \<ratio> T \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (auto simp add: MemAddrState_def)

subsection \<open>Array'\<close>

definition Array' :: "('a::field, 'b) \<phi> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b option list) \<phi>"
  where "Array' N x' = {heap. (case x' of (base |+ ofs) \<R_arr_tail> xs \<Rightarrow>
    (\<forall>i < length xs. pred_option (\<lambda>x. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s x \<tycolon> N) (xs ! i)) \<and>
    ofs + length xs \<le> segment_len base \<and> segment_llty base = LLTY('a))}"

lemma [simp]: "heap \<in> ((base |+ ofs) \<R_arr_tail> xs \<tycolon> Array' N) \<longleftrightarrow>
    (ofs + length xs \<le> segment_len base \<and>
    segment_llty base = LLTY('a) \<and>
    (\<forall>i < length xs. pred_option (\<lambda>x. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s x \<tycolon> N) (xs ! i))
)" for N :: "('a::field, 'b) \<phi>"
  by (auto simp add: lrep_exps Array'_def \<phi>Type_def)

lemma [elim,\<phi>elim]: "a \<R_arr_tail> xs \<ratio> Array' N \<Longrightarrow> (
    (\<And>i. i < length xs \<Longrightarrow> pred_option (\<lambda>x. x \<ratio> N) (xs ! i)) \<Longrightarrow> offset_of a + length xs \<le> address_len a \<Longrightarrow> address_llty a = LLTY('a)
  \<Longrightarrow> C) \<Longrightarrow> C"
   for N :: "('a::field, 'b) \<phi>"
  unfolding Inhabited_def[of "a \<R_arr_tail> xs \<tycolon> Array' N"]
  by (cases a) (auto simp add: lrep_exps pred_option_def list_all2_conv_all_nth)

lemma Array'_to_Ref_\<phi>app:
 "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m i \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! (i-j)) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ (a |+ j) \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> (a |+ j) \<R_arr_tail> xs[ (i-j) := None] \<tycolon> Array' N \<heavy_comma> (a |+ i) \<R_arr_tail> the (xs ! (i-j)) \<tycolon> Ref N"
  unfolding Cast_def Separation_expn pair_forall
  apply (auto simp add: nu_exps) apply (rule heap_split_by_addr_set[of _  _ "{a |+ i}"])
  subgoal premises prems for y v proof -
    define k where "k = i - j"
    have i: "i = j + k" unfolding k_def using prems by simp
    show ?thesis unfolding k_def[symmetric] unfolding i
      using prems[unfolded k_def[symmetric], unfolded i]
      by (auto  simp add: pred_option_def Ball_def nth_list_update)
  qed done

lemma [\<phi>reason on ?any]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! (i-j)) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ (a |+ j) \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> (a |+ j) \<R_arr_tail> xs[ (i-j) := None] \<tycolon> Array' N \<heavy_comma> (a |+ i) \<R_arr_tail> the (xs ! (i-j)) \<tycolon> Ref N"
  unfolding cast_def
  using Array'_to_Ref_\<phi>app[unfolded Cast_def ParamTag_def] by blast

lemma Ref_to_Array':
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a |+ j) \<R_arr_tail> xs[ i-j := None] \<tycolon> Array' N \<heavy_comma> (a |+ i) \<R_arr_tail> y \<tycolon> Ref N \<longmapsto> OBJ (a |+ j) \<R_arr_tail> xs[ i-j := Some y] \<tycolon> Array' N"
  unfolding Cast_def Separation_expn
  apply (auto simp add: pred_option_def Ball_def nu_exps)
  by (metis MemAddrState_add_I1 MemAddrState_add_I2 le_add_diff_inverse nth_list_update nth_list_update_neq option.sel)

lemma [\<phi>reason on ?any]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! (i-j)) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ (a |+ j) \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> (a |+ j) \<R_arr_tail> xs[i-j := None] \<tycolon> Array' N \<heavy_comma> (a |+ i) \<R_arr_tail> the (xs ! (i-j)) \<tycolon> Ref N \<^bold>w\<^bold>i\<^bold>t\<^bold>h True
    \<^bold>d\<^bold>u\<^bold>a\<^bold>l (a |+ j) \<R_arr_tail> xs[i-j := None] \<tycolon> Array' N \<heavy_comma> (a |+ i) \<R_arr_tail> y \<tycolon> Ref N \<longmapsto> OBJ (a |+ j) \<R_arr_tail> xs[i-j := Some y] \<tycolon> Array' N"
  by (meson Array'_to_Ref_\<phi>app CastDual_I ParamTag Ref_to_Array')

(* lemma Ref_to_Array':
  "\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H1 \<longmapsto> H2 \<heavy_comma> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> y \<tycolon> Ref N \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket> \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H2 \<longmapsto> H3 \<heavy_comma> \<medium_left_bracket> a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket> \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow>
  \<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H1  \<longmapsto> H3 \<heavy_comma> \<medium_left_bracket> a \<R_arr_tail> xs[i := Some y] \<tycolon> Array' N \<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>" *)


lemma split_cast_Array'_\<phi>app[\<phi>overload split_cast]:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m n \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n \<le> length l \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ a \<R_arr_tail> l \<tycolon> Array' T \<longmapsto> a \<R_arr_tail> take n l \<tycolon> Array' T \<heavy_comma> (a ||+ n) \<R_arr_tail> drop n l \<tycolon> Array' T"
  unfolding Cast_def Premise_def Separation_expn
    apply (cases a) apply (auto simp add: nu_exps min_absorb2) 
  subgoal for base ofs v
    apply (rule heap_split_by_set[of _ _ "-{ MemAddress (base |+ ofs + i) | i. i < n}"])
    apply (auto simp add: pred_option_def Ball_def split: option.split)
    apply (rule MemAddrState_restrict_I2)
     apply (metis add.assoc add.commute less_diff_conv)
    by simp
  done

(*solve*)
lemma merge_cast_Array'_2_\<phi>app:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n = length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l1 \<tycolon> Array' T \<heavy_comma> (a ||+ n) \<R_arr_tail> l2 \<tycolon> Array' T \<longmapsto> OBJ a \<R_arr_tail> l1 @ l2 \<tycolon> Array' T "
  unfolding Cast_def Premise_def Separation_expn apply (cases a)
  apply (auto simp add: nu_exps min_absorb2 pred_option_def Ball_def nth_append)
  apply (meson MemAddrState_add_I2)
  by (metis MemAddrState_add_I1 add.assoc add_diff_inverse_nat nat_add_left_cancel_less)
  

lemma merge_cast_Array'_\<phi>app:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ofs' = ofs + length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (base |+ ofs) \<R_arr_tail> l1 \<tycolon> Array' T \<heavy_comma> (base |+ ofs') \<R_arr_tail> l2 \<tycolon> Array' T \<longmapsto> OBJ (base |+ ofs) \<R_arr_tail> l1 @ l2 \<tycolon> Array' T "
  using merge_cast_Array'_2_\<phi>app[of _ _ "base |+ ofs", simplified] by blast

(* lemma Array'_dual_Ref_\<phi>app [\<phi>intro]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! i) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_comma> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> the (xs ! i) \<tycolon> Ref N \<medium_right_bracket>
  \<^bold>d\<^bold>u\<^bold>a\<^bold>l a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_comma> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> y \<tycolon> Ref N \<medium_right_bracket> \<longmapsto> a \<R_arr_tail> xs[i := Some y] \<tycolon> Array' N"
  unfolding CastDual_def Heap_Cast_Goal_def apply (simp add: Array'_to_Ref_\<phi>app)
  unfolding Cast_def apply (cases a) apply (auto simp add: pred_option_def Ball_def)
  by (metis MemAddrState_add_I1 MemAddrState_add_I2 nth_list_update option.sel)
*)


subsection \<open>Array\<close>

definition Array :: "('a::field, 'b) \<phi> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b list) \<phi>"
  where "Array N = Array' N <down-lift> (map_object id (map Some)) "

lemma Array_to_Array': "(a \<R_arr_tail> l \<tycolon> Array T) = (a \<R_arr_tail> map Some l \<tycolon> Array' T) "
  unfolding Array_def by auto
(* lemma [simp]: "heap \<nuLinkL> Array N \<nuLinkR> (base |+ ofs) \<R_arr_tail> xs \<longleftrightarrow>
    (ofs + length xs \<le> segment_len base \<and>
    segment_llty base = LLTY('a) \<and>
    (\<forall>i < length xs. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s xs ! i \<tycolon> N)
)" for N :: "('a::field, 'b) \<phi>"
  by (auto simp add: lrep_exps Array_def) *)
  
lemma [elim,\<phi>elim]: "a \<R_arr_tail> xs \<ratio> Array N \<Longrightarrow> (
    (\<And>i. i < length xs \<Longrightarrow> xs ! i \<ratio> N) \<Longrightarrow> offset_of a + length xs \<le> address_len a \<Longrightarrow> address_llty a = LLTY('a)
  \<Longrightarrow> C) \<Longrightarrow> C"
   for N :: "('a::field, 'b) \<phi>"
  unfolding Inhabited_def[of "a \<R_arr_tail> xs \<tycolon> Array N"]
  unfolding Array_def
  by (cases a) (auto simp add: lrep_exps list_all2_conv_all_nth)

(* lemma [THEN cast_trans, simplified, \<phi>intro 50]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> map Some xs \<tycolon> Array' N"
  unfolding Cast_def Array_def by (cases a) auto *)

definition mapSome :: " 'a list \<Rightarrow> 'a option list " where "mapSome = map Some"
lemma [simp]: "length (mapSome l) = length l" unfolding mapSome_def by auto
lemma [simp]: "i < length l \<Longrightarrow> mapSome l ! i = Some (l ! i)" unfolding mapSome_def by auto
lemma [simp]: "i < length l \<Longrightarrow> (mapSome l) [i := Some v] = mapSome (l [i:=v])" unfolding mapSome_def by (metis map_update)
lemma [simp]: "i < length l \<Longrightarrow> the (mapSome l ! i) = l ! i" unfolding mapSome_def by auto
lemma [simp]: "drop n (mapSome l) = mapSome (drop n l)" unfolding mapSome_def by (meson drop_map)
lemma [simp]: "take n (mapSome l) = mapSome (take n l)" unfolding mapSome_def using take_map by blast 

lemma Array'_cast_Array: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs' = mapSome xs2 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs' \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N"
  unfolding Cast_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def)
lemma Array_cast_Array': "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> mapSome xs \<tycolon> Array' N"
  unfolding Cast_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def)

lemma [\<phi>reason]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> a \<R_arr_tail> xs' \<tycolon> Array' N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs' = mapSome xs2 \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def using Array'_cast_Array[unfolded Cast_def] by blast

lemma [\<phi>reason]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> mapSome xs \<tycolon> Array' N \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def using Array_cast_Array'[unfolded Cast_def] by blast

lemma [\<phi>reason on ?any]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ a \<R_arr_tail> mapSome xs \<tycolon> Array' N \<longmapsto> H \<heavy_comma> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<heavy_comma> X\<^sub>m \<longmapsto> OBJ a \<R_arr_tail> xs'\<^sub>m \<tycolon> Array' N \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs'\<^sub>m = mapSome xs\<^sub>m \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> H \<heavy_comma> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<heavy_comma> X\<^sub>m \<longmapsto> OBJ a \<R_arr_tail> xs\<^sub>m \<tycolon> Array N"
  unfolding  CastDual_def Cast_def
  by (simp add: Array_to_Array' Premise_def mapSome_def)

(* lemma single_Array_is_Ref: "\<tort_lbrace>a \<R_arr_tail> [x] \<tycolon> Array T\<tort_rbrace> = \<tort_lbrace>a \<R_arr_tail> x \<tycolon> Ref T\<tort_rbrace>"
  unfolding Array_def by (cases a) (auto simp add: pred_option_def Ball_def) *)

lemma [\<phi>reason on \<open>\<^bold>c\<^bold>a\<^bold>s\<^bold>t ?a \<R_arr_tail> [?x] \<tycolon> Array ?T \<longmapsto> ?a \<R_arr_tail> ?x \<tycolon> Ref ?T'' \<^bold>w\<^bold>i\<^bold>t\<^bold>h ?P\<close>]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> [x] \<tycolon> Array T \<longmapsto> a \<R_arr_tail> x \<tycolon> Ref T"
  unfolding Cast_def Array_def by (cases a) (simp add: pred_option_def Ball_def)

lemma split_cast_Array_\<phi>app[\<phi>overload split_cast]:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m n \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n \<le> length l \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ a \<R_arr_tail> l \<tycolon> Array T \<longmapsto> a \<R_arr_tail> take n l \<tycolon> Array T \<heavy_comma> (a ||+ n) \<R_arr_tail> drop n l \<tycolon> Array T"
  by (simp add: Array_to_Array'
      split_cast_Array'_\<phi>app[of n "map Some l" a T, simplified, simplified take_map drop_map])

lemma pop_cast_Array'_\<phi>app[\<phi>overload pop_cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e l \<noteq> [] \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t OBJ a \<R_arr_tail> l \<tycolon> Array T \<longmapsto> (a ||+ 1) \<R_arr_tail> tl l \<tycolon> Array T \<heavy_comma> a \<R_arr_tail> hd l \<tycolon> Ref T"
  unfolding Premise_def cast_def
  apply (cases a)
  apply (auto simp add: nu_exps pair_forall Array_to_Array' neq_Nil_conv)
  subgoal for x1 x2 y ys aa
    apply (rule heap_split_by_set[where S = "{ MemAddress (x1 |+ x2) }"])
    apply (auto)
   apply (rule MemAddrState_restrict_I2)
    apply (metis Suc_leI add.assoc le_less_Suc_eq le_less_trans le_refl nth_Cons_Suc plus_1_eq_Suc)
    apply (metis less_add_one memaddr.inject not_add_less1 resource_key.inject(1) singletonD)
    by (metis MemAddrState_restrict_I1 add.right_neutral insert_iff nth_Cons_0 zero_less_Suc)
  done
    

lemma push_Array'_2_\<phi>app[\<phi>overload push]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (a ||+ 1) \<R_arr_tail> l \<tycolon> Array T \<heavy_comma> a \<R_arr_tail> x \<tycolon> Ref T \<longmapsto> OBJ a \<R_arr_tail> x # l \<tycolon> Array T"
  unfolding Premise_def cast_def
  apply (cases a)
  apply (auto simp add: nu_exps pair_forall Array_to_Array' neq_Nil_conv pred_option_def)
  subgoal for x1 x2 h1 h2 i xa
    apply (cases i) apply (simp_all add: Suc_eq_plus1) apply blast
    by (metis MemAddrState_add_I2 add.commute add.left_commute)
  done

lemma push_Array'_\<phi>app[\<phi>overload push]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i' = i + 1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a |+ i') \<R_arr_tail> l \<tycolon> Array T \<heavy_comma> (a |+ i) \<R_arr_tail> x \<tycolon> Ref T \<longmapsto> OBJ (a |+ i) \<R_arr_tail> x # l \<tycolon> Array T"
  unfolding Premise_def cast_def
  apply (auto simp add: nu_exps pair_forall Array_to_Array' neq_Nil_conv pred_option_def)
  subgoal for h1 h2 ia xa
    apply (cases ia) apply (simp_all add: Suc_eq_plus1) apply blast
    by (metis MemAddrState_add_I2 Suc_eq_plus1 add.commute add_Suc_right)
  done


lemma merge_cast_Array_2_\<phi>app[\<phi>overload merge]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n = length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l1 \<tycolon> Array T \<heavy_comma> (a ||+ n) \<R_arr_tail> l2 \<tycolon> Array T \<longmapsto> OBJ a \<R_arr_tail> l1 @ l2 \<tycolon> Array T "
  unfolding Array_to_Array' map_append
  using merge_cast_Array'_2_\<phi>app[of _ "map Some l1", simplified] .

lemma merge_cast_Array_\<phi>app[\<phi>overload merge]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ofs' = ofs + length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (base |+ ofs) \<R_arr_tail> l1 \<tycolon> Array T \<heavy_comma> (base |+ ofs') \<R_arr_tail> l2 \<tycolon> Array T \<longmapsto> OBJ (base |+ ofs) \<R_arr_tail> l1 @ l2 \<tycolon> Array T "
  using merge_cast_Array_2_\<phi>app[of _ _ "base |+ ofs", simplified] by blast

lemma drop_array_\<phi>app:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t px \<R_arr_tail> xs \<tycolon> Array T \<heavy_comma> p \<R_arr_tail> ys \<tycolon> Array U \<longmapsto> OBJ px \<R_arr_tail> xs \<tycolon> Array T"
  unfolding Cast_def apply (cases px, cases p) apply (simp add: nu_exps lrep_exps Array_def)
  by (meson MemAddrState_add_I2)

(* lemma [\<phi>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> x \<tycolon> Ref T \<longmapsto> a \<R_arr_tail> [x] \<tycolon> Array T"
  unfolding Cast_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def) *)

(* lemma [THEN cast_dual_trans, \<phi>intro]: 
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> mapSome xs \<tycolon> Array' N
  \<^bold>d\<^bold>u\<^bold>a\<^bold>l a \<R_arr_tail> xs' \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N \<^bold>w\<^bold>h\<^bold>e\<^bold>n xs' = mapSome xs2"
  unfolding Cast_def CastDual_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def) *)
*)


section \<open>Procedures and Operations\<close>

context std begin

subsection \<open>Basic sequential instructions\<close>


subsubsection \<open>let & local_value\<close>

lemma op_let: " (\<And>p. p \<in> (a \<tycolon> A) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body p \<lbrace> R \<longmapsto> R' \<rbrace>) \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_let body \<lbrace> R \<heavy_comma> VAL a \<tycolon> A \<longmapsto> R' \<rbrace>"
  unfolding Procedure_def op_let_def by (auto simp add: nu_exps)

lemma op_local_value: "v \<in> (a \<tycolon> A) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_local_value v \<lbrace> R \<longmapsto> R \<heavy_comma> VAL a \<tycolon> A \<rbrace>"
  unfolding Procedure_def op_local_value_def by (auto simp add: nu_exps)

\<phi>processor let_local_value 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [\<RR>] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n R\<close> \<open>let open Parse Scan in
  fn ctx => fn sequent => (($$$ "\<rightarrow>" || $$$ "--" || $$$ "\<lambda>" || $$$ "\<lambda>'") --| option ($$$ "(") -- list1 binding --| option ($$$ ")"))
  >> (fn (keyword,idts) => fn _ =>
    Local_Value.mk_let (keyword = "--" orelse keyword = "\<lambda>'") (rev idts) sequent ctx
) end\<close>


subsubsection \<open>function call\<close>
  \<comment> \<open>A function is the program function in the ordinary meaning that called by pushing stack frame, rarely inline
    (whereas a procedure is generally inline), which is a procedure of \<^term>\<open>Void\<close> as its stack remainder so that
    it can only access its arguments and never the stack remainder.
    A function always corresponds an LLVM function, whereas other ordinary procedures are totally inline at the calling place generally
      except some cases of optimization.
    Only a function but no other ordinary procedure locates at a decided address in memory during the runtime,
    so that has function pointers to it, and therefore can be indirectly called by the pointer. \<close>



(* definition strip_end_tail :: " ('a::lrep \<times> void \<longmapsto> ('b::lrep \<times> void)) \<Rightarrow> 'a \<times> ('r::stack) \<longmapsto> ('b \<times> 'r)"
  where "strip_end_tail f s = (case s of (a,r) \<Rightarrow> bind (f (a,void)) (\<lambda>(b,_). StatOn (b,r)))"
lemma strip_end_tail: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> A \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> B \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c strip_end_tail f \<lbrace> R\<heavy_comma> A \<longmapsto> R\<heavy_comma> B \<rbrace>"
  unfolding strip_end_tail_def Procedure_def bind_def by (auto 4 4)
*)


subsection \<open>Branches & Loops\<close>

subsubsection \<open>sel\<close>

declare op_sel_def[\<phi>instr]

lemma sel_\<phi>app:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sel \<lbrace> VAL a \<Ztypecolon> T\<heavy_comma> b \<Ztypecolon> T\<heavy_comma> c \<Ztypecolon> \<bool> \<longmapsto> (if c then a else b) \<Ztypecolon> T \<rbrace> "
  unfolding \<phi>Procedure_def op_sel_def
  by (auto simp add: \<phi>expns) (metis append.left_neutral append_Cons)+


subsubsection \<open>if\<close>

declare op_if_def[\<phi>instr]

lemma "__if_rule__":
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c cond \<lbrace> X \<longmapsto> X \<heavy_comma> P \<Ztypecolon> \<bool> \<rbrace>
    \<longrightarrow>\<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_true \<lbrace> X \<^bold>s\<^bold>u\<^bold>b\<^bold>j P \<longmapsto> Y\<^sub>T \<rbrace>
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_false \<lbrace> X \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> P \<longmapsto> Y\<^sub>F \<rbrace>
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (cond \<then> op_if branch_true branch_false) \<lbrace> X \<longmapsto> If P Y\<^sub>T Y\<^sub>F \<rbrace>"
  unfolding \<phi>def op_if_def Conv_def Merge_def instr_comp_def bind_def
  by (auto simp add: \<phi>expns pair_forall split: list.split)


lemma if_\<phi>app:
  "(cond \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_true \<lbrace> X \<longmapsto> Y\<^sub>T \<rbrace>)
    \<longrightarrow> (\<not> cond \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_false \<lbrace> X \<longmapsto> Y\<^sub>F \<rbrace>)
    \<longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v Merge cond Y\<^sub>T Y\<^sub>F = Y
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if TYPE('y::stack) branch_true branch_false \<lbrace> X \<heavy_comma> cond \<tycolon> \<bool> \<longmapsto> Y \<rbrace>"
  unfolding \<phi>def op_if_def Conv_def Merge_def by (auto simp add: nu_exps)


subsubsection \<open>do while\<close>

lemma SemDoWhile_deterministic:
  assumes "SemDoWhile c s s1"
      and "SemDoWhile c s s2"
    shows "s1 = s2"
proof -
  have "SemDoWhile c s s1 \<Longrightarrow> (\<forall>s2. SemDoWhile c s s2 \<longrightarrow> s1 = s2)"
    by (induct rule: SemDoWhile.induct) (subst SemDoWhile.simps, simp)+
  thus ?thesis
    using assms by simp
qed

lemma SemDoWhile_deterministic2: " SemDoWhile body s x \<Longrightarrow> The ( SemDoWhile body s) = x"
  using SemDoWhile_deterministic by blast


lemma "__DoWhile__rule":
  "(\<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and>P x \<longmapsto> X x' \<heavy_comma> P x' \<tycolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<rbrace>)
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while TYPE('a::stack) body \<lbrace> X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. I x \<and> P x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. I x' \<and> \<not> P x' \<rbrace>"
  unfolding op_do_while_def Procedure_def Auto_def
  apply (auto simp add: SemDoWhile_deterministic2 nu_exps pair_forall LooseStateTy_expn')
  subgoal for a b x M c
    apply (rotate_tac 1)
    apply (induct  body "(a, b)" x arbitrary: a b c rule: SemDoWhile.induct)
    apply (metis fst_conv snd_conv state.sel state.simps(5) zero_neq_one)
    apply blast
     apply (metis state.distinct(1) state.distinct(5))
    apply (simp add: nu_exps pair_forall Heap'_expn)
    by (metis fst_conv snd_conv state.distinct(3) state.sel)
  done

thm "__DoWhile__rule"[simplified]

declare Heap'_expn[simp del]

lemma "__DoWhile___\<phi>app":
  "(\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X x \<longmapsto> X x' \<heavy_comma> P x' \<tycolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. True \<rbrace>)
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while TYPE('a::stack) body \<lbrace> X x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. \<not> P x' \<rbrace>"
(*  for X :: "(heap \<times> 'a::lrep, 'b) \<phi>" *)
  unfolding op_do_while_def Procedure_def Auto_def
  apply (auto simp add: SemDoWhile_deterministic2 nu_exps pair_forall)
  subgoal for a b xa H
    apply (rotate_tac 2)
    by (induct  body "(a, b)" xa arbitrary: a b x rule: SemDoWhile.induct)
        (auto 0 7 simp add: nu_exps pair_forall Heap'_expn)
  done
declare Heap'_expn[simp]


lemma do_while_\<phi>app:
  "Variant_Cast vars X X' \<longrightarrow>
  \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m cond \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond vars \<longrightarrow>
  (\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X' x \<longmapsto> \<exists>* x'. X' x' \<heavy_comma> cond x' \<tycolon> \<bool> \<rbrace>) \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while TYPE('a::stack) body \<lbrace> X \<longmapsto> \<exists>* x'. X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> cond x' \<rbrace>"
  unfolding Variant_Cast_def Premise_def apply simp
  using "__DoWhile___\<phi>app"[of "cond" _ "X'", unfolded Premise_def, simplified] by blast


lemma do_while_\<phi>app_old:
  "Variant_Cast vars X X' \<longrightarrow>
  \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m cond \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond vars \<longrightarrow>
  (\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<lbrace> X' x \<longmapsto> \<exists>* x'. X' x' \<heavy_comma> cond x' \<tycolon> \<bool> \<rbrace>) \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while TYPE('a::stack)  body \<lbrace> X \<longmapsto> \<exists>* x'. X' x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j \<not> cond x' \<rbrace>"
  unfolding Variant_Cast_def Premise_def apply simp
  using "__DoWhile___\<phi>app"[of "cond" _ "X'", unfolded Premise_def, simplified] by blast


subsubsection \<open>while\<close>


proc while: \<open>X'\<close> :: "'s::stack" \<longmapsto> \<open>X x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. \<not> cond x\<close>
  requires [unfolded Variant_Cast_def, simp]: "Variant_Cast vars X' X"
    and Cond_\<phi>app: "\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c (Cond :: 's::stack \<longmapsto> 1 word \<times> 's) \<lbrace> X x \<longmapsto> X x' \<heavy_comma> cond x' \<tycolon> \<bool> \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. True\<rbrace>"
    and Body_\<phi>app: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (Body :: 's \<longmapsto> 's) \<lbrace> X x \<longmapsto> X x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. True \<rbrace>"
  \<bullet> Cond if \<medium_left_bracket> do_while var x' \<open>cond x'\<close> \<medium_left_bracket> Body Cond \<medium_right_bracket> subj \<open>\<not> cond x'\<close> \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> generalize \<open>x'\<close> x' \<open>\<lambda>x'. \<not> cond x'\<close> \<medium_right_bracket>
  finish

subsubsection \<open>recursion\<close>

lemma SemRec_IR: "SemRec F x y \<Longrightarrow> SemRec (F o F) x y"
  by (induct rule: SemRec.induct, rule SemRec_I0, simp)

lemma SemRec_deterministic:
  assumes "SemRec c s s1" and "SemRec c s s2" shows "s1 = s2"
proof -
  have "SemRec c s s1 \<Longrightarrow> (\<forall>s2. SemRec c s s2 \<longrightarrow> s1 = s2)"
    apply (induct rule: SemRec.induct)
     apply clarify
    subgoal for F a b y s2 apply (rotate_tac 1)
      apply (induct rule: SemRec.induct) by auto 
    apply clarify apply (blast intro: SemRec_IR) done
  thus ?thesis using assms by simp
qed

lemma SemRec_deterministic2: " SemRec body s x \<Longrightarrow> The ( SemRec body s) = x"
  using SemRec_deterministic by blast


declare Heap'_expn[simp del]


lemma op_recursion:
  " (\<And>g x'. (\<forall>x''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> X x'' \<longmapsto> Y x'' \<rbrace>) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g \<lbrace> X x' \<longmapsto> Y x' \<rbrace>) \<Longrightarrow>
    (\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion UNIQ_ID TYPE('x::stack) TYPE('y::stack) F \<lbrace> X x \<longmapsto> Y x \<rbrace>)"
  unfolding op_recursion_def Procedure_def atomize_all
  apply (auto simp add: SemRec_deterministic2)
  subgoal for x a b xa
    apply (rotate_tac 1) apply (induct rule:  SemRec.induct) by (auto 0 6) done

declare Heap'_expn[simp]


subsection \<open>Constant Pushing\<close>

subsubsection \<open>Integer\<close>

lemma [\<phi>reason on ?any]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e ((numeral x) \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (numeral x) \<lbrace> R \<longmapsto> R \<heavy_comma> (numeral x) \<tycolon> \<nat>['w] \<rbrace>"
  unfolding op_const_int_def \<phi>def by (auto simp add: nu_exps) (metis mod_if unat_bintrunc unat_numeral)
  \<comment> \<open>Only literal number could be constructed automatically\<close>

lemma [\<phi>reason on ?any]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<lbrace> R \<longmapsto> R \<heavy_comma> 0 \<tycolon> \<nat>['w] \<rbrace>"
  unfolding MakeTag_def \<phi>def op_const_int_def by (auto simp add: nu_exps)

lemma [\<phi>reason on ?any]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (1 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<lbrace> R \<longmapsto> R \<heavy_comma> 1 \<tycolon> \<nat>['w] \<rbrace>"
  unfolding MakeTag_def \<phi>def op_const_int_def by (auto simp add: nu_exps)

lemma [\<phi>reason on ?any]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e ((numeral x) \<tycolon> \<nat>\<^sup>r['w])
   \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (numeral x) \<lbrace> R \<longmapsto> R \<heavy_comma> (numeral x) \<tycolon> \<nat>\<^sup>r['w] \<rbrace>"
  unfolding op_const_int_def \<phi>def by (auto simp add: nu_exps)

lemma [\<phi>reason on ?any]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<lbrace> R \<longmapsto> R \<heavy_comma> 0 \<tycolon> \<nat>\<^sup>r['w] \<rbrace>"
  unfolding op_const_int_def \<phi>def by (auto simp add: nu_exps)

lemma [\<phi>reason on ?any]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (1 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<lbrace> R \<longmapsto> R \<heavy_comma> 1 \<tycolon> \<nat>\<^sup>r['w] \<rbrace>"
  unfolding op_const_int_def \<phi>def by (auto simp add: nu_exps)


lemma [\<phi>reason 1100 on ?any]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e ((numeral x) \<tycolon> \<nat>[size_t])
   \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t (numeral x) \<lbrace> R \<longmapsto> R \<heavy_comma> (numeral x) \<tycolon> \<nat>[size_t] \<rbrace>"
  unfolding op_const_size_t_def \<phi>def by (auto simp add: nu_exps nat_take_bit_eq take_bit_nat_eq_self_iff)


subsection \<open>Arithmetic\<close>

\<phi>overloads "+" and round_add and "<" and "\<le>" and "-" and "/" and "=" and "not" and "\<and>" and "\<or>"

subsubsection \<open>Common\<close>

term op_equal

theorem op_equal[\<phi>overload =]:
  "\<phi>Equal N P eq \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P a b
  \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (op_equal TYPE('a::{ceq,lrep}) :: 'a \<times> 'a \<times> 'r::stack \<longmapsto> 1 word \<times> 'r ) \<lbrace> a \<tycolon> N \<heavy_comma> b \<tycolon> N \<longmapsto> eq a b \<tycolon> \<bool> \<rbrace>"
  for N :: "('a::{ceq,lrep},'ax) \<phi>"
  unfolding \<phi>def op_equal_def by (auto 0 6 simp add: nu_exps)


subsubsection \<open>Integer\<close>

theorem add_nat_\<phi>app[\<phi>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^b \<longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b \<lbrace> x \<Ztypecolon> \<nat>[b] \<heavy_comma> y \<Ztypecolon> \<nat>[b] \<longmapsto> x + y \<Ztypecolon> \<nat>[b] \<rbrace>"
  unfolding op_add_def by (rule, elim Premise_E, rule \<phi>M_getV, simp add: \<phi>expns,
      rule \<phi>M_tail_left, rule \<phi>M_getV, simp add: \<phi>expns, rule \<phi>M_tail_right,
      rule \<phi>M_put_Val, simp add: \<phi>expns)

theorem add_nat_round[\<phi>overload +]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add b \<lbrace> x \<Ztypecolon> \<nat>\<^sup>r[b] \<heavy_comma> y \<Ztypecolon> \<nat>\<^sup>r[b] \<longmapsto> (x + y) \<Ztypecolon> \<nat>\<^sup>r[b] \<rbrace>"
  unfolding op_add_def by (rule \<phi>M_getV, simp_all add: \<phi>expns,
      rule \<phi>M_tail_left, rule \<phi>M_getV, simp_all add: \<phi>expns,
      rule \<phi>M_tail_right, rule \<phi>M_put_Val, simp add: \<phi>expns) presburger

theorem sub_nat_\<phi>app[\<phi>overload -]:
    "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x \<longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub TYPE('w::len) \<lbrace> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w] \<longmapsto> x - y \<tycolon> \<nat>['w] \<rbrace>"
  unfolding \<phi>def op_sub_def by (auto simp add: nu_exps) (meson unat_sub_if_size)

theorem udiv_nat_\<phi>app[\<phi>overload /]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_udiv TYPE('w::len) \<lbrace> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w] \<longmapsto> x div y \<tycolon> \<nat>['w] \<rbrace>"
  unfolding \<phi>def op_udiv_def by (auto simp add: nu_exps) (meson unat_div)

theorem op_lt_\<phi>app[\<phi>overload <]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt TYPE('w::len) \<lbrace> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w] \<longmapsto> (x < y) \<tycolon> \<bool> \<rbrace>"
  unfolding \<phi>def op_lt_def by (auto simp add: word_less_nat_alt nu_exps)

theorem op_le_\<phi>app[\<phi>overload \<le>]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le TYPE('w::len) \<lbrace> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w] \<longmapsto> (x \<le> y) \<tycolon> \<bool> \<rbrace>"
  unfolding \<phi>def op_le_def by (auto simp add: word_le_nat_alt nu_exps)

lemma boolean_not_\<phi>app[\<phi>overload not]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_not TYPE(1) \<lbrace> x \<tycolon> \<bool> \<longmapsto> \<not> x \<tycolon> \<bool> \<rbrace>"
  unfolding Procedure_def op_not_def apply (auto simp add: lrep_exps nu_exps)
  by (metis even_take_bit_eq even_zero iszero_def odd_numeral one_neq_zero)

lemma boolean_and_\<phi>app[\<phi>overload \<and>]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_and TYPE(1) \<lbrace> x \<tycolon> \<bool> \<heavy_comma> y \<tycolon> \<bool> \<longmapsto> x \<and> y \<tycolon> \<bool> \<rbrace>"
  unfolding Procedure_def op_and_def by (auto simp add: lrep_exps nu_exps)

lemma boolean_or_\<phi>app[\<phi>overload \<or>]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_or TYPE(1) \<lbrace> x \<tycolon> \<bool> \<heavy_comma> y \<tycolon> \<bool> \<longmapsto> x \<or> y \<tycolon> \<bool> \<rbrace>"
  unfolding Procedure_def op_or_def by (auto simp add: lrep_exps nu_exps)

subsection \<open>Field Index\<close>

subsubsection \<open>Abstraction\<close>

definition FieldIndex :: " ('a,'a,'ax,'ax) index \<Rightarrow> ('ax::lrep,'bx) \<phi> \<Rightarrow> ('a::lrep,'b) \<phi> \<Rightarrow> ('b \<Rightarrow> 'bx) \<Rightarrow> (('bx \<Rightarrow> 'bx) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>bool"
  where "FieldIndex adr X A gt mp \<longleftrightarrow> (\<forall>a f. \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<lbrace> gt a \<tycolon> X \<^bold>@ a \<tycolon> A \<longmapsto> f (gt a) \<tycolon> X \<^bold>@ mp f a \<tycolon> A \<rbrace>)"

lemma FieldIndex_here: "FieldIndex index_here X X id id"
  unfolding FieldIndex_def \<phi>index_def index_here_def by auto
lemma FieldIndex_left: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_left f) X (A \<cross_product> R) (gt o fst) (apfst o mp)"
  unfolding FieldIndex_def \<phi>index_def index_left_def by (auto simp add: nu_exps)
lemma FieldIndex_right: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_right f) X (R \<cross_product> A) (gt o snd) (apsnd o mp)"
  unfolding FieldIndex_def \<phi>index_def index_right_def by (auto simp add: nu_exps)

lemma FieldIndex_tupl: "FieldIndex f X A gt mp \<Longrightarrow> FieldIndex (index_tuple f) X \<lbrace> A \<rbrace> gt mp"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def by (auto simp add: tuple_forall nu_exps)

\<phi>processor field_index 110 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn major => Parse.nat >> (fn i => fn _ =>
  let open NuBasics NuHelp
    val arity = Logic.dest_implies (prop_of major) |> #1
        |> dest_Trueprop |> dest_quinop \<^const_name>\<open>FieldIndex\<close> |> #3
        |> dest_monop \<^const_name>\<open>NuTuple\<close> |> strip_binop_r \<^const_name>\<open>Fusion\<close> |> length
    val path1 = funpow (i-1) (fn th => th RS @{thm FieldIndex_right})
        (@{thm FieldIndex_here}
              |> (fn th => if arity = i then th else th RS @{thm FieldIndex_left}))
  in 
    (path1 RS (@{thm FieldIndex_tupl} RS major), ctx)
  end)\<close>



(*  WORK IN PROGRESS
subsection \<open>Field Index\<close>

lemma [\<phi>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ \<lbrace> A \<rbrace> \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ \<lbrace> A \<rbrace> \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<rbrace> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<rbrace>"
  unfolding \<phi>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<phi>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<lbrace> X \<^bold>@ \<lbrace> A \<rbrace> \<rbrace> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<phi>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

subsubsection \<open>Abstraction\<close>


\<phi>processor field_index 110 \<open>\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<lbrace> X \<^bold>@ A \<rbrace> \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn sequent =>
  Parse.nat >> (fn i => fn _ =>
  let open NuBasics NuHelp
    val A = Thm.major_prem_of sequent |> dest_Trueprop |> dest_triop \<^const_name>\<open>AdrGet\<close> |> #3
    val A = repeat (dest_monop \<^const_name>\<open>NuTuple\<close>)
    val arity = 1
val _ =
Logic.dest_implies (prop_of sequent) |> #1
        |> dest_Trueprop |> dest_quinop \<^const_name>\<open>FieldIndex\<close> |> #3
        |> dest_monop \<^const_name>\<open>NuTuple\<close> |> strip_binop_r \<^const_name>\<open>Fusion\<close> |> length
    val path1 = funpow (i-1) (fn th => th RS @{thm FieldIndex_right})
        (@{thm FieldIndex_here}
              |> (fn th => if arity = i then th else th RS @{thm FieldIndex_left}))
  in 
    (path1 RS (@{thm FieldIndex_tupl} RS major), ctx)
  end)\<close>

\<phi>processor field_index_getter 110 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn major => Parse.nat >> (fn i => fn _ =>
  let open NuBasics NuHelp
    val arity = Logic.dest_implies (prop_of major) |> #1
        |> dest_Trueprop |> dest_quinop \<^const_name>\<open>FieldIndex\<close> |> #3
        |> dest_monop \<^const_name>\<open>NuTuple\<close> |> strip_binop_r \<^const_name>\<open>Fusion\<close> |> length
    val path1 = funpow (i-1) (fn th => th RS @{thm FieldIndex_right})
        (@{thm FieldIndex_here}
              |> (fn th => if arity = i then th else th RS @{thm FieldIndex_left}))
  in 
    (path1 RS (@{thm FieldIndex_tupl} RS major), ctx)
  end)\<close>

*)
subsection \<open>Tuple Operations\<close>

subsubsection \<open>Construction & Destruction\<close>

theorem tup_\<phi>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup TYPE('a::field_list) \<lbrace> x \<tycolon> X \<longmapsto> x \<tycolon> \<lbrace> X \<rbrace>  \<rbrace>"
  for X :: "('a::field_list, 'ax) \<phi>"
  unfolding cons_tup_def Procedure_def by (simp add: pair_forall nu_exps)

theorem det_\<phi>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup TYPE('a::field_list) \<lbrace> x \<tycolon> \<lbrace> X \<rbrace> \<longmapsto> x \<tycolon> X \<rbrace>"
  for X :: "('a::field_list, 'ax) \<phi>"
  unfolding Procedure_def op_dest_tup_def by (simp add: tuple_forall pair_forall nu_exps)

subsubsection \<open>Field Accessing\<close>

lemma
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<rbrace> \<Longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_tuple idx TYPE('a::field_list) \<lbrace> VAL A \<longmapsto> VAL X \<rbrace> "
  for A :: " 'a::field_list tuple set"
  unfolding \<phi>index_def \<phi>def pair_forall op_get_tuple_def tuple_forall
  by (simp add: nu_exps)

lemma "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<lbrace> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<rbrace> \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_tuple idx TYPE('a::field_list) TYPE('y::lrep) \<lbrace> VAL A \<heavy_comma> VAL Y \<longmapsto> VAL B \<rbrace> "
  for A :: "'a::field_list tuple set" and Y :: "'y::lrep set"
  unfolding \<phi>index_def \<phi>def pair_forall op_set_tuple_def
  by (simp add: nu_exps)


subsection \<open>Memory & Pointer Operations\<close>

subsubsection \<open>Pointer Arithmetic\<close>


theorem op_shift_pointer[\<phi>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e address_llty addr = LLTY('a::lrep) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e offset_of addr + delta \<le> address_len addr \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer TYPE('a::lrep) \<lbrace> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> delta \<tycolon> \<nat>[size_t] \<longmapsto>
      R\<heavy_comma> addr ||+ delta \<tycolon> Pointer \<rbrace>"
  unfolding \<phi>def op_shift_pointer_def by (cases addr) (auto simp add: lrep_exps same_addr_offset_def nu_exps)


theorem op_shift_pointer_slice[ unfolded SepNu_to_SepSet, \<phi>overload split ]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < length xs \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer TYPE('p) \<lbrace> addr \<R_arr_tail> xs \<tycolon> Array T \<heavy_comma> addr \<tycolon> Pointer \<heavy_comma> n \<tycolon> \<nat>[size_t]
      \<longmapsto> (addr \<R_arr_tail> take n xs, shift_addr addr n \<R_arr_tail> drop n xs) \<tycolon> (Array T \<^emph> Array T) \<heavy_comma> addr ||+ n \<tycolon> Pointer \<rbrace>"
  for T :: "('p::field, 'x) \<phi>"
  unfolding \<phi>def op_shift_pointer_def Array_def Separation_expn_R pair_forall
  apply (cases addr)
  apply (auto simp add: lrep_exps same_addr_offset_def raw_offset_of_def distrib_right nu_exps
        add.commute add.left_commute pair_forall Shallowize'_expn intro: heap_split_id)
  subgoal for x1 x2 aa b H h1 h2
    apply (rule heap_split_id, simp)
    apply (rule heap_split_by_addr_set[of _ _ "- {(x1 |+ x2 + i) | i. i < n}"])
    apply (auto simp add: nu_exps) done
  done


subsubsection \<open>Allocation\<close>

lemma malloc_split: "Heap h \<Longrightarrow> P (heap_assignN n v (malloc h) Map.empty) h \<Longrightarrow>
    \<exists>h1 h2. heap_assignN n v (malloc h) h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  apply (rule exI[of _ "heap_assignN n v (malloc h) Map.empty"], rule exI[of _ h], simp)
  subgoal premises prems
    unfolding heap_assignN_def using prems(1)
    by (simp add: map_add_def fun_eq_iff resource_key_forall disjoint_rewL memaddr_forall dom_def
          malloc option.case_eq_if) done

lemma [intro]: "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" proof -
  have "AvailableSegments h \<subseteq> {seg} \<union> AvailableSegments (heap_assignN n v seg h)"
    unfolding AvailableSegments_def heap_assignN_def by auto 
  then show "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" 
    unfolding Heap_def using infinite_super by auto
qed

lemma heap_assignN_eval: "v \<in> T \<Longrightarrow> i < n \<Longrightarrow> heap_assignN n (Some (deepize v)) seg h \<^bold>a\<^bold>t (seg |+ i) \<^bold>i\<^bold>s T"
  unfolding MemAddrState_def addr_allocated_def heap_assignN_def by auto



      
theorem alloc_array_\<phi>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N \<Longrightarrow> \<phi>Zero N zero \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc TYPE('x)
      \<lbrace> n \<tycolon> \<nat>[size_t] 
        \<longmapsto> ptr \<R_arr_tail> replicate n zero \<tycolon> Array N \<heavy_comma> ptr \<tycolon> Pointer \<^bold>s\<^bold>u\<^bold>b\<^bold>j ptr. addr_cap ptr n \<rbrace>"
  for N :: "('x::{zero,field},'b)\<phi>"
  unfolding \<phi>def op_alloc_def Array_def
  apply (auto simp add: lrep_exps list_all2_conv_all_nth Let_def same_addr_offset_def nu_exps
      Separation_expn)
  subgoal for aa b M h2
  apply (rule malloc_split, simp add: heap_assignN_eval)
    apply (auto simp add: heap_assignN_eval nu_exps) done
  done


proc alloc : \<open>Void\<close> \<longmapsto> \<open>ptr \<R_arr_tail> zero \<tycolon> Ref T \<heavy_comma> ptr \<tycolon> Pointer \<^bold>s\<^bold>u\<^bold>b\<^bold>j ptr. addr_cap ptr 1\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m T" and [\<phi>reason on ?any]: "\<phi>Zero T zero"
  have A[simp]: "replicate 1 zero = [zero]" by (simp add: One_nat_def)
  \<bullet>\<open>1 \<tycolon> \<nat>[size_t]\<close> alloc_array T
  finish


subsubsection \<open>Load & Store\<close>

\<phi>overloads \<up> and "\<up>:" and \<Up> and "\<Up>:" and \<down> and "\<down>:" and \<Down> and "\<Down>:" and free

abbreviation "list_map_at f i l \<equiv> list_update l i (f (l ! i))"

lemma op_load[ \<phi>overload "\<up>:" ]:
  "FieldIndex field_index Y X gt mp \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load TYPE('y::field) TYPE('x) field_index
    \<lbrace> addr \<R_arr_tail> x \<tycolon> Ref X \<heavy_comma> addr \<tycolon> Pointer \<longmapsto> addr \<R_arr_tail> x \<tycolon> Ref X \<heavy_comma> gt x \<tycolon> Y\<rbrace> "
  for X :: "('x::field, 'a) \<phi>" and Y :: "('y::field, 'b) \<phi>"
  unfolding op_load_def Procedure_def \<phi>index_def Protector_def FieldIndex_def
  by (cases field_index, cases addr)
    (auto simp add: lrep_exps MemAddrState_def nu_exps disjoint_rewR split: option.split iff: addr_allocated_def)


lemmas [ \<phi>overload "\<up>" ] = op_load[THEN mp, OF FieldIndex_here, simplified]

proc i_load_n[\<phi>overload "\<up>:"]:
  \<open>a \<R_arr_tail> xs \<tycolon> Array X \<heavy_comma> a \<tycolon> Pointer \<heavy_comma> i \<tycolon> \<nat>[size_t]\<close> \<longmapsto> \<open>a \<R_arr_tail> xs \<tycolon> Array X \<heavy_comma> gt (xs ! i) \<tycolon> Y\<close>
  for Y :: "('y::field, 'd) \<phi>"
  premises "i < length xs"
  requires idx: "FieldIndex field_index Y X gt mp"
  obtain a' j where a: "a = (a' |+ j)" by (cases a)
  \<bullet> unfold a + \<up>: idx fold a
  finish

lemmas [ \<phi>overload "\<up>" ] = i_load_n_\<phi>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]

lemma op_store[ \<phi>overload "\<down>:" ]:
  "FieldIndex field_index Y X gt mp \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store TYPE('y::field) TYPE('x) field_index
    \<lbrace> addr \<R_arr_tail> x \<tycolon> Ref X \<heavy_comma> addr \<tycolon> Pointer \<heavy_comma> y \<tycolon> Y \<longmapsto> addr \<R_arr_tail> mp (\<lambda>_. y) x \<tycolon> Ref X\<rbrace> "
  for X :: "('x::field, 'c) \<phi>"
  unfolding op_store_def Procedure_def FieldIndex_def \<phi>index_def
  apply (cases field_index, cases addr)
  apply (auto simp add: lrep_exps Let_def nu_exps split: option.split iff: addr_allocated_def)
  apply (meson MemAddrState_E addr_allocated_def disjoint_rewR domI)
  subgoal premises prems for x1 x2 x1a x2a aa ofs b x2b M h1 h2 proof -
    have t1: "\<And>v. (h1 ++ h2)(MemAddress (x1a |+ x2a) \<mapsto> v) = (h1(MemAddress (x1a |+ x2a) \<mapsto> v)) ++ h2"
      using prems by (simp add: domIff map_add_upd_left)
    have t2: "\<And>v.  dom (h1(MemAddress (x1a |+ x2a) \<mapsto> v)) = dom h1"
      using prems by auto
    show ?thesis apply (unfold t1, rule heap_split_id, unfold t2, simp add: prems)
      using prems by (auto simp add: nu_exps MemAddrState_def)
  qed done

lemmas [ \<phi>overload "\<down>" ] = op_store[THEN mp, OF FieldIndex_here, simplified]

proc i_store_n[\<phi>overload "\<down>:"]:
  \<open>a \<R_arr_tail> xs \<tycolon> Array X \<heavy_comma> a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> y \<tycolon> Y\<close> \<longmapsto> \<open>ELE a \<R_arr_tail> xs[i := mp (\<lambda>_. y) (xs ! i)] \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<phi>"
  premises "i < length xs"
  requires idx: "FieldIndex field_index Y X gt mp"
  obtain a' j where a: "a = (a' |+ j)" by (cases a) 
  \<bullet> unfold a \<rightarrow> y + y \<down>: idx fold a
  finish

lemmas [ \<phi>overload "\<down>" ] = i_store_n_\<phi>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]


section \<open>Misc\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp] split_paired_All[simp]

proc times: \<open>R' \<heavy_comma> n \<tycolon> \<nat>['b::len]\<close> \<longmapsto> \<open>R x \<^bold>s\<^bold>u\<^bold>b\<^bold>j x. P x n\<close>
  requires [unfolded Variant_Cast_def, simp]: "Variant_Cast vars R' R"
  requires \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P\<close>
  premises \<open>P vars 0\<close>
  requires Body: \<open>\<forall>x i. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < n \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x i \<longrightarrow>
      \<^bold>p\<^bold>r\<^bold>o\<^bold>c (body :: 'b word \<times> '\<RR>::stack \<longmapsto> '\<RR>) \<lbrace> R x \<heavy_comma> i \<tycolon> \<nat>['b] \<longmapsto> R x' \<^bold>s\<^bold>u\<^bold>b\<^bold>j x'. P x' (Suc i)\<rbrace>\<close>
  \<bullet> \<rightarrow> n \<open>0 \<tycolon> \<nat>['b]\<close>
  \<bullet> while var vars i in \<open>R vars\<close>, i always \<open>i \<le> n \<and> P vars i\<close>
  \<bullet> \<medium_left_bracket> dup n < \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> -- i Body i 1 + cast ie \<open>Suc i\<close> \<medium_right_bracket> drop
  finish

proc split_array[\<phi>overload split]:
  argument \<open>ptr \<R_arr_tail> l \<tycolon> Array T \<heavy_comma> ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<close>
  return \<open>ptr \<R_arr_tail> take n l \<tycolon> Array T \<heavy_comma> (ptr ||+ n) \<R_arr_tail> drop n l \<tycolon> Array T \<heavy_comma> ptr ||+ n \<tycolon> Pointer\<close>
  premises [useful]: "n \<le> length l"
  \<bullet> + split_cast n
  finish

proc pop_array[\<phi>overload pop]: \<open>ptr \<R_arr_tail> l \<tycolon> Array T \<heavy_comma> ptr \<tycolon> Pointer\<close>
  \<longmapsto> \<open>(ptr ||+ 1) \<R_arr_tail> tl l \<tycolon> Array T \<heavy_comma> ptr \<R_arr_tail> hd l \<tycolon> Ref T \<heavy_comma> ptr ||+ 1 \<tycolon> Pointer\<close>
  premises A: "l \<noteq> []"
  have [useful]: "1 \<le> length l" by (meson Premise_def length_0_conv less_one not_le A)
  \<bullet> \<open>1 \<tycolon> \<nat>[size_t]\<close> + pop_cast
  finish


section \<open>Codegen\<close>

ML_file \<open>codegen/codegen.ML\<close>
ML_file \<open>codegen/NuSys.ML\<close>
ML_file \<open>codegen/NuPrime.ML\<close>
ML_file \<open>codegen/NuLLReps.ML\<close>
ML_file \<open>codegen/misc.ML\<close>
ML_file \<open>codegen/Instructions.ML\<close>


\<phi>export_llvm

end