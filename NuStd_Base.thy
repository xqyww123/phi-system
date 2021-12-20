theory NuStd_Base
  imports NuSys NuBasicAbstractors NuInstructions
  keywords
     "\<up>:" "\<Up>:" "\<down>:" "\<Down>:" "subj" "always" "--" :: quasi_command
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

section \<open>Declarations\<close>

\<nu>overloads singular and plural
\<nu>overloads split and split_cast and merge and pop and pop_cast and push

declare Separation_assoc[simp]

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]
declare Separation_assoc[simp]

section \<open>\<nu>-Types\<close>

subsection \<open>DeepModel\<close>

definition DeepModel :: "('a::lrep, 'b) \<nu> \<Rightarrow> (deep_model, 'b) \<nu>"
  where "DeepModel T x = {p. shallowize p \<nuLinkL> T \<nuLinkR> x}"

lemma [simp]: "deepize p \<nuLinkL> DeepModel T \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> T \<nuLinkR> x" unfolding DeepModel_def Refining_def by simp

subsection \<open>Ref\<close>

definition Ref  :: "('a::field, 'b) \<nu> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b) \<nu>"
  where "Ref T xx = {heap. (case xx of addr \<R_arr_tail> x \<Rightarrow> heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T)}"

lemma [simp]: "heap \<nuLinkL> Ref T \<nuLinkR> addr \<R_arr_tail> x \<longleftrightarrow> (heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T)"
  by (auto simp add: lrep_exps Ref_def Refining_def)
lemma [elim]: " addr \<R_arr_tail> x \<ratio> Ref T \<Longrightarrow> (x \<ratio> T \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (auto simp add: MemAddrState_def)

subsection \<open>Array'\<close>

definition Array' :: "('a::field, 'b) \<nu> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b option list) \<nu>"
  where "Array' N x' = {heap. (case x' of (base |+ ofs) \<R_arr_tail> xs \<Rightarrow>
    (\<forall>i < length xs. pred_option (\<lambda>x. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s x \<tycolon> N) (xs ! i)) \<and>
    ofs + length xs \<le> segment_len base \<and> segment_llty base = LLTY('a))}"

lemma [simp]: "heap \<nuLinkL> Array' N \<nuLinkR> (base |+ ofs) \<R_arr_tail> xs \<longleftrightarrow>
    (ofs + length xs \<le> segment_len base \<and>
    segment_llty base = LLTY('a) \<and>
    (\<forall>i < length xs. pred_option (\<lambda>x. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s x \<tycolon> N) (xs ! i))
)" for N :: "('a::field, 'b) \<nu>"
  by (auto simp add: lrep_exps Array'_def Refining_def)

lemma [elim,\<nu>elim]: "a \<R_arr_tail> xs \<ratio> Array' N \<Longrightarrow> (
    (\<And>i. i < length xs \<Longrightarrow> pred_option (\<lambda>x. x \<ratio> N) (xs ! i)) \<Longrightarrow> offset_of a + length xs \<le> address_len a \<Longrightarrow> address_llty a = LLTY('a)
  \<Longrightarrow> C) \<Longrightarrow> C"
   for N :: "('a::field, 'b) \<nu>"
  unfolding Inhabited_def[of "\<tort_lbrace>a \<R_arr_tail> xs \<tycolon> Array' N\<tort_rbrace>"]
  by (cases a) (auto simp add: lrep_exps pred_option_def list_all2_conv_all_nth)

lemma Array'_to_Ref_\<nu>app:
 "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m i \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! (i-j)) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a |+ j) \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> (a |+ j) \<R_arr_tail> xs[ (i-j) := None] \<tycolon> Array' N \<heavy_asterisk> (a |+ i) \<R_arr_tail> the (xs ! (i-j)) \<tycolon> Ref N"
  unfolding Dest_def Cast_def Heap_Divider_def
  apply (auto simp add: nu_exps) apply (rule heap_split_by_addr_set[of _  _ "-{a |+ i}"])
  subgoal premises prems for y v proof -
    define k where "k = i - j"
    have i: "i = j + k" unfolding k_def using prems by simp
    show ?thesis unfolding k_def[symmetric] unfolding i
      using prems[unfolded k_def[symmetric], unfolded i]
      by (auto  simp add: pred_option_def Ball_def nth_list_update)
  qed done

lemma [\<nu>intro]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! (i-j)) \<noteq> None \<Longrightarrow>
  \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a |+ j) \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> (a |+ j) \<R_arr_tail> xs[ (i-j) := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> (a |+ i) \<R_arr_tail> the (xs ! (i-j)) \<tycolon> Ref N \<medium_right_bracket>\<medium_right_bracket> \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Cast_def Heap_Cast_Goal_def
  using Array'_to_Ref_\<nu>app[unfolded Cast_def ParamTag_def] by blast

lemma Ref_to_Array':
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a |+ j) \<R_arr_tail> xs[ i-j := None] \<tycolon> Array' N \<heavy_asterisk> (a |+ i) \<R_arr_tail> y \<tycolon> Ref N \<longmapsto> (a |+ j) \<R_arr_tail> xs[ i-j := Some y] \<tycolon> Array' N"
  unfolding Intro_def Cast_def Heap_Divider_def Heap_Cast_Goal_def
  apply (auto simp add: pred_option_def Ball_def nu_exps)
  by (metis MemAddrState_add_I1 MemAddrState_add_I2 le_add_diff_inverse nth_list_update nth_list_update_neq option.sel)

lemma [\<nu>intro]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e j \<le> i \<and> i < j + length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! (i-j)) \<noteq> None \<Longrightarrow>
  \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a |+ j) \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> (a |+ j) \<R_arr_tail> xs[i-j := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> (a |+ i) \<R_arr_tail> the (xs ! (i-j)) \<tycolon> Ref N \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h True
      \<^bold>d\<^bold>u\<^bold>a\<^bold>l (a |+ j) \<R_arr_tail> xs[i-j := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> (a |+ i) \<R_arr_tail> y \<tycolon> Ref N \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> (a |+ j) \<R_arr_tail> xs[i-j := Some y] \<tycolon> Array' N \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Heap_Cast_Goal_def
  by (meson Array'_to_Ref_\<nu>app CastDual_I ParamTag Ref_to_Array')

(* lemma Ref_to_Array':
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H1 \<longmapsto> H2 \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> (a ||+ i) \<R_arr_tail> y \<tycolon> Ref N \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<medium_right_bracket>\<medium_right_bracket> \<Longrightarrow>
  \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H2 \<longmapsto> H3 \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<medium_right_bracket>\<medium_right_bracket> \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow>
  \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t H1  \<longmapsto> H3 \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> a \<R_arr_tail> xs[i := Some y] \<tycolon> Array' N \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2 \<medium_right_bracket>\<medium_right_bracket>" *)


lemma split_cast_Array'_\<nu>app[\<nu>overload split_cast]:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m n \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n \<le> length l \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l \<tycolon> Array' T \<longmapsto> a \<R_arr_tail> take n l \<tycolon> Array' T \<heavy_asterisk> (a ||+ n) \<R_arr_tail> drop n l \<tycolon> Array' T"
  unfolding Cast_def Premise_def Heap_Divider_def apply (cases a) apply (auto simp add: nu_exps min_absorb2) 
  subgoal for base ofs v
    apply (rule heap_split_by_set[of _ _ "{ MemAddress (base |+ ofs + i) | i. i < n}"])
    apply (auto simp add: pred_option_def Ball_def split: option.split)
    apply (rule MemAddrState_restrict_I2)
     apply (metis add.assoc add.commute less_diff_conv)
    by simp
  done

(*solve*)
lemma merge_cast_Array'_2_\<nu>app:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n = length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a ||+ n) \<R_arr_tail> l2 \<tycolon> Array' T \<heavy_asterisk> a \<R_arr_tail> l1 \<tycolon> Array' T \<longmapsto> a \<R_arr_tail> l1 @ l2 \<tycolon> Array' T "
  unfolding Cast_def Premise_def Heap_Divider_def apply (cases a)
  apply (auto simp add: nu_exps min_absorb2 pred_option_def Ball_def nth_append)
  by (smt (z3) MemAddrState_add_I1 add.assoc add.commute le_add_diff_inverse less_diff_conv2 not_le)

lemma merge_cast_Array'_\<nu>app:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ofs' = ofs + length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (base |+ ofs') \<R_arr_tail> l2 \<tycolon> Array' T \<heavy_asterisk> (base |+ ofs) \<R_arr_tail> l1 \<tycolon> Array' T \<longmapsto> (base |+ ofs) \<R_arr_tail> l1 @ l2 \<tycolon> Array' T "
  using merge_cast_Array'_2_\<nu>app[of _ _ "base |+ ofs", simplified] by blast

(* lemma Array'_dual_Ref_\<nu>app [\<nu>intro]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! i) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> the (xs ! i) \<tycolon> Ref N \<medium_right_bracket>
  \<^bold>d\<^bold>u\<^bold>a\<^bold>l a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> y \<tycolon> Ref N \<medium_right_bracket> \<longmapsto> a \<R_arr_tail> xs[i := Some y] \<tycolon> Array' N"
  unfolding CastDual_def Heap_Cast_Goal_def apply (simp add: Array'_to_Ref_\<nu>app)
  unfolding Cast_def apply (cases a) apply (auto simp add: pred_option_def Ball_def)
  by (metis MemAddrState_add_I1 MemAddrState_add_I2 nth_list_update option.sel)
*)


subsection \<open>Array\<close>

definition Array :: "('a::field, 'b) \<nu> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b list) \<nu>"
  where "Array N = Array' N <down-lift> (map_object id (map Some)) "

lemma Array_to_Array': "\<tort_lbrace>a \<R_arr_tail> l \<tycolon> Array T\<tort_rbrace> = \<tort_lbrace> a \<R_arr_tail> map Some l \<tycolon> Array' T \<tort_rbrace>"
  unfolding Array_def by auto
(* lemma [simp]: "heap \<nuLinkL> Array N \<nuLinkR> (base |+ ofs) \<R_arr_tail> xs \<longleftrightarrow>
    (ofs + length xs \<le> segment_len base \<and>
    segment_llty base = LLTY('a) \<and>
    (\<forall>i < length xs. heap \<^bold>a\<^bold>t base |+ (ofs + i) \<^bold>i\<^bold>s xs ! i \<tycolon> N)
)" for N :: "('a::field, 'b) \<nu>"
  by (auto simp add: lrep_exps Array_def) *)
  
lemma [elim,\<nu>elim]: "a \<R_arr_tail> xs \<ratio> Array N \<Longrightarrow> (
    (\<And>i. i < length xs \<Longrightarrow> xs ! i \<ratio> N) \<Longrightarrow> offset_of a + length xs \<le> address_len a \<Longrightarrow> address_llty a = LLTY('a)
  \<Longrightarrow> C) \<Longrightarrow> C"
   for N :: "('a::field, 'b) \<nu>"
  unfolding Inhabited_def[of "\<tort_lbrace>a \<R_arr_tail> xs \<tycolon> Array N\<tort_rbrace>"]
  unfolding Array_def
  by (cases a) (auto simp add: lrep_exps list_all2_conv_all_nth)

(* lemma [THEN cast_trans, simplified, \<nu>intro 50]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> map Some xs \<tycolon> Array' N"
  unfolding Cast_def Array_def by (cases a) auto *)

definition mapSome :: " 'a list \<Rightarrow> 'a option list " where "mapSome = map Some"
lemma [simp]: "length (mapSome l) = length l" unfolding mapSome_def by auto
lemma [simp]: "i < length l \<Longrightarrow> mapSome l ! i = Some (l ! i)" unfolding mapSome_def by auto
lemma [simp]: "i < length l \<Longrightarrow> (mapSome l) [i := Some v] = mapSome (l [i:=v])" unfolding mapSome_def by (metis map_update)
lemma [simp]: "i < length l \<Longrightarrow> the (mapSome l ! i) = l ! i" unfolding mapSome_def by auto


lemma Array'_cast_Array: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs' = mapSome xs2 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs' \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N"
  unfolding Cast_def Intro_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def)
lemma Array_cast_Array': "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> mapSome xs \<tycolon> Array' N"
  unfolding Cast_def Dest_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def)

lemma [\<nu>intro -100000]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> a \<R_arr_tail> xs' \<tycolon> Array' N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs' = mapSome xs2 \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def using Array'_cast_Array[unfolded Cast_def] by blast

lemma [\<nu>intro -100000]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> mapSome xs \<tycolon> Array' N \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def using Array_cast_Array'[unfolded Cast_def] by blast

lemma [\<nu>intro -100000]:
  "\<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> mapSome xs \<tycolon> Array' N \<longmapsto> H \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> a \<R_arr_tail> xs'\<^sub>m \<tycolon> Array' N \<medium_right_bracket>\<medium_right_bracket> \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs'\<^sub>m = mapSome xs\<^sub>m \<Longrightarrow>
   \<medium_left_bracket>\<medium_left_bracket> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> H \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> X \<medium_right_bracket>\<medium_right_bracket> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<heavy_asterisk> \<medium_left_bracket>\<medium_left_bracket> X\<^sub>m \<medium_right_bracket>\<medium_right_bracket> \<longmapsto> a \<R_arr_tail> xs\<^sub>m \<tycolon> Array N \<medium_right_bracket>\<medium_right_bracket>"
  unfolding Heap_Cast_Goal_def  CastDual_def Cast_def
  using Array_cast_Array'[unfolded Cast_def] Array'_cast_Array[unfolded Cast_def] by blast

(* lemma single_Array_is_Ref: "\<tort_lbrace>a \<R_arr_tail> [x] \<tycolon> Array T\<tort_rbrace> = \<tort_lbrace>a \<R_arr_tail> x \<tycolon> Ref T\<tort_rbrace>"
  unfolding Array_def by (cases a) (auto simp add: pred_option_def Ball_def) *)

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> [x] \<tycolon> Array T \<longmapsto> a \<R_arr_tail> x \<tycolon> Ref T"
  unfolding Cast_def Array_def by (cases a) (simp add: pred_option_def Ball_def)

lemma split_cast_Array_\<nu>app[\<nu>overload split_cast]:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m n \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n \<le> length l \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l \<tycolon> Array T \<longmapsto> a \<R_arr_tail> take n l \<tycolon> Array T \<heavy_asterisk> (a ||+ n) \<R_arr_tail> drop n l \<tycolon> Array T"
  by (simp add: Array_to_Array'
      split_cast_Array'_\<nu>app[of n "map Some l" a T, simplified, simplified take_map drop_map])

lemma pop_cast_Array'_\<nu>app[\<nu>overload pop_cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e l \<noteq> [] \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l \<tycolon> Array T \<longmapsto> (a ||+ 1) \<R_arr_tail> tl l \<tycolon> Array T \<heavy_asterisk> a \<R_arr_tail> hd l \<tycolon> Ref T"
  unfolding Premise_def sorry 

lemma push_Array'_2_\<nu>app[\<nu>overload push]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t (a ||+ 1) \<R_arr_tail> l \<tycolon> Array T \<heavy_asterisk> a \<R_arr_tail> x \<tycolon> Ref T \<longmapsto> a \<R_arr_tail> x # l \<tycolon> Array T"
  unfolding Premise_def sorry 

lemma push_Array'_\<nu>app[\<nu>overload push]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i' = i + 1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a |+ i') \<R_arr_tail> l \<tycolon> Array T \<heavy_asterisk> (a |+ i) \<R_arr_tail> x \<tycolon> Ref T \<longmapsto> (a |+ i) \<R_arr_tail> x # l \<tycolon> Array T"
  unfolding Premise_def sorry

  (*subgoal premises prems 
proof -
  have t1: "1 \<le> length l"
    by (metis One_nat_def Suc_leI length_greater_0_conv list.size(3) not_one_le_zero prems)
  have t2: "take 1 l = [hd l]" by (simp add: take_Suc prems)
  have t3: "drop 1 l = tl l" by (simp add: drop_Suc prems) 

  thm split_cast_Array_\<nu>app[of 1 l, unfolded Premise_def ParamTag_def, simplified t1, simplified t2 t3]
  thm One_nat_def Suc_le_eq length_greater_0_conv
*)

lemma merge_cast_Array_2_\<nu>app[\<nu>overload merge]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n = length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (a ||+ n) \<R_arr_tail> l2 \<tycolon> Array T \<heavy_asterisk> a \<R_arr_tail> l1 \<tycolon> Array T \<longmapsto> a \<R_arr_tail> l1 @ l2 \<tycolon> Array T "
  unfolding Array_to_Array' map_append
  using merge_cast_Array'_2_\<nu>app[of _ "map Some l1", simplified] .

lemma merge_cast_Array_\<nu>app[\<nu>overload merge]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ofs' = ofs + length l1 \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (base |+ ofs') \<R_arr_tail> l2 \<tycolon> Array T \<heavy_asterisk> (base |+ ofs) \<R_arr_tail> l1 \<tycolon> Array T \<longmapsto> (base |+ ofs) \<R_arr_tail> l1 @ l2 \<tycolon> Array T "
  using merge_cast_Array_2_\<nu>app[of _ _ "base |+ ofs", simplified] by blast



(* lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> x \<tycolon> Ref T \<longmapsto> a \<R_arr_tail> [x] \<tycolon> Array T"
  unfolding Cast_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def) *)

(* lemma [THEN cast_dual_trans, \<nu>intro]: 
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> a \<R_arr_tail> mapSome xs \<tycolon> Array' N
  \<^bold>d\<^bold>u\<^bold>a\<^bold>l a \<R_arr_tail> xs' \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N \<^bold>w\<^bold>h\<^bold>e\<^bold>n xs' = mapSome xs2"
  unfolding Cast_def CastDual_def Array_def by (cases a) (auto simp add: pred_option_def Ball_def) *)


subsection \<open>Numbers\<close>

\<nu>overloads nat and int

lemma unat_nat: assumes a0:"0 < x" and a1:"sint (xa::('a::len) word) = x"
  shows "unat xa = nat x"
proof-
  have a00:"0 < sint xa"
    by (simp add: a0 a1)
  then have "bit xa (LENGTH('a) - Suc 0)  = False"
    using bit_last_iff by force  
  moreover have "signed_take_bit (LENGTH('a) - Suc 0) xa = xa"
    by (metis scast_id signed_scast_eq) 
  moreover have "sint xa =  signed_take_bit (LENGTH('a) - Suc 0) (uint xa)"using sint_uint by auto
  ultimately have "uint xa = sint xa"
    using bit_uint_iff signed_take_bit_eq_if_positive uint_take_bit_eq 
    by metis 
  then show ?thesis using a0 a1 by auto
qed


lemma [\<nu>overload nat]: 
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e 0 < x \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> \<int>['bits::len] \<longmapsto> nat x \<tycolon> \<nat>['bits]"
  unfolding Cast_def Premise_def apply (simp add: lrep_exps nu_exps) using unat_nat  by auto

lemma sint_int: assumes a0:"x < 2 ^ (LENGTH('bits::len) - Suc 0)" and a1:"unat (xa::'bits word) = x"
  shows "sint xa = int x"
proof-
  have a00:"unat xa <  2 ^ (LENGTH('bits) - Suc 0)"
    by (simp add: a0 a1)  
  then have "bit xa (LENGTH('bits) - Suc 0)  = False"
    apply transfer apply auto  
    by (metis bit_take_bit_iff decr_length_less_iff linorder_not_le 
        order_less_irrefl take_bit_int_eq_self_iff take_bit_nonnegative) 
  moreover have "sint xa =  signed_take_bit (LENGTH('bits) - Suc 0) (uint xa)"using sint_uint by auto
  ultimately have "uint xa = sint xa"
    using bit_uint_iff signed_take_bit_eq_if_positive uint_take_bit_eq 
    by (metis scast_id signed_of_int  word_of_int_uint)     
  then show ?thesis using a0 a1 by auto
qed

lemma [\<nu>overload int]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x < 2^(LENGTH('bits) - 1) \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> \<nat>['bits::len] \<longmapsto> int x \<tycolon> \<int>['bits]"
  unfolding Cast_def Premise_def apply (simp add: lrep_exps nu_exps)
  by (simp add: sint_int One_nat_def) 


section \<open>Procedures and Operations\<close>

subsection \<open>Basic sequential instructions\<close>

subsubsection \<open>crash\<close>

lemma crash_\<nu>app[no_atp]:  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_crash \<blangle> X \<longmapsto> Y \<brangle>" unfolding \<nu>def op_crash_def by auto

subsubsection \<open>drop\<close>

declare op_drop_def[\<nu>instr]
theorem drop_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> R\<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_drop_def by (auto simp add: nu_exps)

subsubsection \<open>duplication\<close>

declare op_dup_def[\<nu>instr]
lemma bring:
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ R \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dup idx \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing\<brangle>"
  unfolding \<nu>def op_dup_def \<nu>index_def by (auto simp add: nu_exps)

lemmas "&_\<nu>app" = bring
lemmas dup_\<nu>app = bring[OF index_left_getter, OF index_here_getter]


subsubsection \<open>pair & de-pair\<close>

(* declare op_pair_def[\<nu>instr] op_depair_def[\<nu>instr] *)

lemma pr_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pair \<blangle> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B)\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def  op_pair_def by (auto simp add: nu_exps)
lemma dpr_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_depair \<blangle> R \<heavy_comma> (a,b) \<tycolon> (A \<cross_product> B)\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> a \<tycolon> A \<heavy_comma> b \<tycolon> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def  op_depair_def by (auto simp add: nu_exps)

lemma hpr_\<nu>app: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<heavy_asterisk> h1 \<tycolon> H1 \<heavy_asterisk> h2 \<tycolon> H2 \<longmapsto> H \<heavy_asterisk> (h2,h1) \<tycolon> H2 \<^emph> H1"
  unfolding Cast_def SepNu_to_SepSet Separation_assoc by blast
lemma hdpr_\<nu>app: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t H \<heavy_asterisk> (h2,h1) \<tycolon> H2 \<^emph> H1 \<longmapsto> H \<heavy_asterisk> h1 \<tycolon> H1 \<heavy_asterisk> h2 \<tycolon> H2"
  unfolding Cast_def SepNu_to_SepSet Separation_assoc by blast

(* \<nu>processor pair_auto_dest 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B) \<flower> W)\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema} |> NuSys.accept_proc ctx)\<close>
\<nu>processor pair_auto_dest' 30 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> (a,b) \<tycolon> (A \<nuFusion>' B))\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta |> NuBasics.apply_proc_naive @{thm dpr_auto_schema'} |> NuSys.accept_proc ctx)\<close> *)

subsubsection \<open>let & local_value\<close>

lemma op_let: " (\<And>p. p \<nuLinkL> A \<nuLinkR> a \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body p \<blangle> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> X' \<brangle>) \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_let body \<blangle> S\<heavy_comma> a \<tycolon> A\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> X' \<brangle>"
  unfolding Procedure_def op_let_def by (auto simp add: nu_exps)

lemma op_local_value: "v \<nuLinkL> A \<nuLinkR> a \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_local_value v \<blangle> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> S\<heavy_comma> a \<tycolon> A\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding Procedure_def op_local_value_def by (auto simp add: nu_exps)

ML_file "library/local_value.ML"

\<nu>processor let_local_value 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [\<HH>] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H)\<close> \<open>let open Parse in
  fn ctx => fn sequent => (($$$ "\<rightarrow>" || $$$ "--") -- list1 binding) >> (fn (keyword,idts) => fn _ =>
    Local_Value.mk_let (keyword = "--") (rev idts) sequent ctx
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
lemma strip_end_tail: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> A \<longmapsto> \<^bold>E\<^bold>N\<^bold>D\<heavy_comma> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c strip_end_tail f \<blangle> R\<heavy_comma> A \<longmapsto> R\<heavy_comma> B \<brangle>"
  unfolding strip_end_tail_def Procedure_def bind_def by (auto 4 4)
*)


subsection \<open>Branches & Loops\<close>

subsubsection \<open>sel\<close>

lemma sel_\<nu>app:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sel TYPE('a::lrep) \<blangle> R\<heavy_comma> a \<tycolon> T\<heavy_comma> b \<tycolon> T\<heavy_comma> c \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (if c then a else b) \<tycolon> T\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle> "
  unfolding Procedure_def op_sel_def by (auto simp add: nu_exps)

subsubsection \<open>Branch Convergence\<close>

named_theorems branch_convergence
consts branch_convergence_setting :: mode

abbreviation BrCon_Simplify :: " 'a \<Rightarrow> 'a \<Rightarrow> bool " ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>b\<^bold>r\<^bold>a\<^bold>n\<^bold>c\<^bold>h] _ : _" [1000,27] 26)
  where "BrCon_Simplify \<equiv> Simplify branch_convergence_setting"

lemma ExSet_if_simu: "(if P then (\<exists>*a. A a) else (\<exists>*a. B a)) \<equiv> (\<exists>*a. if P then A a else B a)" unfolding atomize_eq by auto
lemma ExSet_if_right: "(if P then A else (\<exists>*a. B a)) \<equiv> (\<exists>*a. if P then A else B a)" unfolding atomize_eq by auto
lemma ExSet_if_left: "(if P then (\<exists>*a. A a) else B) \<equiv> (\<exists>*a. if P then A a else B)" unfolding atomize_eq by auto

lemma Subj_simu: "(if P then A \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q else B \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<equiv> ((if P then A else B) \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q)" unfolding atomize_eq by auto
lemma Subj_left: "(if P then A \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q else B) \<equiv> ((if P then A else B) \<^bold>s\<^bold>u\<^bold>b\<^bold>j (P \<longrightarrow> Q))" unfolding atomize_eq by auto
lemma Subj_right: "(if P then A else B \<^bold>s\<^bold>u\<^bold>b\<^bold>j Q) \<equiv> ((if P then A else B) \<^bold>s\<^bold>u\<^bold>b\<^bold>j (\<not>P \<longrightarrow> Q))" unfolding atomize_eq by auto

ML_file \<open>library/branch_convergence.ML\<close>


\<nu>reasoner \<open>BrCon_Simplify\<close> 1000 (\<open>BrCon_Simplify x y\<close>) = \<open>fn ctxt =>
  let open Nu_BrCon_Simplify
    val ctxt = Raw_Simplifier.clear_simpset ctxt
          addsimps Named_Theorems.get ctxt \<^named_theorems>\<open>branch_convergence\<close>
          addsimprocs [simp_ex_proc, simp_subj_proc]
  in HEADGOAL (fn i => simp_tac ctxt i o @{print}) THEN
     HEADGOAL (resolve0_tac @{thms Simplify_I})
  end
\<close>

declare if_cancel[branch_convergence]
lemma [branch_convergence]:
  "(if P then \<tort_lbrace>x \<tycolon> X\<tort_rbrace> else \<tort_lbrace>y \<tycolon> Y\<tort_rbrace>) = \<tort_lbrace>(if P then x else y) \<tycolon> (if P then X else Y)\<tort_rbrace>" by simp
lemma [branch_convergence]:
  "(if P then (a,b) else (a',b')) = ((if P then a else a'), (if P then b else b'))" by simp
(* lemma AA: "(if P then A else B) = (\<lambda>x. if P then A x else B x)" by simp *)
lemma [branch_convergence]:
  "(if P then (S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) else (S'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H')) = ((if P then S else S')\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (if P then H else H'))" by simp
lemma [branch_convergence]:
  "(if P then (A\<heavy_comma> B) else (A'\<heavy_comma> B')) = ((if P then A else A')\<heavy_comma> (if P then B else B'))" by simp
lemma [branch_convergence]:
  "(if P then (A \<heavy_asterisk> B) else (A' \<heavy_asterisk> B')) = ((if P then A else A') \<heavy_asterisk> (if P then B else B'))" by simp
(* lemma [simp]: "(if P then (A \<^bold>a\<^bold>n\<^bold>d B) else (A' \<^bold>a\<^bold>n\<^bold>d B')) = ((if P then A else A') \<^bold>a\<^bold>n\<^bold>d (if P then B else B'))"  by auto *)
lemma [branch_convergence]:
  "(if P then Labelled name T else Labelled name' T') = Labelled name (if P then T else T')" unfolding Labelled_def by simp
lemma [branch_convergence]:
  "(if P then a \<R_arr_tail> x else a \<R_arr_tail> x') = a \<R_arr_tail> (if P then x else x')" by auto

(*TODO: implement the simproc retaining name of bound variables*)

subsubsection \<open>if\<close>

declare op_if_def[\<nu>instr]

lemma if_\<nu>app:
  "(cond \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_true \<blangle> X \<longmapsto> Y\<^sub>T \<brangle>)
    \<longrightarrow> (\<not> cond \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c branch_false \<blangle> X \<longmapsto> Y\<^sub>F \<brangle>)
    \<longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y[\<^bold>b\<^bold>r\<^bold>a\<^bold>n\<^bold>c\<^bold>h] Y : (if cond then Y\<^sub>T else Y\<^sub>F)
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if TYPE('y::stack) branch_true branch_false \<blangle> X \<heavy_comma>^ cond \<tycolon> \<bool> \<longmapsto> Y \<brangle>"
  unfolding \<nu>def op_if_def by (auto simp add: nu_exps)

(* text \<open>Despite the feasibility of divergence of \<nu>-types in the branch, i.e.
  \<^term>\<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_if branch_true branch_false \<blangle> x \<tycolon> X \<heavy_comma>^ cond \<tycolon> \<bool> \<longmapsto> (if cond then y\<^sub>T else y\<^sub>F) \<tycolon> (if cond then Y\<^sub>T else Y\<^sub>F ) \<brangle>\<close>,
  from the design of the programming principles, considering the role of \<nu>-types which encodes the invariant properties,
  we prohibit the divergence of \<nu>-types.\<close> *)



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

declare Heap'_expn[simp del]
lemma "__DoWhile___\<nu>app":
  "(\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<blangle> X x \<longmapsto> \<exists>* x'. X x' \<heavy_comma>^ P x' \<tycolon> \<bool> \<brangle>)
    \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while TYPE('a::stack) body \<blangle> X x \<longmapsto> \<exists>* x'. X x' \<and>\<^sup>s (\<not> P x') \<brangle>"
(*  for X :: "(heap \<times> 'a::lrep, 'b) \<nu>" *)
  unfolding op_do_while_def Procedure_def Auto_def
  apply (auto simp add: SemDoWhile_deterministic2 nu_exps Heap'_Stack_Front Heap'_ExSet Heap'_Addition)
  subgoal for a b xa H
    apply (rotate_tac 2)
    by (induct  body "(a, b)" xa arbitrary: a b x rule: SemDoWhile.induct) (auto 0 7 simp add: nu_exps)
  done
declare Heap'_expn[simp]


lemma do_while_\<nu>app:
  "Variant_Cast vars S H S' H' \<longrightarrow>
  \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m cond \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond vars \<longrightarrow>
  (\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<blangle> S' x\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H' x \<longmapsto> \<exists>* x'. (S' x' \<heavy_comma> cond x' \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H' x') \<brangle>) \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_do_while TYPE('a::stack)  body \<blangle> S\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> \<exists>* x'. (S' x'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H' x') \<and>\<^sup>s (\<not> cond x') \<brangle>"
  unfolding Variant_Cast_def Premise_def apply simp
  using "__DoWhile___\<nu>app"[of "cond" _ "(\<lambda>x. S' x\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H' x)", unfolded Premise_def, simplified] by blast


subsubsection \<open>while\<close>

proc while: \<open>S'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H'\<close> \<longmapsto> \<open>\<exists>* x. (S x\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x) \<and>\<^sup>s (\<not> cond x)\<close>
  for S' :: " 'b::stack set"
  requires [unfolded Variant_Cast_def, simp]: "Variant_Cast vars S' H' S H"
    and Cond_\<nu>app: "\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c Cond \<blangle> S x\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x \<longmapsto> \<exists>* x'. (S x'\<heavy_comma> cond x' \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x')\<brangle>"
    and Body_\<nu>app: "\<forall>x. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e cond x \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c Body \<blangle> S x\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x \<longmapsto> \<exists>* x'. (S x'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x') \<brangle>"
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
lemma op_recursion':
  "(\<And>g x'. (\<forall>x''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> X x'' \<longmapsto> Y x'' \<brangle>) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g \<blangle> X x' \<longmapsto> Y x' \<brangle>) \<Longrightarrow>
    (\<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion' F \<blangle> X x \<longmapsto> Y x \<brangle>)"
  (* for X :: "'b \<Rightarrow> (heap \<times> 'a::lrep, 'b) \<nu>" *)
  unfolding op_recursion'_def Procedure_def Function_def atomize_all
  apply (auto simp add: SemRec_deterministic2)
  subgoal for x a b xa apply (rotate_tac 1) apply (induct rule:  SemRec.induct) by (auto 0 6) done
declare Heap'_expn[simp]

lemma op_recursion:
  "(\<And>g x'. (\<forall>x''. \<^bold>f\<^bold>u\<^bold>n\<^bold>c g \<blangle> X x'' \<longmapsto> Y x'' \<brangle>) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g \<blangle> X x' \<longmapsto> Y x' \<brangle>) \<Longrightarrow>
    (\<forall>x. \<^bold>f\<^bold>u\<^bold>n\<^bold>c op_recursion UNIQ_ID TYPE('x::lrep) TYPE('y::lrep) F \<blangle> X x \<longmapsto> Y x \<brangle>)"
  unfolding op_recursion_def func_ALL Function_def apply simp
  using op_recursion'[of X Y "F o func", simplified] .

hide_const op_recursion'
hide_fact op_recursion'


subsection \<open>Constant Pushing\<close>

subsubsection \<open>Integer\<close>

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e ((numeral x) \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (numeral x)
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> (numeral x) \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps) (metis mod_if unat_bintrunc unat_numeral)
  \<comment> \<open>Only literal number could be constructed automatically\<close>

lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R \<heavy_comma> 0 \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding MakeTag_def \<nu>def op_const_int_def by (auto simp add: nu_exps)

lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (1 \<tycolon> \<nat>['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> 1 \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding MakeTag_def \<nu>def op_const_int_def by (auto simp add: nu_exps)

lemma [\<nu>intro]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (numeral x :: nat) < 2^LENGTH('w) \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e ((numeral x) \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (numeral x)
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> (numeral x) \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps)

lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (0 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 0 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> 0 \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps)

lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e (1 \<tycolon> \<nat>\<^sup>r['w]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) 1 \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> 1 \<tycolon> \<nat>\<^sup>r['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_int_def \<nu>def including show_more1 by (auto simp add: nu_exps)


lemma [\<nu>intro 1100]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e ((numeral x) \<tycolon> \<nat>[size_t]) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_size_t (numeral x)
    \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto> R\<heavy_comma> (numeral x) \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding op_const_size_t_def \<nu>def by (auto simp add: nu_exps nat_take_bit_eq take_bit_nat_eq_self_iff)


subsection \<open>Arithmetic\<close>

\<nu>overloads "+" and round_add and "<" and "\<le>" and "-" and "/" and "=" and "not"

subsubsection \<open>Common\<close>

theorem op_equal[\<nu>overload =]:
  "\<nu>Equal N P eq \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P a b
  \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_equal TYPE('a::{ceq,lrep}) \<blangle> R\<heavy_comma> a \<tycolon> N\<heavy_comma> b \<tycolon> N\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> eq a b \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_equal_def by (auto 0 6 simp add: nu_exps)


subsubsection \<open>Integer\<close>

(* theorem const_nat_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) c \<blangle> R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> c \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_const_int_def apply (auto simp add: nu_exps) *)
(* theorem const_nat_round_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_const_int TYPE('w::len) (of_nat n) \<blangle> R \<longmapsto> R \<heavy_comma> n \<tycolon> \<nat>\<^sup>r['w] \<brangle>"
  unfolding \<nu>def op_const_int_def by auto *)

(* schematic_goal "\<^bold>m\<^bold>a\<^bold>k\<^bold>e 3 \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f
  \<blangle>\<flower_L>\<medium_left_bracket> A \<flower_L>\<flower>\<flower_R>X\<medium_right_bracket>\<flower_R>   \<longmapsto> ?T \<brangle>" by (rule \<nu>intro) *)

(* instantiation typing :: (lrep, plus) plus begin
definition plus_typing :: "('a,'b) typing \<Rightarrow> ('a,'b) typing \<Rightarrow> ('a,'b) typing"
  where "nu_of a = nu_of b \<Longrightarrow> plus_typing a b = (case a of xa \<tycolon> Na \<Rightarrow> case b of xb \<tycolon> Nb \<Rightarrow> xa + xb \<tycolon> Na)"
lemma [simp]: "(x \<tycolon> N) + (y \<tycolon> N) = (x + y \<tycolon> N)" using plus_typing_def by auto
instance by standard
end *)

theorem add_nat_\<nu>app[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x + y < 2^LENGTH('b::len) \<longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add TYPE('b) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['b] \<heavy_comma> y \<tycolon> \<nat>['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> x + y \<tycolon> \<nat>['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: of_nat_inverse nu_exps)

theorem add_nat_round[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add TYPE('b) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>\<^sup>r['b::len]\<heavy_comma> y \<tycolon> \<nat>\<^sup>r['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (x + y) \<tycolon> \<nat>\<^sup>r['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: nu_exps)

(* theorem add_nat_mod[\<nu>overload round_add]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_add (LENGTH('b)) \<blangle>\<^bold>E\<^bold>N\<^bold>D \<RR> \<heavy_comma> y \<tycolon> \<nat>['b::len] \<heavy_comma> x \<tycolon> \<nat>['b] \<longmapsto> \<^bold>E\<^bold>N\<^bold>D \<RR> \<heavy_comma> ((x + y) mod 2^(LENGTH('b))) \<tycolon> \<nat>['b]  \<brangle>"
  unfolding op_add_def Procedure_def by (auto simp add: unat_word_ariths)
*)

theorem sub_nat_\<nu>app[\<nu>overload -]:
    "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e y \<le> x \<longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_sub TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> x - y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_sub_def by (auto simp add: nu_exps) (meson unat_sub_if_size)

theorem udiv_nat_\<nu>app[\<nu>overload /]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_udiv TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w] \<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> x div y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_udiv_def by (auto simp add: nu_exps) (meson unat_div)

theorem op_lt_\<nu>app[\<nu>overload <]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_lt TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (x < y) \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_lt_def by (auto simp add: word_less_nat_alt nu_exps)

theorem op_le_\<nu>app[\<nu>overload \<le>]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_le TYPE('w::len) \<blangle> R\<heavy_comma> x \<tycolon> \<nat>['w]\<heavy_comma> y \<tycolon> \<nat>['w]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> (x \<le> y) \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_le_def by (auto simp add: word_le_nat_alt nu_exps)

lemma boolean_not_\<nu>app[\<nu>overload not]:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_not TYPE(1) \<blangle> R\<heavy_comma> x \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> \<not> x \<tycolon> \<bool>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding Procedure_def op_not_def apply (auto simp add: lrep_exps nu_exps)
  by (metis even_take_bit_eq even_zero iszero_def odd_numeral one_neq_zero)

subsection \<open>Field Index\<close>

lemma [\<nu>intro]:
  "\<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ \<lbrace> A \<rbrace> \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<nu>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e Suc i \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ \<lbrace> A \<rbrace> \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<nu>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B \<brangle> \<Longrightarrow>
   \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<brangle>"
  unfolding \<nu>index_def  MakeTag_def index_tuple_def by (cases idx) (simp add: nu_exps tuple_forall)
lemma [\<nu>intro]:
  "\<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m
    \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>k\<^bold>e i#l \<^bold>b\<^bold>y \<^bold>f\<^bold>i\<^bold>e\<^bold>l\<^bold>d \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ \<lbrace> A \<rbrace> \<brangle> \<^bold>g\<^bold>e\<^bold>t g \<^bold>m\<^bold>a\<^bold>p m"
  unfolding FieldIndex_def \<nu>index_def index_tuple_def
  by (cases idx) (simp add: tuple_forall nu_exps)

subsubsection \<open>Abstraction\<close>


\<nu>processor field_index 110 \<open>\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x adr \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn sequent =>
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

\<nu>processor field_index_getter 110 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn major => Parse.nat >> (fn i => fn _ =>
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


subsection \<open>Tuple Operations\<close>

subsubsection \<open>Construction & Destruction\<close>

theorem tup_\<nu>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup TYPE('a::field_list) \<blangle> R \<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R \<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace> \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding cons_tup_def Procedure_def by (simp add: pair_forall nu_exps)

theorem det_\<nu>app:
    "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup \<blangle> R\<heavy_comma> x \<tycolon> \<lbrace> X \<rbrace>\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> x \<tycolon> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding Procedure_def op_dest_tup_def by (simp add: tuple_forall pair_forall nu_exps)

subsubsection \<open>Field Accessing\<close>

lemma
  "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_tuple idx TYPE('a::field_list) \<blangle> R\<heavy_comma> A\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle> "
  unfolding \<nu>index_def \<nu>def pair_forall op_get_tuple_def tuple_forall by simp

lemma "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle> \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_tuple idx TYPE('a::field_list) TYPE('y::lrep) \<blangle> R\<heavy_comma> A\<heavy_comma> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto> R\<heavy_comma> B\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle> "
  unfolding \<nu>index_def \<nu>def pair_forall op_set_tuple_def by simp


subsection \<open>Memory & Pointer Operations\<close>

subsubsection \<open>Pointer Arithmetic\<close>

(* theorem op_shift_pointer_raw[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer ty \<blangle> R\<heavy_comma> addr \<tycolon> RawPointer\<heavy_comma> delta \<tycolon> Identity\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<longmapsto>
      R\<heavy_comma> shift_addr addr (delta * of_nat (size_of ty)) \<tycolon> RawPointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<brangle>"
  unfolding \<nu>def op_shift_pointer_def by (cases addr) (simp add: lrep_exps) *)
  
theorem op_shift_pointer[\<nu>overload +]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e address_llty addr = LLTY('a::lrep) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e offset_of addr + delta \<le> address_len addr \<Longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer TYPE('a::lrep) \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> delta \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<longmapsto>
      R\<heavy_comma> addr ||+ delta \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing \<brangle>"
  unfolding \<nu>def op_shift_pointer_def by (cases addr) (auto simp add: lrep_exps same_addr_offset_def nu_exps)


theorem op_shift_pointer_slice[ unfolded Separation_assoc, \<nu>overload split ]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e n < length xs \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_shift_pointer TYPE('p) \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p addr \<R_arr_tail> xs \<tycolon> Array T
      \<longmapsto> R\<heavy_comma> addr ||+ n \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (addr \<R_arr_tail> take n xs \<tycolon> Array T \<heavy_asterisk> shift_addr addr n \<R_arr_tail> drop n xs \<tycolon> Array T) \<brangle>"
  for T :: "('p::field, 'x) \<nu>"
  unfolding \<nu>def op_shift_pointer_def Array_def Heap_Divider_def apply (cases addr)
  apply (auto simp add: lrep_exps same_addr_offset_def raw_offset_of_def distrib_right nu_exps
        add.commute add.left_commute intro: heap_split_id)
  subgoal for x1 x2 aa b H h1 h2
    by (rule heap_split_id, simp, rule heap_split_by_addr_set[of _ _ "{(x1 |+ x2 + i) | i. i < n}"]) (auto simp add: nu_exps)
  done

(*
theorem op_slice_merge[\<nu>overload merge]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e shift_addr addr1 (length xs1) = addr2 \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_drop \<blangle> \<^bold>E\<^bold>N\<^bold>D R\<heavy_comma> addr1 \<R_arr_tail> xs1 \<tycolon> Slice T\<heavy_comma> addr2 \<R_arr_tail> xs2 \<tycolon> Slice T
      \<longmapsto> \<^bold>E\<^bold>N\<^bold>D R\<heavy_comma> addr1 \<R_arr_tail> xs1 @ xs2 \<tycolon> Slice T \<brangle>"
  unfolding \<nu>def op_drop_def apply (cases addr1; cases addr2)
  apply (auto 0 0 simp add: lrep_exps nth_append)
  by (metis add.assoc add_diff_inverse_nat diff_add_inverse diff_less_mono not_le
*)


subsubsection \<open>Allocation\<close>

lemma malloc_split: "Heap h \<Longrightarrow> P h (heap_assignN n v (malloc h) Map.empty) \<Longrightarrow>
    \<exists>h1 h2. heap_assignN n v (malloc h) h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  apply (rule exI[of _ h], rule exI[of _ "heap_assignN n v (malloc h) Map.empty"], simp)
  subgoal premises prems
    unfolding heap_assignN_def using prems(1)
    by (simp add: map_add_def fun_eq_iff resource_key_forall disjoint_rewL memaddr_forall dom_def
          malloc option.case_eq_if) done

(* lemma heap_assignN_subset: "Heap h \<Longrightarrow> h \<subseteq>\<^sub>m heap_assignN n v (malloc h) h"
  unfolding heap_assignN_def map_le_def Ball_def by (simp add: malloc2 resource_key_forall memaddr_forall) *)

lemma [intro]: "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" proof -
  have "AvailableSegments h \<subseteq> {seg} \<union> AvailableSegments (heap_assignN n v seg h)"
    unfolding AvailableSegments_def heap_assignN_def by auto 
  then show "Heap h \<Longrightarrow> Heap (heap_assignN n v seg h)" 
    unfolding Heap_def using infinite_super by auto
qed

lemma heap_assignN_eval: "v \<in> T \<Longrightarrow> i < n \<Longrightarrow> heap_assignN n (Some (deepize v)) seg h \<^bold>a\<^bold>t (seg |+ i) \<^bold>i\<^bold>s T"
  unfolding MemAddrState_def addr_allocated_def heap_assignN_def by auto



      
theorem alloc_array_\<nu>app:
  "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m N \<Longrightarrow> \<nu>Zero N zero \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc TYPE('x)
      \<blangle> R\<heavy_comma> n \<tycolon> \<nat>[size_t] \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing
        \<longmapsto> (\<exists>*seg. (R\<heavy_comma> (seg |+ 0) \<tycolon> Pointer \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (seg |+ 0) \<R_arr_tail> replicate n zero \<tycolon> Array N)) \<brangle>"
  for N :: "('x::{zero,field},'b)\<nu>"
  unfolding \<nu>def op_alloc_def Array_def Heap_Divider_def
  apply (auto simp add: lrep_exps list_all2_conv_all_nth Let_def same_addr_offset_def nu_exps)
  apply (rule malloc_split, simp add: heap_assignN_eval)
  apply (auto simp add: heap_assignN_eval nu_exps) done


proc alloc : \<open>R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p Nothing\<close> \<longmapsto> \<open>\<exists>*ptr. (R\<heavy_comma> ptr \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> zero \<tycolon> Ref T)\<close>
  requires "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m T" and [\<nu>intro]: "\<nu>Zero T zero"
  have A[simp]: "replicate 1 zero = [zero]" by (simp add: One_nat_def)
  \<bullet>\<open>1 \<tycolon> \<nat>[size_t]\<close> alloc_array T
  finish

subsubsection \<open>Load & Store\<close>

\<nu>overloads \<up> and "\<up>:" and \<Up> and "\<Up>:" and \<down> and "\<down>:" and \<Down> and "\<Down>:"

abbreviation "list_map_at f i l \<equiv> list_update l i (f (l ! i))"

lemma op_load[ \<nu>overload "\<up>:" ]:
  "\<^bold>(\<^bold>( \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x field_index \<blangle> y \<tycolon> Y \<^bold>@ x \<tycolon> X \<brangle> \<^bold>)\<^bold>) \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load TYPE('y::field) TYPE('x) field_index
    \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> addr \<R_arr_tail> x \<tycolon> Ref X \<longmapsto> R\<heavy_comma> y \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> addr \<R_arr_tail> x \<tycolon> Ref X\<brangle> "
  for X :: "('x::field, 'c) \<nu>"
  unfolding op_load_def Procedure_def \<nu>index_def Heap_Divider_def Protector_def
  by (cases field_index, cases addr)  (auto simp add: lrep_exps MemAddrState_def nu_exps split: option.split iff: addr_allocated_def)

lemmas [ \<nu>overload "\<up>" ] = op_load[THEN mp, OF Protector_I, OF index_here_getter, simplified]

proc i_load_n[\<nu>overload "\<up>:"]:
  \<open>a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs \<tycolon> Array X\<close> \<longmapsto> \<open>gt (xs ! i) \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H \<heavy_asterisk> a \<R_arr_tail> xs \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<nu>"
  premises "i < length xs"
  requires idx: "FieldIndex field_index Y X gt mp"
  obtain a' j where a: "a = (a' |+ j)" by (cases a)
  \<bullet> unfold a + \<up>: idx fold a
  finish

lemmas [ \<nu>overload "\<up>" ] = i_load_n_\<nu>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]

lemma op_store[ \<nu>overload "\<down>:" ]:
  "FieldIndex field_index Y X gt mp \<longrightarrow>
  \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store TYPE('y::field) TYPE('x) field_index
    \<blangle> R\<heavy_comma> addr \<tycolon> Pointer\<heavy_comma> y \<tycolon> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p addr \<R_arr_tail> x \<tycolon> Ref X \<longmapsto> R \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p addr \<R_arr_tail> mp (\<lambda>_. y) x \<tycolon> Ref X\<brangle> "
  for X :: "('x::field, 'c) \<nu>"
  unfolding op_store_def Procedure_def FieldIndex_def \<nu>index_def Heap_Divider_def Stack_Delimiter_def
  apply (cases field_index, cases addr)
  apply (auto simp add: lrep_exps Let_def nu_exps split: option.split iff: addr_allocated_def)
  subgoal premises prems for x1 x2 x1a x2a aa ofs b x2b H h1 h2 proof -
    have t1: "\<And>v. (h1 ++ h2)(MemAddress (x1a |+ x2a) \<mapsto> v) = h1 ++ (h2(MemAddress (x1a |+ x2a) \<mapsto> v))"
      using prems disjoint_rewR by simp
    have t2: "\<And>v.  dom (h2(MemAddress (x1a |+ x2a) \<mapsto> v)) = dom h2"
      using prems by auto
    show ?thesis apply (unfold t1, rule heap_split_id, unfold t2, simp add: prems)
      using prems by (auto simp add: nu_exps MemAddrState_def)
  qed done

lemmas [ \<nu>overload "\<down>" ] = op_store[THEN mp, OF FieldIndex_here, simplified]

proc i_store_n[\<nu>overload "\<down>:"]:
  \<open>R\<heavy_comma> a \<tycolon> Pointer\<heavy_comma> i \<tycolon> \<nat>[size_t]\<heavy_comma> y \<tycolon> Y \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p a \<R_arr_tail> xs \<tycolon> Array X\<close> \<longmapsto> \<open>R\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p a \<R_arr_tail> xs[i := mp (\<lambda>_. y) (xs ! i)] \<tycolon> Array X\<close>
  for Y :: "('y::field, 'd) \<nu>"
  premises "i < length xs"
  requires idx: "FieldIndex field_index Y X gt mp"
  obtain a' j where a: "a = (a' |+ j)" by (cases a) 
  \<bullet> unfold a \<rightarrow> y + y \<down>: idx fold a
  finish

lemmas [ \<nu>overload "\<down>" ] = i_store_n_\<nu>app[THEN mp, THEN mp, OF _ FieldIndex_here, unfolded atomize_imp, simplified]


section \<open>Misc\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp] split_paired_All[simp]

bundle xx = Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp] split_paired_All[simp]

proc times: \<open>R'\<heavy_comma> n \<tycolon> \<nat>['b::len]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H'\<close> \<longmapsto> \<open>\<exists>*x. (R x\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x) \<and>\<^sup>s P x n\<close>
  requires [unfolded Variant_Cast_def, simp]: "Variant_Cast vars R' H' R H"
  requires \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P\<close>
  premises \<open>P vars 0\<close>
  requires Body: \<open>\<forall>x i. \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < n \<longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P x i \<longrightarrow>
      \<^bold>p\<^bold>r\<^bold>o\<^bold>c body \<blangle> R x\<heavy_comma> i \<tycolon> \<nat>['b]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x \<longmapsto> \<exists>*x'. ((R x'\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H x') \<and>\<^sup>s P x' (Suc i))\<brangle>\<close>
  \<bullet> \<rightarrow> n \<open>0 \<tycolon> \<nat>['b]\<close>
  \<bullet> while var vars i stack \<open>R vars\<close>, i heap \<open>H vars\<close> always \<open>i \<le> n \<and> P vars i\<close>
  \<bullet> \<medium_left_bracket> dup n < \<medium_right_bracket> \<medium_left_bracket> -- i Body i 1 + cast ie \<open>Suc i\<close> \<medium_right_bracket> drop
  finish

ML_file \<open>codegen/codegen.ML\<close>
ML_file \<open>codegen/NuSys.ML\<close>
ML_file \<open>codegen/NuPrime.ML\<close>
ML_file \<open>codegen/NuLLReps.ML\<close>
ML_file \<open>codegen/misc.ML\<close>
ML_file \<open>codegen/Instructions.ML\<close>


proc split_array[\<nu>overload split]: \<open>ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> l \<tycolon> Array T\<close>
  \<longmapsto> \<open>ptr ||+ n \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> take n l \<tycolon> Array T \<heavy_asterisk> (ptr ||+ n) \<R_arr_tail> drop n l \<tycolon> Array T\<close>
  premises [useful]: "n \<le> length l"
  \<bullet> + split_cast n
  finish

proc pop_array[\<nu>overload pop]: \<open>ptr \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> l \<tycolon> Array T\<close>
  \<longmapsto> \<open>ptr ||+ 1 \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (ptr ||+ 1) \<R_arr_tail> tl l \<tycolon> Array T \<heavy_asterisk> ptr \<R_arr_tail> hd l \<tycolon> Ref T \<close>
  premises A: "l \<noteq> []"
  have [useful]: "1 \<le> length l" by (meson Premise_def length_0_conv less_one not_le A)
  \<bullet> \<open>1 \<tycolon> \<nat>[size_t]\<close> + pop_cast
  finish

\<nu>export_llvm \<open>/tmp/xx.ll\<close>

end