theory NuBasicAbstractors
  imports NuLLReps NuSys
  abbrevs "<some>" = "\<^bold>s\<^bold>o\<^bold>m\<^bold>e"
begin

\<nu>overloads singular and plural
\<nu>overloads split_cast and pop_cast

text \<open>Basic \<nu>-abstractors\<close>

(* text \<open>Examples for automatic property inference\<close>
schematic_goal [simplified]: "\<nu>Share (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<bool>) ?set ?sh" by (rule \<nu>intro)+
(* schematic_goal [simplified]: "\<nu>Share N s f \<Longrightarrow> \<nu>Share (N \<nuFusion> N \<nuFusion> N) ?set ?sh" for N :: "('a::sharable_lrep, 'b) nu"
  including show_more1 by (blast intro: \<nu>intro Premise_I) *)
schematic_goal [simplified]: "\<nu>Equalable (\<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<nat>['a :: len]) ?ceq" by (rule \<nu>intro)+
schematic_goal [simplified]: "\<nu>Disposable ((b,x,y) \<tycolon> \<bool> \<nuFusion> \<nat>['b :: len] \<nuFusion> \<nat>['a :: len])" by (rule \<nu>intro)+
ML_val \<open>
val tm2 = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic @{context})
    "\<nu>Share N s f \<Longrightarrow> \<nu>Share (N \<nuFusion> N \<nuFusion> N) ?set ?sh"
  |> Thm.cterm_of @{context}
val tm = Thm.cprop_of @{thm th1}
val th = Goal.init tm2
val th2 = SOLVED' (Tactical.REPEAT o Tactic.ares_tac @{context} @{thms \<nu>share}) 1 th |> Seq.hd
\<close>
*)
section \<open>Abstractors for specification\<close>


subsection \<open>\<nu>-abstraction : DeepModel\<close>

definition DeepModel :: "('a::lrep, 'b) \<nu> \<Rightarrow> (deep_model, 'b) \<nu>"
  where "DeepModel T x = {p. shallowize p \<nuLinkL> T \<nuLinkR> x}"

lemma [simp]: "deepize p \<nuLinkL> DeepModel T \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> T \<nuLinkR> x" unfolding DeepModel_def Refining_def by simp

subsection \<open>\<nu>-abstraction : Ref\<close>

definition Ref  :: "('a::field, 'b) \<nu> \<Rightarrow> (heap, nat memaddr \<R_arr_tail> 'b) \<nu>"
  where "Ref T xx = {heap. (case xx of addr \<R_arr_tail> x \<Rightarrow> heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T)}"

lemma [simp]: "heap \<nuLinkL> Ref T \<nuLinkR> addr \<R_arr_tail> x \<longleftrightarrow> (heap \<^bold>a\<^bold>t addr \<^bold>i\<^bold>s x \<tycolon> T)"
  by (auto simp add: lrep_exps Ref_def Refining_def)
lemma [elim]: " addr \<R_arr_tail> x \<ratio> Ref T \<Longrightarrow> (x \<ratio> T \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (auto simp add: MemAddrState_def)

subsection \<open>\<nu>-abstraction : Array'\<close>

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

(* lemma Array'_dual_Ref_\<nu>app [\<nu>intro]:
 "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length xs \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e (xs ! i) \<noteq> None \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array' N \<longmapsto> a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> the (xs ! i) \<tycolon> Ref N \<medium_right_bracket>
  \<^bold>d\<^bold>u\<^bold>a\<^bold>l a \<R_arr_tail> xs[i := None] \<tycolon> Array' N \<heavy_asterisk> \<medium_left_bracket> (a ||+ i) \<R_arr_tail> y \<tycolon> Ref N \<medium_right_bracket> \<longmapsto> a \<R_arr_tail> xs[i := Some y] \<tycolon> Array' N"
  unfolding CastDual_def Heap_Cast_Goal_def apply (simp add: Array'_to_Ref_\<nu>app)
  unfolding Cast_def apply (cases a) apply (auto simp add: pred_option_def Ball_def)
  by (metis MemAddrState_add_I1 MemAddrState_add_I2 nth_list_update option.sel)
*)


subsection \<open>\<nu>-abstraction : Array\<close>

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

lemma [\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> a \<R_arr_tail> xs' \<tycolon> Array' N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs' = mapSome xs2 \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> a \<R_arr_tail> xs2 \<tycolon> Array N \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def using Array'_cast_Array[unfolded Cast_def] by blast

lemma [\<nu>intro]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> mapSome xs \<tycolon> Array' N \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow>
   \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> xs \<tycolon> Array N \<longmapsto> T \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def using Array_cast_Array'[unfolded Cast_def] by blast

lemma [\<nu>intro]:
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

(* lemma pop_cast_Array'_\<nu>app[\<nu>overload pop_cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e l \<noteq> [] \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<R_arr_tail> l \<tycolon> Array T \<longmapsto> (a ||+ 1) \<R_arr_tail> tl l \<tycolon> Array T \<heavy_asterisk> a \<R_arr_tail> hd l \<tycolon> Ref T"
  unfolding Premise_def subgoal premises prems
proof -
  have t1: "1 \<le> length l"
    by (metis One_nat_def Suc_leI length_greater_0_conv list.size(3) not_one_le_zero prems)
  have t2: "take 1 l = [hd l]" by (simp add: take_Suc prems)
  have t3: "drop 1 l = tl l" by (simp add: drop_Suc prems) 

  thm split_cast_Array_\<nu>app[of 1 l, unfolded Premise_def ParamTag_def, simplified t1, simplified t2 t3]
  thm One_nat_def Suc_le_eq length_greater_0_conv
*)
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
  unfolding Cast_def Premise_def apply (simp add: lrep_exps nu_exps) using sint_int by auto

(* section \<open>Others\<close>

definition stepin :: "( ('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> ( ('c::lrep) \<times> 'a \<Rightarrow> ('c \<times> 'b) state)"
  where "stepin f x = (case x of (c,a) \<Rightarrow> bind (f a) (\<lambda>y. StatOn (c,y)))"
lemma stepin: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> u \<tycolon> U \<longmapsto> v \<tycolon> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c stepin f \<blangle> (x,u) \<tycolon> (X \<nuFusion> U) \<longmapsto> (x,v) \<tycolon> (X \<nuFusion> V) \<brangle>"
  unfolding stepin_def \<nu>def bind_def by auto

definition stepinR :: "( ('a::lrep) \<times>('z::lrep) \<Rightarrow> ('z1::lrep) state) \<Rightarrow> ((('c::lrep) \<times> 'a) \<times>'z \<Rightarrow> ('c \<times> 'z1) state)"
  where "stepinR f x = (case x of ((c,a),z) \<Rightarrow> bind (f (a,z)) (\<lambda>y. StatOn (c,y)))"
lemma stepinR: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> (a \<tycolon> A)\<heavy_comma>Z \<longmapsto> Z1 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c stepinR f \<blangle> (c,a) \<tycolon> (C \<nuFusion> A)\<heavy_comma>Z \<longmapsto> c \<tycolon> C\<heavy_comma>Z1 \<brangle>"
  unfolding stepinR_def \<nu>def bind_def by (auto 4 3)
definition op_pairring_make :: "( ('z1::lrep) \<Rightarrow> ( ('b::lrep) \<times> ('z2::lrep) ) state) \<Rightarrow> ('a \<times> ('z1::lrep) \<Rightarrow> (( ('a::lrep) \<times> 'b) \<times> 'z2) state)"
  where "op_pairring_make f s = (case s of (a,z1) \<Rightarrow> bind (f z1) (\<lambda>(b,z2). StatOn ((a,b),z2)))"
lemma op_pairring_make: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> Z1 \<longmapsto> b \<tycolon> B\<heavy_comma>Z2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_pairring_make f \<blangle> a \<tycolon> A\<heavy_comma>Z1 \<longmapsto> (a,b) \<tycolon> A \<nuFusion> B\<heavy_comma>Z2 \<brangle>"
  unfolding op_pairring_make_def \<nu>def bind_def by (auto 4 3)

lemma [\<nu>auto_destruct]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> r \<tycolon> R\<heavy_comma>Z \<longmapsto> Z1 \<brangle> \<Longrightarrow>  \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> l \<tycolon> L\<heavy_comma>Z1 \<longmapsto> Z2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (stepinR g \<nuInstrComp> f) \<blangle> (l,r) \<tycolon> (L \<nuFusion> R)\<heavy_comma>Z \<longmapsto> Z2\<brangle>"
  unfolding AutoTag_def by (blast intro: instr_comp stepinR)
lemma [\<nu>auto_construct]:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> EoC Z \<longmapsto> l \<tycolon> L\<heavy_comma>EoC Z1 \<brangle> \<Longrightarrow>  \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle>EoC Z1 \<longmapsto> r \<tycolon> R\<heavy_comma>EoC Z' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> op_pairring_make g) \<blangle>EoC Z \<longmapsto> (l,r) \<tycolon> (L \<nuFusion> R)\<heavy_comma>EoC Z'\<brangle>"
  unfolding AutoTag_def by (blast intro: instr_comp op_pairring_make)

schematic_goal "\<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<blangle> ?x \<tycolon> ((\<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c A \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c B) \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c D) \<nuFusion> \<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c C\<heavy_comma>Z \<longmapsto> (?Z1::(?'a::lrep) set) \<brangle>" by (rule \<nu>auto_destruct)+
thm \<nu>auto_construct

ML \<open>@{term "29::32"}\<close>
lemma [simplified]: "(10::3) = (0::3)"  by auto
  thm term_def *)


end

