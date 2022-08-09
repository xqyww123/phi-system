theory NuStd_Base
  imports NuSys NuInstructions NuLLReps
  keywords
     "\<up>:" "\<Up>:" "\<down>:" "\<Down>:" "always" "--" "\<rightarrow>" "\<lambda>" "\<lambda>'" "$" :: quasi_command
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


(*

subsubsection \<open>recursion\<close>

lemma SemRec_IR: "SemRec F x res y \<Longrightarrow> SemRec (F o F) x res y"
  by (induct rule: SemRec.induct, rule SemRec_I0, simp)

lemma SemRec_deterministic:
  assumes "SemRec c v res s1" and "SemRec c v res s2" shows "s1 = s2"
proof -
  have "SemRec c v res s1 \<Longrightarrow> (\<forall>s2. SemRec c v res s2 \<longrightarrow> s1 = s2)"
    apply (induct rule: SemRec.induct)
     apply clarify
    subgoal for F a b y s2 apply (rotate_tac 1)
      apply (induct rule: SemRec.induct) by auto 
    apply clarify apply (blast intro: SemRec_IR) done
  thus ?thesis using assms by simp
qed

lemma SemRec_deterministic2: "SemRec body v res x \<Longrightarrow> The (SemRec body v res) = x"
  using SemRec_deterministic by blast

term \<phi>SemType

definition \<phi>SemTypes :: \<open>('FIC_N,'FIC) assn \<Rightarrow> 'TY list \<Rightarrow> bool\<close>
  where \<open>\<phi>SemTypes S TYs \<longleftrightarrow> (fst ` S) \<subseteq> Collect (list_all2 (\<lambda>t x. x \<in> Well_Type t) TYs)\<close>

lemma [\<phi>reason 1200 on \<open>\<phi>SemTypes (OBJ ?X) ?TYs\<close>]:
  \<open>\<phi>SemTypes (OBJ X) []\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemTypes R TYs
\<Longrightarrow> \<phi>SemTypes (R\<heavy_comma> OBJ X) TYs\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200 on \<open>\<phi>SemTypes (VAL ?X) ?TYs\<close>]:
  \<open> \<phi>SemType X TY
\<Longrightarrow> \<phi>SemTypes (VAL X) [TY]\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemType X TY
\<Longrightarrow> \<phi>SemTypes R TYs
\<Longrightarrow> \<phi>SemTypes (R\<heavy_comma> VAL X) (TY # TYs)\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. \<phi>SemTypes (S x) TYs)
\<Longrightarrow> \<phi>SemTypes (ExSet S) TYs\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma [\<phi>reason 1200]:
  \<open> \<phi>SemTypes S TYs
\<Longrightarrow> \<phi>SemTypes (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) TYs\<close>
  unfolding \<phi>SemTypes_def subset_iff image_iff Bex_def \<phi>SemType_def
  by (auto simp add: \<phi>expns times_list_def)

lemma "__op_recursion__":
  " (\<And>x. \<phi>SemTypes (X x) TXs)
\<Longrightarrow> (\<And>x. \<phi>SemTypes (Y x) TYs)
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<forall>g x'. (\<forall>x''. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> X x'' \<longmapsto> Y x'' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x'' \<rbrace>) \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F g \<lbrace> X x' \<longmapsto> Y x' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x' \<rbrace>)
\<Longrightarrow> \<forall>x. \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_recursion TXs TYs F \<lbrace> X x \<longmapsto> Y x \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E x \<rbrace>"
  unfolding op_recursion_def \<phi>Procedure_def atomize_all
  apply (auto simp add: SemRec_deterministic2)
  subgoal for x a b xa R
    apply (rotate_tac 3) apply (induct rule:  SemRec.induct) by (auto 0 6) .


rec_proc dec:
  var i
  premises A: \<open>0 \<le> i\<close>
  argument \<open>i \<Ztypecolon> \<nat>[b]\<close>
  return \<open>0 \<Ztypecolon> \<nat>[b]\<close>
  \<medium_left_bracket> \<rightarrow> vi ;;
    if \<open>0 < $vi\<close> \<medium_left_bracket> \<open>$vi - 1\<close> dec \<medium_right_bracket>.
                 \<medium_left_bracket> $vi is 0 \<medium_right_bracket>.
  \<medium_right_bracket>. .



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

\<phi>processor field_index 5000 \<open>FieldIndex f X \<lbrace> A \<rbrace> gt mp \<Longrightarrow> PROP P\<close> \<open>fn ctx => fn major => Parse.nat >> (fn i => fn _ =>
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
*)
end