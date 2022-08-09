theory NuInstructions
  imports NuPrime NuLLReps
begin

section \<open>A Set of Predefined Minimal Instructions\<close>

context \<phi>empty_sem begin

subsection \<open>Throw Exception\<close>

text \<open>The opcode for throwing an exception is directly \<^term>\<open>Exception\<close>\<close>

lemma (in \<phi>empty) throw_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c Exception \<lbrace> X \<longmapsto> (\<lambda>_::unreachable sem_value. 0) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s X \<rbrace>\<close>
  unfolding \<phi>Procedure_def by blast

subsection \<open>Try-Catch\<close>

definition op_try :: "('ret,'RES_N,'RES) proc \<Rightarrow> ('ret,'RES_N,'RES) proc \<Rightarrow> ('ret,'RES_N,'RES) proc"
  where \<open>op_try f g s = (case f s of Success x s' \<Rightarrow> Success x s' | Exception s' \<Rightarrow> g s'
                                   | PartialCorrect \<Rightarrow> PartialCorrect | Fail \<Rightarrow> Fail)\<close>

lemma (in \<phi>empty) "__op_try__":
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> E \<longmapsto> Y2 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_try f g \<lbrace> X \<longmapsto> \<lambda>v. Y1 v + Y2 v \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace> \<close>
  unfolding op_try_def \<phi>Procedure_def 
  by (auto 2 5 simp add: ring_distribs)

definition "Union_the_Same_Or_Arbitrary_when_Var Z X Y \<longleftrightarrow> (\<forall>v. (Z::'v \<Rightarrow> 'a set) v = X v + Y v)"

lemma Union_the_Same_Or_Arbitrary_when_Var__the_Same:
  \<open>Union_the_Same_Or_Arbitrary_when_Var Z Z Z\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by simp

lemma Union_the_Same_Or_Arbitrary_when_Var__Arbitrary:
  \<open>Union_the_Same_Or_Arbitrary_when_Var (\<lambda>v. X v + Y v) X Y\<close>
  unfolding Union_the_Same_Or_Arbitrary_when_Var_def by blast

\<phi>reasoner_ML Union_the_Same_Or_Arbitrary_when_Var 1200
  (conclusion \<open>Union_the_Same_Or_Arbitrary_when_Var ?Z ?X ?Y\<close>) = \<open>
fn (ctxt,sequent) =>
  let
    val \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Union_the_Same_Or_Arbitrary_when_Var\<close>, _)
          $ Z $ _ $ _) = Thm.major_prem_of sequent
  in (ctxt,
        (if is_Var (Envir.beta_eta_contract Z)
         then @{thm Union_the_Same_Or_Arbitrary_when_Var__Arbitrary}
         else @{thm Union_the_Same_Or_Arbitrary_when_Var__the_Same})
        RS sequent) |> Seq.single
  end
\<close>

declare [ [\<phi>not_define_new_const] ]

proc (in \<phi>empty) try'':
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> YY \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> E \<longmapsto> YY \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s EE2 \<rbrace>\<close>
  argument X
  return YY
  throws EE2
  \<medium_left_bracket> ;; "__op_try__"  ;; F G \<medium_right_bracket>. .

proc (in \<phi>empty) try':
  assumes A: \<open>Union_the_Same_Or_Arbitrary_when_Var Z Y1 Y2\<close>
  assumes F: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> X \<longmapsto> Y1 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  assumes G: \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> E \<longmapsto> Y2 \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E2 \<rbrace>\<close>
  argument X
  return Z
  throws E2
  \<medium_left_bracket> "__op_try__" F G 
    unfold A[unfolded Union_the_Same_Or_Arbitrary_when_Var_def, THEN spec, symmetric]
  \<medium_right_bracket>. .

declare [ [\<phi>not_define_new_const = false] ]


subsection \<open>Access the Resource\<close>

paragraph \<open>Legacy\<close>

definition (in \<phi>resource_sem)
    \<phi>M_get_res :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'a ?) \<Rightarrow> ('a \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res R F = (\<lambda>res. F (the_fine (R res)) res)\<close>

definition (in \<phi>resource_sem)
    \<phi>M_get_res_entry :: \<open>(('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('k \<rightharpoonup> 'a) ?) \<Rightarrow> 'k \<Rightarrow> ('a \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_res_entry R k F = \<phi>M_get_res R (\<lambda>res.
    case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. Fail))\<close>

definition (in \<phi>resource_sem) \<phi>M_set_res :: \<open>
    (('x ? \<Rightarrow> 'x ?) \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'RES_N \<Rightarrow> 'RES)
      \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> (unit,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_set_res Updt F = (\<lambda>res.
    Success (sem_value ()) (Updt (map_fine F) res))\<close>

paragraph \<open>Getters\<close>

definition (in fine_resource)
    \<phi>R_get_res :: \<open>('T \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_get_res F = (\<lambda>res. F (the_fine (get res)) res)\<close>

definition (in partial_map_resource)
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> ('val \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_get_res_entry k F = \<phi>R_get_res (\<lambda>res.
    case res k of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. Fail))\<close>

definition (in partial_map_resource2)
    \<phi>R_get_res_entry :: \<open>'key \<Rightarrow> 'key2 \<Rightarrow> ('val \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_get_res_entry k k2 F = \<phi>R_get_res (\<lambda>res.
    case res k k2 of Some v \<Rightarrow> F v | _ \<Rightarrow> (\<lambda>_. Fail))\<close>

lemma (in fine_resource) \<phi>R_get_res[\<phi>reason!]:
  \<open> !!(get res) = v
\<Longrightarrow> F v res \<in> \<S> Y E
\<Longrightarrow> \<phi>R_get_res F res \<in> \<S> Y E\<close>
  unfolding \<phi>R_get_res_def by simp

lemma (in partial_map_resource) \<phi>R_get_res_entry[\<phi>reason!]:
  \<open> !!(get res) k = Some v
\<Longrightarrow> F v res \<in> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry k F res \<in> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp

lemma (in partial_map_resource2) \<phi>R_get_res_entry[\<phi>reason!]:
  \<open> !!(get res) k k2 = Some v
\<Longrightarrow> F v res \<in> \<S> Y E
\<Longrightarrow> \<phi>R_get_res_entry k k2 F res \<in> \<S> Y E\<close>
  unfolding \<phi>R_get_res_entry_def \<phi>R_get_res_def by simp


paragraph \<open>Setters\<close>

definition (in fine_resource) \<phi>R_set_res :: \<open>('T \<Rightarrow> 'T) \<Rightarrow> (unit,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_set_res F = (\<lambda>res. Success (sem_value ()) (updt (map_fine F) res))\<close>

lemma (in partial_map_resource) \<phi>R_set_res:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> P (!!(get res))
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k \<mapsto> any)))})
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res
      \<in> \<S> (\<lambda>_. \<phi>Res_Spec (R * {mk (Fine (1(k := u)))})) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__")

lemma (in partial_map_resource2) \<phi>R_set_res[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> map_fun_at (map_fun_at (\<lambda>_. u) k2) k m \<in> Valid)
\<Longrightarrow> P (!!(get res))
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := 1(k2 \<mapsto> any))))})
\<Longrightarrow> \<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. u) k2) k) res
      \<in> \<S> (\<lambda>_. \<phi>Res_Spec (R * {mk (Fine (1(k := 1(k2 := u))))})) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__updt_rule__")


paragraph \<open>Dispose\<close>

lemma (in partial_map_resource) \<phi>R_dispose_res[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> m(k := None) \<in> Valid)
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k \<mapsto> any)))})
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := None)) res
      \<in> \<S> (\<lambda>_. \<phi>Res_Spec R) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__")

lemma (in partial_map_resource2) \<phi>R_dispose_res[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> P m \<longrightarrow> m(k:=1) \<in> Valid)
\<Longrightarrow> dom (!!(get res) k) = dom any
\<Longrightarrow> P (!!(get res))
\<Longrightarrow> res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := any)))})
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := 1)) res
      \<in> \<S> (\<lambda>_. \<phi>Res_Spec R) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__dispose_rule__")


paragraph \<open>Allocate\<close>

definition (in mapping_resource)
    \<phi>R_allocate_res_entry :: \<open>('key \<Rightarrow> bool)
                           \<Rightarrow> 'val
                           \<Rightarrow> ('key \<Rightarrow> ('ret,'RES_N,'RES) proc)
                           \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>R_allocate_res_entry P init F =
    \<phi>R_get_res (\<lambda>res.
    let k = (@k. res k = 1 \<and> P k)
     in \<phi>R_set_res (\<lambda>f. f(k := init))
        \<ggreater> F k
)\<close>

lemma (in mapping_resource) \<phi>R_set_res_new[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> m(k := u) \<in> Valid)
\<Longrightarrow> k \<notin> dom1 !!(get res)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> \<phi>R_set_res (\<lambda>f. f(k := u)) res
      \<in> \<S> (\<lambda>_. \<phi>Res_Spec (R * {mk (Fine (1(k := u)))})) Any\<close>
  unfolding \<phi>R_set_res_def by (simp add: \<phi>expns "__new_rule__")

lemma (in mapping_resource) \<phi>R_allocate_res_entry[\<phi>reason!]:
  \<open> (\<forall>m. m \<in> Valid \<longrightarrow> (\<exists>k. m k = 1 \<and> P k))
\<Longrightarrow> (\<forall>k m. P k \<longrightarrow> m \<in> Valid \<longrightarrow> m(k := init) \<in> Valid)
\<Longrightarrow> (\<And>k res. res \<in> \<phi>Res_Spec (R * {mk (Fine (1(k := init)))} \<^bold>s\<^bold>u\<^bold>b\<^bold>j P k)
      \<Longrightarrow> F k res \<in> \<S> Y E)
\<Longrightarrow> res \<in> \<phi>Res_Spec R
\<Longrightarrow> \<phi>R_allocate_res_entry P init F res \<in> \<S> Y E\<close>
  unfolding \<phi>R_allocate_res_entry_def \<phi>R_get_res_def
  subgoal premises prems proof -
    let ?m = \<open>!!(get res)\<close>
    define k' where \<open>k' = (SOME k. ?m k = 1 \<and> P k)\<close>
    have \<open>\<exists>k'. ?m k' = 1 \<and> P k'\<close>
      by (metis (mono_tags, opaque_lifting) IntD1 \<phi>resource_sem.\<phi>Res_Spec_def \<r>_valid_split fine.sel image_iff prems(1) prems(4) proj_inj)
    note this[THEN someI_ex]
    then have t1[simp]: \<open>?m k' = 1 \<and> P k'\<close> unfolding k'_def by blast
    show ?thesis
      unfolding k'_def[symmetric]
      apply (simp, rule \<phi>M_RS_WP_SEQ, rule \<phi>R_set_res_new)
      using prems(2) t1 apply blast
      apply (simp add: dom1_def)
      using \<open>res \<in> \<phi>Res_Spec _\<close> apply this
      by (simp add: prems(3))
  qed .



(*


(*
subsection \<open>Tuple Operations\<close>



subsubsection \<open>Construct Tuple\<close>

definition cons_tup :: "'TY list \<Rightarrow> 'VAL list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "cons_tup tys vs = (
    let N = length tys in
    \<phi>M_assert (N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (rev (take N vs)) tys)
    \<ggreater> Success (V_tup.mk (rev (take N vs))))"

lemma cons_tup_nil:
  \<open>cons_tup [] = \<phi>M_put_Val (V_tup.mk [])\<close>
  unfolding cons_tup_def \<phi>M_put_Val_def
  by simp

lemma cons_tup_cons:
  \<open>cons_tup (TY#TYs) =
    cons_tup TYs \<ggreater>
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (V_tup.mk [v] * tup)
    ))\<close>
  apply (auto split: list.split
    simp add: cons_tup_def fun_eq_iff pair_forall instr_comp_def bind_def
    \<phi>M_get_Val_def \<phi>M_assert_def \<phi>M_put_Val_def Let_def V_tup_mult)
  apply (metis Suc_le_eq list.sel(1) take_hd_drop)
  apply (metis Cons_nth_drop_Suc Suc_le_eq list.sel(3))
  apply (metis Suc_le_eq drop_all leI list.simps(3))
  apply (metis (no_types, lifting) drop_all leI list.ctr_transfer(1) list.sel(1) list.simps(3) list_all2_Cons2 list_all2_appendI list_all2_rev1 rev.simps(2) take_hd_drop)
  apply (smt (verit, del_insts) Suc_le_eq append1_eq_conv list.sel(1) list_all2_Cons2 rev_eq_Cons_iff take_hd_drop)
  by (simp add: take_Suc_conv_app_nth)

lemma (in \<phi>empty) op_cons_tup_nil:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup [] \<lbrace> Void \<longmapsto> () \<Ztypecolon> EmptyTuple \<rbrace>\<close>
  unfolding cons_tup_nil by \<phi>reason

lemma (in \<phi>empty) op_cons_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup TYs \<lbrace> X \<longmapsto> VAL y \<Ztypecolon> Y \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c cons_tup (TY#TYs) \<lbrace> VAL a \<Ztypecolon> A\<heavy_comma> X \<longmapsto> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> Y) \<rbrace>\<close>
  unfolding cons_tup_cons
  apply \<phi>reason apply (rule \<phi>frame0, assumption)
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  apply \<phi>reason apply (simp add: \<phi>expns) by blast


subsubsection \<open>Destruct Tuple\<close>


definition op_dest_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_dest_tup tys =
    \<phi>M_getV (\<tau>Tuple tys) V_tup.dest (\<lambda>tup.
    \<lambda>(vs, res). Success (rev tup@vs, res))"

lemma op_dest_tup_nil_expn:
  \<open>op_dest_tup [] = \<phi>M_getV (\<tau>Tuple []) V_tup.dest (\<lambda>_. SKIP)\<close>
  by (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)

lemma op_dest_tup_cons_expn:
  \<open>op_dest_tup (TY#TYs) =
    \<phi>M_get_Val (\<lambda>tup.
    \<phi>M_assert (\<exists>h tup'. tup = V_tup.mk (h#tup') \<and> h \<in> Well_Type TY) \<ggreater>
    \<phi>M_put_Val (hd (V_tup.dest tup)) \<ggreater>
    \<phi>M_put_Val (V_tup.mk (tl (V_tup.dest tup))) \<ggreater>
    op_dest_tup TYs)\<close>
  apply (auto split: list.split
    simp add: op_dest_tup_def \<phi>M_get_Val_def \<phi>M_put_Val_def \<phi>M_getV_def Let_def fun_eq_iff \<phi>M_assert_def
      instr_comp_def bind_def)
  by (metis list.discI list.exhaust_sel list.rel_sel list.sel(1))

lemma (in \<phi>empty) op_dest_tup_nil:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup [] \<lbrace> () \<Ztypecolon> EmptyTuple \<longmapsto> Void \<rbrace> \<close>
  unfolding op_dest_tup_nil_expn by \<phi>reason

lemma (in \<phi>empty) op_dest_tup_cons:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup TYs \<lbrace> VAL y \<Ztypecolon> Y \<longmapsto> X \<rbrace>
\<Longrightarrow> \<phi>SemType (a \<Ztypecolon> A) TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_dest_tup (TY#TYs) \<lbrace> VAL (a,y) \<Ztypecolon> (\<clubsuit> A \<^emph> \<phi>Is_Tuple Y) \<longmapsto> VAL a \<Ztypecolon> A\<heavy_comma> X \<rbrace>\<close>
  unfolding op_dest_tup_cons_expn
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  apply \<phi>reason apply (clarsimp simp add: \<phi>SemType_def subset_iff V_tup_mult \<phi>expns, assumption)
  by (rule \<phi>frame0, assumption)



subsubsection \<open>Accessing Elements\<close>


definition op_get_element :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_element idx TY =
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx) \<ggreater>
    \<phi>M_put_Val (index_value idx v))"

definition op_set_element :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_element idx TY =
    \<phi>M_get_Val (\<lambda>u.
    \<phi>M_get_Val (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY \<and> valid_index TY idx \<and> u \<in> Well_Type (index_type idx TY)) \<ggreater>
    \<phi>M_put_Val (index_mod_value idx (\<lambda>_. u) v)
  ))"

lemma (in \<phi>empty) op_get_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_element idx TY \<lbrace> VAL x \<Ztypecolon> X \<longmapsto> VAL f x \<Ztypecolon> Y \<rbrace> \<close>
  unfolding op_get_element_def \<phi>Index_getter_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason

lemma (in \<phi>empty) op_set_element:
  \<open> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>r\<^bold>e\<^bold>m valid_index TY idx
\<Longrightarrow> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> X) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> Y) (index_type idx TY)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_set_element idx TY \<lbrace> VAL x \<Ztypecolon> X\<heavy_comma> VAL y \<Ztypecolon> Y \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> X \<rbrace>\<close>
  unfolding op_set_element_def \<phi>Index_mapper_def Premise_def
  apply \<phi>reason apply (simp add: \<phi>SemType_def subset_iff)
   apply (simp add: \<phi>SemType_def subset_iff)
  by \<phi>reason


*)

*)

end

end
