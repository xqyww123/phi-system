theory PhiSem_Mem_C_Base
  imports PhiSem_Aggregate_Base
begin

section \<open>Semantics\<close>

debt_axiomatization
        MemObj_Size :: \<open>TY \<Rightarrow> nat\<close>
    and idx_step_offset :: \<open>TY \<Rightarrow> nat \<Rightarrow> nat\<close>
  where memobj_size_step : \<open>valid_idx_step T i \<Longrightarrow> MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
    and idx_step_offset_size:
          \<open>valid_idx_step T i
                \<Longrightarrow> idx_step_offset T i + MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
    and idx_step_offset_disj:
          \<open>valid_idx_step T i \<Longrightarrow> valid_idx_step T j \<Longrightarrow>
                idx_step_offset T i \<le> idx_step_offset T j \<Longrightarrow>
                idx_step_offset T j < idx_step_offset T i + MemObj_Size (idx_step_type i T) \<Longrightarrow>
                i = j\<close>

primrec index_offset :: \<open>TY \<Rightarrow> nat list \<Rightarrow> nat\<close>
  where \<open>index_offset T [] = 0\<close>
      | \<open>index_offset T (i#idx) = idx_step_offset T i + index_offset (idx_step_type i T) idx\<close>

lemma index_offset_tail[simp]:
  \<open>index_offset T (idx@[i]) = index_offset T idx + idx_step_offset (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma fold_tail:
  \<open>fold f (l @ [x]) = f x o fold f l\<close>
  by (induct l; simp)

lemma index_offset_upper_bound:
  \<open>valid_index T (base@idx) \<Longrightarrow>
   index_offset T (base@idx) + MemObj_Size (index_type (base@idx) T) \<le> index_offset T base + MemObj_Size (index_type base T)\<close>
  apply (induct idx arbitrary: base rule: rev_induct;
         simp del: append_assoc add: append_assoc[symmetric] fold_tail)
  using idx_step_offset_size by fastforce

lemmas index_offset_upper_bound_0 = index_offset_upper_bound[where base = "[]", simplified]

lemma index_offset_bound:
  \<open>valid_index T (base@idx) \<Longrightarrow>
  index_offset T base \<le> index_offset T (base@idx) \<and> index_offset T (base@idx) \<le> index_offset T base + MemObj_Size (index_type base T)\<close>
  apply (induct idx arbitrary: base rule: rev_induct;
         simp del: append_assoc add: append_assoc[symmetric] fold_tail)
  using idx_step_offset_size index_offset_upper_bound by fastforce

lemma index_offset_bound_strict:
  \<open>valid_index T (base@idx) \<Longrightarrow> 0 < MemObj_Size (index_type (base@idx) T) \<Longrightarrow>
  index_offset T base \<le> index_offset T (base@idx) \<and> index_offset T (base@idx) < index_offset T base + MemObj_Size (index_type base T)\<close>
  apply (induct idx arbitrary: base rule: rev_induct;
         simp del: append_assoc add: append_assoc[symmetric] fold_tail)
  using idx_step_offset_size index_offset_upper_bound by fastforce


section \<open>Fiction\<close>

debt_axiomatization Mapof_Val :: \<open>VAL \<Rightarrow> nat list \<rightharpoonup> VAL\<close>
  where Mapof_Val_inj: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> Mapof_Val Va = Mapof_Val Vb \<Longrightarrow> Va = Vb\<close>
  and   Mapof_Val_same_dom: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> dom (Mapof_Val Va) = dom (Mapof_Val Vb)\<close>
  and   Mapof_not_1[simp]: \<open>Mapof_Val V \<noteq> 1\<close>
  and   Mapof_Val_pull_step: \<open>valid_idx_step T i \<Longrightarrow> V \<in> Well_Type T
                          \<Longrightarrow> pull_map [i] (Mapof_Val V) = Mapof_Val (idx_step_value i V)\<close>
  and   Mapof_Val_mod_step: \<open>valid_idx_step T i \<Longrightarrow> v \<in> Well_Type T
                         \<Longrightarrow> Mapof_Val (idx_step_mod_value i f v) = Mapof_Val v ++ push_map [i] (Mapof_Val (f (idx_step_value i v)))\<close>

lemma Mapof_Val_pull:
  \<open>valid_index T idx \<Longrightarrow> V \<in> Well_Type T \<Longrightarrow> pull_map idx (Mapof_Val V) = Mapof_Val (index_value idx V)\<close>
  apply (induct idx arbitrary: V T; simp)
  using Mapof_Val_pull_step
  by (metis idx_step_value_welltyp pull_map_cons)

lemma total_Mapof_disjoint:
   \<open>g ## (push_map idx (to_share \<circ> h))
\<Longrightarrow> to_share \<circ> f = g * (push_map idx (to_share \<circ> h))
\<Longrightarrow> dom g \<inter> dom (push_map idx (to_share \<circ> h)) = {}\<close>
  using to_share_total_disjoint push_map_to_share by metis

lemma map_add_subsumed_dom:
  \<open>dom f \<subseteq> dom g \<Longrightarrow> f ++ g = g\<close>
  unfolding map_add_def dom_def subset_eq fun_eq_iff apply simp
  by (metis option.case_eq_if option.collapse option.simps(3))

lemma Mapof_Val_mod:
  \<open> valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> u \<in> Well_Type (index_type idx T)
\<Longrightarrow> Mapof_Val (index_mod_value idx (\<lambda>_. u) v) = Mapof_Val v ++ push_map idx (Mapof_Val u)\<close>
  apply (induct idx arbitrary: u v T; simp)
  using Mapof_Val_same_dom map_add_subsumed_dom apply (metis order_refl)
  by clarify (simp add: idx_step_value_welltyp Mapof_Val_mod_step  push_map_distrib_map_add
                        Mapof_Val_pull_step[symmetric] push_pull_map map_add_subsumed2
                        push_map_push_map)

lemma Mapof_Val_modify_fiction:
   \<open>valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> u \<in> Well_Type (index_type idx T)
\<Longrightarrow> u'\<in> Well_Type (index_type idx T)
\<Longrightarrow> g ## (push_map idx (to_share \<circ> Mapof_Val u))
\<Longrightarrow> to_share \<circ> (Mapof_Val v) = g * (push_map idx (to_share \<circ> Mapof_Val u))
\<Longrightarrow> to_share \<circ> (Mapof_Val (index_mod_value idx (\<lambda>_. u') v)) = g * (push_map idx (to_share \<circ> Mapof_Val u'))\<close>
  apply (simp add: Mapof_Val_mod to_share_funcomp_map_add push_map_to_share
      times_fun_map_add_right total_Mapof_disjoint[simplified push_map_to_share]
      Mapof_Val_same_dom push_map_dom_eq)
  subgoal premises prems proof -
    have \<open>dom g \<inter> dom (to_share \<circ> push_map idx (Mapof_Val u)) = {}\<close>
      using prems to_share_total_disjoint by blast
    moreover have t1:
      \<open>dom (to_share \<circ> push_map idx (Mapof_Val u)) = dom (to_share \<circ> push_map idx (Mapof_Val u'))\<close>
      using prems by (metis Mapof_Val_same_dom dom_map_option_comp push_map_dom_eq)
    ultimately have \<open>dom g \<inter> dom (to_share \<circ> push_map idx (Mapof_Val u')) = {}\<close> by metis
    note [simp] = times_fun_map_add_right[OF this]
    show ?thesis by simp (metis t1 map_add_subsumed_dom order_eq_refl)
  qed
  done
(* lemma pull_map_share_Mapof_not_eq_1[simp]:
  \<open>valid_index (Typeof v) idx \<Longrightarrow> pull_map idx (share n (to_share \<circ> Mapof_Val v)) = 1 \<longleftrightarrow> n = 0\<close>
  by (cases \<open>n = 0\<close>; simp add: pull_map_share pull_map_to_share Mapof_Val_pull)
*)


lemma map_add_restrict_itself [simp]: \<open>(f ++ g) |` dom g = g\<close>
  unfolding fun_eq_iff restrict_map_def map_add_def
  by (simp add: domIff option.case_eq_if)

lemma Mapof_Val_inj_plus:
  \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> f ++ Mapof_Val Va = f ++ Mapof_Val Vb \<Longrightarrow> Va = Vb\<close>
proof (rule Mapof_Val_inj, assumption)
  assume tyA: \<open>Va \<in> Well_Type T\<close>
     and tyB: \<open>Vb \<in> Well_Type T\<close>
     and feq: \<open>f ++ Mapof_Val Va = f ++ Mapof_Val Vb\<close>
  then have \<open>(f ++ Mapof_Val Va) |` dom (Mapof_Val Va) = (f ++ Mapof_Val Vb) |` dom (Mapof_Val Vb)\<close>
    using Mapof_Val_same_dom by metis 
  note this [simplified]
  then show \<open>Mapof_Val Va = Mapof_Val Vb\<close> .
qed

definition \<open>Valof_Map TY M = (@V. (\<exists>f. f ++ Mapof_Val V = M) \<and> V \<in> Well_Type TY)\<close>

lemma Valof_Map_append[simp]:
  \<open>v \<in> Well_Type T \<Longrightarrow> Valof_Map T (f ++ Mapof_Val v) = v\<close>
  unfolding Valof_Map_def
  using someI[where P=\<open>\<lambda>V. (\<exists>fa. fa ++ Mapof_Val V = f ++ Mapof_Val v) \<and> V \<in> Well_Type T\<close> and x=v, simplified]
        Mapof_Val_inj_plus
  by (metis (no_types, lifting) Mapof_Val_same_dom map_add_restrict_itself) 

lemmas Valof_Map[simp] = Valof_Map_append[where f = \<open>Map.empty\<close>, simplified]


lemma
  \<open> perm_ins_homo' f
\<Longrightarrow> perm_ins_homo' (\<lambda>v. f o Mapof_Val v)\<close>

  term \<open>(\<lambda>v. f o Mapof_Val v)\<close>
  term Mapof_Val
  term \<open>((o) to_share) o Mapof_Val\<close>





definition \<open>fic_val_to_share_map TY =
      Interp (\<lambda>m. if m = 1 then {None} else {Some v |v. v \<in> Well_Type TY \<and> to_share o Mapof_Val v = m})\<close>

lemma fic_val_to_share_map[simp]:
  \<open>\<I> (fic_val_to_share_map TY) = (\<lambda>m. if m = 1 then {None} else {Some v |v. v \<in> Well_Type TY \<and> to_share o Mapof_Val v = m})\<close>
  unfolding fic_val_to_share_map_def by (rule Interp_inverse) (simp add: Interpretation_def one_set_def)


paragraph \<open>Basic fictions for resource elements\<close>



definition "share_mem' = 
              fiction.pointwise' (\<lambda>seg.  (share_val_fiction (segidx.layout seg)))"

definition "share_mem = fiction_mem (fiction.defined (
              fiction.pointwise' (\<lambda>seg. fiction.fine (share_val_fiction (segidx.layout seg)))))"

lemma share_mem_def':
  \<open>share_mem = fiction_mem (fiction.defined share_mem')\<close>
  unfolding share_mem_def share_mem'_def ..



end