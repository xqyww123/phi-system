theory PhiSem_Aggregate
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype aggregate_ty = \<phi>empty_ty +
  tup     :: \<open>'self list\<close>
  array   :: \<open>'self \<times> nat\<close>

context aggregate_ty begin

abbreviation \<open>tup \<equiv> tup.mk\<close>
abbreviation \<open>array N T \<equiv> array.mk (T,N)\<close>

definition \<open>length_\<tau>Array T = (@N. \<exists>any. T = array N any)\<close>
abbreviation \<open>is_\<tau>Array T t \<equiv> (\<exists>N. t = array N T)\<close>

lemma length_\<tau>Array[simp]:
  \<open>length_\<tau>Array (array N T) = N\<close>
  unfolding length_\<tau>Array_def
  by blast

end

debt_axiomatization T_tup :: \<open>TY list type_entry\<close>
                and T_array :: \<open>(TY \<times> nat) type_entry\<close>
  where aggregate_ty_ax: \<open>aggregate_ty TY_CONS_OF T_tup T_array\<close>

interpretation aggregate_ty TY_CONS_OF _ _ T_tup T_array
  using aggregate_ty_ax .

hide_fact aggregate_ty_ax


subsubsection \<open>Value\<close>

virtual_datatype aggregate_val = \<phi>empty_val +
  V_tup     :: \<open>'self list\<close>
  V_array   :: \<open>TY \<times> 'self list\<close>

debt_axiomatization V_tup :: \<open>VAL list value_entry\<close>
                and V_array :: \<open>(TY \<times> VAL list) value_entry\<close>
  where aggregate_val_ax: \<open>aggregate_val VAL_CONS_OF V_tup V_array\<close>

interpretation aggregate_val VAL_CONS_OF _ _ V_tup V_array
  using aggregate_val_ax .

hide_fact aggregate_val_ax


subsection \<open>Semantics\<close>

debt_axiomatization
        valid_idx_step :: \<open>TY \<Rightarrow> nat \<Rightarrow> bool\<close>
    and idx_step_type  :: \<open>nat \<Rightarrow> TY \<Rightarrow> TY\<close>
    and idx_step_value :: \<open>nat \<Rightarrow> VAL \<Rightarrow> VAL\<close>
    and idx_step_mod_value :: \<open>nat \<Rightarrow> (VAL \<Rightarrow> VAL) \<Rightarrow> VAL \<Rightarrow> VAL\<close>
    and type_measure :: \<open>TY \<Rightarrow> nat\<close>
  where WT_tup[simp]: \<open>Well_Type (tup ts)  = { V_tup.mk vs       |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
  and   WT_arr[simp]: \<open>Well_Type (array n t) = { V_array.mk (t,vs) |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs \<and> Valid_Type t }\<close>
  and   zero_tup[simp]: \<open>Zero (tup Ts)     = map_option V_tup.mk (those (map Zero Ts))\<close>
  and   zero_arr[simp]: \<open>Zero (array N T)  = map_option (\<lambda>z. V_array.mk (T, replicate N z)) (Zero T)\<close>
  and   V_tup_sep_disj[simp]: \<open>V_tup.mk l1 ## V_tup.mk l2\<close>
  and   V_tup_mult    : \<open>V_tup.mk l1 * V_tup.mk l2 = V_tup.mk (l2 @ l1)\<close>
  and   idx_step_type_measure: \<open>valid_idx_step T i
                            \<Longrightarrow> type_measure (idx_step_type i T) < type_measure T\<close>
  and   idx_step_type_tup  : \<open>i < length tys \<Longrightarrow> idx_step_type i (tup tys) = tys!i \<close>
  and   idx_step_type_arr  : \<open>i \<le> N \<Longrightarrow> idx_step_type i (array N T) = T\<close>
  and   valid_idx_step_tup : \<open>valid_idx_step (tup tys) i \<longleftrightarrow> i < length tys\<close>
  and   valid_idx_step_arr : \<open>valid_idx_step (array N T) i \<longleftrightarrow> i < N\<close>
  and   idx_step_value_welltyp: \<open>valid_idx_step T i
                             \<Longrightarrow> v \<in> Well_Type T
                             \<Longrightarrow> idx_step_value i v \<in> Well_Type (idx_step_type i T)\<close>
  and   idx_step_value_tup : \<open>idx_step_value i (V_tup.mk vs)   = vs!i\<close>
  and   idx_step_value_arr : \<open>idx_step_value i (V_array.mk (T,vs)) = vs!i\<close>
  and   idx_step_mod_value : \<open>valid_idx_step T i
                          \<Longrightarrow> valid_idx_step T j
                          \<Longrightarrow> v \<in> Well_Type T
                          \<Longrightarrow> idx_step_value i (idx_step_mod_value j f v) =
                                (if i = j then f (idx_step_value j v) else idx_step_value i v) \<close>
  and   idx_step_mod_value_welltyp: \<open>valid_idx_step T i
                                 \<Longrightarrow> v \<in> Well_Type T
                                 \<Longrightarrow> f (idx_step_value i v) \<in> Well_Type (idx_step_type i T)
                                 \<Longrightarrow> idx_step_mod_value i f v \<in> Well_Type T\<close>
  and   idx_step_mod_value_tup : \<open>idx_step_mod_value i f (V_tup.mk vs) = V_tup.mk (vs[i := f (vs!i)])\<close>
  and   idx_step_mod_value_arr : \<open>idx_step_mod_value i f (V_array.mk (T,vs)) = V_array.mk (T,vs[i := f (vs!i)])\<close>


lemma V_tup_mult_cons:
  \<open>NO_MATCH vs ([]::VAL list) \<Longrightarrow> V_tup.mk (v#vs) = V_tup.mk vs * V_tup.mk [v]\<close>
  using V_tup_mult by simp

abbreviation \<open>index_value \<equiv> fold idx_step_value\<close>
abbreviation \<open>index_type  \<equiv> fold idx_step_type\<close>
abbreviation \<open>index_mod_value \<equiv> foldr idx_step_mod_value\<close>

primrec valid_index :: \<open>TY \<Rightarrow> nat list \<Rightarrow> bool\<close>
  where \<open>valid_index T [] \<longleftrightarrow> True\<close>
      | \<open>valid_index T (i#idx) \<longleftrightarrow> valid_idx_step T i \<and> valid_index (idx_step_type i T) idx\<close>

lemma valid_index_tail[simp]:
  \<open>valid_index T (idx@[i]) \<longleftrightarrow> valid_index T idx \<and> valid_idx_step (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma index_type_measure:
  \<open>valid_index T idx \<Longrightarrow> idx \<noteq> [] \<Longrightarrow> type_measure (index_type idx T) < type_measure T\<close>
  apply (induct idx arbitrary: T; simp)
  by (metis dual_order.strict_trans fold_simps(1) idx_step_type_measure)

lemma valid_index_cat: \<open>valid_index T (a@b) \<Longrightarrow> valid_index T a \<and> valid_index (index_type a T) b\<close>
  by (induct a arbitrary: T; simp)

lemma valid_index_cons: \<open>valid_index T [i] \<longleftrightarrow> valid_idx_step T i\<close> by simp

lemma index_value_welltyp:
  \<open>valid_index T idx \<Longrightarrow> v \<in> Well_Type T \<Longrightarrow> index_value idx v \<in> Well_Type (index_type idx T)\<close>
  apply (induct idx arbitrary: v T; simp)
  using idx_step_value_welltyp
  by blast

lemma index_mod_value_welltyp:
   \<open>valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> f (index_value idx v) \<in> Well_Type (index_type idx T)
\<Longrightarrow> index_mod_value idx f v \<in> Well_Type T\<close>
  apply (induct idx arbitrary: T v; simp)
  using idx_step_mod_value_welltyp idx_step_value_welltyp by blast



(* TODO: move this

primrec index_offset :: \<open>TY \<Rightarrow> nat list \<Rightarrow> nat\<close>
  where \<open>index_offset T [] = 0\<close>
      | \<open>index_offset T (i#idx) = idx_step_offset T i + index_offset (idx_step_type i T) idx\<close>

lemma index_offset_tail[simp]:
  \<open>index_offset T (idx@[i]) = index_offset T idx + idx_step_offset (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp) *)

lemma index_type_idem:
  \<open>valid_index T idx \<Longrightarrow> index_type idx T = T \<longleftrightarrow> idx = []\<close>
  apply (cases idx; simp; rule)
  using index_type_measure
  by (metis fold_simps(2) list.discI order_less_irrefl valid_index.simps(2))

lemma list_all_replicate:
  \<open>list_all P (replicate n x) \<longleftrightarrow> n = 0 \<or> P x\<close>
  by (induct n; simp; blast)

lemma Valid_Type_\<tau>Array[simp]:
  \<open>Valid_Type (array n T) \<longleftrightarrow> Valid_Type T\<close>
  by (simp add: Inhabited_def;
      meson length_replicate list_all_replicate)

lemma Valid_Type_\<tau>Tuple[simp]:
  \<open>Valid_Type (tup Ts) \<longleftrightarrow> list_all Valid_Type Ts\<close>
  unfolding Inhabited_def
  by (simp; induct Ts; simp add: list_all2_Cons1)


section \<open>\<phi>Type\<close>

subsection \<open>Tuple\<close>

subsubsection \<open>Empty Tuple\<close>

definition EmptyTuple :: \<open>(VAL, unit) \<phi>\<close>
  where \<open>EmptyTuple x = { V_tup.mk [] }\<close>

lemma EmptyTuple_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> EmptyTuple) \<longleftrightarrow> p = V_tup.mk []\<close>
  unfolding EmptyTuple_def \<phi>Type_def by simp

subsubsection \<open>Field\<close>

definition \<phi>Field :: "(VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>" ("\<clubsuit>")
  where "\<phi>Field T x = { V_tup.mk [v] |v. v \<in> T x }"

lemma \<phi>Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Field T) \<longleftrightarrow> (\<exists>v. p = V_tup.mk [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Field_def \<phi>Type_def by simp

lemma \<phi>Field_inhabited[elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> \<clubsuit> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma EmptyTuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> EmptyTuple \<^emph> \<clubsuit> T) = (a \<Ztypecolon> \<clubsuit> T)\<close>
  \<open>((a,()) \<Ztypecolon> \<clubsuit> T \<^emph> EmptyTuple) = (a \<Ztypecolon> \<clubsuit> T)\<close>
  unfolding set_eq_iff
  apply (clarsimp; rule; clarsimp simp add: \<phi>expns V_tup_mult)
  apply (metis V_tup_mult V_tup_sep_disj append_Nil)
  apply (clarsimp; rule; clarsimp simp add: \<phi>expns V_tup_mult)
  by (metis V_tup_mult V_tup_sep_disj append_Cons append_Nil)

lemma \<phi>Field_zero  [\<phi>reason for \<open>\<phi>Zero (tup [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x \<Longrightarrow> \<phi>Zero (tup [ty]) (\<clubsuit> T) x \<close>
  unfolding \<phi>Zero_def by (clarsimp simp add: \<phi>expns)

lemma \<phi>Field_zeros [\<phi>reason for \<open>\<phi>Zero (tup [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x
    \<Longrightarrow> \<phi>Zero (tup tys) Ts xs
    \<Longrightarrow> \<phi>Zero (tup (ty#tys)) (\<clubsuit> T \<^emph> Ts) (x,xs) \<close>
  unfolding \<phi>Zero_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult_cons image_iff)
  using V_tup_sep_disj by blast
  

lemma \<phi>Field_semty[\<phi>reason for \<open>\<phi>SemType (?x \<Ztypecolon> \<clubsuit> ?T) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> T) TY \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<clubsuit> T) (tup [TY])\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp simp add: \<phi>expns)

lemma \<phi>Field_semtsy[\<phi>reason for \<open>\<phi>SemType (?x \<Ztypecolon> \<clubsuit> ?T \<^emph> ?Ts) ?ty\<close>]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (xs \<Ztypecolon> Ts) (tup TYs)
\<Longrightarrow> \<phi>SemType ((x,xs) \<Ztypecolon> (\<clubsuit> T \<^emph> Ts)) (tup (TY#TYs))\<close>
  unfolding \<phi>SemType_def subset_iff
  apply (clarsimp simp add: \<phi>expns)
  by (metis V_tup_mult append.left_neutral append_Cons list.rel_inject(2))

subsubsection \<open>Helpers\<close>

definition \<open>\<phi>Is_Tuple T x = { V_tup.mk vs |vs. V_tup.mk vs \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>Is_Tuple_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Is_Tuple T) \<longleftrightarrow> (\<exists>vs. p = V_tup.mk vs \<and> V_tup.mk vs \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Is_Tuple_def \<phi>Type_def by simp

lemma \<phi>Is_Tuple_\<phi>Is_Tuple[simp]:
  \<open>\<phi>Is_Tuple (\<phi>Is_Tuple T) = \<phi>Is_Tuple T\<close>
  unfolding \<phi>Is_Tuple_def fun_eq_iff set_eq_iff \<phi>Type_def by simp


lemma \<phi>Is_Tuple_\<phi>Is_Tuple_more[simp]:
  \<open>\<phi>Is_Tuple (\<clubsuit> A \<^emph> \<phi>Is_Tuple B) = (\<clubsuit> A \<^emph> \<phi>Is_Tuple B)\<close>
  apply (rule \<phi>Type_eqI)
  apply (clarsimp simp add: \<phi>expns, rule; clarify)
  by (metis V_tup_mult)

lemma \<phi>Is_Tuple_Field[simp]:
  \<open>\<phi>Is_Tuple (\<clubsuit> A) = \<clubsuit> A\<close>
  by (rule \<phi>Type_eqI, clarsimp simp add: \<phi>expns, rule; clarify; blast)

lemma \<phi>Is_Tuple_EmptyTuple[simp]:
  \<open>\<phi>Is_Tuple EmptyTuple = EmptyTuple\<close>
  by (rule \<phi>Type_eqI, clarsimp simp add: \<phi>expns)



subsection \<open>Array\<close>

definition Array :: "nat \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a list) \<phi>"
  where \<open>Array N T = (\<lambda>l. { V_array.mk (TY,vs) |TY vs.
    length l = N \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)) })\<close>

lemma Array_expns[\<phi>expns]:
  \<open>v \<in> (l \<Ztypecolon> Array N T) \<longleftrightarrow>
    (\<exists> TY vs. length l = N \<and> v = V_array.mk (TY,vs) \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l
        \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)))\<close>
  unfolding Array_def \<phi>Type_def by simp blast

lemma Array_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open> Inhabited (l \<Ztypecolon> Array N T)
\<Longrightarrow> (length l = N \<Longrightarrow>(\<And>i. i < length l \<Longrightarrow> Inhabited (l!i \<Ztypecolon> T)) \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns list_all2_conv_all_nth) blast

lemma Array_semty[\<phi>reason for \<open>\<phi>SemType (?x \<Ztypecolon> Array ?N ?T) ?ty\<close>]:
  \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY) \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> Array N T) (array N TY)\<close>
  apply (clarsimp simp add: \<phi>expns list_all_length list_all2_conv_all_nth \<phi>SemType_def subset_iff
          Inhabited_def)
  using Well_Type_unique by blast
  
lemma Array_zero[\<phi>reason for \<open>\<phi>Zero (array ?N ?TY) (Array ?N ?T) ?x\<close>]:
  \<open>\<phi>Zero TY T zero \<Longrightarrow> \<phi>\<phi>SemType T TY \<Longrightarrow> \<phi>Zero (array N TY) (Array N T) (replicate N zero)\<close>
  unfolding \<phi>Zero_def
  by (clarsimp simp add: \<phi>expns list_all2_conv_all_nth Inhabited_def image_iff; blast)


subsection \<open>Index to Fields of Structures\<close>

definition \<phi>Index_getter :: \<open>nat list \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_getter idx T U g \<longleftrightarrow> index_value idx \<in> (g \<Ztypecolon> T \<Rrightarrow> U)\<close>

definition \<phi>Index_mapper :: \<open>nat list \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_mapper idx T U f \<longleftrightarrow> (\<forall>g g'. g \<in> (g' \<Ztypecolon> U \<Rrightarrow> U) \<longrightarrow> index_mod_value idx g \<in> (f g' \<Ztypecolon> T \<Rrightarrow> T))\<close>


lemma idx_step_value_V_tup_suc:
  \<open>idx_step_value (Suc i) (V_tup.mk (va # vs)) = idx_step_value i (V_tup.mk vs)\<close>
  by (simp add: idx_step_value_tup)

lemma idx_step_mod_value_V_tup_suc:
  \<open>idx_step_mod_value (Suc i) g (V_tup.mk (va # vs)) = idx_step_mod_value i g (V_tup.mk vs) * V_tup.mk [va]\<close>
  by (metis NO_MATCH_I V_tup_mult_cons idx_step_mod_value_tup list_update_code(3) nth_Cons_Suc)


lemma \<phi>Index_getter_tup_suc:
  \<open> \<phi>Index_getter (i # idx) X Y f
\<Longrightarrow> \<phi>Index_getter (Suc i # idx) (\<clubsuit> T \<^emph> \<phi>Is_Tuple X) Y (f o snd)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_V_tup_suc)

lemma \<phi>Index_getter_tup_0:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (0 # idx) (\<clubsuit> X) Y f\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma \<phi>Index_getter_tup_0r:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (0 # idx) (\<clubsuit> X \<^emph> \<phi>Is_Tuple R) Y (f o fst)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma \<phi>Index_getter_arr:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < N
\<Longrightarrow> \<phi>Index_getter (i # idx) (Array N X) Y (\<lambda>l. f (l!i))\<close>
  unfolding \<phi>Index_getter_def Premise_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_arr list_all2_conv_all_nth)



lemma \<phi>Index_mapper_tup_suc:
  \<open> \<phi>Index_mapper (i # idx) X Y f
\<Longrightarrow> \<phi>Index_mapper (Suc i # idx) (\<clubsuit> T \<^emph> \<phi>Is_Tuple X) Y (apsnd o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_V_tup_suc)
  by (metis V_tup_sep_disj idx_step_mod_value_tup)


lemma \<phi>Index_mapper_tup_0:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>Index_mapper (0 # idx) (\<clubsuit> X) Y f\<close>
  unfolding \<phi>Index_mapper_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)

lemma \<phi>Index_mapper_tup_0r:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>Index_mapper (0 # idx) (\<clubsuit> X \<^emph> \<phi>Is_Tuple X) Y (apfst o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)
  by (metis Cons_eq_appendI V_tup_mult V_tup_sep_disj append_self_conv2)

lemma \<phi>Index_mapper_arr:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < N
\<Longrightarrow> \<phi>Index_mapper (i # idx) (Array N X) Y (\<lambda>g l. l[i := f g (l!i)])\<close>
  unfolding \<phi>Index_mapper_def Premise_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_arr list_all2_conv_all_nth)
  by (metis nth_list_update)


end