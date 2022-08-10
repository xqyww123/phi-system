theory Phi_Aggregate
  imports Phi_Min
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype aggregate_ty = \<phi>min_ty +
  T_tup     :: \<open>'self list\<close>
  T_array   :: \<open>'self \<times> nat\<close>

context aggregate_ty begin

abbreviation \<open>\<tau>Tuple \<equiv> T_tup.mk\<close>
abbreviation \<open>\<tau>Array N T \<equiv> T_array.mk (T,N)\<close>

definition \<open>length_\<tau>Array T = (@N. \<exists>any. T = \<tau>Array N any)\<close>
abbreviation \<open>is_\<tau>Array T t \<equiv> (\<exists>N. t = \<tau>Array N T)\<close>

lemma length_\<tau>Array[simp]:
  \<open>length_\<tau>Array (\<tau>Array N T) = N\<close>
  unfolding length_\<tau>Array_def
  by blast

end

subsubsection \<open>Value\<close>

virtual_datatype 'TY aggregate_val :: "nonsepable_semigroup" = 'TY \<phi>min_val +
  V_tup     :: \<open>'self list\<close>
  V_array   :: \<open>'TY \<times> 'self list\<close>


subsection \<open>Semantics\<close>

datatype ('TY,'VAL) \<I>\<D>\<X> = \<I>\<D>\<X>
  (valid_idx_step: \<open>'TY \<Rightarrow> nat \<Rightarrow> bool\<close>)
  (idx_step_type: \<open>nat \<Rightarrow> 'TY \<Rightarrow> 'TY\<close>)
  (idx_step_value: \<open>nat \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>)
  (idx_step_mod_value: \<open>nat \<Rightarrow> ('VAL \<Rightarrow> 'VAL) \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>)
  (idx_step_offset: \<open>'TY \<Rightarrow> nat \<Rightarrow> nat\<close>)
  (type_measure: \<open>'TY \<Rightarrow> nat\<close>)

locale aggregate =
  aggregate_ty where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ aggregate_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ \<phi>min where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::{comm_monoid_mult,no_inverse})
                  \<times> ('FIC_N \<Rightarrow> 'FIC::{comm_monoid_mult,no_inverse}))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N => 'VAL) \<times> ('RES_N => 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>

fixes \<I>\<D>\<X> :: \<open>('TY,'VAL) \<I>\<D>\<X>\<close>

assumes WT_tup[simp]: \<open>Well_Type (\<tau>Tuple ts)  = { V_tup.mk vs       |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
  and   WT_arr[simp]: \<open>Well_Type (\<tau>Array n t) = { V_array.mk (t,vs) |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs }\<close>

assumes zero_tup[simp]: \<open>Zero (T_tup.mk Ts)     = V_tup.mk (map Zero Ts)\<close>
  and   zero_arr[simp]: \<open>Zero (T_array.mk (T,N))= V_array.mk (T, replicate N (Zero T))\<close>


assumes V_tup_mult: \<open>V_tup.mk t1 * V_tup.mk t2 = V_tup.mk (t1 @ t2)\<close>
    and   idx_step_type_measure: \<open>valid_idx_step \<I>\<D>\<X> T i
                              \<Longrightarrow> type_measure \<I>\<D>\<X> (idx_step_type \<I>\<D>\<X> i T) < type_measure \<I>\<D>\<X> T\<close>
    and   idx_step_type_tup  : \<open>i < length tys \<Longrightarrow> idx_step_type \<I>\<D>\<X> i (\<tau>Tuple tys) = tys!i \<close>
    and   idx_step_type_arr  : \<open>i \<le> N \<Longrightarrow> idx_step_type \<I>\<D>\<X> i (\<tau>Array N T) = T\<close>
    and   valid_idx_step_tup : \<open>valid_idx_step \<I>\<D>\<X> (\<tau>Tuple tys) i \<longleftrightarrow> i < length tys\<close>
    and   valid_idx_step_arr : \<open>valid_idx_step \<I>\<D>\<X> (\<tau>Array N T) i \<longleftrightarrow> i < N\<close>
    and   idx_step_value_welltyp: \<open>valid_idx_step \<I>\<D>\<X> T i
                               \<Longrightarrow> v \<in> Well_Type T
                               \<Longrightarrow> idx_step_value \<I>\<D>\<X> i v \<in> Well_Type (idx_step_type \<I>\<D>\<X> i T)\<close>
    and   idx_step_value_tup : \<open>idx_step_value \<I>\<D>\<X> i (V_tup.mk vs)   = vs!i\<close>
    and   idx_step_value_arr : \<open>idx_step_value \<I>\<D>\<X> i (V_array.mk (T,vs)) = vs!i\<close>
    and   idx_step_mod_value : \<open>valid_idx_step \<I>\<D>\<X> T i
                            \<Longrightarrow> valid_idx_step \<I>\<D>\<X> T j
                            \<Longrightarrow> v \<in> Well_Type T
                            \<Longrightarrow> idx_step_value \<I>\<D>\<X> i (idx_step_mod_value \<I>\<D>\<X> j f v) =
                                  (if i = j then f (idx_step_value \<I>\<D>\<X> j v) else idx_step_value \<I>\<D>\<X> i v) \<close>
    and   idx_step_mod_value_welltyp: \<open>valid_idx_step \<I>\<D>\<X> T i
                                   \<Longrightarrow> v \<in> Well_Type T
                                   \<Longrightarrow> f (idx_step_value \<I>\<D>\<X> i v) \<in> Well_Type (idx_step_type \<I>\<D>\<X> i T)
                                   \<Longrightarrow> idx_step_mod_value \<I>\<D>\<X> i f v \<in> Well_Type T\<close>
    and   idx_step_mod_value_tup : \<open>idx_step_mod_value \<I>\<D>\<X> i f (V_tup.mk vs) = V_tup.mk (vs[i := f (vs!i)])\<close>
    and   idx_step_mod_value_arr : \<open>idx_step_mod_value \<I>\<D>\<X> i f (V_array.mk (T,vs)) = V_array.mk (T,vs[i := f (vs!i)])\<close>
    and   idx_step_offset_arr: \<open>idx_step_offset \<I>\<D>\<X> (\<tau>Array N T) i = i * MemObj_Size T\<close>
begin

lemma V_tup_mult_cons:
  \<open>NO_MATCH vs ([]::'VAL list) \<Longrightarrow> V_tup.mk (v#vs) = V_tup.mk [v] * V_tup.mk vs\<close>
  using V_tup_mult by simp

abbreviation \<open>index_value \<equiv> fold (idx_step_value \<I>\<D>\<X>)\<close>
abbreviation \<open>index_type  \<equiv> fold (idx_step_type \<I>\<D>\<X>)\<close>
abbreviation \<open>index_mod_value \<equiv> foldr (idx_step_mod_value \<I>\<D>\<X>)\<close>

primrec valid_index :: \<open>'TY \<Rightarrow> nat list \<Rightarrow> bool\<close>
  where \<open>valid_index T [] \<longleftrightarrow> True\<close>
      | \<open>valid_index T (i#idx) \<longleftrightarrow> valid_idx_step \<I>\<D>\<X> T i \<and> valid_index (idx_step_type \<I>\<D>\<X> i T) idx\<close>

lemma valid_index_tail[simp]:
  \<open>valid_index T (idx@[i]) \<longleftrightarrow> valid_index T idx \<and> valid_idx_step \<I>\<D>\<X> (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma index_type_measure:
  \<open>valid_index T idx \<Longrightarrow> idx \<noteq> [] \<Longrightarrow> type_measure \<I>\<D>\<X> (index_type idx T) < type_measure \<I>\<D>\<X> T\<close>
  apply (induct idx arbitrary: T; simp)
  by (metis dual_order.strict_trans fold_simps(1) idx_step_type_measure)

lemma valid_index_cat: \<open>valid_index T (a@b) \<Longrightarrow> valid_index T a \<and> valid_index (index_type a T) b\<close>
  by (induct a arbitrary: T; simp)

lemma valid_index_cons: \<open>valid_index T [i] \<longleftrightarrow> valid_idx_step \<I>\<D>\<X> T i\<close> by simp

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



primrec index_offset :: \<open>'TY \<Rightarrow> nat list \<Rightarrow> nat\<close>
  where \<open>index_offset T [] = 0\<close>
      | \<open>index_offset T (i#idx) = idx_step_offset \<I>\<D>\<X> T i + index_offset (idx_step_type \<I>\<D>\<X> i T) idx\<close>

lemma index_offset_tail[simp]:
  \<open>index_offset T (idx@[i]) = index_offset T idx + idx_step_offset \<I>\<D>\<X> (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma index_type_idem:
  \<open>valid_index T idx \<Longrightarrow> index_type idx T = T \<longleftrightarrow> idx = []\<close>
  apply (cases idx; simp; rule)
  using index_type_measure
  by (metis fold_simps(2) list.discI order_less_irrefl valid_index.simps(2))


lemma Valid_Type_\<tau>Array[simp]:
  \<open>Valid_Type (\<tau>Array n T) \<longleftrightarrow> Valid_Type T\<close>
  unfolding Inhabited_def
  by simp (metis length_replicate list_all_length nth_replicate zero_well_typ)

lemma Valid_Type_\<tau>Tuple[simp]:
  \<open>Valid_Type (\<tau>Tuple Ts) \<longleftrightarrow> list_all Valid_Type Ts\<close>
  unfolding Inhabited_def
  using Ball_set zero_well_typ by blast

end


section \<open>\<phi>Type\<close>

context aggregate begin

subsection \<open>Tuple\<close>

subsubsection \<open>Empty Tuple\<close>

definition EmptyTuple :: \<open>('VAL, unit) \<phi>\<close>
  where \<open>EmptyTuple x = { V_tup.mk [] }\<close>

lemma EmptyTuple_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> EmptyTuple) \<longleftrightarrow> p = V_tup.mk []\<close>
  unfolding EmptyTuple_def \<phi>Type_def by simp

subsubsection \<open>Field\<close>

definition \<phi>Field :: "('VAL, 'a) \<phi> \<Rightarrow> ('VAL, 'a) \<phi>" ("\<clubsuit>")
  where "\<phi>Field T x = { V_tup.mk [v] |v. v \<in> T x }"

lemma \<phi>Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Field T) \<longleftrightarrow> (\<exists>v. p = V_tup.mk [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Field_def \<phi>Type_def by simp

lemma \<phi>Field_inhabited[elim!,\<phi>reason_elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<clubsuit> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma EmptyTuple_reduce[simp]:
  \<open>((a,()) \<Ztypecolon> \<clubsuit> T \<^emph> EmptyTuple) = (a \<Ztypecolon> \<clubsuit> T)\<close>
  unfolding set_eq_iff apply (simp add: \<phi>expns V_tup_mult)
  by (metis V_tup_mult append.left_neutral append_Cons)

lemma \<phi>Field_zero  [\<phi>reason on \<open>\<phi>Zero (T_tup.mk [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x \<Longrightarrow> \<phi>Zero (T_tup.mk [ty]) (\<clubsuit> T) x \<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Field_zeros [\<phi>reason on \<open>\<phi>Zero (T_tup.mk [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x
    \<Longrightarrow> \<phi>Zero (T_tup.mk tys) Ts xs
    \<Longrightarrow> \<phi>Zero (T_tup.mk (ty#tys)) (\<clubsuit> T \<^emph> Ts) (x,xs) \<close>
  unfolding \<phi>Zero_def
  by (simp add: \<phi>expns V_tup_mult_cons) blast

lemma \<phi>Field_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<clubsuit> ?T) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> T) TY \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<clubsuit> T) (\<tau>Tuple [TY])\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp simp add: \<phi>expns)

lemma \<phi>Field_semtsy[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> \<clubsuit> ?T \<^emph> ?Ts) ?ty\<close>]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (xs \<Ztypecolon> Ts) (\<tau>Tuple TYs)
\<Longrightarrow> \<phi>SemType ((x,xs) \<Ztypecolon> (\<clubsuit> T \<^emph> Ts)) (\<tau>Tuple (TY#TYs))\<close>
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


lemma (in aggregate) \<phi>Is_Tuple_\<phi>Is_Tuple_more[simp]:
  \<open>\<phi>Is_Tuple (\<clubsuit> A \<^emph> \<phi>Is_Tuple B) = (\<clubsuit> A \<^emph> \<phi>Is_Tuple B)\<close>
  apply (rule \<phi>Type_eqI)
  apply (clarsimp simp add: \<phi>expns, rule; clarify)
  by (metis V_tup_mult)

lemma (in aggregate) \<phi>Is_Tuple_Field[simp]:
  \<open>\<phi>Is_Tuple (\<clubsuit> A) = \<clubsuit> A\<close>
  by (rule \<phi>Type_eqI, clarsimp simp add: \<phi>expns, rule; clarify; blast)

lemma (in aggregate) \<phi>Is_Tuple_EmptyTuple[simp]:
  \<open>\<phi>Is_Tuple EmptyTuple = EmptyTuple\<close>
  by (rule \<phi>Type_eqI, clarsimp simp add: \<phi>expns)



subsection \<open>Array\<close>

definition Array :: "nat \<Rightarrow> ('VAL, 'a) \<phi> \<Rightarrow> ('VAL, 'a list) \<phi>"
  where \<open>Array N T = (\<lambda>l. { V_array.mk (TY,vs) |TY vs.
    length l = N \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)) })\<close>

lemma Array_expns[\<phi>expns]:
  \<open>v \<in> (l \<Ztypecolon> Array N T) \<longleftrightarrow>
    (\<exists> TY vs. length l = N \<and> v = V_array.mk (TY,vs) \<and> list_all2 (\<lambda>v x. v \<in> (x \<Ztypecolon> T)) vs l
        \<and> \<phi>\<phi>SemType T TY \<and> (\<exists>x. Inhabited (x \<Ztypecolon> T)))\<close>
  unfolding Array_def \<phi>Type_def by simp blast

lemma Array_inhabited[\<phi>reason_elim!, elim!]:
  \<open> Inhabited (l \<Ztypecolon> Array N T)
\<Longrightarrow> (length l = N \<Longrightarrow>(\<And>i. i < length l \<Longrightarrow> Inhabited (l!i \<Ztypecolon> T)) \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def by (clarsimp simp add: \<phi>expns list_all2_conv_all_nth) blast

lemma Array_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> Array ?N ?T) ?ty\<close>]:
  \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY) \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> Array N T) (\<tau>Array N TY)\<close>
  apply (clarsimp simp add: \<phi>expns list_all_length list_all2_conv_all_nth \<phi>SemType_def subset_iff
          Inhabited_def)
  using Well_Type_unique by blast
  
lemma Array_zero[\<phi>reason on \<open>\<phi>Zero (\<tau>Array ?N ?TY) (Array ?N ?T) ?x\<close>]:
  \<open>\<phi>Zero TY T zero \<Longrightarrow> \<phi>\<phi>SemType T TY \<Longrightarrow> \<phi>Zero (\<tau>Array N TY) (Array N T) (replicate N zero)\<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns list_all2_conv_all_nth Inhabited_def; blast)


subsection \<open>Index to Fields of Structures\<close>

definition \<phi>Index_getter :: \<open>nat list \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> ('VAL,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_getter idx T U g \<longleftrightarrow> index_value idx \<in> (g \<Ztypecolon> T \<Rrightarrow> U)\<close>

definition \<phi>Index_mapper :: \<open>nat list \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> ('VAL,'b) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_mapper idx T U f \<longleftrightarrow> (\<forall>g g'. g \<in> (g' \<Ztypecolon> U \<Rrightarrow> U) \<longrightarrow> index_mod_value idx g \<in> (f g' \<Ztypecolon> T \<Rrightarrow> T))\<close>


lemma idx_step_value_V_tup_suc:
  \<open>idx_step_value \<I>\<D>\<X> (Suc i) (V_tup.mk (va # vs)) = idx_step_value \<I>\<D>\<X> i (V_tup.mk vs)\<close>
  by (simp add: idx_step_value_tup)

lemma idx_step_mod_value_V_tup_suc:
  \<open>idx_step_mod_value \<I>\<D>\<X> (Suc i) g (V_tup.mk (va # vs)) = V_tup.mk [va] * idx_step_mod_value \<I>\<D>\<X> i g (V_tup.mk vs)\<close>
  by (metis NO_MATCH_I V_tup_mult_cons idx_step_mod_value_tup list_update_code(3) nth_Cons_Suc)
  



lemma (in aggregate) \<phi>Index_getter_tup_suc:
  \<open> \<phi>Index_getter (i # idx) X Y f
\<Longrightarrow> \<phi>Index_getter (Suc i # idx) (\<clubsuit> T \<^emph> \<phi>Is_Tuple X) Y (f o snd)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_V_tup_suc)

lemma (in aggregate) \<phi>Index_getter_tup_0:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (0 # idx) (\<clubsuit> X) Y f\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma (in aggregate) \<phi>Index_getter_tup_0r:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<phi>Index_getter (0 # idx) (\<clubsuit> X \<^emph> \<phi>Is_Tuple R) Y (f o fst)\<close>
  unfolding \<phi>Index_getter_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_tup)

lemma (in aggregate) \<phi>Index_getter_arr:
  \<open> \<phi>Index_getter idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < N
\<Longrightarrow> \<phi>Index_getter (i # idx) (Array N X) Y (\<lambda>l. f (l!i))\<close>
  unfolding \<phi>Index_getter_def Premise_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_arr list_all2_conv_all_nth)



lemma (in aggregate) \<phi>Index_mapper_tup_suc:
  \<open> \<phi>Index_mapper (i # idx) X Y f
\<Longrightarrow> \<phi>Index_mapper (Suc i # idx) (\<clubsuit> T \<^emph> \<phi>Is_Tuple X) Y (apsnd o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_V_tup_suc)
  by (metis idx_step_mod_value_tup)

lemma (in aggregate) \<phi>Index_mapper_tup_0:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>Index_mapper (0 # idx) (\<clubsuit> X) Y f\<close>
  unfolding \<phi>Index_mapper_def
  by (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)

lemma (in aggregate) \<phi>Index_mapper_tup_0r:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<phi>Index_mapper (0 # idx) (\<clubsuit> X \<^emph> \<phi>Is_Tuple X) Y (apfst o f)\<close>
  unfolding \<phi>Index_mapper_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_tup)
  by (metis V_tup_mult append.left_neutral append_Cons)

lemma (in aggregate) \<phi>Index_mapper_arr:
  \<open> \<phi>Index_mapper idx X Y f
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < N
\<Longrightarrow> \<phi>Index_mapper (i # idx) (Array N X) Y (\<lambda>g l. l[i := f g (l!i)])\<close>
  unfolding \<phi>Index_mapper_def Premise_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_arr list_all2_conv_all_nth)
  by (metis nth_list_update)



end


hide_const (open) valid_idx_step idx_step_type idx_step_value idx_step_mod_value idx_step_offset type_measure
hide_const (open) \<I>\<D>\<X>

end