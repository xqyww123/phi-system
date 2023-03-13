theory PhiSem_Aggregate
  imports PhiSem_Aggregate_Base
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
        WT_tup[simp]: \<open>Well_Type (tup ts)  = { V_tup.mk vs       |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
  and   WT_arr[simp]: \<open>Well_Type (array n t) = { V_array.mk (t,vs) |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs \<and> Valid_Type t }\<close>
  and   zero_tup[simp]: \<open>Zero (tup Ts)     = map_option V_tup.mk (those (map Zero Ts))\<close>
  and   zero_arr[simp]: \<open>Zero (array N T)  = map_option (\<lambda>z. V_array.mk (T, replicate N z)) (Zero T)\<close>
  and   V_tup_sep_disj[simp]: \<open>V_tup.mk l1 ## V_tup.mk l2\<close>
  and   V_tup_mult    : \<open>V_tup.mk l1 * V_tup.mk l2 = V_tup.mk (l2 @ l1)\<close>
(*  and   idx_step_type_measure: \<open>valid_idx_step T i
                            \<Longrightarrow> type_measure (idx_step_type i T) < type_measure T\<close>*)
  and   idx_step_type_tup  : \<open>i < length tys \<Longrightarrow> idx_step_type i (tup tys) = tys!i \<close>
  and   idx_step_type_arr  : \<open>i \<le> N \<Longrightarrow> idx_step_type i (array N T) = T\<close>
  and   valid_idx_step_tup : \<open>valid_idx_step (tup tys) i \<longleftrightarrow> i < length tys\<close>
  and   valid_idx_step_arr : \<open>valid_idx_step (array N T) i \<longleftrightarrow> i < N\<close>
  and   idx_step_value_tup : \<open>idx_step_value i (V_tup.mk vs)   = vs!i\<close>
  and   idx_step_value_arr : \<open>idx_step_value i (V_array.mk (T,vs)) = vs!i\<close>
  and   idx_step_mod_value_tup : \<open>idx_step_mod_value i f (V_tup.mk vs) = V_tup.mk (vs[i := f (vs!i)])\<close>
  and   idx_step_mod_value_arr : \<open>idx_step_mod_value i f (V_array.mk (T,vs)) = V_array.mk (T,vs[i := f (vs!i)])\<close>


lemma V_tup_mult_cons:
  \<open>NO_MATCH vs ([]::VAL list) \<Longrightarrow> V_tup.mk (v#vs) = V_tup.mk vs * V_tup.mk [v]\<close>
  using V_tup_mult by simp






(* TODO: move this

primrec index_offset :: \<open>TY \<Rightarrow> nat list \<Rightarrow> nat\<close>
  where \<open>index_offset T [] = 0\<close>
      | \<open>index_offset T (i#idx) = idx_step_offset T i + index_offset (idx_step_type i T) idx\<close>

lemma index_offset_tail[simp]:
  \<open>index_offset T (idx@[i]) = index_offset T idx + idx_step_offset (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp) *)


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

definition Tuple_Field :: "(VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>"
  where "Tuple_Field T x = { V_tup.mk [v] |v. v \<in> T x }"

syntax "_\<phi>Tuple" :: \<open>tuple_args \<Rightarrow> logic\<close> ("\<lbrace> _ \<rbrace>")

translations
  "_\<phi>Tuple (_tuple_arg X)" \<rightleftharpoons> "CONST Tuple_Field X"
  "_\<phi>Tuple (_tuple_args y z)" \<rightleftharpoons> "CONST \<phi>Prod (_\<phi>Tuple (_tuple_arg y)) (_\<phi>Tuple z)"

lemma Tuple_Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<lbrace> T \<rbrace>) \<longleftrightarrow> (\<exists>v. p = V_tup.mk [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding Tuple_Field_def \<phi>Type_def by simp

lemma Tuple_Field_inhabited[elim!,\<phi>inhabitance_rule]:
  \<open>Inhabited (x \<Ztypecolon> \<lbrace> T \<rbrace>) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma EmptyTuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> EmptyTuple \<^emph> \<lbrace> T \<rbrace>) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  \<open>((a,()) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> EmptyTuple) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding set_eq_iff
  apply (clarsimp; rule; clarsimp simp add: \<phi>expns V_tup_mult)
  apply (metis V_tup_mult V_tup_sep_disj append_Nil)
  apply (clarsimp; rule; clarsimp simp add: \<phi>expns V_tup_mult)
  by (metis V_tup_mult V_tup_sep_disj append_Cons append_Nil)

lemma Tuple_Field_zero  [\<phi>reason 1000]:
  \<open>\<phi>Zero ty T x \<Longrightarrow> \<phi>Zero (tup [ty]) \<lbrace> T \<rbrace> x \<close>
  unfolding \<phi>Zero_def by (clarsimp simp add: \<phi>expns)

lemma Tuple_Field_zeros [\<phi>reason 1000]:
  \<open>\<phi>Zero ty T x
    \<Longrightarrow> \<phi>Zero (tup tys) Ts xs
    \<Longrightarrow> \<phi>Zero (tup (ty#tys)) (\<lbrace> T \<rbrace> \<^emph> Ts) (x,xs) \<close>
  unfolding \<phi>Zero_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult_cons image_iff)
  using V_tup_sep_disj by blast


lemma Tuple_Field_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (x \<Ztypecolon> T) TY \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<lbrace> T \<rbrace>) (tup [TY])\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp simp add: \<phi>expns)

lemma Tuple_Field_semtys[\<phi>reason 1000]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (xs \<Ztypecolon> Ts) (tup TYs)
\<Longrightarrow> \<phi>SemType ((x,xs) \<Ztypecolon> (\<lbrace> T \<rbrace> \<^emph> Ts)) (tup (TY#TYs))\<close>
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

lemma Array_semty[\<phi>reason 1000]:
  \<open>(\<And>x. \<phi>SemType (x \<Ztypecolon> T) TY) \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> Array N T) (array N TY)\<close>
  apply (clarsimp simp add: \<phi>expns list_all_length list_all2_conv_all_nth \<phi>SemType_def subset_iff
          Inhabited_def)
  using Well_Type_unique by blast

lemma Array_zero[\<phi>reason 1000]:
  \<open>\<phi>Zero TY T zero \<Longrightarrow> \<phi>\<phi>SemType T TY \<Longrightarrow> \<phi>Zero (array N TY) (Array N T) (replicate N zero)\<close>
  unfolding \<phi>Zero_def
  by (clarsimp simp add: \<phi>expns list_all2_conv_all_nth Inhabited_def image_iff; blast)


subsection \<open>Index to Fields of Structures\<close>

definition \<phi>Index_getter :: \<open>nat list \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_getter idx T U g \<longleftrightarrow> index_value idx \<in> (g \<Ztypecolon> T \<Rrightarrow> U)\<close>

definition \<phi>Index_mapper :: \<open>nat list \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_mapper idx T U f \<longleftrightarrow> (\<forall>g g'. g \<in> (g' \<Ztypecolon> U \<Rrightarrow> U) \<longrightarrow> index_mod_value idx g \<in> (f g' \<Ztypecolon> T \<Rrightarrow> T))\<close>

declare [[
  \<phi>reason_default_pattern \<open>\<phi>Index_getter ?idx ?T _ _\<close> \<Rightarrow> \<open>\<phi>Index_getter ?idx ?T _ _\<close> (100),
  \<phi>reason_default_pattern \<open>\<phi>Index_mapper ?idx ?T _ _\<close> \<Rightarrow> \<open>\<phi>Index_mapper ?idx ?T _ _\<close> (100)
]]

declare [[\<phi>trace_reasoning = 1]]

lemma idx_step_value_V_tup_suc:
  \<open>idx_step_value (Suc i) (V_tup.mk (va # vs)) = idx_step_value i (V_tup.mk vs)\<close>
  by (simp add: idx_step_value_tup)

lemma idx_step_mod_value_V_tup_suc:
  \<open>idx_step_mod_value (Suc i) g (V_tup.mk (va # vs)) = idx_step_mod_value i g (V_tup.mk vs) * V_tup.mk [va]\<close>
  by (metis NO_MATCH_I V_tup_mult_cons idx_step_mod_value_tup list_update_code(3) nth_Cons_Suc)


lemma [\<phi>reason 1200]:
  \<open> \<phi>Index_getter (i # idx) X Y f
\<Longrightarrow> \<phi>Index_getter (Suc i # idx) (\<clubsuit> T \<^emph> X) Y (f o snd)\<close>
  unfolding \<phi>Index_getter_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_value_V_tup_suc)

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
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
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
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> i < N
\<Longrightarrow> \<phi>Index_mapper (i # idx) (Array N X) Y (\<lambda>g l. l[i := f g (l!i)])\<close>
  unfolding \<phi>Index_mapper_def Premise_def
  apply (clarsimp simp add: \<phi>expns V_tup_mult idx_step_mod_value_arr list_all2_conv_all_nth)
  by (metis nth_list_update)





definition op_get_tuple :: "index list \<Rightarrow> TY \<Rightarrow> (VAL, VAL) proc'"
  where "op_get_tuple idx T = (\<lambda>v.
    \<phi>M_getV T id v (\<lambda>v'.
    \<phi>M_assert (valid_index T idx) \<ggreater>
    Return (\<phi>arg (index_value idx v'))
))"

term \<open>3-4-5\<close>

definition op_set_tuple :: "index \<Rightarrow> TY \<Rightarrow> (VAL, VAL) proc'"
  where "op_set_tuple idx T = (\<lambda>v.
    \<phi>M_getV T V_tup.dest v (\<lambda>vals.
    Return (\<phi>arg (vals ! idx))
))"



definition op_get_tuple :: "index list \<Rightarrow> TY \<Rightarrow> VAL proc"
  where "op_get_tuple idx T = (\<lambda>(v#vs,res).
    if valid_index T idx \<and> v \<in> Well_Type T
    then Success (index_value idx v # vs, res)
    else Fail)"


term V_tup.mk





end