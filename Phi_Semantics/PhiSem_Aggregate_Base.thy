theory PhiSem_Aggregate_Base
  imports Phi_System.PhiSem_Formalization_Tools
begin

text \<open>The base for aggregate values which have inner structures and whose members can be
  accessed using indexes.\<close>

section \<open>Semantics\<close>

type_synonym index = nat

debt_axiomatization
        valid_idx_step :: \<open>TY \<Rightarrow> index \<Rightarrow> bool\<close>
    and idx_step_type  :: \<open>index \<Rightarrow> TY \<Rightarrow> TY\<close>
    and idx_step_value :: \<open>index \<Rightarrow> VAL \<Rightarrow> VAL\<close>
    and idx_step_mod_value :: \<open>index \<Rightarrow> (VAL \<Rightarrow> VAL) \<Rightarrow> VAL \<Rightarrow> VAL\<close>
    and type_measure :: \<open>TY \<Rightarrow> nat\<close>
where idx_step_value_welltyp:
           \<open>valid_idx_step T i
        \<Longrightarrow> v \<in> Well_Type T
        \<Longrightarrow> idx_step_value i v \<in> Well_Type (idx_step_type i T)\<close>
and   idx_step_mod_value :
           \<open>valid_idx_step T i
        \<Longrightarrow> valid_idx_step T j
        \<Longrightarrow> v \<in> Well_Type T
        \<Longrightarrow> idx_step_value i (idx_step_mod_value j f v) =
              (if i = j then f (idx_step_value j v) else idx_step_value i v) \<close>
and   idx_step_mod_value_welltyp:
           \<open>valid_idx_step T i
        \<Longrightarrow> v \<in> Well_Type T
        \<Longrightarrow> f (idx_step_value i v) \<in> Well_Type (idx_step_type i T)
        \<Longrightarrow> idx_step_mod_value i f v \<in> Well_Type T\<close>
and   idx_step_type_measure:
           \<open>valid_idx_step T i \<Longrightarrow> type_measure (idx_step_type i T) < type_measure T\<close>

text \<open>We first formalize the behavior of indexing one-step inside one level of the inner structures,
  and upon them indexing of multiple steps is successively playing each step.

  \<^const>\<open>valid_idx_step\<close> asserts whether an index is valid on the type.
  \<^const>\<open>idx_step_type\<close> steps into the inner type of the given type.
  \<^const>\<open>idx_step_value\<close> gives the inner structure of a given value, and \<^const>\<open>idx_step_mod_value\<close>
    enables to modify the inner structure.
  \<^const>\<open>type_measure\<close> is a scaffold giving a decreasing measurement when indexing inside,
    such as the size of the term. It helps induction over the indexing. 
\<close>

abbreviation \<open>index_value \<equiv> fold idx_step_value\<close>
abbreviation \<open>index_type  \<equiv> fold idx_step_type\<close>
abbreviation \<open>index_mod_value \<equiv> foldr idx_step_mod_value\<close>

primrec valid_index :: \<open>TY \<Rightarrow> nat list \<Rightarrow> bool\<close>
  where \<open>valid_index T [] \<longleftrightarrow> True\<close>
      | \<open>valid_index T (i#idx) \<longleftrightarrow> valid_idx_step T i \<and> valid_index (idx_step_type i T) idx\<close>

lemma valid_index_tail[simp]:
  \<open>valid_index T (idx@[i]) \<longleftrightarrow> valid_index T idx \<and> valid_idx_step (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma valid_index_cat: \<open>valid_index T (a@b) \<Longrightarrow> valid_index T a \<and> valid_index (index_type a T) b\<close>
  by (induct a arbitrary: T; simp)

lemma valid_index_cons: \<open>valid_index T [i] \<longleftrightarrow> valid_idx_step T i\<close> by simp

lemma index_value_welltyp:
  \<open>valid_index T idx \<Longrightarrow> v \<in> Well_Type T \<Longrightarrow> index_value idx v \<in> Well_Type (index_type idx T)\<close>
  apply (induct idx arbitrary: v T; simp)
  using idx_step_value_welltyp
  by blast

lemma index_type_measure:
  \<open>valid_index T idx \<Longrightarrow> idx \<noteq> [] \<Longrightarrow> type_measure (index_type idx T) < type_measure T\<close>
  apply (induct idx arbitrary: T; simp)
  by (metis dual_order.strict_trans fold_simps(1) idx_step_type_measure)

lemma index_mod_value_welltyp:
   \<open>valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> f (index_value idx v) \<in> Well_Type (index_type idx T)
\<Longrightarrow> index_mod_value idx f v \<in> Well_Type T\<close>
  apply (induct idx arbitrary: T v; simp)
  using idx_step_mod_value_welltyp idx_step_value_welltyp by blast

lemma index_type_idem:
  \<open>valid_index T idx \<Longrightarrow> index_type idx T = T \<longleftrightarrow> idx = []\<close>
  apply (cases idx; simp; rule)
  using index_type_measure
  by (metis fold_simps(2) list.discI order_less_irrefl valid_index.simps(2))




end