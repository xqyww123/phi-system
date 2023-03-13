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

declare [[\<phi>reason_default_pattern \<open>valid_index ?T ?idx\<close> \<Rightarrow> \<open>valid_index ?T ?idx\<close> (100)]]

lemma [\<phi>reason 1200]: \<open>valid_index T []\<close> by simp

lemma valid_index_tail[simp]:
  \<open>valid_index T (idx@[i]) \<longleftrightarrow> valid_index T idx \<and> valid_idx_step (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma [\<phi>reason 1]:
  \<open> FAIL TEXT(\<open>Fail to show the validity of index\<close> idx \<open>on type\<close> T)
\<Longrightarrow> valid_index T idx\<close>
  by blast

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

section \<open>Reasoning\<close>

subsection \<open>Evaluate Index\<close>

consts eval_semantic_index :: mode

ML \<open>
structure Eval_Sem_Idx_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>eval_semantic_index\<close>
  val comment = "Rules evaluating indexing of semantic type and value"
)\<close>

\<phi>reasoner_ML eval_semantic_index 1300 (\<open>Simplify eval_semantic_index ?X' ?X\<close>)
  = \<open>PLPR_Simplifier.simplifier_by_ss' NONE Eval_Sem_Idx_SS.get'\<close>

lemmas [eval_semantic_index] = nth_Cons_0 nth_Cons_Suc fold_simps


subsection \<open>Index to Fields of Structures\<close>

definition \<phi>Index_getter :: \<open>nat list \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_getter idx T U g \<longleftrightarrow> index_value idx \<in> (g \<Ztypecolon> T \<Rrightarrow> U)\<close>

definition \<phi>Index_mapper :: \<open>nat list \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'a2) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> (VAL,'b2) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b2) \<Rightarrow> 'a \<Rightarrow> 'a2) \<Rightarrow> bool\<close>
  where \<open>\<phi>Index_mapper idx T T' U U' f
    \<longleftrightarrow> (\<forall>g g'. g \<in> (g' \<Ztypecolon> U \<Rrightarrow> U') \<longrightarrow> index_mod_value idx g \<in> (f g' \<Ztypecolon> T \<Rrightarrow> T'))\<close>

declare [[
  \<phi>reason_default_pattern \<open>\<phi>Index_getter ?idx ?T _ _\<close> \<Rightarrow> \<open>\<phi>Index_getter ?idx ?T _ _\<close> (100),
  \<phi>reason_default_pattern \<open>\<phi>Index_mapper ?idx ?T _ _ _ _\<close> \<Rightarrow> \<open>\<phi>Index_mapper ?idx ?T _ _ _ _\<close> (100)
]]

lemma [\<phi>reason 1200]:
  \<open>\<phi>Index_getter [] T T id\<close>
  unfolding \<phi>Index_getter_def
  by (simp add: \<phi>Mapping_expn)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Index_mapper [] T T' T T' id\<close>
  unfolding \<phi>Index_mapper_def
  by (simp add: \<phi>Mapping_expn)



end