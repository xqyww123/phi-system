theory PhiSem_Aggregate_Base
  imports PhiSem_Base
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


section \<open>Instructions\<close>

(* definition op_cons_tuple :: "'TY list \<Rightarrow> (VAL list) proc'"
  where "op_cons_tuple tys = (\<lambda>(vs,res).
    let N = length tys in
    if N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (take N vs) tys
    then Success (V_tup.mk (take N vs) # drop N vs, res)
    else Fail)" *)


definition op_get_aggregate :: "index list \<Rightarrow> TY \<Rightarrow> (VAL, VAL) proc'"
  where "op_get_aggregate idx T = (\<lambda>v.
    \<phi>M_getV T id v (\<lambda>v'.
    \<phi>M_assert (valid_index T idx) \<ggreater>
    Return (\<phi>arg (index_value idx v'))
))"

debt_axiomatization allow_assigning_different_typ :: \<open>TY \<Rightarrow> index list \<Rightarrow> bool\<close>

definition op_set_aggregate :: "TY \<Rightarrow> TY \<Rightarrow> index list \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_set_aggregate Tt Tv idx = 
    \<phi>M_caseV (\<lambda>v tup.
    \<phi>M_assert (valid_index Tt idx \<and> (index_type idx Tt = Tv \<or> allow_assigning_different_typ Tt idx)) \<ggreater>
    \<phi>M_getV Tv id v (\<lambda>v'.
    \<phi>M_getV Tt id tup (\<lambda>tup'.
    Return (\<phi>arg (index_mod_value idx (\<lambda>_. v') tup'))
)))"


section \<open>Reasoning\<close>

subsection \<open>Evaluate Index\<close>

consts eval_semantic_index :: mode

ML \<open>
structure Eval_Sem_Idx_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>eval_semantic_index\<close>
  val comment = "Rules evaluating indexing of semantic type and value"
)\<close>

\<phi>reasoner_ML eval_semantic_index 1300 ( \<open>Simplify eval_semantic_index ?X' ?X\<close>
                                      | \<open>Premise eval_semantic_index ?P\<close> )
  = \<open>PLPR_Simplifier.simplifier_by_ss' NONE Eval_Sem_Idx_SS.get'\<close>


lemmas [eval_semantic_index] = nth_Cons_0 nth_Cons_Suc fold_simps list.size simp_thms


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


subsection \<open>IDE-Interfaces\<close>

term ParamTag

definition Index_Param_Tag :: \<open>index list \<Rightarrow> bool\<close> ("\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> _" [1000] 26)
  where "\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> x \<equiv> True"

lemma Index_Param_Tag_Swap:
  \<open> \<p>\<a>\<r>\<a>\<m> P \<Longrightarrow> \<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> P \<close>
  unfolding Index_Param_Tag_def ..

ML_file \<open>syntax/index_param.ML\<close>

ML \<open>Scan.pass\<close>

\<phi>processor set_index_param 5000 (premises \<open>\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> _\<close>) \<open>fn (ctxt,sequent) =>
  Scan.pass (Context.Proof ctxt) Synt_Index_Param.index_term_parser >> (fn term => fn _ =>
      Phi_Sys.set_param term (ctxt, @{thm Index_Param_Tag_Swap} RS sequent))\<close>


section \<open>First-level Abstraction of Instructions\<close>

lemma op_get_aggregate:
  \<open> \<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> valid_index TY idx
\<Longrightarrow> \<phi>Index_getter idx T U f
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_aggregate idx TY rv \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] T \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> U \<rbrace>\<close>
  unfolding op_get_aggregate_def \<phi>SemType_def subset_iff \<phi>Index_getter_def
  by (cases rv; simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>Mapping_expn)

lemma op_set_aggregate:
  \<open> \<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY2
\<Longrightarrow> Premise eval_semantic_index (index_type idx TY = TY2 \<or> allow_assigning_different_typ TY idx)
\<Longrightarrow> valid_index TY idx
\<Longrightarrow> \<phi>Index_mapper idx T T' U' U f
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_aggregate TY TY2 idx (ru\<^bold>, rv) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[ru] U \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> \<v>\<a>\<l> T' \<rbrace>\<close>
  unfolding op_set_aggregate_def \<phi>SemType_def subset_iff \<phi>Index_mapper_def Premise_def
  by (cases rv; cases ru; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>Mapping_expn)





end