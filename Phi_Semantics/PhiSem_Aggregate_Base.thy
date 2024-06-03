theory PhiSem_Aggregate_Base
  imports PhiSem_Common_Int PhiSem_Symbol
  keywords "\<lbrace>" "\<rbrace>" "\<tribullet>" :: quasi_command
  abbrevs "|>"  = "\<tribullet>"
begin

text \<open>The base for aggregate values which have inner structures and whose members can be
  accessed using indexes.\<close>

section \<open>Semantics\<close>

debt_axiomatization
        valid_idx_step :: \<open>TY \<Rightarrow> aggregate_index \<Rightarrow> bool\<close>
    and idx_step_type  :: \<open>aggregate_index \<Rightarrow> TY \<Rightarrow> TY\<close>
    and idx_step_value :: \<open>aggregate_index \<Rightarrow> VAL \<Rightarrow> VAL\<close>
    and idx_step_mod_value :: \<open>aggregate_index \<Rightarrow> (VAL \<Rightarrow> VAL) \<Rightarrow> VAL \<Rightarrow> VAL\<close>
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
and   idx_step_mod_value_unchanged :
          \<open> valid_idx_step T i
        \<Longrightarrow> u \<in> Well_Type T
        \<Longrightarrow> f (idx_step_value i u) = idx_step_value i u
        \<Longrightarrow> idx_step_mod_value i f u = u \<close>
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

abbreviation \<open>index_value \<equiv> fold idx_step_value\<close> (*TODO: rename \<rightarrow> get_element_of_value*)
abbreviation \<open>index_type  \<equiv> fold idx_step_type\<close>  (* get_element_of_type *)
abbreviation \<open>index_mod_value \<equiv> foldr idx_step_mod_value\<close> (* modify_value_element *)

primrec valid_index :: \<open>TY \<Rightarrow> aggregate_path \<Rightarrow> bool\<close>
  where \<open>valid_index T [] \<longleftrightarrow> True\<close>
      | \<open>valid_index T (i#idx) \<longleftrightarrow> valid_idx_step T i \<and> valid_index (idx_step_type i T) idx\<close>

declare [[\<phi>reason_default_pattern \<open>valid_index ?T ?idx\<close> \<Rightarrow> \<open>valid_index ?T ?idx\<close> (100)]]

\<phi>reasoner_group chk_sem_ele_idx_all = (1000, [0, 2000]) for (\<open>is_valid_step_idx_of idx T U\<close>,
                                                              \<open>is_valid_index_of idx T U\<close>)
    \<open>check whether the given element index \<open>idx\<close> is valid against semantic type \<open>T\<close>\<close>
  and chk_sem_ele_idx = (1010, [1000,1030]) in chk_sem_ele_idx_all
    \<open>cutting rules\<close>
  and chk_sem_ele_idx_fail = (0, [0,0]) in chk_sem_ele_idx_all
    \<open>failure\<close>

lemma [\<phi>reason %chk_sem_ele_idx]: \<open>valid_index T []\<close> by simp

lemma valid_index_tail[iff]:
  \<open>valid_index T (idx@[i]) \<longleftrightarrow> valid_index T idx \<and> valid_idx_step (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma [\<phi>reason %chk_sem_ele_idx_fail]:
  \<open> FAIL TEXT(\<open>Fail to show the validity of index\<close> idx \<open>on type\<close> T)
\<Longrightarrow> valid_index T idx\<close>
  unfolding FAIL_def
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

lemma index_type_neq:
  \<open> valid_index T idx \<Longrightarrow> idx \<noteq> [] \<Longrightarrow> index_type idx T \<noteq> T \<close>
  using index_type_measure by fastforce

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

lemma index_mod_value_unchanged:
  \<open> valid_index T idx
\<Longrightarrow> u \<in> Well_Type T
\<Longrightarrow> f (index_value idx u) = (index_value idx u)
\<Longrightarrow> index_mod_value idx f u = u \<close>
  by (induct idx arbitrary: T u f; clarsimp simp add: idx_step_mod_value_unchanged idx_step_value_welltyp)
  

subsection \<open>Semantics of aggregate path\<close>

definition \<open>AgIdx_VN v = AgIdx_N (the (\<phi>Sem_int_to_logic_nat (\<phi>arg.dest v)))\<close>

subsubsection \<open>Reasoning Rules\<close>

paragraph \<open>Syntactical Check of Semantics Validity of Aggregate Path\<close>

lemma [\<phi>reason 1000]:
  \<open>chk_semantics_validity ([]::aggregate_path)\<close>
  unfolding chk_semantics_validity_def ..

lemma [\<phi>reason 1000]:
  \<open> chk_semantics_validity [X]
\<Longrightarrow> chk_semantics_validity R
\<Longrightarrow> chk_semantics_validity (X#R)\<close>
  for R :: aggregate_path
  unfolding chk_semantics_validity_def ..

lemma [\<phi>reason 1020]:
  \<open>chk_semantics_validity [AgIdx_VN v]\<close>
  unfolding chk_semantics_validity_def ..

lemma [\<phi>reason 1020]:
  \<open>chk_semantics_validity [AgIdx_S s]\<close>
  unfolding chk_semantics_validity_def ..

lemma [\<phi>reason 1020]:
  \<open> Is_Literal n
\<Longrightarrow> chk_semantics_validity [AgIdx_N n]\<close>
  unfolding chk_semantics_validity_def ..



section \<open>Instructions\<close>

definition op_get_aggregate :: "aggregate_path \<Rightarrow> TY \<Rightarrow> (VAL, VAL) proc'"
  where "op_get_aggregate idx T = (\<lambda>v.
    \<phi>M_getV T id v (\<lambda>v'.
    \<phi>M_assert (valid_index T idx) \<then>
    Return (\<phi>arg (index_value idx v'))
))"

debt_axiomatization allow_assigning_different_typ :: \<open>TY \<Rightarrow> aggregate_path \<Rightarrow> bool\<close>

definition op_set_aggregate :: "TY \<Rightarrow> TY \<Rightarrow> aggregate_path \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_set_aggregate Tt Tv idx = 
    \<phi>M_caseV (\<lambda>tup v.
    \<phi>M_assert (valid_index Tt idx \<and> (index_type idx Tt = Tv \<or> allow_assigning_different_typ Tt idx)) \<then>
    \<phi>M_getV Tt id tup (\<lambda>tup'.
    \<phi>M_getV Tv id v (\<lambda>v'.
    Return (\<phi>arg (index_mod_value idx (\<lambda>_. v') tup'))
)))"


section \<open>Reasoning\<close>

text \<open>All the reasoning rules below are for semantic properties.
      All reasoning rules for transformations and SL are derived automatically\<close>

subsection \<open>Index Validation\<close>

definition \<open>is_valid_step_idx_of idx T U \<longleftrightarrow> valid_idx_step T idx \<and> U = idx_step_type idx T\<close>
definition \<open>is_valid_index_of idx T U \<longleftrightarrow> valid_index T idx \<and> U = index_type idx T\<close>

declare [[
  \<phi>reason_default_pattern \<open>is_valid_index_of ?idx ?T _\<close> \<Rightarrow> \<open>is_valid_index_of ?idx ?T _\<close> (100)
                      and \<open>is_valid_step_idx_of ?idx ?T _ \<close> \<Rightarrow> \<open>is_valid_step_idx_of ?idx ?T _ \<close> (100),
  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>is_valid_index_of _ _ _\<close>     (%\<phi>attr),
  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>is_valid_step_idx_of _ _ _\<close>  (%\<phi>attr)
]]

lemma is_valid_index_of_Nil:
  \<open>is_valid_index_of [] TY TY' \<longleftrightarrow> TY = TY'\<close>
  unfolding is_valid_index_of_def by simp blast

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> is_valid_index_of idx T U
\<Longrightarrow> valid_index T idx\<close>
  unfolding is_valid_index_of_def by blast

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> is_valid_index_of [] T T \<close>
  unfolding is_valid_index_of_def by simp

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> is_valid_step_idx_of i T W
\<Longrightarrow> is_valid_index_of idx W U
\<Longrightarrow> is_valid_index_of (i # idx) T U \<close>
  unfolding is_valid_index_of_def is_valid_step_idx_of_def
  by simp

subsection \<open>parse_ele_idx\<close> \<comment> \<open>Parse Element Index Input by Semantic Type\<close>

consts \<A>parse_eleidx :: action

definition \<open>parse_eleidx_input TY (input::element_index_input) semantic_idx spec_idx (reject::element_index_input)
    \<longleftrightarrow> valid_index TY spec_idx \<and> semantic_idx = spec_idx\<close>

definition \<open>parse_eleidx_input_least1 TY input sem_idx spec_idx reject
    \<longleftrightarrow> parse_eleidx_input TY input sem_idx spec_idx reject \<and>
        (input \<noteq> [] \<longrightarrow> spec_idx \<noteq> [])\<close>

declare [[
  \<phi>reason_default_pattern
      \<open>parse_eleidx_input ?TY ?input _ _ _ \<close> \<Rightarrow> \<open>parse_eleidx_input ?TY ?input _ _ _ \<close> (100)
  and \<open>parse_eleidx_input_least1 ?TY ?input _ _ _ \<close> \<Rightarrow> \<open>parse_eleidx_input_least1 ?TY ?input _ _ _ \<close> (100),

  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>parse_eleidx_input _ _ _ _ _\<close>         (%\<phi>attr),
  \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>parse_eleidx_input_least1 _ _ _ _ _\<close>  (%\<phi>attr)
]]

\<phi>reasoner_group \<A>parse_eleidx = (1000, [1000,1000]) for \<open>\<phi>arg.dest v \<Turnstile> S @tag \<A>parse_eleidx\<close>
      \<open>rules giving abstract specifiction of the values of an element index\<close>
  and parse_eleidx_input_all = (1000, [1, 2000]) for \<open>parse_eleidx_input TY input semantic_idx spec_idx reject\<close>
      \<open>reasoning parsing source of element index\<close>
  and parse_eleidx_input_success = (2000, [2000, 2000]) in parse_eleidx_input_all
      \<open>direct success\<close>
  and parse_eleidx_literal_symbol = (1700, [1700, 1700]) in parse_eleidx_input_all and < parse_eleidx_input_success
      \<open>literal index\<close>
  and parse_eleidx_literal_number = (1600, [1600, 1600]) in parse_eleidx_input_all and < parse_eleidx_literal_symbol
      \<open>literal number\<close>
  and parse_eleidx_input = (1000, [1000, 1200]) in parse_eleidx_input_all and < parse_eleidx_literal_number
      \<open>usual rules\<close>
  and parse_eleidx_number = (700, [700,899]) in parse_eleidx_input_all and < parse_eleidx_input \<open>\<close>
  and parse_eleidx_val = (500, [500,699]) in parse_eleidx_input_all and < parse_eleidx_number \<open>\<close>
  and parse_eleidx_input_fallback = (1, [1,1]) in parse_eleidx_input_all and < parse_eleidx_val
      \<open>rejecting all input, meaning the parsing fails\<close>

lemma [\<phi>reason %parse_eleidx_input]:
  \<open> parse_eleidx_input TY input sem_idx spec_idx reject
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input = [] \<or> spec_idx \<noteq> []
\<Longrightarrow> parse_eleidx_input_least1 TY input sem_idx spec_idx reject\<close>
  unfolding parse_eleidx_input_least1_def Premise_def by simp blast

lemma [\<phi>reason %parse_eleidx_input_success]:
  \<open>parse_eleidx_input TY [] [] [] []\<close>
  unfolding parse_eleidx_input_def
  by simp

lemma [\<phi>reason default %parse_eleidx_input_fallback]:
  \<open>parse_eleidx_input TY input [] [] input\<close>
  unfolding parse_eleidx_input_def
  by simp

lemma [\<phi>reason %parse_eleidx_literal_symbol]:
  \<open> \<g>\<u>\<a>\<r>\<d> is_valid_step_idx_of (AgIdx_S s) TY U
\<Longrightarrow> parse_eleidx_input U input sem_idx spec_idx reject
\<Longrightarrow> parse_eleidx_input TY
      ((\<phi>arg.dest (semantic_literal (sem_mk_symbol s)), S) # input)
      (AgIdx_S s # sem_idx) (AgIdx_S s # spec_idx) reject \<close>
  unfolding parse_eleidx_input_def is_valid_step_idx_of_def \<r>Guard_def Ant_Seq_def
  by clarsimp

lemma [\<phi>reason %parse_eleidx_number]:
  \<open> \<g>\<u>\<a>\<r>\<d> (\<phi>arg.dest v \<Turnstile> S @tag \<A>parse_eleidx) \<and>\<^sub>\<r>
          get_logical_nat_from_semantic_int S n \<and>\<^sub>\<r>
          is_valid_step_idx_of (AgIdx_N n) TY U
\<Longrightarrow> parse_eleidx_input U input sem_idx spec_idx reject
\<Longrightarrow> parse_eleidx_input TY              
      ((\<phi>arg.dest v, S) # input) (AgIdx_VN v # sem_idx) (AgIdx_N n # spec_idx) reject \<close>
  unfolding parse_eleidx_input_def Action_Tag_def
            get_logical_nat_from_semantic_int_def AgIdx_VN_def is_valid_step_idx_of_def
            \<r>nat_to_suc_nat_def \<r>Guard_def Ant_Seq_def
  by (cases v; clarsimp; metis option.sel)

lemma [\<phi>reason %parse_eleidx_literal_number]:
  \<open> \<g>\<u>\<a>\<r>\<d> (\<phi>arg.dest (semantic_literal v) \<Turnstile> S @tag \<A>parse_eleidx) \<and>\<^sub>\<r>
          get_logical_nat_from_semantic_int (v \<Ztypecolon> Itself) n \<and>\<^sub>\<r>
          is_valid_step_idx_of (AgIdx_N n) TY U
\<Longrightarrow> parse_eleidx_input U input sem_idx spec_idx reject
\<Longrightarrow> parse_eleidx_input TY
      ((\<phi>arg.dest (semantic_literal v), S) # input) (AgIdx_N n # sem_idx) (AgIdx_N n # spec_idx) reject \<close>
  unfolding parse_eleidx_input_def Action_Tag_def
            get_logical_nat_from_semantic_int_def AgIdx_VN_def is_valid_step_idx_of_def
            \<r>nat_to_suc_nat_def \<r>Guard_def Ant_Seq_def
  by (clarsimp; metis option.sel)


subsection \<open>Evaluate Index\<close>

consts eval_aggregate_path :: mode

ML \<open>
structure Eval_Sem_Idx_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>eval_aggregate_path\<close>
  val comment = "Rules evaluating indexing of semantic type and value"
  val attribute = NONE
  val post_merging = I
)\<close>

setup \<open>Context.theory_map (Eval_Sem_Idx_SS.map (
  Simplifier.add_cong @{thm' mk_symbol_cong}
))\<close>

\<phi>reasoner_ML eval_aggregate_path 1300 ( \<open>\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[eval_aggregate_path] ?X' : ?X\<close>
                                      | \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[eval_aggregate_path] ?P\<close> )
  = \<open>Phi_Reasoners.wrap (
      PLPR_Simplifier.simplifier_by_ss' (K Seq.empty) Eval_Sem_Idx_SS.get' {fix_vars=false}) o snd\<close>


lemmas [eval_aggregate_path] = nth_Cons_0 nth_Cons_Suc fold_simps list.size simp_thms

declare [[
  \<phi>premise_attribute       [THEN Premise_D] for \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[eval_aggregate_path] _\<close>  (%\<phi>attr_late_normalize),
  \<phi>premise_attribute once? [useful]         for \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[eval_aggregate_path] _\<close>  (%\<phi>attr) (*TODO: use EIF instead of this?*)
]]


subsection \<open>Index to Fields of Structures\<close>

definition \<open>\<phi>Type_Mapping T U f g \<longleftrightarrow> (\<forall>v x. v \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> g v \<Turnstile> (f x \<Ztypecolon> U))\<close>

definition \<phi>Aggregate_Getter :: \<open>aggregate_path \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Getter idx T U g \<longleftrightarrow> \<phi>Type_Mapping T U g (index_value idx) \<close>

definition \<phi>Aggregate_Mapper :: \<open>aggregate_path \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'a2) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> (VAL,'b2) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b2) \<Rightarrow> 'a \<Rightarrow> 'a2) \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Mapper idx T T' U U' f
    \<longleftrightarrow> (\<forall>g g'. \<phi>Type_Mapping U U' g' g \<longrightarrow> \<phi>Type_Mapping T T' (f g') (index_mod_value idx g)) \<close>

definition \<phi>Aggregate_Constructor_Synth :: \<open>(VAL list \<Rightarrow> VAL) \<Rightarrow> VAL list set \<Rightarrow> TY \<Rightarrow> VAL set \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Constructor_Synth constructor Args TY Spec
    \<longleftrightarrow> (\<forall>args. args \<Turnstile> Args \<longrightarrow> constructor args \<Turnstile> Spec \<and> constructor args \<in> Well_Type TY)\<close>

definition \<phi>Aggregate_Constructor :: \<open>(VAL list \<Rightarrow> VAL) \<Rightarrow> VAL \<phi>arg list \<Rightarrow> TY \<Rightarrow> VAL set \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Constructor constructor args TY Spec
    \<longleftrightarrow> constructor (map \<phi>arg.dest args) \<Turnstile> Spec \<and> constructor (map \<phi>arg.dest args) \<in> Well_Type TY\<close>

consts \<A>ctr_arg :: \<open>symbol + nat \<Rightarrow> action\<close>

declare [[\<phi>reason_default_pattern
    \<open>\<phi>Aggregate_Getter ?idx ?T _ _ \<close> \<Rightarrow> \<open>\<phi>Aggregate_Getter ?idx ?T _ _ \<close> (100)
and \<open>\<phi>Aggregate_Mapper ?idx ?T _ _ _ _ \<close> \<Rightarrow> \<open>\<phi>Aggregate_Mapper ?idx ?T _ _ _ _ \<close> (100)
and \<open>\<phi>Aggregate_Constructor_Synth _ _ _ ?T\<close> \<Rightarrow> \<open>\<phi>Aggregate_Constructor_Synth _ _ _ ?T\<close> (100)
and \<open>\<phi>Aggregate_Constructor ?ctor ?args _ _\<close> \<Rightarrow> \<open>\<phi>Aggregate_Constructor ?ctor ?args _ _\<close> (100),


    \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>\<phi>Aggregate_Getter _ _ _ _\<close>       (%\<phi>attr),
    \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>\<phi>Aggregate_Mapper _ _ _ _ _ _\<close>   (%\<phi>attr),
    \<phi>premise_attribute once? [\<phi>reason? %local] for \<open>\<phi>Aggregate_Constructor _ _ _ _\<close>  (%\<phi>attr)
]]

\<phi>reasoner_group aggregate_access_all = (100, [1, 2000]) for (\<open>\<phi>Aggregate_Getter idx T U g\<close>,
                                                         \<open>\<phi>Aggregate_Mapper idx T T' U U' f\<close>)
      \<open>Rules lifting semantic access of aggregate structures onto abstract domain\<close>
  and aggregate_access = (1010, [1000,1030]) in aggregate_access_all
      \<open>cutting rules\<close>

(*
lemma [\<phi>reason 1]:
  \<open>\<phi>Aggregate_Getter [] T T id\<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by simp
*)

lemma \<phi>Aggregate_Getter_Nil[\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Getter [] T T id\<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by simp

(*
lemma [\<phi>reason 1]:
  \<open>\<phi>Aggregate_Mapper [] T T' T T' id\<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by simp
*)

lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Mapper [] T T' T T' id\<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by simp


subsection \<open>Is Aggregate\<close>

definition Is_Aggregate :: \<open>('c,'a) \<phi> \<Rightarrow> bool\<close>
  where \<open>Is_Aggregate T \<longleftrightarrow> True\<close>

\<phi>reasoner_group is_aggregate_all = (1000, [1, 2000]) for \<open>Is_Aggregate T\<close>
      \<open>checking whether the given \<phi>type specifies an aggregate\<close>
  and is_aggregate = (1000, [1000, 1030]) in is_aggregate_all
      \<open>cutting rules\<close>

\<phi>property_deriver Is_Aggregate 555 for (\<open>Is_Aggregate _\<close>)
  = \<open>Phi_Type_Derivers.meta_Synt_Deriver
      ("Is_Aggregate", @{lemma' \<open>Is_Aggregate T\<close> by (simp add: Is_Aggregate_def)},
       SOME @{reasoner_group %is_aggregate})\<close>

lemma [\<phi>reason %is_aggregate]:
  \<open> Is_Aggregate T
\<Longrightarrow> Is_Aggregate U
\<Longrightarrow> Is_Aggregate (T \<^emph> U)\<close>
  unfolding Is_Aggregate_def ..

(*
subsection \<open>IDE-Interfaces\<close>

term ParamTag

definition Index_Param_Tag :: \<open>aggregate_path \<Rightarrow> bool\<close> ("\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> _" [1000] 26)
  where "\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> x \<equiv> True"

lemma Index_Param_Tag_Swap:
  \<open> \<p>\<a>\<r>\<a>\<m> P \<Longrightarrow> \<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> P \<close>
  unfolding Index_Param_Tag_def ..

ML_file \<open>syntax/index_param.ML\<close>

\<phi>lang_parser set_index_param 5000 (premises \<open>\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> _\<close>) \<open>fn (ctxt,sequent) =>
  Scan.pass (Context.Proof ctxt) Synt_Index_Param.index_term_parser >> (fn term => fn _ =>
      Phi_Sys.set_param term (ctxt, @{thm Index_Param_Tag_Swap} RS sequent))\<close>
*)


section \<open>First-level Abstraction of Instructions\<close>

lemma op_get_aggregate:
  \<open> Is_Aggregate T
\<Longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> parse_eleidx_input_least1 TY input_index sem_idx spec_idx reject
\<Longrightarrow> \<phi>Aggregate_Getter spec_idx T U f
\<Longrightarrow> report_unprocessed_element_index reject \<E>\<I>\<H>\<O>\<O>\<K>_none
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_aggregate sem_idx TY rv \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] T \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> U \<rbrace>\<close>
  unfolding op_get_aggregate_def Semantic_Type'_def subset_iff \<phi>Aggregate_Getter_def
            parse_eleidx_input_def
            parse_eleidx_input_least1_def
  by (cases rv; simp, rule, simp, rule, simp add: \<phi>Type_Mapping_def)

lemma "_op_set_aggregate_":
  \<open> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> parse_eleidx_input_least1 TY input_index sem_idx idx reject
\<Longrightarrow> Semantic_Type' (y \<Ztypecolon> U) TY\<^sub>U
\<Longrightarrow> is_valid_index_of idx TY TY\<^sub>U'
\<Longrightarrow> Premise eval_aggregate_path (TY\<^sub>U' = TY\<^sub>U \<or> allow_assigning_different_typ TY idx)
\<Longrightarrow> \<phi>Aggregate_Mapper idx T T' U' U f
\<Longrightarrow> report_unprocessed_element_index reject \<E>\<I>\<H>\<O>\<O>\<K>_none
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_aggregate TY TY\<^sub>U sem_idx (rv\<^bold>,ru)
      \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[ru] U \<longmapsto> \<lambda>ret. f (\<lambda>_. y) x \<Ztypecolon> \<v>\<a>\<l>[ret] T'
        \<s>\<u>\<b>\<j> (TY\<^sub>U' = TY\<^sub>U \<longrightarrow> \<phi>arg.dest ret \<in> Well_Type TY) \<rbrace>\<close>
  unfolding op_set_aggregate_def Semantic_Type'_def subset_iff \<phi>Aggregate_Mapper_def Premise_def
            parse_eleidx_input_def is_valid_index_of_def
            parse_eleidx_input_least1_def
  by (cases rv; cases ru; simp, rule, rule, simp, rule, simp,
      rule \<phi>M_Success_P[where X=1, simplified], simp add: \<phi>Type_Mapping_def,
      simp add: index_mod_value_welltyp)

lemma op_set_aggregate:
  \<open> Is_Aggregate T
\<Longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> parse_eleidx_input_least1 TY input_index sem_idx idx reject
\<Longrightarrow> Semantic_Type' (y \<Ztypecolon> U) TY2
\<Longrightarrow> is_valid_index_of idx TY TY2'
\<Longrightarrow> Premise eval_aggregate_path (TY2' = TY2 \<or> allow_assigning_different_typ TY idx)
\<Longrightarrow> \<phi>Aggregate_Mapper idx T T' U' U f
\<Longrightarrow> report_unprocessed_element_index reject \<E>\<I>\<H>\<O>\<O>\<K>_none
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_aggregate TY TY2 sem_idx (rv\<^bold>, ru) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[ru] U \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> \<v>\<a>\<l> T' \<rbrace>\<close>
  by ((rule \<phi>CONSEQ[OF "_op_set_aggregate_" view_shift_refl view_shift_by_implication view_shift_refl]; simp?),
      simp add: Transformation_def, blast)

hide_fact "_op_set_aggregate_"

proc op_construct_aggregate:
  input  \<open>Void\<close>
  requires C[unfolded \<phi>Aggregate_Constructor_def, useful]:
            \<open>\<phi>Aggregate_Constructor constructor args TY (x \<Ztypecolon> T)\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<close>
  \<medium_left_bracket>
    semantic_assert \<open>constructor (map \<phi>arg.dest args) \<in> Well_Type TY\<close>
    semantic_return \<open>constructor (map \<phi>arg.dest args) \<Turnstile> (x \<Ztypecolon> T)\<close>
  \<medium_right_bracket> .


proc synthesis_construct_aggregate:
  requires [unfolded \<phi>Aggregate_Constructor_def, useful]:
           \<open>\<phi>Aggregate_Constructor_Synth constructor (y \<Ztypecolon> U) TY (x \<Ztypecolon> T)\<close>
       and C: \<open>\<p>\<r>\<o>\<c> C \<lbrace> R\<^sub>0 \<longmapsto> \<lambda>ret. y \<Ztypecolon> \<v>\<a>\<l>\<s>[ret] U \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<^sub>1 \<rbrace> @tag synthesis\<close>
  input  \<open>R\<^sub>0\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<l> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<^sub>1\<close>
  @tag synthesis
  \<medium_left_bracket>
    C semantic_local_values_nochk
    semantic_assert \<open>constructor (\<phi>arg.dest \<v>0) \<in> Well_Type TY\<close>
    semantic_return \<open>constructor (\<phi>arg.dest \<v>0) \<Turnstile> (x \<Ztypecolon> T)\<close>
  \<medium_right_bracket> .

\<phi>reasoner_group \<phi>synthesis_ag = (%\<phi>synthesis_cut, [%\<phi>synthesis_cut, %\<phi>synthesis_cut+300])
  \<open>synthesis for aggregate structures\<close>



section \<open>Syntax Base\<close>

subsection \<open>Structure and Tuple\<close>

nonterminal "\<phi>_tuple_args_" and "\<phi>_tuple_arg_"

consts \<phi>_Empty_Tuple_sugar :: \<open>(VAL, 'any) \<phi>\<close> ("\<lbrace> \<rbrace>") \<comment> \<open>A syntax sugar to be overloaded\<close>

syntax "_\<phi>Tuple" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("\<lbrace> _ \<rbrace>")
       "_\<phi>tuple_arg"  :: "\<phi>_tuple_arg_ \<Rightarrow> \<phi>_tuple_args_" ("_")
       "_\<phi>tuple_args" :: "\<phi>_tuple_arg_ \<Rightarrow> \<phi>_tuple_args_ \<Rightarrow> \<phi>_tuple_args_" ("_,/ _")

translations
  "_\<phi>Tuple (_\<phi>tuple_args y z)" \<rightleftharpoons> "CONST \<phi>Prod (_\<phi>Tuple (_\<phi>tuple_arg y)) (_\<phi>Tuple z)"

ML \<open>fun strip_phi_tuple_args (Const(\<^syntax_const>\<open>_\<phi>tuple_args\<close>, _) $ x $ L)
          = x :: strip_phi_tuple_args L
      | strip_phi_tuple_args (Const(\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, _) $ x) = [x]
      | strip_phi_tuple_args _ = error "Bad Syntax"\<close>


subsection \<open>Access to Element Field\<close>

consts access_to_ele_synt :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
    \<comment> \<open>A syntax sugar to be overloaded\<close>
syntax "_access_to_ele_synt_" :: \<open>logic \<Rightarrow> \<phi>_ag_idx_ \<Rightarrow> logic\<close> (infixl "\<tribullet>" 55)

parse_translation \<open>[
  (\<^syntax_const>\<open>_access_to_ele_synt_\<close>, fn ctxt => fn [a,x] =>
      Const(\<^const_syntax>\<open>access_to_ele_synt\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.parse_index x)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>access_to_ele_synt\<close>, fn ctxt => fn [a,x] =>
      Const(\<^syntax_const>\<open>_access_to_ele_synt_\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.print_index x )
]\<close>
 
text \<open>We can use \<^term>\<open>p \<tribullet> field\<close> to access the address of the element named \<open>field\<close> in the
  object pointed by \<open>p\<close>.
  We may also use \<^term>\<open>p \<tribullet> 2\<close> to access the address of the 2nd element.
  Use \<^term>\<open>p \<tribullet> LOGIC_IDX(var)\<close> to access the element \<open>var\<close> which is a logical variable\<close>



section \<open>IDE Interface\<close>

(* declare_\<phi>lang_operator infix 40 := *)

\<phi>overloads "\<tribullet>" and ":="

declare op_get_aggregate[\<phi>overload "\<tribullet>"]
        op_set_aggregate[\<phi>overload ":="]

\<phi>reasoner_group \<phi>parser_lbrack = (500, [500,500]) \<open>\<close>
  and \<phi>parser_rbrack = (500,[500,500]) \<open>\<close>

ML_file \<open>library/generic_element_access.ML\<close>

\<phi>lang_parser aggregate_getter_setter (%\<phi>parser_lbrack, %\<phi>lang_top) ["["] (\<open>PROP _\<close>)
\<open> fn s => Parse.position \<^keyword>\<open>[\<close> >> (fn (_, pos) => fn cfg =>
    Generic_Element_Access.open_bracket_opr pos cfg s) \<close>

\<phi>lang_parser aggregate_getter_end (%\<phi>parser_rbrack, %\<phi>lang_top) ["]"] (\<open>PROP _\<close>)
\<open> fn opr_ctxt => Parse.position \<^keyword>\<open>]\<close> >> (fn (_, pos) => fn cfg => (
    Generic_Element_Access.close_bracket pos cfg opr_ctxt
)) \<close>

\<phi>lang_parser construct_aggregate (%\<phi>parser_lbrack, %\<phi>lang_top) ["\<lbrace>"] (\<open>PROP _\<close>)
\<open> fn s => Parse.position \<^keyword>\<open>\<lbrace>\<close> -- Scan.option (Parse.short_ident --| \<^keyword>\<open>:\<close>)
>> (fn ((_, pos), arg_name) => fn cfg =>
    Generic_Element_Access.gen_constructor "" (("\<lbrace>",pos), (arg_name, pos)) cfg s) \<close>

\<phi>lang_parser construct_aggregate_end (%\<phi>parser_rbrack, %\<phi>lang_top) ["\<rbrace>"] (\<open>PROP _\<close>)
\<open> fn opr_ctxt => Parse.position \<^keyword>\<open>\<rbrace>\<close> >> (fn (_, pos) => fn cfg => (
    Phi_Opr_Stack.check_meta_apply_balance "\<lbrace>" pos (#1 (#1 opr_ctxt)) ;
    Phi_Opr_Stack.close_parenthesis (cfg, NONE, false) opr_ctxt
)) \<close>

\<phi>lang_parser triangle_operator (%\<phi>parser_unique, %\<phi>lang_top) ["\<tribullet>"] (\<open>PROP _\<close>)
\<open> fn opr_ctxt => Parse.position \<^keyword>\<open>\<tribullet>\<close> >> (fn (_, pos) => fn cfg => (
  Phi_Opr_Stack.push_meta_operator cfg
            (Generic_Element_Access.mk_dot_opr pos (#1 (#1 opr_ctxt))) opr_ctxt
)) \<close>

text \<open>We differentiate \<open>\<leftarrow>\<close> and \<open>:=\<close>.
  \<open>\<leftarrow>\<close> is used to update the value of a local variable.
  \<open>:=\<close> is used to change the value of a memory object.
  Without this differentiation, ambiguity occurs when we have a local variable of a pointer
  pointing to a memory object which also stores a pointer, and an assignment can ambiguously refer
  to updating the variable or writing to the memory object.
\<close>

ML \<open>
fun dot_opr_chk_left_precedence prio pos oprs =
  let open Phi_Opr_Stack
      fun prec_of first (Meta_Opr (_,_,("$",_),_,_,_,_) :: L) =
            let val p = precedence_of L
             in if p >= @{priority %\<phi>lang_dot_opr}
                then prec_of false L
                else if p < prio
                then if first
                  then @{priority loose %\<phi>lang_push_val+1}
                  else @{priority loose %\<phi>lang_dot_opr+1}
                else prio
            end
        | prec_of first [] =
            if first
            then @{priority loose %\<phi>lang_push_val+1}
            else @{priority loose %\<phi>lang_dot_opr+1}
        | prec_of _ (Meta_Opr (_,_,("\<tribullet>",_),_,_,_,_) :: L) = prec_of false L
        | prec_of _ (Meta_Opr (pr,_,_,_,_,_,_) :: L) =
            if pr > @{priority %\<phi>lang_app}
            then prec_of false L
            else Generic_Element_Access.err_assignment pos
        | prec_of _ (Opr (pr,_,_,_,_,_) :: L) =
            if pr > @{priority %\<phi>lang_app}
            then prec_of false L
            else Generic_Element_Access.err_assignment pos
        | prec_of _ _ = prio
   in prec_of true oprs
  end
\<close>

\<phi>lang_parser assignment_opr (%\<phi>parser_left_arrow, %\<phi>lang_top) ["\<leftarrow>"] (\<open>PROP _\<close>)
\<open> fn opr_ctxt => Parse.position \<^keyword>\<open>\<leftarrow>\<close> >> (fn (_, pos) => fn cfg => (
let open Phi_Opr_Stack
    val prio = dot_opr_chk_left_precedence @{priority %\<phi>lang_assignment} pos (#1 (#1 opr_ctxt))
 in push_meta_operator cfg ((prio, @{priority %\<phi>lang_assignment}, (VAR_ARITY_IN_OPSTACK,1)), ("\<leftarrow>", pos), NONE,
                       Generic_Element_Access.dot_triangle_assignment) opr_ctxt
end
)) \<close>

\<phi>lang_parser update_opr (%\<phi>parser_left_arrow, %\<phi>lang_top) [":="] (\<open>PROP _\<close>)
\<open> fn opr_ctxt => Parse.position \<^keyword>\<open>:=\<close> >> (fn (_, pos) => fn cfg => (
let open Phi_Opr_Stack
    val prio = dot_opr_chk_left_precedence @{priority %\<phi>lang_update_opr} pos (#1 (#1 opr_ctxt))
 in push_meta_operator cfg ((prio, @{priority %\<phi>lang_update_opr}, (VAR_ARITY_IN_OPSTACK,1)), (":=", pos), NONE,
                       Generic_Element_Access.dot_triangle_update_opr) opr_ctxt
end
)) \<close>

\<phi>lang_parser literal_symbol_in_eleidx (%\<phi>parser_app-250, %\<phi>lang_push_val) [""]
                                      (\<open>CurrentConstruction programming_mode ?blk ?H ?S\<close>) \<open>
fn (oprs,(ctxt,sequent)) =>
  case #1 oprs
    of Phi_Opr_Stack.Meta_Opr (_,_,("\<tribullet>",_),_,_,_,_) :: _ => (
        Parse.name >> (fn s => fn _ =>
        (oprs, (ctxt, #transformation_rule Phi_Working_Mode.programming
                  OF [sequent, Thm.instantiate
                                  (TVars.empty, Vars.make [((("s",0),\<^typ>\<open>symbol\<close>),
                                                           Thm.cterm_of ctxt (Phi_Tool_Symbol.mk_symbol s))])
                                  @{thm "_intro_symbol_"}]))))
     | _ => Scan.fail
\<close>



end