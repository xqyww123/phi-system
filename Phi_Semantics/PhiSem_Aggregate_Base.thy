theory PhiSem_Aggregate_Base
  imports PhiSem_Aggregate_Path PhiSem_Common_Int
  keywords "\<lbrace>" "\<rbrace>" :: quasi_command
  abbrevs "|>"  = "\<tribullet>"
begin

text \<open>The base for aggregate values which have inner structures and whose members can be
  accessed using indexes.\<close>

section \<open>Semantics\<close>

subsection \<open>Formalization\<close>

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

paragraph \<open>Unwind aggregate path into logical form easy for reasoning\<close>

definition \<open>unwind_aggregate_path_into_logical_form A B \<longleftrightarrow> A = B\<close>

declare [[\<phi>reason_default_pattern
  \<open>unwind_aggregate_path_into_logical_form ?A _\<close> => \<open>unwind_aggregate_path_into_logical_form ?A _\<close> (100)
]]

lemma [\<phi>reason 1000]:
  \<open>unwind_aggregate_path_into_logical_form [] []\<close>
  unfolding unwind_aggregate_path_into_logical_form_def ..

lemma [\<phi>reason 1000]:
  \<open> unwind_aggregate_path_into_logical_form X X'
\<Longrightarrow> unwind_aggregate_path_into_logical_form R R'
\<Longrightarrow> unwind_aggregate_path_into_logical_form (X#R) (X'#R')\<close>
  unfolding unwind_aggregate_path_into_logical_form_def by simp

lemma [\<phi>reason 1000]:
  \<open> \<phi>arg.dest v \<in> S
\<Longrightarrow> get_logical_nat_from_semantic_int S n
\<Longrightarrow> \<r>nat_to_suc_nat n n'
  \<or> ERROR TEXT(\<open>Fail to access the\<close> n \<open>th element: Fail to reduce it into a literal number\<close>)
\<Longrightarrow> unwind_aggregate_path_into_logical_form (AgIdx_VN v) (AgIdx_N n')\<close>
  unfolding get_logical_nat_from_semantic_int_def unwind_aggregate_path_into_logical_form_def
            AgIdx_VN_def Ball_def
  by (cases v; simp; metis option.sel)

lemma [\<phi>reason 1000]:
  \<open> Is_Literal n
\<Longrightarrow> unwind_aggregate_path_into_logical_form (AgIdx_N n) (AgIdx_N n)\<close>
  unfolding unwind_aggregate_path_into_logical_form_def ..

lemma [\<phi>reason 1000]:
  \<open> unwind_aggregate_path_into_logical_form (AgIdx_S s) (AgIdx_S s)\<close>
  unfolding unwind_aggregate_path_into_logical_form_def ..


section \<open>Instructions\<close>

(* definition op_cons_tuple :: "'TY list \<Rightarrow> (VAL list) proc'"
  where "op_cons_tuple tys = (\<lambda>(vs,res).
    let N = length tys in
    if N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (take N vs) tys
    then Success (V_tup.mk (take N vs) # drop N vs, res)
    else Fail)" *)


definition op_get_aggregate :: "aggregate_path \<Rightarrow> TY \<Rightarrow> (VAL, VAL) proc'"
  where "op_get_aggregate idx T = (\<lambda>v.
    \<phi>M_getV T id v (\<lambda>v'.
    \<phi>M_assert (valid_index T idx) \<ggreater>
    Return (\<phi>arg (index_value idx v'))
))"

debt_axiomatization allow_assigning_different_typ :: \<open>TY \<Rightarrow> aggregate_path \<Rightarrow> bool\<close>

definition op_set_aggregate :: "TY \<Rightarrow> TY \<Rightarrow> aggregate_path \<Rightarrow> (VAL \<times> VAL, VAL) proc'"
  where "op_set_aggregate Tt Tv idx = 
    \<phi>M_caseV (\<lambda>v tup.
    \<phi>M_assert (valid_index Tt idx \<and> (index_type idx Tt = Tv \<or> allow_assigning_different_typ Tt idx)) \<ggreater>
    \<phi>M_getV Tv id v (\<lambda>v'.
    \<phi>M_getV Tt id tup (\<lambda>tup'.
    Return (\<phi>arg (index_mod_value idx (\<lambda>_. v') tup'))
)))"


section \<open>Reasoning\<close>

subsection \<open>Evaluate Index\<close>

consts eval_aggregate_path :: mode

ML \<open>
structure Eval_Sem_Idx_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = \<^binding>\<open>eval_aggregate_path\<close>
  val comment = "Rules evaluating indexing of semantic type and value"
)\<close>

\<phi>reasoner_ML eval_aggregate_path 1300 ( \<open>\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[eval_aggregate_path] ?X' : ?X\<close>
                                      | \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[eval_aggregate_path] ?P\<close> )
  = \<open>PLPR_Simplifier.simplifier_by_ss' Eval_Sem_Idx_SS.get'\<close>


lemmas [eval_aggregate_path] = nth_Cons_0 nth_Cons_Suc fold_simps list.size simp_thms

declare [[
  \<phi>premise_attribute  [elim_premise_tag] for \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[eval_aggregate_path] _\<close>,
  \<phi>premise_attribute? [useful]           for \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[eval_aggregate_path] _\<close>
]]


subsection \<open>Index to Fields of Structures\<close>

definition \<phi>Aggregate_Getter :: \<open>aggregate_path \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Getter idx T U g \<longleftrightarrow> index_value idx \<in> (g \<Ztypecolon> T \<Rrightarrow> U)\<close>

definition \<phi>Aggregate_Mapper :: \<open>aggregate_path \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (VAL,'a2) \<phi> \<Rightarrow> (VAL,'b) \<phi> \<Rightarrow> (VAL,'b2) \<phi> \<Rightarrow> (('b \<Rightarrow> 'b2) \<Rightarrow> 'a \<Rightarrow> 'a2) \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Mapper idx T T' U U' f
    \<longleftrightarrow> (\<forall>g g'. g \<in> (g' \<Ztypecolon> U \<Rrightarrow> U') \<longrightarrow> index_mod_value idx g \<in> (f g' \<Ztypecolon> T \<Rrightarrow> T'))\<close>

definition \<phi>Aggregate_Constructor :: \<open>(VAL \<phi>arg list \<Rightarrow> VAL) \<Rightarrow> VAL \<phi>arg list \<Rightarrow> TY \<Rightarrow> VAL set \<Rightarrow> bool\<close>
  where \<open>\<phi>Aggregate_Constructor constructor args TY Spec
    \<longleftrightarrow> constructor args \<in> Spec \<and> constructor args \<in> Well_Type TY\<close>

declare [[\<phi>reason_default_pattern
    \<open>\<phi>Aggregate_Getter ?idx ?T _ _\<close> \<Rightarrow> \<open>\<phi>Aggregate_Getter ?idx ?T _ _\<close> (100)
and \<open>\<phi>Aggregate_Mapper ?idx ?T _ _ _ _\<close> \<Rightarrow> \<open>\<phi>Aggregate_Mapper ?idx ?T _ _ _ _\<close> (100)
and \<open>\<phi>Aggregate_Constructor ?ctor ?args _ _\<close> \<Rightarrow> \<open>\<phi>Aggregate_Constructor ?ctor ?args _ _\<close> (100)
]]

lemma [\<phi>reason 1200]:
  \<open>\<phi>Aggregate_Getter [] T T id\<close>
  unfolding \<phi>Aggregate_Getter_def
  by (simp add: \<phi>Mapping_expn)

lemma [\<phi>reason 1200]:
  \<open>\<phi>Aggregate_Mapper [] T T' T T' id\<close>
  unfolding \<phi>Aggregate_Mapper_def
  by (simp add: \<phi>Mapping_expn)

(*
subsection \<open>IDE-Interfaces\<close>

term ParamTag

definition Index_Param_Tag :: \<open>aggregate_path \<Rightarrow> bool\<close> ("\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> _" [1000] 26)
  where "\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> x \<equiv> True"

lemma Index_Param_Tag_Swap:
  \<open> \<p>\<a>\<r>\<a>\<m> P \<Longrightarrow> \<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> P \<close>
  unfolding Index_Param_Tag_def ..

ML_file \<open>syntax/index_param.ML\<close>

\<phi>processor set_index_param 5000 (premises \<open>\<i>\<n>\<d>\<e>\<x> \<p>\<a>\<r>\<a>\<m> _\<close>) \<open>fn (ctxt,sequent) =>
  Scan.pass (Context.Proof ctxt) Synt_Index_Param.index_term_parser >> (fn term => fn _ =>
      Phi_Sys.set_param term (ctxt, @{thm Index_Param_Tag_Swap} RS sequent))\<close>
*)

section \<open>First-level Abstraction of Instructions\<close>

lemma op_get_aggregate:
  \<open> unwind_aggregate_path_into_logical_form raw_idx idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> valid_index TY idx
\<Longrightarrow> \<phi>Aggregate_Getter idx T U f
\<Longrightarrow> \<p>\<r>\<o>\<c> op_get_aggregate raw_idx TY rv \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] T \<longmapsto> f x \<Ztypecolon> \<v>\<a>\<l> U \<rbrace>\<close>
  unfolding op_get_aggregate_def \<phi>SemType_def subset_iff \<phi>Aggregate_Getter_def
            unwind_aggregate_path_into_logical_form_def
  by (cases rv; simp, rule, simp add: \<phi>expns, rule, simp add: \<phi>Mapping_expn)

lemma op_set_aggregate:
  \<open> unwind_aggregate_path_into_logical_form raw_idx idx
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (y \<Ztypecolon> U) TY2
\<Longrightarrow> Premise eval_aggregate_path (index_type idx TY = TY2 \<or> allow_assigning_different_typ TY idx)
\<Longrightarrow> valid_index TY idx
\<Longrightarrow> \<phi>Aggregate_Mapper idx T T' U' U f
\<Longrightarrow> \<p>\<r>\<o>\<c> op_set_aggregate TY TY2 raw_idx (ru\<^bold>, rv) \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[rv] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[ru] U \<longmapsto> f (\<lambda>_. y) x \<Ztypecolon> \<v>\<a>\<l> T' \<rbrace>\<close>
  unfolding op_set_aggregate_def \<phi>SemType_def subset_iff \<phi>Aggregate_Mapper_def Premise_def
            unwind_aggregate_path_into_logical_form_def
  by (cases rv; cases ru; simp, rule, rule, simp add: \<phi>expns, rule, simp add: \<phi>expns,
      rule, simp add: \<phi>Mapping_expn)

proc op_construct_aggregate:
  input  \<open>Void\<close>
  requires C[unfolded \<phi>Aggregate_Constructor_def, useful]:
            \<open>\<phi>Aggregate_Constructor constructor args TY (x \<Ztypecolon> T)\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  semantic_assert \<open>constructor args \<in> Well_Type TY\<close>
  semantic_return \<open>constructor args \<in> (x \<Ztypecolon> T)\<close>
\<medium_right_bracket> .


section \<open>Syntax Base\<close>

nonterminal "\<phi>_tuple_args_" and "\<phi>_tuple_arg_"

consts \<phi>_Empty_Tuple_sugar :: \<open>(VAL, 'any) \<phi>\<close> ("\<lbrace> \<rbrace>") \<comment> \<open>A syntax sugar to be overloaded\<close>

syntax "_\<phi>Tuple" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("\<lbrace> _ \<rbrace>")
       "_\<phi>tuple_arg"  :: "\<phi>_tuple_arg_ \<Rightarrow> \<phi>_tuple_args_" ("_")
       "_\<phi>tuple_args" :: "\<phi>_tuple_arg_ \<Rightarrow> \<phi>_tuple_args_ \<Rightarrow> \<phi>_tuple_args_" ("_,/ _")

translations
  "_\<phi>Tuple (_\<phi>tuple_args y z)" \<rightleftharpoons> "CONST \<phi>Prod (_\<phi>Tuple (_\<phi>tuple_arg y)) (_\<phi>Tuple z)"


section \<open>IDE Interface\<close>

\<phi>overloads "[]" and "[]="

declare op_get_aggregate[\<phi>overload "[]"]

ML_file \<open>library/generic_element_access.ML\<close>

\<phi>processor aggregate_getter 8990 (\<open>CurrentConstruction programming_mode ?blk ?H ?S\<close>)
\<open> fn s => Parse.position \<^keyword>\<open>[\<close> >> (fn (_, pos) => fn _ =>
    Phi_Generic_Element_Access.gen_access \<^named_theorems>\<open>[]_\<phi>app\<close> (("[",pos), (NONE, pos)) s) \<close>

\<phi>processor aggregate_getter_end 8990 (\<open>CurrentConstruction programming_mode ?blk ?H ?S\<close>)
\<open> fn (ctxt,sequent) => Parse.position \<^keyword>\<open>]\<close> >> (fn (_, pos) => fn _ => (
    if Phi_Delayed_App.is_during_apply ctxt "[" then ()
    else error ("Unbalanced paranthenses and bracks. " ^ Position.here pos) ;
    Phi_Delayed_App.close_parenthesis I (ctxt,sequent)
)) \<close>

\<phi>processor construct_aggregate 8990 (\<open>CurrentConstruction programming_mode ?blk ?H ?S\<close>)
\<open> fn s => Parse.position \<^keyword>\<open>\<lbrace>\<close> -- Scan.option (Parse.short_ident --| \<^keyword>\<open>:\<close>)
>> (fn ((_, pos), arg_name) => fn _ =>
    Phi_Generic_Element_Access.gen_constructor "" (("\<lbrace>",pos), (arg_name, pos)) s) \<close>

\<phi>processor construct_aggregate_end 8990 (\<open>CurrentConstruction programming_mode ?blk ?H ?S\<close>)
\<open> fn (ctxt,sequent) => Parse.position \<^keyword>\<open>\<rbrace>\<close> >> (fn (_, pos) => fn _ => (
    if Phi_Delayed_App.is_during_apply ctxt "\<lbrace>" then ()
    else error ("Unbalanced paranthenses and bracks. " ^ Position.here pos) ;
    Phi_Delayed_App.close_parenthesis I (ctxt,sequent)
)) \<close>

(*
syntax
  "_tuple"      :: "'a \<Rightarrow> tuple_args \<Rightarrow> 'a \<times> 'b"        ("(1'(_,/ _'))")
  "_tuple_arg"  :: "'a \<Rightarrow> tuple_args"                   ("_")
  "_tuple_args" :: "'a \<Rightarrow> tuple_args \<Rightarrow> tuple_args"     ("_,/ _")
  "_pattern"    :: "pttrn \<Rightarrow> patterns \<Rightarrow> pttrn"         ("'(_,/ _')")
  ""            :: "pttrn \<Rightarrow> patterns"                  ("_")
  "_patterns"   :: "pttrn \<Rightarrow> patterns \<Rightarrow> patterns"      ("_,/ _")
  "_unit"       :: pttrn                                ("'(')")
translations
  "(x, y)" \<rightleftharpoons> "CONST Pair x y"
  "_pattern x y" \<rightleftharpoons> "CONST Pair x y"
  "_patterns x y" \<rightleftharpoons> "CONST Pair x y"
  "_tuple x (_tuple_args y z)" \<rightleftharpoons> "_tuple x (_tuple_arg (_tuple y z))"
  "\<lambda>(x, y, zs). b" \<rightleftharpoons> "CONST case_prod (\<lambda>x (y, zs). b)"
  "\<lambda>(x, y). b" \<rightleftharpoons> "CONST case_prod (\<lambda>x y. b)"
  "_abs (CONST Pair x y) t" \<rightharpoonup> "\<lambda>(x, y). t"
  \<comment> \<open>This rule accommodates tuples in \<open>case C \<dots> (x, y) \<dots> \<Rightarrow> \<dots>\<close>:
     The \<open>(x, y)\<close> is parsed as \<open>Pair x y\<close> because it is \<open>logic\<close>,
     not \<open>pttrn\<close>.\<close>
  "\<lambda>(). b" \<rightleftharpoons> "CONST case_unit b"
  "_abs (CONST Unity) t" \<rightharpoonup> "\<lambda>(). t"

*)


end