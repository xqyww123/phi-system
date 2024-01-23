theory PhiSem_Mem_OO
  imports PhiSem_OO_Class_Algebra
begin

chapter \<open>Object Oriented Programming Model\<close>

setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put
                                          (SOME Generic_Variable_Access.store_value_no_clean))\<close>

section \<open>Semantics & Fictions\<close>

subsection \<open>Models\<close>

(*not ready to use*)

subsubsection \<open>Type\<close>

virtual_datatype \<phi>OO_ty =
  T_ref :: unit

debt_axiomatization T_ref :: \<open>unit type_entry\<close>
  where \<phi>OO_ty_ax: \<open>\<phi>OO_ty TY_CONS_OF T_ref\<close>

interpretation \<phi>OO_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_ref using \<phi>OO_ty_ax .

(*does user really need to input the semantic type manually?*)
abbreviation \<open>reference \<equiv> T_ref.mk ()\<close>


subsubsection \<open>Value\<close>

declare [[typedef_overloaded]]

datatype object_ref = object_ref ("class": \<open>class\<close>) ("instance_id": nat) | Nil
hide_const (open) "class" instance_id

lemma object_ref_all:
  \<open>All P \<longleftrightarrow> (\<forall>cls i. P (object_ref cls i)) \<and> P Nil\<close>
  by (metis object_ref.exhaust)

lemma object_ref_ex:
  \<open>Ex P \<longleftrightarrow> (\<exists>cls i. P (object_ref cls i)) \<or> P Nil\<close>
  by (metis object_ref.exhaust)


declare [[typedef_overloaded = false]]


paragraph \<open>Properties\<close>

primrec of_class
  where \<open>of_class cls (object_ref cls' _) \<longleftrightarrow> cls = cls'\<close>
  | \<open>of_class _ Nil \<longleftrightarrow> True\<close>

instantiation object_ref :: zero begin
definition \<open>zero_object_ref = Nil\<close>
instance ..
end


paragraph \<open>The Model\<close>

virtual_datatype \<phi>OO_val =
  V_ref :: \<open>object_ref\<close>

debt_axiomatization V_ref :: \<open>object_ref value_entry\<close>
  where \<phi>OO_val_ax: \<open>\<phi>OO_val VAL_CONS_OF V_ref\<close>

interpretation \<phi>OO_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_ref using \<phi>OO_val_ax .

debt_axiomatization
        WT_ref[simp]: \<open>Well_Type reference = UNIV\<close>
  and   zero_ref[simp]: \<open>Zero reference = Some (V_ref.mk Nil)\<close>
  and   Can_EqCompare_ref[simp]: \<open>Can_EqCompare res (V_ref.mk ref1) (V_ref.mk ref2)\<close>
  and   EqCompare_ref[simp]:     \<open>EqCompare (V_ref.mk ref1) (V_ref.mk ref2) \<longleftrightarrow> ref1 = ref2\<close>



subsubsection \<open>Resource\<close>

type_synonym object_heap = \<open>(object_ref \<Rightarrow> field_name \<Rightarrow> VAL discrete option)\<close>

definition \<open>Valid_Objs = {h::object_heap. h Nil = 1} \<inter> {h. finite (dom1 h)}
       \<inter> {h. (\<forall>cls id. dom (h (object_ref cls id)) \<subseteq> dom (class.fields_of cls) ) }\<close>

lemma In_Valid_Objs[simp]:
  \<open>h \<in> Valid_Objs \<longleftrightarrow> h Nil = 1 \<and> finite (dom1 h) \<and>
     ((\<forall>cls id. dom (h (object_ref cls id)) \<subseteq> dom (class.fields_of cls) ))\<close>
  unfolding Valid_Objs_def by simp

resource_space \<phi>OO =
  Objs :: \<open>Valid_Objs\<close> (partial_map_resource2)
  by (standard; simp)

lemma objref_infinite_cls:
  \<open>infinite {a. a \<noteq> Nil \<and> object_ref.class a = cls}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. a \<noteq> Nil \<and> object_ref.class a = cls}\<close>
        and f = \<open>\<lambda>n. object_ref cls n\<close>]
  using inj_def by fastforce

lemma Sep_Homo_Valid_Objs[simp]:
  \<open>Sep_Homo Valid_Objs\<close>
  unfolding Valid_Objs_def
  apply (rule Sep_Homo_inter, rule Sep_Homo_inter)
  apply (simp add: Sep_Homo_def times_fun)
   apply simp
  apply (rule Sep_Homo_pointwise[where P=\<open>\<lambda>k v.
          case k of object_ref cls i \<Rightarrow> dom v \<subseteq> dom (class.fields_of cls)
                  | _ \<Rightarrow> True\<close>,
      simplified object_ref_all, simplified])
  by (clarsimp simp add: dom_mult one_partial_map[symmetric])
  


(*
lemma Valid_Objs_1[simp]: \<open>1 \<in> Valid_Objs\<close>
  unfolding Valid_Objs_def one_fun_def by (simp add: dom1_def one_fun_def)
*)

lemma obj_map_freshness:
  \<open>finite (dom1 f) \<Longrightarrow> \<exists>k. f k = 1 \<and> k \<noteq> Nil \<and> object_ref.class k = cls\<close>
  unfolding dom1_def
  by (metis (mono_tags, lifting) finite_subset mem_Collect_eq objref_infinite_cls subsetI)



fiction_space \<phi>OO_fic =
  OO_share :: RES.Objs.share_fiction (share_fiction_for_partial_mapping_resource2 RES.Objs) ..

lemma "__case_prod_ref_field__":
  \<open>(\<lambda>(x, y). (1(ref := 1(field \<mapsto> n \<odiv> v))) x y) = 1((ref,field) \<mapsto> n \<odiv> v)\<close>
  unfolding fun_eq_iff by simp


section \<open>\<phi>Types\<close>

subsection \<open>Reference\<close>

(*Do we really need the class annotation here?*)

definition Ref :: \<open>class \<Rightarrow> (VAL, object_ref) \<phi>\<close>
  where \<open>Ref cls ref = ({ V_ref.mk ref } \<s>\<u>\<b>\<j> of_class cls ref)\<close>

lemma \<phi>Ref_expns[\<phi>expns]:
  \<open>v \<in> (ref \<Ztypecolon> Ref cls) \<longleftrightarrow> v = V_ref.mk ref \<and> of_class cls ref\<close>
  unfolding Ref_def \<phi>Type_def by (simp add: \<phi>expns)

lemma \<phi>Ref_inhabited[\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited (ref \<Ztypecolon> Ref cls) \<Longrightarrow> (of_class cls ref \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Ref_zero[\<phi>reason 1000]:
  \<open>Semantic_Zero_Val reference (Ref cls) Nil\<close>
  unfolding Semantic_Zero_Val_def by (simp add: \<phi>expns)

lemma \<phi>Ref_eq[\<phi>reason 1000]:
  \<open>\<phi>Equal (Ref cls) (\<lambda>_ _. True) (=)\<close>
  unfolding \<phi>Equal_def by (simp add: \<phi>expns)

lemma \<phi>Ref_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (ref \<Ztypecolon> Ref cls) reference\<close>
  unfolding \<phi>SemType_def by (simp add: \<phi>expns)


subsection \<open>Object\<close>

paragraph \<open>Fields in A Object\<close>

notation FIC.OO_share.\<phi> ("obj: _" [52] 51)

section \<open>Instructions\<close>

paragraph \<open>Reference Value\<close>

(* definition \<open>\<phi>M_getV_ref v F = \<phi>M_getV reference V_ref.dest v F\<close> *)

paragraph \<open>Allocation\<close>

definition initial_value_of_class
  where \<open>initial_value_of_class cls = map_option (map_discrete (the o Zero)) o class.fields_of cls\<close>

lemma dom_initial_value_of_class:
  \<open>dom (initial_value_of_class cls) = dom (class.fields_of cls)\<close>
  unfolding initial_value_of_class_def dom_def set_eq_iff by simp

definition op_obj_allocate :: \<open>class \<Rightarrow> VAL proc\<close>
  where \<open>op_obj_allocate cls =
      RES.Objs.\<phi>R_allocate_res_entry (\<lambda>ref. ref \<noteq> Nil \<and> object_ref.class ref = cls)
            (initial_value_of_class cls) (\<lambda>ref. Return (\<phi>arg (V_ref.mk ref)))\<close>


paragraph \<open>Load Field\<close>

definition op_obj_load_field :: \<open>field_name \<Rightarrow> TY \<Rightarrow> (VAL,VAL) proc'\<close>
  where \<open>op_obj_load_field field TY v =
    \<phi>M_getV reference V_ref.dest v (\<lambda>ref.
    RES.Objs.\<phi>R_get_res_entry ref field (\<lambda>v.
    \<phi>M_assert (discrete.dest v \<in> Well_Type TY) \<ggreater>
    Return (\<phi>arg (discrete.dest v))))\<close>


paragraph \<open>Store Field\<close>

definition op_obj_store_field :: \<open>field_name \<Rightarrow> TY \<Rightarrow> (VAL \<times> VAL, unit) proc'\<close>
  where \<open>op_obj_store_field field TY =
    \<phi>M_caseV (\<lambda>vstore vref.
    \<phi>M_getV TY id vstore (\<lambda>store.
    \<phi>M_getV reference V_ref.dest vref (\<lambda>ref.
    RES.Objs.\<phi>R_get_res_entry ref field (\<lambda>v. \<phi>M_assert (discrete.dest v \<in> Well_Type TY))
 \<ggreater> RES.Objs.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some (discrete store)) field) ref)
)))\<close>

paragraph \<open>Dispose\<close>

definition op_obj_dispose :: \<open>class \<Rightarrow> (VAL, unit) proc'\<close>
  where \<open>op_obj_dispose cls vref =
    \<phi>M_getV reference V_ref.dest vref (\<lambda>ref.
    RES.Objs.\<phi>R_get_res (\<lambda>m.
    \<phi>M_assert ((ref \<in> dom1 m \<or> class.fields_of cls = 1) \<and> object_ref.class ref = cls))
 \<ggreater> RES.Objs.\<phi>R_set_res (\<lambda>f. f(ref := 1))
)\<close>


section \<open>Specification of Instructions\<close>

paragraph \<open>Reference Value\<close>

lemma \<phi>M_getV_ref:
  \<open> (of_class cls ref \<Longrightarrow> \<p>\<r>\<o>\<c> F ref \<lbrace> X \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E)
\<Longrightarrow> \<p>\<r>\<o>\<c> \<phi>M_getV reference V_ref.dest raw F \<lbrace> X\<heavy_comma> ref \<Ztypecolon> Val raw (Ref cls) \<longmapsto> Y \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E\<close>
  by (cases raw; simp; rule; simp add: \<phi>expns)


paragraph \<open>Allocation\<close>

lemma op_obj_allocate:
  \<open>\<p>\<r>\<o>\<c> op_obj_allocate cls
      \<lbrace> Void \<longmapsto> \<lambda>ret. \<exists>*ref. to_share o initial_value_of_class cls \<Ztypecolon> obj: ref \<^bold>\<rightarrow> Itself\<heavy_comma> ref \<Ztypecolon> Val ret (Ref cls) \<rbrace>\<close>
  unfolding \<phi>Procedure_Hybrid_DL op_obj_allocate_def
  apply (clarsimp simp add: \<phi>expns del: subsetI)
  apply (rule RES.Objs.\<phi>R_allocate_res_entry)
  apply (clarsimp)
  using obj_map_freshness apply blast
  
  apply (clarsimp simp add: one_fun_def dom_initial_value_of_class)

  prefer 2 apply assumption

  apply (simp add: \<phi>expns Return_def det_lift_def del: set_mult_expn)
  subgoal premises prems for r res k res' proof -
    have t: \<open>of_class cls k\<close>
      by (metis object_ref.collapse of_class.simps(1) prems(3))
    show ?thesis
      using t FIC.OO_share.expand[where x=\<open>1(k := initial_value_of_class cls)\<close>, simplified] prems
      using FIC.OO_share.sep_disj_fiction by fastforce
  qed .

paragraph \<open>Load Field\<close>

lemma op_obj_load_field_raw_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_obj_load_field field TY raw \<lbrace>
      discrete v \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> n \<odiv> \<coercion> Itself \<heavy_comma> ref \<Ztypecolon> \<v>\<a>\<l>[raw] (Ref cls)
  \<longmapsto> discrete v \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> n \<odiv> \<coercion> Itself \<heavy_comma> \<v>\<a>\<l> v \<Ztypecolon> Itself
\<rbrace>\<close>
  unfolding op_obj_load_field_def Premise_def
  by (rule \<phi>M_getV_ref, rule, rule \<phi>SEQ, rule \<phi>M_assert, simp, rule, simp add: Itself_expn)
   
proc (nodef) op_obj_load_field:
  requires A: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  input  \<open>x \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> n \<odiv> \<coercion> T \<heavy_comma> ref \<Ztypecolon> Val raw (Ref cls)\<close>
  output \<open>x \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> n \<odiv> \<coercion> T \<heavy_comma> \<v>\<a>\<l> x \<Ztypecolon> T\<close>
\<medium_left_bracket> \<open>obj: _\<close> to Itself \<exists>v
  have [simp]: \<open>v \<in> Well_Type TY\<close> using A[unfolded \<phi>SemType_def subset_iff] \<phi> by blast
  ;; $ref op_obj_load_field_raw[where TY=TY]
\<medium_right_bracket> certified by (simp add: Discrete_expns the_\<phi>lemmata) .
  

paragraph \<open>Store Field\<close>

lemma op_obj_store_field_raw_\<phi>app:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> v \<in> Well_Type TY
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> u \<in> Well_Type TY
\<Longrightarrow> \<p>\<r>\<o>\<c> op_obj_store_field field TY (\<phi>V_pair rawu rawref) \<lbrace>
      discrete v \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> \<coercion> Itself \<heavy_comma> ref \<Ztypecolon> Val rawref (Ref cls)\<heavy_comma> u \<Ztypecolon> Val rawu Itself
  \<longmapsto> discrete u \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> \<coercion> Itself
\<rbrace>\<close>
  unfolding op_obj_store_field_def Premise_def
  apply (cases rawref; cases rawu; simp, rule, rule, simp add: Itself_expn Premise_def,
          rule \<phi>M_getV_ref, rule, rule, rule \<phi>M_assert, simp, simp add: Itself_expn)
  apply (rule FIC.OO_share.\<phi>R_set_res[where P="\<lambda>m. field \<in> dom (m ref)"])
   apply (cases ref; clarsimp simp add: map_fun_at_def dom1_def)
  apply (smt (verit, del_insts) Collect_cong dom_1 dom_eq_empty_conv insert_dom option.distinct(1) subsetD domI)
  using RES.Objs.raw_unit_assertion_implies by blast


proc (nodef) op_obj_store_field:
  requires A: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  requires B: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  input  \<open>x \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> \<coercion> T \<heavy_comma> \<v>\<a>\<l> ref \<Ztypecolon> Ref cls \<heavy_comma> \<v>\<a>\<l> y \<Ztypecolon> U\<close>
  output \<open>y \<Ztypecolon> obj: ref \<^bold>\<rightarrow> field \<^bold>\<rightarrow> \<coercion> U\<close>
  \<medium_left_bracket> to Itself \<exists>u
    \<open>obj: _\<close> to Itself \<exists>v
    op_obj_store_field_raw[where TY=TY]
      certified using A[unfolded \<phi>SemType_def subset_iff] \<phi> by blast ;;
      certified using B[unfolded \<phi>SemType_def subset_iff] \<phi> by blast
  \<medium_right_bracket> certified by (simp add: Discrete_expns the_\<phi>lemmata) .


paragraph \<open>Dispose\<close>

lemma op_obj_dispose:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> ref \<noteq> Nil
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> dom fields = dom (class.fields_of cls)
\<Longrightarrow> \<p>\<r>\<o>\<c> op_obj_dispose cls rawv
    \<lbrace> to_share o fields \<Ztypecolon> obj: ref \<^bold>\<rightarrow> Itself \<heavy_comma> ref \<Ztypecolon> Val rawv (Ref cls) \<longmapsto> \<lambda>ret. Void \<rbrace>\<close>
  unfolding op_obj_dispose_def Premise_def
  apply (rule \<phi>M_getV_ref)
  apply (rule \<phi>SEQ[where B=\<open>\<lambda>_. to_share \<circ> fields \<Ztypecolon> obj: ref \<^bold>\<rightarrow> Itself\<close>])
  apply (clarsimp simp add: \<phi>expns zero_set_def \<phi>Procedure_Hybrid_DL del: subsetI)
  apply (rule RES.Objs.\<phi>R_get_res, simp, simp add: dom1_def)
  subgoal premises prems for r res proof -
    have t1: \<open>object_ref.class ref = cls\<close>
      by (metis object_ref.collapse of_class.simps(1) prems(1) prems(3))
    have t3: \<open>fields = Map.empty \<Longrightarrow> class.fields_of cls = Map.empty\<close> 
      subgoal premises prem proof -
        have \<open>dom fields = {}\<close> by (simp add: prem)
        then have \<open>dom (class.fields_of cls) = {}\<close> using prems(2) by simp
        then show ?thesis by fastforce
      qed .
    have t4: \<open>r ## FIC.OO_share.mk (1(ref := to_share \<circ> fields))\<close>
      using prems(6) by blast
    have t2: \<open>RES.Objs.get res ref = 1 \<Longrightarrow> class.fields_of cls = 1\<close>
      unfolding one_fun_def one_option_def
      apply (cases \<open>fields = Map.empty\<close>)
      using t3 apply blast
      using FIC.OO_share.partial_implies[where x=\<open>1(ref := fields)\<close> and n=1, simplified,
            OF \<open>r \<in> FIC.SPACE\<close>, OF t4, OF \<open>\<s>\<t>\<a>\<t>\<e> res \<i>\<s> _\<close>]
            discrete_partial_map_subsumption_L2
      by (metis domIff map_le_def)
    show ?thesis by (simp add: t1 t2 prems Return_def det_lift_def)
  qed
  apply (rule FIC.OO_share.\<phi>R_dispose_res[where P=\<open>\<lambda>_. True\<close>])
  apply (clarsimp simp add: one_fun_def)
  apply (cases ref; simp)
  using RES.Objs.get_res_Valid[simplified Valid_Objs_def, simplified]
    RES.Objs.raw_unit_assertion_implies'[where f=fields]
  by (metis (no_types, lifting) map_le_implies_dom_le set_eq_subset)


setup \<open>Context.theory_map (Generic_Variable_Access.Process_of_Argument.put NONE)\<close>

end
