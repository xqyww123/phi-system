theory Phi_OO
  imports NuInstructions Phi_Min
begin

chapter \<open>Object Oriented Programming Model\<close>

section \<open>Semantics & Fictions\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

paragraph \<open>Algebra of Class Dependency\<close>

datatype 'TY class_id = Class (name: string) (parents: \<open>'TY class_id list\<close>) (fields: \<open>string \<rightharpoonup> 'TY\<close>)
hide_const (open) name parents fields

text \<open>Name of a class is not its identity but the name plus parents.
  It simplifies the model by ensuring two identical classes have identical parents.\<close>

fun parents_of_with_self
  where \<open>parents_of_with_self (Class name parents fields) =
            insert (Class name parents fields) (\<Union> (parents_of_with_self ` set parents))\<close>

instantiation class_id :: (type) order begin

definition \<open>less_eq_class_id C1 C2 \<longleftrightarrow> C2 \<in> parents_of_with_self C1\<close>
definition \<open>less_class_id (C1::'a class_id) C2 \<longleftrightarrow> C1 \<le> C2 \<and> C1 \<noteq> C2\<close>

instance proof
  fix x y z :: \<open>'a class_id\<close>

  have \<open>\<And>x y S. x \<in> parents_of_with_self y \<Longrightarrow> x \<noteq> y \<Longrightarrow> size_class_id S x < size_class_id S y\<close>
  subgoal for x y S
  apply (induct y arbitrary: x)
  subgoal for name parents fields x
    apply clarsimp
    subgoal for z
      apply (cases \<open>x = z\<close>)
      apply (metis class_id.collapse class_id.size_gen not_less_eq order_refl size_list_estimation' verit_comp_simplify1(3))
      by (metis class_id.exhaust class_id.size_gen less_Suc_eq size_list_estimation) . . .
  then have t1: \<open>\<And>x y. y \<in> parents_of_with_self x \<and> x \<in> parents_of_with_self y \<Longrightarrow> x = y\<close>
    by (metis order_less_asym)
  then  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    apply (simp_all add: less_eq_class_id_def less_class_id_def)
    by blast

  show \<open> x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_class_id_def less_class_id_def t1)

  show \<open>x \<le> x\<close>
    by (cases x; simp add: less_eq_class_id_def less_class_id_def)

  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    unfolding less_eq_class_id_def less_class_id_def
    by (induct x, auto)
qed
end

lemma [simp]: \<open>x \<in> parents_of_with_self x\<close>
  by (cases x, simp)

lemma [simp]: \<open>Class name (x # L) fields \<noteq> x\<close>
proof
  assume A: \<open>Class name (x # L) fields = x\<close>
  then have t: \<open>\<And>S. size_class_id S (Class name (x # L) fields) = size_class_id S x\<close> by simp
  then show False
    by (metis A add_Suc_right class_id.size(2) list.set_intros(1) not_add_less1 not_less_eq size_list_estimation)
qed

lemma prop_subclass_1[intro]: \<open>Class name (x#L) fields < x\<close>
  unfolding less_class_id_def less_eq_class_id_def by simp

lemma subclass_1[intro]: \<open>Class name (x#L) fields \<le> x\<close>
  unfolding less_class_id_def less_eq_class_id_def by simp

lemma subclass_0[intro]: \<open>x \<le> x\<close> for x :: \<open>'a class_id\<close> by simp

(* TODO!
 lemma [intro]: \<open>Class name L \<le> x \<Longrightarrow> Class name (y#L) \<le> x\<close>
  unfolding less_class_id_def less_eq_class_id_def apply simp*)


paragraph \<open>Main Stuff\<close>

virtual_datatype \<phi>OO_ty = \<phi>min_ty +
  T_ref :: unit

context \<phi>OO_ty begin
abbreviation \<open>\<tau>Ref \<equiv> T_ref.mk ()\<close>
end


subsubsection \<open>Value\<close>

datatype 'TY object_ref = object_ref ("class": \<open>'TY class_id\<close>) ("nonce": nat) | Nil
hide_const (open) "class" nonce

primrec of_class
  where \<open>of_class cls (object_ref cls' _) \<longleftrightarrow> cls = cls'\<close>
     | \<open>of_class _ Nil \<longleftrightarrow> True\<close>

virtual_datatype 'TY \<phi>OO_val :: "nonsepable_semigroup" = 'TY \<phi>min_val +
  V_ref :: \<open>'TY object_ref\<close>


subsubsection \<open>Resource\<close>

type_synonym field_name = string
type_synonym ('TY,'VAL) object_heap = \<open>('TY object_ref \<Rightarrow> field_name \<Rightarrow> 'VAL option)\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) \<phi>OO_res = ('VAL,'TY) \<phi>min_res +
  R_objs :: \<open>('TY,'VAL) object_heap ?\<close>


subsection \<open>Main Stuff of Semantics\<close>

locale \<phi>OO_sem_pre =
  \<phi>min_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult}))\<close>
+ \<phi>OO_ty where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ \<phi>OO_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ \<phi>OO_res where TYPE'VAL  = \<open>TYPE('VAL)\<close>
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('RES_N)\<close>
            and TYPE'REP  = \<open>TYPE('RES::{no_inverse,comm_monoid_mult})\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult})
            ) itself\<close>
assumes WT_ref[simp]: \<open>Well_Type \<tau>Ref = UNIV\<close>
  and   zero_ref[simp]: \<open>Zero \<tau>Ref = V_ref.mk Nil\<close>
  and   type_measure_ref[simp]:  \<open>type_measure \<tau>Ref = 1\<close>
  and   Can_EqCompare_ref[simp]: \<open>Can_EqCompare res (V_ref.mk ref1) (V_ref.mk ref2)\<close>
  and   EqCompare_ref[simp]:     \<open>EqCompare (V_ref.mk ref1) (V_ref.mk ref2) \<longleftrightarrow> ref1 = ref2\<close>
begin

lemma Valid_Type_Ref[simp]:
  \<open>Valid_Type \<tau>Ref\<close>
  unfolding Inhabited_def by simp

lemma objref_infinite_cls:
  \<open>infinite {a. a \<noteq> Nil \<and> object_ref.class a = cls}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. a \<noteq> Nil \<and> object_ref.class a = cls}\<close>
        and f = \<open>\<lambda>n. object_ref cls n\<close>]
  using inj_def by fastforce


definition Valid_Objs :: "('TY,'VAL) object_heap set"
  where "Valid_Objs =
      {h. h Nil = 1 \<and> finite (dom1 h)
       \<and> (\<forall>cls nonce. dom (h (object_ref cls nonce)) = {} \<or>
                      dom (h (object_ref cls nonce)) = dom (class_id.fields cls) ) }"

lemma Valid_Objs_1[simp]: \<open>1 \<in> Valid_Objs\<close>
  unfolding Valid_Objs_def one_fun_def one_fine_def by (simp add: dom1_def one_fun_def)

lemma R_Objs_freshness:
  \<open>finite (dom1 f) \<Longrightarrow> \<exists>k. f k = 1 \<and> k \<noteq> Nil \<and> object_ref.class k = cls\<close>
  unfolding dom1_def
  by (metis (mono_tags, lifting) finite_subset mem_Collect_eq objref_infinite_cls subsetI)

end


locale \<phi>OO_sem =
  \<phi>OO_sem_pre where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult}))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES)) itself\<close>
assumes Resource_Validator_objs: \<open>Resource_Validator R_objs.name = R_objs.inject ` Fine ` Valid_Objs\<close>
begin

sublocale R_objs: partial_map_resource2 Valid_Objs R_objs Resource_Validator
  by (standard, simp_all add: Resource_Validator_objs)

definition initial_value_of_class
  where \<open>initial_value_of_class cls = map_option Zero o class_id.fields cls\<close>

lemma dom_initial_value_of_class:
  \<open>dom (initial_value_of_class cls) = dom (class_id.fields cls)\<close>
  unfolding initial_value_of_class_def dom_def set_eq_iff by simp

end

fiction_space (in \<phi>OO_sem) \<phi>OO_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> = \<phi>min_fic +
  FIC_OO_share :: R_objs.share_fiction

lemma "__case_prod_ref_field__":
  \<open>(\<lambda>(x, y). (1(ref := 1(field \<mapsto> n \<Znrres> v))) x y) = 1((ref,field) \<mapsto> n \<Znrres> v)\<close>
  unfolding fun_eq_iff pair_forall by simp



locale \<phi>OO =
  \<phi>OO_fic where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult}))\<close>
      and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
      and TYPE'REP = \<open>TYPE('FIC::{no_inverse,comm_monoid_mult})\<close>
+ \<phi>min where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult})
                  \<times> ('FIC_N \<Rightarrow> 'FIC))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>



section \<open>\<phi>Types\<close>

subsection \<open>Reference\<close>

context \<phi>OO_sem begin

definition Ref :: \<open>'TY class_id \<Rightarrow> ('VAL, 'TY object_ref) \<phi>\<close>
  where \<open>Ref cls ref = ({ V_ref.mk ref } \<^bold>s\<^bold>u\<^bold>b\<^bold>j of_class cls ref)\<close>

lemma \<phi>Ref_expns[\<phi>expns]:
  \<open>v \<in> (ref \<Ztypecolon> Ref cls) \<longleftrightarrow> v = V_ref.mk ref \<and> of_class cls ref\<close>
  unfolding Ref_def \<phi>Type_def by (simp add: \<phi>expns)

lemma \<phi>Ref_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (ref \<Ztypecolon> Ref cls) \<Longrightarrow> (of_class cls ref \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Ref_zero[\<phi>reason 1000]:
  \<open>\<phi>Zero \<tau>Ref (Ref cls) Nil\<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Ref_eq[\<phi>reason 1000]:
  \<open>\<phi>Equal (Ref cls) (\<lambda>_ _. True) (=)\<close>
  unfolding \<phi>Equal_def by (simp add: \<phi>expns)

lemma \<phi>Ref_semty[\<phi>reason 1000]:
  \<open>\<phi>SemType (ref \<Ztypecolon> Ref cls) \<tau>Ref\<close>
  unfolding \<phi>SemType_def by (simp add: \<phi>expns)

end

subsection \<open>Field\<close>

definition \<phi>Field :: \<open>field_name \<Rightarrow> ('v, 'x) \<phi> \<Rightarrow> (field_name \<Rightarrow> 'v option, 'x) \<phi>\<close>
  where \<open>\<phi>Field field T x = { 1(field \<mapsto> v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>Field_expns[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Field field T) \<longleftrightarrow> (\<exists>v. p = 1(field \<mapsto> v) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Field_def \<phi>Type_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Field field T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

subsection \<open>Object\<close>

context \<phi>OO begin

paragraph \<open>Fields in A Object\<close>

definition \<phi>InObj :: \<open>'TY object_ref \<Rightarrow> (field_name \<Rightarrow> 'VAL share option, 'x) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'x) \<phi>\<close>
  where \<open>\<phi>InObj obj T x = { FIC_OO_share.mk (Fine (1(obj := v))) |v. v \<in> (x \<Ztypecolon> T) \<and> obj \<noteq> Nil }\<close>

lemma \<phi>InObj_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>InObj obj T) \<longleftrightarrow> (\<exists>v. p = FIC_OO_share.mk (Fine (1(obj := v))) \<and> v \<in> (x \<Ztypecolon> T) \<and> obj \<noteq> Nil)\<close>
  unfolding \<phi>InObj_def \<phi>Type_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>InObj obj T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

paragraph \<open>A Whole Object\<close>

definition \<phi>RawObject :: \<open>'TY object_ref \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, field_name \<Rightarrow> 'VAL share option) \<phi>\<close>
  where \<open>\<phi>RawObject ref obj = { FIC_OO_share.mk (Fine (1(ref := obj))) }\<close>

lemma \<phi>RawObject_expn[\<phi>expns]:
  \<open>p \<in> (obj \<Ztypecolon> \<phi>RawObject ref) \<longleftrightarrow> p = FIC_OO_share.mk (Fine (1(ref := obj)))\<close>
  unfolding \<phi>RawObject_def \<phi>Type_def by simp

lemma \<phi>RawObject_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (obj \<Ztypecolon> \<phi>RawObject ref) \<Longrightarrow> C \<Longrightarrow> C\<close> .

end

section \<open>Instructions\<close>

paragraph \<open>Reference Value\<close>

definition (in \<phi>OO_sem) \<phi>M_getV_ref :: \<open>'VAL sem_value \<Rightarrow> ('TY object_ref \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV_ref v F = \<phi>M_getV \<tau>Ref V_ref.dest v F\<close>

lemma (in \<phi>OO) \<phi>M_getV_ref[\<phi>reason!]:
  \<open> (of_class cls ref \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F ref \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_ref raw F \<lbrace> X\<heavy_comma> ref \<Ztypecolon> Val raw (Ref cls) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_ref_def by (cases raw, simp, \<phi>reason, simp add: \<phi>expns)


paragraph \<open>Allocation\<close>

definition (in \<phi>OO_sem) op_obj_allocate :: \<open>'TY class_id \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>op_obj_allocate cls =
      R_objs.\<phi>R_allocate_res_entry (\<lambda>ref. ref \<noteq> Nil \<and> object_ref.class ref = cls)
            (initial_value_of_class cls) (\<lambda>ref. Success (sem_value (V_ref.mk ref)))\<close>

lemma (in \<phi>OO) op_obj_allocate:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_obj_allocate cls
      \<lbrace> Void \<longmapsto> \<lambda>ret. \<exists>*ref. to_share o initial_value_of_class cls \<Ztypecolon> \<phi>RawObject ref\<heavy_comma> ref \<Ztypecolon> Val ret (Ref cls) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec op_obj_allocate_def
  apply (clarsimp simp add: \<phi>expns FIC_OO_share.interp_split')
  apply (rule R_objs.\<phi>R_allocate_res_entry)
  apply (clarsimp simp add: Valid_Objs_def)
  using R_Objs_freshness apply blast
    apply (clarsimp simp add: Valid_Objs_def one_fun_def dom_initial_value_of_class)
  prefer 2 apply assumption
  apply (simp add: \<phi>expns)
  subgoal for r res k res'
    by (cases k; simp add: R_objs.share_fiction_expn_full') .



paragraph \<open>Load Field\<close>

definition (in \<phi>OO_sem) op_obj_load_field :: \<open>field_name \<Rightarrow> 'TY \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_obj_load_field field TY v =
    \<phi>M_getV_ref v (\<lambda>ref.
    R_objs.\<phi>R_get_res_entry ref field (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater> Success (sem_value v)))\<close>

lemma (in \<phi>OO) \<phi>M_get_res_entry_R_objs[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (n \<Znrres>\<phi> Identity)) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_objs.\<phi>R_get_res_entry ref field F
      \<lbrace> v \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (n \<Znrres>\<phi> Identity)) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def)
  apply (rule R_objs.\<phi>R_get_res_entry[where v=v])
   apply (simp add: FIC_OO_share.interp_split')
  by blast

lemma (in \<phi>OO) op_obj_load_field:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_obj_load_field field TY raw \<lbrace>
      v \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (\<phi>Share n Identity)) \<heavy_comma> ref \<Ztypecolon> Val raw (Ref cls)
  \<longmapsto> v \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (\<phi>Share n Identity)) \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity
\<rbrace>\<close>
  unfolding op_obj_load_field_def Premise_def
  by (\<phi>reason, assumption, \<phi>reason)


paragraph \<open>Store Field\<close>

definition (in \<phi>OO_sem) op_obj_store_field :: \<open>field_name \<Rightarrow> 'TY \<Rightarrow> ('VAL \<times> 'VAL, unit,'RES_N,'RES) proc'\<close>
  where \<open>op_obj_store_field field TY =
    \<phi>M_caseV (\<lambda>vstore vref.
    \<phi>M_getV_ref vref (\<lambda>ref.
    \<phi>M_getV TY id vstore (\<lambda>store.
    R_objs.\<phi>R_get_res_entry ref field (\<lambda>v. \<phi>M_assert (v \<in> Well_Type TY))
 \<ggreater> R_objs.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some store) field) ref)
)))\<close>

lemma (in \<phi>OO) "\<phi>R_set_res_objs"[\<phi>reason!]:
  \<open> field \<in> dom (class_id.fields (object_ref.class ref))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_objs.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some u) field) ref)
         \<lbrace> v \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (1 \<Znrres>\<phi> Identity))
  \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (1 \<Znrres>\<phi> Identity)) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_OO_share.interp_split'
          R_objs.share_fiction_expn_full)
  apply (rule R_objs.\<phi>R_set_res[where P="\<lambda>m. field \<in> dom (m ref)"])
  apply (cases ref; clarsimp simp add: Valid_Objs_def map_fun_at_def dom1_def)
  apply (smt (verit, del_insts) Collect_cong dom_1 dom_eq_empty_conv insert_dom option.distinct(1))
  using R_objs.raw_unit_assertion_implies apply blast
  by assumption

lemma (in \<phi>OO) op_obj_store_field:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e field \<in> dom (class_id.fields (object_ref.class ref))
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_obj_store_field field TY (\<phi>V_pair rawu rawref) \<lbrace>
      v \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (\<phi>Share 1 Identity)) \<heavy_comma> u \<Ztypecolon> Val rawu Identity \<heavy_comma> ref \<Ztypecolon> Val rawref (Ref cls)
  \<longmapsto> u \<Ztypecolon> \<phi>InObj ref (\<phi>Field field (\<phi>Share 1 Identity))
\<rbrace>\<close>
  unfolding op_obj_store_field_def Premise_def
  by (cases rawref; cases rawu; simp; \<phi>reason, assumption, simp add: \<phi>expns, \<phi>reason, assumption)

paragraph \<open>Allocation\<close>

definition (in \<phi>OO_sem) op_obj_dispose :: \<open>'TY class_id \<Rightarrow> ('VAL, unit,'RES_N,'RES) proc'\<close>
  where \<open>op_obj_dispose cls vref =
    \<phi>M_getV_ref vref (\<lambda>ref.
    R_objs.\<phi>R_get_res (\<lambda>m. \<phi>M_assert ((ref \<in> dom1 m \<or> class_id.fields cls = 1) \<and> object_ref.class ref = cls))
 \<ggreater> R_objs.\<phi>R_set_res (\<lambda>f. f(ref := 1))
)\<close>

lemma (in \<phi>OO) op_obj_dispose:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ref \<noteq> Nil
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e dom fields = dom (class_id.fields cls)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_obj_dispose cls rawv \<lbrace>
      to_share o fields \<Ztypecolon> \<phi>RawObject ref \<heavy_comma> ref \<Ztypecolon> Val rawv (Ref cls)
  \<longmapsto> Void
\<rbrace>\<close>
  unfolding op_obj_dispose_def Premise_def
  apply (rule \<phi>M_getV_ref)
  apply (rule \<phi>SEQ[where B=\<open>\<lambda>_. to_share \<circ> fields \<Ztypecolon> \<phi>RawObject ref\<close>])
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_OO_share.interp_split'
          R_objs.share_fiction_expn_full')
   apply (rule R_objs.\<phi>R_get_res, simp, simp add: dom1_def)
  subgoal premises prems for r res proof -
    have t1: \<open>object_ref.class ref = cls\<close>
      by (metis object_ref.collapse of_class.simps(1) prems(1) prems(3))
    have t2: \<open>!!(R_objs.get res) ref = 1 \<longrightarrow> class_id.fields cls = 1\<close>
      unfolding one_fun_def one_option_def
      using R_objs.raw_unit_assertion_implies'[unfolded map_le_def, OF \<open>res \<in> _\<close>]
      by (metis domIff prems(2))
    show ?thesis by (simp add: t1 t2 prems)
  qed
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_OO_share.interp_split'
          R_objs.share_fiction_expn_full')
  apply (rule R_objs.\<phi>R_dispose_res[where P=\<open>\<lambda>_. True\<close> and any=fields])
     apply (clarsimp simp add: Valid_Objs_def one_fun_def)
  apply (cases ref; simp)
  using R_objs.get_res_Valid[simplified Valid_Objs_def, simplified]
    R_objs.raw_unit_assertion_implies'[where f=fields]
  apply (smt (z3) dom_eq_empty_conv empty_iff map_le_antisym map_le_def)
  ..  


end