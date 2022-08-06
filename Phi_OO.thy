theory Phi_OO
  imports NuInstructions
begin

chapter \<open>Object Oriented Programming Model\<close>

section \<open>Semantics & Fictions\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

paragraph \<open>Algebra of Class Dependency\<close>

datatype 'TY class_id = Class (name: string) (parents: \<open>'TY class_id list\<close>) (fields: \<open>'TY list\<close>)
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
      apply (metis not_add_less1 not_less_eq size_list_estimation)
      by (metis Suc_lessD Suc_mono size_list_estimation trans_less_add1) . . .
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
  assume \<open>Class name (x # L) fields = x\<close>
  then have \<open>\<And>S. size_class_id S (Class name (x # L) fields) = size_class_id S x\<close> by simp
  then show False by simp
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
type_synonym ('TY,'VAL) object_heap = \<open>('TY object_ref \<times> field_name \<Rightarrow> 'VAL option)\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) \<phi>OO_res = ('VAL,'TY) \<phi>min_res +
  R_objs :: \<open>('TY,'VAL) object_heap ?\<close>


subsection \<open>Main Stuff of Semantics\<close>

locale \<phi>OO_sem_pre =
  \<phi>min_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult))\<close>
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
            and TYPE'REP  = \<open>TYPE('RES::comm_monoid_mult)\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult)
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
  \<open>infinite {a. object_ref.class a = cls}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. object_ref.class a = cls}\<close>
        and f = \<open>\<lambda>n. object_ref cls n\<close>]
  using inj_def by fastforce


definition Valid_Objs :: "('TY,'VAL) object_heap fine set"
  where "Valid_Objs = Fine ` {h. \<forall>k. h (Nil,k) = None}"

lemma Valid_Objs_1[simp]: \<open>1 \<in> Valid_Objs\<close>
  unfolding Valid_Objs_def one_fun_def one_fine_def by simp



lemma ObjHeap_freshness:
  \<open>finite (dom f) \<Longrightarrow> \<exists>k. f k = 1 \<and> object_ref.class k = cls\<close>
  unfolding dom_def
  by (metis (mono_tags, lifting) finite_subset mem_Collect_eq objref_infinite_cls one_option_def subsetI)

subsection \<open>Fictions\<close>

definition \<open>fiction_objs I = Fiction (\<lambda>x. { 1(R_objs #= Fine y) |y. y \<in> \<I> I x })\<close>
lemma fiction_objs_\<I>:
  "\<I> (fiction_objs I) = (\<lambda>x. { 1(R_objs #= Fine y) |y. y \<in> \<I> I x})"
  unfolding fiction_objs_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def one_fine_def)

definition \<open>share_val_fiction =
      Fiction (\<lambda>m. {f. m = to_share o f})\<close>
lemma share_val_fiction_\<I>:
  \<open>\<I> share_val_fiction = (\<lambda>m. {f. m = to_share o f})\<close>
  unfolding share_val_fiction_def
  by (rule Fiction_inverse, simp add: Fictional_def one_set_def)

definition "share_objs = fiction_objs (fiction.fine share_val_fiction)"

end


locale \<phi>OO_sem =
  \<phi>OO_sem_pre where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES)) itself\<close>
assumes res_valid_objects[simp]: \<open>Resource_Validator R_objs.name = R_objs.inject ` Valid_Objs\<close>
begin

lemma "__res_valid_objects_R_objs_get__":
  \<open> res \<in> Valid_Resource
\<Longrightarrow> R_objs.get res \<in> Valid_Objs\<close>
  unfolding Valid_Resource_def
  apply simp
  subgoal premises prems
    using prems(1)[THEN spec[where x=R_objs.name], simplified res_valid_objects]
    by fastforce .
  

end



fiction_space (in \<phi>OO_sem) \<phi>OO_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> = \<phi>min_fic +
  FIC_OO_share :: share_objs

locale \<phi>OO =
  \<phi>OO_fic where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult))\<close>
      and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
      and TYPE'REP = \<open>TYPE('FIC::{no_inverse,comm_monoid_mult})\<close>
+ \<phi>min where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult)
                  \<times> ('FIC_N \<Rightarrow> 'FIC))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>
begin

lemma R_objs_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    R_objs.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_objs.name = R_objs.inject (Fine m) \<and> m \<in> Valid_Objs)\<close>
  by (subst R_objs.split, simp add: Valid_Resource_def times_fun_def image_iff one_fine_def, blast)

lemma R_objs_valid_split': \<open>NO_MATCH (R_objs.clean res') res \<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow>
    R_objs.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_objs.name = R_objs.inject (Fine m) \<and> m \<in> Valid_Objs)\<close>
  using R_objs_valid_split .

lemma share_objs_implies_value_full:
  \<open> res \<in> \<I> share_objs (FIC_OO_share.get r * Fine (\<lambda>(x, y). (1(ref := 1(field \<mapsto> 1 \<Znrres> v))) x y))
\<Longrightarrow> \<exists>objs. R_objs.get res = Fine (objs * 1((ref,field) \<mapsto> v))\<close>
  apply (clarsimp simp add: share_objs_def fiction_objs_\<I> share_val_fiction_\<I>
            mult_strip_fine_011 fun_eq_iff times_fun sep_disj_fun_def)
  subgoal premises prems for y m a
    apply (rule exI[where x="strip_share o a"])
    apply (insert prems(2,4,5)[THEN spec[where x=ref], THEN spec[where x=field], simplified])
    apply (cases \<open>a (ref, field)\<close>; cases \<open>y (ref, field)\<close>; clarsimp)
    subgoal for aa bb
      apply (insert prems(2,4,5)[THEN spec[where x=aa], THEN spec[where x=bb], simplified])
      by (cases \<open>aa = ref\<close>; simp)
    subgoal for u
      by (cases u; simp) . .


lemma share_objs_implies_value:
  \<open> res \<in> \<I> share_objs (FIC_OO_share.get r * Fine (\<lambda>(x, y). (1(ref := 1(field \<mapsto> n \<Znrres> v))) x y))
\<Longrightarrow> \<exists>objs. R_objs.get res = Fine objs \<and> objs (ref,field) = Some v\<close>
  apply (clarsimp simp add: share_objs_def fiction_objs_\<I> share_val_fiction_\<I>
            mult_strip_fine_011 fun_eq_iff times_fun sep_disj_fun_def)
  subgoal premises prems for y m a
    apply (rule exI[where x=y], simp)
    apply (insert prems(2,4,5)[THEN spec[where x=ref], THEN spec[where x=field], simplified])
    apply (cases \<open>a (ref, field)\<close>; simp)
    apply (metis option.simps(9) strip_share_Share)
    by (metis option.simps(9) sep_disj_share share.exhaust strip_share_Share times_share) .

thm "__res_valid_objects_R_objs_get__"

lemma
  assumes A: \<open>res \<in> \<I> share_objs (FIC_OO_share.get r * Fine (\<lambda>(x, y). (1(ref := 1(field \<mapsto> n \<Znrres> v))) x y))\<close>
  shows share_objs_implies_\<phi>M_get_res_entry:
            \<open>\<phi>M_get_res_entry R_objs.get (ref, field) F res = F v res\<close>
proof -
  note A' = share_objs_implies_value[of res, of r, OF A]
  show ?thesis
    unfolding \<phi>M_get_res_entry_def \<phi>M_get_res_def
    by (insert A', clarsimp)
qed


lemma
  assumes V: \<open>res_r * res \<in> Valid_Resource\<close>
  assumes A: \<open>res \<in> \<I> share_objs (FIC_OO_share.get r * Fine (\<lambda>(x, y). (1(ref := 1(field \<mapsto> n \<Znrres> v))) x y))\<close>
  shows share_objs_implies_\<phi>M_get_res_entry':
            \<open>\<phi>M_get_res_entry R_objs.get (ref, field) F (res_r * res) = F v (res_r * res)\<close>
proof -
  note A' = share_objs_implies_value[of res, of r, OF A]
  show ?thesis
    unfolding \<phi>M_get_res_entry_def \<phi>M_get_res_def
    by (insert A', insert V[THEN "__res_valid_objects_R_objs_get__"],
          clarsimp simp add: R_objs.get_homo_mult Valid_Objs_def
          mult_strip_fine_011 times_fun R_objs.proj_homo_mult
          sep_disj_fun_nonsepable(2)[where x=\<open>(ref, field)\<close>])
qed



end


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

definition \<phi>Object :: \<open>'TY object_ref \<Rightarrow> (field_name \<Rightarrow> 'VAL share option, 'x) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'x) \<phi>\<close>
  where \<open>\<phi>Object obj T x = { FIC_OO_share.mk (Fine (case_prod (1(obj := v)))) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>Object_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Object obj T) \<longleftrightarrow> (\<exists>v. p = FIC_OO_share.mk (Fine (case_prod (1(obj := v)))) \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Object_def \<phi>Type_def by simp

lemma [\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Object obj T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)






section \<open>Instructions\<close>

definition \<phi>M_getV_ref :: \<open>'VAL sem_value \<Rightarrow> ('TY object_ref \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV_ref v F = \<phi>M_getV \<tau>Ref V_ref.dest v F\<close>

(*
definition \<phi>M_obj_allocate :: \<open>'TY class_id \<Rightarrow> ('TY object_ref \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_obj_allocate cls F = \<close>

definition op_obj_new :: \<open>'TY class_id \<Rightarrow> ('VAL,'RES_N,'RES) proc\<close>
  where \<open>op_obj_new cls = \<close> *)

definition op_obj_load_field :: \<open>field_name \<Rightarrow> 'TY \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_obj_load_field field TY v =
    \<phi>M_getV_ref v (\<lambda>ref.
    \<phi>M_get_res_entry R_objs.get (ref,field) (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater> Success (sem_value v)))\<close>

definition op_obj_store_field :: \<open>field_name \<Rightarrow> 'TY \<Rightarrow> ('VAL \<times> 'VAL, unit,'RES_N,'RES) proc'\<close>
  where \<open>op_obj_store_field field TY =
    \<phi>M_caseV (\<lambda>vstore vref.
    \<phi>M_getV_ref vref (\<lambda>ref.
    \<phi>M_getV TY id vstore (\<lambda>store.
    \<phi>M_get_res_entry R_objs.get (ref,field) (\<lambda>v. \<phi>M_assert (v \<in> Well_Type TY))
 \<ggreater> \<phi>M_set_res R_objs.updt (\<lambda>f. f((ref,field) \<mapsto> store))
)))\<close>




lemma (in \<phi>OO) \<phi>M_getV_ref[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F ref \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_ref raw F \<lbrace> X\<heavy_comma> ref \<Ztypecolon> Val raw (Ref cls) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_ref_def by (cases raw, simp, \<phi>reason, simp add: \<phi>expns)





lemma (in \<phi>OO) \<phi>M_get_res_entry_R_objs[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> \<phi>Object ref (\<phi>Field field (n \<Znrres>\<phi> Identity)) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_res_entry R_objs.get (ref, field) F
      \<lbrace> v \<Ztypecolon> \<phi>Object ref (\<phi>Field field (n \<Znrres>\<phi> Identity)) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_alt
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_OO_share.interp_split')
  subgoal premises prems for fic_r res_r res
    apply (subst share_objs_implies_\<phi>M_get_res_entry'[OF \<open>_ \<in> Valid_Resource\<close>, of fic_r, OF \<open>res \<in> _\<close>])
    apply (rule prems(1)[THEN spec[where x="res_r * res"], THEN spec[where x=fic_r], THEN mp])
    apply (simp add: prems \<phi>expns FIC_OO_share.interp_split')
    using prems by blast .


lemma (in \<phi>OO) op_obj_load_field:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_obj_load_field field TY raw \<lbrace>
      v \<Ztypecolon> \<phi>Object ref (\<phi>Field field (\<phi>Share n Identity)) \<heavy_comma> ref \<Ztypecolon> Val raw (Ref cls)
  \<longmapsto> v \<Ztypecolon> \<phi>Object ref (\<phi>Field field (\<phi>Share n Identity)) \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity
\<rbrace>\<close>
  unfolding op_obj_load_field_def Premise_def
  by (\<phi>reason, simp, \<phi>reason)


lemma (in \<phi>OO)
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_set_res R_objs.updt (\<lambda>f. f((ref, field) \<mapsto> u))
         \<lbrace> v \<Ztypecolon> \<phi>Object ref (\<phi>Field field (1 \<Znrres>\<phi> Identity))
  \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> \<phi>Object ref (\<phi>Field field (1 \<Znrres>\<phi> Identity)) \<rbrace>\<close>
  unfolding \<phi>Procedure_alt \<phi>M_set_res_def
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_OO_share.interp_split')
  subgoal premises prems for fic_r res_r res
    apply (insert share_objs_implies_value_full[of res, of fic_r, OF \<open>res \<in> \<I> share_objs _\<close>])
    apply (clarify)
    thm prems


lemma (in \<phi>OO) op_obj_store_field:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_obj_store_field field TY (\<phi>V_pair rawu rawref) \<lbrace>
      v \<Ztypecolon> \<phi>Object ref (\<phi>Field field (\<phi>Share n Identity)) \<heavy_comma> u \<Ztypecolon> Val rawu Identity \<heavy_comma> ref \<Ztypecolon> Val rawref (Ref cls)
  \<longmapsto> u \<Ztypecolon> \<phi>Object ref (\<phi>Field field (\<phi>Share n Identity))
\<rbrace>\<close>
  unfolding op_obj_store_field_def Premise_def
  apply (cases rawref; cases rawu; simp; \<phi>reason, assumption, simp add: \<phi>expns)
    unfolding \<phi>Procedure_alt
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_OO_share.interp_split')
  subgoal premises prems for x1 fic_r res_r res
    apply (subst share_objs_implies_\<phi>M_get_res_entry'[OF \<open>_ \<in> Valid_Resource\<close>, of fic_r, OF \<open>res \<in> _\<close>])
    apply (simp add: prems \<phi>expns )
    thm FIC_OO_share.interp_split'
    using prems 



lemma
  \<open>
 \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_res_entry R_objs.get (ref, field) F \<lbrace>
     FIC_OO_share.mk (Fine (\<lambda>(x, y). (1(ref := 1(field \<mapsto> n \<Znrres> v))) x y))
 \<longmapsto>
\<rbrace>\<close>


  apply (subst ext_func_forall_eq_simp)
thm ext_func_forall_eq_simp
  unfolding \<phi>M_get_res_entry_def \<phi>M_get_res_def \<phi>Procedure_def
  apply (clarsimp simp add: \<phi>expns FIC_OO_share.interp_split' R_objs_valid_split' share_objs_def
            fiction_objs_\<I> mult_strip_fine_011 R_objs.mult_strip_inject_011 share_val_fiction_\<I>
            Valid_Objs_def times_fun)
  

apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' times_fun dom_mult
                        R_mem.mult_in_dom Valid_Mem_def mult_strip_fine_011 mult_strip_fine_001
                        fiction_mem_\<I>'' share_mem_def' times_list_def)
end



end