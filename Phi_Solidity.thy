theory Phi_Solidity
  imports Phi_OO Map_of_Tree
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype solidity_ty = \<phi>OO_ty +
  T_LedgeRef   :: unit
  T_Address    :: unit

context solidity_ty begin
abbreviation \<open>\<tau>LedgeRef \<equiv> T_LedgeRef.mk ()\<close>
abbreviation \<open>\<tau>Address  \<equiv> T_Address.mk  ()\<close>
end

subsubsection \<open>Value\<close>

definition "class_user = Class [] [] 1"

datatype 'VAL storage_key = SP_field field_name | SP_map_key 'VAL | SP_array_ind nat
type_synonym 'VAL storage_path = \<open>'VAL storage_key list\<close>
type_synonym address = \<open>unit object_ref\<close>
  \<comment> \<open>The ledge doesn't need to records the type of fields, so the type parameter of object_ref is unit.
      It the class of an instance_ref is \<^term>\<open>class_user\<close>, it is an user address.\<close>
datatype 'VAL ledge_ref = ledge_ref ("instance": address) (path: \<open>'VAL storage_path\<close>)
hide_const (open) "instance" path

paragraph \<open>Properties\<close>

instantiation ledge_ref :: (type) zero begin
definition \<open>zero_ledge_ref = ledge_ref Nil []\<close>
instance ..
end

paragraph \<open>The Model\<close>

virtual_datatype 'TY solidity_val = 'TY \<phi>OO_val +
  V_LedgeRef   :: \<open>'self ledge_ref\<close>
  V_Address    :: address

subsubsection \<open>Resource\<close>

type_synonym 'VAL ledge = \<open>(address \<Rightarrow> 'VAL storage_path \<Rightarrow> 'VAL option)\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) solidity_res = ('VAL,'TY) \<phi>min_res +
  R_ledge :: \<open>'VAL ledge ?\<close>


subsection \<open>Semantics\<close>

locale solidity_sem =
  \<phi>OO_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult}))\<close>
+ solidity_ty where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ solidity_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ solidity_res where TYPE'VAL  = \<open>TYPE('VAL)\<close>
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('RES_N)\<close>
            and TYPE'REP  = \<open>TYPE('RES::{no_inverse,comm_monoid_mult})\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult})
            ) itself\<close>
assumes WT_LedgeRef[simp]: \<open>Well_Type \<tau>LedgeRef = UNIV\<close>
  and   WT_Address [simp]: \<open>Well_Type \<tau>Address  = UNIV\<close>
  and   zero_LedgeRef[simp]: \<open>Zero \<tau>LedgeRef = V_LedgeRef.mk (ledge_ref Nil [])\<close>
  and   zero_Address[simp]:  \<open>Zero \<tau>Address  = V_Address.mk Nil\<close>
  and   Can_EqCompare_LedgeRef[simp]: \<open>Can_EqCompare res (V_LedgeRef.mk lref1) (V_LedgeRef.mk lref2)\<close>
  and   Can_EqCompare_Address[simp]:  \<open>Can_EqCompare res (V_Address.mk addr1)  (V_Address.mk addr2)\<close>
  and   EqCompare_LedgeRef[simp]:     \<open>EqCompare (V_LedgeRef.mk lref1) (V_LedgeRef.mk lref2) \<longleftrightarrow> lref1 = lref2\<close>
  and   EqCompare_Address[simp]:      \<open>EqCompare (V_Address.mk addr1)  (V_Address.mk addr2)  \<longleftrightarrow> addr1 = addr2\<close>
  and   Resource_Validator_Ledge': \<open>Resource_Validator R_ledge.name = R_ledge.inject ` Fine ` {h. h Nil = 1 \<and> finite (dom1 h) }\<close>
begin

lemma Valid_Type_LedgeRef[simp]:
  \<open>Valid_Type \<tau>LedgeRef\<close>
  unfolding Inhabited_def by simp

lemma Valid_Type_Address[simp]:
  \<open>Valid_Type \<tau>Address\<close>
  unfolding Inhabited_def by simp

definition Valid_Ledge :: "'VAL ledge set"
  where "Valid_Ledge = {h. h Nil = 1 \<and> finite (dom1 h) }"

lemma Valid_Ledge_1[simp]: \<open>1 \<in> Valid_Ledge\<close>
  unfolding Valid_Ledge_def one_fun_def one_fine_def by (simp add: dom1_def one_fun_def)

lemma Resource_Validator_Ledge[simp]:
  \<open>Resource_Validator R_ledge.name = R_ledge.inject ` Fine ` Valid_Ledge\<close>
  unfolding Valid_Ledge_def Resource_Validator_Ledge' ..

sublocale R_ledge: partial_map_resource2 Valid_Ledge R_ledge Resource_Validator
  by (standard, simp_all add: Resource_Validator_objs)

end


subsection \<open>Fiction\<close>

fiction_space (in solidity_sem) solidity_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> =
  FIC_ledge :: \<open>R_ledge.share_fiction\<close>

locale solidity =
  solidity_fic where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                            \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult}))\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::{no_inverse,comm_monoid_mult})\<close> 
+ \<phi>OO where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                          \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                          \<times> ('RES_N \<Rightarrow> 'RES::{no_inverse,comm_monoid_mult})
                          \<times> ('FIC_N \<Rightarrow> 'FIC))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>
begin

sublocale FIC_ledge: share_fiction_for_partial_mapping_resource2 Valid_Ledge R_ledge
    Resource_Validator INTERPRET FIC_ledge ..

end

section \<open>Primitive \<phi>-Type\<close>

context solidity_sem begin

subsection \<open>\<phi>-Types for Values\<close>

subsubsection \<open>Address\<close>

definition Address :: \<open>('VAL, address)\<phi>\<close>
  where \<open>Address addr = { V_Address.mk addr }\<close>

lemma Address_expn[\<phi>expns]:
  \<open>p \<in> (addr \<Ztypecolon> Address) \<longleftrightarrow> p = V_Address.mk addr\<close>
  unfolding Address_def \<phi>Type_def by simp

lemma Address_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (addr \<Ztypecolon> Address) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma Address_Zero[\<phi>reason]:
  \<open>\<phi>Zero \<tau>Address Address 0\<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_object_ref_def)

lemma [\<phi>reason]:
  \<open>\<phi>SemType (addr \<Ztypecolon> Address) \<tau>Address\<close>
  unfolding \<phi>SemType_def subset_iff by (simp add: \<phi>expns)

lemma [\<phi>reason]:
  \<open>\<phi>Equal Address (\<lambda>_ _. True) (=)\<close>
  unfolding \<phi>Equal_def by (simp add: \<phi>expns)


subsubsection \<open>Ledge Ref\<close>

definition LedgeRef :: \<open>('VAL, 'VAL ledge_ref)\<phi>\<close>
  where \<open>LedgeRef lref = { V_LedgeRef.mk lref }\<close>

lemma LedgeRef_expns[\<phi>expns]:
  \<open>p \<in> (lref \<Ztypecolon> LedgeRef) \<longleftrightarrow> p = V_LedgeRef.mk lref\<close>
  unfolding LedgeRef_def \<phi>Type_def by simp

lemma LedgeRef_inhabited[\<phi>reason_elim!,elim!]:
  \<open>Inhabited (lref \<Ztypecolon> LedgeRef) \<Longrightarrow> C \<Longrightarrow> C\<close>
  .

lemma LedgeRef_Zero[\<phi>reason]:
  \<open>\<phi>Zero \<tau>LedgeRef LedgeRef 0\<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_ledge_ref_def)

lemma LedgeRef_semty[\<phi>reason]:
  \<open>\<phi>SemType (lref \<Ztypecolon> LedgeRef) \<tau>LedgeRef\<close>
  unfolding \<phi>SemType_def by (simp add: \<phi>expns zero_ledge_ref_def)

lemma LedgeRef_eq[\<phi>reason]:
  \<open>\<phi>Equal LedgeRef (\<lambda>_ _. True) (=)\<close>
  unfolding \<phi>Equal_def by (simp add: \<phi>expns zero_ledge_ref_def)

end

subsection \<open>\<phi>-Types for Resources\<close>

subsubsection \<open>Slot of Ledge\<close>

text \<open>About the slot mentioned here, the semantic model does not consider compact storage where
  multiple fields are compact and stored in a single physical slot.\<close>

definition \<phi>AtLedge :: \<open>'VAL storage_path \<Rightarrow> ('y::one, 'x) \<phi> \<Rightarrow> ('VAL storage_path \<Rightarrow> 'y, 'x) \<phi>\<close>
  where \<open>\<phi>AtLedge path T x = { 1(path := v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>AtLedge_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>AtLedge path T) \<longleftrightarrow> (\<exists>v. p = 1(path := v) \<and> v \<in> (x \<Ztypecolon> T) )\<close>
  unfolding \<phi>AtLedge_def \<phi>Type_def by simp

lemma \<phi>AtLedge_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>AtLedge path T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)


subsubsection \<open>Path towards a Slot\<close>

definition \<phi>LedgePath
    :: \<open>'VAL storage_path \<Rightarrow> ('VAL storage_path \<Rightarrow> 'y, 'x) \<phi> \<Rightarrow> ('VAL storage_path \<Rightarrow> 'y::one, 'x) \<phi>\<close>
  where \<open>\<phi>LedgePath path T x = { push_map path v |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>LedgePath_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>LedgePath path T) \<longleftrightarrow> (\<exists>v. p = push_map path v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>LedgePath_def \<phi>Type_def by simp

lemma \<phi>LedgePath_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>LedgePath path T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>LedgePath_\<phi>LedgePath[simp]:
  \<open>(x \<Ztypecolon> \<phi>LedgePath path1 (\<phi>LedgePath path2 T)) = (x \<Ztypecolon> \<phi>LedgePath (path1@path2) T)\<close>
  by (simp add: set_eq_iff \<phi>expns push_map_push_map[symmetric], blast)

lemma \<phi>LedgePath_\<phi>AtLedge[simp]:
  \<open>(x \<Ztypecolon> \<phi>LedgePath path1 (\<phi>AtLedge path2 T)) = (x \<Ztypecolon> \<phi>AtLedge (path1@path2) T)\<close>
  apply (simp add: set_eq_iff \<phi>expns)
  using push_map_unit
  by force


subsubsection \<open>Spec of an Instance\<close>

definition (in solidity) LInstance
    :: \<open>address \<Rightarrow> ('VAL storage_path \<Rightarrow> 'VAL share option, 'x) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'x) \<phi>\<close>
  where \<open>LInstance addr T x = { FIC_ledge.mk (Fine (1(addr := v))) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma (in solidity) LInstance_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> LInstance addr T) \<longleftrightarrow> (\<exists>v. p = FIC_ledge.mk (Fine (1(addr := v))) \<and> v \<in> (x \<Ztypecolon> T) )\<close>
  unfolding \<phi>Type_def LInstance_def by simp

lemma (in solidity) LInstance_inhabited[\<phi>expns]:
  \<open>Inhabited (x \<Ztypecolon> LInstance addr T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)


section Instruction

subsection \<open>Value Arithmetic\<close>

definition (in solidity_sem) \<phi>M_getV_LedgeRef
    :: \<open>'VAL sem_value \<Rightarrow> ('VAL ledge_ref \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV_LedgeRef v F = \<phi>M_getV \<tau>Ref V_LedgeRef.dest v F\<close>

lemma (in solidity) \<phi>M_getV_LedgeRef[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F lref \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_LedgeRef raw F \<lbrace> X\<heavy_comma> lref \<Ztypecolon> Val raw LedgeRef \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_LedgeRef_def by (cases raw, simp, \<phi>reason, simp add: \<phi>expns)

definition (in solidity_sem) \<phi>M_getV_Address
    :: \<open>'VAL sem_value \<Rightarrow> (address \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV_Address v F = \<phi>M_getV \<tau>Address V_Address.dest v F\<close>

lemma (in solidity) \<phi>M_getV_Address[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F lref \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_Address raw F \<lbrace> X\<heavy_comma> lref \<Ztypecolon> Val raw Address \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_Address_def by (cases raw, simp, \<phi>reason, simp add: \<phi>expns)


subsection \<open>Resource\<close>

paragraph \<open>Load Field\<close>

definition (in solidity_sem) op_load_ledge :: \<open>'TY \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_load_ledge TY v =
    \<phi>M_getV_LedgeRef v (\<lambda>ref.
    R_ledge.\<phi>R_get_res_entry (ledge_ref.instance ref) (ledge_ref.path ref) (\<lambda>v.
    \<phi>M_assert (v \<in> Well_Type TY) \<ggreater> Success (sem_value v)))\<close>

lemma (in solidity) \<phi>M_get_res_entry_R_ledge[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> LInstance addr (\<phi>AtLedge path (n \<Znrres>\<phi> Identity)) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_ledge.\<phi>R_get_res_entry addr path F
      \<lbrace> v \<Ztypecolon> LInstance addr (\<phi>AtLedge path (n \<Znrres>\<phi> Identity)) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def)
  apply (rule R_ledge.\<phi>R_get_res_entry[where v=v])
  apply (simp add: FIC_ledge.partial_implies')
  by blast

lemma (in solidity) op_load_ledge:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load_ledge TY raw \<lbrace>
      v \<Ztypecolon> LInstance addr (\<phi>AtLedge path (\<phi>Share n Identity)) \<heavy_comma> ledge_ref addr path \<Ztypecolon> Val raw LedgeRef
  \<longmapsto> v \<Ztypecolon> LInstance addr (\<phi>AtLedge path (\<phi>Share n Identity)) \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity
\<rbrace>\<close>
  unfolding op_load_ledge_def Premise_def
  by (\<phi>reason, simp, \<phi>reason, assumption, \<phi>reason)

paragraph \<open>Store Field\<close>


definition (in solidity) op_store_ledge
      :: \<open>'TY \<Rightarrow> ('VAL \<times> 'VAL, unit,'RES_N,'RES) proc'\<close>
  where \<open>op_store_ledge TY =
    \<phi>M_caseV (\<lambda>vstore vref.
    \<phi>M_getV_LedgeRef vref (\<lambda>lref.
    \<phi>M_getV TY id vstore (\<lambda>store.
    R_ledge.\<phi>R_get_res_entry (ledge_ref.instance lref) (ledge_ref.path lref)
        (\<lambda>v. \<phi>M_assert (v \<in> Well_Type TY))
 \<ggreater> R_ledge.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some store) (ledge_ref.path lref)) (ledge_ref.instance lref))
)))\<close>

lemma (in solidity) "\<phi>R_set_res_ledge"[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_ledge.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some u) path) lref)
         \<lbrace> v \<Ztypecolon> LInstance lref (\<phi>AtLedge path (1 \<Znrres>\<phi> Identity))
  \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> LInstance lref (\<phi>AtLedge path (1 \<Znrres>\<phi> Identity)) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_ledge.interp_split'
          R_ledge.share_fiction_expn_full)
  apply (rule R_ledge.\<phi>R_set_res[where P="\<lambda>m. path \<in> dom (m lref)"])
  apply (cases lref; clarsimp simp add: Valid_Ledge_def map_fun_at_def dom1_def)
  apply (smt (verit, ccfv_SIG) Collect_cong dom_1 dom_eq_empty_conv option.distinct(1))
  using R_ledge.raw_unit_assertion_implies apply blast
  by assumption


lemma (in solidity) op_store_ledge:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store_ledge TY (\<phi>V_pair rawu rawref) \<lbrace>
      v \<Ztypecolon> LInstance lref (\<phi>AtLedge path (\<phi>Share 1 Identity)) \<heavy_comma> u \<Ztypecolon> Val rawu Identity \<heavy_comma> ledge_ref lref path \<Ztypecolon> Val rawref LedgeRef
  \<longmapsto> u \<Ztypecolon> LInstance lref (\<phi>AtLedge path (\<phi>Share 1 Identity))
\<rbrace>\<close>
  unfolding op_store_ledge_def Premise_def
  by (cases rawref; cases rawu; simp; \<phi>reason, simp, \<phi>reason, assumption, simp add: \<phi>expns, \<phi>reason)


paragraph \<open>Allocation\<close>

definition (in solidity) op_allocate_ledge :: \<open>('VAL,'RES_N,'RES) proc\<close>
  where \<open>op_allocate_ledge =
      R_ledge.\<phi>R_allocate_res_entry (\<lambda>ref. ref \<noteq> Nil) 1 (\<lambda>ref. Success (sem_value (V_ref.mk ref)))\<close>

lemma (in \<phi>OO) op_obj_allocate:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_obj_allocate cls
      \<lbrace> Void \<longmapsto> \<lambda>ret. \<exists>*ref. to_share o initial_value_of_class cls \<Ztypecolon> \<phi>RawObject ref\<heavy_comma> ref \<Ztypecolon> Val ret (Ref cls) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec op_obj_allocate_def
  apply (clarsimp simp add: \<phi>expns FIC_OO_share.interp_split')
  apply (rule R_objs.\<phi>R_allocate_res_entry)
  apply (clarsimp simp add: Valid_Objs_def)
  using obj_map_freshness apply blast
    apply (clarsimp simp add: Valid_Objs_def one_fun_def dom_initial_value_of_class)
  prefer 2 apply assumption
  apply (simp add: \<phi>expns)
  subgoal for r res k res'
    by (cases k; simp add: R_objs.share_fiction_expn_full') .





end