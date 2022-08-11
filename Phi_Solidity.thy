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
  \<comment> \<open>A user address always has this class\<close>

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

paragraph \<open>Algebra to represent uninitialized data\<close>

datatype 'V uninit = initialized 'V | uninitialized

instantiation uninit :: (nonsepable_semigroup) nonsepable_semigroup begin
definition \<open>sep_disj_uninit (x::'a uninit) (y::'a uninit) \<longleftrightarrow> False\<close>
instance apply standard unfolding sep_disj_uninit_def by simp_all
end

paragraph \<open>Models for Runtime Environment\<close>

datatype environ = Environ (sender: address) (code: address)

paragraph \<open>Models for Balance Table\<close>

type_synonym balance_table = \<open>address \<rightharpoonup> nat nonsepable\<close>
  \<comment> \<open>None means this part of the resource is not accessible and not specified\<close>

paragraph \<open>Main Model\<close>

type_synonym 'VAL ledge = \<open>(address \<Rightarrow> 'VAL storage_path \<Rightarrow> 'VAL uninit option)\<close>

text \<open>\<^term>\<open>Some (initialized V)\<close> means an initialized slot with value \<^term>\<open>V\<close>;
  \<^term>\<open>Some uninitialized\<close> means an uninitialized slot which is accessible from
    current computation state by legal ledge-accessing operations (excluding creation
    of new contract instance).
  \<^term>\<open>None\<close> means a slot which is not accessible. It is not allocated space typically.\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) solidity_res = ('VAL,'TY) \<phi>min_res +
  R_ledge   :: \<open>'VAL ledge ?\<close>
  R_environ :: \<open>environ nonsepable option ?\<close>
      \<comment> \<open>None means this part of the resource is not accessible and not specified\<close>
  R_balance :: \<open>balance_table ?\<close>


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
  and   Resource_Validator_Ledge':   \<open>Resource_Validator R_ledge.name   = R_ledge.inject ` Fine ` {h. h Nil = 1 \<and> finite (dom1 h) }\<close>
  and   Resource_Validator_Environ': \<open>Resource_Validator R_environ.name = R_environ.inject ` Fine ` UNIV\<close>
  and   Resource_Validator_Balance[simp]:
              \<open>Resource_Validator R_balance.name = R_balance.inject ` Fine ` UNIV\<close>
begin

paragraph \<open>Valid Types\<close>

lemma Valid_Type_LedgeRef[simp]:
  \<open>Valid_Type \<tau>LedgeRef\<close>
  unfolding Inhabited_def by simp

lemma Valid_Type_Address[simp]:
  \<open>Valid_Type \<tau>Address\<close>
  unfolding Inhabited_def by simp

paragraph \<open>Resource Ledge\<close>

definition Valid_Ledge :: "'VAL ledge set"
  where "Valid_Ledge = {h. h Nil = 1 \<and> finite (dom1 h) }"

lemma Valid_Ledge_1[simp]: \<open>1 \<in> Valid_Ledge\<close>
  unfolding Valid_Ledge_def one_fun_def one_fine_def by (simp add: dom1_def one_fun_def)

lemma Resource_Validator_Ledge[simp]:
  \<open>Resource_Validator R_ledge.name = R_ledge.inject ` Fine ` Valid_Ledge\<close>
  unfolding Valid_Ledge_def Resource_Validator_Ledge' ..

sublocale R_ledge: partial_map_resource2 Valid_Ledge R_ledge Resource_Validator
  by (standard, simp_all add: Resource_Validator_objs)


paragraph \<open>Resource Environ\<close>

definition Valid_Environ :: "environ set" where "Valid_Environ = UNIV"

sublocale R_environ: nosepable_mono_resource R_environ Resource_Validator \<open>nonsepable ` Valid_Environ\<close>
  apply standard apply simp
  apply (simp add: Resource_Validator_Environ' image_iff set_eq_iff)
  by (metis UNIV_I Valid_Environ_def nonsepable.exhaust not_None_eq)


paragraph \<open>Resource Balance\<close>

sublocale R_balance: partial_map_resource UNIV R_balance Resource_Validator
  by (standard; simp add: image_iff set_eq_iff)

end


subsection \<open>Fiction\<close>

fiction_space (in solidity_sem) solidity_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> =
  FIC_ledge   :: \<open>R_ledge.share_fiction\<close>
  FIC_environ :: \<open>R_environ.fiction_agree\<close>
  FIC_balance :: \<open>R_balance.share_fiction\<close>

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

sublocale FIC_environ: agreement_fiction_for_nosepable_mono_resource \<open>nonsepable ` Valid_Environ\<close>
  R_environ Resource_Validator INTERPRET FIC_environ ..

sublocale FIC_balance: share_fiction_for_partial_mapping_resource UNIV R_balance
    Resource_Validator INTERPRET FIC_balance ..

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
(*
term \<phi>MapAt

definition \<phi>AtLedge :: \<open>'VAL storage_path \<Rightarrow> ('y::one, 'x) \<phi> \<Rightarrow> ('VAL storage_path \<Rightarrow> 'y, 'x) \<phi>\<close>
  where \<open>\<phi>AtLedge path T x = { 1(path := v) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>AtLedge_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>AtLedge path T) \<longleftrightarrow> (\<exists>v. p = 1(path := v) \<and> v \<in> (x \<Ztypecolon> T) )\<close>
  unfolding \<phi>AtLedge_def \<phi>Type_def by simp

lemma \<phi>AtLedge_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>AtLedge path T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)
*)

subsubsection \<open>Path towards a Slot\<close>

definition \<phi>MapKeys
    :: \<open>'k list \<Rightarrow> ('k list \<Rightarrow> 'y, 'x) \<phi> \<Rightarrow> ('k list \<Rightarrow> 'y::one, 'x) \<phi>\<close>
  where \<open>\<phi>MapKeys path T x = { push_map path v |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma \<phi>MapKeys_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>MapKeys path T) \<longleftrightarrow> (\<exists>v. p = push_map path v \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>MapKeys_def \<phi>Type_def by simp

lemma \<phi>MapKeys_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>MapKeys path T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>MapKeys_\<phi>MapKeys[simp]:
  \<open>(x \<Ztypecolon> \<phi>MapKeys path1 (\<phi>MapKeys path2 T)) = (x \<Ztypecolon> \<phi>MapKeys (path1@path2) T)\<close>
  by (simp add: set_eq_iff \<phi>expns push_map_push_map[symmetric], blast)

(*
lemma \<phi>MapKeys_\<phi>AtLedge[simp]:
  \<open>(x \<Ztypecolon> \<phi>MapKeys path1 (\<phi>AtLedge path2 T)) = (x \<Ztypecolon> \<phi>AtLedge (path1@path2) T)\<close>
  apply (simp add: set_eq_iff \<phi>expns)
  using push_map_unit
  by force *)


subsubsection \<open>Spec of an Instance\<close>

definition (in solidity) LInstance
    :: \<open>address \<Rightarrow> ('VAL storage_path \<Rightarrow> 'VAL uninit share option, 'x) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'x) \<phi>\<close>
  where \<open>LInstance addr T x = { FIC_ledge.mk (Fine (1(addr := v))) |v. v \<in> (x \<Ztypecolon> T) }\<close>

lemma (in solidity) LInstance_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> LInstance addr T) \<longleftrightarrow> (\<exists>v. p = FIC_ledge.mk (Fine (1(addr := v))) \<and> v \<in> (x \<Ztypecolon> T) )\<close>
  unfolding \<phi>Type_def LInstance_def by simp

lemma (in solidity) LInstance_inhabited[\<phi>expns]:
  \<open>Inhabited (x \<Ztypecolon> LInstance addr T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

subsubsection \<open>Initialized or Not\<close>

definition (in solidity) \<phi>Init :: \<open>('VAL, 'x) \<phi> \<Rightarrow> ('VAL uninit, 'x) \<phi>\<close>
  where \<open>\<phi>Init T x = (({uninitialized} \<^bold>s\<^bold>u\<^bold>b\<^bold>j Zero (SemTyp_Of (x \<Ztypecolon> T)) \<in> (x \<Ztypecolon> T)) + initialized ` (x \<Ztypecolon> T))\<close>

lemma (in solidity) \<phi>Inited_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Init T) \<longleftrightarrow> (p = uninitialized \<and> Zero (SemTyp_Of (x \<Ztypecolon> T)) \<in> (x \<Ztypecolon> T) \<or> (\<exists>v. p = initialized v \<and> v \<in> (x \<Ztypecolon> T)))\<close>
  unfolding \<phi>Type_def \<phi>Init_def by (simp add: \<phi>expns, blast)
  
lemma (in solidity) \<phi>Inited_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Init T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)


definition \<phi>Uninit :: \<open>('v uninit, unit) \<phi>\<close>
  where \<open>\<phi>Uninit x = {uninitialized}\<close>

lemma \<phi>Uninit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Uninit) \<longleftrightarrow> p = uninitialized\<close>
  unfolding \<phi>Type_def \<phi>Uninit_def by simp

lemma \<phi>Uninit_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Uninit) \<Longrightarrow> C \<Longrightarrow> C\<close> .

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

context solidity_sem begin
term R_ledge.\<phi>R_get_res_entry
end

definition (in solidity_sem)
  \<phi>M_get_res_entry_ledge :: \<open>
    'TY \<Rightarrow> 'VAL ledge_ref
       \<Rightarrow> ('VAL \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('a, 'RES_N, 'RES) state)
         \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('a, 'RES_N, 'RES) state\<close>
  where "\<phi>M_get_res_entry_ledge TY k F =
    R_ledge.\<phi>R_get_res_entry (ledge_ref.instance k) (ledge_ref.path k) (\<lambda>v.
      case v of initialized u \<Rightarrow> \<phi>M_assert (u \<in> Well_Type TY) \<ggreater> F u
        | uninitialized \<Rightarrow> F (Zero TY))"

definition (in solidity_sem) op_load_ledge :: \<open>'TY \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_load_ledge TY v =
    \<phi>M_getV_LedgeRef v (\<lambda>ref.
    \<phi>M_get_res_entry_ledge TY ref (\<lambda>v. Success (sem_value v)))\<close>

lemma (in \<phi>empty_sem) [simp]:
  \<open> v \<in> Well_Type TY
\<Longrightarrow> SemTyp_Of (v \<Ztypecolon> Identity) = TY\<close>
  unfolding \<phi>Type_def Identity_def
  by (simp add: \<phi>SemType_def)

lemma (in solidity) \<phi>M_get_res_entry_R_ledge[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> LInstance addr (\<phi>MapAt path (n \<Znrres>\<phi> (\<phi>Init Identity))) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_res_entry_ledge TY (ledge_ref addr path) F
      \<lbrace> v \<Ztypecolon> LInstance addr (\<phi>MapAt path (n \<Znrres>\<phi> (\<phi>Init Identity))) \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec \<phi>M_get_res_entry_ledge_def Premise_def
  apply (clarsimp simp add: \<phi>expns zero_set_def)
  subgoal for r res vb
  apply (rule R_ledge.\<phi>R_get_res_entry[where v=vb])
  apply (simp add: FIC_ledge.partial_implies')
    apply (cases vb; simp)
    subgoal premises prems for x1
      apply (rule prems(2)[THEN spec[where x=r], THEN spec[where x=res], THEN mp, simplified prems, simplified])
      using FIC_ledge.Fic_Space_m prems(3) by blast
    subgoal premises prems
      apply (rule prems(2)[THEN spec[where x=r], THEN spec[where x=res], THEN mp, simplified prems, simplified])
      using FIC_ledge.Fic_Space_m prems(3) by blast . .

lemma (in solidity) op_load_ledge:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load_ledge TY raw \<lbrace>
      v \<Ztypecolon> LInstance addr (\<phi>MapAt path (\<phi>Share n (\<phi>Init Identity))) \<heavy_comma> ledge_ref addr path \<Ztypecolon> Val raw LedgeRef
  \<longmapsto> v \<Ztypecolon> LInstance addr (\<phi>MapAt path (\<phi>Share n (\<phi>Init Identity))) \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity
\<rbrace>\<close>
  unfolding op_load_ledge_def Premise_def
  by (\<phi>reason, simp, \<phi>reason)


paragraph \<open>Store Field\<close>

definition (in solidity) op_store_ledge
      :: \<open>'TY \<Rightarrow> ('VAL \<times> 'VAL, unit,'RES_N,'RES) proc'\<close>
  where \<open>op_store_ledge TY =
    \<phi>M_caseV (\<lambda>vstore vref.
    \<phi>M_getV_LedgeRef vref (\<lambda>lref.
    \<phi>M_getV TY id vstore (\<lambda>store.
    \<phi>M_get_res_entry_ledge TY lref (\<lambda>_. Success \<phi>V_nil)
 \<ggreater> R_ledge.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some (initialized store)) (ledge_ref.path lref)) (ledge_ref.instance lref))
)))\<close>

lemma (in solidity) "\<phi>R_set_res_ledge"[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_ledge.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some (initialized u)) path) lref)
         \<lbrace> v \<Ztypecolon> LInstance lref (\<phi>MapAt path (1 \<Znrres>\<phi> \<phi>Init Identity))
  \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> LInstance lref (\<phi>MapAt path (1 \<Znrres>\<phi> \<phi>Init Identity)) \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def FIC_ledge.interp_split')
  apply (rule \<phi>Res_Spec_ex_\<S>[where x=\<open>FIC_ledge.mk (Fine (1(lref := 1(path := Some (1 \<Znrres> initialized u)))))\<close>],
         rule \<phi>Res_Spec_subj_\<S>)
  using FIC_ledge.Fic_Space_m apply blast
  apply (simp add: R_ledge.share_fiction_expn_full)
  apply (rule R_ledge.\<phi>R_set_res[where P="\<lambda>m. path \<in> dom (m lref)"])
  apply (cases lref; clarsimp simp add: Valid_Ledge_def map_fun_at_def dom1_def)
  apply (smt (verit, ccfv_SIG) Collect_cong dom_1 dom_eq_empty_conv option.distinct(1))
  using R_ledge.raw_unit_assertion_implies apply blast
  by assumption


lemma (in solidity) op_store_ledge:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store_ledge TY (\<phi>V_pair rawu rawref) \<lbrace>
      v \<Ztypecolon> LInstance lref (\<phi>MapAt path (\<phi>Share 1 (\<phi>Init Identity))) \<heavy_comma> u \<Ztypecolon> Val rawu Identity \<heavy_comma> ledge_ref lref path \<Ztypecolon> Val rawref LedgeRef
  \<longmapsto> u \<Ztypecolon> LInstance lref (\<phi>MapAt path (\<phi>Share 1 (\<phi>Init Identity)))
\<rbrace>\<close>
  unfolding op_store_ledge_def Premise_def
  by (cases rawref; cases rawu; simp; \<phi>reason, simp add: Premise_def, \<phi>reason, simp add: \<phi>expns, \<phi>reason)


paragraph \<open>Allocation\<close>

definition (in solidity) op_allocate_ledge :: \<open>('VAL,'RES_N,'RES) proc\<close>
  where \<open>op_allocate_ledge =
      R_ledge.\<phi>R_allocate_res_entry (\<lambda>addr. addr \<noteq> Nil) (\<lambda>_. Some uninitialized)
        (\<lambda>addr. Success (sem_value (V_Address.mk addr)))\<close>

lemma (in solidity) op_obj_allocate:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_allocate_ledge
      \<lbrace> Void \<longmapsto> \<lambda>ret. \<exists>*ref. 1 \<Ztypecolon> LInstance ref (Identity \<Rrightarrow> 1 \<Znrres>\<phi> \<phi>Uninit)\<heavy_comma> ref \<Ztypecolon> Val ret Address \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec op_allocate_ledge_def
  apply (clarsimp simp add: \<phi>expns FIC_ledge.interp_split')
  apply (rule R_ledge.\<phi>R_allocate_res_entry)
  apply (clarsimp simp add: Valid_Ledge_def)
  using obj_map_freshness apply blast
  apply (clarsimp simp add: Valid_Ledge_def one_fun_def dom_initial_value_of_class)
  prefer 2 apply assumption
  apply (simp add: \<phi>expns)
  subgoal for r res k res'
    apply (rule exI[where x=\<open>FIC_ledge.mk (Fine (1(k := (\<lambda>_. Some (1 \<Znrres> uninitialized)))))\<close>])
    apply (cases k; simp add: R_ledge.share_fiction_expn_full'
            [where f=\<open>\<lambda>_. Some uninitialized\<close>, simplified comp_def, simplified])
    by blast .




end