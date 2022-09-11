theory Phi_Solidity
  imports Phi_OO Map_of_Tree Phi_Min_ex
    Phi_Prime_ex
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
type_synonym contract_class = \<open>unit class\<close>
type_synonym address = \<open>unit object_ref\<close>
  \<comment> \<open>The ledge doesn't need to records the type of fields, so the type parameter of object_ref is unit.
      It the class of an instance_ref is \<^term>\<open>class_user\<close>, it is an user address.\<close>
datatype 'VAL ledge_ref = ledge_ref ("instance": address) (path: \<open>'VAL storage_path\<close>)
hide_const (open) "instance" path


definition prepend_ledge_ref :: \<open>'VAL storage_key \<Rightarrow> 'VAL ledge_ref \<Rightarrow> 'VAL ledge_ref\<close>
  where \<open>prepend_ledge_ref a ref = (case ref of ledge_ref addr path \<Rightarrow> ledge_ref addr (a#path))\<close>

lemma prepend_ledge_ref[simp]:
  \<open>prepend_ledge_ref a (ledge_ref addr path) = ledge_ref addr (a#path)\<close>
  unfolding prepend_ledge_ref_def by simp


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

text \<open>Not Supported: msg.data\<close>

datatype environ = Environ
  (blockhash: \<open>nat \<Rightarrow> 256 word\<close>)
  (basefee: \<open>256 word\<close>)
  (chainid: \<open>256 word\<close>)
  (coinbase: \<open>256 word\<close>)
  (difficulty: \<open>256 word\<close>)
  (gaslimit: \<open>256 word\<close>)
  (blocknumber: \<open>256 word\<close>)
  (timestamp: \<open>256 word\<close>)
  (gasprice: \<open>256 word\<close>)
  (origin: address)

datatype mutable_environ = Mutable_Environ
  (sender: address)
  (sig: \<open>32 word\<close>)
  ("value": \<open>256 word\<close>)

hide_const (open) blockhash basefee chainid coinbase difficulty gaslimit blocknumber timestamp
  sender sig "value" gasprice origin

paragraph \<open>Models for Balance Table\<close>

type_synonym balance_table = \<open>address \<rightharpoonup> 256 word\<close>
  \<comment> \<open>None means this part of the resource is not accessible and not specified\<close>

paragraph \<open>Main Model\<close>

type_synonym 'VAL ledge = \<open>(address \<Rightarrow> 'VAL storage_path \<Rightarrow> 'VAL uninit option)\<close>

text \<open>\<^term>\<open>Some (initialized V)\<close> means an initialized slot with value \<^term>\<open>V\<close>;
  \<^term>\<open>Some uninitialized\<close> means an uninitialized slot which is accessible from
    current computation state by legal ledge-accessing operations (excluding creation
    of new contract instance).
  \<^term>\<open>None\<close> means a slot which is not accessible. It is not allocated space typically.\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) solidity_res = ('VAL,'TY) \<phi>min_res +
  R_ledge   :: \<open>'VAL ledge\<close>
  R_environ :: \<open>environ nonsepable option\<close>
      \<comment> \<open>None means this part of the resource is not accessible and not specified\<close>
  R_balance :: \<open>balance_table\<close>
  R_msg :: \<open>mutable_environ nonsepable option\<close>


subsection \<open>Semantics\<close>

datatype 'TY method_sig = method_sig (name: string) (typ_sig: \<open>'TY list \<times> 'TY list\<close>)
hide_const (open) "name" "typ_sig"

locale solidity_sem =
  \<phi>OO_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra))\<close>
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
            and TYPE'REP  = \<open>TYPE('RES::sep_algebra)\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra)
            ) itself\<close>
assumes WT_LedgeRef[simp]: \<open>Well_Type \<tau>LedgeRef = UNIV\<close>
  and   WT_Address [simp]: \<open>Well_Type \<tau>Address  = UNIV\<close>
  and   zero_LedgeRef[simp]: \<open>Zero \<tau>LedgeRef = Some (V_LedgeRef.mk (ledge_ref Nil []))\<close>
  and   zero_Address[simp]:  \<open>Zero \<tau>Address  = Some (V_Address.mk Nil)\<close>
  and   Can_EqCompare_LedgeRef[simp]: \<open>Can_EqCompare res (V_LedgeRef.mk lref1) (V_LedgeRef.mk lref2)\<close>
  and   Can_EqCompare_Address[simp]:  \<open>Can_EqCompare res (V_Address.mk addr1)  (V_Address.mk addr2)\<close>
  and   EqCompare_LedgeRef[simp]:     \<open>EqCompare (V_LedgeRef.mk lref1) (V_LedgeRef.mk lref2) \<longleftrightarrow> lref1 = lref2\<close>
  and   EqCompare_Address[simp]:      \<open>EqCompare (V_Address.mk addr1)  (V_Address.mk addr2)  \<longleftrightarrow> addr1 = addr2\<close>
  and   Resource_Validator_Ledge':   \<open>Resource_Validator R_ledge.name   = R_ledge.inject ` {h. h Nil = 1 \<and> finite (dom1 h) }\<close>
  and   Resource_Validator_Environ': \<open>Resource_Validator R_environ.name = R_environ.inject ` UNIV\<close>
  and   Resource_Validator_Msg[simp]: \<open>Resource_Validator R_msg.name = R_msg.inject ` UNIV\<close>
  and   Resource_Validator_Balance[simp]:
              \<open>Resource_Validator R_balance.name = R_balance.inject ` UNIV\<close>

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
  unfolding Valid_Ledge_def one_fun_def by (simp add: dom1_def one_fun_def)

lemma Resource_Validator_Ledge[simp]:
  \<open>Resource_Validator R_ledge.name = R_ledge.inject ` Valid_Ledge\<close>
  unfolding Valid_Ledge_def Resource_Validator_Ledge' ..

sublocale R_ledge: partial_map_resource2 Valid_Ledge R_ledge Resource_Validator
  by (standard, simp_all add: Resource_Validator_objs)


paragraph \<open>Resource Environ\<close>

sublocale R_environ: nonsepable_mono_resource R_environ Resource_Validator UNIV
  apply standard apply simp
  apply (simp add: Resource_Validator_Environ' image_iff set_eq_iff)
  by (metis nonsepable.exhaust not_None_eq)

sublocale R_msg: nonsepable_mono_resource R_msg Resource_Validator UNIV
  apply standard apply simp
  apply (simp add: Resource_Validator_Environ' image_iff set_eq_iff)
  by (metis nonsepable.exhaust not_None_eq)


paragraph \<open>Resource Balance\<close>

sublocale R_balance: partial_map_resource UNIV R_balance Resource_Validator
  by (standard; simp add: image_iff set_eq_iff)

paragraph \<open>Transition Closure\<close>



end


subsection \<open>Fiction\<close>

fiction_space (in solidity_sem) solidity_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> =
  FIC_ledge   :: \<open>R_ledge.share_fiction\<close>
  FIC_environ :: \<open>R_environ.fiction_agree\<close>
  FIC_balance :: \<open>R_balance.share_fiction\<close>
  FIC_msg     :: \<open>R_msg.raw_basic_fiction fiction.it\<close>

locale solidity =
  solidity_fic where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                            \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra))\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::sep_algebra)\<close> 
+ \<phi>OO where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                          \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                          \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra)
                          \<times> ('FIC_N \<Rightarrow> 'FIC))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>
begin

sublocale FIC_ledge: share_fiction_for_partial_mapping_resource2 Valid_Ledge R_ledge
    Resource_Validator INTERPRET FIC_ledge ..

sublocale FIC_environ: agreement_fiction_for_nosepable_mono_resource UNIV
  R_environ Resource_Validator INTERPRET FIC_environ ..

sublocale FIC_balance: share_fiction_for_partial_mapping_resource UNIV R_balance
    Resource_Validator INTERPRET FIC_balance ..

sublocale FIC_msg: identity_fiction UNIV R_msg
    Resource_Validator INTERPRET FIC_msg
  apply (standard; simp add: set_eq_iff image_iff)
  by (metis nonsepable.exhaust option.exhaust)

end

subsection \<open>Project\<close>

text \<open>This section gives bases for extending the common solidity semantics for each verification
  project. This extension contains basically public methods in the project, which are a part of
  the program semantics but different for each project.
  (It is essentially due to our formalization do not internalize the behavior of
   declaring public methods. We do not have a model for program modules. I think locale,
   is pretty good for modeling them in this shallow way, though it indeed extends the semantics
   every time. Or we may say, our model for modules is exact locale, in this shallow way?)
  Later we will provide a common installation of the common semantics but for each project,
  the extension is different, and users have to instantiate that extension.\<close>

locale solidity_project_sem =
  solidity_sem where TYPES = TYPES
for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
             \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
             \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra)
           ) itself\<close>
+
fixes Internal_Public_Methods_Transitions :: \<open>('RES_N,'RES) transition list\<close>
  \<comment> \<open>It is a restriction. The verification conclusion is not extensible.
      Every time we only consider the sub-system consisting of the modules to be verified,
      and we only consider state of this sub-system, not including state outside.
      It causes any time we want to extend the conclusion to a larger project,
      the proof cannot be reused.
      This restriction is because, any transition of this sub-system is an instance belongs to
      the closure of all its public methods, but transitions in outer system is unknowable.
      The frame rule which gives us localization before, is not available here because the
      state of outer system is not constant anymore.

      TODO: why not use an explicit R1 R2 to express the change of outer state,
          { R1 * X } C { R2 * Y }
      Question: but what if we call two outer methods sequentially,
          { Ra1 * Xa } Ca { Ra2 * Ya }       { Rb1 * Xb } Cb { Rb2 * Yb }
      How to connect / coordinate these two free variables Ra2 and Rb1?\<close>

fixes Public_Methods :: \<open>contract_class \<Rightarrow> 'TY method_sig \<Rightarrow> ('VAL list,'VAL list,'RES_N,'RES) proc' option\<close>
  \<comment> \<open>All public methods in the smart contract environment, including methods inside the module
        and those outside methods of clients.\<close>
  \<comment> \<open>The public methods can be defined unspecifiedly, just requiring meeting the proposition
      ``public_methods_transition_closure'', typically by a Hilbert Choice.
      We leave this to be a fixed variable instead of defining it, is for the sake of
      potentially specific assignment in an actual verification project.
      User may assigns the transition of some method of some class to be something specific.\<close>
  \<comment> \<open>Here talk about a drawback in Solidity. Currently the signature of virtual methods in
    the base class actually specifies nothing but only types of arguments and returns.
    It is far from the ideal. The ideal should be specifying more and restricting more,
    to be best a specification written in Separation Logic. This is an advantage of a
    theorem based contract language.\<close>

assumes public_methods_well_typed:
  \<open>\<forall>cls name. name \<in> dom (Public_Methods cls)
\<longrightarrow> \<phi>Type_Spec_for_Deep (method_sig.typ_sig name) (the (Public_Methods cls name))\<close>

assumes public_methods_transition_closure':
   \<open>\<forall>cls name. name \<in> dom (Public_Methods cls)
\<longrightarrow> Transition_Of' (the (Public_Methods cls name)) \<subseteq> (\<Union> (set Internal_Public_Methods_Transitions))\<^sup>*\<close>
begin

definition \<open>Transition_Closure = (\<Union> (set Internal_Public_Methods_Transitions))\<^sup>*\<close>

lemma public_methods_transition_closure:
  \<open>\<forall>cls name. name \<in> dom (Public_Methods cls)
\<longrightarrow> Transition_Of' (the (Public_Methods cls name)) \<subseteq> Transition_Closure\<close>
  unfolding Transition_Closure_def using public_methods_transition_closure' .

end


locale solidity_project =
  solidity_project_sem where TYPES = \<open>TYPE (('TY_N \<Rightarrow> 'TY)
                                         \<times> ('VAL_N \<Rightarrow> 'VAL)
                                         \<times> ('RES_N \<Rightarrow> 'RES)
                                     )\<close>
+ solidity where TYPES = \<open>TYPE (('TY_N \<Rightarrow> 'TY)
                              \<times> ('VAL_N \<Rightarrow> 'VAL)
                              \<times> ('RES_N \<Rightarrow> 'RES)
                              \<times> ('FIC_N \<Rightarrow> 'FIC)
                        )\<close>
for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
             \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
             \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra)
             \<times> ('FIC_N \<Rightarrow> 'FIC::sep_algebra)
           ) itself\<close>
+
fixes Transition_Closure_Spec :: \<open>('RES_N, 'RES) transition\<close>
  \<comment> \<open>This constant is intended to be given by user! that meets the Transition_Closure_Spec'.\<close>
assumes Transition_Closure:
  \<open>Transition_Closure \<subseteq> Transition_Closure_Spec\<close>



section \<open>Primitive \<phi>-Types\<close>

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

subsection \<open>\<phi>-Types for Ledge\<close>

subsubsection \<open>Initialized or Not\<close>

text \<open>\<phi>Init T relates a value with T if the value is initialized; or if not, it relates the zero
  value of that type with T.\<close>

context \<phi>empty_sem begin

definition \<phi>Init :: \<open>('VAL, 'x) \<phi> \<Rightarrow> ('VAL uninit, 'x) \<phi>\<close>
  where \<open>\<phi>Init T x = ({uninitialized} \<^bold>s\<^bold>u\<^bold>b\<^bold>j the (Zero (SemTyp_Of (x \<Ztypecolon> T))) \<in> (x \<Ztypecolon> T)) + initialized ` (x \<Ztypecolon> T)\<close>

abbreviation \<phi>Share_Some_Init ("\<fish_eye>i _" [91] 90)
  where \<open>\<phi>Share_Some_Init T \<equiv> \<fish_eye> \<phi>Init T\<close>

lemma \<phi>Inited_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Init T) \<longleftrightarrow> (p = uninitialized \<and> the (Zero (SemTyp_Of (x \<Ztypecolon> T))) \<in> (x \<Ztypecolon> T) \<or> (\<exists>v. p = initialized v \<and> v \<in> (x \<Ztypecolon> T)))\<close>
  unfolding \<phi>Type_def \<phi>Init_def by (simp add: \<phi>expns, blast)
  
lemma \<phi>Inited_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Init T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns, blast)

end

definition \<phi>Uninit :: \<open>('v uninit, unit) \<phi>\<close>
  where \<open>\<phi>Uninit x = {uninitialized}\<close>

lemma \<phi>Uninit_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Uninit) \<longleftrightarrow> p = uninitialized\<close>
  unfolding \<phi>Type_def \<phi>Uninit_def by simp

lemma \<phi>Uninit_inhabited[\<phi>reason_elim!, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<phi>Uninit) \<Longrightarrow> C \<Longrightarrow> C\<close> .

context solidity begin

subsubsection \<open>Spec of an Instance\<close>

notation FIC_ledge.\<phi> ("ledge: _" [52] 51)

subsection \<open>Balance\<close>

notation FIC_balance.\<phi> ("balance: _" [52] 51)

end

section Instructions

context solidity_sem begin

subsection \<open>Value Arithmetic\<close>

paragraph \<open>Auxiliary\<close>

definition \<phi>M_getV_LedgeRef
    :: \<open>'VAL sem_value \<Rightarrow> ('VAL ledge_ref \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV_LedgeRef v F = \<phi>M_getV \<tau>Ref V_LedgeRef.dest v F\<close>

definition \<phi>M_getV_Address
    :: \<open>'VAL sem_value \<Rightarrow> (address \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_getV_Address v F = \<phi>M_getV \<tau>Address V_Address.dest v F\<close>

subsubsection \<open>Calculation of Ledge Ref\<close>

paragraph \<open>Get Member of a Structure\<close>

definition op_get_member_ledgeRef :: \<open>field_name \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_get_member_ledgeRef field raw =
    \<phi>M_getV_LedgeRef raw (\<lambda>ref.
    Return (sem_value (V_LedgeRef.mk (prepend_ledge_ref (SP_field field) ref)))
)\<close>

paragraph \<open>Get Value of a Mapping\<close>

definition op_get_mapping_ledgeRef :: \<open>('VAL \<times> 'VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_get_mapping_ledgeRef =
    \<phi>M_caseV (\<lambda>raw_ref raw_v.
    \<phi>M_getV_LedgeRef raw_ref (\<lambda>ref.
    \<phi>M_getV_raw id raw_v(\<lambda>v.
    Return (sem_value (V_LedgeRef.mk (prepend_ledge_ref (SP_map_key v) ref)))
)))\<close>

subsection \<open>Ledge\<close>

paragraph \<open>Load Field\<close>

definition \<phi>M_get_res_entry_ledge :: \<open>
    'TY \<Rightarrow> 'VAL ledge_ref
       \<Rightarrow> ('VAL \<Rightarrow> ('a, 'RES_N, 'RES) proc)
         \<Rightarrow> ('a, 'RES_N, 'RES) proc\<close>
  where "\<phi>M_get_res_entry_ledge TY k F =
    R_ledge.\<phi>R_get_res_entry (ledge_ref.instance k) (ledge_ref.path k) (\<lambda>v.
      case v of initialized u \<Rightarrow> \<phi>M_assert (u \<in> Well_Type TY) \<ggreater> F u
        | uninitialized \<Rightarrow> F (the (Zero TY)))"

subsection \<open>Ledge\<close>

paragraph \<open>Load Field\<close>

definition op_load_ledge :: \<open>'TY \<Rightarrow> ('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_load_ledge TY v =
    \<phi>M_getV_LedgeRef v (\<lambda>ref.
    \<phi>M_get_res_entry_ledge TY ref (\<lambda>v. Return (sem_value v)))\<close>

paragraph \<open>Store Field\<close>

definition op_store_ledge
      :: \<open>'TY \<Rightarrow> ('VAL \<times> 'VAL, unit,'RES_N,'RES) proc'\<close>
  where \<open>op_store_ledge TY =
    \<phi>M_caseV (\<lambda>vstore vref.
    \<phi>M_getV_LedgeRef vref (\<lambda>lref.
    \<phi>M_getV TY id vstore (\<lambda>store.
    \<phi>M_get_res_entry_ledge TY lref (\<lambda>_. Return \<phi>V_none)
 \<ggreater> R_ledge.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some (initialized store)) (ledge_ref.path lref)) (ledge_ref.instance lref))
)))\<close>

paragraph \<open>Allocation\<close>

definition op_allocate_ledge :: \<open>('VAL,'RES_N,'RES) proc\<close>
  where \<open>op_allocate_ledge =
      R_ledge.\<phi>R_allocate_res_entry (\<lambda>addr. addr \<noteq> Nil) (\<lambda>_. Some uninitialized)
        (\<lambda>addr. Return (sem_value (V_Address.mk addr)))\<close>

subsection \<open>Environment & Balance\<close>

subsubsection \<open>Balance Table\<close>

definition op_get_balance :: \<open>('VAL,'VAL,'RES_N,'RES) proc'\<close>
  where \<open>op_get_balance va =
    \<phi>M_getV_Address va (\<lambda>addr.
    R_balance.\<phi>R_get_res_entry addr (\<lambda>n.
    Return (sem_value (word_to_V_int n))
  ))\<close>

definition \<phi>M_set_balance :: \<open>('VAL \<times> 'VAL, unit,'RES_N,'RES) proc'\<close>
  where \<open>\<phi>M_set_balance =
    \<phi>M_caseV (\<lambda>va vm.
    \<phi>M_getV_Address va (\<lambda>addr.
    \<phi>M_getV (\<tau>Int 256) V_int.dest vm (\<lambda>(_,m).
    R_balance.\<phi>R_set_res (\<lambda>f. f(addr \<mapsto> of_nat m))
  )))\<close>

subsubsection \<open>Globally Available Variables\<close>

definition op_get_environ_word :: \<open>(environ \<Rightarrow> 'len::len word) \<Rightarrow> ('VAL, 'RES_N,'RES) proc\<close>
  where \<open>op_get_environ_word G =
    R_environ.\<phi>R_get_res_entry (\<lambda>env. Return (sem_value (word_to_V_int (G env))))\<close>

definition op_get_mutable_environ_word :: \<open>(mutable_environ \<Rightarrow> 'len::len word) \<Rightarrow> ('VAL, 'RES_N,'RES) proc\<close>
  where \<open>op_get_mutable_environ_word G =
    R_msg.\<phi>R_get_res_entry (\<lambda>env. Return (sem_value (word_to_V_int (G env))))\<close>

definition op_get_sender :: \<open>('VAL, 'RES_N,'RES) proc\<close>
  where \<open>op_get_sender =
    R_msg.\<phi>R_get_res_entry (\<lambda>env. Return (sem_value (V_Address.mk (mutable_environ.sender env))))\<close>


end

section Specifications

context solidity begin

subsection \<open>Value Arithmetic\<close>

paragraph \<open>Auxiliary\<close>

lemma \<phi>M_getV_LedgeRef[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F lref \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_LedgeRef raw F \<lbrace> X\<heavy_comma> lref \<Ztypecolon> Val raw LedgeRef \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_LedgeRef_def by (cases raw, simp, \<phi>reason, simp add: \<phi>expns)

declare \<phi>M_getV_LedgeRef[where X=1, simplified, \<phi>reason!]

lemma \<phi>M_getV_Address[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F lref \<lbrace> X \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_getV_Address raw F \<lbrace> X\<heavy_comma> lref \<Ztypecolon> Val raw Address \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>M_getV_Address_def by (cases raw, simp, \<phi>reason, simp add: \<phi>expns)


subsubsection \<open>Calculation of Ledge Ref\<close>

paragraph \<open>Get Member of a Structure\<close>

lemma op_get_member_ledgeRef_\<phi>app:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_member_ledgeRef field raw \<lbrace>
    ledge_ref addr path \<Ztypecolon> Val raw LedgeRef
\<longmapsto> \<^bold>v\<^bold>a\<^bold>l ledge_ref addr (SP_field field#path) \<Ztypecolon> LedgeRef
\<rbrace>\<close>
  unfolding op_get_member_ledgeRef_def
  by (cases raw; simp; \<phi>reason)


paragraph \<open>Get Value of a Mapping\<close>

lemma op_get_mapping_ledgeRef_\<phi>app:
  \<open> is_singleton (x \<Ztypecolon> T)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_mapping_ledgeRef (\<phi>V_pair raw_ref raw_v) \<lbrace>
    x \<Ztypecolon> Val raw_v T\<heavy_comma>
    ledge_ref addr path \<Ztypecolon> Val raw_ref LedgeRef
\<longmapsto> \<^bold>v\<^bold>a\<^bold>l ledge_ref addr (SP_map_key (the_elem (x \<Ztypecolon> T))#path) \<Ztypecolon> LedgeRef
\<rbrace>\<close>
  unfolding op_get_mapping_ledgeRef_def
  apply (cases raw_v; cases raw_ref; simp; \<phi>reason; simp add: \<phi>expns)
  by (metis is_singleton_the_elem singletonD)


subsection \<open>Ledge\<close>

paragraph \<open>Load Field\<close>

lemma \<phi>M_get_res_entry_R_ledge[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> ledge: addr \<^bold>\<rightarrow> path \<^bold>\<rightarrow> n \<Znrres> \<fish_eye>i Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_res_entry_ledge TY (ledge_ref addr path) F
      \<lbrace> v \<Ztypecolon> ledge: addr \<^bold>\<rightarrow> path \<^bold>\<rightarrow> n \<Znrres> \<fish_eye>i Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec \<phi>M_get_res_entry_ledge_def Premise_def
  apply (clarsimp simp add: \<phi>expns zero_set_def del: subsetI)
  subgoal for r res vb
  apply (rule R_ledge.\<phi>R_get_res_entry[where v=vb])
  apply simp
    apply (cases vb; simp)
    subgoal premises prems for x1
      apply (rule prems(2)[THEN spec[where x=r], THEN spec[where x=res], THEN mp])
      apply (rule exI[where x=\<open>FIC_ledge.mk (1(addr := 1(path \<mapsto> Share n (initialized v))))\<close>], simp add: prems)
      apply (rule exI[where x=\<open>1(path \<mapsto> Share n (initialized v))\<close>], simp)
      apply (rule exI[where x=\<open>Some (Share n (initialized v))\<close>], simp)
      apply (rule exI[where x=\<open>Some (Share 1 (initialized v))\<close>], simp add: prems)
      by (rule exI[where x=\<open>Some (initialized v)\<close>], simp)
    subgoal premises prems
      apply (rule prems(2)[THEN spec[where x=r], THEN spec[where x=res], THEN mp])
      apply (rule exI[where x=\<open>FIC_ledge.mk (1(addr := 1(path \<mapsto> Share n uninitialized)))\<close>], simp add: prems)
      apply (rule exI[where x=\<open>1(path \<mapsto> Share n uninitialized)\<close>], simp)
      apply (rule exI[where x=\<open>Some (Share n uninitialized)\<close>], simp)
      apply (rule exI[where x=\<open>Some (Share 1 uninitialized)\<close>], simp add: prems)
      by (rule exI[where x=\<open>Some uninitialized\<close>], simp)
    . .

lemma \<phi>M_get_res_entry_R_ledge_1[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c F v
      \<lbrace> v \<Ztypecolon> ledge: addr \<^bold>\<rightarrow> path \<^bold>\<rightarrow> \<fish_eye>i Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_res_entry_ledge TY (ledge_ref addr path) F
      \<lbrace> v \<Ztypecolon> ledge: addr \<^bold>\<rightarrow> path \<^bold>\<rightarrow> \<fish_eye>i Identity \<longmapsto> Y \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>\<close>
  using \<phi>M_get_res_entry_R_ledge[where n=1, simplified] .

lemma op_load_ledge:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load_ledge TY raw \<lbrace>
      v \<Ztypecolon> ledge: addr \<^bold>\<rightarrow> path \<^bold>\<rightarrow> n \<Znrres> \<fish_eye>i Identity \<heavy_comma> ledge_ref addr path \<Ztypecolon> Val raw LedgeRef
  \<longmapsto> v \<Ztypecolon> ledge: addr \<^bold>\<rightarrow> path \<^bold>\<rightarrow> n \<Znrres> \<fish_eye>i Identity \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity
\<rbrace>\<close>
  unfolding op_load_ledge_def Premise_def
  by (\<phi>reason, simp, \<phi>reason)


paragraph \<open>Store Field\<close>

lemma  "\<phi>R_set_res_ledge"[\<phi>reason!]:
  \<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c R_ledge.\<phi>R_set_res (map_fun_at (map_fun_at (\<lambda>_. Some (initialized u)) path) lref)
         \<lbrace> v \<Ztypecolon> ledge: lref \<^bold>\<rightarrow> path \<^bold>\<rightarrow> \<fish_eye>i Identity \<longmapsto> \<lambda>\<r>\<e>\<t>. u \<Ztypecolon> ledge: lref \<^bold>\<rightarrow> path \<^bold>\<rightarrow> \<fish_eye>i Identity \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns zero_set_def del: subsetI)
  apply (rule \<phi>Res_Spec_ex_\<S>[where x=\<open>FIC_ledge.mk (1(lref := 1(path := Some (Share 1 (initialized u)))))\<close>])
  subgoal for r res x
  apply (simp add: FIC_ledge.expand[where x=\<open>1(lref := 1(path \<mapsto> x))\<close>, simplified])
  subgoal premises prems proof -
    let \<open>?proc \<subseteq> \<S> (\<lambda>v. ?Spec \<^bold>s\<^bold>u\<^bold>b\<^bold>j ?P_ex \<and> ?P_disj) {}\<close> = ?thesis
    have t1: ?P_ex
      by (rule exI[where x=\<open>1(path \<mapsto> Share 1 (initialized u))\<close>], simp,
          rule exI[where x=\<open>Some (Share 1 (initialized u))\<close>], simp,
          rule exI[where x=\<open>Some (initialized u)\<close>], simp)
    show ?thesis apply (simp add: t1)
      apply (simp add: FIC_ledge.expand_subj[where x=\<open>1(lref := 1(path \<mapsto> initialized u))\<close>, simplified] prems)
      apply (insert prems, rule R_ledge.\<phi>R_set_res[where P="\<lambda>m. path \<in> dom (m lref)"])
      apply (cases lref; clarsimp simp add: Valid_Ledge_def map_fun_at_def dom1_def)
      apply (smt (verit, ccfv_SIG) Collect_cong dom_1 dom_eq_empty_conv option.distinct(1))
      using R_ledge.raw_unit_assertion_implies apply blast
      by assumption
  qed . .

lemma op_store_ledge:
  \<open> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store_ledge TY (\<phi>V_pair rawu rawref) \<lbrace>
      v \<Ztypecolon> ledge: lref \<^bold>\<rightarrow> path \<^bold>\<rightarrow> \<fish_eye>i Identity \<heavy_comma> u \<Ztypecolon> Val rawu Identity \<heavy_comma> ledge_ref lref path \<Ztypecolon> Val rawref LedgeRef
  \<longmapsto> u \<Ztypecolon> ledge: lref \<^bold>\<rightarrow> path \<^bold>\<rightarrow> \<fish_eye>i Identity
\<rbrace>\<close>
  unfolding op_store_ledge_def Premise_def
  by (cases rawref; cases rawu; simp; \<phi>reason, simp add: Premise_def, \<phi>reason, simp add: \<phi>expns, \<phi>reason)


paragraph \<open>Allocation\<close>

lemma op_obj_allocate:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_allocate_ledge
      \<lbrace> Void \<longmapsto> \<lambda>ret. \<exists>*ref. 1 \<Ztypecolon> ledge: ref \<^bold>\<rightarrow> (Identity \<Rrightarrow> \<fish_eye> \<phi>Uninit)\<heavy_comma> ref \<Ztypecolon> Val ret Address \<rbrace>\<close>
  unfolding \<phi>Procedure_\<phi>Res_Spec op_allocate_ledge_def
  apply (clarsimp simp add: \<phi>expns del: subsetI)
  apply (rule R_ledge.\<phi>R_allocate_res_entry)
  apply (clarsimp simp add: Valid_Ledge_def)
  using obj_map_freshness apply blast
  apply (clarsimp simp add: Valid_Ledge_def one_fun_def dom_initial_value_of_class del: subsetI)
  prefer 2 apply assumption
  apply (simp add: \<phi>expns Return_def det_lift_def)
  subgoal for r res k res'
    apply (rule exI[where x=\<open>FIC_ledge.mk (1(k := to_share o (\<lambda>_. Some uninitialized)))\<close>])
    apply (simp add: \<phi>Res_Spec_mult_homo)
    subgoal premises prems proof -
      have t1: \<open>(\<exists>v. 1(k := to_share \<circ> (\<lambda>_. Some uninitialized)) = 1(k := v) \<and>
         (\<forall>va. v va = Some (Share 1 uninitialized)))\<close>
        by fastforce
      show ?thesis
        by (simp add: t1 FIC_ledge.expand_conj[where x=\<open>1(k := \<lambda>_. Some (uninitialized))\<close>, simplified] prems)
    qed . .


subsection \<open>Environment & Balance\<close>

subsubsection \<open>Balance Table\<close>

lemma op_get_balance_raw:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_balance va \<lbrace>
      m \<Ztypecolon> balance: addr \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity \<heavy_comma> addr \<Ztypecolon> Val va Address
  \<longmapsto> m \<Ztypecolon> balance: addr \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> Identity \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l unat m \<Ztypecolon> \<nat>[256]
\<rbrace>\<close>
  unfolding op_get_balance_def
  apply \<phi>reason subgoal proof -
  have t1:
    \<open>V_int.mk (LENGTH('a), unat m) \<in> (unat m \<Ztypecolon> \<nat>[LENGTH('a)]) \<close>
    for m :: \<open>'a::len word\<close>
    by (simp add: \<phi>expns)
  show ?thesis by (simp add: t1[of m, simplified] Premise_def)
qed .

declare [[\<phi>not_define_new_const]]

proc op_get_balance:
  argument \<open>m \<Ztypecolon> balance: addr \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> \<nat>\<^sup>w \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l addr \<Ztypecolon> Address\<close>
  return \<open>m \<Ztypecolon> balance: addr \<^bold>\<rightarrow> n \<Znrres> \<fish_eye> \<nat>\<^sup>w \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l m \<Ztypecolon> \<nat>[256]\<close>
  \<medium_left_bracket>
  have [useful]: \<open>m < 2^ Big 256\<close> using \<phi> by simp
  ;; op_get_balance_raw[where n=n]
  \<medium_right_bracket>. .

declare [[\<phi>not_define_new_const = false]]
  

lemma \<phi>M_set_balance_raw:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_set_balance (\<phi>V_pair va vm) \<lbrace>
      m \<Ztypecolon> balance: addr \<^bold>\<rightarrow> \<fish_eye> Identity \<heavy_comma> m' \<Ztypecolon> Val vm \<nat>[256] \<heavy_comma> addr \<Ztypecolon> Val va Address
  \<longmapsto> (of_nat m') \<Ztypecolon> balance: addr \<^bold>\<rightarrow> \<fish_eye> Identity
\<rbrace>\<close>
  unfolding \<phi>M_set_balance_def
  by (cases vm; simp; \<phi>reason; simp only: \<phi>Nat_expn V_int.dest_mk case_prod_conv,
      rule FIC_balance.\<phi>R_set_res, simp, simp)

declare [[\<phi>not_define_new_const]]

proc \<phi>M_set_balance:
  argument \<open>m \<Ztypecolon> balance: addr \<^bold>\<rightarrow> \<fish_eye> \<nat>\<^sup>w\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l m' \<Ztypecolon> \<nat>[256] \<heavy_comma> \<^bold>v\<^bold>a\<^bold>l addr \<Ztypecolon> Address\<close>
  return \<open>m' \<Ztypecolon> balance: addr \<^bold>\<rightarrow> \<fish_eye> \<nat>\<^sup>w\<close>
  \<medium_left_bracket>
  have [useful]: \<open>m' < 2^ Big 256\<close> using \<phi> by simp
  ;; \<phi>M_set_balance_raw
  \<medium_right_bracket>. .

declare [[\<phi>not_define_new_const = false]]

subsubsection \<open>Globally Available Variables\<close>

lemma
\<open> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_get_environ_word G \<lbrace>
      env \<Ztypecolon> FIC_environ.\<phi> (Agreement (Nonsepable Identity))
  \<longmapsto> env \<Ztypecolon> FIC_environ.\<phi> (Agreement (Nonsepable Identity))\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l unat (G env) \<Ztypecolon> \<nat>[LENGTH('len)]
\<rbrace>\<close>
  for G :: \<open>environ \<Rightarrow> 'len::len word\<close>
  unfolding op_get_environ_word_def \<phi>Procedure_\<phi>Res_Spec
  apply (clarsimp simp add: \<phi>expns del: subsetI, rule R_environ.\<phi>R_get_res_entry[where v=env])
   apply (simp add: FIC_environ.partial_implies)
  by (simp add: \<phi>expns Return_def det_lift_def)

end




(*WIP*)

subsection \<open>Call\<close>

definition \<open>fallback_N = ''fallback''\<close>


definition (in \<phi>empty_sem) \<phi>Transition_Spec_to_Proc_Spec
    :: \<open> ('VAL list, 'a) \<phi>
      \<Rightarrow> ('VAL list, 'b) \<phi>
      \<Rightarrow> ('VAL list, 'VAL list, 'RES_N, 'RES) proc'
      \<Rightarrow> 'TY list \<times> 'TY list
      \<Rightarrow> ('RES_N,'RES) transition
      \<Rightarrow> bool
      \<Rightarrow> prop\<close>
  where \<open>\<phi>Transition_Spec_to_Proc_Spec XV YV proc Tys Tr P
      \<equiv> Trueprop ( \<phi>Type_Spec_for_Deep Tys proc
        \<longrightarrow> Transition_Of' proc \<subseteq> Tr
        \<longrightarrow> P)\<close>

definition (in \<phi>empty_sem) \<phi>Transition_Spec_to_Proc_Spec_cast_type
  where \<open>\<phi>Transition_Spec_to_Proc_Spec_cast_type \<equiv> Trueprop\<close>

lemma (in \<phi>empty)[\<phi>reason 2000 on
      \<open>PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
              ((\<exists>*x. x \<Ztypecolon> Val ?rawvs ?X) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*y. y \<Ztypecolon> Val ?rawvs' ?Y))\<close>]:
  \<open> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
              ((\<exists>*x. x \<Ztypecolon> X) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*y. y \<Ztypecolon> Y))
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
              ((\<exists>*x. x \<Ztypecolon> Val rawvs X) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*y. y \<Ztypecolon> Val rawvs Y))\<close>
  unfolding Imply_def \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  by (simp add: \<phi>expns)

lemma (in \<phi>empty_sem) [\<phi>reason 2000]:
  \<open> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
      ((\<exists>*x. x \<Ztypecolon> Empty_List) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*y. y \<Ztypecolon> Identity <of-types> []))\<close>
  unfolding Imply_def \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  by (clarsimp simp add: \<phi>expns times_list_def)

lemma (in \<phi>empty_sem) [\<phi>reason 2000]:
  \<open>(\<And>x. x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y x \<Ztypecolon> Identity <of-type> Ty)
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
        ((\<exists>*x. x \<Ztypecolon> List_Item T) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*y. y \<Ztypecolon> Identity <of-types> [Ty]))\<close>
  unfolding Imply_def \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  by (clarsimp simp add: \<phi>expns times_list_def)

lemma (in \<phi>empty_sem) [\<phi>reason 2000]:
  \<open>(\<And>x. x \<Ztypecolon> T \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s y x \<Ztypecolon> Identity <of-type> Ty)
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
        ((\<exists>*x. x \<Ztypecolon> X) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*y. y \<Ztypecolon> Identity <of-types> Tys))
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
        ((\<exists>*x. x \<Ztypecolon> (List_Item T \<^emph> X)) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*y. y \<Ztypecolon> Identity <of-types> (Ty#Tys)))\<close>
  unfolding Imply_def \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  by (clarsimp simp add: \<phi>expns times_list_def, blast)

lemma (in \<phi>empty_sem) [\<phi>reason 2000]:
  \<open> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
            ((\<exists>*y. y \<Ztypecolon> Identity <of-types> []) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*x. x \<Ztypecolon> Empty_List))\<close>
  unfolding Imply_def \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  by (clarsimp simp add: \<phi>expns times_list_def)

lemma (in \<phi>empty_sem) [\<phi>reason 2000]:
  \<open> (\<And>y. y \<Ztypecolon> Identity <of-type> Ty \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x y \<Ztypecolon> T)
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
            ((\<exists>*y. y \<Ztypecolon> Identity <of-types> [Ty]) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*x. x \<Ztypecolon> List_Item T))\<close>
  unfolding Imply_def \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  apply (clarsimp simp add: \<phi>expns times_list_def)
  by (metis (no_types, lifting) list_all2_Cons2 list_all2_Nil2)

lemma (in \<phi>empty_sem) [\<phi>reason 2000]:
  \<open> (\<And>y. y \<Ztypecolon> Identity <of-type> Ty \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s x y \<Ztypecolon> T)
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
            ((\<exists>*y. y \<Ztypecolon> Identity <of-types> Tys) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*x. x \<Ztypecolon> X))
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
            ((\<exists>*y. y \<Ztypecolon> Identity <of-types> (Ty#Tys)) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*x. x \<Ztypecolon> (List_Item T \<^emph> X)))\<close>
  unfolding Imply_def \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  apply (clarsimp simp add: \<phi>expns times_list_def)
  by (metis (no_types, lifting) append_Cons list_all2_Cons2 self_append_conv2)

lemma (in \<phi>empty) [\<phi>reason 2000 on
    \<open>PROP \<phi>Transition_Spec_to_Proc_Spec ?XV ?YV ?proc (?Tya,?Tyb) (?X \<longrightarrow>\<^sub>R\<^sub>\<phi> ?Y) ?RET\<close>
]:
  \<open> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
        ((\<exists>*x. x \<Ztypecolon> XV) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*vx. vx \<Ztypecolon> Identity <of-types> Tya))
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec_cast_type
        ((\<exists>*vy. vy \<Ztypecolon> Identity <of-types> Tyb) \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s (\<exists>*x. x \<Ztypecolon> YV))
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec XV YV proc (Tya,Tyb) (X \<longrightarrow>\<^sub>R\<^sub>\<phi> Y)
      (\<^bold>p\<^bold>r\<^bold>o\<^bold>c proc rawv \<lbrace> X\<heavy_comma> (\<exists>*x. x \<Ztypecolon> Val rawv XV) \<longmapsto> \<lambda>ret. Y\<heavy_comma> (\<exists>*x. x \<Ztypecolon> Val ret YV) \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s Y
  \<rbrace>)\<close>
  unfolding \<phi>Transition_Spec_to_Proc_Spec_def \<phi>Type_Spec_for_Deep_def subset_iff Imply_def
      \<phi>Transition_Spec_to_Proc_Spec_cast_type_def
  apply (clarsimp simp add: \<phi>expns Transition_Of_def \<phi>GTS_def \<phi>Procedure_def GTS_def)
  subgoal for comp R s u r x
    apply (cases rawv; cases s; simp add: \<phi>expns sem_value_All sem_value_forall) 
    by (smt (verit, del_insts) mult_1_class.mult_1_right)+ .

lemma (in \<phi>empty) [\<phi>reason 2000 on
    \<open>PROP \<phi>Transition_Spec_to_Proc_Spec ?XV ?YV ?proc ?Tys (?S1 \<inter> ?S2) ?P\<close>
]:
  \<open> PROP \<phi>Transition_Spec_to_Proc_Spec XV YV proc Tys S1 P1
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec XV YV proc Tys S2 P2
\<Longrightarrow> PROP \<phi>Transition_Spec_to_Proc_Spec XV YV proc Tys (S1 \<inter> S2) (P1 \<and> P2)\<close>
  unfolding \<phi>Transition_Spec_to_Proc_Spec_def
  by blast




lemma (in solidity)
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c Public_Methods cls name rawv \<lbrace>
     
     vx \<Ztypecolon> Val rawv (Identity <of-types> fst (method_sig.typ_sig name))
 \<longmapsto> \<lambda>ret. (vy \<Ztypecolon> Val ret (Identity <of-types> snd (method_sig.typ_sig name)) \<^bold>s\<^bold>u\<^bold>b\<^bold>j vy. True)
\<rbrace>\<close>


definition (in solidity_sem) op_raw_call
      :: \<open>'TY method_sig
       \<Rightarrow> ('VAL \<times> 'arg,'ret,'RES_N,'RES) proc'\<close>
  where \<open>op_raw_call fname Arg Ret =
    \<phi>M_caseV (\<lambda>va varg.
    \<phi>M_getV_Address va (\<lambda>addr.
      shallowize_proc Arg Ret (the (Public_Methods (object_ref.class addr) fname)) varg
  ))\<close>
\<comment> \<open>It is nondeterministic! cuz, one cannot assume the height of the calling stack, considering
  send consumes one space in the stack and fails when overflow, so the success of a send operation
  cannot be predicted in the semantics of Solidity!

  Albeit, one can infer from a previous success of an external calling, that the next calling will
  not trigger stack overflow. Other factors like exceptions throwed from the callee are also hard
  to predict.
  To simply, we adopt a slightly stricter policy that, every external call is
  nondeterministic and can fail. It relieves us from counting stack height or gas consumption.\<close>

end