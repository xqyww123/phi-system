theory PhSem_BC_Storage
  imports Phi_System.Resource_Template PhSem_MoV
begin

section \<open>Semantics\<close>

declare [[typedef_overloaded]]

datatype contract = Null | Contract nat TY

declare [[typedef_overloaded = false]]

setup \<open>Sign.mandatory_path "RES"\<close>

type_synonym storage = \<open>contract \<rightharpoonup> VAL discrete\<close>

setup \<open>Sign.parent_path\<close>

resource_space aggregate_mem =
  aggregate_mem :: \<open>{h::RES.storage. finite (dom h) \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` discrete ` Well_Type (block.layout seg))}\<close>
  (MoV_res Byte_Rep_of_Val \<open>block.layout\<close>)
  by (standard; simp)



end