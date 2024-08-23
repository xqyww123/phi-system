theory PhSem_BC_Storage
  imports Phi_System.Resource_Template PhSem_MoV
begin

section \<open>Semantics\<close>

datatype contract = Null | MemBlk nat TY


locale BC_storage =
  partial_map_resource Res \<open>\<lambda>blk. discrete ` Well_Type (typ_of_blk blk)\<close>
  for Res :: "('blk \<Rightarrow> VAL discrete option) resource_entry"
  and typ_of_blk :: \<open>'blk \<Rightarrow> TY\<close>


end