theory SmartContract
  imports NuSys
begin

section \<open>Semantic\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype sc_ty = std_ty +
  T_LedgeRef   :: unit
  T_Mapping    :: unit
  T_ChainArray :: unit

subsubsection \<open>Address\<close>

datatype 'TY contract_class = contract_class (name: string) (type: 'TY)
hide_const (open) name type

datatype 'TY address_type = IT_contract \<open>'TY contract_class\<close> | IT_user

datatype 'TY address = address ("type": \<open>'TY address_type\<close>) (nonce: nat)
hide_const (open) "type" nonce


subsubsection \<open>Value\<close>

datatype 'VAL storage_loc = SL_Field string | SL_MappingElement 'VAL | SL_ArrayElement nat
type_synonym ('TY,'VAL) storage_index = \<open>'TY address \<times> 'VAL storage_loc list\<close>

virtual_datatype 'TY sc_val :: "nonsepable_semigroup" = 'TY std_val +
  V_Mapping    :: \<open>(('TY,'self) storage_index \<times> 'TY \<times> 'TY)\<close>
  V_LedgeArray :: \<open>(('TY,'self) storage_index \<times> 'TY)\<close>

subsubsection \<open>Pre-model\<close>

locale sc_sem_pre =
    std   where TYPES = TYPES
  + sc_ty where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ std_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N => 'VAL::nonsepable_semigroup)
      \<times> ('RES_N => 'RES::comm_monoid_mult)
      \<times> ('FIC_N \<Rightarrow> 'FIC::{comm_monoid_mult,no_inverse})) itself\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>

fixes ledge_idx_settings :: \<open>()\<close>



subsection \<open>Resource\<close>

subsubsection \<open>\<close>



type_synonym ('TY,'VAL) R_ledge = \<open>(('TY,'VAL) storage_index \<rightharpoonup> 'VAL) ?\<close>
  \<comment> \<open>Zero element is the result of applying monoid operation on undefined operands.
      If every storage location under an address is None, this address is free and not occupied.
      For a non-free address, None in its space means invalid storage location.

      This algebric structure is separable.
      Under the context of separation, None means unspecified.
      A monoid for a specified part and another one where that part is unspecified can be combined\<close>
type_synonym ('TY,'VAL) R_mem = \<open>('TY,'VAL) R_mem' ?\<close>
type_synonym ('TY,'VAL) R_var = \<open>(varname \<rightharpoonup> 'VAL) ?\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) sc_res = ('VAL,'TY) std_res +
  R_ledge :: \<open>('TY,'VAL) R_ledge\<close>


end