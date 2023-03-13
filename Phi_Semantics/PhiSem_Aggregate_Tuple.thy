theory PhiSem_Aggregate_Tuple
  imports PhiSem_Aggregate_Base
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype tuple_ty = \<phi>empty_ty +
  tup     :: \<open>'self list\<close>
  array   :: \<open>'self \<times> nat\<close>


end