theory PhiSem_Procedure_Table
  imports Phi_System.PhiSem_Formalization_Tools
begin

type_synonym proc_index = nat

consts proc_runtime_table :: \<open>proc_index \<rightharpoonup> 'a proc\<close>

specification (proc_runtime_table)
  proc_runtime_table_inj:
        \<open>inj_on (proc_runtime_table::proc_index \<rightharpoonup> 'a proc)
                    (dom (proc_runtime_table::proc_index \<rightharpoonup> 'a proc))\<close>
  proc_runtime_table_0: \<open>proc_runtime_table 0 = None\<close>
  by (rule exI[where x=\<open>\<lambda>_. None\<close>]; simp)

text \<open>A table assigning id to all procedures encountered during an execution trace.\<close>


(*
definition proc_of :: \<open>'a proc \<Rightarrow> proc_index proc\<close>
  where \<open>proc_of F = (if )\<close> *)


end