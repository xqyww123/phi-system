theory PhiSem_Base
  imports Phi_System.PhiSem_Formalization_Tools2
begin

section \<open>Semantics Base\<close>

subsection \<open>Type Classes for Common Reasoning Strategies\<close>

(*
definition Atomic_SemTyp :: \<open>TY \<Rightarrow> bool\<close>
  where \<open>Atomic_SemTyp TY \<equiv> True\<close>

\<phi>reasoner_group Atomic_SemTyp = (1000, [1000, 2000]) for \<open>Atomic_SemTyp TY\<close>
  \<open>testing whether \<open>TY\<close> is an aomitc semantic type, i.e., integers, booleans, floats, but except
    arrays and records\<close>

declare [[
  \<phi>reason_default_pattern \<open>Atomic_SemTyp ?TY\<close> \<Rightarrow> \<open>Atomic_SemTyp ?TY\<close> (100),
  \<phi>default_reasoner_group \<open>Atomic_SemTyp _\<close> : %Atomic_SemTyp (100)
]]
*)


end