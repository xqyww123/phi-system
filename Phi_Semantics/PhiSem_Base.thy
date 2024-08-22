theory PhiSem_Base
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantics Base\<close>

subsection \<open>Type Classes for Common Reasoning Strategies\<close>


\<phi>type_def Uninit_Val :: \<open>TY \<Rightarrow> (VAL, unit) \<phi>\<close> ("\<top>[_]")
  where \<open>x \<Ztypecolon> \<top>[TY] \<equiv> v \<Ztypecolon> Itself \<s>\<u>\<b>\<j> v. v \<in> Well_Type TY\<close>
  deriving Basic

(*
term x

lemma
  \<open>\<exists>c. c \<in> Well_Type TY \<longleftrightarrow> TY \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
*)

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