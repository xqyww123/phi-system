theory PhiSem_Void
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantics\<close>

debt_axiomatization sem_void_T :: TY ("\<void>")
               and voidV      :: VAL
  where WT_void  [simp]: \<open>Well_Type \<void> = {voidV} \<close>
    and Zero_void[simp]: \<open>Zero \<void> = Some voidV\<close>

lemma void_neq_poison[simp]: \<open>\<void> \<noteq> \<poison>\<close>
  using WT_void by force

lemma poison_neq_void[simp]: \<open>\<poison> \<noteq> \<void>\<close>
  using void_neq_poison by force 

lemma has_Zero_void[simp]:
  \<open> has_Zero \<void> \<close>
  unfolding has_Zero_def
  by simp


end