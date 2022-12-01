section \<open>\<phi>-BI\<close>

theory Phi_BI
  imports BI
begin

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete set "

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a set" (infix "\<Ztypecolon>" 20) where " (x \<Ztypecolon> T) = (T x)"

lemma typing_inhabited: "p \<in> (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (x \<Ztypecolon> T)"
  unfolding Inhabited_def \<phi>Type_def by blast

lemma \<phi>Type_eqI:
  \<open>(\<forall>x p. p \<in> (x \<Ztypecolon> a) \<longleftrightarrow> p \<in> (x \<Ztypecolon> b)) \<Longrightarrow> a = b\<close>
  unfolding \<phi>Type_def by blast

ML_file \<open>library/NuSimpCongruence.ML\<close>

end