theory Unital_Homo
  imports Algebras
begin

section \<open>Unital Homomorphism\<close>

typedef (overloaded) ('a::one,'b::one) unital_homo
    = \<open>Collect (homo_one :: ('a \<Rightarrow> 'b) \<Rightarrow> bool)\<close>
  morphisms apply_unital_homo Unital_Homo
  by (rule exI[where x = \<open>\<lambda>_. 1\<close>]) (simp add:sep_mult_commute homo_one_def)

setup_lifting type_definition_unital_homo

lemmas unital_homo_inverse[simp] = Unital_Homo_inverse[simplified]

lemma apply_unital_homo_1[simp]: "apply_unital_homo I 1 = 1"
  using homo_one_def apply_unital_homo by blast

lemma unital_homo_eq_I[intro!]:
  \<open>apply_unital_homo x = apply_unital_homo y \<Longrightarrow> x = y\<close>
  by (simp add: apply_unital_homo_inject)

lemma apply_unital_homo__homo_one:
  \<open>homo_one (apply_unital_homo x)\<close>
  by (simp add: homo_one_def)

lift_definition unital_homo_composition
    :: \<open>('a::one,'b::one) unital_homo \<Rightarrow> ('c::one,'a) unital_homo \<Rightarrow> ('c,'b) unital_homo\<close>
    (infixl "\<circ>\<^sub>U\<^sub>H" 55)
  is \<open>(o) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b)\<close>
  by (clarsimp simp add: homo_one_def)

notation unital_homo_composition (infixl "o\<^sub>U\<^sub>H" 55)

lemma apply_unital_homo_comp[simp]:
  \<open>apply_unital_homo (f \<circ>\<^sub>U\<^sub>H g) = apply_unital_homo f o apply_unital_homo g\<close>
  by (transfer; clarsimp)


end