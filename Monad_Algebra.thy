theory Monad_Algebra
  imports Main
begin

locale monad =
  fixes return :: \<open>'a \<Rightarrow> 'b\<close>
    and bind :: \<open>'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b\<close> ("_ \<bind>/ _" [76,75] 75)
  assumes return_identity_left [simp]: \<open>return x \<bind> f = f x\<close>
    and   return_identity_right[simp]: \<open>m \<bind> return = m\<close>
    and   bind_associtive: \<open>m \<bind> (\<lambda>x. f x \<bind> g) = (m \<bind> f) \<bind> g\<close>
begin

inductive_set M_rtrancl :: "('a \<Rightarrow> 'b) set \<Rightarrow> ('a \<Rightarrow> 'b) set"  ("(_\<^sup>M*)" [1000] 999)
  for r :: "('a \<Rightarrow> 'b) set"
  where
    M_rtrancl_refl [intro!, Pure.intro!, simp]: "return \<in> r\<^sup>M*"
  | M_rtrancl_into_rtrancl [Pure.intro]: "f \<in> r\<^sup>M* \<Longrightarrow> g \<in> r \<Longrightarrow> (\<lambda>x. f x \<bind> g) \<in> r\<^sup>M*"

inductive_set trancl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(_\<^sup>+)" [1000] 999)
  for r :: "('a \<times> 'a) set"
  where
    r_into_trancl [intro, Pure.intro]: "(a, b) \<in> r \<Longrightarrow> (a, b) \<in> r\<^sup>+"
  | trancl_into_trancl [Pure.intro]: "(a, b) \<in> r\<^sup>+ \<Longrightarrow> (b, c) \<in> r \<Longrightarrow> (a, c) \<in> r\<^sup>+"

notation
  rtranclp  ("(_\<^sup>*\<^sup>*)" [1000] 1000) and
  tranclp  ("(_\<^sup>+\<^sup>+)" [1000] 1000)


end

end