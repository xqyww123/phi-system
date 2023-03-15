theory Phi_Refinement_Algebra
  imports Phi_BI
begin

section \<open>The Algebra of \<open>\<phi>\<close>-Refinement\<close>

locale Transformation_Functor =
  fixes F1 :: \<open>('b,'a1) \<phi> \<Rightarrow> ('c,'a1) \<phi>\<close>
    and F2 :: \<open>('b,'a2) \<phi> \<Rightarrow> ('c,'a2) \<phi>\<close>
  assumes transformation[\<phi>reason 1200]:
      \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> U \<a>\<n>\<d> P \<Longrightarrow> x \<Ztypecolon> F1 T \<i>\<m>\<p>\<l>\<i>\<e>\<s> y \<Ztypecolon> F2 U \<a>\<n>\<d> P\<close>

locale Unit_Homo =
  fixes T :: \<open>('b::one, 'a::one) \<phi>\<close>
  assumes identity_homo: \<open>(1 \<Ztypecolon> T) \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1\<close>

locale Unit_Functor =
  fixes F :: \<open>('b::one, 'a::one) \<phi> \<Rightarrow> ('c::one, 'a) \<phi>\<close>
  assumes identity_functor: \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 \<a>\<n>\<d> P \<Longrightarrow> x \<Ztypecolon> F T \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 \<a>\<n>\<d> P\<close>

(* locale Separation_Homo =
  fixes T :: \<open>('b::sep_magma,'a::times)\<close> *)


end