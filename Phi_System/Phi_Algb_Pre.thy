section \<open>Preliminary for \<open>\<phi>\<close>-Type Algebra\<close>

theory Phi_Algb_Pre
  imports IDE_CP_Reasoning1
          Phi_Algebras.Map_of_Tree
begin 

subsection \<open>Auxiliary Annotations\<close>

definition scalar_mult :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close> where \<open>scalar_mult f \<equiv> f\<close>
  \<comment> \<open>A tag annotating the function is a scalar multiplication so that the automation for semimodules
      will be activated. It also distinguishes the function part and the parameter part, so that
      resolves multi-unification.\<close>

lemma [\<phi>reason 1000]:
  \<open> f = g
\<Longrightarrow> u = v
\<Longrightarrow> scalar_mult f u = scalar_mult g v\<close>
  unfolding scalar_mult_def by simp

lemma [\<phi>reason 1000]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> f = g
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> u = v
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> scalar_mult f u = scalar_mult g v\<close>
  unfolding scalar_mult_def Premise_def by simp


subsection \<open>Configuration of Existing Procedures\<close>

declare [[\<phi>reason_default_pattern \<open>module_scalar_assoc ?\<psi> _\<close> \<Rightarrow> \<open>module_scalar_assoc ?\<psi> _\<close>   (100)
                              and \<open>module_scalar_identity ?\<psi>\<close> \<Rightarrow> \<open>module_scalar_identity ?\<psi>\<close> (100)]]

subsubsection \<open>Separation Algebra\<close>

paragraph \<open>Setup Reasoning Rules\<close>

declare (in homo_one) homo_one_axioms[\<phi>reason 1000]

lemma extraction_homo_one[\<phi>premise_extraction]:
  \<open>homo_one \<psi> \<equiv> \<psi> 1 = 1 \<and> True\<close>
  unfolding homo_one_def
  by simp

declare (in homo_sep_mult) homo_sep_mult_axioms [\<phi>reason 1000]

declare (in closed_homo_sep_disj) closed_homo_sep_disj_axioms [\<phi>reason 1000]

subparagraph \<open>homo_mul_carrier\<close>

declare (in homo_mul_carrier) homo_mul_carrier_axioms[\<phi>reason 1000]

lemma prem_extract_homo_mul_carrier:
  \<open>homo_mul_carrier \<psi> \<equiv> (\<forall>x. mul_carrier x \<longrightarrow> mul_carrier (\<psi> x)) \<and> True\<close>
  unfolding homo_mul_carrier_def
  by simp

lemma [\<phi>reason default 1]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>x. mul_carrier x \<longrightarrow> mul_carrier (\<psi> x))
\<Longrightarrow> homo_mul_carrier \<psi>\<close>
  unfolding homo_mul_carrier_def Premise_def .

lemma [\<phi>reason no explorative backtrack 0]:
  \<open> TRACE_FAIL TEXT(\<open>Fail to show the multiplicative carrier homomorphism of\<close> \<psi>)
\<Longrightarrow> homo_mul_carrier \<psi> \<close>
  unfolding TRACE_FAIL_def
  by blast

paragraph \<open>Reasoning Hierarchy\<close>

lemmas [\<phi>reason 20] =
        closed_homo_sep.intro
        homo_sep.intro

lemma [\<phi>reason 10]:
  \<open> closed_homo_sep_disj \<psi>
\<Longrightarrow> homo_sep_disj \<psi>\<close>
  unfolding homo_sep_disj_def closed_homo_sep_disj_def
  by blast

lemmas [\<phi>reason 30] =
        closed_homo_sep_disj_comp
        homo_sep_disj_comp
        homo_sep_comp
        homo_sep_mult_comp


subsection \<open>Constant Functions\<close>

definition \<open>constant_1 \<psi> \<equiv> (\<forall>x. \<psi> x = 1)\<close>

lemma [\<phi>premise_extraction]:
  \<open> constant_1 \<psi> \<equiv> (\<forall>x. \<psi> x = 1) \<and> True \<close>
  unfolding constant_1_def atomize_eq
  by simp

lemma [\<phi>reason default 1]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>x. \<psi> x = 1)
\<Longrightarrow> constant_1 \<psi>\<close>
  unfolding constant_1_def Premise_def
  by simp

subsection \<open>Arithmetic Evaluation\<close>

consts \<A>arith_eval :: action

subsubsection \<open>Partial Addition\<close>

text \<open>Solving \<open>?d + a = ?b + c @action \<A>arith_eval\<close>\<close>


subsection \<open>Preset Properties for Specific Elements\<close>

subsubsection \<open>Identity Function\<close>

lemmas [\<phi>reason 1000] =
    closed_homo_sep_disj_id
    homo_sep_disj_id
    homo_sep_mult_id
    homo_one_id
    homo_sep_id
    closed_homo_sep
    homo_mul_carrier_id

subsubsection \<open>Functional Pointwise\<close>

lemma homo_mul_carrier_fun_upd [\<phi>reason 1100]:
  \<open>homo_mul_carrier (fun_upd (1::'k \<Rightarrow> 'a::sep_carrier_1) k)\<close>
  unfolding homo_mul_carrier_def
  by simp

lemma homo_mul_carrier_fun_upd' [\<phi>reason 1100]:
  \<open> homo_mul_carrier f
\<Longrightarrow> homo_mul_carrier (\<lambda>x. fun_upd (1 :: 'k \<Rightarrow> 'a::sep_carrier_1) k (f x))\<close>
  unfolding homo_mul_carrier_def
  by clarsimp

lemma closed_homo_sep_disj_fun_upd [\<phi>reason 1100]:
  \<open>closed_homo_sep_disj (fun_upd (1 :: 'k \<Rightarrow> 'a::sep_magma_1) k)\<close>
  unfolding closed_homo_sep_disj_def
  by (simp add: sep_disj_fun_def)

lemma closed_homo_sep_disj_fun_upd' [\<phi>reason 1000]:
  \<open> closed_homo_sep_disj f
\<Longrightarrow> closed_homo_sep_disj (\<lambda>x. fun_upd (1 :: 'k \<Rightarrow> 'a::sep_magma_1) k (f x))\<close>
  unfolding closed_homo_sep_disj_def
  by (simp add: sep_disj_fun_def)

lemma homo_sep_mult_fun_upd[\<phi>reason 1100]:
  \<open>homo_sep_mult (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k)\<close>
  unfolding homo_sep_mult_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_sep_mult_fun_upd'[\<phi>reason 100]:
  \<open> homo_sep_mult f
\<Longrightarrow> homo_sep_mult (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x))\<close>
  unfolding homo_sep_mult_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_one_fun_upd[\<phi>reason 1100]:
  \<open>homo_one (fun_upd 1 k)\<close>
  unfolding homo_one_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_one_fun_upd'[\<phi>reason 1000]:
  \<open> homo_one f
\<Longrightarrow> homo_one (\<lambda>x. fun_upd 1 k (f x))\<close>
  unfolding homo_one_def
  by (simp add: fun_eq_iff times_fun_def)

lemma homo_sep_fun_upd[\<phi>reason 1100]:
  \<open> homo_sep (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k) \<close>
  by (rule homo_sep.intro; simp add: homo_sep_mult_fun_upd homo_sep_disj_def)

lemma homo_sep_fun_upd'[\<phi>reason 1000]:
  \<open> homo_sep f
\<Longrightarrow> homo_sep (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x)) \<close>
  unfolding homo_sep_def
  by (simp add: homo_sep_mult_fun_upd' homo_sep_disj_def)

lemma closed_homo_sep_fun_upd[\<phi>reason 1100]:
  \<open> closed_homo_sep (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k) \<close>
  by (rule closed_homo_sep.intro; simp add: homo_sep_fun_upd closed_homo_sep_disj_fun_upd)

lemma closed_homo_sep_fun_upd'[\<phi>reason 1000]:
  \<open> closed_homo_sep f
\<Longrightarrow> closed_homo_sep (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x)) \<close>
  unfolding closed_homo_sep_def
  by (simp add: closed_homo_sep_disj_fun_upd' homo_sep_fun_upd')

lemma [\<phi>reason 1000]:
  \<open> constant_1 \<psi>
\<Longrightarrow> constant_1 (\<lambda>x. fun_upd 1 k (\<psi> x))\<close>
  unfolding constant_1_def
  by simp


subsubsection \<open>Push map\<close>

declare homo_mul_carrier_push_map [\<phi>reason 1000]
        closed_homo_sep_disj_push_map [\<phi>reason 1000]
        homo_sep_mult_push_map [\<phi>reason 1000]
        homo_one_push_map [\<phi>reason 1000]
        module_scalar_identity_push_map [\<phi>reason 1000]
        module_scalar_assoc_push_map [\<phi>reason 1000]

subsubsection \<open>Share Division\<close>

lemma homo_mul_carrier_share [\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_mul_carrier ((\<odivr>) n :: 'a::share_carrier \<Rightarrow> 'a)\<close>
  unfolding homo_mul_carrier_def Premise_def
  by (clarsimp simp add: share_carrier_closed)

lemma homo_mul_carrier_share_1[\<phi>reason 1100]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_mul_carrier ((\<odivr>) n :: 'a::share_carrier_1 \<Rightarrow> 'a)\<close>
  unfolding homo_mul_carrier_def Premise_def
  by (clarsimp simp add: share_carrier_closed_1)

lemma homo_one_share[\<phi>reason 1000]:
  \<open>homo_one ((\<odivr>) n :: 'a::share_one \<Rightarrow> 'a)\<close>
  unfolding homo_one_def
  by simp

lemma homo_sep_mult_share0[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep_mult ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_mult_def Premise_def
  by (simp add: share_sep_right_distrib_0)

lemma homo_sep_mult_share[\<phi>reason 1010]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_sep_mult ((\<odivr>) n :: 'a::share_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_mult_def Premise_def
  by (simp add: share_sep_right_distrib)

lemma homo_sep_disj_share0[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep_disj ((\<odivr>) n :: 'a::share_sep_disj \<Rightarrow> 'a)\<close>
  unfolding homo_sep_disj_def Premise_def
  by simp

lemma homo_sep_disj_share [\<phi>reason 1010]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_sep_disj ((\<odivr>) n :: 'a::{share_sep_disj, share_one, sep_magma_1} \<Rightarrow> 'a)\<close>
  unfolding homo_sep_disj_def Premise_def
  by (cases \<open>n = 0\<close>; simp)

lemma closed_homo_sep_disj_share0[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> closed_homo_sep_disj ((\<odivr>) n :: 'a::share_sep_disj \<Rightarrow> 'a)\<close>
  unfolding closed_homo_sep_disj_def Premise_def
  by simp

lemma homo_sep_share0[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_def Premise_def
  by (simp add: homo_sep_mult_share0 homo_sep_disj_share0)

lemma homo_sep_share [\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 \<le> n \<Longrightarrow> homo_sep ((\<odivr>) n :: 'a::share_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_def Premise_def
  by (simp add: homo_sep_mult_share homo_sep_disj_share)

lemma closed_homo_sep_share[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> closed_homo_sep ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding closed_homo_sep_def Premise_def
  by (simp add: homo_sep_share0 closed_homo_sep_disj_share0)

lemma [\<phi>reason 1000]:
  \<open>constant_1 ((\<odivr>) 0 :: 'a::share_one \<Rightarrow> 'a)\<close>
  unfolding constant_1_def
  by simp

declare module_scalar_assoc_share0   [\<phi>reason 1000, assertion_simps]
        module_scalar_assoc_share    [\<phi>reason 1100, assertion_simps]
        module_scalar_identity_share [\<phi>reason 1000, assertion_simps]


subsubsection \<open>Annotation of Scalar Multiplication\<close>

lemma [\<phi>reason 1000]:
  \<open> homo_mul_carrier (\<psi> s)
\<Longrightarrow> homo_mul_carrier (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason 1000]:
  \<open> homo_one (\<psi> s)
\<Longrightarrow> homo_one (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason 1000]:
  \<open> homo_sep_mult (\<psi> s)
\<Longrightarrow> homo_sep_mult (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason 1000]:
  \<open> homo_sep_disj (\<psi> s)
\<Longrightarrow> homo_sep_disj (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason 1000]:
  \<open> closed_homo_sep_disj (\<psi> s)
\<Longrightarrow> closed_homo_sep_disj (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason 1000]:
  \<open> homo_sep (\<psi> s)
\<Longrightarrow> homo_sep (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason 1000]:
  \<open> closed_homo_sep (\<psi> s)
\<Longrightarrow> closed_homo_sep (scalar_mult \<psi> s) \<close>
  unfolding scalar_mult_def .

lemma [\<phi>reason 1000]:
  \<open> constant_1 (\<psi> s)
\<Longrightarrow> constant_1 (scalar_mult \<psi> s)\<close>
  unfolding scalar_mult_def
  by simp


end