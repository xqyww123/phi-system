chapter \<open>Domainoid\<close>

theory Phi_Domainoid
  imports Phi_BI Phi_Algb_Pre
begin

section \<open>Motivation \& Introduction\<close>

text \<open>The section covers two mechanisms about reasoning the separation disjunction between two given assertions,
i.e., (for the first mechanism) whether all of, and (for the second mechanism) whether exists some,
two objects \<open>u \<Turnstile> A\<close> and \<open>v \<Turnstile> B\<close> satisfying the given assertions \<open>A\<close> and \<open>B\<close>,
have defined separation operation between them, denoted by \<open>u ## v\<close> following the paper by Calcagno.
The motivation to infer such compatibility is based on two reasons.

\<^enum> The first mechanism focuses on the following property,
\<close>

definition Separation_Disj :: \<open>('a::sep_magma \<Rightarrow> 'b::sep_magma) \<Rightarrow> 'a BI \<Rightarrow> 'a BI \<Rightarrow> bool\<close>
  where \<open>Separation_Disj \<psi> X Y \<longleftrightarrow> (\<forall>u v. u \<Turnstile> X \<and> v \<Turnstile> Y \<and> \<psi> u ## \<psi> v \<longrightarrow> u ## v)\<close>

definition Separation_Disj\<^sub>\<phi> :: \<open>('ca::sep_magma \<Rightarrow> 'cb::sep_magma) \<Rightarrow> ('ay \<times> 'ax) set \<Rightarrow> ('ca, 'ax) \<phi> \<Rightarrow> ('ca, 'ay) \<phi> \<Rightarrow> bool\<close>
  where \<open>Separation_Disj\<^sub>\<phi> \<psi> D T U \<longleftrightarrow> (\<forall>x y. (y,x) \<in> D \<longrightarrow> Separation_Disj \<psi> (x \<Ztypecolon> T) (y \<Ztypecolon> U))\<close>

declare [[
\<phi>reason_default_pattern
      \<open>Separation_Disj ?\<psi> ?A ?B\<close> \<Rightarrow> \<open>Separation_Disj ?\<psi> ?A ?B\<close> (100)
  and \<open>Separation_Disj\<^sub>\<phi> ?\<psi> _ ?W ?T\<close> \<Rightarrow> \<open>Separation_Disj\<^sub>\<phi> ?\<psi> _ _ ?T\<close> (130)
]]

text \<open>
  The standard homomorphism from a partial algebra \<open>\<A>\<close> to another \<open>\<B>\<close> only assumes the group operation
  defined (between two certain elements) in \<open>\<A>\<close>, is also defined in \<open>\<B>\<close>, but not reversely, i.e.,
  \<open>u ## v \<longrightarrow> \<psi>(u) ## \<psi>(v)   but not generally   \<psi>(u) ## \<psi>(v) \<longrightarrow> u ## v \<close>
  It blocks the \<open>x \<Ztypecolon> (\<psi> \<Zcomp> T) \<^emph> (\<psi> \<Zcomp> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> zip(x) \<Ztypecolon> (\<psi> \<Zcomp> T \<^emph> U)\<close>, one side of the \<phi>-type separation homomorphism.

  Certainly, to circumvent it, we can ask a stronger assumption i.e. closed homomorphism,
  but not all homomorphisms are closed. An example is super permission...

  As a remedy, \<open>Separation_Disj\<^sub>\<psi> A B\<close> allows the \<phi>-type transformation for non-closed separation homomorphism.

  To enable \<open>x \<Ztypecolon> (\<psi> \<Zcomp> T) \<^emph> (\<psi> \<Zcomp> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> zip(x) \<Ztypecolon> \<psi> \<Zcomp> (T \<^emph> U)\<close>, the weakest condition is
  \<open>SD\<^sub>\<psi>'(A,B) \<longleftrightarrow> (\<forall>u v. u \<Turnstile> A \<and> v \<Turnstile> B \<and> \<psi> u ## \<psi> v \<longrightarrow> \<exists>u' v'. u' \<Turnstile> A \<and> v' \<Turnstile> B \<and> \<psi>(u) * \<psi>(v) = \<psi>(u') * \<psi>(v') \<and> u' ## v')\<close>
  However, \<open>SD\<^sub>\<psi>'(A,B)\<close> is difficult to automate and \<open>\<psi>(u) * \<psi>(v) = \<psi>(u') * \<psi>(v')\<close> is hard to deal.
  We fail to find a reasoning rule splitting \<open>SD\<^sub>\<psi>'(A, B\<^sub>1 \<^emph> B\<^sub>2)\<close> to the respective cases for \<open>B\<^sub>1\<close> and \<open>B\<^sub>2\<close>.
  Due to this, we apply an approximation assuming the \<open>u',v'\<close> are equal to the \<open>u,v\<close>, and then
  we get the form of \<open>Separation_Disj\<^sub>\<psi>\<close> and it has simpler reasoning rules such as
  \<open> Separation_Disj \<psi> A B\<^sub>1
\<Longrightarrow> Separation_Disj \<psi> A B\<^sub>2
\<Longrightarrow> Separation_Disj \<psi> A (B\<^sub>1 * B\<^sub>2)\<close> for separation homomorphism \<open>\<psi>\<close>.

  See \<section>\<open>Domainoid gives Separation_Disj\<close>

\<^enum> The second mechanism focuses on satisfaction of multiplicative conjunction, of the following form,
  \<open>Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> with_what_condition \<longrightarrow> Inhabited (A * B)\<close>

  The implication reasoning \<open>Inhabited A \<longrightarrow> P\<close> infers a weaker but simpler approximation
  of the pure fact implied inside \<open>A\<close>.
  However, only the weakening part is not enough for \<phi>-types of mappings such as
  \<open>f \<Ztypecolon> T \<Rrightarrow> U := {g. (\<forall>u x. u \<Turnstile> x \<Ztypecolon> T \<longrightarrow> g(y) \<Turnstile> f(x) \<Ztypecolon> U)}\<close> (forward simulation)
  whose domain \<phi>-type \<open>T\<close> is contravariant.
  To extract its implication, the dual of the implication reasoning is required, namely satisfaction reasoning.
  It infers a stronger approximation \<open>Q\<close> such that \<open>Q \<longrightarrow> Inhabited A\<close> for a given assertion \<open>A\<close>.
  By it, we can complete the implication rule of \<open>f \<Ztypecolon> T \<Rrightarrow> U\<close>,
  \<open> (\<And>x. Q x \<longrightarrow> Inhabited (x \<Ztypecolon> T))
\<Longrightarrow> (\<And>x. Inhabited (x \<Ztypecolon> T) \<rightarrow> P x)
\<Longrightarrow> (\<And>y. Inhabited (y \<Ztypecolon> U) \<rightarrow> P' y)
\<Longrightarrow> Inhabited (f \<Ztypecolon> T \<Rrightarrow> U) \<longrightarrow> (\<forall>x. Q x \<longrightarrow> P x \<and> P' (f x))\<close>.
  
  The rules of satisfaction reasoning for logical connectives are given where???, except those
  for conjunctive operators (\<open>\<and>\<close> and \<open>*\<close>).
  For \<open>\<and>\<close>, it is due to that the inhabitance of each side of the conjunction
  does not imply the inhabitance of the both sides, because the residents may not equal.
  For \<open>*\<close>, it is due to, though we have two residents \<open>u \<Turnstile> A\<close> and \<open>v \<Turnstile> B\<close> for each assertions,
  we do not know if \<open>u ## v\<close>, so we cannot deduce \<open>u * v \<Turnstile> A * B\<close>.

  Even though \<open>\<and>\<close> is less-intuitive and rarely used under our interpretation of data refinement,
  multiplicative conjunction is essential,
  especially for example, when the key of the map is a tuple and the tuple fields are connected by \<open>*\<close>.

  See \<section>\<open>Domainoid gives Satisfaction of Separation Conjunction\<close>
\<close>

text \<open>
The satisfaction reasoning of multiplicative conjunctions, together with the above \<open>Separation_Disj\<^sub>\<psi>\<close>,
relies on the notion of \<^emph>\<open>domainoid\<close>, which is invented in order to reason the separation disjunction
from the abstract side of \<phi>-types, particularly by means of \<open>Domainoid_Homo\<close> presented later.
\<close>


section \<open>The Algebra of Domainoid\<close>

subsection \<open>Domainoid\<close>

type_synonym ('a,'d) domainoid = \<open> 'a \<Rightarrow> 'd \<close>
  \<comment> \<open>A forgetful functor that extracts out domains and trims off data\<close>

definition domainoid :: \<open>'a itself \<Rightarrow> ('a::sep_magma,'d::sep_magma) domainoid \<Rightarrow> bool\<close>
  where \<open>domainoid _ \<delta> \<longleftrightarrow> closed_homo_sep \<delta>\<close>

text \<open>A domainoid extraction \<open>\<delta>\<close> is a closed homomorphism and also a forgetful functor that extracts the domain
  parts and forgets the data parts of a SA, such that \<open>\<delta>(x) ## \<delta>(y) \<longleftrightarrow> x ## y\<close> is sufficient to
  determine the separation disjunction \<open>x ## y\<close>, but of a simpler expression.
  Usually, \<open>\<delta>(x)\<close> is the domain of the resource \<open>x\<close>, such as the address of a memory object,
  but it can be others like \<open>address \<rightarrow> permission\<close> the permission map of a sharing memory
  \<open>address \<rightarrow> permission \<times> value\<close>. Considering this, we call it domain-oid extraction or simply domainoid.

  The domainoid of an algebra \<open>A\<close> can be defined as the terminal object of the coslice
  \<open>CH_Group/A\<close> of the category \<open>CH_Group\<close> of closed homomorphisms, i.e., the homomorphism to
  the minimal algebra that just preserves the domain of the group operation of \<open>A\<close>.
  However, as the domainoid only means to be an intermediate representation helping the reasoning, we
  relax the definition to be any closed homomorphism that helps evaluating the separation disjunction.

  By extracting the domainoids of two \<phi>-type assertions or other assertions, we can determine the
  separation disjunction between the two assertions without involving and reducing to
  concrete representations of the resources, as usually we only abstract the data and leave the
  resource identifiers untouched.

  With abbreviation \<open>domainoid d \<triangleq> closed_homo_sep \<delta>\<close> we emphasize \<open>\<delta>\<close> is a domainoid.

  Modality \<open>\<DD>[d] S \<triangleq> (\<delta> u \<Ztypecolon> Itself \<s>\<u>\<b>\<j> u. u \<Turnstile> S)\<close> for domaionoid extraction \<open>\<delta>\<close> maps
  an assertion \<open>S\<close> to the domainoids of its resources, specified still by a BI assertion.
  The modality is homomorphic over all logical connectives except additive conjunctions (including universal quantification).
  Though domainoid is designed to solve satisfaction of multiplicative conjunction, it still can do nothing
  to additive conjunctions.

  For mapping the domainoid functor onto the abstract domain of a \<phi>-type \<open>x \<Ztypecolon> T\<close>,
  there are lower and upper homomorphisms giving stronger and lower approximations respectively
  for domainoid \<open>d\<close>,
  \<open>Domainoid_Homo\<^sub>L d T d' \<longleftrightarrow> (\<forall>x. d' x \<longrightarrow> \<Psi>[d] (x \<Ztypecolon> T) )\<close>
  \<open>Domainoid_Homo\<^sub>U d T d' \<longleftrightarrow> (\<forall>x. \<Psi>[d] (x \<Ztypecolon> T) \<longrightarrow> d' x )\<close>
  We use approximations in case of the precise expression is too complicated.

  The lower homomorphism is used for deducing the satisfaction of multiplicative conjunction.
  The upper homomorphism is for enabling transformation of non-closed separation homomorphism.
\<close>

definition Domainoid_Modality ("\<DD>[_]" [10] 1000) where \<open>\<DD>[\<delta>] = \<Psi>[\<delta>]\<close>
  \<comment> \<open>\<open>\<Psi>[\<psi>] (x \<Ztypecolon> T) \<equiv> x \<Ztypecolon> \<phi>Fun \<psi> \<Zcomp> T\<close>, therefore \<open>\<phi>Fun \<psi> \<Zcomp> T\<close> is always an exact solution for
      evaluating \<open>\<Psi>[\<psi>] (x \<Ztypecolon> T)\<close>. However, in the case of domainoid extraction, this is not a
      final expression directly giving the domainoids of resources. We want a direct expression
      even if just an upper or lower approximation. Due to this, here
      we introduce a differentiated syntax to emphasize the intention of extracting domainoid,
      on which specific reasoning procedures can be given to reduce the expression further.\<close>


subsection \<open>Approximately Evaluating Domainoid of BI Assertions\<close>

\<phi>reasoner_group domainoids = (100, [10,3000]) for \<open>domainoid TYPE('c::sep_magma) \<delta>\<close>
    \<open>Rules giving domainoid extraction \<open>\<delta>\<close> on the given concrete algbera \<open>'c\<close>\<close>
 and domainoid_fallback = (1, [1,1]) for \<open>domainoid TYPE('c::sep_magma) \<delta>\<close>
    \<open>The identity homomorphism is always a domainoid extraction from one algebra to itself\<close>
 and domainoid_cut = (1000, [1000,1030]) for \<open>domainoid TYPE('c::sep_magma) \<delta>\<close> in domainoids
    \<open>Cutting rules\<close>

declare [[
  \<phi>reason_default_pattern \<open>domainoid ?TY _\<close> \<Rightarrow> \<open>domainoid ?TY _\<close> (100),
  \<phi>reason_default_pattern \<open>\<Psi>[?d] ?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S'\<close> \<Rightarrow> \<open>\<Psi>[?d] ?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?S'\<close> \<open>\<Psi>[?d] ?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_S'\<close> (200)
                      and \<open>?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<Psi>[?d] ?S'\<close> \<Rightarrow> \<open>?S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<Psi>[?d] ?S'\<close> \<open>?var_S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<Psi>[?d] ?S'\<close> (200)
]]

text \<open>For a domain extraction \<open>\<delta>\<close>, \<open>\<Psi>[\<delta>] S\<close> is used to extract the domain of concrete objects
  specified by the given BI assertion \<open>S\<close>\<close>

(*
definition domainoid_BI_modality :: \<open>('c,'d) domainoid \<Rightarrow> 'c::sep_magma BI \<Rightarrow> 'd::sep_magma set\<close> ("\<Psi>[_]" [10] 1000)
  where \<open>(\<Psi>[d] S) = (\<Psi>[d] S \<s>\<u>\<b>\<j> domainoid TYPE('c) d)\<close>
  \<comment> \<open> The domain of concrete objects specified by the given BI assertion \<open>S\<close> \<close>

lemma domainoid_BI_modality_expn[\<phi>expns, simp]:
  \<open>p \<Turnstile> \<Psi>[d] S \<longleftrightarrow> (\<exists>u. p = d u \<and> u \<Turnstile> S \<and> domainoid TYPE('c::sep_magma) d)\<close>
  unfolding domainoid_BI_modality_def
  by (clarsimp, blast)
*)

(*
lemma domainoid_BI_modality_expn'[\<phi>expns, simp]:
  \<open>p \<in> \<Psi>[d] S \<longleftrightarrow> (\<exists>u. p = d u \<and> u \<Turnstile> S \<and> domainoid TYPE('c::sep_magma) d)\<close>
  unfolding domainoid_BI_modality_def Satisfaction_def
  by clarsimp*)


subsubsection \<open>Evaluation on Specific BI Connectives\<close>



subsection \<open>Homomorphism of Domainoid\<close>

(* A --domainoid--> D(A)
   \<down> \<psi>               \<down> D(\<psi>)
   B --domainoid--> D(B) *)




(*TODO: move!*)

(* C----T----> A
   \<down>\<psi>    \<subseteq>   | \<psi>'
   D <-------
*)
(*
definition Abstract_Morphism\<^sub>U :: \<open>('c::sep_magma,'d::sep_magma) domainoid \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'd set) \<Rightarrow> bool\<close>
  where \<open>Abstract_Morphism\<^sub>U \<psi> T \<psi>' \<longleftrightarrow> (\<forall>x u. u \<Turnstile> \<Psi>[dm] (x \<Ztypecolon> T) \<longrightarrow> u \<in> dm' x )\<close>
  \<comment> \<open>\<phi>-Type Homomorphism, \<open>dm'\<close> is an upper approximation of the \<open>dm\<close> in the abstract domain,
      which gives for each abstract object the domain of the concrete objects refining it.\<close>

definition Domainoid_Homo\<^sub>L :: \<open>('c::sep_magma,'d::sep_magma) domainoid \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'd set) \<Rightarrow> bool\<close>
  where \<open>Domainoid_Homo\<^sub>L dm T dm' \<longleftrightarrow> domainoid TYPE('c) dm \<and> (\<forall>x u'. u' \<in> dm' x \<longrightarrow> u' \<Turnstile> \<Psi>[dm] (x \<Ztypecolon> T) )\<close>
  \<comment> \<open>The lower approximation\<close>
*)

subsection \<open>Approximately Evaluating Domainoid of BI Assertions\<close>

declare [[\<phi>trace_reasoning = 1]]



\<phi>reasoner_group \<DD>_approximate = (100, [10,3000]) for (\<open>D \<le> \<DD>[\<delta>] A\<close>, \<open>\<DD>[\<delta>] A \<le> D\<close>)
    \<open>Reasoning rules approximately evaluating the domainoid of a given BI assertion\<close>
  and \<DD>_approx_cut = (1000, [1000,1030]) for (\<open>D \<le> \<DD>[d] A\<close>, \<open>\<DD>[d] A \<le> D\<close>) in \<DD>_approximate
    \<open>Cutting rules\<close>



(*Do we need to consider relation in commutativity?*)


text \<open>
Logic connectives:
\<^item> Sep_Homo gives the commutativity between \<open>F\<^sub>a\<close> and \<open>\<^emph>\<close>
\<^item> Subjection is given directly by transformation functor
\<^item> \<open>\<and>\<^sub>\<phi>\<close>, \<open>\<and>\<^sub>\<phi>\<^sub>E\<close> is implied, \<open>\<and>\<^sub>\<phi>\<^sub>I\<close> is not
\<^item> \<open>+\<^sub>\<phi>\<close>, \<open>+\<^sub>\<phi>\<^sub>I\<close> is implied, \<open>+\<^sub>\<phi>\<^sub>E\<close> is not

\<^item> \<open>\<S>\<close> has a half, \<open>x \<Ztypecolon> F (\<S> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> \<S> (F T)\<close>, the other half is unknown
\<^item> \<open>\<Sigma>\<close>, \<open>\<Sigma>\<^sub>I\<close> is implied in transformation functor, \<open>\<Sigma>\<^sub>E\<close> is by Trivial_\<Sigma> deriver
\<^item> 
\<close>





(*
subsubsection \<open>\<phi>-Type\<close>

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> Domainoid_Homo\<^sub>L d T dm\<^sub>T
\<Longrightarrow> dm\<^sub>T x \<le> \<Psi>[d] (x \<Ztypecolon> T)\<close>
  unfolding Domainoid_Homo\<^sub>L_def set_eq_iff
  by clarsimp

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> Domainoid_Homo\<^sub>U d T dm\<^sub>T
\<Longrightarrow> \<Psi>[d] (x \<Ztypecolon> T) \<le> dm\<^sub>T x\<close>
  unfolding Domainoid_Homo\<^sub>U_def set_eq_iff
  by clarsimp
*)
subsubsection \<open>BI Connectives\<close>

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> domainoid TYPE('c::sep_magma_1) \<psi>
\<Longrightarrow> homo_one \<psi>
\<Longrightarrow> \<Psi>[\<psi>] 1 \<le> 1 \<close>
  unfolding \<Psi>_1 by simp

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> domainoid TYPE('c::sep_magma_1) \<psi>
\<Longrightarrow> homo_one \<psi>
\<Longrightarrow> 1 \<le> \<Psi>[\<psi>] 1 \<close>
  unfolding \<Psi>_1 by simp

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> 0 \<le> \<Psi>[\<psi>] 0 \<close>
  unfolding \<Psi>_0 by simp

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> \<Psi>[\<psi>] 0 \<le> 0 \<close>
  unfolding \<Psi>_0 by simp

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> closed_homo_sep \<psi>
\<Longrightarrow> A' \<le> \<Psi>[\<psi>] A
\<Longrightarrow> B' \<le> \<Psi>[\<psi>] B
\<Longrightarrow> A' * B' \<le> \<Psi>[\<psi>] (A * B)\<close>
  unfolding \<Psi>_Multiplicative_Conj
  by (meson subset_trans times_set_subset(1) times_set_subset(2))

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> closed_homo_sep \<psi>
\<Longrightarrow> \<Psi>[\<psi>] A \<le> A'
\<Longrightarrow> \<Psi>[\<psi>] B \<le> B'
\<Longrightarrow> \<Psi>[\<psi>] (A * B) \<le> A' * B'\<close>
  unfolding \<Psi>_Multiplicative_Conj
  by (meson dual_order.trans times_set_subset(1) times_set_subset(2))

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> closed_homo_sep \<psi>
\<Longrightarrow> homo_one \<psi>
\<Longrightarrow> (\<And>i\<in>I. \<Psi>[\<psi>] (A i) \<le> A' i)
\<Longrightarrow> \<Psi>[\<psi>] (\<big_ast>i\<in>I. A i) \<le> (\<big_ast>i\<in>I. A' i) \<close>
  unfolding \<Psi>_Mul_Quant BI_sub_transformation
  by (rule sep_quant_transformation[where P=\<open>\<lambda>_. True\<close>, simplified])

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> closed_homo_sep \<psi>
\<Longrightarrow> homo_one \<psi>
\<Longrightarrow> (\<And>i\<in>I. A' i \<le> \<Psi>[\<psi>] (A i))
\<Longrightarrow> (\<big_ast>i\<in>I. A' i) \<le> \<Psi>[\<psi>] (\<big_ast>i\<in>I. A i) \<close>
  unfolding \<Psi>_Mul_Quant BI_sub_transformation
  by (rule sep_quant_transformation[where P=\<open>\<lambda>_. True\<close>, simplified])

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> A' \<le> \<Psi>[\<psi>] A
\<Longrightarrow> B' \<le> \<Psi>[\<psi>] B
\<Longrightarrow> A' + B' \<le> \<Psi>[\<psi>] (A + B) \<close>
  unfolding \<Psi>_Additive_Disj
  by (clarsimp; fastforce)

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> \<Psi>[\<psi>] A \<le> A'
\<Longrightarrow> \<Psi>[\<psi>] B \<le> B'
\<Longrightarrow> \<Psi>[\<psi>] (A + B) \<le> A' + B' \<close>
  unfolding \<Psi>_Additive_Disj
  by (clarsimp; fastforce)

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> (\<And>c. \<Psi>[\<psi>] (S c) \<le> S' c)
\<Longrightarrow> \<Psi>[\<psi>] (ExSet S) \<le> ExSet S'\<close>
  unfolding \<Psi>_ExSet BI_sub_transformation
  by (simp add: ExSet_transformation)

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> (\<And>c. S' c \<le> \<Psi>[\<psi>] (S c))
\<Longrightarrow> ExSet S' \<le> \<Psi>[\<psi>] (ExSet S)\<close>
  unfolding \<Psi>_ExSet BI_sub_transformation
  by (simp add: ExSet_transformation)

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> ((\<Psi>[\<psi>] S) \<s>\<u>\<b>\<j> P) \<le> S'
\<Longrightarrow> \<Psi>[\<psi>] (S \<s>\<u>\<b>\<j> P) \<le> S'\<close>
  unfolding \<Psi>_Subjection BI_sub_transformation
  by simp

lemma [\<phi>reason %\<DD>_approx_cut]:
  \<open> S' \<le> ((\<Psi>[\<psi>] S) \<s>\<u>\<b>\<j> P)
\<Longrightarrow> S' \<le> \<Psi>[\<psi>] (S \<s>\<u>\<b>\<j> P)\<close>
  unfolding \<Psi>_Subjection
  by (clarsimp simp add: Subjection_ord)



subsection \<open>Applications\<close>

subsubsection \<open>Domainoid gives Satisfaction of Separation Conjunction\<close>

lemma [\<phi>reason 1000]:
  \<open> Pa \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A
\<Longrightarrow> Pb \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> B
\<Longrightarrow> domainoid TYPE('c::sep_magma) \<delta>
\<Longrightarrow> A' \<le> \<Psi>[\<delta>] A \<comment>\<open>expand \<open>\<Psi>[d] A, \<Psi>[d] B\<close> to a simpler (but should still strong) upper approximation\<close>
\<Longrightarrow> B' \<le> \<Psi>[\<delta>] B
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Pa \<and> Pb \<longrightarrow> (\<exists>a b. a \<Turnstile> A' \<and> b \<Turnstile> B' \<and> a ## b))
\<Longrightarrow> Pa \<and> Pb \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> A * B\<close>
  unfolding Inhabited_def BI_sub_iff Premise_def Action_Tag_def domainoid_def
  by (clarsimp simp add: closed_homo_sep_def closed_homo_sep_disj_def; blast)

lemma \<comment> \<open>The above rule is reversible for any domainoid extraction \<open>d\<close>\<close>
  \<open> domainoid TYPE('c::sep_magma) d
\<Longrightarrow> Inhabited (A * B) \<longleftrightarrow> (\<exists>a b. a \<in> \<Psi>[d] A \<and> b \<in> \<Psi>[d] B \<and> a ## b)\<close>
  unfolding Inhabited_def
  by (clarsimp simp add: domainoid_def closed_homo_sep_def closed_homo_sep_disj_def; blast)


subsubsection \<open>Domainoid gives Separation_Disj\<close>


lemma [\<phi>reason default 10]:
  \<open> domainoid TYPE('c::sep_magma) \<delta>
\<Longrightarrow> domainoid TYPE('c\<^sub>\<psi>::sep_magma) \<delta>\<^sub>\<psi>
\<Longrightarrow> (\<And>x. \<Psi>[\<delta>] (x \<Ztypecolon> T) \<le> \<DD>\<^sub>T x)
\<Longrightarrow> (\<And>y. \<Psi>[\<delta>] (y \<Ztypecolon> U) \<le> \<DD>\<^sub>U y)
\<Longrightarrow> fun_commute \<delta>\<^sub>\<psi> \<psi> \<delta> \<psi>\<^sub>D \<and> has_\<psi>\<^sub>D = True \<or>\<^sub>c\<^sub>u\<^sub>t has_\<psi>\<^sub>D = False
\<Longrightarrow> Separation_Disj\<^sub>\<phi> \<psi> ({(y,x). \<forall>d\<^sub>x d\<^sub>y. d\<^sub>x \<Turnstile> \<DD>\<^sub>T x \<and> d\<^sub>y \<Turnstile> \<DD>\<^sub>U y \<and> (has_\<psi>\<^sub>D \<longrightarrow> \<psi>\<^sub>D d\<^sub>x ## \<psi>\<^sub>D d\<^sub>y) \<longrightarrow> d\<^sub>x ## d\<^sub>y}) T U
                          \<comment> \<open>\<open>\<psi>\<^sub>D d\<^sub>x ## \<psi>\<^sub>D d\<^sub>y\<close> reflects the condition \<open>\<psi> u ## \<psi> v\<close> in \<open>Separation_Disj\<close>\<close> \<close>
  unfolding Separation_Disj\<^sub>\<phi>_def Separation_Disj_def Orelse_shortcut_def BI_sub_iff
  by (clarsimp simp add: domainoid_def Premise_def fun_commute_def[unfolded fun_eq_iff, simplified]
                         closed_homo_sep_def closed_homo_sep_disj_def; metis)

lemma [\<phi>reason 1000]:
  \<open> Separation_Disj\<^sub>\<phi> \<psi> D T U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (y,x) \<in> D
\<Longrightarrow> Separation_Disj \<psi> (x \<Ztypecolon> T) (y \<Ztypecolon> U) \<close>
  unfolding Separation_Disj\<^sub>\<phi>_def Premise_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> A B\<^sub>1
\<Longrightarrow> Separation_Disj \<psi> A B\<^sub>2
\<Longrightarrow> Separation_Disj \<psi> A (B\<^sub>1 * B\<^sub>2)\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_right)

lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> A (fst y \<Ztypecolon> U\<^sub>1)
\<Longrightarrow> Separation_Disj \<psi> A (snd y \<Ztypecolon> U\<^sub>2)
\<Longrightarrow> Separation_Disj \<psi> A (y \<Ztypecolon> U\<^sub>1 \<^emph> U\<^sub>2)\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_right)

lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> A\<^sub>1 B
\<Longrightarrow> Separation_Disj \<psi> A\<^sub>2 B
\<Longrightarrow> Separation_Disj \<psi> (A\<^sub>1 * A\<^sub>2) B\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_left)

lemma [\<phi>reason 1000]:
  \<open> MEMOIZE homo_sep \<psi>
\<Longrightarrow> Separation_Disj \<psi> (fst x \<Ztypecolon> T\<^sub>1) B
\<Longrightarrow> Separation_Disj \<psi> (snd x \<Ztypecolon> T\<^sub>2) B
\<Longrightarrow> Separation_Disj \<psi> (x \<Ztypecolon> T\<^sub>1 \<^emph> T\<^sub>2) B\<close>
  for \<psi> :: \<open>'a::sep_disj_distrib \<Rightarrow> 'b::sep_disj_distrib\<close>
  unfolding Separation_Disj_def homo_sep_def homo_sep_mult_def
  by (clarsimp, metis homo_sep_disj_def sep_disj_distrib_left)

(*definition Separation_Disj :: \<open>'a::sep_magma set \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where \<open>Separation_Disj X Y \<longleftrightarrow> (\<forall>u v. u \<Turnstile> X \<and> v \<Turnstile> Y \<longrightarrow> u ## v)\<close>*)


section \<open>Concrete Instances of Domainoids\<close>

lemma [\<phi>reason %domainoid_fallback]:
  \<open>domainoid TYPE('c::sep_magma) (\<lambda>x. x)\<close>
  unfolding domainoid_def
  by simp

lemma [\<phi>reason %domainoid_cut]:
  \<open> domainoid TYPE('c::discrete_semigroup) (\<lambda>_. nosep ()) \<close>
  unfolding domainoid_def
  by simp

lemma [\<phi>reason %domainoids]:
  \<open> domainoid TYPE('c) d
\<Longrightarrow> domainoid TYPE('k \<Rightarrow> 'c::sep_magma) ((o) d) \<close>
  unfolding domainoid_def
  by simp

lemma [\<phi>reason %domainoids]:
  \<open> domainoid TYPE('c) d
\<Longrightarrow> domainoid TYPE('c::sep_magma option) (map_option d) \<close>
  unfolding domainoid_def
  by simp

text \<open>\<open>'c share\<close> has no meaningful domainoid as that structure inevitably involves equality checking
  of inner data (luckily we don't need that domainoid).\<close>


end