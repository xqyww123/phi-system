theory Phi_Type_Algebra
  imports IDE_CP_Reasoning2
  keywords "\<phi>type_def" "\<phi>property_deriver" "let_\<phi>type" :: thy_defn
       and "deriving" :: quasi_command
begin

text \<open>
Motivation:

Old school logicians may argue that the whole point of automated reasoning was to let computers do
reasoning without understanding the semantics. However, particularly in the domain of program logic,
most of logics only have semidecidable algorithms at best. As a consequence, classical methods including
tableaux, sequent calculus, can be very limited on automating the verification of practical low-level
programs --- the search does not end in a reasonable time of human's life.

Could the automation utilize the semantics by understanding it by some means, to boost the performance?
The performance means the portion of problems that an automation can solve in a reasonable time.

Temporarily putting this stream of thought aside, we also notice coarse-grand type systems
give good automation to derive the coarse information of programs (by contrast with fine-grand type
systems which have great expressiveness but no decidable algorithm, as they are isomorphic to some
expressive program logics).

Could we, figuratively, extract the coarse portion of the expressiveness of the logic, forming
a type system in the logic, to guide the reasoning (on any fine-grand properties)
and by an efficient automation that such type system can have, to improve the performance?

Again we suspend the thought. Data refinement is an efficient approach hiding the complicated concrete
details and lifting the verification onto abstraction, (from a bottom-up view for post-hoc
verification instead of the top-down method for correctness-by-construction).

When the three stream meet, we come up with the logic of \<open>\<phi>\<close>-type, namely the type of refinement,
taking the homonym of re\<phi>ment.
It provides an embedding of data refinement into the logic of
Bunched Implications (BI), and on the other hand guides the automatic reasoning by reasoning rules
which can also be automatically generated.

Each \<open>\<phi>\<close>-type assertion \<open>x \<Ztypecolon> T\<close> (which is a normal BI assertion) specifies how a concrete
representation \<open>c \<Turnstile> x \<Ztypecolon> T\<close> of a data structure \<open>T\<close> is lifted to or equivalently refines
the abstract representation \<open>x\<close> of the data structure.
\<open>x\<close> is the fine portion complementing the coarse type \<open>T\<close> to support expressibility.
\<open>T\<close> guides the automation to generate a proof obligation as a proposition about \<open>x\<close> and therefore on the abstract domain,
thus lifting the verification onto abstraction.

\<phi>-Type is able to characterize many properties of the data structure and raises a meta theory on which
we can build a general automation, such as the general property of subtyping functor over a type operator \<open>F\<close>,
\<open>(\<forall>a. a \<Ztypecolon> T \<longrightarrow> f(a) \<Ztypecolon> U) \<Longrightarrow> (\<forall>x. x \<Ztypecolon> F(T) \<longrightarrow> mapper f x \<Ztypecolon> F(U))\<close>,
which specifies how the entire data structure is transformed when the abstraction of its element is transformed.
By utilizing the algebraic properties of data structures, the automation captures the semantics of them (up to isomorphism).
The properties can be given by manual annotations from users, or be guessed (can be wrong) and therefore fully automated (can fail)
if the abstract representation is defined from Natural Bounded Functor (BNF), i.e., by algebraic data type tools
in most of proof assistants.

The attempt to introduce a type system in a logic is ubiquitous. However, they are rudimentary
comparing with the abundant algebraic properties that \<phi>-type owns, which instantiate the automation,
and also the rule generation algorithms that our theory provides, which derive the algebraic properties.
RefinedC gives a theory diving into neither algebraic properties nor rule generation algorithms,
but only the notion of coarse-grand types itself with reasoning rules written manually by human experts.
The type in ReLoC is basically the syntactic notation of a logical connective without meta theory of the
type such as the functor of subtyping over type operators.
Both of the works above are based on specific (concurrent) separation logics with complicated add-ons,
whereas our work is based on pure BI logic (with necessary but minimal add-ons) and therefore is fundamental and general. 

There are also many works combining data refinement into separation logic. Comparing with our constructions
where refinement relations are simply represented by predicates, their embedding is far from simple
and clean, mostly attached with heavy and standalone structures to bring (data) refinement inside.
Admittedly a limitation in our work is that, from a perspective of the more general refinement (instead of
only the data refinement), our abstract program must be a relation and is not represented explicitly
as a specific term in the logic, but we argue, the effect is the same if we only expect the refinement
to simplify the workload of verifying a concrete program, instead of showing the relationships between two
given programs (known as relational reasoning). Under such condition,
for the first time we show how simple and clean the data refinement can be embedded into BI.

To measure our approach, we implement it on Isabelle/HOL. On a subset of C semantics, we show
many algorithms and data structures can be verified automatically, reaching a degree of automation
outperforming existing works as far as we know.

\section{The Approach of \<open>\<phi>\<close>-Types}

<overview first.>




Conclusion:

Based on the abundant algebriac properties that \<phi>-type owns, we believe we found the correct
  counterpart of type theory in the domain of program logic for verification.
  Furthermore, forming a type system of a language built upon a program logic, it may bring new choices
  for certified programming. We are studying this as our future work.\<close>

section \<open>The Algebra of \<open>\<phi>\<close>-Refinement\<close>

subsection \<open>Definitions\<close>

subsubsection \<open>Transformation\<close>

definition \<open>Transformation_Functor F1 F2 D R mapper \<longleftrightarrow>
  (\<forall>T U x g. (\<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b) \<longrightarrow>
               (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x) \<longrightarrow>
               (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y))\<close>
  \<comment> \<open>f1 and d1 make the domain set.

  The definition is given in reasoning-friendly form and should entail, (TODO: verify!)

  definition \<open>Transformation_Functor F1 F2 mapper \<longleftrightarrow>
    (\<forall>T U r x. (\<forall>x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. (x,y) \<in> r) \<longrightarrow>
               (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. (x,y) \<in> mapper r))\<close>,
  when D is UNIV

  The nondeterminancy from relation \<open>r\<close> can be achieved by embedding ExTyp.

  We strengthen this original definition by allowing the domain of the element transformation to be
  depended on the source object of the functor transformation so that the reasoning can have more
  information about the domain of the element transformation.


  \<open>R\<close> constrains the range of the transformation of the inner elements, which will be a proof obligation
      reported to user for each transformation application.
  It is useful especially for dependent data types like a list of even numbers.
  Such constraint usually assumes the logic type (the algbera) of the transformation target.
  For general data structures which do not assumes such, tt is usually \<open>\<lambda>_. \<top>\<close>.
  Our automatic deriver always assigns it to \<open>\<lambda>_. \<top>\<close> if no user hint is given.
\<close>

lemma Transformation_Functor_sub_dom:
  \<open> (\<And>x. Da x \<subseteq> Db x)
\<Longrightarrow> Transformation_Functor F1 F2 Da R mapper
\<Longrightarrow> Transformation_Functor F1 F2 Db R mapper\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_Functor_sub_rng:
  \<open> (\<And>x. Rb x \<subseteq> Ra x)
\<Longrightarrow> Transformation_Functor F1 F2 D Ra mapper
\<Longrightarrow> Transformation_Functor F1 F2 D Rb mapper\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_Functor_sub_mapper:
  \<open> ma \<le> mb
\<Longrightarrow> Transformation_Functor F1 F2 D R ma
\<Longrightarrow> Transformation_Functor F1 F2 D R mb\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: le_fun_def Transformation_def Ball_def, blast)

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb D R mapper
\<Longrightarrow> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<close>
  unfolding Transformation_Functor_def Premise_def
  by simp



subsubsection \<open>Separation\<close>

definition Object_Sep_Homo\<^sub>I :: \<open>('b::sep_magma, 'a::sep_magma) \<phi> \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool\<close>
  where \<open>Object_Sep_Homo\<^sub>I T D \<longleftrightarrow> (\<forall>x y. (y,x) \<in> D \<longrightarrow> ((x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> T \<w>\<i>\<t>\<h> x ## y ))\<close>

definition \<open>Object_Sep_Homo\<^sub>E T \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> ( (x * y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) ))\<close>

definition \<open>Separation_Homo\<^sub>I Ft Fu F3 Prem D z \<longleftrightarrow>
              (\<forall>T U x y. Prem T U (x,y) \<longrightarrow> (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (T \<^emph> U)))\<close>

definition \<open>Separation_Homo\<^sub>E Ft Fu F3 un \<longleftrightarrow> \<comment> \<open>Does it need a domain constraint?\<close>
              (\<forall>T U z. z \<Ztypecolon> F3 (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph> Fu U)\<close>

definition Semimodule_Scalar_Homo :: \<open>('s \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> 's::semigroup_mult set \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Homo F T D \<longleftrightarrow> (\<forall>s \<in> D. \<forall>t \<in> D. F s (F t T) = F (t * s) T)\<close>
  \<comment> \<open>Associativity of scalar multiplication\<close>

definition Semimodule_LDistr_Homo\<^sub>Z :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                    \<Rightarrow> ('c::sep_magma,'a) \<phi>
                                    \<Rightarrow> ('s::partial_add_semigroup \<Rightarrow> bool)
                                    \<Rightarrow> (('a \<times> 'a) \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                    \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx x \<longrightarrow>
                  (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> F (s + t) T ))\<close>
  \<comment> \<open>The left distributive law (i.e., the distributivity of scalar addition) of a left-module.
      Note the right distributive law (i.e., the distributivity of vector addition) is just the separation homomorphism.
      So, when both of \<open>Semimodule_Scalar_Homo\<close>, \<open>Separation_Homo\<close>, \<open>Semimodule_LDistr_Homo\<^sub>Z\<close>, and
      homomorphism of identity element, are satisfied, it is then a semimodule.
\<close>

definition Semimodule_LDistr_Homo\<^sub>O\<^sub>Z :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>O\<^sub>Z T Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>x. s ##\<^sub>+ t \<and> Dx x \<longrightarrow> (x \<Ztypecolon> T t \<^emph> T s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> T (s + t) ))\<close>
  \<comment> \<open>the subscript O stands for \<^emph>\<open>non-type-Operator\<close>\<close>

definition Semimodule_LDistr_Homo\<^sub>Z_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>Z_rev F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T ))\<close>

definition Semimodule_LDistr_Homo\<^sub>U :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> 's::partial_add_semigroup set \<Rightarrow> (('c,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a) \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>U F Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>T x. t ##\<^sub>+ s \<and> Dx T x \<longrightarrow> (x \<Ztypecolon> F (t + s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T ))\<close>


subsection \<open>Configurations\<close>

declare (in homo_one) homo_one_axioms[\<phi>reason 1100]

lemma [\<phi>premise_extraction]:
  \<open>homo_one \<psi> \<equiv> \<psi> 1 = 1 \<and> True\<close>
  unfolding homo_one_def
  by simp

lemma (in homo_sep_mult) [\<phi>reason 1100]:
  \<open>homo_sep_mult \<psi>\<close>
  by (simp add: homo_sep_mult_axioms)

lemma (in closed_homo_sep_disj) [\<phi>reason 1100]:
  \<open>closed_homo_sep_disj \<psi>\<close>
  by (simp add: closed_homo_sep_disj_axioms)


declare [[
  \<phi>reason_default_pattern_ML
      \<open>Transformation_Functor ?F1 ?F2 _ _ _\<close> \<Rightarrow> \<open>fn generic => fn term =>
          let val ctxt = Context.proof_of generic
              val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
              val Trueprop $ (_ (*Transformation_Functor*) $ F1 $ F2 $ D $ mapper) = term'
              val ind = Int.max (maxidx_of_term F1, maxidx_of_term F2) + 1
              fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
              val H = Const(\<^const_name>\<open>Transformation_Functor\<close>, TVar(("'TF",ind),[]))
           in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "D" "'D" $ var "R" "'R" $ var "M" "'M"),
                    Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "D" "'D" $ var "R" "'R" $ var "Ma" "'M")]
          end\<close> (100)
]]

(*The default patterns of the rules are more general here by varifying types.
  This is designed specially.
  In \<^const>\<open>Reverse_Transformation\<close>, as the reverse transformation can have different type,
    and in the algebraic general rule \<open>_Structural_Extract_general_rule'_\<close> the functors are
    represented by variables, it means we have no simple way to varify the type of the functors.
    We use ML (who?) to capture the functor constant and varify the type variables as much as it can
    (we have no way to know the appropriate extend to which it varifies).
    Under such varified types, we set the default pattern of the algebraic properties to be also
    similarly very varified, to hope the rules can still capture the very varified
    reasoning subgoals.
  We only need to over-varify Transformation_Functor and Separation_Functor in such way, because
  only them two are used in the reverse transformation.*)

(*TODO: if we can depreciate this, as the reasonings are by template*)

declare [[
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Transformation_Functor _ _ _ _ _\<close>,
  \<phi>reason_default_pattern \<open>Object_Sep_Homo\<^sub>I ?T _\<close> \<Rightarrow> \<open>Object_Sep_Homo\<^sub>I ?T _\<close> (100),

  \<phi>reason_default_pattern_ML \<open>Separation_Homo\<^sub>I ?Ft ?Fu _ _ _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Homo\<^sub>I*) $ F1 $ F2 $ F3 $ _ $ D $ f) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, TVar(("'SF",ind),[]))
       in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "Pr" "'P" $ var "D" "'d" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "Pr" "'P" $ var "D" "'d" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "Pr" "'P" $ var "D" "'d" $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>reason_default_pattern_ML \<open>Separation_Homo\<^sub>E ?Ft ?Fu _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Functor*) $ F1 $ F2 $ F3 $ f) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, TVar(("'SF",ind),[]))
       in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>I _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>E _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_LDistr_Homo\<^sub>Z _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_LDistr_Homo\<^sub>Z_rev _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_LDistr_Homo\<^sub>U _ _ _ _\<close>,
  \<phi>reason_default_pattern
      \<open>Semimodule_LDistr_Homo\<^sub>Z ?F ?T _ _ _\<close> \<Rightarrow> \<open>Semimodule_LDistr_Homo\<^sub>Z ?F ?T _ _ _\<close> (100)
  and \<open>Semimodule_LDistr_Homo\<^sub>U ?F _ _ _\<close> \<Rightarrow> \<open>Semimodule_LDistr_Homo\<^sub>U ?F _ _ _\<close> (100)
  and \<open>Semimodule_LDistr_Homo\<^sub>Z_rev ?F _ _ _\<close> \<Rightarrow> \<open>Semimodule_LDistr_Homo\<^sub>Z_rev ?F _ _ _\<close> (100)
]]


subsection \<open>Applications\<close>

subsubsection \<open>Separation Homo / Functor\<close>

lemma apply_sep_homo:
  \<open> Object_Sep_Homo\<^sub>I T D
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (y,x) \<in> D
\<Longrightarrow> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> T \<w>\<i>\<t>\<h> x ## y\<close>
  unfolding Object_Sep_Homo\<^sub>I_def Premise_def by simp

lemma apply_sep_homo_unzip:
  \<open> Object_Sep_Homo\<^sub>E T
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x ## y
\<Longrightarrow> (x * y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T)\<close>
  unfolding Object_Sep_Homo\<^sub>E_def Premise_def by blast

lemma apply_Separation_Functor_zip:
  \<open> Separation_Homo\<^sub>I Ft Fu Fc Prem D z
\<Longrightarrow> Prem T U x
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z x \<Ztypecolon> Fc(T \<^emph> U)\<close>
  unfolding Separation_Homo\<^sub>I_def Premise_def meta_Ball_def meta_case_prod_def split_paired_all
  by (cases x; simp)

lemma apply_Separation_Functor_unzip:
  \<open> Separation_Homo\<^sub>E Ft Fu Fc un
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph> Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'[symmetric]
  by simp

lemma apply_Semimodule_LDistr_Homo\<^sub>Z:
  \<open> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx x
\<Longrightarrow> x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> F (s + t) T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_def Premise_def
  by blast

lemma apply_Semimodule_LDistr_Homo\<^sub>Z_rev:
  \<open> Semimodule_LDistr_Homo\<^sub>Z_rev F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_rev_def Premise_def
  by blast

lemma apply_Semimodule_LDistr_Homo\<^sub>U:
  \<open> Semimodule_LDistr_Homo\<^sub>U F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> s \<in> Ds \<and> t \<in> Ds \<and> t ##\<^sub>+ s
\<Longrightarrow> Dx T x
\<Longrightarrow> x \<Ztypecolon> F (t + s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>U_def Premise_def
  by blast


subsubsection \<open>Transformation Functor\<close>

(*
lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb fa fb
\<Longrightarrow> \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t fa x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fb y \<Ztypecolon> U \<w>\<i>\<t>\<h> Q
\<Longrightarrow> (x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> Q)\<close>
  unfolding Transformation_Functor_def Argument_def
  by blast

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb mapper
\<Longrightarrow> (fa x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fb y \<Ztypecolon> U \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> (x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> Q)\<close>
  unfolding Transformation_Functor_def
  by blas
*)


subsection \<open>Definition and Deriving Tools\<close>

text \<open>The @{command \<phi>type_def} command always generate 4 sorts of rules.
  For instance, for definition \<open>x \<Ztypecolon> T \<equiv> U\<close>,

\<^item> \<^verbatim>\<open>T.intro\<close> of form \<^prop>\<open>U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<close>. There are corresponding reasoning rules named \<^verbatim>\<open>T.intro_reasoning\<close>.
      By default the reasoning rules are not activated. You may activate them by
      \<^verbatim>\<open>declare T.intro_reasoning[\<phi>reason]\<close> in order to, for instance, reduce to \<open>U\<close> the reasoning of
      \<^emph>\<open>every\<close> transformation goal targeting to \<open>T\<close>. Depending on the priority you configured,
      if the priority is greater than 54 (the priority of the entry point of the Structural Extraction),,
      this reduction happens before any in-depth reasoning that collects proportions in the source
      objects to synthesis the target \<open>T\<close> (i.e. the Structural Extraction, SE);
      if the priority is less than 50, it serves as a fallback when the SE fails.

      In any case even if you do not activate the intro rule, the system always activates a rule
      that allows you to use \<^term>\<open>MAKE T\<close> tag to invoke the intro rule and to make a \<phi>-type term
      of \<open>T\<close> from \<open>U\<close>. To use it, just write \<phi>-Lang \<^verbatim>\<open>\<open>x \<Ztypecolon> MAKE T\<close>\<close> to invoke the synthesis process.

\<^item> \<^verbatim>\<open>T.elim\<close> of form \<^prop>\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U\<close>. There are also corresponding reasoning rules named \<^verbatim>\<open>T.elim_reasoning\<close>.
      They are also not activated by default. The priority of them can be more arbitrary because they are
      in the SE process as the last stage of the \<exists>free-ToA reasoning. Note the \<exists>free-ToA reasoning
      works not good if the elim rule introduces existential quantification, because the \<exists>free-ToA
      by design does not consider opening abstraction.

      No matter if the reasoning rules are activated, you can always open an abstraction using
      To-Transformation, i.e., \<phi>-Lang \<^verbatim>\<open>to \<open>List OPEN\<close>\<close> for instance to open \<open>x" \<Ztypecolon> List T\<close> into
      \<open>{ y" \<Ztypecolon> List U' | List.rel P x" y" }\<close> if \<open>U \<equiv> { y \<Ztypecolon> U' | P y }\<close> for some \<open>y\<close> and \<open>y"\<close> that
      maybe in a set if \<open>x \<Ztypecolon> T\<close> is an abstraction of a set of \<open> { y \<Ztypecolon> U' | P y } \<close>.

\<^item> \<^verbatim>\<open>T.unfold\<close>, \<^prop>\<open>(x \<Ztypecolon> T) = U\<close>

\<^item> \<^verbatim>\<open>T.expansion\<close>, \<^prop>\<open>p \<Turnstile> (x \<Ztypecolon> T) \<longleftrightarrow> p \<Turnstile> U\<close>. This rule is added to the system global simplifier.

If a definition like those recursive definitions is characterized by multiple equations.
The above rules are generated for each equation correspondingly.
\<close>

subsubsection \<open>Convention\<close>

text \<open>
Priority:
\<^item> 30: Destruction \<open>to RAW\<close>
\<^item> 40: Transformations, To-Transformations
\<^item> 40: \<^const>\<open>Identity_Element\<^sub>I\<close>, \<^const>\<open>Identity_Element\<^sub>E\<close>
      \<^const>\<open>Object_Equiv\<close>
\<^item> 45: Simplification for \<open>\<^emph>\<^sub>\<A>\<close>
\<^item> 80: Construction \<open>to T\<close> where \<open>T\<close> is the type just defined
\<^item> 80: Implication \<^prop>\<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P\<close>,
      \<^prop>\<open>Is_Functional (x \<Ztypecolon> T)\<close>
      Open_All_Abstraction \<^prop>\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r y @action to Itself\<close>
\<^item> 1000: Type_Variant_of_the_Same_Type_Operator
\<^item> 1100: \<^const>\<open>Transformation_Functor\<close>
\<close>

subsubsection \<open>Implementation\<close>

lemma \<phi>inductive_destruction_rule_from_direct_definition:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> P \<longrightarrow> (R * U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> P \<longrightarrow> (R * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q) \<close>
  by simp

lemma \<phi>inductive_destruction_rule_from_direct_definition':
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> P \<longrightarrow> (U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> P \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q) \<close>
  by simp

lemma \<phi>intro_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<close>
  by simp

lemma \<phi>intro_reasoning_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma \<phi>intro'_reasoning_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma \<phi>elim_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<close>
  by simp

lemma \<phi>elim_reasoning_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma \<phi>elim'SE_transformation:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (y x \<Ztypecolon> U x))
\<Longrightarrow> (case x of (a,b) \<Rightarrow> (y a, b)) \<Ztypecolon> U (fst x) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE\<close>
  by (cases x; simp add: \<phi>Prod_expn')

lemma \<phi>elim'SEi_transformation:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (y x \<Ztypecolon> U x))
\<Longrightarrow> (case x of (a,b) \<Rightarrow> (y a, b)) \<Ztypecolon> \<black_circle> U (fst x) \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  by (cases x; simp add: \<phi>Prod_expn' \<phi>Some_eq_term_strip[where T=T, symmetric])

(* TODO!!!:
lemma \<phi>elim'SE_transformation:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (y x \<Ztypecolon> U))
\<Longrightarrow> (y (fst x), snd x) \<Ztypecolon> U \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Auto_Transform_Hint Y' (x' \<Ztypecolon> T') \<and> P @action \<A>SE True\<close>*)

lemma \<phi>open_abstraction:
  \<open> (x \<Ztypecolon> T) = (y' \<Ztypecolon> U')
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U' \<s>\<u>\<b>\<j> y. y = y' @action to RAW \<close>
  unfolding Action_Tag_def Simplify_def
  by simp

lemma \<phi>make_abstraction:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def MAKE_def by simp

lemma \<phi>make_abstraction'R:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def MAKE_def by simp

lemma \<phi>gen_expansion:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> p \<Turnstile> (x \<Ztypecolon> T) \<equiv> p \<Turnstile> U \<close>
  by simp


ML_file \<open>library/phi_type_algebra/properties.ML\<close>
ML_file \<open>library/phi_type_algebra/typ_def.ML\<close>


(* ML_file \<open>library/tools/type_algebra_guess_mapper.ML\<close> *)
term \<open>HOL.eq\<close>

datatype yyy = YLeaf nat | YNode nat yyy
datatype ('a,'b) xxx = Leaf 'a | LeafB 'b 'a | Node nat \<open>('a,'b) xxx\<close>

term xxx.rel_xxx
thm xxx.set




datatype 'a zzz = AA

ML \<open>val x = the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>xxx\<close>)
val a = BNF_Def.lives_of_bnf x
val s = BNF_Def.sets_of_bnf x
val z = BNF_Def.mk_sets_of_bnf [[],[]] [[\<^typ>\<open>nat\<close>, \<^typ>\<open>int\<close>], [\<^typ>\<open>bool\<close>, \<^typ>\<open>int\<close>]] x
val d = BNF_Def.set_transfer_of_bnf x\<close>

ML \<open>(the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>xxx\<close>))
|> #BT\<close>

declare [[ML_print_depth = 1000]]

ML \<open>#fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))
|> #ctr_sugar

\<close>

ML \<open>BNF_Def.pred_of_bnf (the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>xxx\<close>))\<close>

ML \<open>#fp_bnf_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))\<close>

ML \<open>local val bnf = (the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>list\<close>))
in 
val xx = BNF_Def.rel_map_of_bnf bnf
end\<close>

thm list.rel_eq

ML \<open>(the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))\<close>

ML \<open>
val ths = #fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))
|> #ctr_sugar
|> #disc_thmss
|> flat
val ((_,ths2),_) = Variable.import true ths \<^context>
val xxx = ths2
|> map (Phi_Reasoners.asm_simplify true (Simplifier.clear_simpset \<^context> addsimps @{thms HOL.simp_thms ex_simps[symmetric]}))
|> filter (fn th => (case Thm.concl_of th of \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> => false | _ => true))
|> distinct (Thm.equiv_thm \<^theory>)
\<close>

ML \<open>    
    val equal_binding = \<^binding>\<open>=\<close>;

fun is_disc_binding_valid b =
      not (Binding.is_empty b orelse Binding.eq_name (b, equal_binding));
\<close>

thm list.collapse


ML \<open>#fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))\<close>

ML \<open>BNF_Def.bnf_of \<^context> \<^type_name>\<open>yyy\<close>\<close>

ML \<open>local val bnf = the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>list\<close>) in
val x = BNF_Def.deads_of_bnf bnf
val z = BNF_Def.mk_sets_of_bnf [[]] [[\<^typ>\<open>nat\<close>]] bnf
end\<close>
ML \<open>BNF_Def.bnf_of \<^context> \<^type_name>\<open>option\<close>\<close>


fun fib :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>fib a 0 c = 1+c\<close> | \<open>fib a (Suc 0) c = 1+c\<close> | \<open>fib a (Suc (Suc n)) c = fib a (Suc n) c + fib (a+1) n c\<close>

ML \<open>Function_Common.retrieve_function_data \<^context> \<^term>\<open>fib\<close>\<close>

thm fib.elims






paragraph \<open>Configuration\<close>

(* hide_fact \<phi>inductive_destruction_rule_from_direct_definition
          \<phi>inductive_destruction_rule_from_direct_definition'
          \<phi>Type_conv_eq_1 \<phi>Type_conv_eq_2 \<phi>intro_transformation *)

lemmas [simp_for_\<phi>TA_rule_generation] =
  conj_imp_eq_imp_imp Premise_I sing_times_sing sing_if

setup \<open>
let fun attach_var F =
      let val i = maxidx_of_term F + 1
       in case fastype_of F of \<^Type>\<open>fun T _\<close> => F $ Var(("uu",i),T)
                             | _ => error "Impossible #8da16473-84ef-4bd8-9a96-331bcff88011"
      end
    open Phi_Type_Template_Properties
in (*Phi_Type_Algebra.Detection_Rewr.setup_attribute \<^binding>\<open>\<phi>functor_of\<close>
  "set the pattern rewrite to parse the functor part and the argument part from a term\
  \ matching the patter"
#>*)add_property_kind \<^const_name>\<open>Transformation_Functor\<close>
      (fn (_ $ F $ _ $ _ $ _ $ _) => F)
#> add_property_kind \<^const_name>\<open>Separation_Homo\<^sub>I\<close>
      (fn (_ $ F $ _ $ _ $ _ $ _ $ _ ) => F)
#> add_property_kind \<^const_name>\<open>Separation_Homo\<^sub>E\<close>
      (fn (_ $ F $ _ $ _ $ _ ) => F)
#> add_property_kind \<^const_name>\<open>Semimodule_Scalar_Homo\<close>
      (fn (_ $ F $ _ $ _ ) => attach_var F)
(* #> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Unit_Functor\<close> (fn (_ $ F) => F) *)
#> add_property_kind \<^const_name>\<open>Semimodule_LDistr_Homo\<^sub>Z\<close>
      (fn (_ $ F $ _ $ _ $ _ $ _) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_LDistr_Homo\<^sub>Z_rev\<close>
      (fn (_ $ F $ _ $ _ $ _) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_LDistr_Homo\<^sub>U\<close>
      (fn (_ $ F $ _ $ _ $ _) => attach_var F)
#> add_property_kind \<^const_name>\<open>Identity_Element\<^sub>I\<close>
      (fn (_ $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) $ _) => T)
#> add_property_kind \<^const_name>\<open>Identity_Element\<^sub>E\<close>
      (fn (_ $ (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T)) => T)
(*#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Object_Equiv\<close> (fn (_ $ T $ _) => T)*)
  \<comment> \<open>We do not add Object_Equiv into the property-based template instantiation here because
  it can have special overridings for singular points like that many type operators \<open>F\<close> have a
  wider reachability relation at \<open>F \<circle>\<close>. The overloadings multiply the resulted instantiations
  and they requires priority precedence which is not in the capability of the template
  instantiation automation.\<close>
end
\<close>


(* subsubsection \<open>Void Homo / Functor\<close>

lemma [\<phi>reason 30]:
  \<open> Unit_Homo F
\<Longrightarrow> Semi_Unit_Homo F\<close>
  unfolding Semi_Unit_Homo_def Unit_Homo_def
  by simp

lemma [\<phi>reason 30]:
  \<open> Unit_Functor F
\<Longrightarrow> Semi_Unit_Functor F\<close>
  unfolding Semi_Unit_Functor_def Unit_Functor_def
  by blast

lemma Semi_Unit_Homo_by_functor:
  \<open> Semi_Unit_Homo T
\<Longrightarrow> Semi_Unit_Functor F
\<Longrightarrow> Semi_Unit_Homo (F T)\<close>
  unfolding Semi_Unit_Homo_def Semi_Unit_Functor_def
  by (clarsimp; metis set_eq_iff set_in_1)

lemma Unit_Homo_by_functor:
  \<open> Unit_Homo T
\<Longrightarrow> Unit_Functor F
\<Longrightarrow> Unit_Homo (F T)\<close>
  unfolding Unit_Homo_def Unit_Functor_def Transformation_def
  by (clarsimp; metis set_eq_iff set_in_1)

\<phi>reasoner_ML Unit_Homo_by_functor 50 (\<open>Unit_Homo _\<close>) = \<open>
fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (_ (*Unit_Homo*) $ T) = Thm.major_prem_of sequent
   in case Phi_Type_Algebra.detect_type_operator 1 ctxt T
        of SOME [Ft,Tt] => let
            val rule = Drule.infer_instantiate ctxt
                          [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                          @{thm "Unit_Homo_by_functor"}
             in SOME ((ctxt, rule RS sequent), Seq.empty) end
         | _ => NONE
  end)
\<close>
*)


subsection \<open>Programming Methods to Prove the Properties\<close>

subsubsection \<open>Equiv Object\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>x y. \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x y \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T) M D R F
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Object_Equiv T eq)) M D R F\<close>
  unfolding \<phi>Programming_Method_def Object_Equiv_def Premise_def
  by clarsimp

subsubsection \<open>Transformation Functor\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>T U x g.
            \<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b
        \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
        \<Longrightarrow> x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Transformation_Functor F1 F2 D R mapper)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Transformation_Functor_def Premise_def
  by clarsimp

subsubsection \<open>Semimodule Functor\<close>

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t (x,y) \<Ztypecolon> F (s + t) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_LDistr_Homo\<^sub>Z_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s (x,y) \<Ztypecolon> F (t + s) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_LDistr_Homo\<^sub>Z_rev F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_LDistr_Homo\<^sub>Z_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (\<And>t s T x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> t \<in> Ds \<and> s \<in> Ds \<and> t ##\<^sub>+ s
          \<Longrightarrow> Dx T x
          \<Longrightarrow> x \<Ztypecolon> F (t + s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F s T \<^emph> F t T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_LDistr_Homo\<^sub>U F Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_LDistr_Homo\<^sub>U_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')


subsection \<open>Reasonings and Their Applications\<close>

subsubsection \<open>Vary Type Operator among Instantiations\<close>

definition Type_Variant_of_the_Same_Type_Operator :: \<open> ('a \<Rightarrow> ('b,'c) \<phi>) \<Rightarrow> ('a2 \<Rightarrow> ('b2,'c2) \<phi>) \<Rightarrow> bool \<close>
  where \<open> Type_Variant_of_the_Same_Type_Operator Fa Fb \<longleftrightarrow> True \<close>
  \<comment> \<open>Fa and Fb are the same functor having identical parameters but of different type instantiations.
      We use this to simulate the \<Lambda> operator in system-F\<close>

(*definition Parameter_Variant_of_the_Same_Type :: \<open> ('a,'b) \<phi> \<Rightarrow> ('c,'d) \<phi> \<Rightarrow> bool \<close>
  where \<open> Parameter_Variant_of_the_Same_Type Fa Fb \<longleftrightarrow> True \<close> *)

declare [[
  \<phi>reason_default_pattern
      \<open>Type_Variant_of_the_Same_Type_Operator ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Type_Operator ?Fa _\<close> (100)
  (*and \<open>Parameter_Variant_of_the_Same_Type ?Fa _\<close> \<Rightarrow> \<open>Parameter_Variant_of_the_Same_Type ?Fa _\<close> (100) *),
  
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Type_Variant_of_the_Same_Type_Operator _ _\<close>
  (* \<phi>premise_attribute? [\<phi>reason add] for \<open>Parameter_Variant_of_the_Same_Type _ _\<close> *)
]]

(*
lemma Parameter_Variant_of_the_Same_Type_I [\<phi>reason 1]:
  \<open>Parameter_Variant_of_the_Same_Type Fa Fb\<close>
  unfolding Parameter_Variant_of_the_Same_Type_def .. *)

lemma Type_Variant_of_the_Same_Type_Operator_I [\<phi>reason 1]:
  \<open>Type_Variant_of_the_Same_Type_Operator Fa Fb\<close>
  unfolding Type_Variant_of_the_Same_Type_Operator_def ..

ML_file \<open>library/phi_type_algebra/variant_phi_type_instantiations.ML\<close>

setup \<open>Phi_Type_Template_Properties.add_property_kind
          \<^const_name>\<open>Type_Variant_of_the_Same_Type_Operator\<close> (fn (_ $ F $ _) => F)\<close>


(*
subsubsection \<open>Locale Base of Type Operator\<close>

locale \<phi>Type_Functor =
  fixes F :: \<open>('c,'a) \<phi> \<Rightarrow> ('c1,'a1) \<phi>\<close>
begin
 
(* declare [[\<phi>functor_of \<open>F ?T\<close> \<Rightarrow> \<open>F\<close> \<open>?T\<close> (31)]] *)

declaration \<open>fn m => fn ctxt =>
  let val ctxt' = Context.proof_of ctxt
      fun incr_typ_idx protect d tm =
            Term.map_types (Term.map_atyps (
                    fn T as TVar ((N,i),S) =>
                          if member (op =) protect (N,i) then T else TVar ((N,i+d),S)
                     | T => T)) (Thm.term_of tm)
              |> Thm.cterm_of ctxt'
      fun mk_rules tm =
        let val d = Term.maxidx_of_term (Thm.term_of tm) + 1
            val tm' = Thm.incr_indexes_cterm d tm
            val protect_tvars = fold (fn (_,T) => fn L =>
                                          fold (fn (N,_) => fn L' => insert (op =) N L')
                                               (Term.add_tvarsT T []) L)
                                     (Term.add_vars (Thm.term_of tm) []) []
            val tm'T = incr_typ_idx protect_tvars d tm
            val rule = Thm.instantiate (TVars.make [((("'a",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm ),
                                                    ((("'b",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm')],
                                         Vars.make [((("Fa",0), Thm.typ_of_cterm tm ), tm ),
                                                    ((("Fb",0), Thm.typ_of_cterm tm'), tm')])
                                       @{thm Parameter_Variant_of_the_Same_Type_I}
            val rule'= Thm.instantiate (TVars.make [((("'a",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm ),
                                                    ((("'b",0),\<^sort>\<open>type\<close>), Thm.ctyp_of_cterm tm'T)],
                                         Vars.make [((("Fa",0), Thm.typ_of_cterm tm ), tm ),
                                                    ((("Fb",0), Thm.typ_of_cterm tm'T), tm'T)])
                                       @{thm Type_Variant_of_the_Same_Type_Operator_I}
         in [rule,rule']
        end
      fun collect_rules ret ctm =
            case Thm.term_of ctm
              of _ $ _ => collect_rules (mk_rules ctm @ ret) (Thm.dest_fun ctm)
               | _ => mk_rules ctm @ ret
      val ctm = Morphism.cterm m \<^cterm>\<open>F\<close>
      val rules = collect_rules [] ctm
    (* val _ = Phi_Reasoner.info_pretty_generic ctxt 0 (fn () => let open Pretty in
                  chunks (str "Generated reasoning rules: " ::
                          map (fn rule => item [Syntax.pretty_term ctxt' (Thm.prop_of rule)]) rules)
                end) *)
   in Phi_Reasoner.add_rules (
        map (fn rule => ([rule], \<^here>, Phi_Reasoner.NORMAL_LOCAL_CUT, 1000, [], [], NONE)) rules
        ) ctxt
  end
\<close>
(*
lemma [\<phi>reason add!]:
  \<open>Type_Variant_of_the_Same_Type_Operator F F\<close>
  unfolding Type_Variant_of_the_Same_Type_Operator_def ..*)

(*priority of the 2-arity functor: 32
  priority of the n-arity functor: 3n
*)

end
*)

subsubsection \<open>Transformation Functor\<close>

lemma Transformation_Functor_L_simp_cong:
  \<open> Transformation_Functor Fa Fa (\<lambda>x. {x}) (\<lambda>x. \<top>) (\<lambda>x. x)
\<Longrightarrow> (x \<Ztypecolon> T) \<equiv> (x' \<Ztypecolon> T')
\<Longrightarrow> (x \<Ztypecolon> Fa T) \<equiv> (x' \<Ztypecolon> Fa T')\<close>
  unfolding Transformation_Functor_def Transformation_def atomize_eq
  apply (auto simp add: BI_eq_iff)
  subgoal premises prems for xa
    using prems(1)[THEN spec[where x=T], THEN spec[where x=T'], THEN spec[where x=x],
            THEN spec[where x=\<open>\<lambda>_ c. c = x'\<close>], simplified]
    using prems(2) prems(3) by blast
  subgoal premises prems for xa
    using prems(1)[THEN spec[where x=T'], THEN spec[where x=T], THEN spec[where x=x'],
            THEN spec[where x=\<open>\<lambda>_ c. c = x\<close>], simplified]
    using prems(2) prems(3) by blast
  .

attribute_setup \<phi>TA_internal_simplify_special_cases = \<open>Scan.succeed (
  let fun rule_attribute f (x, th) =
            if Thm.is_free_dummy th
            then (NONE, NONE)
            else (SOME x, SOME (f x th))
   in rule_attribute (fn generic => fn rule =>
        let val ctxt = Context.proof_of generic
            val sctxt = Simplifier.clear_simpset ctxt addsimps @{thms meta_Ball_sing}
            val rule' = Simplifier.full_simplify sctxt rule
                      |> Phi_Help.instantiate_higher_order_schematic_var ~2 ctxt
         in rule'
        end)
  end
)\<close>

 
locale Transformation_Functor_L =
  fixes Fa :: \<open>('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>\<close>
    and Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
    and D  :: \<open>'c \<Rightarrow> 'a set\<close>
    and R  :: \<open>'c \<Rightarrow> 'e set\<close>
    and mapper :: \<open>('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool\<close>
    and Prem :: bool
  assumes Transformation_Functor[\<phi>reason 1100]:
    \<open>Prem \<Longrightarrow> Transformation_Functor Fa Fb D R mapper\<close>
begin

lemma transformation[\<phi>TA_internal_simplify_special_cases,
                     \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Fb _ \<s>\<u>\<b>\<j> y. _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>
  unfolding meta_Ball_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def]
  by blast

declaration \<open>fn m => fn ctxt =>
  let val rule = Morphism.thm m @{thm Transformation_Functor}
      val thy = Context.theory_of ctxt
   in if Pattern.matches thy (\<^pattern>\<open>True \<Longrightarrow> Transformation_Functor _ _ (\<lambda>x. {x}) (\<lambda>x. \<top>) (\<lambda>x. x)\<close>, Thm.prop_of rule)
      then let
        val rule' = (@{thm TrueI} RS rule) RS @{thm Transformation_Functor_L_simp_cong}
        val (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ LHS $ _) = Thm.concl_of rule'
         in Simplifier.map_ss (fn ctxt =>
              ctxt addsimprocs [Simplifier.cert_simproc thy "Transformation_Functor_L.\<phi>simp_cong" {
                lhss = [LHS],
                proc = K (Phi_SimpProc.cong rule')
              }]
            ) ctxt
        end
      else ctxt
  end\<close>

(*
lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<s>\<u>\<b>\<j> y. _ @action \<A>_structural _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>_structural Act)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using transformation .
*)

(*
lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<s>\<u>\<b>\<j> y. _ @action as _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action as Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action as Z \<close>
  unfolding Action_Tag_def
  using transformation .
*)

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fb Z) \<close>
  unfolding Action_Tag_def
  using transformation .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z) \<close>
  unfolding Action_Tag_def
  using transformation .
   
lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>transformation_based_simp default 40 no trigger]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>simp)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>simp \<close>
  unfolding Action_Tag_def Premise_def
  using transformation[unfolded Premise_def] .

end

(*
lemma [\<phi>reason_template default 53 requires Separation_Homo\<^sub>E]:
  \<open> Transformation_Functor Fa Fb D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (\<s>\<p>\<l>\<i>\<t> Z))
\<Longrightarrow> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action \<A>\<T>split_step
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action to (\<s>\<p>\<l>\<i>\<t> (Fa Z)) \<close>
  unfolding Action_Tag_def meta_Ball_def Premise_def Transformation_Functor_def Ball_def
  by (rule transformation_trans[where P=True and Q=True and B=\<open>y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>, simplified], blast)

lemma [\<phi>reason_template default 50 requires Separation_Homo\<^sub>E]:
  \<open> Transformation_Functor Fa Fb D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (\<s>\<p>\<l>\<i>\<t> Z))
\<Longrightarrow> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action \<A>\<T>split_step
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> FcU \<s>\<u>\<b>\<j> z. g' x z @action to (\<s>\<p>\<l>\<i>\<t> Z) \<close>
  unfolding Action_Tag_def meta_Ball_def Premise_def Transformation_Functor_def Ball_def
  by (rule transformation_trans[where P=True and Q=True and B=\<open>y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>, simplified], blast)
*)

lemma [\<phi>reason_template default 45]:
  \<open> Separation_Homo\<^sub>E Fa\<^sub>L Fa\<^sub>R Fb un
\<Longrightarrow> x \<Ztypecolon> Fb (U\<^sub>L \<^emph>\<^sub>\<A> U\<^sub>R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fa\<^sub>L U\<^sub>L \<^emph>\<^sub>\<A> Fa\<^sub>R U\<^sub>R \<s>\<u>\<b>\<j> y. y = un x @action \<A>simp\<close>
  unfolding Separation_Homo\<^sub>E_def Action_Tag_def \<phi>Auto_Prod_def
  by (clarsimp simp add: Subjection_transformation_expn Ex_transformation_expn)


locale Functional_Transformation_Functor =
  Transformation_Functor_L Fa Fb D R mapper Prem
  for Fa :: \<open>('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>\<close>
  and Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
  and D  :: \<open>'c \<Rightarrow> 'a set\<close>
  and R  :: \<open>'c \<Rightarrow> 'e set\<close>
  and mapper :: \<open>('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f \<Rightarrow> bool\<close> \<comment> \<open>relational mapper\<close>
  and Prem :: bool
+ fixes pred_mapper :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> bool\<close>
    and func_mapper :: \<open>('a \<Rightarrow> 'e) \<Rightarrow> 'c \<Rightarrow> 'f\<close>
  assumes functional_mapper:
      \<open>Prem \<Longrightarrow> mapper (\<lambda>a b. b = f a \<and> P a) = (\<lambda>a' b'. b' = func_mapper f a' \<and> pred_mapper P a')\<close>

setup \<open>Phi_Type_Template_Properties.add_property_kind \<^const_name>\<open>Functional_Transformation_Functor\<close>
            (fn (_ $ F $ _ $ _ $ _ $ _ $ _ $ _ $ _) => F)\<close>

context Functional_Transformation_Functor
begin

lemma Functional_Transformation_Functor[\<phi>reason add]:
  \<open>Functional_Transformation_Functor Fa Fb D R mapper Prem pred_mapper func_mapper\<close>
  by (simp add: Functional_Transformation_Functor_axioms)

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 40 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Fb _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x\<close>
  unfolding meta_Ball_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], simplified functional_mapper,
          simplified]
  by blast

lemma functional_transformation:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x\<close>
  unfolding meta_Ball_def Argument_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], simplified functional_mapper,
          simplified]
  by blast

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action \<A>_structural _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action \<A>_structural Act)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action \<A>_structural Act \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .

(*
lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action as _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action as Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action as Z \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .
*)

(*
lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 35 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action to _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action to Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action to (Fb Z) \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .

lemma [\<phi>TA_internal_simplify_special_cases,
       \<phi>reason default 31 for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action to _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action to Z)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper P x @action to Z \<close>
  unfolding Action_Tag_def
  using functional_transformation[unfolded Argument_def] .
*)

end

hide_fact Transformation_Functor_L_simp_cong



subsubsection \<open>Separation Homomorphism\<close>

lemma Object_Sep_Homo\<^sub>I_subdom[\<phi>reason default 1]:
  \<open> Object_Sep_Homo\<^sub>I T Da
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Db \<subseteq> Da
\<Longrightarrow> Object_Sep_Homo\<^sub>I T Db\<close>
  unfolding Object_Sep_Homo\<^sub>I_def Premise_def subset_iff
  by blast

(*Object_Sep_Homo\<^sub>I is necessary at least for composition \<phi>-type
Object_Sep_Homo\<^sub>I B \<longleftrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x)
*)

(*There are two inner element \<open>a,b\<close>, we construct an inner transformation from \<open>(a \<Ztypecolon> T) * (b \<Ztypecolon> T)\<close>
    to \<open>(b * a) \<Ztypecolon> T\<close>
  Note here \<open>c = b * a\<close> only if the \<open>*\<close> is defined between b and a.
*)

lemma Separation_Homo_functor[\<phi>reason_template 50]:
  \<open> Separation_Homo\<^sub>I F F F' Prem Ds zz
\<Longrightarrow> Transformation_Functor F' F D R m
\<Longrightarrow> (\<And>yx \<in> Ds. Prem T T yx)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x y z. m (\<lambda>(a, b) c. c = b * a \<and> b ## a \<and> (a, b) \<in> D (zz (x, y))) (zz (x, y)) z
                        \<longrightarrow> z = y * x \<and> y ## x) \<and>
           (\<forall>x y a b. (a, b) \<in> D (zz (x, y)) \<longrightarrow> b * a \<in> R (zz (x, y)))
\<Longrightarrow> Object_Sep_Homo\<^sub>I T (Set.bind Ds (D o zz))
\<Longrightarrow> Object_Sep_Homo\<^sub>I (F T) Ds\<close>
  unfolding Object_Sep_Homo\<^sub>I_def Transformation_Functor_def Separation_Homo\<^sub>I_def Premise_def
            meta_Ball_def meta_case_prod_def split_paired_all
  apply (simp (no_asm_use) add: \<phi>Prod_expn'[symmetric] del: split_paired_All; clarify)
  subgoal premises prems for x y
  proof -
    have t1: \<open>\<forall>a\<in>D (zz (y, x)). a \<Ztypecolon> T \<^emph> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> T \<s>\<u>\<b>\<j> b. (case a of (b, a) \<Rightarrow> \<lambda>c. c = a * b \<and> a ## b \<and> (b, a) \<in> D (zz (y, x))) b\<close>
      by (clarsimp, insert prems(4,7), blast)
    from prems(2)[THEN spec[where x=\<open>T \<^emph> T\<close>], THEN spec[where x=T], THEN spec[where x=\<open>zz (y,x)\<close>],
                 THEN spec[where x=\<open>\<lambda>(b,a) c. c = a * b \<and> a ## b \<and> (b,a) \<in> D (zz (y,x))\<close>],
                 THEN mp, OF t1]
         prems(5)[THEN spec[where x=y], THEN spec[where x=x]]
         prems(1,3,6,7)
    show ?thesis
      by (clarsimp simp add: Transformation_def; blast)
  qed .


(* \<p>\<r>\<e>\<m>\<i>\<s>\<e> mapper {(a * b, (a, b)) |a b. a ## b} = {(a * b, (a, b)) |a b. a ## b}
\<Longrightarrow>  *)

(* (*Is this really needed?*)
lemma Separation_Homo_eq_functor:
  \<open> (\<And>x y z. \<p>\<r>\<e>\<m>\<i>\<s>\<e> (m (\<lambda>(a, b) c. c = a * b \<and> a ## b \<and> (a, b) \<in> D (x, y)) (x, y) z
                        \<longrightarrow> z = x * y \<and> x ## y))
\<Longrightarrow> Sep_Homo_Ty F F F' T T
\<Longrightarrow> Transformation_Functor F F' pred mapper
\<Longrightarrow> Separation_Homo_eq T
\<Longrightarrow> Separation_Homo_eq (F T)\<close>
  unfolding Separation_Homo_eq_def Transformation_Functor_def Sep_Homo_Ty_def
            Object_Sep_Homo\<^sub>I_def
  apply (clarsimp simp add: \<phi>Prod_split[symmetric])
  subgoal premises prems for x y
  proof -
    thm prems(2)[THEN spec[where x=T], THEN spec[where x=\<open>T \<^emph> T\<close>],
                 THEN spec[where x=\<open>{x*y}\<close>],
                 THEN spec[where x=\<open>{(x * y, (x, y))}\<close>]]
thm prems

  by (simp; metis \<phi>Prod_split) *)

(*
\<phi>reasoner_ML Separation_Homo_functor 50 (\<open>Object_Sep_Homo\<^sub>I _\<close>) = \<open>
fn (ctxt, sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (Const(\<^const_name>\<open>Object_Sep_Homo\<^sub>I\<close>, _) $ T)
        = Thm.major_prem_of sequent
   in case Phi_Functor_Detect.detect 1 ctxt T
        of SOME [Ft,Tt] => let
            val rule = Drule.infer_instantiate ctxt
                        [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                        @{thm "Separation_Homo_functor"}
            in SOME ((ctxt, rule RS sequent), Seq.empty) end
            handle THM _ => NONE
         | _ => NONE
  end)
\<close>
*)

(*
\<phi>reasoner_ML Separation_Homo_eq_functor 50 (\<open>Separation_Homo_eq _\<close>) = \<open>
fn (ctxt, sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (Const(\<^const_name>\<open>Separation_Homo_eq\<close>, _) $ T)
        = Thm.major_prem_of sequent
   in case Phi_Functor_Detect.detect 1 ctxt T
        of SOME [Ft,Tt] => let
              val rule = Drule.infer_instantiate ctxt
                            [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                            @{thm "Separation_Homo_eq_functor"}
              in SOME ((ctxt, rule RS sequent), Seq.empty) end
              handle THM _ => NONE
         | _ => NONE
  end)
\<close>
*)


locale Sep_Homo_Type_zip_L =
  fixes Fa :: \<open>('b::sep_magma,'a) \<phi> \<Rightarrow> ('d::sep_magma,'c) \<phi>\<close>
    and Fb :: \<open>('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>\<close>
    and Fc :: \<open>('b,'a \<times> 'e) \<phi> \<Rightarrow> ('d,'g) \<phi>\<close>
    and D  :: \<open>('c \<times> 'f) set\<close>
    and z  :: \<open>'c \<times> 'f \<Rightarrow> 'g\<close>
    and Prem :: \<open>('b,'a) \<phi> \<Rightarrow> ('b,'e) \<phi> \<Rightarrow> 'c \<times> 'f \<Rightarrow> bool\<close>
  assumes Separation_Homo\<^sub>I: \<open>Separation_Homo\<^sub>I Fa Fb Fc Prem D z\<close>
begin

(*TODO!!!!

Do we really need it?*)

end



subsubsection \<open>Semimodule\<close>

lemma [\<phi>reason_template [assertion_simps]]:
  \<open> Semimodule_Scalar_Homo F T D
\<Longrightarrow> a \<in> D \<and> b \<in> D
\<Longrightarrow> F a (F b T) = F (b * a) T\<close>
  unfolding Semimodule_Scalar_Homo_def
  by simp





subsubsection \<open>Reasonings in Separation Extraction\<close>

paragraph \<open>Transformation Functor\<close>

declare [[\<phi>trace_reasoning = 2]]

lemma "_Structural_Extract_general_rule_":
  \<open> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Prem
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 Prem_SH Dz z
\<Longrightarrow> Prem_SH T W x
\<Longrightarrow> Separation_Homo\<^sub>E F3 F2 F23 uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P x @action \<A>SE )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f (z x)) \<Ztypecolon> F3 U \<^emph> F2 R \<w>\<i>\<t>\<h> pred_mapper P (z x) @action \<A>SE \<close>
  \<medium_left_bracket> premises FTF and [\<phi>reason add] and _ and [\<phi>reason add] and _ and _ and Tr
    interpret Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U \<^emph> R\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_Separation_Functor_unzip
  \<medium_right_bracket> .
 
declare "_Structural_Extract_general_rule_"[THEN \<A>SE_clean_waste, \<phi>reason_template default 80]

lemma [THEN \<A>SE_clean_waste_TH, \<phi>reason_template default 81]:
  \<open> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Prem
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 Prem_SH Dz z
\<Longrightarrow> Prem_SH T W x
\<Longrightarrow> Separation_Homo\<^sub>E F3 F2 F23 uz
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F1 F1'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F2 F2'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F3 F3'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F4 F4'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y\<^sub>H \<Ztypecolon> U\<^sub>H \<^emph> R\<^sub>H) (x\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P x) @action \<A>SE )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f (z x)) \<Ztypecolon> F3 U \<^emph> F2 R \<w>\<i>\<t>\<h> 
      Auto_Transform_Hint (y'\<^sub>H \<Ztypecolon> F3' U\<^sub>H \<^emph> F2' R\<^sub>H) (x'\<^sub>H \<Ztypecolon> F1' T\<^sub>H \<^emph> F4' W\<^sub>H) \<and> pred_mapper P (z x) @action \<A>SE \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using "_Structural_Extract_general_rule_"[where f=f and uz=uz and func_mapper=func_mapper and z=z and pred_mapper=pred_mapper] .


(* This crazy rule is for the boundary cases when we reason the last element and when the algebra doesn't
   have an identity element so that we cannot reduce it to the usual case by adding an identity element at the tail.

The idea is to lift the non-unital algebra by adding an identity element. We use \<^const>\<open>\<black_circle>\<close> for it.
But it is not the end. Because substantially its reasoning has no identity element, we have to use
\<^term>\<open>\<half_blkcirc>[Cw] W\<close> with a boolean flag \<open>Cw\<close> to rudimentarily check if the remainder is needed or not.

If u cannot use the identity element, the reasoning itself changes,
like sometimes you have to apply Sep_Homo zipper while in another case you shouldn't use that.
There is no trivial degeneration of Sep_Homo. There is no an identity element representing nothing.
So if u are going to zip something, u really need to zip some two concrete things,
instead of using the identity element to represent the degenerated situation where you actually zipped nothing.
It forces us to really consider the cases of having remainders or not in the reasoning.

The rule below is complicated, but is branch-less in reasoning. All branch expressions are in object level,
free from explosion of expression, and can be simplified easily because the boolean flags are
assigned by constants after the reasoning.

*)
lemma "_Structural_Extract_general_rule_i_"[\<phi>reason_template default 80]:
  \<open> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Prem
\<Longrightarrow> Functional_Transformation_Functor F14 F3 Dom Rng'r mapper'r Prem'r pred_mapper func_mapper'r
\<Longrightarrow> Prem'r
\<Longrightarrow> Functional_Transformation_Functor F1 F23 Dom'w Rng'w mapper'w Prem'w pred_mapper'w func_mapper'w
\<Longrightarrow> Prem'w
\<Longrightarrow> Functional_Transformation_Functor F1 F3  Dom'w Rng'b mapper'b Prem'b pred_mapper'w func_mapper'b
\<Longrightarrow> Prem'b
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 Prem_SH Dz z
\<Longrightarrow> Prem_SH T W x
\<Longrightarrow> Separation_Homo\<^sub>E F3 F2 F23 uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e>
        (Cw \<longrightarrow> x \<in> Dz) \<and>
        (if Cw then if Cr then (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
                          else (\<forall>a. a \<in> Dom (z x) \<longrightarrow> fst (f a) \<in> Rng'r (z x))
               else if Cr then (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> f (a, undefined) \<in> Rng'w (fst x))
                          else (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> fst (f (a, undefined)) \<in> Rng'b (fst x)))

\<Longrightarrow> (\<And>x \<in> (if Cw then Dom (z x) else Dom'w (fst x) \<times> {undefined}).
        x \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P x @action \<A>SEi )

\<Longrightarrow> x \<Ztypecolon> \<black_circle> F1 T \<^emph> \<half_blkcirc>[Cw] F4 W

    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if Cw then if Cr then uz (func_mapper f (z x))
                                else (func_mapper'r (fst o f) (z x), undefined)
                     else if Cr then uz (func_mapper'w (\<lambda>x. f (x, undefined)) (fst x))
                                else (func_mapper'b (\<lambda>x. fst (f (x, undefined))) (fst x), undefined))
                \<Ztypecolon> \<black_circle> F3 U \<^emph> \<half_blkcirc>[Cr] F2 R

    \<w>\<i>\<t>\<h> (if Cw then pred_mapper P (z x) else pred_mapper'w (\<lambda>x. P (x, undefined)) (fst x))
    @action \<A>SEi \<close>
  apply (cases Cw; cases Cr; simp add: \<phi>Some_\<phi>Prod)
  apply (simp_all add: \<phi>Some_\<phi>None_freeobj \<phi>Some_transformation_strip Action_Tag_def
                       "_Structural_Extract_general_rule_"[unfolded Action_Tag_def])
  \<medium_left_bracket> premises [] and [] and FTF and [] and [] and [] and [] and []
         and _ and [\<phi>reason add] and []
         and _ and Tr
    interpret Functional_Transformation_Functor F14 F3 Dom Rng'r mapper'r True pred_mapper func_mapper'r
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U\<close> and f=\<open>fst o f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
  \<medium_right_bracket>
  \<medium_left_bracket> premises [] and [] and [] and [] and FTF and [] and [] and []
         and [] and [\<phi>reason add] and _
         and _ and Tr
    interpret Functional_Transformation_Functor F1 F23 Dom'w Rng'w mapper'w True pred_mapper'w func_mapper'w
      using FTF . ;;
    apply_rule functional_transformation[where U=\<open>U \<^emph> R\<close> and f=\<open>\<lambda>x. f (x, undefined)\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
    apply_Separation_Functor_unzip
  \<medium_right_bracket>
  \<medium_left_bracket> premises [] and [] and [] and [] and [] and [] and FTF and []
         and [] and [\<phi>reason add] and []
         and _ and Tr
    interpret Functional_Transformation_Functor F1 F3 Dom'w Rng'b mapper'b True pred_mapper'w func_mapper'b
      using FTF . ;;
    apply_rule functional_transformation[where U=\<open>U\<close> and f=\<open>\<lambda>x. fst (f (x, undefined))\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
  \<medium_right_bracket> .

lemma "_Structural_Extract_general_rule_i_TH_"[\<phi>reason_template default 81]:
  \<open> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Prem
\<Longrightarrow> Functional_Transformation_Functor F14 F3 Dom Rng'r mapper'r Prem'r pred_mapper func_mapper'r
\<Longrightarrow> Prem'r
\<Longrightarrow> Functional_Transformation_Functor F1 F23 Dom'w Rng'w mapper'w Prem'w pred_mapper'w func_mapper'w
\<Longrightarrow> Prem'w
\<Longrightarrow> Functional_Transformation_Functor F1 F3  Dom'w Rng'b mapper'b Prem'b pred_mapper'w func_mapper'b
\<Longrightarrow> Prem'b
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 Prem_SH Dz z
\<Longrightarrow> Prem_SH T W x
\<Longrightarrow> Separation_Homo\<^sub>E F3 F2 F23 uz
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F1 F1'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F2 F2'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F3 F3'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F4 F4'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e>
        (Cw \<longrightarrow> x \<in> Dz) \<and>
        (if Cw then if Cr then (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
                          else (\<forall>a. a \<in> Dom (z x) \<longrightarrow> fst (f a) \<in> Rng'r (z x))
               else if Cr then (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> f (a, undefined) \<in> Rng'w (fst x))
                          else (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> fst (f (a, undefined)) \<in> Rng'b (fst x)))

\<Longrightarrow> (\<And>x \<in> (if Cw then Dom (z x) else Dom'w (fst x) \<times> {undefined}).
        x \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
            Auto_Transform_Hint (y1\<^sub>H \<Ztypecolon> \<black_circle> U\<^sub>H \<^emph> \<half_blkcirc>[Cr] R\<^sub>H) (x1\<^sub>H \<Ztypecolon> \<black_circle> T\<^sub>H \<^emph> \<half_blkcirc>[Cw] W\<^sub>H) \<and> P x @action \<A>SEi )

\<Longrightarrow> x \<Ztypecolon> \<black_circle> F1 T \<^emph> \<half_blkcirc>[Cw] F4 W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if Cw then if Cr then uz (func_mapper f (z x))
                                else (func_mapper'r (fst o f) (z x), undefined)
                     else if Cr then uz (func_mapper'w (\<lambda>x. f (x, undefined)) (fst x))
                                else (func_mapper'b (\<lambda>x. fst (f (x, undefined))) (fst x), undefined))
                \<Ztypecolon> \<black_circle> F3 U \<^emph> \<half_blkcirc>[Cr] F2 R

    \<w>\<i>\<t>\<h> Auto_Transform_Hint (y2\<^sub>H \<Ztypecolon> \<black_circle> F3' U\<^sub>H \<^emph> \<half_blkcirc>[Cr] F2' R\<^sub>H) (x2\<^sub>H \<Ztypecolon> \<black_circle> F1' T\<^sub>H \<^emph> \<half_blkcirc>[Cw] F4' W\<^sub>H)
      \<and> (if Cw then pred_mapper P (z x) else pred_mapper'w (\<lambda>x. P (x, undefined)) (fst x))
    @action \<A>SEi \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using "_Structural_Extract_general_rule_i_"[where pred_mapper=pred_mapper
          and pred_mapper'w=pred_mapper'w and P=P and uz=uz and func_mapper=func_mapper
          and func_mapper'r=func_mapper'r and func_mapper'w=func_mapper'w
          and func_mapper'b=func_mapper'b] .

  
lemma "_Structural_Extract_general_rule_a_":
  \<open> Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Prem
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 Prem_SH Dz z
\<Longrightarrow> Prem_SH T W x
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<w>\<i>\<t>\<h> P x @action \<A>SEa )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f (z x) \<Ztypecolon> F3 U \<w>\<i>\<t>\<h> pred_mapper P (z x) @action \<A>SEa \<close>
  \<medium_left_bracket> premises FTF and [\<phi>reason add] and _ and [\<phi>reason add] and _ and Tr
    interpret Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
  \<medium_right_bracket> .

declare "_Structural_Extract_general_rule_a_"[THEN \<A>SEa_clean_waste, \<phi>reason_template default 80]

lemma "_Structural_Extract_general_rule_a_TH_"[\<phi>reason_template default 81]:
  \<open> Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Prem
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 Prem_SH Dz z
\<Longrightarrow> Prem_SH T W x
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F1 F1'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F3 F3'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F4 F4'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<w>\<i>\<t>\<h>
      Auto_Transform_Hint (y1\<^sub>H \<Ztypecolon> U\<^sub>H) (x2\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P x @action \<A>SEa )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f (z x) \<Ztypecolon> F3 U \<w>\<i>\<t>\<h>
      Auto_Transform_Hint (y2\<^sub>H \<Ztypecolon> F3' U\<^sub>H) (x2\<^sub>H \<Ztypecolon> F1' T\<^sub>H \<^emph> F4' W\<^sub>H) \<and> pred_mapper P (z x) @action \<A>SEa \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using "_Structural_Extract_general_rule_a_"[where func_mapper=func_mapper and P=P
            and pred_mapper=pred_mapper] .

(*
lemma "_Structural_Extract_general_rule_b_":
  \<open> Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 Dz z
\<Longrightarrow> Prem
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<w>\<i>\<t>\<h> P x @action \<A>SE False)
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f (z x) \<Ztypecolon> F3 U \<w>\<i>\<t>\<h> pred_mapper P (z x) @action \<A>SE False \<close>
  \<medium_left_bracket> premises FTF and _ and [\<phi>reason add] and _ and Tr
    interpret Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
  \<medium_right_bracket> .

declare "_Structural_Extract_general_rule_b_"[(*THEN SE_clean_waste,*) \<phi>reason_template 80]
*)


paragraph \<open>Seminearing\<close>







declare [[\<phi>trace_reasoning = 2]]

lemma SE_general_Scala_Seminearing_left: (*need test, to be tested once we have usable test case*)
  \<open> Semimodule_Scalar_Homo F3 U Ds
\<Longrightarrow> Semimodule_Scalar_Homo F4 W Ds
\<Longrightarrow> Separation_Homo\<^sub>I (F1 a) (F4 a) F14 Prem_SH Dz z
\<Longrightarrow> Prem_SH T (F4 c W) x
\<Longrightarrow> Separation_Homo\<^sub>E (F3 a) (F2 a) F23 uz
\<Longrightarrow> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Prem
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c * a = b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> F4 c W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3 c U \<^emph> R \<w>\<i>\<t>\<h> P x @action \<A>SE )
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F4 b W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f (z x)) \<Ztypecolon> F3 b U \<^emph> F2 a R \<w>\<i>\<t>\<h> pred_mapper P (z x) @action \<A>SE \<close>
  \<medium_left_bracket> premises LSF3[\<phi>reason add] and LSF4[\<phi>reason add] and _ and [\<phi>reason add] and _ and FTF and [\<phi>reason add]
             and _ and _ and _ and Tr
    interpret Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (metis LSF4 Semimodule_Scalar_Homo_def \<open>a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds\<close> the_\<phi>(6))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (metis LSF3 Semimodule_Scalar_Homo_def \<open>a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds\<close> the_\<phi>(6)) ;;
    unfold F4D
    apply_rule apply_Separation_Functor_zip[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U \<^emph> R\<close> and f=f and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Functor_unzip[where x=\<open>func_mapper f (z x)\<close>]
    fold F3D
  \<medium_right_bracket> .

declare SE_general_Scala_Seminearing_left[THEN \<A>SE_clean_waste, \<phi>reason_template add 60]

lemma SE_general_Scala_Seminearing_left_b: (*need test, to be tested once we have usable test case*)
  \<open> Semimodule_Scalar_Homo F3 U Ds
\<Longrightarrow> Semimodule_Scalar_Homo F4 W Ds
\<Longrightarrow> Separation_Homo\<^sub>I (F1 a) (F4 a) F14 Prem_SH Dz z
\<Longrightarrow> Separation_Homo\<^sub>E (F3 a) (F2 a) F23 uz
\<Longrightarrow> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Functional_Transformation_Functor F14 (F3 a) Dom Rng'r mapper'r Prem'r pred_mapper func_mapper'r
\<Longrightarrow> Functional_Transformation_Functor (F1 a) F23 Dom'w Rng'w mapper'w Prem'w pred_mapper'w func_mapper'w
\<Longrightarrow> Functional_Transformation_Functor (F1 a) (F3 a) Dom'w Rng'b mapper'b Prem'b pred_mapper'w func_mapper'b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c * a = b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds
\<Longrightarrow> Prem \<comment> \<open>TODO: move!\<close>
\<Longrightarrow> Prem_SH T (F4 c W) x
\<Longrightarrow> Prem'r
\<Longrightarrow> Prem'w
\<Longrightarrow> Prem'b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Cw \<longrightarrow> x \<in> Dz) \<and>
           (if Cw then if Cr then (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
                             else (\<forall>a. a \<in> Dom (z x) \<longrightarrow> fst (f a) \<in> Rng'r (z x))
                  else if Cr then (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> f (a, undefined) \<in> Rng'w (fst x))
                             else (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> fst (f (a, undefined)) \<in> Rng'b (fst x)))

\<Longrightarrow> (\<And>x \<in> (if Cw then Dom (z x) else Dom'w (fst x) \<times> {undefined}).
          x \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] F4 c W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> \<black_circle> F3 c U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P x @action \<A>SEi )

\<Longrightarrow> x \<Ztypecolon> \<black_circle> F1 a T \<^emph> \<half_blkcirc>[Cw] F4 b W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if Cw then if Cr then uz (func_mapper f (z x))
                                else (func_mapper'r (fst o f) (z x), undefined)
                     else if Cr then uz (func_mapper'w (\<lambda>x. f (x, undefined)) (fst x))
                                else (func_mapper'b (\<lambda>x. fst (f (x, undefined))) (fst x), undefined))
                \<Ztypecolon> \<black_circle> F3 b U \<^emph> \<half_blkcirc>[Cr] F2 a R
    \<w>\<i>\<t>\<h> (if Cw then pred_mapper P (z x) else pred_mapper'w (\<lambda>x. P (x, undefined)) (fst x))
    @action \<A>SEi \<close>
  apply (cases Cw; cases Cr; simp add: \<phi>Some_\<phi>Prod)
  apply (simp_all add: \<phi>Some_\<phi>None_freeobj \<phi>Some_transformation_strip Action_Tag_def
                       "SE_general_Scala_Seminearing_left"[unfolded Action_Tag_def])
  \<medium_left_bracket> premises LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and _ and []
         and [] and FTF and [] and []
         and _ and _
         and [] and [\<phi>reason add] and [] and [] and []
         and _ and Tr
    interpret Functional_Transformation_Functor F14 \<open>F3 a\<close> Dom Rng'r mapper'r True pred_mapper func_mapper'r
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (metis LSF4 Semimodule_Scalar_Homo_def \<open>a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds\<close> the_\<phi>(6))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (metis LSF3 Semimodule_Scalar_Homo_def \<open>a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds\<close> the_\<phi>(6)) ;;
    unfold F4D
    apply_rule apply_Separation_Functor_zip[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U\<close> and f=\<open>fst o f\<close> and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
    fold F3D
  \<medium_right_bracket>
  \<medium_left_bracket> premises LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and [] and _
         and [] and [] and FTF and []
         and _ and _
         and [] and [\<phi>reason add] and [] and [] and []
         and _ and Tr
    interpret Functional_Transformation_Functor \<open>F1 a\<close> F23 Dom'w Rng'w mapper'w True pred_mapper'w func_mapper'w
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (metis LSF4 Semimodule_Scalar_Homo_def the_\<phi>(2) the_\<phi>(4) the_\<phi>(5))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (metis LSF3 Semimodule_Scalar_Homo_def the_\<phi>(2) the_\<phi>(4) the_\<phi>(5)) ;;
    unfold F4D
    apply_rule functional_transformation[where U=\<open>F3 c U \<^emph> R\<close> and f=\<open>\<lambda>x. f (x, undefined)\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
    apply_rule apply_Separation_Functor_unzip[where x=\<open>func_mapper'w (\<lambda>x. f (x, undefined)) (fst x)\<close> and Fc = F23]
    fold F3D
  \<medium_right_bracket>
  \<medium_left_bracket> premises LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and _ and _
         and [] and [] and [] and FTF
         and _ and _
         and [] and [\<phi>reason add] and [] and [] and []
         and _ and Tr
    interpret Functional_Transformation_Functor \<open>F1 a\<close> \<open>F3 a\<close> Dom'w Rng'b mapper'b True pred_mapper'w func_mapper'b
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (metis LSF4 Semimodule_Scalar_Homo_def the_\<phi>(2) the_\<phi>(4) the_\<phi>(5))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (metis LSF3 Semimodule_Scalar_Homo_def the_\<phi>(2) the_\<phi>(4) the_\<phi>(5)) ;;
    unfold F4D
    apply_rule functional_transformation[where U=\<open>F3 c U\<close> and f=\<open>\<lambda>x. fst (f (x, undefined))\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
    fold F3D
  \<medium_right_bracket> .



lemma SE_general_Scala_Seminearing_left_b: (*need test, to be tested once we have usable test case*)
  \<open> Semimodule_Scalar_Homo F3 U Ds
\<Longrightarrow> Semimodule_Scalar_Homo F4 W Ds
\<Longrightarrow> Separation_Homo\<^sub>I (F1 a) (F4 a) F14 Prem_SH Dz z
\<Longrightarrow> Functional_Transformation_Functor F14 (F3 a) Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c * a = b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds
\<Longrightarrow> Prem
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> F4 c W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3 c U \<w>\<i>\<t>\<h> P x @action \<A>SE False)
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F4 b W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f (z x) \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> pred_mapper P (z x) @action \<A>SE False\<close>
  \<medium_left_bracket> premises LSF3[\<phi>reason add] and LSF4[\<phi>reason add] and _ and FTF
             and _ and _ and [\<phi>reason add] and _ and Tr
    interpret Functional_Transformation_Functor F14 \<open>F3 a\<close> Dom Rng mapper Prem pred_mapper func_mapper
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (metis LSF4 Semimodule_Scalar_Homo_def \<open>a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds\<close> the_\<phi>(6))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (metis LSF3 Semimodule_Scalar_Homo_def \<open>a \<in> Ds \<and> b \<in> Ds \<and> c \<in> Ds\<close> the_\<phi>(6)) ;;
    unfold F4D
    apply_rule apply_Separation_Functor_zip[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U\<close> and f=f and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    fold F3D
  \<medium_right_bracket> .

declare SE_general_Scala_Seminearing_left_b[(*THEN SE_clean_waste,*) \<phi>reason_template add 60]



subsection \<open>Properties for Specific Elements\<close>

subsubsection \<open>Reasoning Hierarchy\<close>

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

subsubsection \<open>Identity\<close>

lemmas [\<phi>reason 1000] =
    closed_homo_sep_disj_id
    homo_sep_disj_id
    homo_sep_mult_id
    homo_one_id
    homo_sep_id
    closed_homo_sep


subsubsection \<open>Functional Pointwise\<close>

lemma closed_homo_sep_disj_fun_upd [\<phi>reason 1100]:
  \<open>closed_homo_sep_disj (fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k)\<close>
  unfolding closed_homo_sep_disj_def
  by (simp add: sep_disj_fun_def)

lemma closed_homo_sep_disj_fun_upd' [\<phi>reason 1000]:
  \<open> closed_homo_sep_disj f
\<Longrightarrow> closed_homo_sep_disj (\<lambda>x. fun_upd (1::'k \<Rightarrow> 'a::sep_magma_1) k (f x))\<close>
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


subsubsection \<open>Push map\<close>

declare closed_homo_sep_disj_push_map [\<phi>reason 1100]
        homo_sep_mult_push_map [\<phi>reason 1100]
        homo_one_push_map [\<phi>reason 1100]

subsubsection \<open>Share Division\<close>

lemma homo_one_share[\<phi>reason 1000]:
  \<open>homo_one ((\<odivr>) n :: 'a::share_one \<Rightarrow> 'a)\<close>
  unfolding homo_one_def
  by simp

lemma homo_sep_mult_share[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep_mult ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_mult_def Premise_def
  by (simp add: share_sep_right_distrib_0)

lemma homo_sep_disj_share[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep_disj ((\<odivr>) n :: 'a::share_sep_disj \<Rightarrow> 'a)\<close>
  unfolding homo_sep_disj_def Premise_def
  by simp

lemma closed_homo_sep_disj_share[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> closed_homo_sep_disj ((\<odivr>) n :: 'a::share_sep_disj \<Rightarrow> 'a)\<close>
  unfolding closed_homo_sep_disj_def Premise_def
  by simp

lemma homo_sep_share[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> homo_sep ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding homo_sep_def Premise_def
  by (simp add: homo_sep_mult_share homo_sep_disj_share)

lemma closed_homo_sep_share[\<phi>reason 1000]:
  \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> 0 < n \<Longrightarrow> closed_homo_sep ((\<odivr>) n :: 'a::share_nun_semimodule \<Rightarrow> 'a)\<close>
  unfolding closed_homo_sep_def Premise_def
  by (simp add: homo_sep_share closed_homo_sep_disj_share)


subsection \<open>Property Derivers\<close>

subsubsection \<open>Extension of BNF-FP\<close>

ML_file \<open>library/phi_type_algebra/tools/BNF_fp_sugar_more.ML\<close>
ML_file \<open>library/phi_type_algebra/tools/extended_BNF_info.ML\<close>


subsubsection \<open>Deriver Framework\<close>

consts \<phi>TA_ind_target :: \<open>action \<Rightarrow> action\<close>
       \<phi>TA_conditioned_ToA_template :: action
       \<phi>TA_ANT :: action \<comment> \<open>Antecedent in the outcome\<close>
       \<phi>TA_pure_facts :: action \<comment> \<open>to derive something maybe\<close>

lemma mk_ToA_rule:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> Q
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> Q \<and> P\<close>
  using transformation_trans by blast

lemma mk_ToA_rule':
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> A \<brangle> \<w>\<i>\<t>\<h> Q
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> B \<brangle> \<w>\<i>\<t>\<h> Q \<and> P\<close>
  unfolding FOCUS_TAG_def
  using implies_left_prod mk_ToA_rule by blast

lemma [fundef_cong]:
  \<open>T x = T' x' \<Longrightarrow> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')\<close>
  unfolding \<phi>Type_def by simp

lemma \<phi>TA_reason_rule__NToA:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action NToA
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action A\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def)

lemma \<phi>TA_reason_rule__\<A>_NToA:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' \<w>\<i>\<t>\<h> Any @action \<A>_map_each_item A
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action NToA
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action A\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def)

lemma \<phi>TA_reason_rule__simp_NToA:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' \<w>\<i>\<t>\<h> Any' @action \<A>_apply_simplication
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action NToA
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action \<A>simp\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def)

lemma \<phi>TA_reason_rule__\<A>_simp_NToA:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X' \<w>\<i>\<t>\<h> Any @action \<A>_map_each_item A
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X'' \<w>\<i>\<t>\<h> Any' @action \<A>_apply_simplication
\<Longrightarrow> X'' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action NToA
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action A\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def)

ML_file \<open>library/phi_type_algebra/deriver_framework.ML\<close>



subsubsection \<open>Warn if the Def contains Sat\<close>

\<phi>property_deriver Warn_if_contains_Sat 10 = \<open>fn quiet => fn [] => fn phi => fn thy => (
  if Phi_Type_Algebra.is_Type_Opr (Term.fastype_of (#term phi)) andalso
     Phi_Type_Algebra.def_contains_satisfaction phi andalso
     not quiet
  then warning ("The \<phi>-type definition contains satisfaction operator (\<Turnstile>).\n\
                \When a \<phi>-type is specified by satisfaction in a boolean assertion, it looses the ability to guide the reasoning.\n\
                \The deriving may fail. It is recommended to use composition operator (\<Zcomp>) to replace the (\<Turnstile>) if possible.")
  else () ;
  thy
)\<close>

subsubsection \<open>Abstract Domain\<close>

lemma \<phi>TA_Inh_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow> Inhabited (x \<Ztypecolon> T) \<longrightarrow> P x @action \<phi>TA_ind_target \<A>EIF)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Abstract_Domain T P\<close>
  unfolding Action_Tag_def Abstract_Domain_def
  by simp

lemma \<phi>TA_SuC_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow> P x \<longrightarrow> Inhabited (x \<Ztypecolon> T) @action \<phi>TA_ind_target \<A>ESC)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Abstract_Domain\<^sub>L T P\<close>
  unfolding Action_Tag_def Abstract_Domain\<^sub>L_def
  by simp

lemma \<phi>TA_Inh_rewr:
  \<open>Trueprop (Ant \<longrightarrow> XX @action \<phi>TA_ind_target A)
 \<equiv> (Ant \<Longrightarrow> XX @action A)\<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_Inh_step:
  \<open> Inh \<longrightarrow> Any @action \<A>EIF
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Any \<longrightarrow> P)
\<Longrightarrow> Inh \<longrightarrow> P @action \<A>EIF\<close>
  unfolding Action_Tag_def Premise_def
  by blast

lemma \<phi>TA_Suc_step:
  \<open> Any \<longrightarrow> Inh @action \<A>ESC
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> Any)
\<Longrightarrow> P \<longrightarrow> Inh @action \<A>ESC\<close>
  unfolding Action_Tag_def Premise_def
  by blast

lemma \<phi>TA_Inh_extract_prem:
  \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<equiv> ((\<exists>v. v \<Turnstile> (x \<Ztypecolon> T)) \<longrightarrow> P) \<and> (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P)\<close>
  unfolding Action_Tag_def Inhabited_def atomize_eq
  by blast

ML_file \<open>library/phi_type_algebra/implication.ML\<close>

(*hide_fact \<phi>TA_Inh_rule \<phi>TA_Inh_rewr \<phi>TA_Inh_step*)


\<phi>property_deriver Abstract_Domain\<^sub>L 89 for ( \<open>Abstract_Domain\<^sub>L _ _\<close> ) = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain_L
\<close>

\<phi>property_deriver Abstract_Domain 90 for ( \<open>Abstract_Domain _ _\<close> ) requires Abstract_Domain\<^sub>L ? = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain
\<close>



subsubsection \<open>Identity Element Intro \& Elim\<close>

lemma \<phi>TA_1L_rule:
  \<open> (Ant @action \<phi>TA_ANT \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P\<close>
  unfolding Action_Tag_def Identity_Element\<^sub>I_def Premise_def
  using transformation_weaken by blast

(*lemma \<phi>TA_1L_rule':
  \<open> (Ant \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P\<close>
  unfolding Action_Tag_def Identity_Element\<^sub>I_def Premise_def
  using transformation_weaken by blast*)

lemma \<phi>TA_1R_rule:
  \<open> (Ant @action \<phi>TA_ANT \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T)\<close>
  unfolding Action_Tag_def .

lemma \<phi>TA_Ident_I_rule_step:
  \<open> Identity_Element\<^sub>I X Q
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Q \<longrightarrow> P)
\<Longrightarrow> Identity_Element\<^sub>I X P \<close>
  unfolding Identity_Element\<^sub>I_def Premise_def
  by (simp add: transformation_weaken)

lemma \<phi>TA_Ident_I_rule_step_infer:
  \<open> Identity_Element\<^sub>I X Q
\<Longrightarrow> Identity_Element\<^sub>I X (Any \<or> Q) \<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def
  by simp

ML_file \<open>library/phi_type_algebra/identity_element.ML\<close>

hide_fact \<phi>TA_1L_rule \<phi>TA_1R_rule

\<phi>property_deriver Identity_Element\<^sub>I 101 for (\<open>Identity_Element\<^sub>I _ _\<close>)
    requires Warn_if_contains_Sat
  = \<open>Phi_Type_Algebra_Derivers.identity_element_I\<close>

\<phi>property_deriver Identity_Element\<^sub>E 102 for (\<open>Identity_Element\<^sub>E _\<close>)
    requires Warn_if_contains_Sat
  = \<open>Phi_Type_Algebra_Derivers.identity_element_E\<close>

\<phi>property_deriver Identity_Element 103 requires Identity_Element\<^sub>I and Identity_Element\<^sub>E


subsubsection \<open>Object Equivalence\<close>

lemma Object_Equiv_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
            (\<forall>y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T)) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Object_Equiv T eq \<close>
  unfolding Object_Equiv_def Premise_def Action_Tag_def
  by blast

lemma \<phi>TA_OE_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>y. P y \<longrightarrow> Q y) @action \<phi>TA_ind_target undefined)
\<equiv> (\<And>y. Ant \<Longrightarrow> P y @action \<phi>TA_pure_facts \<Longrightarrow> Q y @action \<phi>TA_conditioned_ToA_template)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)

lemma \<phi>TA_OE_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target undefined) \<equiv> (Ant \<Longrightarrow> P)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)

lemma Object_Equiv_rule_move_all:
  \<open>(\<And>x. P x \<and> Q) \<Longrightarrow> (\<forall>x. P x) \<and> Q\<close>
  by blast

lemma Object_Equiv_rule_move_all2:
  \<open>(P \<longrightarrow> (\<forall>x. Q x)) \<and> R \<Longrightarrow> (\<forall>x. P \<longrightarrow> Q x) \<and> R\<close>
  by blast

lemma Object_Equiv_rule_move_set_eq:
  \<open>RR \<Longrightarrow> (R \<and> P \<and> R2 \<longrightarrow> P) \<and> RR\<close>
  by blast

lemma Object_Equiv_rule_move_set_eq_end:
  \<open>(P \<and> R \<longrightarrow> P)\<close>
  by blast


paragraph \<open>Object Equivalence at Singular Point\<close>

consts \<A>base_case :: \<open>(unit,unit) \<phi>\<close>

lemma \<phi>TA_OE\<^sub>O_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
            (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> base \<Ztypecolon> T) @action \<phi>TA_ind_target (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> \<A>base_case)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
            (base \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Object_Equiv T (\<lambda>_ _. True)\<close>
  unfolding Object_Equiv_def Action_Tag_def Transformation_def Premise_def
  by blast

lemma \<phi>TA_OE\<^sub>O_rewr_IH1:
  \<open> Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> \<A>base_case)))
 \<equiv> (Ant \<Longrightarrow> P @action to \<A>base_case)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)


lemma \<phi>TA_OE\<^sub>O_rewr_IH2:
  \<open>Trueprop (Ant \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) @action \<phi>TA_ind_target \<A>)
\<equiv> (\<And>A R. Ant \<Longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) &&& (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> R))\<close>
  unfolding Action_Tag_def atomize_imp atomize_all atomize_conj Transformation_def FOCUS_TAG_def
  by (rule; simp; blast)

lemma \<phi>TA_OE\<^sub>O_rewr:
  \<open>Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target \<A>) \<equiv> (Ant \<Longrightarrow> P @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)


ML_file \<open>library/phi_type_algebra/object_equiv.ML\<close>
(*
hide_fact Object_Equiv_rule \<phi>TA_OE_rewr_IH \<phi>TA_OE_rewr_C Object_Equiv_rule_move_all
          Object_Equiv_rule_move_all2 Object_Equiv_rule_move_set_eq
          Object_Equiv_rule_move_set_eq_end *)

\<phi>property_deriver Object_Equiv\<^sub>O 104
  = \<open>Phi_Type_Algebra_Derivers.object_equiv_singular\<close>

\<phi>property_deriver Object_Equiv 105 for (\<open>Object_Equiv _ _\<close>) requires Object_Equiv\<^sub>O?
  = \<open>Phi_Type_Algebra_Derivers.object_equiv\<close>

\<phi>property_deriver Basic 109 requires Object_Equiv and Abstract_Domain



subsubsection \<open>Transformation Functor\<close>

lemma \<phi>TA_TF_rule:
  \<open>(\<And>T U g x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x) \<Longrightarrow>
              (Ant @action \<phi>TA_ANT) \<longrightarrow>
              (\<forall>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<longrightarrow> (a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)) \<longrightarrow> \<comment> \<open>split D\<close>
              (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) @action \<phi>TA_ind_target (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Transformation_Functor F1 F2 D R mapper\<close>
  unfolding Transformation_Functor_def Action_Tag_def Ball_def Premise_def
  by simp

lemma \<phi>TA_TF_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x. P x \<longrightarrow> A2 x) \<longrightarrow> C @action \<phi>TA_ind_target (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U)))
\<equiv> (Ant \<Longrightarrow> (\<And>x. P x \<Longrightarrow> A2 x @action to U) \<Longrightarrow> C @action to U)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

lemma \<phi>TA_TF_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x. P x \<longrightarrow> A2 x) \<longrightarrow> C @action \<phi>TA_ind_target (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U)))
\<equiv> (Ant \<Longrightarrow> (\<And>x. P x \<Longrightarrow> A2 x @action to U) \<Longrightarrow> C @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U))\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

lemma \<phi>TA_TF_pattern_IH:
  \<open> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action A
\<Longrightarrow> PROP Pure.term (\<And>a \<in> S. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Any a \<w>\<i>\<t>\<h> Any' a @action A)\<close> .


subsubsection \<open>Functional Transformation Functor\<close>

lemma \<phi>TA_FTF_rule:
  \<open> (Ant @action \<phi>TA_ANT \<Longrightarrow> Prem \<Longrightarrow> Transformation_Functor F1 F2 D R mapper)
\<Longrightarrow> (Ant @action \<phi>TA_ANT \<Longrightarrow> Prem \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>f P a' b'. mapper (\<lambda>a b. b = f a \<and> P a) a' b' \<longleftrightarrow> b' = fm f a' \<and> pm P a'))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Functional_Transformation_Functor F1 F2 D R mapper Prem pm fm\<close>
  unfolding Functional_Transformation_Functor_def Premise_def fun_eq_iff
            Functional_Transformation_Functor_axioms_def Transformation_Functor_L_def
            Action_Tag_def
  by blast

ML_file \<open>library/phi_type_algebra/transformation_functor.ML\<close>

\<phi>property_deriver Transformation_Functor 110 for (\<open>Transformation_Functor _ _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.transformation_functor
\<close>

\<phi>property_deriver Functional_Transformation_Functor 111
  for (\<open>Functional_Transformation_Functor _ _ _ _ _ _ _ _\<close>)
  requires Transformation_Functor
    = \<open>Phi_Type_Algebra_Derivers.functional_transformation_functor\<close>

(* TODO:
hide_fact \<phi>TA_TF_rule \<phi>TA_TF_rewr_IH \<phi>TA_TF_rewr_C \<phi>TA_TF_pattern_IH \<phi>TA_FTF_rule
*)


subsubsection \<open>Congruence in Function Definition\<close>

lemma function_congruence_template:
  \<open> Transformation_Functor F F D R M
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x \<subseteq> R x \<and> M (=) = (=)
\<Longrightarrow> \<r>Success
\<Longrightarrow> x = y
\<Longrightarrow> (\<And>a \<in> D x. T a = U a)
\<Longrightarrow> F T x = F U y\<close>
  unfolding Transformation_Functor_def Premise_def Transformation_def \<phi>Type_def BI_eq_iff
            subset_iff meta_Ball_def Ball_def
  apply clarify
  subgoal premises prems for u
    by (insert prems(1)[THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=y], THEN spec[where x=\<open>(=)\<close>]]
               prems(1)[THEN spec[where x=U], THEN spec[where x=T], THEN spec[where x=y], THEN spec[where x=\<open>(=)\<close>]]
               prems(3-6) ;
        auto) .
  
ML_file \<open>library/phi_type_algebra/function_congruence.ML\<close>


subsubsection \<open>Scalar Semimodule Homo\<close>

text \<open>\<phi>-type embedding of separation quantifier \<open>x \<Ztypecolon> \<big_ast>[i\<in>I] T\<close> is a recursive example of this.

  We apply structural induction over the scalar as the scalar usually gives the domain of the \<phi>-type abstraction.
  As the scalar reduces by means of induction, the entire \<phi>-type assertion should also be able to reduce.
\<close>

(*TODO!!!
thm nat_induct [induct rule = ....]

lemma
  \<open> (\<And>t s x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s \<in> D \<and> t \<in> D
         \<Longrightarrow> (Ant @action \<phi>TA_ANT)
         \<longrightarrow> x \<Ztypecolon> F s (F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F (t * s) T @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>t s x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s \<in> D \<and> t \<in> D
         \<Longrightarrow> (Ant @action \<phi>TA_ANT)
         \<longrightarrow> x \<Ztypecolon> F (t * s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F s (F t T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Semimodule_Scalar_Homo F T D \<close>
*)

subsubsection \<open>Separation Homo\<close>

lemma \<phi>TA_SH\<^sub>I_rule:
  \<open> (\<And>T U z. (Ant @action \<phi>TA_ANT) \<longrightarrow>
              (\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z
                  \<longrightarrow> ((y \<Ztypecolon> Fb U) * (x \<Ztypecolon> Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Fc (T \<^emph> U))) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Separation_Homo\<^sub>I Fa Fb Fc (\<lambda>_ _ _. True) D w \<close>
  unfolding Separation_Homo\<^sub>I_def \<phi>Prod_expn' Action_Tag_def
  by simp

lemma \<phi>TA_SH\<^sub>E_rule:
  \<open> (\<And>T U z. (Ant @action \<phi>TA_ANT) \<longrightarrow>
             (z \<Ztypecolon> Fc (T \<^emph>\<^sub>\<A> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz z \<Ztypecolon> Ft T \<^emph>\<^sub>\<A> Fu U) @action \<phi>TA_ind_target \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc uz \<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn' Action_Tag_def \<phi>Auto_Prod_def
  by simp

lemma \<phi>TA_SH\<^sub>I_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x y. P x y \<longrightarrow> Q x y) @action \<phi>TA_ind_target undefined)
\<equiv> (\<And>x y. Ant \<Longrightarrow> P x y @action \<phi>TA_pure_facts \<Longrightarrow> Q x y @action \<phi>TA_conditioned_ToA_template)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

text \<open>This conditioned template is necessary because, see,
  \<^prop>\<open>(\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z \<longrightarrow> ((y \<Ztypecolon> Fb U) * (x \<Ztypecolon> Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Fc (T \<^emph> U)))\<close>
  \<^term>\<open>z\<close> does not decide \<open>x\<close> and \<open>y\<close> during the reasoning phase and until the phase of proof obligation solving.
  When there are multiple choices of such induction hypotheses, for sure, we can attempt every choice
  exhaustively, but it multiplies the search branches and can harm the performance dramatically.
\<close>

lemma \<phi>TA_SH\<^sub>I_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target A)
\<equiv> (Ant \<Longrightarrow> P)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

lemma \<phi>TA_SH\<^sub>E_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (z \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz \<Ztypecolon> U) @action \<phi>TA_ind_target A)
\<equiv> (Ant \<Longrightarrow> z \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z' \<Ztypecolon> U \<s>\<u>\<b>\<j> z'. z' = uz @action A)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by simp

lemma \<phi>TA_SH\<^sub>E_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target A)
\<equiv> (Ant \<Longrightarrow> P @action A)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

ML_file \<open>library/phi_type_algebra/separation_homo.ML\<close>

hide_fact \<phi>TA_SH\<^sub>I_rule \<phi>TA_SH\<^sub>E_rule \<phi>TA_SH\<^sub>I_rewr_IH \<phi>TA_SH\<^sub>I_rewr_C
          \<phi>TA_SH\<^sub>E_rewr_IH \<phi>TA_SH\<^sub>E_rewr_C

\<phi>property_deriver Separation_Homo\<^sub>I 120 for (\<open>Separation_Homo\<^sub>I _ _ _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.separation_homo_I
\<close>

\<phi>property_deriver Separation_Homo\<^sub>E 121 for (\<open>Separation_Homo\<^sub>E _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.separation_homo_E
\<close>

\<phi>property_deriver Separation_Homo 122 requires Separation_Homo\<^sub>I and Separation_Homo\<^sub>E



subsubsection \<open>Exhaustively Open All Abstraction\<close>

lemma \<phi>TA_TrRA_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
         (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_ind_target (to (Itself::('b,'b) \<phi>)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> \<forall>x. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y::'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to (Itself::('b,'b) \<phi>)) \<close>
  unfolding Action_Tag_def
  by simp

lemma \<phi>TA_TrRA_rewr:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_ind_target A) \<equiv> (Ant \<Longrightarrow> X @action A) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma "_all_simps_plus_":
  "NO_MATCH (All X) Q \<Longrightarrow> ((\<forall>x. P x) \<and> Q) = (\<forall>x. P x \<and> Q)"
  "NO_MATCH (All Z) P' \<Longrightarrow> (P' \<and> (\<forall>x. Q' x)) = (\<forall>x. P' \<and> Q' x)"
  by blast+

ML_file \<open>library/phi_type_algebra/open_all_abstraction.ML\<close>

\<phi>property_deriver Open_Abstraction_Full 130 for ( \<open>\<forall>x. (x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself)\<close>
                                                | \<open>\<forall>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself\<close>
                                                | \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r' y @action to Itself\<close>)
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Algebra_Derivers.open_all_abstraction \<close>



subsubsection \<open>Is_Functional\<close>

lemma \<phi>TA_IsFunc_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
          \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P x \<longrightarrow>
          Is_Functional (x \<Ztypecolon> T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Functionality T P \<close>
  unfolding Action_Tag_def Functionality_def Is_Functional_def Premise_def
  by clarsimp

lemma \<phi>TA_IsFunc_rewr:
  \<open> Trueprop (Ant \<longrightarrow> cond \<longrightarrow> Is_Functional S @action Any)
 \<equiv> (Ant \<Longrightarrow> cond \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x y. x \<Turnstile> S \<and> y \<Turnstile> S \<longrightarrow> x = y)) \<close>
  unfolding Action_Tag_def Is_Functional_def Premise_def atomize_imp .

lemma \<phi>TA_IsFunc_rewr_ants:
  \<open>Is_Functional S \<equiv> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>u v. u \<Turnstile> S \<and> v \<Turnstile> S \<longrightarrow> u = v)\<close>
  unfolding Premise_def Is_Functional_def by simp
                                        
ML_file \<open>library/phi_type_algebra/is_functional.ML\<close>

\<phi>property_deriver Is_Functional 100 for (\<open>Is_Functional (_ \<Ztypecolon> _)\<close>)
    = \<open> Phi_Type_Algebra_Derivers.is_functional \<close>



subsubsection \<open>Trim Empty Generated during Separation Extraction\<close>

text \<open>For a type operator \<open>F\<close>, SE_Trim_Empty generates rules that eliminates into \<open>\<circle>\<close>
  any \<open>F \<circle>\<close> generated during Separation Extraction process.

  This elimination is derived from \<open>Identity_Element\<close>. If the elimination rule is condition-less
  (demand no conditional premise nor reasoner subgoals), the rule is activated automatically.
  But if there are conditions, the system needs user's discretion to decide if to activate it.
  If so, activate deriver \<open>SE_Trim_Empty\<close>.
\<close>

lemma derive_\<A>SE_trim_I:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>I (yy \<Ztypecolon> F \<circle>) P
\<Longrightarrow> Object_Equiv (F \<circle>) eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd y) yy
\<Longrightarrow> \<A>SE_trim\<^sub>I y (F \<circle>) (fst y, ()) \<circle> P \<close>
  unfolding \<A>SE_trim\<^sub>I_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>I_def]
    apply_rule R1[THEN implies_right_prod]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_I_TH:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>I (yy \<Ztypecolon> F \<circle>) P
\<Longrightarrow> Object_Equiv (F \<circle>) eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd y) yy
\<Longrightarrow> \<A>SE_trim\<^sub>I_TH y (F \<circle>) (fst y, ()) \<circle> P \<circle> (F' \<circle>) \<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  \<medium_left_bracket> premises _ and  R1[unfolded Identity_Element\<^sub>I_def]
    apply_rule R1[THEN implies_right_prod]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_E:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>E (u \<Ztypecolon> F \<circle>)
\<Longrightarrow> \<A>SE_trim\<^sub>E (fst x', u) (F \<circle>) x' \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>E_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>E_def]
    apply_rule R1[THEN implies_right_prod]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_E_TH:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>E (u \<Ztypecolon> F \<circle>)
\<Longrightarrow> \<A>SE_trim\<^sub>E_TH (fst x', u) (F \<circle>) x' \<circle> \<circle> (F' \<circle>) \<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>E_def]
    apply_rule R1[THEN implies_right_prod]
  \<medium_right_bracket> .


ML_file \<open>library/phi_type_algebra/SE_Trim_Empty.ML\<close>

\<phi>property_deriver SE_Trim_Empty 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.SE_Trim_Empty quiet) \<close>

lemmas [\<phi>reason_template default 40 pass: \<open>Phi_Type_Algebra_Derivers.SE_Trim_Empty__generation_pass\<close>] =
          derive_\<A>SE_trim_I derive_\<A>SE_trim_I_TH
          derive_\<A>SE_trim_E derive_\<A>SE_trim_E_TH




subsection \<open>Configure Simplification Set for Deriving\<close>

subsubsection \<open>Common\<close>

setup \<open>Context.theory_map (Phi_Type_Algebra_Derivers.Simps.map (fn ctxt => ctxt addsimps
  @{thms' HOL.simp_thms ex_simps[symmetric] mem_Collect_eq imp_ex
          prod.case prod.sel fst_apfst snd_apfst fst_apsnd snd_apsnd apfst_id apsnd_id apfst_conv apsnd_conv prod.inject
          ExSet_simps
          \<phi>Prod_expn' \<phi>Prod_expn'' \<phi>Prod_expn'[folded \<phi>Auto_Prod_def] \<phi>Prod_expn''[folded \<phi>Auto_Prod_def]
          FSet.ball_simps(5-7) Set.ball_simps(5-7,9)
          list_all2_Cons1 list_all2_Nil
          map_ident}))\<close>


lemmas [\<phi>constraint_expansion global] =
  Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral Nat.nat.inject

lemmas [\<phi>constraint_expansion] =
  Basic_BNFs.prod_set_defs


subsubsection \<open>List\<close>

definition \<open>zip' = case_prod zip\<close>
definition \<open>unzip' l = (map fst l, map snd l)\<close>

lemma zip'_inj[simp]:
  \<open>length (fst l) = length (snd l) \<Longrightarrow> map fst (zip' l) = fst l\<close>
  \<open>length (fst l) = length (snd l) \<Longrightarrow> map snd (zip' l) = snd l\<close>
  unfolding zip'_def
  by (cases l; simp)+

lemma zip'_eq_Cons_ex:
  \<open>zip' x = (h#l) \<longleftrightarrow> (\<exists>ah al bh bl. fst x = ah # al \<and> snd x = bh # bl \<and> (ah,bh) = h \<and> zip' (al,bl) = l)\<close>
  unfolding zip'_def
  by (cases x; simp; induct_tac b; case_tac a; simp)

lemma zip'_eq_Nil_eq_len:
  \<open>length (fst l) = length (snd l) \<Longrightarrow> (zip' l = []) \<longleftrightarrow> l = ([], [])\<close>
  unfolding zip'_def
  apply (cases l; simp)
  subgoal for a b
    by (induct b; cases a; simp) .

lemma zip'_eq_Nil_with_rel:
  \<open>list_all2 P a b \<and> zip' (a,b) = [] \<longleftrightarrow> a = [] \<and> b = []\<close>
  unfolding zip'_def
  by (induct b; cases a; simp)

lemma length_zip':
  \<open>length a = length b \<Longrightarrow> length (zip' (a,b)) = length b\<close>
  unfolding zip'_def
  by simp

lemma zip'_map:
  \<open>zip' (map f xs, ys) = map (\<lambda>(x,y). (f x, y)) (zip' (xs, ys))\<close>
  \<open>zip' (xs, map g ys) = map (\<lambda>(x,y). (x, g y)) (zip' (xs, ys))\<close>
  unfolding zip'_def
  by (simp add: zip_map1 zip_map2)+

lemma unzip'_inj[simp]:
  \<open>unzip' [] = ([], [])\<close>
  unfolding unzip'_def
  by simp_all

lemma unzip'_prj[simp]:
  \<open>fst (unzip' L) = map fst L\<close>
  \<open>snd (unzip' L) = map snd L\<close>
  unfolding unzip'_def
  by simp_all

lemma map_prod_case_analysis:
  \<open>map (\<lambda>x. (f x, g x)) la = lb \<equiv> map f la = map fst lb \<and> map g la = map snd lb \<close>
  by (induct la arbitrary: lb; clarsimp; fastforce)

lemma list_all2__const_True[simp]:
  \<open>list_all2 (\<lambda>x y. True) = (\<lambda>x y. length x = length y)\<close>
  apply (clarsimp simp add: fun_eq_iff)
  subgoal for x y
  by (induct x arbitrary: y; simp; case_tac y; simp) .

setup \<open> Context.theory_map(
  BNF_FP_Sugar_More.add_fp_more (\<^type_name>\<open>list\<close>, {
      deads = [],
      lives = [\<^typ>\<open>'a\<close>],
      lives'= [\<^typ>\<open>'b\<close>],
      zip = \<^term>\<open>zip'\<close>,
      unzip = \<^Const>\<open>unzip' \<^typ>\<open>'a\<close> \<^typ>\<open>'b\<close>\<close>,
      zip_simps = @{thms' zip'_inj zip'_eq_Cons_ex zip'_eq_Cons_ex zip'_eq_Nil_eq_len
                          length_map length_zip' zip'_map
                          unzip'_inj unzip'_prj map_prod_case_analysis}
  }))
\<close>

lemma list_all2_reduct_rel[simp]: (*TODO!*)
  \<open>list_all2 (\<lambda>a b. b = f a \<and> P a) = (\<lambda>a' b'. b' = map f a' \<and> list_all P a')\<close>
  apply (clarsimp simp add: fun_eq_iff)
  subgoal for x y by (induct x arbitrary: y; simp; case_tac y; simp; blast) .

lemmas [\<phi>constraint_expansion] =
  list.size map_eq_Cons_conv list_all2_lengthD[THEN HOL.Eq_TrueI]


subsubsection \<open>Sum\<close>

lemma pred_sum_eq_case_sum[\<phi>constraint_expansion]:
  \<open>pred_sum P Q x \<longleftrightarrow> case_sum P Q x\<close>
  by (cases x; simp)



subsubsection \<open>Set\<close>


setup \<open> Context.theory_map (eBNF_Info.add_BNF (\<^type_name>\<open>Set.set\<close>, 
let val a = TFree ("a", \<^sort>\<open>type\<close>)
    val b = TFree ("b", \<^sort>\<open>type\<close>)
 in {
  T = \<^Type>\<open>Set.set a\<close>,
  Tname = \<^type_name>\<open>Set.set\<close>,
  casex = NONE,
  case_distribs = [],
  ctrs = [\<^Const>\<open>bot \<^Type>\<open>set a\<close>\<close>, \<^Const>\<open>insert a\<close>, \<^Const>\<open>sup \<^Type>\<open>set a\<close>\<close>],
  deads = [], lives = [a], lives'= [b],
  sets = [Abs("x", a, Bound 0)],
  set_thms = [],
  ctr_simps = [],
  rel = \<^Const>\<open>rel_set a b\<close>,
  rel_distincts = [],
  rel_injects = @{thms' Lifting_Set.empty_transfer},
  rel_eq = @{thm' rel_set_eq},
  pred = Abs("P", a --> HOLogic.boolT, Abs ("S", \<^Type>\<open>Set.set a\<close>, \<^Const>\<open>Ball a\<close> $ Bound 0 $ Bound 1)),
  pred_injects = @{thms' Set.ball_simps(5) Set.ball_Un Set.ball_simps(7)},
  pred_simps = @{thms' Set.ball_simps},
  map = \<^Const>\<open>Set.image a b\<close>,
  map_thms = @{thms' Set.image_insert Set.image_Un Set.image_empty},
  map_disc_iffs = @{thms' image_is_empty},
  map_ident = @{thm' Set.image_ident},
  map_comp_of = @{thm' Set.image_image},
  fp_more = NONE (*{ TODO!
    deads = [],
    lives = [a],
    lives'= [b],
    
  }*)
} end)
)\<close>

lemmas [\<phi>constraint_expansion for set] =
  Set.ball_Un Fun.bind_image Set.empty_bind Set.bind_singleton_conv_image
  Set.nonempty_bind_const Finite_Set.finite_bind

lemma Set_bind_insert[simp, \<phi>constraint_expansion for set]:
  \<open>Set.bind (insert x S) f = f x \<union> Set.bind S f\<close>
  unfolding Set.bind_def
  by auto


subsubsection \<open>Production\<close>

lemma [\<phi>constraint_expansion, simp]:
  \<open>pred_prod (\<lambda>a. True) P x \<longleftrightarrow> P (snd x)\<close>
  \<open>pred_prod Q (\<lambda>a. True) x \<longleftrightarrow> Q (fst x)\<close>
  by (cases x; simp)+

end
                                                          