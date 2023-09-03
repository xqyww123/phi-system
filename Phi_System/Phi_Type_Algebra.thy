theory Phi_Type_Algebra
  imports IDE_CP_Reasoning2
          Phi_Algb_Pre
          Phi_Algebras.LCRO_Interval (*temporarily we add this for testing but will be moved later*)
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
comparing with the rich algebraic properties that \<phi>-type owns, which instantiate the automation,
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
  As \<open>R\<close> is parameterized by the abstract container \<open>x\<close>, by assigning \<open>R\<close> to empty set on certain
  invalid abstract containers, it also constraints the domain of abstract containers on which
  the transformation functor is available.

  For general data structures which do not assumes such, tt is usually \<open>\<lambda>_. \<top>\<close>.
  Our automatic deriver by default assumes it to \<open>\<lambda>_. \<top>\<close> if no user hint is given.
\<close>



subsubsection \<open>Separation\<close>

definition Object_Sep_Homo\<^sub>I :: \<open>('b::sep_magma, 'a::sep_magma) \<phi> \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool\<close>
  where \<open>Object_Sep_Homo\<^sub>I T D \<longleftrightarrow> (\<forall>x y. (y,x) \<in> D \<longrightarrow> ((x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> T \<w>\<i>\<t>\<h> x ## y ))\<close>

definition \<open>Object_Sep_Homo\<^sub>E T \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> ( (x * y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) ))\<close>

definition \<open>Separation_Homo\<^sub>I Ft Fu F3 T U D z \<longleftrightarrow>
              (\<forall>x y. (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (T \<^emph> U)))\<close>

definition \<open>Separation_Homo\<^sub>E Ft Fu F3 T U un \<longleftrightarrow> \<comment> \<open>Does it need a domain constraint?\<close>
              (\<forall>z. z \<Ztypecolon> F3 (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph> Fu U)\<close>

subsubsection \<open>Semimodule\<close>

definition Semimodule_Zero :: \<open>('s::zero \<Rightarrow> ('c::one,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> bool\<close>
  where \<open>Semimodule_Zero F T \<longleftrightarrow> (\<forall>x. (x \<Ztypecolon> F 0 T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1)\<close>

definition Closed_Semimodule_Zero :: \<open>('s::zero \<Rightarrow> ('c::one,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> bool\<close>
  where \<open>Closed_Semimodule_Zero F T \<longleftrightarrow> (\<forall>x. (x \<Ztypecolon> F 0 T) = 1)\<close>
  \<comment> \<open>It is actually a very strong property particularly when \<open>T\<close> is an empty \<phi>-type of empty
      abstract domain. It excludes functional homomorphism like \<open>F c T \<equiv> \<psi> c \<Zcomp>\<^sub>f T\<close>.\<close>

definition Semimodule_Identity :: \<open>('s::one \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> bool\<close>
  where \<open>Semimodule_Identity F T \<longleftrightarrow> F 1 T = T\<close>

definition Semimodule_Scalar_Assoc :: \<open> ('s \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                     \<Rightarrow> ('c,'a) \<phi>
                                     \<Rightarrow> ('s::semigroup_mult \<Rightarrow> bool)
                                     \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Assoc F T Ds \<longleftrightarrow> (\<forall>s t. Ds s \<and> Ds t \<longrightarrow> F s (F t T) = F (t * s) T)\<close>
  \<comment> \<open>Associativity of scalar multiplication\<close>

definition Semimodule_LDistr_Homo\<^sub>Z :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                    \<Rightarrow> ('c::sep_magma,'a) \<phi>
                                    \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                    \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x \<longrightarrow>
                  (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> F (s + t) T ))\<close>
  \<comment> \<open>The left distributive law (i.e., the distributivity of scalar addition) of a left-module.
      Note the right distributive law (i.e., the distributivity of vector addition) is just the separation homomorphism.
      So, when both of \<open>Semimodule_Scalar_Assoc\<close>, \<open>Separation_Homo\<close>, \<open>Semimodule_LDistr_Homo\<^sub>Z\<close>, and
      homomorphism of identity element, are satisfied, it is then a semimodule.
\<close>

definition Semimodule_LDistr_Homo\<^sub>Z_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                        \<Rightarrow> ('c::sep_magma,'a) \<phi>
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>Z_rev F T Ds Dx z \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> t ##\<^sub>+ s \<and> Dx t s x \<longrightarrow>
                  (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T ))\<close>


definition Semimodule_LDistr_Homo\<^sub>O\<^sub>Z :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi>) \<Rightarrow> 's::partial_add_magma set \<Rightarrow> (('a \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>O\<^sub>Z T Ds Dx z \<longleftrightarrow> (\<forall>s \<in> Ds. \<forall> t \<in> Ds. \<forall>x. s ##\<^sub>+ t \<and> Dx x \<longrightarrow> (x \<Ztypecolon> T t \<^emph> T s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> T (s + t) ))\<close>
  \<comment> \<open>the subscript O stands for \<^emph>\<open>non-type-Operator\<close>\<close>


definition Semimodule_LDistr_Homo\<^sub>U :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                        \<Rightarrow> ('c::sep_magma,'a) \<phi>
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>U F T Ds Dx uz \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x \<longrightarrow>
                (x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F t T \<^emph> F s T ))\<close>

definition Semimodule_LDistr_Homo\<^sub>U_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                        \<Rightarrow> ('c::sep_magma,'a) \<phi>
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_LDistr_Homo\<^sub>U_rev F T Ds Dx uz \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x \<longrightarrow>
                (x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F s T \<^emph> F t T ))\<close>


subsubsection \<open>Configurations\<close>

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
  \<phi>reason_default_pattern \<open>Object_Sep_Homo\<^sub>I ?T _\<close> \<Rightarrow> \<open>Object_Sep_Homo\<^sub>I ?T _\<close> (100),

  \<phi>reason_default_pattern_ML \<open>Separation_Homo\<^sub>I ?Ft ?Fu _ _ _ _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Homo\<^sub>I*) $ F1 $ F2 $ F3 $ _ $ _ $ _ $ _) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Separation_Homo\<^sub>I\<close>, TVar(("'SF",ind),[]))
       in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "T" "'T" $ var "U" "'U" $ var "D" "'d" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "T" "'T" $ var "U" "'U" $ var "D" "'d" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "T" "'T" $ var "U" "'U" $ var "D" "'d" $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>reason_default_pattern_ML \<open>Separation_Homo\<^sub>E ?Ft ?Fu _ _ _ _\<close> \<Rightarrow>
    \<open>fn generic => fn term =>
      let val ctxt = Context.proof_of generic
          val [term'] = Variable.exportT_terms ctxt Phi_Help.empty_ctxt [term]
          val Trueprop $ (_ (*Separation_Functor*) $ F1 $ F2 $ F3 $ _ $ _ $ f) = term'
          val ind = Int.max (maxidx_of_term F1, Int.max (maxidx_of_term F2, maxidx_of_term F3)) + 1
          fun var name1 name2 = Var((name1,ind), TVar((name2,ind), []))
          val H = Const(\<^const_name>\<open>Separation_Homo\<^sub>E\<close>, TVar(("'SF",ind),[]))
       in SOME [Trueprop $ (H $ F1 $ var "F2" "'F2" $ var "F3" "'F3" $ var "T" "'T" $ var "U" "'U" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ F2 $ var "F3" "'F3" $ var "T" "'T" $ var "U" "'U" $ var "z" "'z"),
                Trueprop $ (H $ var "F1" "'F1" $ var "F2" "'F2" $ F3 $ var "T" "'T" $ var "U" "'U" $ var "z" "'z")]
      end
    \<close> (100),

  \<phi>premise_attribute? [\<phi>reason add] for \<open>Transformation_Functor _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Object_Sep_Homo\<^sub>I _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Object_Sep_Homo\<^sub>E _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>I _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>E _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Zero _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Closed_Semimodule_Zero _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Identity _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Scalar_Assoc _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_LDistr_Homo\<^sub>Z _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_LDistr_Homo\<^sub>Z_rev _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_LDistr_Homo\<^sub>U _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_LDistr_Homo\<^sub>U_rev _ _ _ _ _\<close>,

  \<phi>reason_default_pattern
      \<open>Semimodule_LDistr_Homo\<^sub>Z ?F ?T _ _ _\<close> \<Rightarrow> \<open>Semimodule_LDistr_Homo\<^sub>Z ?F ?T _ _ _\<close> (100)
  and \<open>Semimodule_LDistr_Homo\<^sub>U ?F ?T _ _ _\<close> \<Rightarrow> \<open>Semimodule_LDistr_Homo\<^sub>U ?F ?T _ _ _\<close> (100)
  and \<open>Semimodule_LDistr_Homo\<^sub>Z_rev ?F ?T _ _ _\<close> \<Rightarrow> \<open>Semimodule_LDistr_Homo\<^sub>Z_rev ?F ?T _ _ _\<close> (100)
  and \<open>Semimodule_LDistr_Homo\<^sub>U_rev ?F ?T _ _ _\<close> \<Rightarrow> \<open>Semimodule_LDistr_Homo\<^sub>U_rev ?F ?T _ _ _\<close> (100)
]]



subsection \<open>Convention\<close>

text \<open>
Priority:
\<^item> 30: Destruction \<open>to OPEN\<close>
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

subsubsection \<open>General Groups of Properties\<close>

\<phi>reasoner_group \<phi>type_algebra_all_properties = (100, [0,4000]) for \<open>_\<close>
    \<open>The universe group containing every sort of \<phi>-type algebraic properties\<close>
 and \<phi>TA_system_bottom = (1, [0,19]) for \<open>_\<close> in \<phi>type_algebra_all_properties
    \<open>Systematic rules of \<phi>-type algebraic properties, of the lowest priority.\<close>
 and \<phi>TA_fallback_lattice = (14, [10,19]) for \<open>_\<close> in \<phi>TA_system_bottom
    \<open>Rules of \<phi>-type algebraic forming a lattice giving fallbacks from weak properties to strong properties\<close>
 and \<phi>type_algebra_properties = (100, [20, 3800]) for \<open>_\<close> in \<phi>type_algebra_all_properties
                                                          and > \<phi>TA_system_bottom
    \<open>User rules of \<phi>-type algebraic properties\<close>
 and \<phi>TA_varify_out = (3900, [3900,3900]) for \<open>_\<close> in \<phi>type_algebra_all_properties and > \<phi>type_algebra_properties
    \<open>Systematic rules of \<phi>-type algebraic properties that varifies OUT arguments that are not varibales\<close>

subsubsection \<open>Groups for Specific Properties\<close>

\<phi>reasoner_group Object_Sep_Homo_functor = (50, [50,50]) for (\<open>Object_Sep_Homo\<^sub>I T D\<close>, \<open>Object_Sep_Homo\<^sub>E T\<close>)
                                                         in \<phi>type_algebra_properties
    \<open>Object_Sep_Homo for functors\<close>

subsubsection \<open>Derived Rules\<close>

\<phi>reasoner_group deriving_IH = (200, [200,200]) for \<open>_\<close> > default
    \<open>The priority of induction hypotheses used during deriving.\<close>

 and ToA_derived_one_to_one_functor = (70, [70,70]) for \<open>x \<Ztypecolon> F(T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U)\<close> in ToA_derived
    \<open>Derived transformation in form \<open>x \<Ztypecolon> F(T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U)\<close>, of a high priority as this is what
     should be attempted in reasoning.\<close>
 and to_trans_derived_Tr_functor = (60, [60,60]) for \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r x y \<w>\<i>\<t>\<h> P @action to U\<close>
                                                  in to_trans_derived
    \<open>Derived To-Transformation rules for transformation functor\<close>
 and \<phi>simp_derived_Tr_functor = (55, [55,60]) for \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>simp\<close>
                                               in \<phi>simp_derived
    \<open>Derived transformation-based simplification for transformation functor\<close>
 and derived_SE_functor = (70, [70,70]) for \<open>x \<Ztypecolon> F(T) \<^emph>[Cw] F(W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U) \<^emph>[Cr] F(R)\<close> in ToA_derived
    \<open>Derived rules of Separation Extraction, of a high priority as this is what
     should be attempted in reasoning. No confliction with %ToA_derived_one_to_one_functor\<close>

\<phi>reasoner_group_assert identity_element_ToA < deriving_IH

paragraph \<open>Separation Extraction on Semimodule\<close>

\<phi>reasoner_group derived_SE_scalar_assoc = (30, [30,30]) for \<open>x \<Ztypecolon> F (a * b) T \<^emph>[Cw] F (a * b) W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (c*d) U \<^emph>[Cr] F (c*d) R\<close>
                                              in ToA_derived and < derived_SE_functor
    \<open>Derived rules for scalar associativity, of a low priority as  it can conflict to scalar distributive rule,
     see \cref{Semimodule-Scalar-Associative}\<close>
 and derived_SE_scalar_distr = (35, [31, 39]) for \<open>x \<Ztypecolon> F (a + b) T \<^emph>[Cw] F (a + b) W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (c+d) U \<^emph>[Cr] F (c+d) R\<close>
                                               in ToA_derived and > derived_SE_scalar_assoc and < derived_SE_functor
    \<open>Derived rules for scalar distributivity.\<close>
 and derived_SE_sdistr_comm = (39, [39, 39]) for \<open>x \<Ztypecolon> F (a + b) T \<^emph>[Cw] F (a + b) W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (c+d) U \<^emph>[Cr] F (c+d) R\<close>
                                              in derived_SE_scalar_distr
    \<open>Derived rules for scalar distributivity on commutative semigroup\<close>
 and derived_SE_sdistr_noncomm = (36, [36, 36]) for \<open>x \<Ztypecolon> F (a + b) T \<^emph>[Cw] F (a + b) W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (c+d) U \<^emph>[Cr] F (c+d) R\<close>
                                                 in derived_SE_scalar_distr < derived_SE_sdistr_comm
    \<open>Derived rules for scalar distributivity on non-commutative semigroup\<close>
 and derived_SE_sdistr_noassoc = (33, [33, 33]) for \<open>x \<Ztypecolon> F (a + b) T \<^emph>[Cw] F (a + b) W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (c+d) U \<^emph>[Cr] F (c+d) R\<close>
                                                 in derived_SE_scalar_distr < derived_SE_sdistr_noncomm
    \<open>Derived rules for scalar distributivity on separational magma\<close>

subsubsection \<open>Guess Algebraic Operators\<close>

\<phi>reasoner_group guess_algebraic_oprs = (100, [0, 3000]) for \<open>_\<close>
    \<open>A general group consisting of reasoning rules derivign or guessing operators for algbebraic properties\<close>
 and guess_algebraic_oprs_cut = (1000, [1000, 1030]) for \<open>_\<close> in guess_algebraic_oprs
    \<open>Cutting rules derivign or guessing operators for algbebraic properties\<close>


subsection \<open>Direct Applications \& Properties\<close>

text \<open>Directly applying the algebraic properties.\<close>

subsubsection \<open>Transformation Functor\<close>

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

lemma Separation_Homo\<^sub>I_sub_D:
  \<open> D' \<subseteq> D
\<Longrightarrow> Separation_Homo\<^sub>I F\<^sub>a F\<^sub>b F\<^sub>c T U D  z
\<Longrightarrow> Separation_Homo\<^sub>I F\<^sub>a F\<^sub>b F\<^sub>c T U D' z\<close>
  unfolding Separation_Homo\<^sub>I_def
  by blast

lemma apply_Separation_Functor_zip:
  \<open> Separation_Homo\<^sub>I Ft Fu Fc T U D z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z x \<Ztypecolon> Fc(T \<^emph> U)\<close>
  unfolding Separation_Homo\<^sub>I_def Premise_def meta_Ball_def meta_case_prod_def split_paired_all
  by (cases x; simp)

lemma apply_Separation_Functor_unzip:
  \<open> Separation_Homo\<^sub>E Ft Fu Fc T U un
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph> Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'[symmetric]
  by simp


subsubsection \<open>Semimodule\<close>

paragraph \<open>Left Distributivity\<close>

lemma Semimodule_LDistr_Homo\<^sub>Z_sub:
  \<open> Ds \<le> Ds' \<and> Dx \<le> Dx'
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z F T Ds' Dx' z
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z\<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_def le_fun_def le_bool_def
  by blast

lemma [\<phi>reason %\<phi>TA_varify_out except \<open>Semimodule_LDistr_Homo\<^sub>Z _ _ ?var_Ds ?var_Dx _\<close> ]:
  \<open> Semimodule_LDistr_Homo\<^sub>Z F T Ds' Dx' z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds \<le> Ds' \<and> Dx \<le> Dx'
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z\<close>
  unfolding Premise_def
  using Semimodule_LDistr_Homo\<^sub>Z_sub by blast

lemma apply_Semimodule_LDistr_Homo\<^sub>Z:
  \<open> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> F (s + t) T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_def Premise_def
  by blast

lemma apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some:
  \<open> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F t T \<^emph> \<black_circle> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> \<black_circle> F (s + t) T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_def Premise_def Transformation_def
  by (clarsimp; metis prod.collapse)

lemma apply_Semimodule_LDistr_Homo\<^sub>Z_rev:
  \<open> Semimodule_LDistr_Homo\<^sub>Z_rev F T Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F s T \<^emph> F t T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> F (s + t) T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_rev_def Premise_def
  by blast

lemma apply_Semimodule_LDistr_Homo\<^sub>Z_rev_\<phi>Some:
  \<open> Semimodule_LDistr_Homo\<^sub>Z_rev F T Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F s T \<^emph> \<black_circle> F t T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> \<black_circle> F (s + t) T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_rev_def Premise_def Transformation_def
  by (clarsimp; metis prod.collapse)

lemma apply_Semimodule_LDistr_Homo\<^sub>U:
  \<open> Semimodule_LDistr_Homo\<^sub>U F T Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F t T \<^emph> F s T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>U_def Premise_def
  by blast

lemma apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some:
  \<open> Semimodule_LDistr_Homo\<^sub>U F T Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> \<black_circle> F t T \<^emph> \<black_circle> F s T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>U_def Premise_def Transformation_def
  by (clarsimp; metis sep_disj_option(1) times_option(1))

lemma apply_Semimodule_LDistr_Homo\<^sub>U_rev:
  \<open> Semimodule_LDistr_Homo\<^sub>U_rev F T Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F s T \<^emph> F t T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>U_rev_def Premise_def
  by blast

lemma apply_Semimodule_LDistr_Homo\<^sub>U_rev_\<phi>Some:
  \<open> Semimodule_LDistr_Homo\<^sub>U_rev F T Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> \<black_circle> F s T \<^emph> \<black_circle> F t T \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>U_rev_def Premise_def Transformation_def
  by (clarsimp; metis sep_disj_option(1) times_option(1))


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

subsubsection \<open>Implementation\<close>

paragraph \<open>Templates Generating Rules\<close>

(*
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
*)

lemma \<phi>intro_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<close>
  by simp

lemma \<phi>intro_reasoning_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P \<close>
  by simp

text \<open>The generated intro-rule is in \<open>x \<Ztypecolon> T \<^emph>[C] R\<close> form to the best which is the most general
      and falls back to \<open>x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R\<close> if the definition cannot be rewrote to type form \<open>x \<Ztypecolon> T \<equiv> y \<Ztypecolon> U\<close>.

Priorities: \<open>\<phi>intro'_reasoning_transformation_ty_var\<close> >
            \<open>\<phi>intro'_reasoning_transformation_ty\<close> >
            \<open>\<phi>intro'_reasoning_transformation\<close>
\<close>

lemma \<phi>intro'_reasoning_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma \<phi>intro'_reasoning_transformation_ty:
  \<open> (x \<Ztypecolon> T) = (y \<Ztypecolon> U)
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, r) \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x, r) \<Ztypecolon> T \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  by (cases C; simp add: \<phi>Prod_expn')

lemma \<phi>elim_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<close>
  by simp

lemma \<phi>elim_reasoning_transformation:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma \<phi>elim'SEi_transformation:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (y x \<Ztypecolon> U x))
\<Longrightarrow> apfst y x \<Ztypecolon> U (fst x) \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by (cases C; cases x; simp add: \<phi>Prod_expn')

(* TODO!!!:
lemma \<phi>elim'SE_transformation:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (y x \<Ztypecolon> U))
\<Longrightarrow> (y (fst x), snd x) \<Ztypecolon> U \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SE True
\<Longrightarrow> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Auto_Transform_Hint Y' (x' \<Ztypecolon> T') \<and> P @action \<A>SE True\<close>*)

lemma \<phi>open_abstraction:
  \<open> (x \<Ztypecolon> T) = (y' \<Ztypecolon> U')
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U' \<s>\<u>\<b>\<j> y. y = y' @action to OPEN \<close>
  unfolding Action_Tag_def Simplify_def
  by simp

lemma \<phi>make_abstraction:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def MAKE_def by simp

lemma \<phi>make_abstraction'R:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def MAKE_def by simp

lemma \<phi>gen_expansion:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> p \<Turnstile> (x \<Ztypecolon> T) \<equiv> p \<Turnstile> U \<close>
  by simp

consts \<A>_template_reason :: action \<comment> \<open>tagging the antecedent has to be solved during the time of
                                       template instantiation.\<close>
definition \<open>template_NO_SIMP_USE (X::bool) \<equiv> X\<close>
  \<comment> \<open>prevent using the protected proposition in simplification during template instantiation.\<close>

ML_file \<open>library/phi_type_algebra/properties.ML\<close>
ML_file \<open>library/phi_type_algebra/typ_def.ML\<close>

(* ML_file \<open>library/tools/type_algebra_guess_mapper.ML\<close> *)

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

ML \<open> (the (BNF_FP_Def_Sugar.fp_sugar_of \<^context> \<^type_name>\<open>list\<close>))

\<close>

ML \<open>BNF_Def.rel_eq_of_bnf (the (BNF_Def.bnf_of \<^context> \<^type_name>\<open>list\<close>))\<close>

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






paragraph \<open>Configurations\<close>

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
      (fn (_ $ F $ _ $ _ $ _ $ _ $ _ $ _ ) => F)
#> add_property_kind \<^const_name>\<open>Separation_Homo\<^sub>E\<close>
      (fn (_ $ F $ _ $ _ $ _ $ _ $ _ ) => F)
#> add_property_kind \<^const_name>\<open>Closed_Semimodule_Zero\<close>
      (fn (_ $ F $ _ ) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_Zero\<close>
      (fn (_ $ F $ _ ) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_Identity\<close>
      (fn (_ $ F $ _ ) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_Scalar_Assoc\<close>
      (fn (_ $ F $ _ $ _ ) => attach_var F)
(* #> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Unit_Functor\<close> (fn (_ $ F) => F) *)
#> add_property_kind \<^const_name>\<open>Semimodule_LDistr_Homo\<^sub>Z\<close>
      (fn (_ $ F $ _ $ _ $ _ $ _) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_LDistr_Homo\<^sub>Z_rev\<close>
      (fn (_ $ F $ _ $ _ $ _ $ _) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_LDistr_Homo\<^sub>U\<close>
      (fn (_ $ F $ _ $ _ $ _) => attach_var F)
#> add_property_kind \<^const_name>\<open>Semimodule_LDistr_Homo\<^sub>U_rev\<close>
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



subsection \<open>Programming Methods to Prove the Properties\<close>


subsubsection \<open>Transformation Functor\<close>

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>T U x g.
            \<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b
        \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
        \<Longrightarrow> x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Transformation_Functor F1 F2 D R mapper)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Transformation_Functor_def Premise_def
  by clarsimp


subsubsection \<open>Separation Homo\<close>

(* TODO
lemma
  \<open> PROP \<phi>Programming_Method (\<And>T U x g.
            \<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b
        \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
        \<Longrightarrow> x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Separation_Homo\<^sub>I Ft Fu Fc D R mapper)) MM DD RR FF \<close> *)


subsubsection \<open>Semimodule Functor\<close>

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t (x,y) \<Ztypecolon> F (s + t) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_LDistr_Homo\<^sub>Z_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds t \<and> Ds s \<and> t ##\<^sub>+ s \<and> Dx t s (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s (x,y) \<Ztypecolon> F (t + s) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_LDistr_Homo\<^sub>Z_rev F T Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_LDistr_Homo\<^sub>Z_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
          \<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F t T \<^emph> F s T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_LDistr_Homo\<^sub>U F T Ds Dx uz)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_LDistr_Homo\<^sub>U_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
          \<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F s T \<^emph> F t T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_LDistr_Homo\<^sub>U_rev F T Ds Dx uz)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_LDistr_Homo\<^sub>U_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')


subsection \<open>Reasonings and Their Applications\<close>

subsubsection \<open>Vary Type Operator among Instantiations\<close>

definition Type_Variant_of_the_Same_Type_Operator
        :: \<open> ('a \<Rightarrow> ('b,'c) \<phi>) \<Rightarrow> ('a2 \<Rightarrow> ('b2,'c2) \<phi>) \<Rightarrow> bool \<close>
  where \<open> Type_Variant_of_the_Same_Type_Operator Fa Fb \<longleftrightarrow> True \<close>
  \<comment> \<open>Fa and Fb are the same functor having identical parameters but of different type instantiations.
      We use this to simulate the \<Lambda> operator in system-F\<close>

definition Type_Variant_of_the_Same_Type_Operator2
        :: \<open> ('s \<Rightarrow> 'a \<Rightarrow> ('b,'c) \<phi>) \<Rightarrow> ('s2 \<Rightarrow> 'a2 \<Rightarrow> ('b2,'c2) \<phi>) \<Rightarrow> bool \<close>
  where \<open> Type_Variant_of_the_Same_Type_Operator2 Fa Fb \<longleftrightarrow> True \<close>

definition Type_Variant_of_the_Same_Scalar_Mul
        :: \<open> ('s \<Rightarrow> 'a \<Rightarrow> ('b,'c) \<phi>) \<Rightarrow> ('s2 \<Rightarrow> 'a2 \<Rightarrow> ('b2,'c2) \<phi>) \<Rightarrow> bool \<close>
  where \<open> Type_Variant_of_the_Same_Scalar_Mul Fa Fb \<longleftrightarrow> True \<close>

(*definition Parameter_Variant_of_the_Same_Type :: \<open> ('a,'b) \<phi> \<Rightarrow> ('c,'d) \<phi> \<Rightarrow> bool \<close>
  where \<open> Parameter_Variant_of_the_Same_Type Fa Fb \<longleftrightarrow> True \<close> *)

declare [[
  \<phi>reason_default_pattern
      \<open>Type_Variant_of_the_Same_Type_Operator ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Type_Operator ?Fa _\<close> (100)
  and \<open>Type_Variant_of_the_Same_Type_Operator2 ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Type_Operator2 ?Fa _\<close> (100)
  and \<open>Type_Variant_of_the_Same_Scalar_Mul ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Scalar_Mul ?Fa _\<close> (100)
  (*and \<open>Parameter_Variant_of_the_Same_Type ?Fa _\<close> \<Rightarrow> \<open>Parameter_Variant_of_the_Same_Type ?Fa _\<close> (100) *)
  
  (* \<phi>premise_attribute? [\<phi>reason add] for \<open>Type_Variant_of_the_Same_Type_Operator _ _\<close> *)
  (* \<phi>premise_attribute? [\<phi>reason add] for \<open>Parameter_Variant_of_the_Same_Type _ _\<close> *)
]]

(*
lemma Parameter_Variant_of_the_Same_Type_I [\<phi>reason 1]:
  \<open>Parameter_Variant_of_the_Same_Type Fa Fb\<close>
  unfolding Parameter_Variant_of_the_Same_Type_def .. *)

lemma Type_Variant_of_the_Same_Type_Operator_I:
  \<open>Type_Variant_of_the_Same_Type_Operator Fa Fb\<close>
  unfolding Type_Variant_of_the_Same_Type_Operator_def ..

lemma Type_Variant_of_the_Same_Type_Operator2_I:
  \<open>Type_Variant_of_the_Same_Type_Operator2 Fa Fb\<close>
  unfolding Type_Variant_of_the_Same_Type_Operator2_def ..

lemma Type_Variant_of_the_Same_Scalar_Mul_I:
  \<open>Type_Variant_of_the_Same_Scalar_Mul Fa Fb\<close>
  unfolding Type_Variant_of_the_Same_Scalar_Mul_def ..

ML_file \<open>library/phi_type_algebra/variant_phi_type_instantiations.ML\<close>

setup \<open>
   Phi_Type_Template_Properties.add_property_kind
          \<^const_name>\<open>Type_Variant_of_the_Same_Type_Operator\<close> (fn (_ $ F $ _) => F)
#> Phi_Type_Template_Properties.add_property_kind
          \<^const_name>\<open>Type_Variant_of_the_Same_Type_Operator2\<close> (fn (_ $ F $ _) => F)
#> Phi_Type_Template_Properties.add_property_kind
          \<^const_name>\<open>Type_Variant_of_the_Same_Scalar_Mul\<close> (fn (_ $ F $ _) => F)
\<close>


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
 
lemma transformation[\<phi>simplify_reasoning_rule]:
  \<open> \<g>\<u>\<a>\<r>\<d> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>
  unfolding meta_Ball_def Premise_def \<r>Guard_def
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

lemma [\<phi>simplify_reasoning_rule,
       \<phi>reason default %to_trans_derived_Tr_functor]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fb Z) \<close>
  unfolding Action_Tag_def
  using transformation[unfolded \<r>Guard_def] .

lemma [\<phi>simplify_reasoning_rule,
       \<phi>reason default %to_trans_derived_Tr_functor]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z) \<close>
  unfolding Action_Tag_def
  using transformation[unfolded \<r>Guard_def] .
   
lemma [\<phi>simplify_reasoning_rule,
       \<phi>transformation_based_simp default %\<phi>simp_derived_Tr_functor no trigger]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>simp)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>simp \<close>
  unfolding Action_Tag_def Premise_def
  using transformation[unfolded Premise_def \<r>Guard_def] .

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

lemma [\<phi>reason_template default %\<phi>simp_derived_Tr_functor+5]:
  \<open> Separation_Homo\<^sub>E Fa\<^sub>L Fa\<^sub>R Fb U\<^sub>L U\<^sub>R un
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
+ fixes pred_mapper :: \<open>('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> bool\<close>
    and func_mapper :: \<open>('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f\<close>
  assumes functional_mapper:
      \<open>Prem \<Longrightarrow> (\<forall>a' b'. mapper (\<lambda>a b. b = f a \<and> P a) a' b' \<longrightarrow> b' = func_mapper f P a' \<and> pred_mapper f P a')\<close>
      \<comment> \<open>When the element transformation is applied with a partial function (with \<open>P\<close> giving the domain),
          the entire transformation is also a partial function.
          The \<^verbatim>\<open>func_mapper\<close> is usually the functional mapper and the
          \<^verbatim>\<open>pred_mapper\<close> is the predicate mapper of an ADT. An exceptional example is set,
          \<open>func_mapper\<^sub>s\<^sub>e\<^sub>t f P S = { f x |x \<in> S. P x }\<close> and \<open>pred_mapper\<^sub>s\<^sub>e\<^sub>t f P S = \<top>\<close>,
          whose (generalized) algebraic mappers are however set image and set-forall (of its element).\<close>

setup \<open>Phi_Type_Template_Properties.add_property_kind \<^const_name>\<open>Functional_Transformation_Functor\<close>
            (fn (_ $ F $ _ $ _ $ _ $ _ $ _ $ _ $ _) => F)\<close>

context Functional_Transformation_Functor
begin

lemma Functional_Transformation_Functor[\<phi>reason add (*pirority?*)]:
  \<open>Functional_Transformation_Functor Fa Fb D R mapper Prem pred_mapper func_mapper\<close>
  by (simp add: Functional_Transformation_Functor_axioms)

lemma [\<phi>simplify_reasoning_rule,
       \<phi>reason default %ToA_derived_one_to_one_functor for \<open>_ \<Ztypecolon> Fa _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> Fb _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x\<close>
  unfolding meta_Ball_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], simplified]
        functional_mapper
  by (clarsimp simp add: Transformation_def, blast)
  

lemma functional_transformation:
  \<open> Prem
\<Longrightarrow> (\<And>a \<in> D x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x\<close>
  unfolding meta_Ball_def Argument_def Premise_def
  using Transformation_Functor[unfolded Transformation_Functor_def,
          THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=x],
          THEN spec[where x=\<open>(\<lambda>a b. b = f a \<and> P a)\<close>], simplified]
        functional_mapper
  by (clarsimp simp add: Transformation_def, blast)

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

declare [[\<phi>reason_default_pattern
      \<open>Functional_Transformation_Functor ?Fa ?Fb _ _ _ _ _ _\<close>
   \<Rightarrow> \<open>Functional_Transformation_Functor ?Fa ?Fb _ _ _ _ _ _\<close> (100)
]]



subsubsection \<open>Separation Homomorphism\<close>

lemma Object_Sep_Homo\<^sub>I_subdom[\<phi>reason %\<phi>TA_varify_out except \<open>Object_Sep_Homo\<^sub>I _ ?var\<close>]:
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

lemma Separation_Homo_functor[\<phi>reason_template %Object_Sep_Homo_functor]:
  \<open> Separation_Homo\<^sub>I F F F' T T Ds zz
\<Longrightarrow> Transformation_Functor F' F D R m
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
      by (clarsimp, insert prems(3,6), blast)
    from prems(2)[THEN spec[where x=\<open>T \<^emph> T\<close>], THEN spec[where x=T], THEN spec[where x=\<open>zz (y,x)\<close>],
                 THEN spec[where x=\<open>\<lambda>(b,a) c. c = a * b \<and> a ## b \<and> (b,a) \<in> D (zz (y,x))\<close>],
                 THEN mp, OF t1]
         prems(4)[THEN spec[where x=y], THEN spec[where x=x]]
         prems(1,5,6)
    show ?thesis
      by (clarsimp simp add: Transformation_def; blast)
  qed .

lemma [\<phi>reason_template name \<phi>Prod []]:
  \<open> Separation_Homo\<^sub>I Ft Fu Fc T U UNIV (\<lambda>x. x)
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U (\<lambda>x. x)
\<Longrightarrow> Fc (T \<^emph> U) = Ft T \<^emph> Fu U \<close>
  unfolding Separation_Homo\<^sub>I_def Separation_Homo\<^sub>E_def
  by (rule \<phi>Type_eqI_Tr ; simp add: split_paired_all)

lemma apply_conditioned_Separation_Functor_unzip:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U un)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Functional_Transformation_Functor Fc Ft D R mapper Prem pred_mapper func_mapper)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Prem)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<and> \<not> C \<longrightarrow> fst a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph>[C] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then un x else (func_mapper fst (\<lambda>_. True) x, undefined)) \<Ztypecolon> Ft(T) \<^emph>[C] Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'[symmetric] Premise_def
  apply (cases C; simp)
  \<medium_left_bracket> premises FTF and [] and [useful] and []
    interpret Functional_Transformation_Functor Fc Ft D R mapper True pred_mapper func_mapper
      using FTF . ;;
    apply_rule functional_transformation[where f=\<open>fst\<close> and P=\<open>\<lambda>_. True\<close>]
    \<medium_left_bracket> ;; \<medium_right_bracket> ;;
  \<medium_right_bracket> .

(*
subsubsection \<open>Transformation of Single \<phi>-Type with Remainders\<close>

lemma [\<phi>reason_template default 80]:
  \<open> \<g>\<u>\<a>\<r>\<d> Prem \<and>\<^sub>\<r> Prem'
\<Longrightarrow> Functional_Transformation_Functor F1 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Functional_Transformation_Functor F23 F3 Dom' Rng' mapper' Prem' pred_mapper' func_mapper'
\<Longrightarrow> Separation_Homo\<^sub>E F3 F2 F23 U R uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> Dom x \<longrightarrow> f a \<in> Rng x) \<and>
           (\<forall>a. a \<in> Dom' (func_mapper f P x) \<and> \<not> C \<longrightarrow> fst a \<in> Rng' (func_mapper f P x))
\<Longrightarrow> (\<And>x \<in> Dom x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P x )
\<Longrightarrow> x \<Ztypecolon> F1 T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then uz (func_mapper f P x) else (func_mapper' fst (\<lambda>_. True) (func_mapper f P x), undefined)) \<Ztypecolon> F3 U \<^emph>[C] F2 R
    \<w>\<i>\<t>\<h> pred_mapper f P x \<close>
  unfolding \<r>Guard_def Ant_Seq_imp
  \<medium_left_bracket> premises [\<phi>reason add] and [\<phi>reason add] and FTF and [\<phi>reason add] and _ and _ and Tr
    interpret Functional_Transformation_Functor F1 F23 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF . ;;
    apply_rule functional_transformation[where U=\<open>U \<^emph>[C] R\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_conditioned_Separation_Functor_unzip[where Fc=F23 and Ft=F3 and Fu=F2]
  \<medium_right_bracket> .
*)
paragraph \<open>\<open>Separation_Homo\<^sub>I\<close> for Non-semigroup\<close> \<comment> \<open>as they cannot be handled by stepwise rule and
                                                    therefore the NToA procedure\<close>


(*
thm apply_Separation_Functor_unzip[unfolded \<phi>Prod_expn''[simplified]]
declare apply_Separation_Functor_unzip
        [unfolded \<phi>Prod_expn''[simplified],
         \<phi>reason_template 45 except \<open>(_ :: ?'a :: sep_semigroup set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _\<close>]
*)


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

(* TODO: depreciate
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
*)

subsubsection \<open>Semimodule\<close>

paragraph \<open>Zero\<close>

lemma [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice,
       \<phi>adding_property = true]:
  \<open> Closed_Semimodule_Zero F T
\<Longrightarrow> Semimodule_Zero F T \<close>
  unfolding Closed_Semimodule_Zero_def Semimodule_Zero_def
  by simp

lemma [\<phi>reason_template [assertion_simps, simp]]:
  \<open> Closed_Semimodule_Zero F T
\<Longrightarrow> (x \<Ztypecolon> F 0 T) = 1 \<close>
  unfolding Closed_Semimodule_Zero_def by blast

lemma [\<phi>reason_template %ToA_derived_red requires Semimodule_Zero]:
  \<open> Semimodule_Zero F T
\<Longrightarrow> NO_SIMP (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F 0 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def Identity_Element\<^sub>E_def NO_SIMP_def
  using mk_elim_transformation by blast

lemma [\<phi>reason_template %ToA_derived_red requires Semimodule_Zero]:
  \<open> Semimodule_Zero F T
\<Longrightarrow> NO_SIMP (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F 0 T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Semimodule_Zero_def Identity_Element\<^sub>E_def NO_SIMP_def
  using implies_bi_frame by fastforce

lemma [\<phi>reason_template %ToA_derived_red requires Closed_Semimodule_Zero]:
  \<open> Closed_Semimodule_Zero F T
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F 0 T \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by simp

lemma [\<phi>reason_template %ToA_derived_red requires Closed_Semimodule_Zero]:
  \<open> Closed_Semimodule_Zero F T
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F 0 T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by simp


paragraph \<open>Identity\<close>

lemma [\<phi>reason_template name scalar_identity [assertion_simps, simp]]:
  \<open> Semimodule_Identity F T
\<Longrightarrow> F 1 T = T \<close>
  unfolding Semimodule_Identity_def .

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity F T
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F 1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity_def NO_SIMP_def \<r>Guard_def
  by simp

lemma [\<phi>reason_template no explorative backtrack %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity F T
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F 1 T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity_def NO_SIMP_def \<r>Guard_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity F T
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F 1 T \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity_def NO_SIMP_def \<r>Guard_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity F T
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F 1 T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity_def NO_SIMP_def \<r>Guard_def
  by simp


paragraph \<open>Associative\<close>

lemma [\<phi>reason_template name scalar_assoc [assertion_simps, simp]]:
  \<open> Semimodule_Scalar_Assoc F T Ds
\<Longrightarrow> Ds a \<and> Ds b
\<Longrightarrow> F a (F b T) = F (b * a) T \<close>
  unfolding Semimodule_Scalar_Assoc_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc F T Ds
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds b
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F (b * a) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F a (F b T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc_def Premise_def NO_SIMP_def \<r>Guard_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc F T Ds
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds b
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F (b * a) T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F a (F b T)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc_def Premise_def NO_SIMP_def \<r>Guard_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc F T Ds
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds b
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F (b * a) T \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F a (F b T) \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc_def Premise_def NO_SIMP_def \<r>Guard_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc F T Ds
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds b
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F (b * a) T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F a (F b T) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc_def Premise_def NO_SIMP_def \<r>Guard_def
  by simp


paragraph \<open>Left Distributivity\<close>

lemma [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice,
       \<phi>adding_property = true ]:
  \<open> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z_rev F T Ds (\<lambda>s t. Dx s t o prod.swap) (\<lambda>s t. z s t o prod.swap)\<close>
  for F :: \<open>('s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)\<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_rev_def Semimodule_LDistr_Homo\<^sub>Z_def
  by (simp add: \<phi>Prod_expn'; metis mult.commute)

lemma [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice-1,
       \<phi>adding_property = true ]:
  \<open> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z_rev F T Ds (\<lambda>s t. Dx t s) (\<lambda>s t. z t s)\<close>
  for F :: \<open>('s::partial_ab_semigroup_add \<Rightarrow> ('c::sep_magma,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)\<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_rev_def Semimodule_LDistr_Homo\<^sub>Z_def
  by (simp add: dom_of_add_commute partial_add_commute)



subsubsection \<open>Separation Extraction\<close>

paragraph \<open>Transformation Functor\<close>

(* preserved for documenting
declare [[\<phi>trace_reasoning = 1]]

lemma "_Structural_Extract_general_rule_":
  \<open> \<g>\<u>\<a>\<r>\<d> Prem
\<Longrightarrow> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 T W Dz z
\<Longrightarrow> Separation_Homo\<^sub>E F3 F2 F23 U R uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P x @action \<A>SE )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f P (z x)) \<Ztypecolon> F3 U \<^emph> F2 R \<w>\<i>\<t>\<h> pred_mapper f P (z x) @action \<A>SE \<close>
  unfolding \<r>Guard_def Ant_Seq_imp
  \<medium_left_bracket> premises [\<phi>reason add] and FTF and _ and _ and _ and Tr
    interpret Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U \<^emph> R\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_Separation_Functor_unzip
  \<medium_right_bracket> .
 
declare "_Structural_Extract_general_rule_"[THEN \<A>SE_clean_waste, \<phi>reason_template default 80]

lemma [THEN \<A>SE_clean_waste_TH, \<phi>reason_template default 81]:
  \<open> \<g>\<u>\<a>\<r>\<d> Prem
\<Longrightarrow> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 T W Dz z
\<Longrightarrow> Separation_Homo\<^sub>E F3 F2 F23 U R uz
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F1 F1'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F2 F2'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F3 F3'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F4 F4'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y\<^sub>H \<Ztypecolon> U\<^sub>H \<^emph> R\<^sub>H) (x\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P x) @action \<A>SE )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f P (z x)) \<Ztypecolon> F3 U \<^emph> F2 R \<w>\<i>\<t>\<h> 
      Auto_Transform_Hint (y'\<^sub>H \<Ztypecolon> F3' U\<^sub>H \<^emph> F2' R\<^sub>H) (x'\<^sub>H \<Ztypecolon> F1' T\<^sub>H \<^emph> F4' W\<^sub>H) \<and> pred_mapper f P (z x) @action \<A>SE \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using "_Structural_Extract_general_rule_"[where f=f and uz=uz and func_mapper=func_mapper and z=z and pred_mapper=pred_mapper] .
*)




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


definition \<open>Separation_Homo\<^sub>I\<^sub>C Ft Fu F3 T U D z Cw \<longleftrightarrow>
              (\<forall>x y. (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph>[Cw] Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (T \<^emph>[Cw] U)))\<close>


(* WIP TODO
lemma
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cw \<Longrightarrow> Separation_Homo\<^sub>I Ft Fu F3 T U Dz z)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> Cw \<Longrightarrow> Functional_Transformation_Functor Ft F3 Dom Rng mapper Prem pred_mapper func_mapper)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> Cw \<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Prem)
\<Longrightarrow> Separation_Homo\<^sub>I\<^sub>C Ft Fu F3 T U
                     (if Cw then Dz else {x. \<forall>a \<in> Dom (fst x). (a, undefined) \<in> Rng (fst x)})
                     (if Cw then z else (\<lambda>x. func_mapper (\<lambda>a. (a, undefined)) (\<lambda>_. True) (fst x))) Cw \<close>
  unfolding Separation_Homo\<^sub>I\<^sub>C_def Premise_def Separation_Homo\<^sub>I_def \<r>Guard_def
  apply (cases Cw; clarsimp)
  \<medium_left_bracket> premises FTF and _ and _ and [useful]
    interpret Functional_Transformation_Functor Ft F3 Dom Rng mapper True pred_mapper func_mapper
      using FTF . ;;
    apply_rule functional_transformation[where f=\<open>\<lambda>a. (a, undefined)\<close> and P=\<open>\<lambda>_. True\<close> and U=\<open>T \<^emph>[Cw] U\<close>]
    \<medium_left_bracket> \<medium_right_bracket>
*)


lemma "_Structural_Extract_general_rule_i_"[\<phi>reason_template default %derived_SE_functor]:
  \<open> \<g>\<u>\<a>\<r>\<d> Prem \<and>\<^sub>\<r> Prem'r \<and>\<^sub>\<r> Prem'w \<and>\<^sub>\<r> Prem'b
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F14 F3 Dom Rng'r mapper'r Prem'r pred_mapper'r func_mapper'r
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F1 F23 Dom'w Rng'w mapper'w Prem'w pred_mapper'w func_mapper'w
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F1 F3  Dom'w Rng'b mapper'b Prem'b pred_mapper'b func_mapper'b
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>I F1 F4 F14 T W Dz z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>E F3 F2 F23 U R uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Cw \<longrightarrow> x \<in> Dz) \<and>
        (if Cw then if Cr then (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
                          else (\<forall>a. a \<in> Dom (z x) \<longrightarrow> fst (f a) \<in> Rng'r (z x))
               else if Cr then (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> f (a, undefined) \<in> Rng'w (fst x))
                          else (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> fst (f (a, undefined)) \<in> Rng'b (fst x)))

\<Longrightarrow> (\<And>x \<in> (if Cw then Dom (z x) else Dom'w (fst x) \<times> {undefined}).
        x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P x )

\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph>[Cw] F4 W

    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if Cw then if Cr then uz (func_mapper f P (z x))
                                else (func_mapper'r (fst o f) P (z x), undefined)
                     else if Cr then uz (func_mapper'w (\<lambda>x. f (x, undefined)) (\<lambda>x. P (x, undefined)) (fst x))
                                else (func_mapper'b (\<lambda>x. fst (f (x, undefined))) (\<lambda>x. P (x, undefined)) (fst x), undefined))
                \<Ztypecolon> F3 U \<^emph>[Cr] F2 R

    \<w>\<i>\<t>\<h> (if Cw then if Cr then pred_mapper f P (z x)
                           else pred_mapper'r (fst o f) P (z x)
                else if Cr then pred_mapper'w (\<lambda>x. f (x, undefined)) (\<lambda>x. P (x, undefined)) (fst x)
                           else pred_mapper'b (\<lambda>x. fst (f (x, undefined))) (\<lambda>x. P (x, undefined)) (fst x)) \<close>
  apply (cases Cw; cases Cr; simp add: \<phi>Some_\<phi>Prod \<r>Guard_def Ant_Seq_imp)
  \<medium_left_bracket> premises [] and [] and [] and []
         and FTF and [] and [] and []
         and _ and _ and _ and Tr
    interpret Functional_Transformation_Functor F14 F23 Dom Rng mapper True pred_mapper func_mapper
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U \<^emph> R\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_Separation_Functor_unzip
  \<medium_right_bracket>
  \<medium_left_bracket> premises [] and [] and [] and []
         and [] and FTF and [] and []
         and _ and [] and _ and Tr
    interpret Functional_Transformation_Functor F14 F3 Dom Rng'r mapper'r True pred_mapper'r func_mapper'r
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U\<close> and f=\<open>fst o f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
  \<medium_right_bracket>
  \<medium_left_bracket> premises [] and [] and [] and []
         and [] and [] and FTF and []
         and [] and _ and _ and Tr
    interpret Functional_Transformation_Functor F1 F23 Dom'w Rng'w mapper'w True pred_mapper'w func_mapper'w
      using FTF . ;;
    apply_rule functional_transformation[where U=\<open>U \<^emph> R\<close> and f=\<open>\<lambda>x. f (x, undefined)\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
      note [[\<phi>trace_reasoning = 2]]
      thm Tr
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_Separation_Functor_unzip
  \<medium_right_bracket>
  \<medium_left_bracket> premises [] and [] and [] and []
         and [] and [] and [] and FTF
         and [] and [] and _ and Tr
    interpret Functional_Transformation_Functor F1 F3 Dom'w Rng'b mapper'b True pred_mapper'b func_mapper'b
      using FTF . ;;
    apply_rule functional_transformation[where U=\<open>U\<close> and f=\<open>\<lambda>x. fst (f (x, undefined))\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
  \<medium_right_bracket> .

(*DO NOT REMOVE, for Auto_Transform_Hint
lemma "_Structural_Extract_general_rule_i_TH_"[\<phi>reason_template default 81]:
  \<open> \<g>\<u>\<a>\<r>\<d> Prem \<and>\<^sub>\<r> Prem'r \<and>\<^sub>\<r> Prem'w \<and>\<^sub>\<r> Prem'b
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F14 F3 Dom Rng'r mapper'r Prem'r pred_mapper'r func_mapper'r
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F1 F23 Dom'w Rng'w mapper'w Prem'w pred_mapper'w func_mapper'w
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F1 F3  Dom'w Rng'b mapper'b Prem'b pred_mapper'b func_mapper'b
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>I F1 F4 F14 T W Dz z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>E F3 F2 F23 U R uz
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
        x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h>
            Auto_Transform_Hint (y1\<^sub>H \<Ztypecolon> U\<^sub>H \<^emph>[Cr] R\<^sub>H) (x1\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph>[Cw] W\<^sub>H) \<and> P x )

\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph>[Cw] F4 W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if Cw then if Cr then uz (func_mapper f P (z x))
                                else (func_mapper'r (fst o f) P (z x), undefined)
                     else if Cr then uz (func_mapper'w (\<lambda>x. f (x, undefined)) (\<lambda>x. P (x, undefined)) (fst x))
                                else (func_mapper'b (\<lambda>x. fst (f (x, undefined))) (\<lambda>x. P (x, undefined)) (fst x), undefined))
                \<Ztypecolon> F3 U \<^emph>[Cr] F2 R

    \<w>\<i>\<t>\<h> Auto_Transform_Hint (y2\<^sub>H \<Ztypecolon> F3' U\<^sub>H \<^emph>[Cr] F2' R\<^sub>H) (x2\<^sub>H \<Ztypecolon> F1' T\<^sub>H \<^emph>[Cw] F4' W\<^sub>H)
      \<and> (if Cw then if Cr then pred_mapper f P (z x) else pred_mapper'r (fst o f) P (z x)
               else if Cr then pred_mapper'w (\<lambda>x. f (x, undefined)) (\<lambda>x. P (x, undefined)) (fst x)
                          else pred_mapper'b (\<lambda>x. fst (f (x, undefined))) (\<lambda>x. P (x, undefined)) (fst x) )
    \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using "_Structural_Extract_general_rule_i_"[where pred_mapper=pred_mapper
          and pred_mapper'w=pred_mapper'w and P=P and uz=uz and func_mapper=func_mapper
          and func_mapper'r=func_mapper'r and func_mapper'w=func_mapper'w
          and func_mapper'b=func_mapper'b] .
*)



(*
lemma "_Structural_Extract_general_rule_a_":
  \<open> \<g>\<u>\<a>\<r>\<d> Prem
\<Longrightarrow> Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 T W Dz z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<w>\<i>\<t>\<h> P x @action \<A>SEa )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P (z x) \<Ztypecolon> F3 U \<w>\<i>\<t>\<h> pred_mapper f P (z x) @action \<A>SEa \<close>
  unfolding \<r>Guard_def Ant_Seq_imp
  \<medium_left_bracket> premises [\<phi>reason add] and FTF and _ and _ and Tr
    interpret Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF . ;;
    apply_rule apply_Separation_Functor_zip[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket> ;;
  \<medium_right_bracket> .

declare "_Structural_Extract_general_rule_a_"[THEN \<A>SEa_clean_waste, \<phi>reason_template default 80]

lemma "_Structural_Extract_general_rule_a_TH_"[\<phi>reason_template default 81]:
  \<open> \<g>\<u>\<a>\<r>\<d> Prem
\<Longrightarrow> Functional_Transformation_Functor F14 F3 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Separation_Homo\<^sub>I F1 F4 F14 T W Dz z
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F1 F1'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F3 F3'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F4 F4'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<w>\<i>\<t>\<h>
      Auto_Transform_Hint (y1\<^sub>H \<Ztypecolon> U\<^sub>H) (x2\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P x @action \<A>SEa )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph> F4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P (z x) \<Ztypecolon> F3 U \<w>\<i>\<t>\<h>
      Auto_Transform_Hint (y2\<^sub>H \<Ztypecolon> F3' U\<^sub>H) (x2\<^sub>H \<Ztypecolon> F1' T\<^sub>H \<^emph> F4' W\<^sub>H) \<and> pred_mapper f P (z x) @action \<A>SEa \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using "_Structural_Extract_general_rule_a_"[where func_mapper=func_mapper and P=P
            and pred_mapper=pred_mapper] .
*)

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


paragraph \<open>Semimodule Scalar Associative \label{Semimodule-Scalar-Associative}\<close>

text \<open>The proof search is inefficient for semimodule \<phi>-type that satisfies both scalar associativity
  and scalar distributivity.
  This inefficiency stems from the two properties deriving rules that can be interchangeably applied.
  Given a \<phi>-type \<open>F a T\<close> and expect \<open>F b U\<close> with \<open>a \<noteq> b\<close>, we might identify some \<open>c\<close> with \<open>c * a = b\<close>,
  so we apply the associative rule and go to element transformations expecting the inner \<phi>-type \<open>T\<close>
  might supply the missing \<open>F c U\<close>;
  alternatively we can also identify a certain \<open>c\<close> with \<open>c + a = b\<close>, so we apply the distributive rule
  and hope the unexplored external portion of assertion contains the \<open>F c U\<close>.
  The situation is further complicated when the two rules are combined: the inner \<phi>-type \<open>T\<close> may
  contain some part \<open>c\<^sub>1\<close> while the external part contains the remaining part \<open>c\<^sub>2\<close>,
  \<open>c\<^sub>2 + c\<^sub>1 * a = b\<close>.

  To tackle this complexity, we introduce a normalization step before the reasoning,
  where we exhaustively apply the associative rules to eliminate any further need for them in the later reasoning.
  Viewing a \<phi>-type expression as a tree with type operators as nodes and atomic types as leaves,
  we push every module-like type operators \<open>F a T\<close> all the way down to the leaves, passing through type
  connectives like \<open>\<^emph>\<close> and \<open>\<^bold>\<rightarrow>\<close> by meas of homomorphic rules like \<open>F a (T \<^emph> U) = (F a T) \<^emph> (F a U)\<close>.
  In this way, all the module operator are gathered at the leaves.
  By exhaustively applying the associative rules on them, any need of associative rules
  is fully addressed, and consequently, in the subsequent reasoning, we can exclusively focus on
  the scalar distribution rules.

  Sure it raises further works for deriving the homomorphic rules. It can be done by a deriver generating
  that ....
\<close>

text \<open>According to the discussion above, the rule below should be used only for non-distributive scalars.\<close>

(*preserved for documenting

declare [[\<phi>trace_reasoning = 2]]

lemma SE_general_Semimodule_Scalar_left: (*need test, to be tested once we have usable test case*)
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c * a = b) \<and>\<^sub>\<r> Prem
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds b \<and> Ds c
\<Longrightarrow> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Semimodule_Scalar_Assoc F3 U Ds
\<Longrightarrow> Semimodule_Scalar_Assoc F4 W Ds
\<Longrightarrow> Separation_Homo\<^sub>I (F1 a) (F4 a) F14 T (F4 c W) Dz z
\<Longrightarrow> Separation_Homo\<^sub>E (F3 a) (F2 a) F23 (F3 c U) R uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> F4 c W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3 c U \<^emph> R \<w>\<i>\<t>\<h> P x @action \<A>SE )
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F4 b W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f P (z x)) \<Ztypecolon> F3 b U \<^emph> F2 a R \<w>\<i>\<t>\<h> pred_mapper f P (z x) @action \<A>SE \<close>
  unfolding \<r>Guard_def Ant_Seq_imp
  \<medium_left_bracket> premises _ and [\<phi>reason add] and _
         and FTF and LSF3[\<phi>reason add] and LSF4[\<phi>reason add] and _ and _
         and _ and Tr
    interpret Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(6))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(6)) ;;
    unfold F4D
    apply_rule apply_Separation_Functor_zip[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U \<^emph> R\<close> and f=f and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Functor_unzip[where x=\<open>func_mapper f P (z x)\<close>]
    fold F3D
  \<medium_right_bracket> .

declare SE_general_Semimodule_Scalar_left[THEN \<A>SE_clean_waste, \<phi>reason_template default 30]
  \<comment> \<open>The priority is smaller than the default rule of functional transformation\<close>
*)

lemma SE_general_Semimodule_Scalar_left_b: (*need test, to be tested once we have usable test case*)
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c * a = b) \<and>\<^sub>\<r> Prem \<and>\<^sub>\<r> Prem'r \<and>\<^sub>\<r> Prem'w \<and>\<^sub>\<r> Prem'b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds b \<and> Ds c
\<Longrightarrow> Functional_Transformation_Functor F14 F23 Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Functional_Transformation_Functor F14 (F3 a) Dom Rng'r mapper'r Prem'r pred_mapper'r func_mapper'r
\<Longrightarrow> Functional_Transformation_Functor (F1 a) F23 Dom'w Rng'w mapper'w Prem'w pred_mapper'w func_mapper'w
\<Longrightarrow> Functional_Transformation_Functor (F1 a) (F3 a) Dom'w Rng'b mapper'b Prem'b pred_mapper'b func_mapper'b
\<Longrightarrow> Semimodule_Scalar_Assoc F3 U Ds
\<Longrightarrow> Semimodule_Scalar_Assoc F4 W Ds
\<Longrightarrow> Separation_Homo\<^sub>I (F1 a) (F4 a) F14 T (F4 c W) Dz z
\<Longrightarrow> Separation_Homo\<^sub>E (F3 a) (F2 a) F23 (F3 c U) R uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Cw \<longrightarrow> x \<in> Dz) \<and>
           (if Cw then if Cr then (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
                             else (\<forall>a. a \<in> Dom (z x) \<longrightarrow> fst (f a) \<in> Rng'r (z x))
                  else if Cr then (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> f (a, undefined) \<in> Rng'w (fst x))
                             else (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> fst (f (a, undefined)) \<in> Rng'b (fst x)))

\<Longrightarrow> (\<And>x \<in> (if Cw then Dom (z x) else Dom'w (fst x) \<times> {undefined}).
          x \<Ztypecolon> T \<^emph>[Cw] F4 c W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3 c U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P x )

\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] F4 b W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if Cw then if Cr then uz (func_mapper f P (z x))
                                else (func_mapper'r (fst o f) P (z x), undefined)
                     else if Cr then uz (func_mapper'w (\<lambda>x. f (x, undefined)) (\<lambda>x. P (x, undefined)) (fst x))
                                else (func_mapper'b (\<lambda>x. fst (f (x, undefined))) (\<lambda>x. P (x, undefined)) (fst x), undefined))
                \<Ztypecolon> F3 b U \<^emph>[Cr] F2 a R
    \<w>\<i>\<t>\<h> (if Cw then if Cr then pred_mapper f P (z x) else pred_mapper'r (fst o f) P (z x)
                else if Cr then pred_mapper'w (\<lambda>x. f (x, undefined)) (\<lambda>x. P (x, undefined)) (fst x)
                           else pred_mapper'b (\<lambda>x. fst (f (x, undefined))) (\<lambda>x. P (x, undefined)) (fst x)) \<close>
  apply (cases Cw; cases Cr; simp add: \<phi>Some_\<phi>Prod \<r>Guard_def Ant_Seq_imp)
  \<medium_left_bracket> premises _ and [] and [] and [] and [] and _
         and FTF and [] and [] and []
         and LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and _ and _ and _ and Tr
    interpret Functional_Transformation_Functor F14 F23 Dom Rng mapper True pred_mapper func_mapper
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(6))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(6)) ;;
    unfold F4D
    apply_rule apply_Separation_Functor_zip[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U \<^emph> R\<close> and f=f and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Functor_unzip[where x=\<open>func_mapper f P (z x)\<close>]
    fold F3D
  \<medium_right_bracket>
  \<medium_left_bracket> premises _ and [] and [] and [] and [] and _
         and [] and FTF and [] and []
         and LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and _ and [] and _ and Tr
    interpret Functional_Transformation_Functor F14 \<open>F3 a\<close> Dom Rng'r mapper'r True pred_mapper'r func_mapper'r
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(6))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(6)) ;;
    unfold F4D
    apply_rule apply_Separation_Functor_zip[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U\<close> and f=\<open>fst o f\<close> and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    fold F3D
  \<medium_right_bracket>
  \<medium_left_bracket> premises _ and [] and [] and [] and [] and _
         and [] and [] and FTF and []
         and LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and [] and _ and _ and Tr
    interpret Functional_Transformation_Functor \<open>F1 a\<close> F23 Dom'w Rng'w mapper'w True pred_mapper'w func_mapper'w
      using FTF .
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (simp add: the_\<phi>(2) the_\<phi>(4) the_\<phi>(5)) ;;
    apply_rule functional_transformation[where U=\<open>F3 c U \<^emph> R\<close> and f=\<open>\<lambda>x. f (x, undefined)\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Functor_unzip[where x=\<open>func_mapper'w (\<lambda>x. f (x, undefined)) (\<lambda>x. P (x, undefined)) (fst x)\<close> and Fc = F23]
    fold F3D
  \<medium_right_bracket>
  \<medium_left_bracket> premises _ and [] and [] and [] and [] and _
         and [] and [] and [] and FTF
         and LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and _ and _ and _ and Tr
    interpret Functional_Transformation_Functor \<open>F1 a\<close> \<open>F3 a\<close> Dom'w Rng'b mapper'b True pred_mapper'b func_mapper'b
      using FTF .
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(5)) ;;
    apply_rule functional_transformation[where U=\<open>F3 c U\<close> and f=\<open>\<lambda>x. fst (f (x, undefined))\<close> and P=\<open>\<lambda>x. P (x, undefined)\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    fold F3D
  \<medium_right_bracket> .

declare SE_general_Semimodule_Scalar_left_b[(*THEN SE_clean_waste,*) \<phi>reason_template default %derived_SE_scalar_assoc]

(*
lemma SE_general_Semimodule_Scalar_left_a:
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> c * a = b) \<and>\<^sub>\<r> Prem
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds b \<and> Ds c
\<Longrightarrow> Functional_Transformation_Functor F14 (F3 a) Dom Rng mapper Prem pred_mapper func_mapper
\<Longrightarrow> Semimodule_Scalar_Assoc F3 U Ds
\<Longrightarrow> Semimodule_Scalar_Assoc F4 W Ds
\<Longrightarrow> Separation_Homo\<^sub>I (F1 a) (F4 a) F14 T (F4 c W) Dz z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph> F4 c W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3 c U \<w>\<i>\<t>\<h> P x @action \<A>SEa )
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F4 b W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P (z x) \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> pred_mapper f P (z x) @action \<A>SEa \<close>
  unfolding \<r>Guard_def Ant_Seq_imp
  \<medium_left_bracket> premises _ and [\<phi>reason add] and _
         and FTF and LSF3[\<phi>reason add] and LSF4[\<phi>reason add]
         and _ and _ and Tr
    interpret Functional_Transformation_Functor F14 \<open>F3 a\<close> Dom Rng mapper Prem pred_mapper func_mapper
      using FTF .
    have F4D: \<open>F4 b W = F4 a (F4 c W)\<close>
      by (simp add: the_\<phi>(3) the_\<phi>(5) the_\<phi>(6))
    have F3D: \<open>F3 b U = F3 a (F3 c U)\<close>
      by (simp add: \<open>Ds a \<and> Ds b \<and> Ds c\<close> the_\<phi>(6)) ;;
    unfold F4D
    apply_rule apply_Separation_Functor_zip[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U\<close> and f=f and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    fold F3D
  \<medium_right_bracket> .

declare SE_general_Semimodule_Scalar_left_a[THEN \<A>SEa_clean_waste, \<phi>reason_template default 30]
*)

subsubsection \<open>Separation Extraction of Semimodule Left Distributivity\<close>

(* preserved for documenting

text \<open>No need to clean the rules by \<A>SE_clean_waste\<close>

paragraph \<open>Commutative, Monoidal, Additive Zero\<close>

(*TODO: the non-commutative version of rules*)

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.*)
lemma SE_Semimodule_LDistr_da_bc[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> b ##\<^sub>+ c \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, fst (snd x)) \<and> Dx  b c (z d a (fst x, fst (snd x)))
\<Longrightarrow> (snd (uz b c (z d a (fst x, fst (snd x)))), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, fst (uz b c (z d a (fst x, fst (snd x)))), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where t=c and s=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.*)
lemma SE_Semimodule_LDistr_ad_cb[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d (fst (snd x), fst x) \<and> Dx  c b (z a d (fst (snd x), fst x))
\<Longrightarrow> (fst (uz c b (z a d (fst (snd x), fst x))), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz c b (z a d (fst (snd x), fst x))), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where t=d and s=a and F=F1 and x=\<open>(fst (snd x), fst x)\<close>]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where t=b and s=c and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma SE_Semimodule_LDistr_a_dbc[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx (d + b) c (fst x) \<and> Dx d b (snd (uz (d + b) c (fst x)))
\<Longrightarrow> (fst (uz d b (snd (uz (d + b) c (fst x)))), snd x) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz d b (snd (uz (d + b) c (fst x)))), fst (uz (d + b) c (fst x)), snd y) \<Ztypecolon> F3 b U \<^emph> F1 d T \<^emph> F1 c T \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where s=\<open>d + b\<close> and t=c and F=F1, folded a]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c. *)
lemma SE_Semimodule_LDistr_dac_b[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + a) \<and> Ds c \<and> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, fst (snd x)) \<and> Dx (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x)))
\<Longrightarrow> (z (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x))), snd (snd (snd x))) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> F1 c T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where s=d and t=a and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(fst (snd (snd x)), z d a (fst x, fst (snd x)))\<close>]
    Tr
  \<medium_right_bracket> .

(*DONE*)

paragraph \<open>Commutative, Monoidal, No Additive Zero\<close>

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative *)
lemma SE_Semimodule_LDistr_da_b[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, fst (snd x))
\<Longrightarrow> (z d a (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(* [--------a---------]
   [-----b-----][--c--]
   Give a, expect b; Remain c, d = 0. *)
lemma SE_Semimodule_LDistr_a_bc[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), snd x) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz b c (fst x)), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where t=c and s=b and F=F1, folded a]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative *)
lemma SE_Semimodule_LDistr_ad_b[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, fst (snd x))
\<Longrightarrow> (uz a d (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev[where s=a and t=d and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b; Remain c, d = 0.*)
lemma SE_Semimodule_LDistr_a_cb[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b (fst x)
\<Longrightarrow> (fst (uz c b (fst x)), snd x) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz c b (fst x)), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where t=b and s=c and F=F1, folded a]
    Tr
  \<medium_right_bracket> .

(*DONE*)

paragraph \<open>Non-Commutative, Monoidal, Additive Zero\<close>

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.*)
lemma SE_Semimodule_LDistr_da_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> b ##\<^sub>+ c \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a x \<and> Dx  b c (z d a x)
\<Longrightarrow> (fst (uz b c (z d a x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz b c (z d a x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=x]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where t=c and s=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.*)
lemma SE_Semimodule_LDistr_ad_cb_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d x \<and> Dx c b (z a d x)
\<Longrightarrow> (fst (uz c b (z a d x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz c b (z a d x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev[where t=d and s=a and F=F1 and x=x]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where t=b and s=c and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma SE_Semimodule_LDistr_a_dbc_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx' uz'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' (d + b) c (fst x) \<and> Dx d b (fst (uz' (d + b) c (fst x)))
\<Longrightarrow> (fst (uz d b (fst (uz' (d + b) c (fst x)))), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz d b (fst (uz' (d + b) c (fst x)))), snd (uz' (d + b) c (fst x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 d T \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where s=\<open>d + b\<close> and t=c and F=F1, folded a]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c. *)
lemma SE_Semimodule_LDistr_dac_b_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx' z'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds (d + a) \<and> Ds c \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, fst (snd x)) \<and> Dx' (d + a) c (z d a (fst x, fst (snd x)), snd (snd x))
\<Longrightarrow> (z' (d + a) c (z d a (fst x, fst (snd x)), snd (snd x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> F1 c T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where s=d and t=a and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(z d a (fst x, fst (snd x)), snd (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(*DONE*)

paragraph \<open>Non-Commutative, Monoidal, No Additive Zero\<close>

(* [--------a---------]
   [-----b-----][--c--]
   Give a, expect b; Remain c, d = 0. *)
lemma SE_Semimodule_LDistr_a_bc_nc[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz b c (fst x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where t=c and s=b and F=F1, folded a]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b; Remain c, d = 0.*)
lemma SE_Semimodule_LDistr_a_cb_nc[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b (fst x)
\<Longrightarrow> (fst (uz c b (fst x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz c b (fst x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where t=b and s=c and F=F1, folded a]
    Tr
  \<medium_right_bracket> .

(*DONE*)
*)

paragraph \<open>Commutative, Non-Unital Associative, No Additive Zero\<close>

text \<open>Non-unital algebra implies no additive zero.\<close>

ML_file \<open>library/phi_type_algebra/semimodule_rule_pass.ML\<close>
                                            
(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; the scalar has to be non-commutative, otherwise reduces to either \<open>SE_Semimodule_LDistr_da_b_i\<close> or \<open>SE_Semimodule_LDistr_a_cb_i\<close>*)
lemma SE_Semimodule_LDistr_da_bc_i
      [where Cw' = True, \<phi>reason_template %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, x\<^sub>d) \<and> Dx b c (z d a (fst x, x\<^sub>d))
\<Longrightarrow> (snd (uz b c (z d a (fst x, x\<^sub>d))), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> ((fst (uz b c (z d a (fst x, x\<^sub>d))), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr and [simp] and b
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F1 and x=\<open>(fst x,x\<^sub>d)\<close>]
       apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some[where t=c and s=b and F=F1]
       Tr
       b
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; the scalar has to be non-commutative, otherwise reduces to either \<open>SE_Semimodule_LDistr_da_b_i\<close> or \<open>SE_Semimodule_LDistr_a_cb_i\<close>*)
lemma SE_Semimodule_LDistr_ad_cb_i
      [where Cw' = True, \<phi>reason_template %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d (x\<^sub>d, fst x) \<and> Dx  c b (z a d (x\<^sub>d, fst x))
\<Longrightarrow> (fst (uz c b (z a d (x\<^sub>d, fst x))), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> ((snd (uz c b (z a d (x\<^sub>d, fst x))), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr and [simp] and b
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some[where t=d and s=a and F=F1 and x=\<open>(x\<^sub>d, fst x)\<close>]
       apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some[where t=b and s=c and F=F1]
       Tr
       b
  \<medium_right_bracket> .

lemma [\<phi>reason %\<A>merge for \<open>((_,_,_) \<Ztypecolon> \<half_blkcirc>[_] _ \<^emph> \<half_blkcirc>[True] _ \<^emph> \<half_blkcirc>[True] _) = (_ \<Ztypecolon> \<half_blkcirc>[_] _) @action \<A>merge\<close>]:
  \<open>((x,y,z) \<Ztypecolon> \<half_blkcirc>[True] T \<^emph> \<half_blkcirc>[True] U \<^emph> \<half_blkcirc>[True]  R) = ((x,y,z) \<Ztypecolon> \<half_blkcirc>[True] (T \<^emph> U \<^emph> R)) @action \<A>merge\<close>
  \<open>((x,y,z) \<Ztypecolon> \<half_blkcirc>[False] T \<^emph> \<half_blkcirc>[True] U \<^emph> \<half_blkcirc>[True] R) = ((y,z) \<Ztypecolon> \<half_blkcirc>[True] (U \<^emph> R)) @action \<A>merge\<close>
  unfolding Action_Tag_def
  by (clarsimp simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj)+

lemma [\<phi>reason %\<A>merge for \<open>((_,_,_) \<Ztypecolon> \<half_blkcirc>[True] _ \<^emph> \<half_blkcirc>[True] _ \<^emph> \<half_blkcirc>[_] _) = (_ \<Ztypecolon> \<half_blkcirc>[_] _) @action \<A>merge\<close>]:
  \<open>((x,y,z) \<Ztypecolon> \<half_blkcirc>[True] T \<^emph> \<half_blkcirc>[True] U \<^emph> \<half_blkcirc>[True]  R) = ((x,y,z) \<Ztypecolon> \<half_blkcirc>[True] (T \<^emph> U \<^emph> R)) @action \<A>merge\<close>
  \<open>((x,y,z) \<Ztypecolon> \<half_blkcirc>[True] T \<^emph> \<half_blkcirc>[True] U \<^emph> \<half_blkcirc>[False] R) = ((x,y) \<Ztypecolon> \<half_blkcirc>[True] (T \<^emph> U)) @action \<A>merge\<close>
  unfolding Action_Tag_def
  by (clarsimp simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj;
      metis \<phi>Prod_expn' \<phi>Some_\<phi>None_freeobj(1) \<phi>Some_\<phi>Prod fst_conv)+

lemma [\<phi>reason %\<A>merge for \<open>((_,_,_) \<Ztypecolon> \<half_blkcirc>[True] _ \<^emph> \<half_blkcirc>[True] _ \<^emph> \<half_blkcirc>[_] _) = (_ \<Ztypecolon> \<half_blkcirc>[_] _) @action \<A>merge\<close>]:
  \<open>(x3 \<Ztypecolon> \<half_blkcirc>[True] (T \<^emph> U \<^emph> R)) = ((fst x3, fst (snd x3), snd (snd x3)) \<Ztypecolon> \<half_blkcirc>[True] T \<^emph> \<half_blkcirc>[True] U \<^emph> \<half_blkcirc>[True]  R) @action \<A>merge\<close>
  \<open>(x2 \<Ztypecolon> \<half_blkcirc>[True] (T \<^emph> U)) = ((fst x2, snd x2, ()) \<Ztypecolon> \<half_blkcirc>[True] T \<^emph> \<half_blkcirc>[True] U \<^emph> \<half_blkcirc>[False] R) @action \<A>merge\<close>
  unfolding Action_Tag_def
  by (cases x3, clarsimp simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj,
      cases x2, clarsimp simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj,
      metis \<phi>Prod_expn' \<phi>Some_\<phi>None_freeobj(1) \<phi>Some_\<phi>Prod fst_conv)


(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise go \<open>SE_Semimodule_LDistr_a_cb_i\<close>*) 
lemma SE_Semimodule_LDistr_a_dbc_i
      [where Cr'=True, \<phi>reason_template %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id d + id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Dx (d + b) c (fst x)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds d \<and> Ds b \<and> d ##\<^sub>+ b \<and> Dx d b (snd (uz (d + b) c (fst x)))
\<Longrightarrow> (fst (uz d b (snd (uz (d + b) c (fst x)))), snd x) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd (uz d b (snd (uz (d + b) c (fst x)))), fst (uz (d + b) c (fst x)), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R)
      = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr and b
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some[where s=\<open>d + b\<close> and t=c and F=F1]
       apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some[where s=\<open>d\<close> and t=b and F=F1]
       Tr
       b (*simplify the abstract object during reasoning*)
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Semimodule_LDistr_da_b_i\<close> *)
lemma SE_Semimodule_LDistr_dac_b_i
      [where Cw'=True, \<phi>reason_template %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a + id c = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + a) \<and> Ds c \<and> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, x\<^sub>d) \<and> Dx (d + a) c (x\<^sub>c, z d a (fst x, x\<^sub>d))
\<Longrightarrow> (z (d + a) c (x\<^sub>c, z d a (fst x, x\<^sub>d)), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, x\<^sub>c, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P\<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some[where s=d and t=a and F=F1 and x=\<open>(fst x, x\<^sub>d)\<close>]
       apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(x\<^sub>c, z d a (fst x, x\<^sub>d))\<close>]
       Tr
  \<medium_right_bracket> .

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative separation algebra. d \<noteq> 0
   All problems on semimodules of commutative scalars (and associative separation algebra) reduces to
    \<open>SE_Semimodule_LDistr_da_b_i\<close> and \<open>SE_Semimodule_LDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_LDistr_da_b_i
      [where Cw'=True, \<phi>reason_template %derived_SE_sdistr_comm]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, x\<^sub>d)
\<Longrightarrow> (z d a (fst x, x\<^sub>d), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F1 and x=\<open>(fst x, x\<^sub>d)\<close>]
       Tr
  \<medium_right_bracket> .

(* [--------a---------]
   [-----b-----][--c--]
   Give a, expect b; Remain c, d = 0.
   c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_LDistr_a_cb_i\<close>*)
lemma SE_Semimodule_LDistr_a_bc_i
  [where Cr'=True, \<phi>reason_template %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), snd x) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd (uz b c (fst x)), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev_\<phi>Some[where t=c and s=b and F=F1]
    Tr
    b
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative separation algebra.
   d \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_LDistr_da_b_i\<close>
*)
lemma SE_Semimodule_LDistr_ad_b_i
      [where Cw' = True, \<phi>reason_template %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, x\<^sub>d)
\<Longrightarrow> (uz a d (fst x, x\<^sub>d), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev_\<phi>Some[where s=a and t=d and F=F1 and x=\<open>(fst x, x\<^sub>d)\<close>]
       Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b; Remain c, d = 0. c \<noteq> 0
   All problems on semimodules of commutative scalars (and associative separation algebra) reduces to
    \<open>SE_Semimodule_LDistr_da_b_i\<close> and \<open>SE_Semimodule_LDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_LDistr_a_cb_i[\<phi>reason_template %derived_SE_sdistr_comm]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b (fst x)
\<Longrightarrow> (fst (uz c b (fst x)), snd x) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd (uz c b (fst x)), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some[where t=b and s=c and F=F1]
    Tr
    b
  \<medium_right_bracket> .


(*Done*)

paragraph \<open>Non-Commutative, Non-Unital Associative, No Additive Zero\<close>

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to either
             \<open>SE_Semimodule_LDistr_da_b_i\<close> or \<open>SE_Semimodule_LDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_LDistr_da_nc_i
      [where Cr'=True, \<phi>reason_template %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> b ##\<^sub>+ c \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a x \<and> Dx  b c (z d a x)
\<Longrightarrow> (fst (uz b c (z d a x)), undefined) \<Ztypecolon> F1 b T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd y, snd (uz b c (z d a x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F1 c T) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close> 
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F1 and x=x]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev_\<phi>Some[where t=c and s=b and F=F1]
    Tr
    apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to either
             \<open>SE_Semimodule_LDistr_da_b_i\<close> or \<open>SE_Semimodule_LDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_LDistr_ad_cb_nc_i
      [where Cr'=True, \<phi>reason_template %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d x \<and> Dx c b (z a d x)
\<Longrightarrow> (fst (uz c b (z a d x)), undefined) \<Ztypecolon> F1 b T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd y, snd (uz c b (z a d x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F1 c T) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev_\<phi>Some[where t=d and s=a and F=F1 and x=x]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some[where t=b and s=c and F=F1]
    Tr
    apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_LDistr_da_b_i\<close>
*)
lemma SE_Semimodule_LDistr_a_dbc_nc_i
      [where Cr'=True, \<phi>reason_template %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id d + id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx' uz'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' (d + b) c (fst x) \<and> Dx d b (fst (uz' (d + b) c (fst x)))
\<Longrightarrow> (fst (uz d b (fst (uz' (d + b) c (fst x)))), ()) \<Ztypecolon> F1 b T \<^emph>[False] \<top> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd y, snd (uz d b (fst (uz' (d + b) c (fst x)))), snd (uz' (d + b) c (fst x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[True] F1 c T)
      = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[False] \<top> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises _ and _ and _ and _ and _ and _ and Tr and b
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev_\<phi>Some[where s=\<open>d + b\<close> and t=c and F=F1]
       apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_\<phi>Some[where s=\<open>d\<close> and t=b and F=F1]
       Tr
       apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_LDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_LDistr_dac_b_nc_i
      [\<phi>reason_template %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a + id c = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx' z'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds (d + a) \<and> Ds c \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, fst (snd x)) \<and> Dx' (d + a) c (z d a (fst x, fst (snd x)), snd (snd x))
\<Longrightarrow> (z' (d + a) c (z d a (fst x, fst (snd x)), snd (snd x)), ()) \<Ztypecolon> F1 b T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] (F1 d T \<^emph> F1 c T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    note \<phi>Some_\<phi>Prod[symmetric, simp]
    ;; apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_\<phi>Some[where s=d and t=a and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
       apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev_\<phi>Some[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(z d a (fst x, fst (snd x)), snd (snd x))\<close>]
       Tr
  \<medium_right_bracket> .

(*DONE*)

(*
paragraph \<open>Non-Associative\<close>

subparagraph \<open>Assuming no algebraic property, allowing no further demand in the element transformation\<close>

text \<open>Has Additive Zero\<close>

text \<open>
\<open>[--d--][--a--][--c--]
 [---------b---------]
 Give a, expect b, demand d, c. \<close>

There is no way to apply such splitting as it requires two steps of splitting anyway,
  and results in \<open>R\<^sub>1 * (R\<^sub>2 * Target)\<close> where \<open>R\<^sub>1\<close> and \<open>R\<^sub>2\<close> are the remainders of the two splittings,
  and due to the absence of associativity, we cannot convert it to \<open>R\<^sub>1 * R\<^sub>2 * Target\<close> to move the Target
  out to enable the element transformation.

If we really want this rule, we have to introduce an algebraic class for a single step splitting
merging the two steps. However, does it really deserves? I don't think so as there is rare usage
for non-associative algebras (I cannot imagine any).
\<close>

text \<open>No Additive Zero\<close>

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0.
*)
lemma SE_Semimodule_LDistr_da_b_na[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a x
\<Longrightarrow> z d a x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=x]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0.
*)
lemma SE_Semimodule_LDistr_ad_b_na[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d x
\<Longrightarrow> uz a d x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev[where s=a and t=d and F=F1 and x=x]
    Tr
  \<medium_right_bracket> .


subparagraph \<open>Assuming associativity, allowing further demand in the element transformation\<close>

text \<open>Has Additive Zero\<close>

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c. *)
lemma SE_Semimodule_LDistr_dac_b_nc_na_W[\<phi>reason_template 38]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + a) \<and> Ds c \<and> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, fst (snd x)) \<and> Dx (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x)))
\<Longrightarrow> (z (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x))), snd (snd (snd x))) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> F1 c T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket>  premises [simp] and _ and _ and _ and _ and Tr
     apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where s=d and t=a and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
     apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(fst (snd (snd x)), z d a (fst x, fst (snd x)))\<close>]
     Tr
  \<medium_right_bracket> .


text \<open>No Additive Zero\<close>

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0. *)
lemma SE_Semimodule_LDistr_da_b_na_W[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, fst (snd x))
\<Longrightarrow> (z d a (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0. *)
lemma SE_Semimodule_LDistr_ad_b_na_W[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, fst (snd x))
\<Longrightarrow> (uz a d (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev[where s=a and t=d and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .
*)

paragraph \<open>Assuming no algebraic property supporting even non-associative group,
  and as a consequence allowing no remainder and subsequent target in the element transformation\<close>

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b, remain d. c \<noteq> 0
*)
lemma SE_Semimodule_LDistr_a_cb_noassoc[\<phi>reason_template %derived_SE_sdistr_noassoc]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b (fst x)
\<Longrightarrow> fst (uz c b (fst x)) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, snd (uz c b (fst x))) \<Ztypecolon> F3 b U \<^emph>[True] F1 c T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where s=\<open>c\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
   d \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Semimodule_LDistr_a_cb_noassoc\<close>
*)
lemma SE_Semimodule_LDistr_a_bd_Tr
      [\<phi>reason_template %derived_SE_sdistr_noassoc pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id b + id d @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> b ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b d (fst x)
\<Longrightarrow> fst (uz b d (fst x)) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz b d (fst x)) \<Ztypecolon> F1 d T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where s=\<open>b\<close> and t=d and F=F1]
    Tr
  \<medium_right_bracket> .

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b, remain d. c \<noteq> 0
*)
lemma SE_Semimodule_LDistr_da_b_noassoc[\<phi>reason_template %derived_SE_sdistr_noassoc]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a x
\<Longrightarrow> z d a x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, undefined) \<Ztypecolon> F3 b U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z[where s=\<open>d\<close> and t=a and F=F1]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [---------b--------]
   Give a, expect b, remain d.
   d \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Semimodule_LDistr_da_b_noassoc\<close>
*)
lemma SE_Semimodule_LDistr_ad_b_noassoc
      [\<phi>reason_template %derived_SE_sdistr_noassoc pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>Z_rev F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d x
\<Longrightarrow> z a d x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, undefined) \<Ztypecolon> F3 b U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>Z_rev[where s=\<open>a\<close> and t=d and F=F1]
    Tr
  \<medium_right_bracket> .

(*
subsubsection \<open>Transformation of Semimodule Left Distributivity\<close>

paragraph \<open>Assuming no algebraic property supporting even non-associative group,
  and as a consequence allowing no remainder in the element transformation\<close>

subparagraph \<open>Has Additive Zero\<close>

text \<open>
\<open>[---------a---------]
 [--d--][--b--][--c--]
 Give a, expect b, remain d, c. \<close>

There is no way to apply such splitting as it requires two steps of splitting anyway,
  and results in \<open>R\<^sub>1 * (R\<^sub>2 * Target)\<close> where \<open>R\<^sub>1\<close> and \<open>R\<^sub>2\<close> are the remainders of the two splittings,
  and due to the absence of associativity, we cannot convert it to \<open>R\<^sub>1 * R\<^sub>2 * Target\<close> to move the Target
  out to enable the element transformation.

If we really want this rule, we have to introduce an algebraic class for a single step splitting
merging the two steps. However, does it really deserves? I don't think so as there is rare usage
for non-associative algebras (I cannot imagine any).
\<close>

subparagraph \<open>No Additive Zero\<close>

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b, remain d.
*)
lemma SE_Semimodule_LDistr_a_db_Tr[\<phi>reason_template %derived_SE_sdistr_noassoc]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b x
\<Longrightarrow> fst (uz c b x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz c b x) \<Ztypecolon> F1 c T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where s=\<open>c\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
*)
lemma SE_Semimodule_LDistr_a_bd_Tr[\<phi>reason_template %derived_SE_sdistr_noassoc]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + d @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> b ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b d x
\<Longrightarrow> fst (uz b d x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz b d x) \<Ztypecolon> F1 d T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where s=\<open>b\<close> and t=d and F=F1]
    Tr
  \<medium_right_bracket> .

paragraph \<open>Assuming associativity, allowing remainders\<close>

subparagraph \<open>Has Additive Zero\<close>

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma SE_Semimodule_LDistr_a_dbc_Tr_R[\<phi>reason_template 33]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx' uz'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' (d + b) c x \<and> Dx d b (fst (uz' (d + b) c x))
\<Longrightarrow> fst (uz d b (fst (uz' (d + b) c x))) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> if C then R' = (snd (uz' (d + b) c x) \<Ztypecolon> F1 c T) * (snd (uz d b (fst (uz' (d + b) c x))) \<Ztypecolon> F1 d T) * R
         else R' = (snd (uz' (d + b) c x) \<Ztypecolon> F1 c T) * (snd (uz d b (fst (uz' (d + b) c x))) \<Ztypecolon> F1 d T)
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>'c::sep_ab_semigroup set\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and _ and Tr and C
    have C': \<open>(if C then (snd (uz' (d + b) c x) \<Ztypecolon> F1 c T) * (snd (uz d b (fst (uz' (d + b) c x))) \<Ztypecolon> F1 d T) * R
                    else (snd (uz' (d + b) c x) \<Ztypecolon> F1 c T) * (snd (uz d b (fst (uz' (d + b) c x))) \<Ztypecolon> F1 d T)) = R'\<close>
      using C by (cases C; simp) ;;
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where s=\<open>d + b\<close> and t=c and F=F1, folded a]
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

subparagraph \<open>No Additive Zero\<close>

(* [---------a--------]
   [--d--][-----b-----]
   Give a, expect b, remain d.
   Assuming associativity, allow R
*)
lemma SE_Semimodule_LDistr_a_db_Tr_R[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d b x
\<Longrightarrow> fst (uz d b x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> if C then R' = (snd (uz d b x) \<Ztypecolon> F1 d T) * R else R' = (snd (uz d b x) \<Ztypecolon> F1 d T)
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>'c::sep_semigroup set\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and C
    have C': \<open>(if C then (snd (uz d b x) \<Ztypecolon> F1 d T) * R else (snd (uz d b x) \<Ztypecolon> F1 d T)) = R'\<close>
      using C by (cases C; simp) ;;
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
   Assuming associativity, allow R
*)
lemma SE_Semimodule_LDistr_a_bd_Tr_R[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + d @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_LDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> b ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b d x
\<Longrightarrow> fst (uz b d x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> if C then R' = (snd (uz b d x) \<Ztypecolon> F1 d T) * R else R' = (snd (uz b d x) \<Ztypecolon> F1 d T)
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>'c::sep_semigroup set\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and C
    have C': \<open>(if C then (snd (uz b d x) \<Ztypecolon> F1 d T) * R else (snd (uz b d x) \<Ztypecolon> F1 d T)) = R'\<close>
      using C by (cases C; simp) ;;
    apply_rule apply_Semimodule_LDistr_Homo\<^sub>U_rev[where s=\<open>b\<close> and t=d and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

(*DONE*)

(*The dual of the above rules is \<A>SEa*)
*)

subsection \<open>Property Derivers\<close>

subsubsection \<open>Extension of BNF-FP\<close>

ML_file \<open>library/phi_type_algebra/tools/BNF_fp_sugar_more.ML\<close>
ML_file \<open>library/phi_type_algebra/tools/extended_BNF_info.ML\<close>


subsubsection \<open>Extending the Guessing of Property\<close>
  \<comment> \<open>A general mechanism to provide user heuristics which guesses the entire property
      of some specific forms of \<phi>-types\<close>

text \<open>When guessing the property, the system first tries to see if there is any user overridings
  by \<open>Guess_Property\<close> reasoning which gives the desired property entirely, if not, it goes to the normal
  guesser procedure implemented by each deriver, and after obtaining the guessed property,
  the system runs the \<open>Guess_Property\<close> again with the \<open>guessed_conclusion\<close> setting to None to force
  guessing the antecedents only, in this way to refine the already guessed antecedent either by
  adding new antecedents or constraining the antecedents by conditions.\<close>

type_synonym variant = bool \<comment>\<open>True for covariant, False for contravariant, undefined for invariant\<close>

definition Guess_Property :: \<open>'property_const \<Rightarrow> variant \<Rightarrow> 'a BI \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool option \<Rightarrow> bool\<close>
  where \<open>Guess_Property the_constant_of_the_property_predicate
                        variantness_of_the_property
                        unfolded_\<phi>type_definition
                        guessed_antecedents
                        conditions_of_antecedents
                        guessed_conclusion \<comment> \<open>None for the mode guessing antecedents only\<close>
          \<equiv> True\<close>

declare [[
  \<phi>reason_default_pattern \<open>Guess_Property ?PC ?V ?A _ _ _\<close> \<Rightarrow> \<open>Guess_Property ?PC ?V ?A _ _ _\<close> (100)
                      and \<open>Guess_Property ?PC ?V ?A _ _ (Some _)\<close> \<Rightarrow> \<open>Guess_Property ?PC ?V ?A _ _ (Some _)\<close> (120)
                      and \<open>Guess_Property ?PC ?V ?A _ _ None\<close> \<Rightarrow> \<open>Guess_Property ?PC ?V ?A _ _ None\<close> (120)
]]

\<phi>reasoner_group \<phi>TA_guesser = (100, [40, 3000]) for \<open>Guess_Property PC V A a c C\<close>
    \<open>User heuristics overriding or extending the guesser mechanism of \<phi>type derivers.\<close>
 and \<phi>TA_guesser_default = (20, [2, 39]) for \<open>Guess_Property PC V A a c C\<close> < \<phi>TA_guesser
    \<open>Default rules handling logical connectives, basically using variantness to guess\<close>
 and \<phi>TA_guesser_assigning_variant = (2200, [2200,2200]) for \<open>Guess_Property PC V A a c C\<close>
                                                          in \<phi>TA_guesser and > \<phi>TA_guesser_default
    \<open>Fallbacks using common default rules\<close>
 and \<phi>TA_guesser_fallback = (1,[1,1]) for \<open>Guess_Property PC V A a c C\<close> < \<phi>TA_guesser_default
    \<open>Fallbacks of Guess_Property\<close>

ML_file \<open>library/phi_type_algebra/guess_property.ML\<close>


paragraph \<open>Rules Setting Variantness\<close>

lemma Is_Covariant:
  \<open> Guess_Property PC True A a p C
\<Longrightarrow> Guess_Property PC var_v A a p C \<close>
  unfolding Guess_Property_def ..

lemma Is_Contravariant:
  \<open> Guess_Property PC False A a p C
\<Longrightarrow> Guess_Property PC var_v A a p C \<close>
  unfolding Guess_Property_def ..

lemma Is_Invariant:
  \<open> Guess_Property PC undefined A a p C
\<Longrightarrow> Guess_Property PC var_v A a p C \<close>
  unfolding Guess_Property_def ..

paragraph \<open>Preset\<close>

lemma [\<phi>reason default %\<phi>TA_guesser_fallback]:
  \<open>Guess_Property PC V A True True None\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser_default]:
  \<open> Guess_Property PC False A a p C
\<Longrightarrow> Guess_Property PC False (A \<s>\<u>\<b>\<j> P) a ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P) \<and>\<^sub>\<r> p) C \<close>
  \<open> (\<And>x. Guess_Property PC False (A' x) (a' x) (c' x) C)
\<Longrightarrow> Guess_Property PC False (ExSet A') (All a') (Ex c') C\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser_default]:
  \<open> Guess_Property PC True A a p C
\<Longrightarrow> Guess_Property PC True (A \<s>\<u>\<b>\<j> P) ((\<p>\<r>\<e>\<m>\<i>\<s>\<e> P) \<and>\<^sub>\<r> a) p C \<close>
  \<open> (\<And>x. Guess_Property PC True (A' x) (a' x) (c' x) C)
\<Longrightarrow> Guess_Property PC True (ExSet A') (Ex a') (All c') C \<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open> Guess_Property PC undefined A a c C
\<Longrightarrow> Guess_Property PC undefined (A \<s>\<u>\<b>\<j> P) a c C\<close>
  \<open> (\<And>x. Guess_Property PC undefined (A' x) a c C)
\<Longrightarrow> Guess_Property PC undefined (ExSet A') a c C\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open> Guess_Property PC V A a1 c1 None
\<Longrightarrow> Guess_Property PC V B a2 c2 None
\<Longrightarrow> Guess_Property PC V (A * B) (a1 \<and>\<^sub>\<r> a2) (c1 \<and>\<^sub>\<r> c2) None\<close>
  unfolding Guess_Property_def ..




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
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> Q
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> Q \<and> P\<close>
  unfolding REMAINS_def
  by (cases C; simp add: implies_left_frame transformation_trans)

lemma [fundef_cong]:
  \<open>T x = T' x' \<Longrightarrow> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')\<close>
  unfolding \<phi>Type_def by simp

lemma \<phi>TA_common_rewr_imp1:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_ind_target A) \<equiv> (Ant \<Longrightarrow> X @action A) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp1_noact:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_ind_target A) \<equiv> (Ant \<Longrightarrow> X) \<close>
  unfolding Action_Tag_def atomize_imp .

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

\<phi>property_deriver Warn_if_contains_Sat 10 = \<open>fn quiet => fn [] => fn _ => fn phi => fn thy => (
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


subsubsection \<open>Abstract Domain\<close>

lemma \<phi>TA_Inh\<^sub>M\<^sub>C_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow> Inhabited\<^sub>M\<^sub>C (x \<Ztypecolon> T) \<longrightarrow> P x @action \<phi>TA_ind_target \<A>EIF)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Abstract_Domain\<^sub>M\<^sub>C T P\<close>
  unfolding Action_Tag_def Abstract_Domain\<^sub>M\<^sub>C_def
  by simp

lemma \<phi>TA_SuC\<^sub>M\<^sub>C_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow> P x \<longrightarrow> Inhabited\<^sub>M\<^sub>C (x \<Ztypecolon> T) @action \<phi>TA_ind_target \<A>ESC)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Abstract_Domain\<^sub>M\<^sub>C\<^sub>L T P\<close>
  unfolding Action_Tag_def Abstract_Domain\<^sub>M\<^sub>C\<^sub>L_def
  by simp

lemma \<phi>TA_Inh\<^sub>M\<^sub>C_extract_prem:
  \<open>x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C P \<equiv> ((\<exists>v. v \<Turnstile> (x \<Ztypecolon> T) \<and> mul_carrier v) \<longrightarrow> P) \<and> (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s>\<^sub>M\<^sub>C P)\<close>
  unfolding Action_Tag_def Inhabited\<^sub>M\<^sub>C_def atomize_eq
  by blast


ML_file \<open>library/phi_type_algebra/implication.ML\<close>

(*hide_fact \<phi>TA_Inh_rule \<phi>TA_Inh_rewr \<phi>TA_Inh_step*)


\<phi>property_deriver Abstract_Domain\<^sub>L 89 for ( \<open>Abstract_Domain\<^sub>L _ _\<close> ) = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain_L
\<close>

\<phi>property_deriver Abstract_Domain 90 for ( \<open>Abstract_Domain _ _\<close> ) requires Abstract_Domain\<^sub>L ? = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain
\<close>

\<phi>property_deriver Abstract_Domain\<^sub>M\<^sub>C\<^sub>L 89 for ( \<open>Abstract_Domain\<^sub>M\<^sub>C\<^sub>L _ _\<close> ) = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain_MCL
\<close>

\<phi>property_deriver Abstract_Domain\<^sub>M\<^sub>C 90 for ( \<open>Abstract_Domain\<^sub>M\<^sub>C _ _\<close> ) requires Abstract_Domain\<^sub>M\<^sub>C\<^sub>L ? = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain_MC
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

paragraph \<open>Guessing Antecedents\<close>

declare Is_Contravariant[where PC=\<open>Identity_Element\<^sub>I\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]
        Is_Covariant[where PC=\<open>Identity_Element\<^sub>E\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]

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
\<equiv> (\<And>A R C. Ant \<Longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) &&& (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R))\<close>
  unfolding Action_Tag_def atomize_imp atomize_all atomize_conj Transformation_def REMAINS_def
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


subsubsection \<open>Functionality\<close>

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
  \<open> Trueprop (Ant \<longrightarrow> cond \<longrightarrow> P @action Any)
 \<equiv> (Ant \<Longrightarrow> cond \<Longrightarrow> P) \<close>
  unfolding Action_Tag_def Is_Functional_def Premise_def atomize_imp .

(*
lemma \<phi>TA_IsFunc_rewr_ants:
  \<open>Is_Functional S \<equiv> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>u v. u \<Turnstile> S \<and> v \<Turnstile> S \<longrightarrow> u = v)\<close>
  unfolding Premise_def Is_Functional_def by simp*)

ML_file \<open>library/phi_type_algebra/is_functional.ML\<close>

\<phi>property_deriver Functionality 100 for (\<open>Functionality _ _\<close>)
    = \<open> Phi_Type_Algebra_Derivers.is_functional \<close>


subsubsection \<open>Carrier Set\<close>

bundle extract_premises_in_Carrier_Set =
  prem_extract_Carrier_Set[\<phi>premise_extraction]
  prem_extract_homo_mul_carrier[\<phi>premise_extraction]


lemma \<phi>TA_CarS_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> P x \<longrightarrow>
          Within_Carrier_Set (x \<Ztypecolon> T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Carrier_Set T P \<close>
  unfolding Carrier_Set_def Action_Tag_def Premise_def
  by clarsimp

lemma \<phi>TA_CarS_rewr:
  \<open> Trueprop (Ant \<longrightarrow> cond \<longrightarrow> P @action Any)
 \<equiv> (Ant \<Longrightarrow> cond \<Longrightarrow> P) \<close>
  unfolding Action_Tag_def Is_Functional_def Premise_def atomize_imp .

ML_file \<open>library/phi_type_algebra/carrier_set.ML\<close>

\<phi>property_deriver Carrier_Set 100 for (\<open>Carrier_Set _ _\<close>)
    = \<open> Phi_Type_Algebra_Derivers.carrier_set \<close>

\<phi>property_deriver Basic 109
  requires Object_Equiv and Abstract_Domain and Carrier_Set ?

declare Is_Contravariant[where PC=\<open>Carrier_Set\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]


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
\<Longrightarrow> (Ant @action \<phi>TA_ANT \<Longrightarrow> Prem \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>f P a' b'. mapper (\<lambda>a b. b = f a \<and> P a) a' b' \<longrightarrow> b' = fm f P a' \<and> pm f P a'))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Functional_Transformation_Functor F1 F2 D R mapper Prem pm fm\<close>
  unfolding Functional_Transformation_Functor_def Premise_def fun_eq_iff
            Functional_Transformation_Functor_axioms_def Transformation_Functor_L_def
            Action_Tag_def
  by blast

lemma [\<phi>reason %\<phi>TA_guesser[top]]:
  \<comment> \<open>Guess_Property in Functional_Transformation_Functor is prohibited\<close>
  \<open> False
\<Longrightarrow> Guess_Property Functional_Transformation_Functor V Any True True (Some C)\<close>
  \<open>Guess_Property Functional_Transformation_Functor V Any True True None\<close>
  unfolding Guess_Property_def
  by simp_all

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
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Transformation_Functor F F' D R M)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Transformation_Functor F' F D' R' M')
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x \<subseteq> R x \<and> (\<forall>x y. M (=) x y \<longrightarrow> x = y) \<and> (\<forall>x. D x = D' x) \<and>
            D y \<subseteq> R' y \<and> (\<forall>x y. M' (=) x y \<longrightarrow> x = y)
\<Longrightarrow> \<r>Success
\<Longrightarrow> eqs
\<Longrightarrow> x = y
\<Longrightarrow> (\<And>a \<in> D y. T a = U a)
\<Longrightarrow> F T x = F' U y \<close>
  unfolding fun_eq_iff[symmetric, where f=D]
  unfolding Transformation_Functor_def Premise_def Transformation_def \<phi>Type_def BI_eq_iff
            subset_iff meta_Ball_def Ball_def
  apply clarify
  subgoal premises prems for u
    by (insert prems(1)[THEN spec[where x=T], THEN spec[where x=U], THEN spec[where x=y], THEN spec[where x=\<open>(=)\<close>]]
               prems(2)[THEN spec[where x=U], THEN spec[where x=T], THEN spec[where x=y], THEN spec[where x=\<open>(=)\<close>]]
               prems(4-);
        clarsimp; rule; blast) .
  
ML_file \<open>library/phi_type_algebra/function_congruence.ML\<close>


subsubsection \<open>Semimodule Scalar Zero\<close>

lemma \<phi>TA_M0_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> F 0 T) True @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Semimodule_Zero F T \<close>
  unfolding Semimodule_Zero_def Action_Tag_def Premise_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
  by (clarsimp simp add: BI_eq_iff Transformation_def; blast)


lemma \<phi>TA_M0c_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> F 0 T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> Semimodule_Zero F T
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Closed_Semimodule_Zero F T \<close>
  unfolding Semimodule_Zero_def Action_Tag_def Premise_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
            Closed_Semimodule_Zero_def
  by (clarsimp simp add: BI_eq_iff Transformation_def; blast)

lemma \<phi>TA_M0_rewr:
  \<open> Trueprop (Ant \<longrightarrow> Q @action \<phi>TA_ind_target Any) \<equiv> (Ant \<Longrightarrow> Q)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_zero.ML\<close>

\<phi>property_deriver Semimodule_Zero 129 for (\<open>Semimodule_Zero _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_zero\<close>

\<phi>property_deriver Closed_Semimodule_Zero 130
    for (\<open>Closed_Semimodule_Zero _ _\<close>) requires Semimodule_Zero
    = \<open>Phi_Type_Algebra_Derivers.closed_semimodule_zero\<close>



subsubsection \<open>Semimodule Scalar Identity\<close>

lemma \<phi>TA_MI_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> (x \<Ztypecolon> F 1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F 1 T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Semimodule_Identity F T \<close>
  unfolding Semimodule_Identity_def Action_Tag_def Premise_def
  by (clarsimp; rule \<phi>Type_eqI_Tr; blast)

lemma \<phi>TA_MI_rewr:
  \<open> Trueprop (Ant \<longrightarrow> Q @action \<phi>TA_ind_target \<A>) \<equiv> (Ant \<Longrightarrow> Q @action \<A>)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_identity.ML\<close>

\<phi>property_deriver Semimodule_Identity 130 for (\<open>Semimodule_Identity _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_identity\<close>


subsubsection \<open>Configuration for guessing default Semimodule properties\<close>


definition guess_domain_of_scalar :: \<open>'s itself \<Rightarrow> 'c itself \<Rightarrow> 'a itself \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>guess_domain_of_scalar _ _ _ _ \<equiv> True\<close>
  \<comment> \<open>indicating the default domain of the scalar of the given types, used as the default guess in derivers\<close>

definition guess_zip_of_semimodule :: \<open>'s itself \<Rightarrow> 'c itself \<Rightarrow> 'a itself
                                      \<Rightarrow> ('s \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times>'a \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                      \<Rightarrow> bool\<close>
  where \<open>guess_zip_of_semimodule type_scalar type_concrete type_abstract
                                 domain_of_scalar domain_of_abstract
                                 zip_opr
       \<equiv> True\<close>



declare [[
  \<phi>reason_default_pattern \<open>guess_domain_of_scalar ?S ?C ?A _\<close> \<Rightarrow> \<open>guess_domain_of_scalar ?S ?C ?A _\<close> (100)
                      and \<open>guess_zip_of_semimodule ?S ?C ?A _ _ _\<close> \<Rightarrow> \<open>guess_zip_of_semimodule ?S ?C ?A _ _ _\<close> (100)
]]

text \<open>To guess the zip operation of a semimodule is far beyond what can be inferred from BNF,
      partially because a semimodule is over two algebraic sorts (i.e., two logical types).
      Due to this, the guessing of the abstract operators of semimodules more relies on pre-registered
      records over the logical types.\<close>

lemma [\<phi>reason %guess_algebraic_oprs_cut]:
  \<open>guess_domain_of_scalar TYPE(rat) TYPE('c::share) TYPE('a) (\<lambda>x. 0 < x)\<close>
  unfolding guess_domain_of_scalar_def ..

lemma [\<phi>reason %guess_algebraic_oprs_cut+10]:
  \<open>guess_domain_of_scalar TYPE(rat) TYPE('c::share_one) TYPE('a) (\<lambda>x. 0 \<le> x)\<close>
  unfolding guess_domain_of_scalar_def ..

lemma [\<phi>reason %guess_algebraic_oprs_cut]:
  \<open>guess_domain_of_scalar TYPE(nat lcro_interval) TYPE('c) TYPE('a list) (\<lambda>_. True)\<close>
  unfolding guess_domain_of_scalar_def ..

lemma [\<phi>reason %guess_algebraic_oprs_cut]:
  \<open>guess_zip_of_semimodule TYPE(rat) TYPE('c) TYPE('a) (\<lambda>x. 0 \<le> x) (\<lambda>s t (x,y). x = y) (\<lambda>_ _ (x,y). x)\<close>
  unfolding guess_zip_of_semimodule_def ..

lemma [\<phi>reason %guess_algebraic_oprs_cut]:
  \<open>guess_zip_of_semimodule TYPE(nat lcro_interval) TYPE('c) TYPE('a list) (\<lambda>_. True)
                           (\<lambda>s t (x,y). LCRO_Interval.width_of t = length x \<and> LCRO_Interval.width_of s = length y)
                           (\<lambda>_ _ (x,y). y * x)\<close>
  unfolding guess_zip_of_semimodule_def ..




subsubsection \<open>Semimodule Scalar Associative\<close>

text \<open>\<phi>-type embedding of separation quantifier \<open>x \<Ztypecolon> \<big_ast>[i\<in>I] T\<close> is a recursive example of this.

  The induction of the \<phi>-type should expand the scalar as the scalar usually represents the domain of the \<phi>-type abstraction. 
\<close>

lemma \<phi>TA_MS_rule:
  \<open> (\<And>t s r x. (Ant @action \<phi>TA_ANT)
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Ds t \<and> r = t * s
         \<longrightarrow> (x \<Ztypecolon> F s (F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F r T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>t s x. (Ant @action \<phi>TA_ANT)
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Ds t
         \<longrightarrow> (x \<Ztypecolon> F (t * s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F s (F t T)) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Semimodule_Scalar_Assoc F T Ds \<close>
  unfolding Semimodule_Scalar_Assoc_def Action_Tag_def Premise_def
  by (clarsimp; rule \<phi>Type_eqI_Tr; blast)

lemma \<phi>TA_MS_rewr:
  \<open> Trueprop (Ant \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<longrightarrow> Q @action \<phi>TA_ind_target \<A>) \<equiv> (Ant \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Q @action \<A>)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_scalar.ML\<close>

\<phi>property_deriver Semimodule_Scalar_Assoc 130 for (\<open>Semimodule_Scalar_Assoc _ _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_scalar\<close>


subsubsection \<open>Semimodule Scalar Distributivity - Zip\<close>

text \<open>Essentially the rules are derived from that of existing \<phi>-types, and the initial rules
  are those from logical connectivities, function embedding \<open>\<phi>Fun\<close> into \<phi>-types and vertical
  composition \<open>\<phi>Composition\<close>. 

TODO: move me!
\<close>

lemma \<phi>TA_MD_rule:
  \<open> (\<And>s t x r z. (Ant @action \<phi>TA_ANT)
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Ds t \<and> s ##\<^sub>+ t
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> r = s + t \<and> Dx s t x \<and> zi s t x = z
         \<longrightarrow> (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> F r T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Semimodule_LDistr_Homo\<^sub>Z F T Ds Dx zi \<close>
  unfolding Semimodule_LDistr_Homo\<^sub>Z_def Action_Tag_def Premise_def Transformation_def
  by clarsimp blast

lemma \<phi>TA_MD_rewr:
  \<open> Trueprop (Ant \<longrightarrow> P1 \<longrightarrow> P2 \<longrightarrow> Q @action \<phi>TA_ind_target \<A>)
 \<equiv> (Ant \<Longrightarrow> P1 \<Longrightarrow> P2 \<Longrightarrow> Q @action \<A>)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_distrib_zip.ML\<close>

\<phi>property_deriver Semimodule_LDistr_Homo\<^sub>Z 130 for (\<open>Semimodule_LDistr_Homo\<^sub>Z _ _ _ _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_distrib_zip\<close>

declare Is_Invariant[where PC=\<open>Semimodule_LDistr_Homo\<^sub>Z\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]


subsubsection \<open>Separation Homo\<close>

lemma \<phi>TA_SH\<^sub>I_rule:
  \<open> (\<And>z. (Ant @action \<phi>TA_ANT) \<longrightarrow>
            (\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z
                \<longrightarrow> ((y \<Ztypecolon> Fb U) * (x \<Ztypecolon> Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Fc (T \<^emph> U))) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Separation_Homo\<^sub>I Fa Fb Fc T U D w \<close>
  unfolding Separation_Homo\<^sub>I_def \<phi>Prod_expn' Action_Tag_def
  by simp

lemma \<phi>TA_SH\<^sub>E_rule:
  \<open> (\<And>z. (Ant @action \<phi>TA_ANT) \<longrightarrow>
             (z \<Ztypecolon> Fc (T \<^emph>\<^sub>\<A> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz z \<Ztypecolon> Ft T \<^emph>\<^sub>\<A> Fu U) @action \<phi>TA_ind_target \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U uz \<close>
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

\<phi>property_deriver Separation_Homo\<^sub>I 120 for (\<open>Separation_Homo\<^sub>I _ _ _ _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.separation_homo_I
\<close>

\<phi>property_deriver Separation_Homo\<^sub>E 121 for (\<open>Separation_Homo\<^sub>E _ _ _ _ _ _\<close>) = \<open>
  Phi_Type_Algebra_Derivers.separation_homo_E
\<close>

\<phi>property_deriver Separation_Homo 122 requires Separation_Homo\<^sub>I and Separation_Homo\<^sub>E

\<phi>property_deriver Separation_Monoid 130
  requires Separation_Homo
       and Functional_Transformation_Functor
       and Identity_Element
       and Basic


subsubsection \<open>Construct Abstraction from Concrete Representation (by Itself)\<close>

lemma \<phi>TA_TrCstr_rule:
  \<open> (Ant @action \<phi>TA_ANT) \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A) @action \<phi>TA_ind_target undefined
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<close>
  unfolding Action_Tag_def
  by simp

ML_file \<open>library/phi_type_algebra/constr_abst_weak.ML\<close>

(*
lemma \<phi>TA_TrCstr_rule:
  \<open> (\<And>c x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
         \<p>\<r>\<e>\<m>\<i>\<s>\<e> P c \<and> x = f c \<longrightarrow>
         (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE_from_RAW T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> \<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> P c \<longrightarrow> MAKE_from_RAW c ()(c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f c \<Ztypecolon> MAKE_from_RAW T) \<close>
  \<comment> \<open>If one concrete representation is related to multiple abstract objects, just choose any one
      that is most representative.\<close>
  unfolding Action_Tag_def
  by simp

ML_file \<open>library/phi_type_algebra/constr_abst.ML\<close>
*)
\<phi>property_deriver Construct_Abstraction_from_Raw 130
  for ( \<open>\<forall>x. Premise _ _ \<longrightarrow> (x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?f x \<Ztypecolon> ?T)\<close>
      | \<open>Premise _ _ \<longrightarrow> (?x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T)\<close>
      | \<open>\<forall>x. x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?f x \<Ztypecolon> ?T\<close>
      | \<open>?x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T\<close> )
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Algebra_Derivers.construct_abstraction_from_raw \<close>


subsubsection \<open>Destruct Abstraction down to Concrete Representation (by Itself)\<close>

lemma \<phi>TA_TrRA_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
         (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_ind_target (to (Itself::('b,'b) \<phi>)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> \<forall>x. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y::'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to (Itself::('b,'b) \<phi>)) \<close>
  unfolding Action_Tag_def
  by simp

ML_file \<open>library/phi_type_algebra/open_all_abstraction.ML\<close>

\<phi>property_deriver Open_Abstraction_Full 130 for ( \<open>\<forall>x. (x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself)\<close>
                                                | \<open>\<forall>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself\<close>
                                                | \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r' y @action to Itself\<close>)
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Algebra_Derivers.open_all_abstraction \<close>




subsubsection \<open>Trim Empty Generated during Separation Extraction\<close>

(*TODO: reform.*)

text \<open>For a type operator \<open>F\<close>, SE_Trim_Empty generates rules that eliminates into \<open>\<circle>\<close>
  any \<open>F \<circle>\<close> generated during Separation Extraction process.

  This elimination is derived from \<open>Identity_Element\<close>. If the elimination rule is condition-less
  (demand no conditional premise nor reasoner subgoals), the rule is activated automatically.
  But if there are conditions, the system needs user's discretion to decide if to activate it.
  If so, activate deriver \<open>SE_Trim_Empty\<close>.
\<close>

lemma [\<phi>reason_template name \<phi>None [assertion_simps, simp]]:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>I (yy \<Ztypecolon> F \<circle>) Any @action \<A>_template_reason
\<Longrightarrow> Identity_Element\<^sub>E (u \<Ztypecolon> F \<circle>) @action \<A>_template_reason
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> NO_SIMP (F \<circle> = \<circle>) \<close>
  unfolding Object_Equiv_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def NO_SIMP_def Action_Tag_def
  by (rule \<phi>Type_eqI_Tr; clarsimp simp add: transformation_weaken)


lemma derive_\<A>SE_trim_I:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>I (yy \<Ztypecolon> F \<circle>) P
\<Longrightarrow> Object_Equiv (F \<circle>) eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd y) yy
\<Longrightarrow> \<A>SE_trim\<^sub>I y (F \<circle>) (fst y, ()) \<circle> P \<close>
  unfolding \<A>SE_trim\<^sub>I_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>I_def]
    apply_rule R1[THEN implies_right_frame]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_I_TH:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>I (yy \<Ztypecolon> F \<circle>) P
\<Longrightarrow> Object_Equiv (F \<circle>) eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd y) yy
\<Longrightarrow> \<A>SE_trim\<^sub>I_TH y (F \<circle>) (fst y, ()) \<circle> P \<circle> (F' \<circle>) \<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  \<medium_left_bracket> premises _ and  R1[unfolded Identity_Element\<^sub>I_def]
    apply_rule R1[THEN implies_right_frame]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_E:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>E (u \<Ztypecolon> F \<circle>)
\<Longrightarrow> \<A>SE_trim\<^sub>E (fst x', u) (F \<circle>) x' \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>E_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>E_def]
    apply_rule R1[THEN implies_right_frame]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_E_TH:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>E (u \<Ztypecolon> F \<circle>)
\<Longrightarrow> \<A>SE_trim\<^sub>E_TH (fst x', u) (F \<circle>) x' \<circle> \<circle> (F' \<circle>) \<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>E_def]
    apply_rule R1[THEN implies_right_frame]
  \<medium_right_bracket> .


ML_file \<open>library/phi_type_algebra/SE_Trim_Empty.ML\<close>

\<phi>property_deriver SE_Trim_Empty 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.SE_Trim_Empty quiet) \<close>

lemmas [\<phi>reason_template default 40 pass: \<open>(Phi_Type_Algebra_Derivers.SE_Trim_Empty__generation_pass, K I)\<close>] =
          derive_\<A>SE_trim_I derive_\<A>SE_trim_I_TH
          derive_\<A>SE_trim_E derive_\<A>SE_trim_E_TH




subsection \<open>Deriving Configures for Specific Abstract Algebras\<close>

subsubsection \<open>Common\<close>

setup \<open>Context.theory_map (Phi_Type_Algebra_Derivers.Expansion.map (fn ctxt => ctxt addsimps
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

(*definition \<open>zip_set = case_prod (\<times>)\<close>
definition \<open>unzip_set s = (Domain s, Range s)\<close> *)

lemma rel_set__const_True[simp]:
  \<open>rel_set (\<lambda>x y. True) = (\<lambda>x y. x = {} \<longleftrightarrow> y = {})\<close>
  by (clarsimp simp add: fun_eq_iff rel_set_def; blast)

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
  sets = [Abs("x", \<^Type>\<open>Set.set a\<close>, Bound 0)],
  set_thms = [],
  ctr_simps = [],
  rel = \<^Const>\<open>rel_set a b\<close>,
  rel_simps = @{thms' Lifting_Set.empty_transfer rel_set__const_True},
  rel_eq = @{thm' rel_set_eq},
  pred = Abs("P", a --> HOLogic.boolT, Abs ("S", \<^Type>\<open>Set.set a\<close>, \<^Const>\<open>Ball a\<close> $ Bound 0 $ Bound 1)),
  pred_injects = @{thms' Set.ball_simps(5) Set.ball_Un Set.ball_simps(7)},
  pred_simps = @{thms' Set.ball_simps},
  map = \<^Const>\<open>Set.image a b\<close>,
  map_thms = @{thms' Set.image_insert Set.image_Un Set.image_empty},
  map_disc_iffs = @{thms' image_is_empty},
  map_ident = @{thm' Set.image_ident},
  map_comp_of = @{thm' Set.image_image},
  fp_more = SOME {
    deads = [],
    lives = [a],
    lives'= [b],
    zip = \<^term>\<open>case_prod (\<times>) :: 'a set \<times> 'b set \<Rightarrow> ('a \<times> 'b) set\<close>,
    unzip = \<^term>\<open>(\<lambda>s. (Domain s, Range s)) :: ('a \<times> 'b) set \<Rightarrow> 'a set \<times> 'b set\<close>,
    zip_simps = []
  }
} end)
)\<close>

term \<open>(\<times>)\<close>
term \<open>(\<lambda>s. (Domain s, Range s)) :: ('a \<times> 'b) set \<Rightarrow> 'a set \<times> 'b set\<close>
term \<open>case_prod (\<times>)\<close>

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

declare Lifting.pred_prod_beta[\<phi>deriver_simp]

end
                                                          