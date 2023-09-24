text \<open>title: 
            Three Pigs: A Synthetic Approach to Data Refinement, an Algebra of Predicates,
                    and a General Automation for Data Structures, on BI
\<close>

theory Phi_Type_Algebra
  imports IDE_CP_Reasoning2
          Phi_Algb_Pre
          Phi_Domainoid
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

text \<open>TODO: move me somewhere

Besides the interpretation based on data refinement, our theory can also be interpreted using the usual
language of predicate logic. Essentially, we developed an assertion language splitting assertions into
structural predicates over objects on abstract domains. Particularly on BI, the structural predicates
specifying the concrete representation (on memory-level) of abstract data structures, have rich algebraic
properties that capture the algebraic model of the data structures and provide us a general automation.

\<close>

text \<open>TODO: move me somewhere

We provide 3 levels of automation,
\<^item> We have identified several key properties of \<phi>-types from which a mechanized reasoning on Separation Logic
  can be instantiated, covering sequential composition, branch, and loop.
  All issues of the automated reasoning about \<phi>-types reduce to providing the properties.
\<^item> We provide derivers to prove the properties from the definition of \<phi>-types automatically with annotated
  parameters of the properties. Induction is applied automatically for inductively
  defined recursive \<phi>-type (no co-inductive case is explored yet; we are also interested in impredicative
  variant of our logic).
\<^item> When no annotation is given, the derivers are able to guess the parameters of the properties
  by inferring through reasoning for non-recursive \<phi>-type and composing operators of Bounded
  Natural Functor for recursive \<phi>-type.
\<close>

text \<open>TODO: move me somewhere  << Classification of \<phi>-TA properties >>

Properties in the algebra of \<phi>-Type can be classified into two sorts,
\<^item> properties about objects, including Functionality, Carrier_Set, Abstract_Domain, Identity_Element
\<^item> properties about morphisms i.e. transformations, which essentially consists of two,
    \<^item> Transformation Functor
    \<^item> Commutativity between \<phi>-Type Operators

\<close>

text \<open>
Transformation of abstraction is ubiquitous. Refining an abstraction to either concrete representation
or a middle-level representation (i.e. stepwise refinement) is a transformation of abstraction, and
is carried as such in the theory (transformation also includes reversed concretization moreover).
The significance of stepwise refinement in conventional verification
is well-known. We in addition consider certified programming over a program logic, where we program in
a way of combining existing proofs of certified programs given in libraries to obtain a certified compositional
program. The abstractions given in a proof library is limited in number whereas the abstractions demanded by
clients can be various. The transformation (can be a kind of stepwise refinement) mitigates this gap,
so improves the composability of such certified programming and the reusability of existing proofs
in ordinary verification. 

Comparing to conventional approaches of data refinement, our approach is synthetic...

Besides, our method extends the composability of data refinement. Conventional data refinement
supports horizontal composition between programs and vertical composition between abstraction layers.
Some work in contextual refinement extends the composition to combining respective abstractions of
separated components by combining BI with refinement, but is much cumbersome than ours (as our method
uses predicates while theirs brings a heavy extension to the logic, though our method
assigning the abstract program into a different space with the concrete program is not suitable for
contextual refinement). 
In addition, we extend the composition to hierarchical structures of data structures by means of functors
of abstraction relations such as List(T) which generate abstractions of containers from the abstractions of elements.

Composability is important because it simplifies transformation by breaking it down to small transformations
and reversely enables the deduction deriving a larger number of transformations from a small set of
primitive transformations, by which the synthetic reasoning is possible and is simpler than the analytic
method by means of reusing the proofs of the primitive transformations and composing them along with
the hierarchical structures and the algebraic features (e.g. transformation functor given below) of
the data structures.

\<close>


section \<open>The Algebra of \<open>\<phi>\<close>-Refinement\<close>

subsection \<open>Definitions\<close>

subsubsection \<open>Transformation\<close>

definition \<open>Transformation_Functor F1 F2 T U D R mapper \<longleftrightarrow>
  (\<forall>x g. (\<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b) \<longrightarrow>
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

text \<open>A transformation functor \<open>mapper\<close> is complete iff for a given complete transformation relation
family \<open>{g\<^sub>i}\<close>, \<open>{mapper g\<^sub>i}\<close> is also complete (the notion of completeness can be extended to relations naturally
by converting a relation as a function to a set).\<close>


definition Functional_Transformation_Functor :: \<open>(('b,'a) \<phi> \<Rightarrow> ('d,'c) \<phi>)
                                               \<Rightarrow> (('b,'e) \<phi> \<Rightarrow> ('d,'f) \<phi>)
                                               \<Rightarrow> ('b,'a) \<phi>
                                               \<Rightarrow> ('b,'e) \<phi>
                                               \<Rightarrow> ('c \<Rightarrow> 'a set)
                                               \<Rightarrow> ('c \<Rightarrow> 'e set)
                                               \<Rightarrow> (('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> bool)
                                               \<Rightarrow> (('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'f)
                                               \<Rightarrow> bool\<close>
  where \<open>Functional_Transformation_Functor Fa Fb T U D R pred_mapper func_mapper \<longleftrightarrow>
            (\<forall>x f P. (\<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
                \<longrightarrow> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x)
                \<longrightarrow> (x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x))\<close>

text \<open>When the element transformation is applied with a partial function (with \<open>P\<close> giving the domain),
  the entire transformation is also a partial function.
  The \<^verbatim>\<open>func_mapper\<close> is usually the functional mapper and the
  \<^verbatim>\<open>pred_mapper\<close> is the predicate mapper of an ADT. An exceptional example is set,
  \<open>func_mapper\<^sub>s\<^sub>e\<^sub>t f P S = { f x |x \<in> S. P x }\<close> and \<open>pred_mapper\<^sub>s\<^sub>e\<^sub>t f P S = \<top>\<close>,
  whose (generalized) algebraic mappers are however set image and set-forall (of its element).

  \<open>P\<close> gives the domain of the partial map \<open>f\<close>.
  \<open>D\<close> gives the domain of the inner elements of the functor.
\<close>


lemma infer_FTF_from_FT:
  \<open> Transformation_Functor F1 F2 T U D R mapper
\<Longrightarrow> Object_Equiv (F2 U) eq
\<Longrightarrow> (\<forall>f P x y. mapper (\<lambda>a b. b = f a \<and> P a) x y \<longrightarrow> eq y (fm f P x) \<and> pm f P x)
\<Longrightarrow> Functional_Transformation_Functor F1 F2 T U D R pm fm \<close>
  unfolding Functional_Transformation_Functor_def Transformation_Functor_def
            Object_Equiv_def
  apply clarsimp
  subgoal premises prems for x f P
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>a b. b = f a \<and> P a\<close>]]
               prems(2-),
        clarsimp simp add: Transformation_def,
        blast) .


subsubsection \<open>Separation\<close>

definition Object_Sep_Homo\<^sub>I :: \<open>('b::sep_magma, 'a::sep_magma) \<phi> \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool\<close>
  where \<open>Object_Sep_Homo\<^sub>I T D \<longleftrightarrow> (\<forall>x y. (y,x) \<in> D \<longrightarrow> ((x \<Ztypecolon> T) * (y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x * y \<Ztypecolon> T \<w>\<i>\<t>\<h> x ## y ))\<close>

definition \<open>Object_Sep_Homo\<^sub>E T \<longleftrightarrow> (\<forall>x y. x ## y \<longrightarrow> ( (x * y \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (x \<Ztypecolon> T) * (y \<Ztypecolon> T) ))\<close>

definition \<open>Separation_Homo\<^sub>I Ft Fu F3 T U D z \<longleftrightarrow>
              (\<forall>x y. (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (T \<^emph> U)))\<close>

definition \<open>Separation_Homo\<^sub>E Ft Fu F3 T U un \<longleftrightarrow> \<comment> \<open>Does it need a domain constraint?\<close>
              (\<forall>z. z \<Ztypecolon> F3 (T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph> Fu U)\<close>

definition \<open>Separation_Homo\<^sub>I_Cond Ft Fu F3 C\<^sub>W T U D z \<longleftrightarrow>
              (\<forall>x y. (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph>[C\<^sub>W] Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (T \<^emph>[C\<^sub>W] U)))\<close>

definition \<open>Separation_Homo\<^sub>E_Cond Ft Fu F3 C\<^sub>R T U D un \<longleftrightarrow> \<comment> \<open>Does it need a domain constraint?\<close>
              (\<forall>z. z \<in> D \<longrightarrow> (z \<Ztypecolon> F3 (T \<^emph>[C\<^sub>R] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph>[C\<^sub>R] Fu U))\<close>


subsubsection \<open>Semimodule\<close>

definition Semimodule_Zero :: \<open>('s::zero \<Rightarrow> ('c::one,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>Semimodule_Zero F T zero \<longleftrightarrow> (\<forall>x. (x \<Ztypecolon> F zero T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1)\<close>

definition Closed_Semimodule_Zero :: \<open>('s::zero \<Rightarrow> ('c::one,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>Closed_Semimodule_Zero F T zero \<longleftrightarrow> (\<forall>x. (x \<Ztypecolon> F zero T) = 1)\<close>
  \<comment> \<open>It is actually a very strong property particularly when \<open>T\<close> is an empty \<phi>-type of empty
      abstract domain. It excludes functional homomorphism like \<open>F c T \<equiv> \<psi> c \<Zcomp>\<^sub>f T\<close>.\<close>

definition Semimodule_Identity\<^sub>I :: \<open>('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> 's \<Rightarrow> ('a\<^sub>T \<Rightarrow> bool) \<Rightarrow> ('a\<^sub>T \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  where \<open>Semimodule_Identity\<^sub>I F T one D i \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> T) = (i x \<Ztypecolon> F one T))\<close>
  \<comment> \<open>It seems \<open>Semimodule_Identity\<^sub>I\<close> is not that useful?\<close>

definition Semimodule_Identity\<^sub>E :: \<open>('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a\<^sub>T) \<Rightarrow> bool\<close>
  where \<open>Semimodule_Identity\<^sub>E F T one D f \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> F one T) = (f x \<Ztypecolon> T))\<close>

(*
definition Semimodule_Scalar_Assoc :: \<open> ('s \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                     \<Rightarrow> ('c,'a) \<phi>
                                     \<Rightarrow> ('s::semigroup_mult \<Rightarrow> bool)
                                     \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Assoc F T Ds \<longleftrightarrow> (\<forall>s t. Ds s \<and> Ds t \<longrightarrow> F s (F t T) = F (t * s) T)\<close>
  \<comment> \<open>Associativity of scalar multiplication\<close>
*)

definition Semimodule_Scalar_Assoc\<^sub>I :: \<open> ('s\<^sub>s \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>_\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                     \<Rightarrow> ('c,'a) \<phi>
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 's\<^sub>c)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t)
                                     \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
      \<longleftrightarrow> (\<forall>s t x. Ds s \<and> Dt t \<and> Dx s t x \<longrightarrow> (x \<Ztypecolon> Fs s (Ft t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fc (smul s t) T))\<close>
  \<comment> \<open>An extension overcoming the type limitation of the simple type theory of Isabelle.
      It can cover mul quant\<close>

definition Semimodule_Scalar_Assoc\<^sub>E :: \<open> ('s\<^sub>s \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>_\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                     \<Rightarrow> ('c,'a) \<phi>
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 's\<^sub>c)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t)
                                     \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
      \<longleftrightarrow> (\<forall>s t x. Ds s \<and> Dt t \<and> Dx s t x \<longrightarrow> (f s t x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fs s (Ft t T)))\<close>

text \<open>The extended scalar association operator for Finite Multiplicative Quantification is just uncurrying.\<close>


definition Semimodule_SDistr_Homo\<^sub>Z :: \<open>('s \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                    \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi>
                                    \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                    \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x \<longrightarrow>
                  (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (s + t) T ))\<close>
  \<comment> \<open>The left distributive law (i.e., the distributivity of scalar addition) of a left-module.
      Note the right distributive law (i.e., the distributivity of vector addition) is just the separation homomorphism.
      So, when both of \<open>Semimodule_Scalar_Assoc\<close>, \<open>Separation_Homo\<close>, \<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, and
      homomorphism of identity element, are satisfied, it is then a semimodule.
\<close>

definition Semimodule_SDistr_Homo\<^sub>Z_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                        \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi>
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>Z_rev F T Ds Dx' z' Dx z \<longleftrightarrow>
            (Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx' z' \<longrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> t ##\<^sub>+ s \<and> Dx t s x \<longrightarrow>
                  (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) T )))\<close>
  \<comment> \<open>Should be only used when assuming non-commutative separation algebra and non-commutative scalar,
      else should use \<open>Semimodule_SDistr_Homo\<^sub>Z\<close> instead, see \<open>SDirst_in_comm_sep_implies_rev\<close>
      and \<open>SDirst_in_comm_scalar_implies_rev\<close>\<close>
  \<comment> \<open>Note antecedents of \<open>Semimodule_SDistr_Homo\<^sub>Z_rev\<close> will not trigger the template instantiation, as
       they are not template parameters but normal reasoning goals.
      You may add a useless premise \<open>Semimodule_SDistr_Homo\<^sub>Z\<close> in your rule serving as a template parameter,
        as all instances of \<open>Semimodule_SDistr_Homo\<^sub>Z_rev\<close> are deduced from \<open>Semimodule_SDistr_Homo\<^sub>Z\<close>.
      It is not a template parameter because one \<open>Semimodule_SDistr_Homo\<^sub>Z\<close> may deduce multiple
        \<open>Semimodule_SDistr_Homo\<^sub>Z_rev\<close> depending on if the scalar or the separation algebra is commutative,
        and we really don't want multiple instantiations of a template parameter because the number
        of instantiations is multiplied!\<close>


definition Semimodule_SDistr_Homo\<^sub>U :: \<open>('s \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                        \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi>
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>U F T Ds Dx uz \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x \<longrightarrow>
                (x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t T \<^emph> F s T ))\<close>

definition Semimodule_SDistr_Homo\<^sub>U_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                        \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi>
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>U_rev F T Ds Dx' uz' Dx uz \<longleftrightarrow>
            (Semimodule_SDistr_Homo\<^sub>U F T Ds Dx' uz' \<longrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> t ##\<^sub>+ s \<and> Dx t s x \<longrightarrow>
                (x \<Ztypecolon> F (t + s) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t T \<^emph> F s T )))\<close>
  \<comment>\<open>Also not a template parameter, see \<open>Semimodule_SDistr_Homo\<^sub>Z_rev\<close>\<close>


subsubsection \<open>Commutativity between \<phi>-Type Operators\<close>

text \<open>\<open>Separation_Homo\<close> is a special case of the commutativity to \<open>\<^emph>\<close>.\<close>

text \<open>The properties are all given in relationform, while functional version can be obtained by
  and should be represented in \<^term>\<open>embedded_func\<close> which prevents over-simplification
  (e.g., when \<open>P = (\<lambda>x. True)\<close>)\<close>

paragraph \<open>Unary-to-Unary\<close>

definition Tyops_Commute :: \<open> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                           \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F,'a\<^sub>F) \<phi>)
                           \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                           \<Rightarrow> (('c\<^sub>F,'a\<^sub>F) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                           \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                           \<Rightarrow> ('a \<Rightarrow> bool)
                           \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)
                           \<Rightarrow> bool\<close>
  where \<open>Tyops_Commute F F' G G' T D r \<longleftrightarrow>
            (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y))\<close>

paragraph \<open>Unary-to-Binary\<close>

definition Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 :: \<open> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                             \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi>)
                             \<Rightarrow> (('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi>)
                             \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                             \<Rightarrow> (('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                             \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                             \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi>
                             \<Rightarrow> ('a \<Rightarrow> bool)
                             \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)
                             \<Rightarrow> bool\<close>
  where \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r \<longleftrightarrow>
            (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r x y))\<close>

paragraph \<open>Binary-to-Unary\<close>

definition Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 :: \<open> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi>)
                              \<Rightarrow> (('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi>)
                              \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                              \<Rightarrow> (('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                              \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                              \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi>
                              \<Rightarrow> ('b \<Rightarrow> bool)
                              \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool)
                              \<Rightarrow> bool\<close>
  where \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r \<longleftrightarrow>
            (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (G T U) \<s>\<u>\<b>\<j> y. r x y))\<close>

subsubsection \<open>Configurations\<close>
(*
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
]]*)

(* TODO: depreciate!!!

The default patterns of the rules are more general here by varifying types.
  This is specially designed.
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

  \<phi>premise_attribute? [\<phi>reason add] for \<open>Transformation_Functor _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Functional_Transformation_Functor _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Object_Sep_Homo\<^sub>I _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Object_Sep_Homo\<^sub>E _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>I _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>E _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>I_Cond _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Separation_Homo\<^sub>E_Cond _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Zero _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Closed_Semimodule_Zero _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Identity\<^sub>I _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Identity\<^sub>E _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Scalar_Assoc\<^sub>I _ _ _ _ _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_Scalar_Assoc\<^sub>E _ _ _ _ _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_SDistr_Homo\<^sub>Z _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_SDistr_Homo\<^sub>Z_rev _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_SDistr_Homo\<^sub>U _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Semimodule_SDistr_Homo\<^sub>U_rev _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Tyops_Commute _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason add] for \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 _ _ _ _ _ _ _ _ _\<close>,

  \<phi>reason_default_pattern
      \<open>Transformation_Functor ?Fa ?Fb _ _ _ _ _\<close> \<Rightarrow>
      \<open>Transformation_Functor ?Fa _ _ _ _ _ _\<close>
      \<open>Transformation_Functor _ ?Fb _ _ _ _ _\<close>   (100)
  and \<open>Functional_Transformation_Functor ?Fa ?Fb _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Functional_Transformation_Functor ?Fa _ _ _ _ _ _ _\<close>
      \<open>Functional_Transformation_Functor _ ?Fb _ _ _ _ _ _\<close>   (100)
  and \<open>Separation_Homo\<^sub>I_Cond ?Ft ?Fu ?Fc _ _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>I_Cond ?Ft _ _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>I_Cond _ ?Fu _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>I_Cond _ _ ?Fc _ _ _ _ _\<close>  (100)
  and \<open>Separation_Homo\<^sub>E_Cond ?Ft ?Fu ?Fc _ _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>E_Cond ?Ft _ _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>E_Cond _ ?Fu _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>E_Cond _ _ ?Fc _ _ _ _ _\<close>  (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>Z ?F ?T _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>Z ?F ?T _ _ _\<close> (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>U ?F ?T _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>U ?F ?T _ _ _\<close> (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>Z_rev ?F ?T _ _ _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>Z_rev ?F ?T _ _ _ _ _\<close> (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>U_rev ?F ?T _ _ _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>U_rev ?F ?T _ _ _ _ _\<close> (100)
  and \<open>Tyops_Commute ?F _ ?G _ ?T _ _\<close> \<Rightarrow> \<open>Tyops_Commute ?F _ ?G _ ?T _ _\<close> (100)
  and \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F _ _ ?G _ ?T ?U _ _\<close> \<Rightarrow>
      \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F _ _ ?G _ ?T ?U _ _\<close>   (100)
  and \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F _ _ ?G _ ?T ?U _ _\<close> \<Rightarrow>
      \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F _ _ ?G _ ?T ?U _ _\<close>   (100)
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
 and \<phi>type_algebra_prop_cut = (1000, [1000, 1030]) for \<open>_\<close> in \<phi>type_algebra_properties
    \<open>Cutting rules\<close>
 and \<phi>TA_derived_properties = (50, [50,50]) for \<open>_\<close> in \<phi>type_algebra_properties
    \<open>Automatically derived properties.\<close>
 and \<phi>TA_varify_out = (3900, [3900,3900]) for \<open>_\<close> in \<phi>type_algebra_all_properties and > \<phi>type_algebra_properties
    \<open>Systematic rules of \<phi>-type algebraic properties that varifies OUT arguments that are not varibales\<close>

subsubsection \<open>Groups for Specific Properties\<close>

\<phi>reasoner_group Object_Sep_Homo_functor = (50, [50,50]) for (\<open>Object_Sep_Homo\<^sub>I T D\<close>, \<open>Object_Sep_Homo\<^sub>E T\<close>)
                                                         in \<phi>type_algebra_properties
    \<open>Object_Sep_Homo for functors\<close>

subsubsection \<open>Derived Rules\<close>

\<phi>reasoner_group deriving_local_rules = (200, [200,200]) for \<open>_\<close> > default
    \<open>Local reasoning rules such as those extracted from induction hypotheses used during deriving.\<close>

 and ToA_derived_one_to_one_functor = (70, [70,70]) for \<open>x \<Ztypecolon> F(T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U)\<close> in ToA_derived
    \<open>Derived transformation in form \<open>x \<Ztypecolon> F(T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U)\<close>, of a high priority as this is what
     should be attempted in reasoning.\<close>
 and To_ToA_derived_Tr_functor = (60, [60,60]) for \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r x y \<w>\<i>\<t>\<h> P @action to U\<close>
                                                in To_ToA_derived
    \<open>Derived To-Transformation rules for transformation functor\<close>
 and To_ToA_derived_to_raw = (60, [60,60]) for \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y \<w>\<i>\<t>\<h> P @action to Itself\<close>
                                            in To_ToA_derived
    \<open>Derived To-Transformation openning down the raw concrete representation\<close>
 and \<phi>simp_derived_Tr_functor = (40, [40,45]) for \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>simp\<close>
                                               in \<phi>simp_derived
    \<open>Derived transformation-based simplification for transformation functor\<close>
 and \<phi>simp_derived_bubbling = (60, [60,61]) for \<open>x \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YY @action \<A>simp\<close>
    \<open>Derived transformation-based simplification about bubbling\<close>
 and derived_SE_functor = (70, [70,70]) for \<open>x \<Ztypecolon> F(T) \<^emph>[Cw] F(W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U) \<^emph>[Cr] F(R)\<close> in ToA_derived
    \<open>Derived rules of Separation Extraction, of a high priority as this is what
     should be attempted in reasoning. No confliction with %ToA_derived_one_to_one_functor\<close>

\<phi>reasoner_group_assert identity_element_ToA < deriving_local_rules

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
 and derived_SE_inj_to_module = (28, [28,28]) for \<open>x \<Ztypecolon> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>
                                              in ToA_derived and < derived_SE_scalar_assoc
    \<open>Derived rules lifting the target part into the module operator \<open>F\<close>\<close>

subsubsection \<open>Guess Algebraic Operators\<close>
(*
\<phi>reasoner_group guess_algebraic_oprs = (100, [0, 3000]) for \<open>_\<close>
    \<open>A general group consisting of reasoning rules derivign or guessing operators for algbebraic properties\<close>
 and guess_algebraic_oprs_default = (1000, [1000, 1030]) for \<open>_\<close> in guess_algebraic_oprs
    \<open>Cutting rules derivign or guessing operators for algbebraic properties\<close>
 and guess_algebraic_oprs_cut = (1000, [1000, 1030]) for \<open>_\<close> in guess_algebraic_oprs
    \<open>Cutting rules derivign or guessing operators for algbebraic properties\<close>
*)

subsection \<open>Direct Applications \& Properties\<close>

text \<open>Directly applying the algebraic properties.\<close>

subsubsection \<open>Transformation Functor\<close>

lemma Transformation_Functor_sub_dom:
  \<open> (\<And>x. Da x \<subseteq> Db x)
\<Longrightarrow> Transformation_Functor F1 F2 T U Da R mapper
\<Longrightarrow> Transformation_Functor F1 F2 T U Db R mapper\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_Functor_sub_rng:
  \<open> (\<And>x. Rb x \<subseteq> Ra x)
\<Longrightarrow> Transformation_Functor F1 F2 T U D Ra mapper
\<Longrightarrow> Transformation_Functor F1 F2 T U D Rb mapper\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_Functor_sub_mapper:
  \<open> ma \<le> mb
\<Longrightarrow> Transformation_Functor F1 F2 T U D R ma
\<Longrightarrow> Transformation_Functor F1 F2 T U D R mb\<close>
  unfolding Transformation_Functor_def
  by (clarsimp simp add: le_fun_def Transformation_def Ball_def, blast)

lemma apply_Transformation_Functor:
  \<open> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<close>
  unfolding Transformation_Functor_def Premise_def
  by simp

lemma apply_Functional_Transformation_Functor:
  \<open> Functional_Transformation_Functor Fa Fb T U D R pred_mapper func_mapper
\<Longrightarrow> (\<And>a \<in> D x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x\<close>
  unfolding meta_Ball_def Argument_def Premise_def
            Functional_Transformation_Functor_def Transformation_Functor_def
  by clarsimp


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

lemma Separation_Homo\<^sub>I_Cond_sub_D:
  \<open> D' \<subseteq> D
\<Longrightarrow> Separation_Homo\<^sub>I_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>W T U D  z
\<Longrightarrow> Separation_Homo\<^sub>I_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>W T U D' z\<close>
  unfolding Separation_Homo\<^sub>I_Cond_def
  by blast

lemma Separation_Homo\<^sub>E_Cond_sub_D:
  \<open> D' \<subseteq> D
\<Longrightarrow> Separation_Homo\<^sub>E_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>R T U D  z
\<Longrightarrow> Separation_Homo\<^sub>E_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>R T U D' z\<close>
  unfolding Separation_Homo\<^sub>E_Cond_def
  by blast

lemma apply_Separation_Homo\<^sub>I:
  \<open> Separation_Homo\<^sub>I Ft Fu Fc T U D z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z x \<Ztypecolon> Fc(T \<^emph> U)\<close>
  unfolding Separation_Homo\<^sub>I_def Premise_def meta_Ball_def meta_case_prod_def split_paired_all
  by (cases x; simp)

lemma apply_Separation_Homo\<^sub>E:
  \<open> Separation_Homo\<^sub>E Ft Fu Fc T U un
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph> Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'[symmetric]
  by simp

lemma apply_Separation_Homo\<^sub>I_Cond:
  \<open> Separation_Homo\<^sub>I_Cond Ft Fu Fc C\<^sub>R T U D z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph>[C\<^sub>R] Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z x \<Ztypecolon> Fc(T \<^emph>[C\<^sub>R] U)\<close>
  unfolding Separation_Homo\<^sub>I_Cond_def Premise_def split_paired_all
  by (cases x; simp)

lemma apply_Separation_Homo\<^sub>E_Cond:
  \<open> Separation_Homo\<^sub>E_Cond Ft Fu Fc C\<^sub>W T U D un
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph>[C\<^sub>W] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph>[C\<^sub>W] Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_Cond_def \<phi>Prod_expn'[symmetric] Premise_def
  by simp


subsubsection \<open>Semimodule\<close>

paragraph \<open>Association\<close>

lemma apply_Semimodule_SAssoc\<^sub>I:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> Fs s (Ft t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fc (smul s t) T \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Premise_def
  by clarsimp

lemma apply_Semimodule_SAssoc\<^sub>E:
  \<open> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> f s t x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fs s (Ft t T) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def
  by clarsimp


paragraph \<open>Left Distributivity\<close>

lemma Semimodule_SDistr_Homo\<^sub>Z_sub:
  \<open> Ds \<le> Ds' \<and> Dx \<le> Dx'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F T Ds' Dx' z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def le_fun_def le_bool_def
  by blast

lemma [\<phi>reason %\<phi>TA_varify_out except \<open>Semimodule_SDistr_Homo\<^sub>Z _ _ ?var_Ds ?var_Dx _\<close> ]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F T Ds' Dx' z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds \<le> Ds' \<and> Dx \<le> Dx'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z\<close>
  unfolding Premise_def
  using Semimodule_SDistr_Homo\<^sub>Z_sub by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>Z:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (s + t) T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F t T \<^emph> \<black_circle> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> \<black_circle> F (s + t) T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Premise_def Transformation_def
  by (clarsimp; metis prod.collapse)

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_rev:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx' z'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F T Ds Dx' z' Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F s T \<^emph> F t T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> F (s + t) T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_rev_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx' z'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F T Ds Dx' z' Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F s T \<^emph> \<black_circle> F t T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> \<black_circle> F (s + t) T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Premise_def Transformation_def
  by (clarsimp; metis prod.collapse)

lemma apply_Semimodule_SDistr_Homo\<^sub>U:
  \<open> Semimodule_SDistr_Homo\<^sub>U F T Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t T \<^emph> F s T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>U F T Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> \<black_circle> F t T \<^emph> \<black_circle> F s T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_def Premise_def Transformation_def
  by (clarsimp; metis sep_disj_option(1) times_option(1))

lemma apply_Semimodule_SDistr_Homo\<^sub>U_rev:
  \<open> Semimodule_SDistr_Homo\<^sub>U F T Ds Dx' uz'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U_rev F T Ds Dx' uz' Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F s T \<^emph> F t T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_rev_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>U_rev_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>U F T Ds Dx' uz'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U_rev F T Ds Dx' uz' Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> \<black_circle> F s T \<^emph> \<black_circle> F t T \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_rev_def Premise_def Transformation_def
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

lemma apfst_id'[simp]:
  \<open>apfst (\<lambda>x. x) = (\<lambda>x. x)\<close>
  by (simp add: fun_eq_iff)

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
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U' \<s>\<u>\<b>\<j> y. y = y' @action to (OPEN T) \<close>
  unfolding Action_Tag_def Simplify_def
  by simp

lemma \<phi>open_abstraction_ToA:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> OPEN T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def
  by simp

lemma \<phi>open_abstraction_ToA_R:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> R * U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (x \<Ztypecolon> OPEN T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def
  by simp

lemma \<phi>open_abstraction_ToA_W:
  \<open> (\<And>x. (x \<Ztypecolon> T) = (f x \<Ztypecolon> U'))
\<Longrightarrow> apfst f x \<Ztypecolon> U' \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> OPEN T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn')

lemma \<phi>make_abstraction:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def MAKE_def by simp

lemma \<phi>make_abstraction'R:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def MAKE_def
  by simp

lemma \<phi>make_abstraction'eq:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Object_Equiv T eq \<and>\<^sub>\<r> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[MODE_SAT] eq x x')
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq x x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> MAKE T \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
  by clarsimp

lemma \<phi>make_abstraction'R'eq:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Object_Equiv T eq \<and>\<^sub>\<r> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[MODE_SAT] eq x x')
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq x x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> MAKE T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
  by (cases C; clarsimp; blast)

lemma \<phi>make_Identity_Element\<^sub>E:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> Identity_Element\<^sub>E U
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> MAKE T) \<close>
  unfolding MAKE_def
  by simp

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


consts \<phi>instantiation :: mode

\<phi>reasoner_ML \<open>Simplify \<phi>instantiation\<close> 1000 (\<open>\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] _ : _\<close>)
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty)
        (Phi_Type_Template_Properties.Template_Inst_SS.enhance) true) o snd\<close>


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
#>*)add_property_kinds [
  \<^pattern_prop>\<open>Transformation_Functor _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Functional_Transformation_Functor _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>I _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>E _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>I_Cond _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>E_Cond _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Closed_Semimodule_Zero _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Zero _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Identity\<^sub>I _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Identity\<^sub>E _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Scalar_Assoc\<^sub>I _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Scalar_Assoc\<^sub>E _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_SDistr_Homo\<^sub>Z _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_SDistr_Homo\<^sub>U _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>TERM (Identity_Elements\<^sub>I _)\<close>,
  \<^pattern_prop>\<open>TERM (Identity_Elements\<^sub>E _)\<close>,
  \<^pattern_prop>\<open>Tyops_Commute _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 _ _ _ _ _ _ _ _ _\<close>
]

(*#> Phi_Type_Algebra.add_property_kind \<^const_name>\<open>Object_Equiv\<close> (fn (_ $ T $ _) => T)*)
\<comment> \<open>We do not add Object_Equiv into the property-based template instantiation here because
  it can have special overridings for singular points like that many type operators \<open>F\<close> have a
  wider reachability relation at \<open>F \<circle>\<close>. The overloadings multiply the resulted instantiations
  and they requires priority precedence which is not in the capability of the template
  instantiation automation.\<close>
end
\<close>

declare [[
  \<phi>reason_default_pattern \<open>TERM (Identity_Elements\<^sub>I ?F)\<close> \<Rightarrow> \<open>TERM (Identity_Elements\<^sub>I ?F)\<close> (100)
                      and \<open>TERM (Identity_Elements\<^sub>E ?F)\<close> \<Rightarrow> \<open>TERM (Identity_Elements\<^sub>E ?F)\<close> (100)
]]

text \<open>Candidates of templates instantiation are not prioritized. When a property requires multiple
  rules ordered by their priorities for overrides and optimizations, the property is not declared
  as a parameter property in the template instantiation system but just a \<phi>-LPR reasoning goal tagged
  by \<open>\<A>_template_reason\<close> in the template.
  Instead, a trigger \<open>TERM (The_Property F)\<close> is used as the parameter property activating
  the instantiation and (when the trigger is given) indicating when the prioritized rules are all given
  so when can the instantiation start. \<close>


subsection \<open>Programming Methods to Prove the Properties\<close>


subsubsection \<open>Transformation Functor\<close>

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>x g.
            \<forall>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b
        \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
        \<Longrightarrow> x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Transformation_Functor F1 F2 T U D R mapper)) MM DD RR FF\<close>
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
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s (x,y) \<Ztypecolon> F (s + t) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_SDistr_Homo\<^sub>Z_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

(* all be deduced from \<open>Semimodule_SDistr_Homo\<^sub>Z\<close> and no need to go to programming
lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x y.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds t \<and> Ds s \<and> t ##\<^sub>+ s \<and> Dx t s (x,y)
          \<Longrightarrow> (y \<Ztypecolon> F s T) * (x \<Ztypecolon> F t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s (x,y) \<Ztypecolon> F (t + s) T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_SDistr_Homo\<^sub>Z_rev F T Ds Dx z)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_SDistr_Homo\<^sub>Z_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')
*)

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
          \<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t T \<^emph> F s T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_SDistr_Homo\<^sub>U F T Ds Dx uz)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_SDistr_Homo\<^sub>U_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

(* all be deduced from \<open>Semimodule_SDistr_Homo\<^sub>Z\<close> and no need to go to programming
lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
          \<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F s T \<^emph> F t T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_SDistr_Homo\<^sub>U_rev F T Ds Dx uz)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_SDistr_Homo\<^sub>U_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')
*)


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
  \<comment> \<open>While \<open>Type_Variant_of_the_Same_Type_Operator\<close> considers the \<phi>-type as a type operator
      over each of its parameters, e.g., \<open>\<lambda>A. F A B C\<close> \<open>\<lambda>B. F A B C\<close> \<open>\<lambda>C. F A B C\<close> for \<open>F A B C\<close>,
      the \<open>Type_Variant_of_the_Same_Type_Operator2\<close> only considers the given \<phi>-type as a binary type
      operator over its last two parameters, e.g., only \<open>\<lambda>B C. F A B C\<close>.
     This is for performance. For other interpretations, user may provide the rule of
      \<open>Type_Variant_of_the_Same_Type_Operator2\<close> manually.\<close>

definition Type_Variant_of_the_Same_Scalar_Mul
        :: \<open> ('s \<Rightarrow> 'a \<Rightarrow> ('b,'c) \<phi>) \<Rightarrow> ('s2 \<Rightarrow> 'a2 \<Rightarrow> ('b2,'c2) \<phi>) \<Rightarrow> bool \<close>
  where \<open> Type_Variant_of_the_Same_Scalar_Mul Fa Fb \<longleftrightarrow> True \<close>

definition Parameter_Variant_of_the_Same_Type :: \<open> 'a \<Rightarrow> 'b \<Rightarrow> bool \<close>
  where \<open> Parameter_Variant_of_the_Same_Type Fa Fb \<longleftrightarrow> True \<close>
  \<comment> \<open>Every parameter together with any types is differentiated\<close>
(*
definition Parameter_Variant_of_the_Same_Type1 :: \<open> ('p \<Rightarrow> ('a,'b) \<phi>) \<Rightarrow> ('p2 \<Rightarrow> ('c,'d) \<phi>) \<Rightarrow> bool \<close>
  where \<open> Parameter_Variant_of_the_Same_Type1 Fa Fb \<longleftrightarrow> True \<close>
  \<comment> \<open>Every parameter together with any types is differentiated\<close>
*)
declare [[
  \<phi>reason_default_pattern
      \<open>Type_Variant_of_the_Same_Type_Operator ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Type_Operator ?Fa _\<close> (100)
  and \<open>Type_Variant_of_the_Same_Type_Operator2 ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Type_Operator2 ?Fa _\<close> (100)
  and \<open>Type_Variant_of_the_Same_Scalar_Mul ?Fa _\<close> \<Rightarrow> \<open>Type_Variant_of_the_Same_Scalar_Mul ?Fa _\<close> (100)
  and \<open>Parameter_Variant_of_the_Same_Type ?Fa _\<close> \<Rightarrow> \<open>Parameter_Variant_of_the_Same_Type ?Fa _\<close> (100)
  (*and \<open>Parameter_Variant_of_the_Same_Type1 ?Fa _\<close> \<Rightarrow> \<open>Parameter_Variant_of_the_Same_Type1 ?Fa _\<close> (100)*)
  
  (* \<phi>premise_attribute? [\<phi>reason add] for \<open>Type_Variant_of_the_Same_Type_Operator _ _\<close> *)
  (* \<phi>premise_attribute? [\<phi>reason add] for \<open>Parameter_Variant_of_the_Same_Type _ _\<close> *)
]]

\<phi>reasoner_group variants_of_type_opr = (%cutting, [%cutting, %cutting])
  for (\<open>Type_Variant_of_the_Same_Type_Operator F F'\<close>,
       \<open>Type_Variant_of_the_Same_Type_Operator2 F F'\<close>,
       \<open>Type_Variant_of_the_Same_Scalar_Mul F F'\<close>,
       \<open>Parameter_Variant_of_the_Same_Type F F'\<close>)
  \<open>variants_of_type_opr\<close>

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
   Phi_Type_Template_Properties.add_property_kinds [
    \<^pattern_prop>\<open>Type_Variant_of_the_Same_Type_Operator _ _\<close>,
    \<^pattern_prop>\<open>Type_Variant_of_the_Same_Type_Operator2 _ _\<close>,
    \<^pattern_prop>\<open>Type_Variant_of_the_Same_Scalar_Mul _ _\<close>,
    \<^pattern_prop>\<open>Parameter_Variant_of_the_Same_Type _ _\<close>
  (*\<^pattern_prop>\<open>Parameter_Variant_of_the_Same_Type1 _ _\<close>*)
  ]
\<close>

\<phi>reasoner_ML Parameter_Variant_of_the_Same_Type 1000 (\<open>Parameter_Variant_of_the_Same_Type _ _\<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () =>
    case Thm.major_prem_of sequent
      of _ (*Trueprop*) $ (_ (*Parameter_Variant_of_the_Same_Type*) $ LHS $ Var (v,_)) =>
          let val thy = Proof_Context.theory_of ctxt
              exception Not_A_Phi_Type
              fun parse lv bvs (X $ Bound i) =
                    if i < lv then parse lv (SOME i :: bvs) X else parse lv (NONE :: bvs) X
                | parse lv bvs (X $ Y) = parse lv (NONE :: bvs) X
                | parse lv bvs (Abs(_,_,X)) = parse (lv+1) (map (Option.map (fn i=>i+1)) bvs) X
                | parse lv bvs (Const(N, _)) =
                    let val idx = Thm.maxidx_of sequent + 1
                        val ty = Logic.incr_tvar idx (Sign.the_const_type thy N )
                        val args = List.take (Term.binder_types ty, length bvs)
                        val const = Const(N, ty)
                        val (F0,bvs) = fold_index (
                              fn (_, (SOME b, ty)) => (fn (X,bvs) => (X $ Bound b, (b,ty)::bvs))
                               | (i, (NONE, ty)) => (fn (X,bvs) => (X $ Var (("x",idx+i),ty), bvs))
                            ) (bvs ~~ args) (const, [])
                        val F = fold_index (fn (i,_) => fn X =>
                                  case AList.lookup (op =) bvs i
                                    of SOME ty => Abs ("_", ty, X)
                                     | NONE => raise Not_A_Phi_Type
                                ) bvs F0
                             |> Thm.cterm_of ctxt
                     in Drule.infer_instantiate ctxt [(v, F)] sequent
                     |> (fn th => @{lemma' \<open>Parameter_Variant_of_the_Same_Type A B\<close>
                                        by (simp add: Parameter_Variant_of_the_Same_Type_def)} RS th)
                     |> (fn th => SOME ((ctxt,th), Seq.empty))
                    end
           in parse 0 [] LHS
          end
       | _ => NONE  
) \<close>



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

(*
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
*)

lemma [\<phi>reason_template name Fa.simp_cong [\<phi>simp_cong]]:
  \<open> Transformation_Functor Fa Fa T U (\<lambda>x. {x}) (\<lambda>x. \<top>) (\<lambda>x. x)
\<Longrightarrow> Transformation_Functor Fa Fa U T (\<lambda>x. {x}) (\<lambda>x. \<top>) (\<lambda>x. x)
\<Longrightarrow> PROP NO_SIMP' ((x \<Ztypecolon> T) \<equiv> (x' \<Ztypecolon> U))
\<Longrightarrow> (x \<Ztypecolon> Fa T) \<equiv> (x' \<Ztypecolon> Fa U)\<close>
  unfolding Transformation_Functor_def Transformation_def atomize_eq NO_SIMP'_def
  apply (auto simp add: BI_eq_iff)
  subgoal premises prems for xa
    using prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>_ c. c = x'\<close>], simplified]
    using prems(3) prems(4) by blast
  subgoal premises prems for xa
    using prems(2)[THEN spec[where x=x'], THEN spec[where x=\<open>\<lambda>_ c. c = x\<close>], simplified]
    using prems(3) prems(4) by blast
  .

lemma transformation[\<phi>reason_template name Fa.transformation []]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>
  unfolding meta_Ball_def Premise_def \<r>Guard_def Transformation_Functor_def
  by clarsimp

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor name Fa.To_ToAformation]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fb Z) \<close>
  unfolding Action_Tag_def \<r>Guard_def
  using transformation[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor name Fa.to_traverse]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z) \<close>
  unfolding Action_Tag_def \<r>Guard_def
  using transformation[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template name Fa.\<A>simp [\<phi>transformation_based_simp default %\<phi>simp_derived_Tr_functor no trigger]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>simp)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>simp \<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  using transformation[unfolded Premise_def \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

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

lemma [\<phi>reason_template default %\<phi>simp_derived_Tr_functor+5 name Fb.\<A>simp_sep_homo]:
  \<open> Separation_Homo\<^sub>E Fa\<^sub>L Fa\<^sub>R Fb U\<^sub>L U\<^sub>R un
\<Longrightarrow> x \<Ztypecolon> Fb (U\<^sub>L \<^emph>\<^sub>\<A> U\<^sub>R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fa\<^sub>L U\<^sub>L \<^emph>\<^sub>\<A> Fa\<^sub>R U\<^sub>R \<s>\<u>\<b>\<j> y. y = un x @action \<A>simp\<close>
  unfolding Separation_Homo\<^sub>E_def Action_Tag_def Bubbling_def
  by (clarsimp simp add: Subjection_transformation_rewr Ex_transformation_expn)


(*locale Functional_Transformation_Functor =
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
     
*)

lemma FTF_template[no_atp, \<phi>reason_template default %ToA_derived_one_to_one_functor name Fa.functional_transformation]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor Fa Fb T U D R pred_mapper func_mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<longrightarrow> f a \<in> R x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x\<close>
  unfolding \<r>Guard_def
  using apply_Functional_Transformation_Functor[unfolded Argument_def,
            where func_mapper=func_mapper and pred_mapper=pred_mapper] .


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
\<Longrightarrow> Transformation_Functor F' F (T \<^emph> T) T D R m
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
    from prems(2)[THEN spec[where x=\<open>zz (y,x)\<close>],
                  THEN spec[where x=\<open>\<lambda>(b,a) c. c = a * b \<and> a ## b \<and> (b,a) \<in> D (zz (y,x))\<close>],
                  THEN mp, OF t1]
         prems(4)[THEN spec[where x=y], THEN spec[where x=x]]
         prems(1,5,6)
    show ?thesis
      by (clarsimp simp add: Transformation_def; blast)
  qed .

lemma [\<phi>reason_template name Fc.\<phi>Prod []]:
  \<open> Separation_Homo\<^sub>I Ft Fu Fc T U UNIV (\<lambda>x. x)
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U (\<lambda>x. x)
\<Longrightarrow> Fc (T \<^emph> U) = Ft T \<^emph> Fu U \<close>
  unfolding Separation_Homo\<^sub>I_def Separation_Homo\<^sub>E_def
  by (rule \<phi>Type_eqI_Tr ; simp add: split_paired_all)

lemma [\<phi>reason_template name Fc.\<phi>Prod_Cond []]:
  \<open> Separation_Homo\<^sub>I_Cond Ft Fu Fc C T U UNIV (\<lambda>x. x)
\<Longrightarrow> Separation_Homo\<^sub>E_Cond Ft Fu Fc C T U UNIV (\<lambda>x. x)
\<Longrightarrow> Fc (T \<^emph>[C] U) = Ft T \<^emph>[C] Fu U \<close>
  unfolding Separation_Homo\<^sub>I_Cond_def Separation_Homo\<^sub>E_Cond_def
  by (rule \<phi>Type_eqI_Tr ; simp add: split_paired_all)
 
lemma apply_conditioned_Separation_Functor_unzip:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U un)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Functional_Transformation_Functor Fc Ft (T \<^emph>[C] U) T D R pred_mapper func_mapper)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<and> \<not> C \<longrightarrow> fst a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph>[C] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then un x else (func_mapper fst (\<lambda>_. True) x, undefined)) \<Ztypecolon> Ft(T) \<^emph>[C] Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'[symmetric] Premise_def
  apply (cases C; simp)
  \<medium_left_bracket> premises FTF[] and [useful] and []
    apply_rule apply_Functional_Transformation_Functor[where f=\<open>fst\<close> and P=\<open>\<lambda>_. True\<close>, OF FTF]
    \<medium_left_bracket> ;; \<medium_right_bracket> ;;
  \<medium_right_bracket> .



lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>I_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>W \<Longrightarrow> Separation_Homo\<^sub>I Ft Fu F3 T U D z)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<Longrightarrow> Functional_Transformation_Functor Ft F3 T (T \<^emph>[C\<^sub>W] U) D' R' pred' func' )
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] DD : (if C\<^sub>W then D else {x. \<forall>a. a \<in> D' (fst x) \<longrightarrow> (a, undefined) \<in> R' (fst x)})) @action \<A>_template_reason
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] ZZ : (if C\<^sub>W then z else func' (\<lambda>x. (x, undefined)) (\<lambda>_. True) o fst)) @action \<A>_template_reason
\<Longrightarrow> Separation_Homo\<^sub>I_Cond Ft Fu F3 C\<^sub>W T U DD ZZ \<close>
  unfolding Separation_Homo\<^sub>I_Cond_def Separation_Homo\<^sub>I_def Premise_def Action_Tag_def Simplify_def
  by (cases C\<^sub>W; clarsimp;
      insert apply_Functional_Transformation_Functor
                [unfolded Argument_def Premise_def,
                  where Fa=Ft and Fb=F3 and func_mapper=func' and f=\<open>(\<lambda>x. (x, undefined))\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_. True\<close> and T=T and U=\<open>T \<^emph>[C\<^sub>W] U\<close> and
                        D=D' and R=R'];
      clarsimp;
      insert transformation_weaken; blast)


lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>E_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R \<Longrightarrow> Separation_Homo\<^sub>E Ft Fu F3 T U uz)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>R \<Longrightarrow> Functional_Transformation_Functor F3 Ft (T \<^emph>[C\<^sub>R] U) T D' R' pred' func' )
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] DD : (if C\<^sub>R then UNIV else {x. \<forall>(a,b) \<in> D' x. a \<in> R' x})) @action \<A>_template_reason
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] UZ : (if C\<^sub>R then uz else (\<lambda>x. (func' fst (\<lambda>_. True) x, undefined)))) @action \<A>_template_reason
\<Longrightarrow> Separation_Homo\<^sub>E_Cond Ft Fu F3 C\<^sub>R T U DD UZ \<close>
  unfolding Separation_Homo\<^sub>E_Cond_def Separation_Homo\<^sub>E_def Premise_def Action_Tag_def Simplify_def
  by (cases C\<^sub>R; clarsimp;
      insert apply_Functional_Transformation_Functor[unfolded Argument_def Premise_def,
                  where Fa=F3 and Fb=Ft and func_mapper=func' and f=\<open>fst\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_. True\<close> and U=T and T=\<open>T \<^emph>[C\<^sub>R] U\<close> and
                        D=D' and R=R'];
      clarsimp;
      metis (no_types, lifting) case_prodD transformation_weaken)



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

(*
paragraph \<open>\<open>Separation_Homo\<^sub>I\<close> for Non-semigroup\<close> \<comment> \<open>as they cannot be handled by stepwise rule and
                                                    therefore the NToA procedure\<close>
*)

(*
thm apply_Separation_Homo\<^sub>E[unfolded \<phi>Prod_expn''[simplified]]
declare apply_Separation_Homo\<^sub>E
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
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> Semimodule_Zero F T zero \<close>
  unfolding Closed_Semimodule_Zero_def Semimodule_Zero_def
  by simp

lemma [\<phi>reason_template name F.scalar_zero [assertion_simps, simp]]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> (x \<Ztypecolon> F zero T) = 1 \<close>
  unfolding Closed_Semimodule_Zero_def by blast

lemma [\<phi>reason_template name F.scalar_zero' [assertion_simps, simp]]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason
\<Longrightarrow> (x \<Ztypecolon> F zero' T) = 1 \<close>
  unfolding Closed_Semimodule_Zero_def Simplify_def Action_Tag_def
  by blast
 
lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Semimodule_Zero F T zero
\<Longrightarrow> NO_SIMP (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def
  using mk_elim_transformation by blast

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Semimodule_Zero F T zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason
\<Longrightarrow> NO_SIMP (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero' T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def Simplify_def Action_Tag_def
  using mk_elim_transformation by blast

lemma [\<phi>reason_template %ToA_derived_red ]:
  \<open> Semimodule_Zero F T zero
\<Longrightarrow> NO_SIMP (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F zero T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Semimodule_Zero_def NO_SIMP_def
  using transformation_bi_frame
  by fastforce

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Semimodule_Zero F T zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason
\<Longrightarrow> NO_SIMP (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F zero' T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Semimodule_Zero_def NO_SIMP_def Simplify_def Action_Tag_def
  using transformation_bi_frame
  by fastforce

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Semimodule_Zero F T zero
\<Longrightarrow> NO_SIMP (((), snd x) \<Ztypecolon> F zero T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def
  by (cases x; cases C; clarsimp)

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Semimodule_Zero F T zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason
\<Longrightarrow> NO_SIMP (((), snd x) \<Ztypecolon> F zero T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero' T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def Simplify_def Action_Tag_def
  by (cases x; cases C; clarsimp)

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero T \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by simp

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero' T \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by simp

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero' T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (any, snd x) \<Ztypecolon> F zero T \<^emph>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by (cases C; clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')

lemma [\<phi>reason_template %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F T zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (any, snd x) \<Ztypecolon> F zero' T \<^emph>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def Simplify_def Action_Tag_def
  by (cases C; clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')



paragraph \<open>Identity\<close>

subparagraph \<open>Reduction given by Elimination Rules\<close>

lemma [\<phi>reason_template name F.scalar_one_ty [assertion_simps, simp]]:
  \<open> Semimodule_Identity\<^sub>E F T one (\<lambda>_. True) (\<lambda>x. x)
\<Longrightarrow> F one T = T \<close>
  unfolding Semimodule_Identity\<^sub>E_def
  by (rule \<phi>Type_eqI_Tr; clarsimp)

lemma [\<phi>reason_template name F.scalar_one [assertion_simps, simp]]:
  \<open> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> D x
\<Longrightarrow> (x \<Ztypecolon> F one T) = (f x \<Ztypecolon> T) \<close>
  unfolding Semimodule_Identity\<^sub>E_def BI_eq_iff
  by clarsimp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (f x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F one T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (f x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F one' T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template no explorative backtrack %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (R * (f x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F one T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def
  by simp

lemma [\<phi>reason_template no explorative backtrack %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (R * (f x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F one' T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template no explorative backtrack %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D (fst x)
\<Longrightarrow> NO_SIMP (apfst f x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F one T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason_template no explorative backtrack %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D (fst x)
\<Longrightarrow> NO_SIMP (apfst f x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F one' T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one T \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Except_Pattern_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one' T \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one' T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D (fst x)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f x \<Ztypecolon> T \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one T \<^emph>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn')

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Identity\<^sub>E F T one D f
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D (fst x)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f x \<Ztypecolon> T \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one' T \<^emph>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn')


subparagraph \<open>Introduction\<close>

text \<open>When the source is in a semimodule operator \<open>F\<close> but the target is not, we can lift the target
  by injecting it into \<open>F one\<close>. The rule should must be of a low priority and applied after any tries
  of other semimdoule rules. The proof obligation \<open>D y\<close> can be strong? but is acceptable I think
  as long as being applied with the lowest priority.\<close>

lemma intro_Semimodule_template[no_atp, \<phi>reason_template default %derived_SE_inj_to_module]:
  \<open> Semimodule_Identity\<^sub>E F U one D f
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F F'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F F''
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F' s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (id one) U \<w>\<i>\<t>\<h> P) \<comment> \<open>protector \<open>id\<close> prevents the generated \<open>F one U\<close> reducing immediately\<close>
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D y
\<Longrightarrow> x \<Ztypecolon> F' s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
    <except-pattern> XX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yy \<Ztypecolon> F'' s'' U'' \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def Premise_def Except_Pattern_def
  by clarsimp


lemma [\<phi>reason_template default %derived_SE_inj_to_module]:
  \<open> Semimodule_Identity\<^sub>E F U one D f
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F F'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F F''
\<Longrightarrow> NO_SIMP (\<g>\<u>\<a>\<r>\<d> NO_MATCH (F'' s'' U'') U)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F' s T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (id one) U \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst y)
\<Longrightarrow> x \<Ztypecolon> F' s T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f y \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Semimodule_Identity\<^sub>E_def NO_SIMP_def Premise_def
  by (cases C; clarsimp simp add: \<phi>Prod_expn'')

text \<open>No rule in form \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _\<close> makes sense.\<close>


paragraph \<open>Extended Associative\<close>

lemma scalar_assoc_template[\<phi>reason_template name Fc.scalar_assoc [assertion_simps, simp]]:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt (\<lambda>_ _ _. True) smul (\<lambda>_ _ x. x)
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt (\<lambda>_ _ _. True) smul (\<lambda>_ _ x. x)
\<Longrightarrow> Ds s \<and> Dt t
\<Longrightarrow> Fs s (Ft t T) = Fc (smul s t) T \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Semimodule_Scalar_Assoc\<^sub>I_def
  by (rule \<phi>Type_eqI_Tr; simp)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (f s t x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> Fs s (Ft t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding NO_SIMP_def Semimodule_Scalar_Assoc\<^sub>I_def \<r>Guard_def Premise_def
  using mk_elim_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (R * (f s t x \<Ztypecolon> Fc (smul s t) T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> Fs s (Ft t T)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Premise_def NO_SIMP_def \<r>Guard_def
  using transformation_left_frame mk_elim_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fc (smul s t) T \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fs s (Ft t T) \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def NO_SIMP_def \<r>Guard_def
  using mk_intro_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fc (smul s t) T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fs s (Ft t T) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def NO_SIMP_def \<r>Guard_def
  apply (cases C; simp)
  using transformation_left_frame mk_intro_transformation apply blast
  using mk_intro_transformation by blast

(*
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
*)

paragraph \<open>Left Distributivity\<close>


lemma [\<phi>reason_template name F.unfold_sdistr[]]:
  \<open> Semimodule_SDistr_Homo\<^sub>U F T Ds Du uz
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dz zi
\<Longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Du t s x \<and> Dz t s (uz t s x) \<and>
    zi t s (uz t s x) = x
\<Longrightarrow> (x \<Ztypecolon> F (s + t) T) = (uz t s x \<Ztypecolon> F t T \<^emph> F s T) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Semimodule_SDistr_Homo\<^sub>U_def
  by (rule assertion_eq_intro; clarsimp simp del: split_paired_All; metis)


subparagraph \<open>Zip\<close>

lemma SDirst_in_comm_scalar_implies_rev\<^sub>Z
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F T Ds Dx z Dx z\<close>
  for F :: \<open>('s::partial_ab_semigroup_add \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Semimodule_SDistr_Homo\<^sub>Z_def
  by (simp add: dom_of_add_commute partial_add_commute)

lemma SDirst_in_comm_sep_implies_rev\<^sub>Z
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice-1,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F T Ds Dx z (\<lambda>s t. Dx t s o prod.swap) (\<lambda>s t. z t s o prod.swap)\<close>
  for F :: \<open>('s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Semimodule_SDistr_Homo\<^sub>Z_def
  by (simp add: \<phi>Prod_expn'; metis mult.commute)


subparagraph \<open>Unzip\<close>

lemma SDirst_in_comm_scalar_implies_rev\<^sub>U
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>U F T Ds Dx uz
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U_rev F T Ds Dx uz Dx uz\<close>
  for F :: \<open>('s::partial_ab_semigroup_add \<Rightarrow> ('c::sep_magma,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_rev_def Semimodule_SDistr_Homo\<^sub>U_def
  by (simp add: dom_of_add_commute partial_add_commute)

lemma SDirst_in_comm_sep_implies_rev\<^sub>U
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice-1,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>U F T Ds Dx z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U_rev F T Ds Dx uz (\<lambda>s t. Dx t s) (\<lambda>s t. prod.swap o z t s)\<close>
  for F :: \<open>('s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_rev_def Semimodule_SDistr_Homo\<^sub>U_def
  by (clarsimp simp add: \<phi>Prod_expn'' mult.commute)


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
    apply_rule apply_Separation_Homo\<^sub>I[where Fu=F4 and Ft=F1]
    apply_rule functional_transformation[where U=\<open>U \<^emph> R\<close> and f=\<open>f\<close> and P=\<open>P\<close>]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_Separation_Homo\<^sub>E
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

 




lemma "_Structural_Extract_general_rule_i_"[\<phi>reason_template default %derived_SE_functor]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F14 F23 (T \<^emph>[Cw] W) (U \<^emph>[Cr] R) Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>I_Cond F1 F4 F14 Cw T W Dz z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>E_Cond F3 F2 F23 Cr U R Du uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x)) \<and> func_mapper f P (z x) \<in> Du
\<Longrightarrow> (\<And>a \<in> Dom (z x). a \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P a )
\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph>[Cw] F4 W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f P (z x)) \<Ztypecolon> F3 U \<^emph>[Cr] F2 R
    \<w>\<i>\<t>\<h> pred_mapper f P (z x) \<close>
  unfolding \<r>Guard_def
  \<medium_left_bracket> premises FTF[] and SH\<^sub>I[] and SH\<^sub>E[] and _ and Tr
    apply_rule apply_Separation_Homo\<^sub>I_Cond[where Fu=F4 and Ft=F1, OF SH\<^sub>I]
    apply_rule apply_Functional_Transformation_Functor[where U=\<open>U \<^emph>[Cr] R\<close> and f=\<open>f\<close> and P=\<open>P\<close>, OF FTF]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>E_Cond[OF SH\<^sub>E]
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
    apply_rule apply_Separation_Homo\<^sub>I[where Fu=F4 and Ft=F1]
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
    apply_rule apply_Separation_Homo\<^sub>I[where Fu=F4 and Ft=F1]
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
    apply_rule apply_Separation_Homo\<^sub>I[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
    apply_rule functional_transformation[where U=\<open>F3 c U \<^emph> R\<close> and f=f and P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>E[where x=\<open>func_mapper f P (z x)\<close>]
    fold F3D
  \<medium_right_bracket> .

declare SE_general_Semimodule_Scalar_left[THEN \<A>SE_clean_waste, \<phi>reason_template default 30]
  \<comment> \<open>The priority is smaller than the default rule of functional transformation\<close>
*)

lemma force_unfold_apfst:
  \<open>apfst f x = (f (fst x), snd x)\<close>
  by (cases x; simp)

lemma force_unfold_apsnd:
  \<open>apsnd f x = (fst x, f (snd x))\<close>
  by (cases x; simp)

 
lemma SE_general_Semimodule_Scalar_left_b: (*need test, to be tested once we have usable test case*)
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> smul a c = b)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Functional_Transformation_Functor F14 F23 (T \<^emph>[Cw] W) (F3\<^sub>c c U \<^emph>[Cr] R) Dom Rng pred_mapper func_mapper
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I F3\<^sub>a F3\<^sub>c F3\<^sub>b U D\<^sub>a D\<^sub>c D\<^sub>x smul g\<^sub>s
\<Longrightarrow> Separation_Homo\<^sub>I_Cond (F1 a) (F4 a) F14 Cw T W Dz z
\<Longrightarrow> Separation_Homo\<^sub>E_Cond (F3\<^sub>a a) (F2 a) F23 Cr (F3\<^sub>c c U) R Du uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x)) \<and>
           func_mapper f P (z x) \<in> Du \<and>
           D\<^sub>x a c (fst (uz (func_mapper f P (z x))))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3\<^sub>c c U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P x )
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] F4 a W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst (g\<^sub>s a c) (uz (func_mapper f P (z x))) \<Ztypecolon> F3\<^sub>b b U \<^emph>[Cr] F2 a R
    \<w>\<i>\<t>\<h> pred_mapper f P (z x) \<close>
  unfolding \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and FTF and SA and SH\<^sub>I and SH\<^sub>E and _ and Tr
   ;; apply_rule apply_Separation_Homo\<^sub>I_Cond[OF SH\<^sub>I]
    apply_rule apply_Functional_Transformation_Functor[where f=f and P=P, OF FTF]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>E_Cond[OF SH\<^sub>E]
    apply_rule apply_Semimodule_SAssoc\<^sub>I[OF SA, THEN transformation_right_frame_conditioned_ty]
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
    apply_rule apply_Separation_Homo\<^sub>I[where Fu=\<open>F4 a\<close> and Ft=\<open>F1 a\<close>]
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
lemma SE_Semimodule_SDistr_da_bc[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> b ##\<^sub>+ c \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, fst (snd x)) \<and> Dx  b c (z d a (fst x, fst (snd x)))
\<Longrightarrow> (snd (uz b c (z d a (fst x, fst (snd x)))), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, fst (uz b c (z d a (fst x, fst (snd x)))), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where t=c and s=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.*)
lemma SE_Semimodule_SDistr_ad_cb[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d (fst (snd x), fst x) \<and> Dx  c b (z a d (fst (snd x), fst x))
\<Longrightarrow> (fst (uz c b (z a d (fst (snd x), fst x))), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz c b (z a d (fst (snd x), fst x))), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where t=d and s=a and F=F1 and x=\<open>(fst (snd x), fst x)\<close>]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where t=b and s=c and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma SE_Semimodule_SDistr_a_dbc[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx (d + b) c (fst x) \<and> Dx d b (snd (uz (d + b) c (fst x)))
\<Longrightarrow> (fst (uz d b (snd (uz (d + b) c (fst x)))), snd x) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz d b (snd (uz (d + b) c (fst x)))), fst (uz (d + b) c (fst x)), snd y) \<Ztypecolon> F3 b U \<^emph> F1 d T \<^emph> F1 c T \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where s=\<open>d + b\<close> and t=c and F=F1, folded a]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c. *)
lemma SE_Semimodule_SDistr_dac_b[\<phi>reason_template default 35]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + a) \<and> Ds c \<and> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, fst (snd x)) \<and> Dx (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x)))
\<Longrightarrow> (z (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x))), snd (snd (snd x))) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> F1 c T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where s=d and t=a and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(fst (snd (snd x)), z d a (fst x, fst (snd x)))\<close>]
    Tr
  \<medium_right_bracket> .

(*DONE*)

paragraph \<open>Commutative, Monoidal, No Additive Zero\<close>

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative *)
lemma SE_Semimodule_SDistr_da_b[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, fst (snd x))
\<Longrightarrow> (z d a (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(* [--------a---------]
   [-----b-----][--c--]
   Give a, expect b; Remain c, d = 0. *)
lemma SE_Semimodule_SDistr_a_bc[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), snd x) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz b c (fst x)), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where t=c and s=b and F=F1, folded a]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative *)
lemma SE_Semimodule_SDistr_ad_b[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, fst (snd x))
\<Longrightarrow> (uz a d (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev[where s=a and t=d and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b; Remain c, d = 0.*)
lemma SE_Semimodule_SDistr_a_cb[\<phi>reason_template default 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b (fst x)
\<Longrightarrow> (fst (uz c b (fst x)), snd x) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd (uz c b (fst x)), snd y) \<Ztypecolon> F3 b U \<^emph> (F1 c T \<^emph> R) \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where t=b and s=c and F=F1, folded a]
    Tr
  \<medium_right_bracket> .

(*DONE*)

paragraph \<open>Non-Commutative, Monoidal, Additive Zero\<close>

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.*)
lemma SE_Semimodule_SDistr_da_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> b ##\<^sub>+ c \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a x \<and> Dx  b c (z d a x)
\<Longrightarrow> (fst (uz b c (z d a x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz b c (z d a x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=x]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where t=c and s=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.*)
lemma SE_Semimodule_SDistr_ad_cb_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d x \<and> Dx c b (z a d x)
\<Longrightarrow> (fst (uz c b (z a d x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz c b (z a d x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding \<r>Guard_def Action_Tag_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev[where t=d and s=a and F=F1 and x=x]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where t=b and s=c and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma SE_Semimodule_SDistr_a_dbc_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx' uz'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' (d + b) c (fst x) \<and> Dx d b (fst (uz' (d + b) c (fst x)))
\<Longrightarrow> (fst (uz d b (fst (uz' (d + b) c (fst x)))), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz d b (fst (uz' (d + b) c (fst x)))), snd (uz' (d + b) c (fst x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 d T \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where s=\<open>d + b\<close> and t=c and F=F1, folded a]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c. *)
lemma SE_Semimodule_SDistr_dac_b_nc[\<phi>reason_template 34]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx' z'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds (d + a) \<and> Ds c \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, fst (snd x)) \<and> Dx' (d + a) c (z d a (fst x, fst (snd x)), snd (snd x))
\<Longrightarrow> (z' (d + a) c (z d a (fst x, fst (snd x)), snd (snd x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> F1 c T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where s=d and t=a and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(z d a (fst x, fst (snd x)), snd (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(*DONE*)

paragraph \<open>Non-Commutative, Monoidal, No Additive Zero\<close>

(* [--------a---------]
   [-----b-----][--c--]
   Give a, expect b; Remain c, d = 0. *)
lemma SE_Semimodule_SDistr_a_bc_nc[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz b c (fst x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where t=c and s=b and F=F1, folded a]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b; Remain c, d = 0.*)
lemma SE_Semimodule_SDistr_a_cb_nc[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b (fst x)
\<Longrightarrow> (fst (uz c b (fst x)), ()) \<Ztypecolon> F1 b T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, snd y, snd (uz c b (fst x))) \<Ztypecolon> F3 b U \<^emph> R \<^emph> F1 c T \<w>\<i>\<t>\<h> P @action \<A>SE \<close>
  for R :: \<open>('c::sep_monoid,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where t=b and s=c and F=F1, folded a]
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
   d, c \<noteq> 0; the scalar has to be non-commutative, otherwise reduces to either \<open>SE_Semimodule_SDistr_da_b_i\<close> or \<open>SE_Semimodule_SDistr_a_cb_i\<close>*)
lemma SE_Semimodule_SDistr_da_bc_i
      [where Cw' = True, \<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d (fst x, x\<^sub>d) \<and> Dx c b (z a d (fst x, x\<^sub>d))
\<Longrightarrow> (snd (uz c b (z a d (fst x, x\<^sub>d))), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> ((fst (uz c b (z a d (fst x, x\<^sub>d))), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr and [simp] and b
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F1 and x=\<open>(fst x,x\<^sub>d)\<close>]
       apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some[where t=c and s=b and F=F1]
       Tr
       b
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; the scalar has to be non-commutative, otherwise reduces to either \<open>SE_Semimodule_SDistr_da_b_i\<close> or \<open>SE_Semimodule_SDistr_a_cb_i\<close>*)
lemma SE_Semimodule_SDistr_ad_cb_i
      [where Cw' = True, \<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (x\<^sub>d, fst x) \<and> Dx b c (z d a (x\<^sub>d, fst x))
\<Longrightarrow> (fst (uz b c (z d a (x\<^sub>d, fst x))), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> ((snd (uz b c (z d a (x\<^sub>d, fst x))), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr and [simp] and b
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=d and s=a and F=F1 and x=\<open>(x\<^sub>d, fst x)\<close>]
       apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some[where t=b and s=c and F=F1]
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
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise go \<open>SE_Semimodule_SDistr_a_cb_i\<close>*) 
lemma SE_Semimodule_SDistr_a_dbc_i
      [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id d + id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Dx c (d + b) (fst x)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds d \<and> Ds b \<and> d ##\<^sub>+ b \<and> Dx b d (snd (uz c (d + b) (fst x)))
\<Longrightarrow> (fst (uz b d (snd (uz c (d + b) (fst x)))), snd x) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd (uz b d (snd (uz c (d + b) (fst x)))), fst (uz c (d + b) (fst x)), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R)
      = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr and b
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some[where s=\<open>d + b\<close> and t=c and F=F1]
       apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some[where s=\<open>d\<close> and t=b and F=F1]
       Tr
       b (*simplify the abstract object during reasoning*)
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Semimodule_SDistr_da_b_i\<close> *)
lemma SE_Semimodule_SDistr_dac_b_i
      [where Cw'=True, \<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a + id c = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + a) \<and> Ds c \<and> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, x\<^sub>d) \<and> Dx c (d + a) (x\<^sub>c, z a d (fst x, x\<^sub>d))
\<Longrightarrow> (z c (d + a) (x\<^sub>c, z a d (fst x, x\<^sub>d)), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, x\<^sub>c, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P\<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where s=d and t=a and F=F1 and x=\<open>(fst x, x\<^sub>d)\<close>]
       apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(x\<^sub>c, z a d (fst x, x\<^sub>d))\<close>]
       Tr
  \<medium_right_bracket> .

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative separation algebra. d \<noteq> 0
   All problems on semimodules of commutative scalars (and associative separation algebra) reduces to
    \<open>SE_Semimodule_SDistr_da_b_i\<close> and \<open>SE_Semimodule_SDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_SDistr_da_b_i
      [where Cw'=True, \<phi>reason_template default %derived_SE_sdistr_comm]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d (fst x, x\<^sub>d)
\<Longrightarrow> (z a d (fst x, x\<^sub>d), w) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F1 and x=\<open>(fst x, x\<^sub>d)\<close>]
       Tr
  \<medium_right_bracket> .

(* [--------a---------]
   [-----b-----][--c--]
   Give a, expect b; Remain c, d = 0.
   c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_SDistr_a_cb_i\<close>*)
lemma SE_Semimodule_SDistr_a_bc_i
  [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx' uz'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx' uz' Dx uz
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
  \<medium_left_bracket> premises a and SD\<^sub>U[] and SD\<^sub>U_rev[] and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev_\<phi>Some[where t=c and s=b and F=F1, OF SD\<^sub>U SD\<^sub>U_rev]
    Tr
    b
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative separation algebra.
   d \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_SDistr_da_b_i\<close>
*)
lemma SE_Semimodule_SDistr_ad_b_i
      [where Cw' = True, \<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' uz'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx' uz' Dx uz
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
  \<medium_left_bracket> premises [simp] and SD\<^sub>Z[] and SD\<^sub>Z_rev[] and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev_\<phi>Some[where s=a and t=d and F=F1 and x=\<open>(fst x, x\<^sub>d)\<close>, OF SD\<^sub>Z SD\<^sub>Z_rev]
       Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b; Remain c, d = 0. c \<noteq> 0
   All problems on semimodules of commutative scalars (and associative separation algebra) reduces to
    \<open>SE_Semimodule_SDistr_da_b_i\<close> and \<open>SE_Semimodule_SDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_SDistr_a_cb_i[\<phi>reason_template default %derived_SE_sdistr_comm]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), snd x) \<Ztypecolon> F1 b T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd (uz b c (fst x)), snd y) \<Ztypecolon> \<half_blkcirc>[True] F1 c T \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises a and _ and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some[where t=b and s=c and F=F1]
    Tr
    b
  \<medium_right_bracket> .


(*Done*)

paragraph \<open>Non-Commutative, Non-Unital Associative, No Additive Zero\<close>

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to either
             \<open>SE_Semimodule_SDistr_da_b_i\<close> or \<open>SE_Semimodule_SDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_SDistr_da_nc_i
      [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx\<^sub>o uz\<^sub>o
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx\<^sub>o uz\<^sub>o Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> b ##\<^sub>+ c \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d x \<and> Dx b c (z a d x)
\<Longrightarrow> (fst (uz b c (z a d x)), undefined) \<Ztypecolon> F1 b T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd y, snd (uz b c (z a d x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F1 c T) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close> 
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises [simp] and SD\<^sub>U[] and SD\<^sub>U_rev[] and SD\<^sub>Z[] and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F1 and x=x, OF SD\<^sub>Z]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev_\<phi>Some[where t=c and s=b and F=F1, OF SD\<^sub>U SD\<^sub>U_rev]
    Tr
    apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to either
             \<open>SE_Semimodule_SDistr_da_b_i\<close> or \<open>SE_Semimodule_SDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_SDistr_ad_cb_nc_i
      [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx'\<^sub>o z\<^sub>o
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx'\<^sub>o z\<^sub>o Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d \<and> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d x \<and> Dx b c (z a d x)
\<Longrightarrow> (fst (uz b c (z a d x)), undefined) \<Ztypecolon> F1 b T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd y, snd (uz b c (z a d x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F1 c T) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises [simp] and SD\<^sub>U[] and SD\<^sub>Z[] and SD\<^sub>Z_rev[] and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev_\<phi>Some[where t=d and s=a and F=F1 and x=x, OF SD\<^sub>Z SD\<^sub>Z_rev]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some[where t=b and s=c and F=F1, OF SD\<^sub>U]
    Tr
    apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_SDistr_da_b_i\<close>
*)
lemma SE_Semimodule_SDistr_a_dbc_nc_i
      [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id d + id b + id c @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx uz Dx' uz'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + b) \<and> Ds c \<and> d + b ##\<^sub>+ c \<and> Ds d \<and> Ds b \<and> d ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' (d + b) c (fst x) \<and> Dx b d (fst (uz' (d + b) c (fst x)))
\<Longrightarrow> (fst (uz b d (fst (uz' (d + b) c (fst x)))), ()) \<Ztypecolon> F1 b T \<^emph>[False] \<top> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd y, snd (uz b d (fst (uz' (d + b) c (fst x)))), snd (uz' (d + b) c (fst x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F1 d T \<^emph> \<half_blkcirc>[True] F1 c T)
      = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[False] \<top> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F3 b U \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises _ and _ and _ and _ and _ and _ and Tr and b
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev_\<phi>Some[where s=\<open>d + b\<close> and t=c and F=F1]
       apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_\<phi>Some[where s=\<open>d\<close> and t=b and F=F1]
       Tr
       apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Semimodule_SDistr_a_cb_i\<close>
*)
lemma SE_Semimodule_SDistr_dac_b_nc_i
      [\<phi>reason_template default %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a + id c = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx z Dx' z'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds (d + a) \<and> Ds c \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, fst (snd x)) \<and> Dx' (d + a) c (z a d (fst x, fst (snd x)), snd (snd x))
\<Longrightarrow> (z' (d + a) c (z a d (fst x, fst (snd x)), snd (snd x)), ()) \<Ztypecolon> F1 b T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] (F1 d T \<^emph> F1 c T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr
    note \<phi>Some_\<phi>Prod[symmetric, simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where s=d and t=a and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
       apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev_\<phi>Some[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(z a d (fst x, fst (snd x)), snd (snd x))\<close>]
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
lemma SE_Semimodule_SDistr_da_b_na[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a x
\<Longrightarrow> z d a x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=x]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0.
*)
lemma SE_Semimodule_SDistr_ad_b_na[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d x
\<Longrightarrow> uz a d x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev[where s=a and t=d and F=F1 and x=x]
    Tr
  \<medium_right_bracket> .


subparagraph \<open>Assuming associativity, allowing further demand in the element transformation\<close>

text \<open>Has Additive Zero\<close>

(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c. *)
lemma SE_Semimodule_SDistr_dac_b_nc_na_W[\<phi>reason_template 38]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds (d + a) \<and> Ds c \<and> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx d a (fst x, fst (snd x)) \<and> Dx (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x)))
\<Longrightarrow> (z (d + a) c (fst (snd (snd x)), z d a (fst x, fst (snd x))), snd (snd (snd x))) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> F1 c T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket>  premises [simp] and _ and _ and _ and _ and Tr
     apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where s=d and t=a and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
     apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where s=\<open>d+a\<close> and t=c and F=F1 and x=\<open>(fst (snd (snd x)), z d a (fst x, fst (snd x)))\<close>]
     Tr
  \<medium_right_bracket> .


text \<open>No Additive Zero\<close>

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0. *)
lemma SE_Semimodule_SDistr_da_b_na_W[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (fst x, fst (snd x))
\<Longrightarrow> (z d a (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where t=a and s=d and F=F1 and x=\<open>(fst x,fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0. *)
lemma SE_Semimodule_SDistr_ad_b_na_W[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, fst (snd x))
\<Longrightarrow> (uz a d (fst x, fst (snd x)), snd (snd x)) \<Ztypecolon> F1 b T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph> F1 d T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P @action \<A>SEa \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev[where s=a and t=d and F=F1 and x=\<open>(fst x, fst (snd x))\<close>]
    Tr
  \<medium_right_bracket> .
*)

paragraph \<open>Assuming no algebraic property supporting even non-associative group,
  and as a consequence allowing no remainder and subsequent target in the element transformation\<close>

(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b, remain d. c \<noteq> 0
*)
lemma SE_Semimodule_SDistr_a_cb_noassoc[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id c + id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> fst (uz b c (fst x)) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, snd (uz b c (fst x))) \<Ztypecolon> F3 b U \<^emph>[True] F1 c T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where s=\<open>c\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
   d \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Semimodule_SDistr_a_cb_noassoc\<close>
*)
lemma SE_Semimodule_SDistr_a_bd_Tr
      [\<phi>reason_template default %derived_SE_sdistr_noassoc pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id b + id d @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx\<^sub>o uz\<^sub>o
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx\<^sub>o uz\<^sub>o Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> b ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b d (fst x)
\<Longrightarrow> fst (uz b d (fst x)) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz b d (fst x)) \<Ztypecolon> F1 d T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and SD\<^sub>U[] and SD\<^sub>U_rev[] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where s=\<open>b\<close> and t=d and F=F1, OF SD\<^sub>U SD\<^sub>U_rev]
    Tr
  \<medium_right_bracket> .

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b, remain d. c \<noteq> 0
*)
lemma SE_Semimodule_SDistr_da_b_noassoc[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d x
\<Longrightarrow> z a d x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, undefined) \<Ztypecolon> F3 b U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where s=\<open>d\<close> and t=a and F=F1]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [---------b--------]
   Give a, expect b, remain d.
   d \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Semimodule_SDistr_da_b_noassoc\<close>
*)
lemma SE_Semimodule_SDistr_ad_b_noassoc
      [\<phi>reason_template default %derived_SE_sdistr_noassoc pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id b @action \<A>arith_eval)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 T Ds Dx\<^sub>o z\<^sub>o
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 T Ds Dx\<^sub>o z\<^sub>o Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d x
\<Longrightarrow> z a d x \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[True] F1 d T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, undefined) \<Ztypecolon> F3 b U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def
  \<medium_left_bracket> premises [simp] and SD\<^sub>Z[] and SD\<^sub>Z_rev[] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev[where s=\<open>a\<close> and t=d and F=F1, OF SD\<^sub>Z SD\<^sub>Z_rev]
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
lemma SE_Semimodule_SDistr_a_db_Tr[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = c + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b x
\<Longrightarrow> fst (uz c b x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz c b x) \<Ztypecolon> F1 c T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where s=\<open>c\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
*)
lemma SE_Semimodule_SDistr_a_bd_Tr[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + d @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> b ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b d x
\<Longrightarrow> fst (uz b d x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz b d x) \<Ztypecolon> F1 d T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where s=\<open>b\<close> and t=d and F=F1]
    Tr
  \<medium_right_bracket> .

paragraph \<open>Assuming associativity, allowing remainders\<close>

subparagraph \<open>Has Additive Zero\<close>

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma SE_Semimodule_SDistr_a_dbc_Tr_R[\<phi>reason_template 33]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b + c @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx' uz'
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
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where s=\<open>d + b\<close> and t=c and F=F1, folded a]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

subparagraph \<open>No Additive Zero\<close>

(* [---------a--------]
   [--d--][-----b-----]
   Give a, expect b, remain d.
   Assuming associativity, allow R
*)
lemma SE_Semimodule_SDistr_a_db_Tr_R[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U F1 T Ds Dx uz
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
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U[where s=\<open>d\<close> and t=b and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
   Assuming associativity, allow R
*)
lemma SE_Semimodule_SDistr_a_bd_Tr_R[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + d @action \<A>arith_eval
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>U_rev F1 T Ds Dx uz
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
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>U_rev[where s=\<open>b\<close> and t=d and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

(*DONE*)

(*The dual of the above rules is \<A>SEa*)
*)


subsubsection \<open>Commutativity between \<phi>-Type Operators\<close>

(*TODO Tyops_Commute\<^sub>1\<^sub>_\<^sub>2*)

paragraph \<open>Implies Rewrites\<close>
 
lemma Comm_Tyops_Rewr_temlpate[\<phi>reason_template name F.G.comm_rewr[]]:
  \<open> Tyops_Commute F F' G G' T D (embedded_func f P)
\<Longrightarrow> Tyops_Commute G' G F' F T D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (g (f x) = x) \<and> D x \<and> D' (f x)
\<Longrightarrow> (x \<Ztypecolon> F (G T)) = (f x \<Ztypecolon> G' (F' T)) \<close>
  unfolding Tyops_Commute_def Premise_def Transformation_def BI_eq_iff
  by clarsimp metis

lemma Comm_Tyops_Rewr\<^sub>2_temlpate[\<phi>reason_template name F.G.comm_rewr[]]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D (embedded_func f P)
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> g (f x) = x \<and> D x \<and> D' (f x)
\<Longrightarrow> (x \<Ztypecolon> F (G T U)) = (f x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U)) \<close>
  unfolding BI_eq_iff Premise_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Transformation_def
  by clarsimp metis


paragraph \<open>Bubbling\<close>

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (r' y) : r x y) @action \<A>_template_reason)
\<Longrightarrow> x \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (F' T) \<s>\<u>\<b>\<j> y. r' y @action \<A>simp \<close>
  unfolding Tyops_Commute_def Premise_def Action_Tag_def Bubbling_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (r' y) : r x y) @action \<A>_template_reason)
\<Longrightarrow> x \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (F'\<^sub>T T) (F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r' y @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Action_Tag_def Bubbling_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (r' y) : r x y) @action \<A>_template_reason)
\<Longrightarrow> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<s>\<u>\<b>\<j> y. r' y @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Action_Tag_def Bubbling_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (r' y) : r x y) @action \<A>_template_reason)
\<Longrightarrow> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<s>\<u>\<b>\<j> y. r' y @action \<A>simp
    <except-pattern> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YYY @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Action_Tag_def Bubbling_def Except_Pattern_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (r' y) : r x y) @action \<A>_template_reason)
\<Longrightarrow> x \<Ztypecolon> G' (F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<s>\<u>\<b>\<j> y. r' y @action \<A>simp
    <except-pattern> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YYY @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Action_Tag_def Bubbling_def Except_Pattern_def Simplify_def \<r>Guard_def
  by clarsimp


paragraph \<open>To-Transformation Interpreter\<close>

lemma [\<phi>reason_template %To_ToA_derived]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (r' y) : r x y) @action \<A>_template_reason)
\<Longrightarrow> x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r' y @action to (\<c>\<o>\<m>\<m>\<u>\<t>\<e> F G) \<close>
  unfolding Tyops_Commute_def Premise_def Action_Tag_def Except_Pattern_def Simplify_def \<r>Guard_def
  by clarsimp


subsection \<open>Property Derivers\<close>

subsubsection \<open>Extension of BNF-FP\<close>

ML_file \<open>library/phi_type_algebra/tools/BNF_fp_sugar_more.ML\<close>
ML_file \<open>library/phi_type_algebra/tools/extended_BNF_info.ML\<close>


subsubsection \<open>Extending the Guessing of Property\<close>

text \<open>When derivers provide gussers of specific strategies typically based on the logic types of the
  abstract domain, boolean constraints implies inside can in addition augment the guessing.
  The section aims to provide a general mechanism syntactically extracting the constraints.

  The extraction works in two modes,
  \<^item> covariant, where the boolean constraints are proof obligations have to be shown, and the \<phi>-type
      typically locates at the right hand side of a transformation;
  \<^item> contra-variant, where the constraints are conditions constraining the proof obligations, and the
      \<phi>-type typically locates at the left hand side of a transformation.
\<close>



  \<comment> \<open>A general mechanism to provide user heuristics which guesses the entire property
      of some specific forms of \<phi>-types\<close>

text \<open>When guessing the property, the system first tries to see if there is any user overridings
  by \<open>Guess_Property\<close> reasoning which gives the desired property entirely, if not, it goes to the normal
  guesser procedure implemented by each deriver, and after obtaining the guessed property,
  the system runs the \<open>Guess_Property\<close> again with the \<open>guessed_conclusion\<close> setting to None to force
  guessing the antecedents only, in this way to refine the already guessed antecedent either by
  adding new antecedents or constraining the antecedents by conditions.\<close>

type_synonym variant = bool \<comment>\<open>True for covariant, False for contravariant, undefined for invariant\<close>

(*
definition Guess_Property :: \<open>'property_const \<Rightarrow> variant \<Rightarrow> 'a BI \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Guess_Property the_constant_of_the_property_predicate \<comment> \<open>gives which sort of properties we are guessing\<close>
                        variantness_of_the_property
                        unfolded_\<phi>type_definition
                        guessed_antecedents         guessed_proof_obligation
                        conditions_of_antecedents   conditions_of_obligation
          \<equiv> True\<close>*)

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

\<phi>reasoner_group \<phi>TA_guesser = (100, [80, 2999]) for \<open>Guess_Property PC V A a c C\<close>
    \<open>User heuristics overriding or extending the guesser mechanism of \<phi>type derivers.\<close>
 and \<phi>TA_guesser_init = (3000, [3000, 3000]) for \<open>Guess_Property PC V A a c C\<close> > \<phi>TA_guesser
    \<open>Initializing the Guessing\<close>
 and \<phi>TA_guesser_default = (30, [2, 79]) for \<open>Guess_Property PC V A a c C\<close> < \<phi>TA_guesser
    \<open>Default rules handling logical connectives\<close>
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
       \<phi>TA_ANT :: action \<comment> \<open>Antecedent in the outcome\<close>
       \<phi>TA_conditioned_ToA_template :: action
       \<phi>TA_pure_facts :: action \<comment> \<open>About \<open>\<phi>TA_conditioned_ToA_template\<close> and \<open>\<phi>TA_pure_facts\<close>,
                                    see comments in \<^file>\<open>library/phi_type_algebra/deriver_framework.ML\<close>
                                    ML function \<open>default_reasoning_configure\<close>\<close>

lemmas intro_\<phi>TA_ANT = Action_Tag_def[where A=\<open>\<phi>TA_ANT\<close>, symmetric, THEN Meson.TruepropI]

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
  by (cases C; simp add: transformation_left_frame transformation_trans)

lemma [fundef_cong]:
  \<open>T x = T' x' \<Longrightarrow> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')\<close>
  unfolding \<phi>Type_def by simp

lemma \<phi>TA_ind_target_strip:
  \<open> X @action \<phi>TA_ind_target \<A> \<equiv> X @action \<A> \<close>
  unfolding Action_Tag_def .

(*TODO: rename Action_Tag \<longrightarrow> Reasoning_Tag, @action \<rightarrow> @tag*)

lemma \<phi>TA_common_rewr_imp1:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_ind_target A) \<equiv> (Ant \<Longrightarrow> X @action A) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp1_noact:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_ind_target A) \<equiv> (Ant \<Longrightarrow> X) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp2_noact:
  \<open> Trueprop (Ant \<longrightarrow> C \<longrightarrow> X @action \<phi>TA_ind_target A) \<equiv> (Ant \<Longrightarrow> C \<Longrightarrow> X) \<close>
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

consts \<phi>deriver_expansion :: mode

\<phi>reasoner_ML \<phi>deriver_expansion %cutting
  (\<open>Premise \<phi>deriver_expansion _\<close> | \<open>Simplify \<phi>deriver_expansion ?X' ?X\<close> )
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier_by_ss' (K Seq.empty)
        Phi_Type_Algebra_Derivers.Expansion.get' true) o snd\<close>



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
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Abstract_Domain T P\<close>
  unfolding Action_Tag_def Abstract_Domain_def
  by simp

lemma \<phi>TA_SuC_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow> P x \<longrightarrow> Inhabited (x \<Ztypecolon> T) @action \<phi>TA_ind_target \<A>ESC)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
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



ML_file \<open>library/phi_type_algebra/implication.ML\<close>

(*hide_fact \<phi>TA_Inh_rule \<phi>TA_Inh_rewr \<phi>TA_Inh_step*)

\<phi>property_deriver Abstract_Domain\<^sub>L 89 for ( \<open>Abstract_Domain\<^sub>L _ _\<close> ) = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain_L
\<close>

\<phi>property_deriver Abstract_Domain 90 for ( \<open>Abstract_Domain _ _\<close> ) = \<open>
  Phi_Type_Algebra_Derivers.abstract_domain
\<close>



subsubsection \<open>Identity Element Intro \& Elim\<close>

lemma \<phi>TA_1L_rule:
  \<open> (\<And>x. Ant \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x \<longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Identity_Elements\<^sub>I T D P \<close>
  unfolding Action_Tag_def Identity_Elements\<^sub>I_def
  by blast


(*lemma \<phi>TA_1L_rule':
  \<open> (Ant \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) P\<close>
  unfolding Action_Tag_def Identity_Element\<^sub>I_def Premise_def
  using transformation_weaken by blast*)

lemma \<phi>TA_1R_rule:
  \<open> (\<And>x. Ant \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x \<longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Identity_Elements\<^sub>E T D\<close>
  unfolding Action_Tag_def Identity_Elements\<^sub>E_def
  by blast

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

\<phi>property_deriver Identity_Elements\<^sub>I 101 for (\<open>Identity_Elements\<^sub>I _ _ _\<close>)
    requires Warn_if_contains_Sat
  = \<open>Phi_Type_Algebra_Derivers.identity_element_I\<close>

\<phi>property_deriver Identity_Elements\<^sub>E 102 for (\<open>Identity_Elements\<^sub>E _ _\<close>)
    requires Warn_if_contains_Sat
  = \<open>Phi_Type_Algebra_Derivers.identity_element_E\<close>

\<phi>property_deriver Identity_Elements 103
  requires Identity_Elements\<^sub>I and Identity_Elements\<^sub>E



paragraph \<open>Guessing Antecedents\<close>

(*TODO:
declare Is_Contravariant[where PC=\<open>Identity_Element\<^sub>I\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]
        Is_Covariant[where PC=\<open>Identity_Element\<^sub>E\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]*)


subsubsection \<open>Object Equivalence\<close>

lemma Object_Equiv_rule:
  \<open> (Ant \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x. eq x x))
\<Longrightarrow> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
            (\<forall>y. eq x y \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T)) @action \<phi>TA_ind_target undefined)
                \<comment> \<open>Induct over \<open>x \<Ztypecolon> T\<close>. When \<open>x\<close> is inductively split, the constraint of \<open>eq x y\<close>
                    should also split \<open>y\<close>, so that \<open>y \<Ztypecolon> T\<close> can reduce.
                    A deficiency is, when the relation \<open>eq\<close> is trivially true such as that when
                     \<open>T = List \<circle>\<close>, \<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
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


(*TODO: depreciated*)
paragraph \<open>Object Equivalence at Singular Point\<close>
  
lemma [ ]:
  \<open> (\<And>x. Identity_Element\<^sub>I (x \<Ztypecolon> T) (P x))
\<Longrightarrow> (\<And>x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (Ex P) \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T))
\<Longrightarrow> Object_Equiv T (\<lambda>_ _. True) \<close>
  unfolding Object_Equiv_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
            Premise_def Transformation_def
  by clarsimp blast





text \<open>Strategy: transforming both sides to (one of) the base case of induction\<close>

definition \<open>\<A>simp_to_base X \<equiv> X\<close>


lemma \<phi>TA_OE\<^sub>O_rule:
  \<open> TERM ((x\<^sub>0 \<Ztypecolon> T\<^sub>0) = Base)
\<Longrightarrow> (Ant \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x. eq x x))
\<Longrightarrow> (\<And>x. Ant \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<exists>y. eq x y) \<longrightarrow> (x \<Ztypecolon> \<A>simp_to_base T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Base) @action \<phi>TA_ind_target \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>x. Ant \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<exists>y. eq y x) \<longrightarrow> (Base \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Object_Equiv T eq\<close>
  unfolding Object_Equiv_def Action_Tag_def Transformation_def Premise_def \<A>simp_to_base_def MAKE_def
  by blast

(*lemma \<phi>TA_OE\<^sub>O_rewr_IH1:
  \<open> Trueprop (Ant \<longrightarrow> P @action \<phi>TA_ind_target \<A>)
 \<equiv> (Ant \<Longrightarrow> P @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)
*)

lemma \<phi>TA_OE\<^sub>O_rewr_IH2:
  \<open>Trueprop (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE T @action \<A>)
\<equiv> (\<And>A R C P. (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P) &&&
              (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P))\<close>
  unfolding Action_Tag_def atomize_imp atomize_all atomize_conj Transformation_def REMAINS_def MAKE_def
  by (rule; simp; blast)

lemma \<phi>TA_OE\<^sub>O_rewr:
  \<open>Trueprop (Ant \<longrightarrow> C \<longrightarrow> P @action \<phi>TA_ind_target \<A>) \<equiv> (Ant \<Longrightarrow> C \<Longrightarrow> P @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all by (rule; blast)

lemma [\<phi>reason default %\<phi>simp_fallback]:
  \<open> x \<Ztypecolon> \<A>simp_to_base T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<s>\<u>\<b>\<j> y. y = x @action \<A>simp \<close>
  unfolding Action_Tag_def \<A>simp_to_base_def
  by simp

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
\<Longrightarrow> Ant @action \<phi>TA_ANT
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
  prem_extract_Carrier_Set[\<phi>premise_extraction add]
  prem_extract_homo_mul_carrier[\<phi>premise_extraction add]


lemma \<phi>TA_CarS_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> P x \<longrightarrow>
          Within_Carrier_Set (x \<Ztypecolon> T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
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
  \<open>(\<And>g x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x) \<Longrightarrow>
              (Ant @action \<phi>TA_ANT) \<longrightarrow>
              (\<forall>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<longrightarrow> (a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b)) \<longrightarrow> \<comment> \<open>split D\<close>
              (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y) @action \<phi>TA_ind_target (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Transformation_Functor F1 F2 T U D R mapper\<close>
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
  \<open> (Ant \<Longrightarrow> Transformation_Functor F1 F2 T U D R mapper)
\<Longrightarrow> (Ant \<Longrightarrow> Object_Equiv (F2 U) eq)
\<Longrightarrow> (Ant \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>f P x y. mapper (\<lambda>a b. b = f a \<and> P a) x y \<longrightarrow> eq y (fm f P x) \<and> pm f P x))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Functional_Transformation_Functor F1 F2 T U D R pm fm\<close>
  unfolding Premise_def fun_eq_iff Action_Tag_def
  using infer_FTF_from_FT .

lemma [\<phi>reason %\<phi>TA_guesser[top]]:
  \<comment> \<open>Guess_Property in Functional_Transformation_Functor is prohibited\<close>
  \<open> False
\<Longrightarrow> Guess_Property Functional_Transformation_Functor V Any True True (Some C)\<close>
  \<open>Guess_Property Functional_Transformation_Functor V Any True True None\<close>
  unfolding Guess_Property_def
  by simp_all

ML_file \<open>library/phi_type_algebra/transformation_functor.ML\<close>

\<phi>property_deriver Transformation_Functor 110 for (\<open>Transformation_Functor _ _ _ _ _ _ _\<close>)
  = \<open> Phi_Type_Algebra_Derivers.transformation_functor \<close>

\<phi>property_deriver Functional_Transformation_Functor 111
  for (\<open>Functional_Transformation_Functor _ _ _ _ _ _ _ _\<close>)
  requires Transformation_Functor
    = \<open>Phi_Type_Algebra_Derivers.functional_transformation_functor\<close>

(* TODO:
hide_fact \<phi>TA_TF_rule \<phi>TA_TF_rewr_IH \<phi>TA_TF_rewr_C \<phi>TA_TF_pattern_IH \<phi>TA_FTF_rule
*)

subsubsection \<open>Separation Homo\<close>

text \<open>Note, as an instance of Commutativity of Type Operators, the names of \<open>introduction rule\<close>
  and \<open>elimination rule\<close> are just reversed. It is intentional, because I really think those names
  are more natural and we don't really have to force the consistency of the names between the two levels.\<close>

lemma \<phi>TA_SH\<^sub>I_rule:
  \<open> (\<And>z. (Ant @action \<phi>TA_ANT) \<longrightarrow>
            (\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z
                \<longrightarrow> ((y \<Ztypecolon> Fb U) * (x \<Ztypecolon> Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Fc (T \<^emph> U))) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Separation_Homo\<^sub>I Fa Fb Fc T U D w \<close>
  unfolding Separation_Homo\<^sub>I_def \<phi>Prod_expn' Action_Tag_def
  by simp

lemma \<phi>TA_SH\<^sub>E_rule:
  \<open> (\<And>z. (Ant @action \<phi>TA_ANT) \<longrightarrow>
             (z \<Ztypecolon> Fc (T \<^emph>\<^sub>\<A> U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz z \<Ztypecolon> MAKE (Ft T) \<^emph> MAKE (Fu U)) @action \<phi>TA_ind_target \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U uz \<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn' Action_Tag_def Bubbling_def MAKE_def
  by simp

lemma \<phi>TA_SH\<^sub>I_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x y. P x y \<longrightarrow> Q x y) @action \<phi>TA_ind_target undefined)
\<equiv> (\<And>x y. Ant \<Longrightarrow> P x y @action \<phi>TA_pure_facts \<Longrightarrow> Q x y @action \<phi>TA_conditioned_ToA_template)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

text \<open>This conditioned template is necessary because, see,
  \<^prop>\<open>(\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z \<longrightarrow> ((y \<Ztypecolon> Fb U) * (x \<Ztypecolon> Fa T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Fc (T \<^emph> U)))\<close>
  \<^term>\<open>z\<close> does not determine \<open>x\<close> and \<open>y\<close> during the reasoning phase and until the phase of proof obligation solving.
  When there are multiple choices of such induction hypotheses, for sure, we can attempt every choice
  exhaustively, but it multiplies the search branches and can harm the performance dramatically.

  Update: perhaps, the conditioned template is not that necessary, because it doesn't really matter
  when \<open>x,y\<close> are undetermined, as they are still constrained by conditions given to proof obligations.
  The form of abstract objects should never matter. All syntactic information guiding the reasoning
  should only be given from \<phi>-type, while the syntax of abstract objects shouldn't bear any convention
  nor expectation.

  BTW, I think we have no way to circumvent the reasoning branches even enormous, because there is a
  fallback always varifies the abstract object in the target to a schematic variable.
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
       and Identity_Elements
       and Basic

  (*TODO: I'm thinking why I gave it this name... yes, there is identity element, but then.. what?
          for what reason it can be called monoidal?*)



subsubsection \<open>Congruence in Function Definition\<close>

lemma function_congruence_template:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Transformation_Functor F F' T U D R M)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Transformation_Functor F' F U T D' R' M')
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Object_Equiv (F' U) eq')
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Object_Equiv (F T) eq)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (x = y \<and> eqs \<longrightarrow>
              D x \<subseteq> R x \<and> (\<forall>x y. M (=) x y \<longrightarrow> eq' y x) \<and> (\<forall>x. D x = D' x) \<and>
              D' y \<subseteq> R' y \<and> (\<forall>x y. M' (=) y x \<longrightarrow> eq x y))
\<Longrightarrow> \<r>Success
\<Longrightarrow> eqs
\<Longrightarrow> x = y
\<Longrightarrow> (\<And>a. a \<in> D y \<Longrightarrow> T a = U a)
\<Longrightarrow> F T x = F' U y \<close>
  unfolding fun_eq_iff[symmetric, where f=D]
  unfolding Transformation_Functor_def Premise_def Transformation_def \<phi>Type_def BI_eq_iff
            subset_iff meta_Ball_def Ball_def Object_Equiv_def
  apply clarify
  subgoal premises prems for u
    by (insert prems(1)[THEN spec[where x=y], THEN spec[where x=\<open>(=)\<close>]]
               prems(2)[THEN spec[where x=y], THEN spec[where x=\<open>(=)\<close>]]
               prems(3-);
        clarsimp; rule; meson) .
  
ML_file \<open>library/phi_type_algebra/function_congruence.ML\<close>


subsubsection \<open>Configuration for guessing default Semimodule properties\<close>

definition Guess_Scalar_Zero :: \<open> 's itself \<Rightarrow> 'c::one itself \<Rightarrow> 'a\<^sub>T itself \<Rightarrow> 'a itself
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('c,'a\<^sub>T) \<phi>
                              \<Rightarrow> 's
                              \<Rightarrow> bool \<Rightarrow> bool
                              \<Rightarrow> bool \<close>
  where \<open>Guess_Scalar_Zero _ _ _ _ F unfolded_F T zero ants conds \<equiv> True\<close>

(*
definition Guess_Scalar_One\<^sub>I :: \<open> 's itself \<Rightarrow> 'c itself \<Rightarrow> 'a\<^sub>T itself \<Rightarrow> 'a itself
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('c,'a\<^sub>T) \<phi>
                              \<Rightarrow> 's \<Rightarrow> ('a\<^sub>T \<Rightarrow> bool) \<Rightarrow> ('a\<^sub>T \<Rightarrow> 'a)
                              \<Rightarrow> bool \<close>
  where \<open>Guess_Scalar_One\<^sub>I _ _ _ _ F unfolded_F T one Dx f \<equiv> True\<close>
*)
definition Guess_Scalar_One\<^sub>E :: \<open> 's itself \<Rightarrow> 'c itself \<Rightarrow> 'a\<^sub>T itself \<Rightarrow> 'a itself
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('c,'a\<^sub>T) \<phi>
                              \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a\<^sub>T)
                              \<Rightarrow> bool \<Rightarrow> bool
                              \<Rightarrow> bool \<close>
  where \<open>Guess_Scalar_One\<^sub>E _ _ _ _ F unfolded_F T one Dx f ants conds \<equiv> True\<close>

definition Guess_Scalar_Assoc :: \<open> bool \<comment> \<open>True for \<open>Scalar_Assoc\<^sub>I\<close>, False for \<open>Scalar_Assoc\<^sub>E\<close>\<close>
                                 \<Rightarrow> 's\<^sub>c itself \<Rightarrow> 'c itself \<Rightarrow> 'c\<^sub>s\<^sub>t itself \<Rightarrow> 'a itself \<Rightarrow> 'a\<^sub>s\<^sub>t itself
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>_\<^sub>t) \<phi>)
                                 \<Rightarrow> ('s\<^sub>t \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>)
                                 \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                 \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                 \<Rightarrow> ('c,'a) \<phi>
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> bool)
                                 \<Rightarrow> ('s\<^sub>t \<Rightarrow> bool)
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> bool)
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 's\<^sub>c)
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t)
                                 \<Rightarrow> bool \<Rightarrow> bool
                                 \<Rightarrow> bool\<close>
  where \<open>Guess_Scalar_Assoc _ _ _ _ _ _ Fs Ft Fc unfolded_Fc T Ds Dt Dx smul f ants conds \<equiv> True\<close>

definition Guess_Zip_of_Semimodule :: \<open>'s itself \<Rightarrow> ('c::sep_magma) itself \<Rightarrow> 'a\<^sub>T itself \<Rightarrow> 'a itself
                                      \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                      \<Rightarrow> 'expr
                                      \<Rightarrow> ('c,'a\<^sub>T) \<phi>
                                      \<Rightarrow> ('s \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                      \<Rightarrow> bool \<Rightarrow> bool
                                      \<Rightarrow> bool\<close>
  where \<open>Guess_Zip_of_Semimodule type_scalar type_concrete type_element_abstract type_abstract
                                 F unfolded_F_def T
                                 domain_of_scalar domain_of_abstract zip_opr
                                 antecedents conditions_of_antecedents
       \<equiv> True\<close>

definition Guess_Unzip_of_Semimodule :: \<open>'s itself \<Rightarrow> 'c itself \<Rightarrow> 'a\<^sub>T itself \<Rightarrow> 'a itself
                                      \<Rightarrow> ('s \<Rightarrow> ('c,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                      \<Rightarrow> 'expr
                                      \<Rightarrow> ('c,'a\<^sub>T) \<phi>
                                      \<Rightarrow> ('s \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool) 
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                      \<Rightarrow> bool \<Rightarrow> bool
                                      \<Rightarrow> bool\<close>
  where \<open>Guess_Unzip_of_Semimodule type_scalar type_concrete type_element_abstract type_abstract
                                   F unfolded_typ_def T
                                   domain_of_scalar domain_of_abstract unzip_opr
                                   antecedents conditions_of_antecedents
       \<equiv> True\<close>

declare [[ \<phi>reason_default_pattern
      (*\<open>Guess_Scalar_One\<^sub>I ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_One\<^sub>I ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _\<close>   (100)
  and*)
      \<open>Guess_Scalar_Zero ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_Zero ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _\<close>   (100)
  and \<open>Guess_Scalar_One\<^sub>E ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_One\<^sub>E ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _ _ _\<close>   (100)
  and \<open>Guess_Zip_of_Semimodule ?S ?C ?A\<^sub>T ?A _ ?def _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Zip_of_Semimodule ?S ?C ?A\<^sub>T ?A _ ?def _ _ _ _ _ _\<close>   (100)
  and \<open>Guess_Unzip_of_Semimodule ?S ?C ?A\<^sub>T ?A _ ?def _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Unzip_of_Semimodule ?S ?C ?A\<^sub>T ?A _ ?def _ _ _ _ _ _\<close>   (100)
  and \<open>Guess_Scalar_Assoc ?mode ?S ?C\<^sub>T ?C ?A\<^sub>T ?A\<^sub>F _ _ _ ?def ?T _ _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_Assoc ?mode ?S ?C\<^sub>T ?C ?A\<^sub>T ?A\<^sub>F _ _ _ ?def ?T _ _ _ _ _ _ _\<close>   (100)
]]

text \<open>Guessing the zip operation of a semimodule is far beyond what can be inferred from BNF,
      partially because a semimodule is over two algebraic sorts (i.e., two logical types).
      Due to this, the guessing of the abstract operators of semimodules more relies on pre-registered
      records over the logical types.\<close>

paragraph \<open>Initialization\<close>

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s T x) : (x \<Ztypecolon> F s T) )
\<Longrightarrow> Guess_Scalar_Zero TS TC TA\<^sub>T TA F var_unfolded_F T z ants conds
\<Longrightarrow> Guess_Scalar_Zero TS TC TA\<^sub>T TA F var_unfolded_F T z ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s T x) : (x \<Ztypecolon> F s T) )
\<Longrightarrow> Guess_Scalar_One\<^sub>E TS TC TA\<^sub>T TA F var_unfolded_F T one Dx f ants conds
\<Longrightarrow> Guess_Scalar_One\<^sub>E TS TC TA\<^sub>T TA F var_unfolded_F T one Dx f ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_Fc s T x) : (x \<Ztypecolon> Fc s T) )
\<Longrightarrow> Guess_Scalar_Assoc flag TS TC TC' TA\<^sub>T TA Fs Ft Fc var_unfolded_Fc T Ds Dt Dx smul f ants conds
\<Longrightarrow> Guess_Scalar_Assoc flag TS TC TC' TA\<^sub>T TA Fs Ft Fc var_unfolded_Fc T Ds Dt Dx smul f ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s T x) : (x \<Ztypecolon> F s T) )
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F var_unfolded_F T Ds Dx z ants conds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA\<^sub>T TA F var_unfolded_F T Ds Dx z ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s T x) : (x \<Ztypecolon> F s T) )
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F var_unfolded_F T Ds Dx z ants conds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA\<^sub>T TA F var_unfolded_F T Ds Dx z ants conds\<close> .


paragraph \<open>Guess_Scalar_Zero\<close>

lemma [\<phi>reason %\<phi>TA_guesser_fallback]:
  \<open>Guess_Scalar_Zero TYPE('s::zero) TYPE('c::one) TYPE('a\<^sub>T) TYPE('a)
                     F unfolded_F T 0 True True \<close>
  unfolding Guess_Scalar_Zero_def ..

paragraph \<open>Guess_Scalar_One\<close>

(* lemma [\<phi>reason %\<phi>TA_guesser_fallback]:
  \<open>Guess_Scalar_One\<^sub>I TYPE('s::one) TYPE('c) TYPE('a) TYPE('a)
                     F whateverT 1 (\<lambda>_. True) (\<lambda>x. x)\<close>
  unfolding Guess_Scalar_One\<^sub>I_def .. *)

lemma [\<phi>reason %\<phi>TA_guesser_fallback]:
  \<open>Guess_Scalar_One\<^sub>E TYPE('s::one) TYPE('c) TYPE('a) TYPE('a)
                     F whatever T 1 (\<lambda>_. True) (\<lambda>x. x) True True\<close>
  unfolding Guess_Scalar_One\<^sub>E_def ..

(* lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_One\<^sub>I TYPE('i set) TYPE('c::sep_algebra) TYPE('a) TYPE('i \<Rightarrow> 'a)
                     F (\<lambda>s T x. \<big_ast> (A s T x) s) T {any} (\<lambda>_. True) (\<lambda>x _. x) \<close>
  unfolding Guess_Scalar_One\<^sub>I_def .. *)

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_One\<^sub>E TYPE('i set) TYPE('c::sep_algebra) TYPE('a) TYPE('i \<Rightarrow> 'a)
                    F (\<lambda>s T x. \<big_ast> (A s T x) s) T {i} (\<lambda>_. True) (\<lambda>f. f i) True True\<close>
  unfolding Guess_Scalar_One\<^sub>E_def ..


paragraph \<open>Guess_Scalar_Assoc\<close>

lemma [\<phi>reason %\<phi>TA_guesser_default[bottom]]:
  \<open>Guess_Scalar_Assoc both_modes TYPE('s::times) TYPE('c) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_Assoc both_mode TYPE(rat) TYPE('c::share) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T ((<) 0) ((<) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default+1]:
  \<open>Guess_Scalar_Assoc both_mode TYPE(rat) TYPE('c::share_one) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T ((\<le>) 0) ((\<le>) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default for
        \<open>Guess_Scalar_Assoc True TYPE(_ set) TYPE(_) TYPE(_) TYPE(_) TYPE(_) _ _ _ (\<lambda>s T x. \<big_ast> (?A s T x) s) _
                            _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Scalar_Mul Fc Fs
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul Fc Ft
\<Longrightarrow> Guess_Scalar_Assoc True TYPE(('i \<times> 'j) set) TYPE('c::sep_algebra) TYPE('c) TYPE('a) TYPE('i \<times> 'j \<Rightarrow> 'a)
                      Fs Ft Fc (\<lambda>s T x. \<big_ast> (A s T x) s) T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True)
                      (\<times>) (\<lambda>_ _. case_prod) True True \<close>
  unfolding Guess_Scalar_Assoc_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default for
        \<open>Guess_Scalar_Assoc False TYPE(_ set) TYPE(_) TYPE(_) TYPE(_) TYPE(_) _ _ _ (\<lambda>s T x. \<big_ast> (?A s T x) s) _
                            _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Scalar_Mul Fc Fs
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul Fc Ft
\<Longrightarrow> Guess_Scalar_Assoc False TYPE(('i \<times> 'j) set) TYPE('c::sep_algebra) TYPE('c) TYPE('a) TYPE('i \<times> 'j \<Rightarrow> 'a)
                      Fs Ft Fc (\<lambda>s T x. \<big_ast> (A s T x) s) T finite finite (\<lambda>_ _ _. True)
                      (\<times>) (\<lambda>_ _. case_prod) True True \<close>
  unfolding Guess_Scalar_Assoc_def ..


paragraph \<open>Guess_(Un)Zip_of_Semimodule\<close>

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Zip_of_Semimodule TYPE(rat) TYPE('c::sep_magma) TYPE('a) TYPE('a)
                           F any T
                           (\<lambda>x. 0 \<le> x) (\<lambda>s t (x,y). x = y) (\<lambda>_ _ (x,y). x)
                           True True \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Unzip_of_Semimodule TYPE(rat) TYPE('c::sep_magma) TYPE('a) TYPE('a)
                             F any T
                             (\<lambda>x. 0 \<le> x) (\<lambda>s t x. True) (\<lambda>_ _ x. (x,x))
                             True True \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Zip_of_Semimodule TYPE(nat lcro_interval) TYPE('c::sep_magma) TYPE('a list) TYPE('a list)
                           F any T (\<lambda>_. True)
                           (\<lambda>s t (x,y). LCRO_Interval.width_of s = length x \<and> LCRO_Interval.width_of t = length y)
                           (\<lambda>_ _ (x,y). y * x)
                           True True\<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Unzip_of_Semimodule TYPE(nat lcro_interval) TYPE('c::sep_magma) TYPE('a list) TYPE('a list)
                             F any T (\<lambda>_. True)
                             (\<lambda>s t x. LCRO_Interval.width_of s + LCRO_Interval.width_of t = length x)
                             (\<lambda>s t x. (take (LCRO_Interval.width_of s) x, drop (LCRO_Interval.width_of s) x))
                             True True\<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Zip_of_Semimodule TYPE('i set) TYPE('c::sep_algebra) TYPE('a) TYPE('i \<Rightarrow> 'a)
                           F (\<lambda>s T x. \<big_ast> (A s T x) s) T
                           (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ D\<^sub>g (f,g). f \<oplus>\<^sub>f[D\<^sub>g] g) True True \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Unzip_of_Semimodule TYPE('i set) TYPE('c::sep_algebra) TYPE('a) TYPE('i \<Rightarrow> 'a)
                             F (\<lambda>s T x. \<big_ast> (A s T x) s) T
                             (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ f. (f,f)) True True \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..


paragraph \<open>ML Library\<close>

ML_file \<open>library/phi_type_algebra/guess_semimodule.ML\<close>


subsubsection \<open>Semimodule Scalar Zero\<close>

lemma \<phi>TA_M0_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> F zero T) True @action \<phi>TA_ind_target undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_Zero F T zero \<close>
  unfolding Semimodule_Zero_def Action_Tag_def Premise_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
  by (clarsimp simp add: BI_eq_iff Transformation_def; blast)


lemma \<phi>TA_M0c_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> F zero T) @action \<phi>TA_ind_target undefined)
\<Longrightarrow> Semimodule_Zero F T zero
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Closed_Semimodule_Zero F T zero \<close>
  unfolding Semimodule_Zero_def Action_Tag_def Premise_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
            Closed_Semimodule_Zero_def
  by (clarsimp simp add: BI_eq_iff Transformation_def; blast)

lemma \<phi>TA_M0_rewr:
  \<open> Trueprop (Ant \<longrightarrow> Q @action \<phi>TA_ind_target Any) \<equiv> (Ant \<Longrightarrow> Q)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_zero.ML\<close>

\<phi>property_deriver Semimodule_Zero 129 for (\<open>Semimodule_Zero _ _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_zero\<close>

\<phi>property_deriver Closed_Semimodule_Zero 130
    for (\<open>Closed_Semimodule_Zero _ _ _\<close>) requires Semimodule_Zero
    = \<open>Phi_Type_Algebra_Derivers.closed_semimodule_zero\<close>


subsubsection \<open>Semimodule Scalar Identity\<close>

(*
lemma \<phi>TA_MI\<^sub>I_rule:
  \<open> 
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant
\<Longrightarrow> Semimodule_Identity\<^sub>I F T one D f \<close>
  unfolding Semimodule_Identity\<^sub>I_def Action_Tag_def Premise_def
  by (clarsimp; rule \<phi>Type_eqI_Tr; blast)
*)

lemma \<phi>TA_MI\<^sub>E_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
      \<longrightarrow> (x \<Ztypecolon> F one T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> (\<And>x. (Ant @action \<phi>TA_ANT)
      \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
      \<longrightarrow> (f x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_Identity\<^sub>E F T one D f \<close>
  unfolding Semimodule_Identity\<^sub>E_def Action_Tag_def Premise_def
  by (clarsimp; rule assertion_eq_intro; blast)

lemma \<phi>TA_MI_rewr:
  \<open> Trueprop (Ant \<longrightarrow> Q \<longrightarrow> P @action \<phi>TA_ind_target \<A>) \<equiv> (Ant \<Longrightarrow> Q \<Longrightarrow> P @action \<A>)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_identity.ML\<close>

\<phi>property_deriver Semimodule_Identity 130 for (\<open>Semimodule_Identity _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_identity\<close>


subsubsection \<open>Semimodule Scalar Associative\<close>

text \<open>\<phi>-type embedding of separation quantifier \<open>x \<Ztypecolon> \<big_ast>[i\<in>I] T\<close> is a recursive example of this.

  The induction of the \<phi>-type should expand the scalar as the scalar usually represents the domain of the \<phi>-type abstraction. 
\<close>

lemma \<phi>TA_MS\<^sub>I_rule:
  \<open> (\<And>t s x r y. (Ant @action \<phi>TA_ANT)
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x \<and> r = smul s t \<and> f s t x = y
         \<longrightarrow> (x \<Ztypecolon> Fs s (Ft t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fc r T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Action_Tag_def Premise_def
  by clarsimp

lemma \<phi>TA_MS\<^sub>E_rule:
  \<open> (\<And>t s x r y. (Ant @action \<phi>TA_ANT)
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> r = smul s t \<and> Dx s t x \<and> f s t x = y
         \<longrightarrow> (y \<Ztypecolon> Fc r T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fs s (Ft t T)) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Action_Tag_def Premise_def
  by clarsimp

lemma \<phi>TA_MS_rewr:
  \<open> Trueprop (Ant \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<longrightarrow> Q @action \<phi>TA_ind_target \<A>) \<equiv> (Ant \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> Q @action \<A>)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_scalar.ML\<close>

\<phi>property_deriver Semimodule_Scalar_Assoc\<^sub>I 130 for (\<open>Semimodule_Scalar_Assoc\<^sub>I _ _ _ _ _ _ _ _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_assoc_I\<close>

\<phi>property_deriver Semimodule_Scalar_Assoc\<^sub>E 130 for (\<open>Semimodule_Scalar_Assoc\<^sub>E _ _ _ _ _ _ _ _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_assoc_E\<close>

\<phi>property_deriver Semimodule_Scalar_Assoc 131
  requires Semimodule_Scalar_Assoc\<^sub>I and Semimodule_Scalar_Assoc\<^sub>E

\<phi>property_deriver Semimodule_NonDistr_no0 132
  requires Semimodule_Scalar_Assoc and Semimodule_Identity

\<phi>property_deriver Semimodule_NonDistr 133
  requires Semimodule_NonDistr_no0 and Semimodule_Zero


subsubsection \<open>Semimodule Scalar Distributivity - Zip\<close>

text \<open>Essentially the rules are derived from that of existing \<phi>-types, and the initial rules
  are those from logical connectivities, function embedding \<open>\<phi>Fun\<close> into \<phi>-types and vertical
  composition \<open>\<phi>Composition\<close>. 

TODO: move me!
\<close>

lemma \<phi>TA_MD\<^sub>Z_rule:
  \<open> (\<And>s t x r z. (Ant @action \<phi>TA_ANT)
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Ds t \<and> s ##\<^sub>+ t
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> r = s + t \<and> Dx t s x \<and> zi t s x = z
         \<longrightarrow> (x \<Ztypecolon> F t T \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> F r T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F T Ds Dx zi \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Action_Tag_def Premise_def Transformation_def
  by clarsimp blast

lemma \<phi>TA_MD\<^sub>U_rule:
  \<open> (\<And>s t r x. (Ant @action \<phi>TA_ANT)
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Ds t \<and> s ##\<^sub>+ t
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> r = s + t \<and> Dx t s x
         \<longrightarrow> (x \<Ztypecolon> F r T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t T \<^emph> F s T) @action \<phi>TA_ind_target NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>U F T Ds Dx uz \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>U_def Action_Tag_def Premise_def Transformation_def
  by clarsimp

lemma \<phi>TA_MD_rewr:
  \<open> Trueprop (Ant \<longrightarrow> P1 \<longrightarrow> P2 \<longrightarrow> Q @action \<phi>TA_ind_target \<A>)
 \<equiv> (Ant \<Longrightarrow> P1 \<Longrightarrow> P2 \<Longrightarrow> Q @action \<A>)\<close>
  unfolding atomize_imp Action_Tag_def ..

ML_file \<open>library/phi_type_algebra/semimodule_distrib_zip.ML\<close>

\<phi>property_deriver Semimodule_SDistr_Homo\<^sub>Z 130 for (\<open>Semimodule_SDistr_Homo\<^sub>Z _ _ _ _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_distrib_zip\<close>

\<phi>property_deriver Semimodule_SDistr_Homo\<^sub>U 130 for (\<open>Semimodule_SDistr_Homo\<^sub>U _ _ _ _ _\<close>)
    = \<open>Phi_Type_Algebra_Derivers.semimodule_distrib_unzip\<close>

\<phi>property_deriver Semimodule_SDistr_Homo 131
  requires Semimodule_SDistr_Homo\<^sub>Z and Semimodule_SDistr_Homo\<^sub>U

\<phi>property_deriver Semimodule_no0 133
  requires Semimodule_NonDistr_no0 and Semimodule_SDistr_Homo

\<phi>property_deriver Semimodule 134
  requires Semimodule_no0 and Semimodule_Zero

declare Is_Invariant[where PC=\<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]
        Is_Invariant[where PC=\<open>Semimodule_SDistr_Homo\<^sub>U\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]



subsubsection \<open>Construct Abstraction from Concrete Representation (by Itself)\<close>

lemma \<phi>TA_TrCstr_rule:
  \<open> (Ant @action \<phi>TA_ANT) \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A) @action \<phi>TA_ind_target undefined
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
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
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> \<forall>c. \<p>\<r>\<e>\<m>\<i>\<s>\<e> P c \<longrightarrow> MAKE_from_RAW c ()(c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f c \<Ztypecolon> MAKE_from_RAW T) \<close>
  \<comment> \<open>If one concrete representation is related to multiple abstract objects, just choose any one
      that is most representative.\<close>
  unfolding Action_Tag_def
  by simp

ML_file \<open>library/phi_type_algebra/constr_abst.ML\<close>
*)
\<phi>property_deriver Make_Abstraction_from_Raw 130
  for ( \<open>\<forall>x. Premise _ _ \<longrightarrow> (x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?f x \<Ztypecolon> ?T)\<close>
      | \<open>Premise _ _ \<longrightarrow> (?x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T)\<close>
      | \<open>\<forall>x. x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?f x \<Ztypecolon> ?T\<close>
      | \<open>?x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T\<close> )
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Algebra_Derivers.Make_Abstraction_from_Raw \<close>


subsubsection \<open>Destruct Abstraction down to Concrete Representation (by Itself)\<close>

lemma \<phi>TA_TrRA_rule:
  \<open> (\<And>x. (Ant @action \<phi>TA_ANT) \<longrightarrow>
         (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_ind_target (to (Itself::('b,'b) \<phi>)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> \<forall>x. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y::'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to (Itself::('b,'b) \<phi>)) \<close>
  unfolding Action_Tag_def
  by simp

ML_file \<open>library/phi_type_algebra/open_all_abstraction.ML\<close>

\<phi>property_deriver Open_Abstraction_to_Raw 130 for ( \<open>\<forall>x. (x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself)\<close>
                                                | \<open>\<forall>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself\<close>
                                                | \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r' y @action to Itself\<close>)
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Algebra_Derivers.open_all_abstraction \<close>

\<phi>property_deriver Abstraction_to_Raw 131
  requires Open_Abstraction_to_Raw and Make_Abstraction_from_Raw


subsubsection \<open>Trim Empty Generated during Separation Extraction\<close>

(*TODO: reform.*)

text \<open>For a type operator \<open>F\<close>, SE_Trim_Empty generates rules that eliminates into \<open>\<circle>\<close>
  any \<open>F \<circle>\<close> generated during Separation Extraction process.

  This elimination is derived from \<open>Identity_Element\<close>. If the elimination rule is condition-less
  (demand no conditional premise nor reasoner subgoals), the rule is activated automatically.
  But if there are conditions, the system needs user's discretion to decide if to activate it.
  If so, activate deriver \<open>SE_Trim_Empty\<close>.
\<close>

lemma [\<phi>reason_template name F.\<phi>None [assertion_simps, simp]]:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Elements\<^sub>I (F \<circle>) D\<^sub>I P\<^sub>I @action \<A>_template_reason
\<Longrightarrow> Identity_Elements\<^sub>E (F \<circle>) D\<^sub>E @action \<A>_template_reason
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> (D\<^sub>I () \<and> D\<^sub>E ())
\<Longrightarrow> NO_SIMP (F \<circle> = \<circle>) \<close>
  unfolding Object_Equiv_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def NO_SIMP_def Action_Tag_def
            Identity_Elements\<^sub>I_def Identity_Elements\<^sub>E_def Premise_def
  by (rule \<phi>Type_eqI_Tr; clarsimp simp add: transformation_weaken)

(* Temporarily disabled, and I am thinking if to depreciate this module as it seems useless now.

lemma derive_\<A>SE_trim_I:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>I (yy \<Ztypecolon> F \<circle>) P
\<Longrightarrow> Object_Equiv (F \<circle>) eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd y) yy
\<Longrightarrow> \<A>SE_trim\<^sub>I y (F \<circle>) (fst y, ()) \<circle> P \<close>
  unfolding \<A>SE_trim\<^sub>I_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>I_def]
    apply_rule R1[THEN transformation_right_frame]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_I_TH:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>I (yy \<Ztypecolon> F \<circle>) P
\<Longrightarrow> Object_Equiv (F \<circle>) eq
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq (snd y) yy
\<Longrightarrow> \<A>SE_trim\<^sub>I_TH y (F \<circle>) (fst y, ()) \<circle> P \<circle> (F' \<circle>) \<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  \<medium_left_bracket> premises _ and  R1[unfolded Identity_Element\<^sub>I_def]
    apply_rule R1[THEN transformation_right_frame]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_E:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>E (u \<Ztypecolon> F \<circle>)
\<Longrightarrow> \<A>SE_trim\<^sub>E (fst x', u) (F \<circle>) x' \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>E_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>E_def]
    apply_rule R1[THEN transformation_right_frame]
  \<medium_right_bracket> .

lemma derive_\<A>SE_trim_E_TH:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Identity_Element\<^sub>E (u \<Ztypecolon> F \<circle>)
\<Longrightarrow> \<A>SE_trim\<^sub>E_TH (fst x', u) (F \<circle>) x' \<circle> \<circle> (F' \<circle>) \<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  \<medium_left_bracket> premises _ and R1[unfolded Identity_Element\<^sub>E_def]
    apply_rule R1[THEN transformation_right_frame]
  \<medium_right_bracket> .


ML_file \<open>library/phi_type_algebra/SE_Trim_Empty.ML\<close>

\<phi>property_deriver SE_Trim_Empty 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.SE_Trim_Empty quiet) \<close>

lemmas [\<phi>reason_template default 40 pass: \<open>(Phi_Type_Algebra_Derivers.SE_Trim_Empty__generation_pass, K I)\<close>] =
          derive_\<A>SE_trim_I derive_\<A>SE_trim_I_TH
          derive_\<A>SE_trim_E derive_\<A>SE_trim_E_TH
*)

subsubsection \<open>Meta Deriver for \<phi>-Type Operator Commutativity\<close>

paragraph \<open>Guess Property\<close>

subparagraph \<open>Definition of Reasoning Goals\<close>

definition Guess_Tyops_Commute :: \<open> bool \<comment> \<open>Intro for true, Elim for false\<close>
                                \<Rightarrow> (('c\<^sub>F,'a\<^sub>F) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                                \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F,'a\<^sub>F) \<phi>)
                                \<Rightarrow> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                                \<Rightarrow> (('c\<^sub>F,'a\<^sub>F) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                                \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F,'a\<^sub>F) \<phi>)
                                \<Rightarrow> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                                \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                                \<Rightarrow> ('a \<Rightarrow> bool)
                                \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)
                                \<Rightarrow> bool \<Rightarrow> bool
                                \<Rightarrow> bool\<close>
  where \<open>Guess_Tyops_Commute is_intro G G' F F' unfolded_G unfolded_G' uF uF' T D r ants conds \<equiv> True\<close>

definition Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 :: \<open> bool \<comment> \<open>True for \<open>1\<rightarrow>2I\<close>, False for \<open>2\<rightarrow>1I\<close>\<close>
                                    \<Rightarrow> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                    \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi>)
                                    \<Rightarrow> (('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi>)
                                    \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                                    \<Rightarrow> (('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                                    \<Rightarrow> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                    \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi>)
                                    \<Rightarrow> (('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi>)
                                    \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                                    \<Rightarrow> (('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                                    \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                                    \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi>
                                    \<Rightarrow> ('b \<Rightarrow> bool)
                                    \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool)
                                    \<Rightarrow> bool \<Rightarrow> bool
                                    \<Rightarrow> bool\<close>
  where \<open>Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 mode F F'\<^sub>T F'\<^sub>U G G' uF uF'\<^sub>T uF'\<^sub>U uG uG' T U D r ants conds \<equiv> True\<close>
    \<comment> \<open>also covers \<open>Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1\<^sub>I\<close>, by swapping \<open>F\<close> and \<open>G\<close>\<close>

definition Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 :: \<open> bool \<comment> \<open>True for \<open>1\<rightarrow>2E\<close>, False for \<open>2\<rightarrow>1E\<close>\<close>
                                   \<Rightarrow> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                   \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi>)
                                   \<Rightarrow> (('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi>)
                                   \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                                   \<Rightarrow> (('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                                   \<Rightarrow> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                                   \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi>)
                                   \<Rightarrow> (('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi>)
                                   \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                                   \<Rightarrow> (('c\<^sub>F\<^sub>T,'a\<^sub>F\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F\<^sub>U,'a\<^sub>F\<^sub>U) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                                   \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                                   \<Rightarrow> ('c\<^sub>U,'a\<^sub>U) \<phi>
                                   \<Rightarrow> ('a \<Rightarrow> bool)
                                   \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)
                                   \<Rightarrow> bool \<Rightarrow> bool
                                   \<Rightarrow> bool\<close>
  where \<open>Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 mode F F'\<^sub>T F'\<^sub>U G G' uF uF'\<^sub>T uF'\<^sub>G uG uG' T U D r ants conds \<equiv> True\<close>


\<phi>reasoner_group guess_tyop_commute_all = (100,[10,3000]) for (\<open>Guess_Tyops_Commute intro F F' G G' unfolded_G unfolded_G' uF uF' T D r ants conds\<close>)
    \<open>Rules guessing the form of the Commutativity between \<phi>-Type Operators\<close>
 and guess_tyop_commute = (1000, [1000, 3000]) for (\<open>Guess_Tyops_Commute intro F F' G G' unfolded_G unfolded_G' uF uF' T D r ants conds\<close>)
                                             in guess_tyop_commute_all
    \<open>User Rules\<close>
 and guess_tyop_commute_fallback = (10, [10,10]) for (\<open>Guess_Tyops_Commute intro F F' G G' unfolded_G unfolded_G' uF uF' T D r ants conds\<close>)
                                                  in guess_tyop_commute_all < guess_tyop_commute
    \<open>Fallback rules\<close>
 and guess_tyop_commute_default = (15, [11, 39]) for (\<open>Guess_Tyops_Commute intro F F' G G' unfolded_G unfolded_G' uF uF' T D r ants conds\<close>)
                                                  in guess_tyop_commute_all and > guess_tyop_commute_fallback and < guess_tyop_commute
    \<open>Predefined default rules guessing the form of the Commutativity between \<phi>-Type Operators\<close>

declare [[
  \<phi>reason_default_pattern \<open>Guess_Tyops_Commute ?mode ?F _ ?G _ ?uG ?uG' ?uF ?uF' _ _ _ _ _\<close> \<Rightarrow>
                          \<open>Guess_Tyops_Commute ?mode ?F _ ?G _ ?uG ?uG' ?uF ?uF' _ _ _ _ _\<close>    (100)
                      and \<open>Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?mode ?F _ _ ?G _ ?uF ?uF\<^sub>T ?uF\<^sub>F ?uG ?uG' _ _ _ _ _ _\<close> \<Rightarrow>
                          \<open>Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?mode ?F _ _ ?G _ ?uF ?uF\<^sub>T ?uF\<^sub>F ?uG ?uG' _ _ _ _ _ _\<close>    (100)
                      and \<open>Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?mode ?G _ _ ?F _ ?uG ?uG\<^sub>T ?uG\<^sub>F ?uF ?uF' _ _ _ _ _ _\<close> \<Rightarrow>
                          \<open>Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?mode ?G _ _ ?F _ ?uG ?uG\<^sub>T ?uG\<^sub>F ?uF ?uF' _ _ _ _ _ _\<close>    (100)
]]

subparagraph \<open>Initialization\<close>

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> Parameter_Variant_of_the_Same_Type G G'
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G T x) : (x \<Ztypecolon> G T) )
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G' T x) : (x \<Ztypecolon> G' T) )
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' var_unfolded_G var_unfolded_G' uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' var_unfolded_G var_unfolded_G' uF uF' T D r ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> Parameter_Variant_of_the_Same_Type G G'
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G T x) : (x \<Ztypecolon> G T) )
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G' T x) : (x \<Ztypecolon> G' T) )
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' var_unfolded_G var_unfolded_G' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute False F F' G G' uF uF' var_unfolded_G var_unfolded_G' T D r ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> Parameter_Variant_of_the_Same_Type F F'\<^sub>T
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F F'\<^sub>U
\<Longrightarrow> Parameter_Variant_of_the_Same_Type G G'
\<Longrightarrow> (\<And>T U x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G T U x) : (x \<Ztypecolon> G T U) )
\<Longrightarrow> (\<And>T U x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G' T U x) : (x \<Ztypecolon> G' T U) )
\<Longrightarrow> Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 True F F'\<^sub>T F'\<^sub>U G G' uF uF'\<^sub>T uF'\<^sub>U var_unfolded_G var_unfolded_G' T U D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 True F F'\<^sub>T F'\<^sub>U G G' uF uF'\<^sub>T uF'\<^sub>U var_unfolded_G var_unfolded_G' T U D r ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> Parameter_Variant_of_the_Same_Type G G'\<^sub>T
\<Longrightarrow> Parameter_Variant_of_the_Same_Type G G'\<^sub>U
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G T x) : (x \<Ztypecolon> G T) )
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G'\<^sub>T T x) : (x \<Ztypecolon> G'\<^sub>T T) )
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G'\<^sub>U T x) : (x \<Ztypecolon> G'\<^sub>U T) )
\<Longrightarrow> Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 False G G'\<^sub>T G'\<^sub>U F F' var_unfolded_G var_unfolded_G'\<^sub>T var_unfolded_G'\<^sub>U uF uF' T U D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 False G G'\<^sub>T G'\<^sub>U F F' var_unfolded_G var_unfolded_G'\<^sub>T var_unfolded_G'\<^sub>U uF uF' T U D r ants conds\<close> .


lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> Parameter_Variant_of_the_Same_Type F F'\<^sub>T
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F F'\<^sub>U
\<Longrightarrow> Parameter_Variant_of_the_Same_Type G G'
\<Longrightarrow> (\<And>T U x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_uG T U x) : (x \<Ztypecolon> G T U) )
\<Longrightarrow> (\<And>T U x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_uG' T U x) : (x \<Ztypecolon> G' T U) )
\<Longrightarrow> Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 True F F'\<^sub>T F'\<^sub>U G G' uF uF'\<^sub>T uF'\<^sub>U var_uG var_uG' T U D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 True F F'\<^sub>T F'\<^sub>U G G' uF uF'\<^sub>T uF'\<^sub>U var_uG var_uG' T U D r ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> Parameter_Variant_of_the_Same_Type G G'\<^sub>T
\<Longrightarrow> Parameter_Variant_of_the_Same_Type G G'\<^sub>U
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_uG T x) : (x \<Ztypecolon> G T) )
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_uG'\<^sub>T T x) : (x \<Ztypecolon> G'\<^sub>T T) )
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_uG'\<^sub>U T x) : (x \<Ztypecolon> G'\<^sub>U T) )
\<Longrightarrow> Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 False G G'\<^sub>T G'\<^sub>U F F' var_uG var_uG'\<^sub>T var_uG'\<^sub>U uF uF' T U D r ants conds
\<Longrightarrow> Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 False G G'\<^sub>T G'\<^sub>U F F' var_uG var_uG'\<^sub>T var_uG'\<^sub>U uF uF' T U D r ants conds\<close> .


subparagraph \<open>Default Rules\<close>

lemma [\<phi>reason %guess_tyop_commute_fallback for \<open>Guess_Tyops_Commute _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Type_Operator F F'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator G G'
\<Longrightarrow> Guess_Tyops_Commute both F F' G G' uF uF' any any' T (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True\<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute_fallback for \<open>Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Type_Operator2 F F'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator G G'\<^sub>T
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator G G'\<^sub>U
\<Longrightarrow> Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 both G G'\<^sub>T G'\<^sub>U F F' uG uG'\<^sub>T uG'\<^sub>U uF uF' T U
                          (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True \<close>
  unfolding Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def ..

lemma [\<phi>reason %guess_tyop_commute_fallback for \<open>Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Type_Operator2 G G'
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F F'\<^sub>T
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F F'\<^sub>U
\<Longrightarrow> Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 both F F'\<^sub>T F'\<^sub>U G G' uF uF'\<^sub>T uF'\<^sub>U uG uG' T U
                               (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True \<close>
  unfolding Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def ..


subparagraph \<open>ML\<close>

ML_file \<open>library/phi_type_algebra/guess_tyops_commute.ML\<close>


subparagraph \<open>Templates\<close>

context begin

private lemma Guess_Tyops_Commute_by_unfolding_1:
  \<open> (\<And>T x. A T x = A' T x)
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' uG uG' A' uF' T D R a c
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' uG uG' A  uF' T D R a c \<close>
  by presburger

private lemma Guess_Tyops_Commute_by_unfolding_2:
  \<open> (\<And>T x. A T x = A' T x)
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' uG uG' uF A' T D R a c
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' uG uG' uF A  T D R a c \<close>
  by presburger

private lemma Guess_Tyops_Commute_by_unfolding_3:
  \<open> (\<And>T x. A T x = A' T x)
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' A' uG' uF uF' T D R a c
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' A  uG' uF uF' T D R a c \<close>
  by presburger

private lemma Guess_Tyops_Commute_by_unfolding_4:
  \<open> (\<And>T x. A T x = A' T x)
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' uG A' uF uF' T D R a c
\<Longrightarrow> Guess_Tyops_Commute mode G G' F F' uG A  uF uF' T D R a c \<close>
  by presburger+

lemmas Guess_Tyops_Commute_by_unfolding =
          Guess_Tyops_Commute_by_unfolding_1 Guess_Tyops_Commute_by_unfolding_2
          Guess_Tyops_Commute_by_unfolding_3 Guess_Tyops_Commute_by_unfolding_4

end

paragraph \<open>ToA with Bubbling in Target\<close>

consts bubbling_target :: action

definition Has_Bubbling :: \<open>'a \<Rightarrow> 'a\<close> ("\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> _" [61] 60) where [iff]: \<open>Has_Bubbling X \<equiv> X\<close>

subparagraph \<open>Bubbling_Target in Transformation\<close>

declare [[ \<phi>reason_default_pattern
     \<open>_ \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?G \<w>\<i>\<t>\<h> _ @action bubbling_target\<close> \<Rightarrow>
     \<open>_ \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?G \<w>\<i>\<t>\<h> _ @action bubbling_target\<close>    (100)
 and \<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?F \<w>\<i>\<t>\<h> _ @action bubbling_target\<close> \<Rightarrow>
     \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?F \<w>\<i>\<t>\<h> _ @action bubbling_target\<close>         (100)
 and \<open>?X @action bubbling_target\<close> \<Rightarrow>
     \<open>ERROR TEXT(\<open>Bad rule of bubbling-target\<close> (?X @action bubbling_target))\<close> (0)
]]

\<phi>reasoner_group bubbling_target = (100, [20, 2000]) for \<open>X @action bubbling_target\<close>
    \<open>Transformation rules moving targets tagged by \<open>bubbling_target\<close> to the top.\<close>
  and derived_bubbling_target = (40, [40,42]) for \<open>X @action bubbling_target\<close> in bubbling_target
    \<open>Derived rules.\<close>

lemma [\<phi>reason_template default %derived_bubbling_target]:
  \<open> Functional_Transformation_Functor Fa Fb T U D R pm fm
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<w>\<i>\<t>\<h> P a @action bubbling_target)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a \<in> D x. f a \<in> R x)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fa (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T) \<w>\<i>\<t>\<h> Q @action bubbling_target
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fm f P x \<Ztypecolon> Fb (\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> U) \<w>\<i>\<t>\<h> pm f P x \<and> Q @action bubbling_target\<close>
  unfolding Functional_Transformation_Functor_def meta_Ball_def Premise_def Has_Bubbling_def
            Transformation_def Action_Tag_def Bubbling_def
  by clarsimp metis

lemma [\<phi>reason %ToA_normalizing]: \<comment> \<open>entry point to \<open>bubbling_target\<close> sub-reasoning\<close>
  \<open> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action bubbling_target
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> Q
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> U \<w>\<i>\<t>\<h> P \<and> Q \<close>
  unfolding Action_Tag_def Has_Bubbling_def Transformation_def Bubbling_def
  by clarsimp blast

subparagraph \<open>Deriving Bubbling ToA\<close>

lemma [\<phi>reason_template default %derived_bubbling_target]:
  \<open> Tyops_Commute F F' G G' T D (embedded_func f P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' T) \<w>\<i>\<t>\<h> P x @action bubbling_target\<close>
  unfolding Tyops_Commute_def Premise_def Bubbling_def Transformation_def Action_Tag_def
  by clarsimp

lemma [\<phi>reason_template default %derived_bubbling_target+1]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D (embedded_func f P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<w>\<i>\<t>\<h> P x @action bubbling_target\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def Action_Tag_def
  by clarsimp

lemma [\<phi>reason_template default %derived_bubbling_target]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D (embedded_func f P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (F'\<^sub>U U) \<w>\<i>\<t>\<h> P x @action bubbling_target\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def Action_Tag_def
  by clarsimp

lemma [\<phi>reason_template default %derived_bubbling_target]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D (embedded_func f P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<w>\<i>\<t>\<h> P x @action bubbling_target\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def Action_Tag_def
  by clarsimp

lemma [\<phi>reason_template default %derived_bubbling_target]:
  \<open> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D (embedded_func f P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T U) \<w>\<i>\<t>\<h> P x @action bubbling_target\<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Bubbling_def Action_Tag_def
  by clarsimp



subparagraph \<open>Simpset adding \<open>\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g>\<close>\<close>

ML \<open> structure Tag_Has_Bubbling = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS_configure (fn ctxt =>
                      Simplifier.add_cong @{lemma' \<open>\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T \<equiv> \<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T\<close>
                                                by (unfold Has_Bubbling_def)} ctxt)
  val post_merging = I
  val binding = SOME \<^binding>\<open>_tagging_has_bubbling_\<close>
  val attribute = NONE
  val comment = "Rules adding \<open>\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g>\<close> tag, should of form \<open>F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T) \<equiv> \<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> (F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T))\<close>"
)
\<close>

lemma [\<phi>reason_template requires \<open>Tyops_Commute _ F' _ G' _ _ _\<close> ["_tagging_has_bubbling_"]]:
  \<open> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' T) \<equiv> \<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' T)\<close>
  unfolding Has_Bubbling_def .

lemma [\<phi>reason_template requires \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ F'\<^sub>T _ _ G' _ _ _ _\<close> ["_tagging_has_bubbling_"]]:
  \<open> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) U \<equiv> \<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) U\<close>
  unfolding Has_Bubbling_def .

lemma [\<phi>reason_template requires \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ _ F'\<^sub>U _ G' _ _ _ _\<close> ["_tagging_has_bubbling_"]]:
  \<open> G' T (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<equiv> \<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' T (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U)\<close>
  unfolding Has_Bubbling_def .

lemma [\<phi>reason_template requires \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F _ _ G _ T U _ _\<close> ["_tagging_has_bubbling_"]]:
  \<open> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T U) \<equiv> \<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T U)\<close>
  unfolding Has_Bubbling_def .


paragraph \<open>Deriver\<close>

\<phi>reasoner_group derived_commutativity_deriver = (150, [150, 151 ]) for \<open>_\<close>
    \<open>The priority of derived deriver for commutativity between type operators\<close>

(*F is fixed myself, G is the target
  Given \<open>F\<close>, generate derivers deriving \<open>Tyops_Commute F F' G G' T D r\<close>
  and \<open>Tyops_Commute G G' F F' T D r\<close> for given G
*)

lemma \<phi>TA_TyComm\<^sub>I_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
          (x \<Ztypecolon> OPEN (G (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F T)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' (MAKE (G' T)) \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_ind_target \<A>simp)
          \<comment>\<open>^ target of inductive expansion, needs \<open>to (\<c>\<o>\<m>\<m>\<u>\<t>\<e> G F)\<close>\<close>
          \<comment>\<open>The \<open>OPEN\<close> tag restricts the deriver to only unfold what should be unfolded,
             especially when reasoning the commutativity between one \<phi>-type and itself.\<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute G G' F F' T D r\<close>
  unfolding Action_Tag_def Tyops_Commute_def Premise_def Bubbling_def MAKE_def OPEN_def
  by blast

lemma \<phi>TA_TyComm\<^sub>E_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x y. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<and> f x = y \<longrightarrow>
          (x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (OPEN (G T)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE (G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' T)) \<w>\<i>\<t>\<h> P x) @action \<phi>TA_ind_target bubbling_target)
                                \<comment>\<open>^ target of inductive expansion. We only support a function \<open>embedded_func f P\<close>
              instead of a relation. It is a limitation. The main difficulty is here if it is a relation,
              we lose the location \<open>y \<Ztypecolon> G' _\<close> to apply induction. \<open>y\<close> is fixed here, but if we consider
              a relation, then \<open>y\<close> is existentially quantified. We have no idea how to overcome this
              limitation right now.\<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute F F' G G' T D (embedded_func f P)\<close>
  unfolding Action_Tag_def Tyops_Commute_def Premise_def embedded_func_def Bubbling_def OPEN_def MAKE_def
  by clarsimp
  

lemma \<phi>TA_TyComm\<^sub>1\<^sub>_\<^sub>2\<^sub>I_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'\<^sub>T
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F F'\<^sub>U
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
          (x \<Ztypecolon> OPEN (G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (MAKE (G T U)) \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_ind_target \<A>simp)
          \<comment>\<open>^ target of inductive expansion, needs \<open>to (\<c>\<o>\<m>\<m>\<u>\<t>\<e> G F)\<close>\<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r\<close>
  unfolding Action_Tag_def Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Bubbling_def OPEN_def MAKE_def
  by blast

lemma \<phi>TA_TyComm\<^sub>1\<^sub>_\<^sub>2\<^sub>E_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'\<^sub>T
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F F'\<^sub>U
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x y. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<and> f x = y \<longrightarrow>
          (x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (OPEN (G T U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE (G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U)) \<w>\<i>\<t>\<h> P x) @action \<phi>TA_ind_target bubbling_target)
                                                \<comment>\<open>^ target of inductive expansion. The same limitation as above.\<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D (embedded_func f P)\<close>
  unfolding Action_Tag_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def embedded_func_def OPEN_def MAKE_def Bubbling_def
  by clarsimp

lemma \<phi>TA_TyComm\<^sub>2\<^sub>_\<^sub>1\<^sub>I_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
          (x \<Ztypecolon> OPEN (G (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F T U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' (MAKE (G'\<^sub>T T)) (MAKE (G'\<^sub>U U)) \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_ind_target \<A>simp)
          \<comment>\<open>^ target of inductive expansion, needs \<open>to (\<c>\<o>\<m>\<m>\<u>\<t>\<e> G F)\<close>\<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 G G'\<^sub>T G'\<^sub>U F F' T U D r\<close>
  unfolding Action_Tag_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def OPEN_def MAKE_def
  by clarsimp

lemma \<phi>TA_TyComm\<^sub>2\<^sub>_\<^sub>1\<^sub>E_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x y. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<and> f x = y \<longrightarrow>
          (x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' (OPEN (G'\<^sub>T T)) (OPEN (G'\<^sub>U U)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE (G (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F T U)) \<w>\<i>\<t>\<h> P x) @action \<phi>TA_ind_target bubbling_target)
                                                          \<comment>\<open>^ target of inductive expansion. The same limitation as above.\<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 G G'\<^sub>T G'\<^sub>U F F' T U D (embedded_func f P)\<close>
  unfolding Action_Tag_def Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def embedded_func_def OPEN_def MAKE_def Bubbling_def
  by clarsimp


ML_file \<open>library/phi_type_algebra/gen_tyops_commute.ML\<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>I 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.meta_Tyops_Commute (false, 1) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>E 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.meta_Tyops_Commute (false, 2) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.meta_Tyops_Commute (false, 3) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>I_rev 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.meta_Tyops_Commute (true, 2) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>E_rev 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.meta_Tyops_Commute (true, 1) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver_rev 110
    = \<open>fn quiet => K (Phi_Type_Algebra_Derivers.meta_Tyops_Commute (true, 3) quiet) \<close>


subsection \<open>Deriving Configures for Specific Abstract Algebras\<close>

subsubsection \<open>Common\<close>

setup \<open>Context.theory_map (Phi_Type_Algebra_Derivers.Expansion.map (fn ctxt => ctxt addsimps
  @{thms' HOL.simp_thms ex_simps[symmetric] mem_Collect_eq imp_ex
          prod.case prod.sel fst_apfst snd_apfst fst_apsnd snd_apsnd apfst_id apsnd_id apfst_conv apsnd_conv prod.inject
          ExSet_simps
          \<phi>Prod_expn' \<phi>Prod_expn''
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


subsubsection \<open>Function\<close>

definition \<open>zip_fun = case_prod BNF_Def.convol\<close>
definition \<open>unzip_fun f = (fst o f, snd o f)\<close>

lemma zip_fun_inj[simp]:
  \<open>fst o (zip_fun f) = fst f\<close>
  \<open>snd o (zip_fun f) = snd f\<close>
  unfolding zip_fun_def fun_eq_iff BNF_Def.convol_def
  by (cases f; clarsimp)+

lemma zip_fun_inj'[simp]:
  \<open>fst (zip_fun f x) = fst f x\<close>
  \<open>snd (zip_fun f x) = snd f x\<close>
  unfolding zip_fun_def fun_eq_iff BNF_Def.convol_def
  by (cases f; clarsimp)+

lemma zip_fun_map:
  \<open>zip_fun (f o x, y) = apfst f o zip_fun (x, y)\<close>
  \<open>zip_fun (x, g o y) = apsnd g o zip_fun (x, y)\<close>
  unfolding zip_fun_def BNF_Def.convol_def
  by clarsimp+

lemma zip_fun_prj[simp]:
  \<open>fst (unzip_fun x) = fst o x\<close>
  \<open>snd (unzip_fun x) = snd o x\<close>
  unfolding unzip_fun_def
  by clarsimp+

lemma map_fun_prod_case_analysis:
  \<open>(\<lambda>x. (f x, g x)) o a = b \<equiv> f o a = fst o b \<and> g o a = snd o b\<close>
  unfolding atomize_eq fun_eq_iff
  by (clarsimp, rule, metis fst_eqD snd_conv, clarsimp)

setup \<open> Context.theory_map(
  let val (i, a, b) = (\<^typ>\<open>'i\<close>, \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close>)
   in BNF_FP_Sugar_More.add_fp_more (\<^type_name>\<open>fun\<close>, {
        deads = [i], lives = [a], lives'= [b],
        zip = \<^Const>\<open>zip_fun i a b\<close>,
        unzip = \<^Const>\<open>unzip_fun i a b\<close>,
        zip_simps = @{thms' zip_fun_inj zip_fun_inj' zip_fun_map zip_fun_prj map_fun_prod_case_analysis}
  }) end)
\<close>



subsubsection \<open>Production\<close>

lemma [\<phi>constraint_expansion, simp]:
  \<open>pred_prod (\<lambda>a. True) P x \<longleftrightarrow> P (snd x)\<close>
  \<open>pred_prod Q (\<lambda>a. True) x \<longleftrightarrow> Q (fst x)\<close>
  by (cases x; simp)+

declare Lifting.pred_prod_beta[\<phi>deriver_simp]

end
                                                          